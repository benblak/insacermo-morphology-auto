from collections import defaultdict
from itertools import permutations
import hashlib,json,sys
from pathlib import Path
from uci_occupancy_locked_blind_v1 import COST,FEATURES,STEP,getcsv,unpack,signature,train_catalog,predict
F=tuple(FEATURES)
OLD=('Light','CO2','Temperature','Humidity','HumidityRatio')
P=tuple(COST[x] for x in F)
def binned(row):
    return tuple(signature(row,(x,))[0] for x in F)
def bellman(train):
    B=[binned(r) for r in train]; Y=[r[1] for r in train]
    cache={}
    def solve(ids,mask):
        key=(mask,tuple((j,B[ids[0]][j]) for j in range(5) if mask & (1<<j)))
        if key in cache:return cache[key]
        y=Y[ids[0]]
        if all(Y[i]==y for i in ids):out=({'act':y},0)
        elif mask==31:out=({'refuse':True},0)
        else:
            candidates=[]
            for j in range(5):
                if mask & (1<<j):continue
                groups=defaultdict(list)
                for i in ids:groups[B[i][j]].append(i)
                branches={}
                total=P[j]*len(ids)
                for val,subids in sorted(groups.items()):
                    tree,cost=solve(tuple(subids),mask|(1<<j))
                    branches[val]=tree;total+=cost
                candidates.append((total,j,{'probe':j,'branches':branches}))
            price,chosen,tree=min(candidates,key=lambda x:(x[0],x[1]))
            out=(tree,price)
        cache[key]=out
        return out
    tree,cost=solve(tuple(range(len(train))),0)
    return tree,cost/len(train),len(cache)
def apply(tree,row):
    values=binned(row);node=tree;cost=used=0
    while True:
        if 'act' in node:return node['act'],cost,used
        if 'refuse' in node:return None,cost,used
        j=node['probe'];cost+=P[j];used+=1
        node=node['branches'].get(values[j])
        if node is None:return None,cost,used
def fixed(train,order):
    lookups=[train_catalog(train,order[:d]) for d in range(1,6)]
    cum=[sum(COST[x] for x in order[:d]) for d in range(1,6)]
    def classify(row):
        for d,cat in enumerate(lookups):
            label=predict(cat,row,order[:d+1])
            if label is not None:return label,cum[d],d+1
        return None,cum[-1],5
    return classify
def score(rows,policy):
    correct=errors=refuse=cost=senses=0;decisions=[]
    for r in rows:
        p,c,s=policy(r);decisions.append(p);cost+=c;senses+=s
        if p is None:refuse+=1
        elif p==r[1]:correct+=1
        else:errors+=1
    n=len(rows);accepted=correct+errors
    return {'total':n,'correct':correct,'errors':errors,'refuse':refuse,
      'coverage':round(accepted/n,6),
      'selective_accuracy':round(correct/accepted,6) if accepted else None,
      'whole_sample_accuracy':round(correct/n,6),
      'average_sensor_cost':round(cost/n,4),
      'average_sensors_used':round(senses/n,4)},decisions
def paired(rows,aa,bb):
    out={'both_accepted':0,'both_correct':0,'only_original_correct':0,
      'only_bellman_correct':0,'both_wrong':0,
      'only_original_accepted':0,'only_bellman_accepted':0,'both_refuse':0}
    for r,a,b in zip(rows,aa,bb):
        if a is None and b is None:out['both_refuse']+=1
        elif a is None:out['only_bellman_accepted']+=1
        elif b is None:out['only_original_accepted']+=1
        else:
            out['both_accepted']+=1
            if a==r[1] and b==r[1]:out['both_correct']+=1
            elif a==r[1]:out['only_original_correct']+=1
            elif b==r[1]:out['only_bellman_correct']+=1
            else:out['both_wrong']+=1
    return out
def run(data):
    train=getcsv(data['datatraining.txt'])
    tests={k:getcsv(data[k]) for k in ('datatest.txt','datatest2.txt')}
    assert len(train)==8143
    assert [len(v) for v in tests.values()]==[2665,9752]
    tree,dp_cost,states=bellman(train)
    all_orders=[]
    for order in permutations(F):
        m,_=score(train,fixed(train,order))
        all_orders.append((m['average_sensor_cost'],order))
    best=min(all_orders)[1]
    methods={'insacermo_original':fixed(train,OLD),
      'independent_train_optimal_order':fixed(train,best),
      'independent_bellman_adaptive':lambda row:apply(tree,row)}
    train_scores={k:score(train,p)[0] for k,p in methods.items()}
    assert dp_cost <= train_scores['independent_train_optimal_order']['average_sensor_cost']+.00011
    result={'source':'UCI 357 Occupancy Detection',
      'caveat':'Comparator developed AFTER previous test outcomes seen; training-only optimization, not fully prospective preregistration.',
      'hashes':{k:hashlib.sha256(v).hexdigest() for k,v in data.items()},
      'fixed_bins':STEP,'costs':COST,'frozen_order':OLD,'optimal_fixed_order':best,
      'number_orders':len(all_orders),'dp_training_cost':round(dp_cost,4),
      'dp_states':states,'train':train_scores,'heldout':{}}
    for name,rows in tests.items():
        scores={};decisions={}
        for k,p in methods.items():scores[k],decisions[k]=score(rows,p)
        result['heldout'][name]={'methods':scores,
          'paired_original_vs_bellman':paired(rows,
             decisions['insacermo_original'],decisions['independent_bellman_adaptive'])}
    return result
if __name__=='__main__':
    result=run(unpack(Path(sys.argv[1])))
    Path(sys.argv[2]).write_text(json.dumps(result,indent=2))
    print('TRAIN OPTIMAL FIXED ORDER',result['optimal_fixed_order'])
    print('DP STATES',result['dp_states'])
    for k,v in result['heldout'].items():print(k,json.dumps(v))
    print('BELLMAN_COMPARE_SUCCESS')
