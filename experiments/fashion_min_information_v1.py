#!/usr/bin/env python3
import gzip, hashlib, json, os, struct, urllib.request
import numpy as np

BASE = 'https://raw.githubusercontent.com/zalandoresearch/fashion-mnist/master/data/fashion/'
FILES = {
 'train-images-idx3-ubyte.gz':'3aede38d61863908ad78613f6a32ed271626dd12800ba2636569512369268a84',
 'train-labels-idx1-ubyte.gz':'a04f17134ac03560a47e3764e11b92fc97de4d1bfaf8ba1a3aa29af54cc90845',
 't10k-images-idx3-ubyte.gz':'346e55b948d973a97e58d2351dde16a484bd415d4595297633bb08f03db6a073',
 't10k-labels-idx1-ubyte.gz':'67da17c76eaffca5446c3361aaab5c3cd6d1c2608764d35dfb1850b086bf8dd5',
}
EXPECTED_V3 = {
 2: {'obs_classes':20343,'ambiguous_classes':1965,'ambiguous_rows':32042,'max_class':5583},
 4: {'obs_classes':55864,'ambiguous_classes':419,'ambiguous_rows':1898,'max_class':200},
 8: {'obs_classes':59948,'ambiguous_classes':4,'ambiguous_rows':10,'max_class':3},
}
M_VALUES = [1,2,4,8,16,32]
BUDGETS = [2,3,4,5,6,8,10,12,16,24,32,49]
Q_VALUES = [2,4,8]

def sha256(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()

def ensure_data(root='fashion_data'):
    os.makedirs(root,exist_ok=True)
    for fn,expected in FILES.items():
        p=os.path.join(root,fn)
        if not os.path.exists(p) or sha256(p)!=expected:
            print('DOWNLOAD',fn,flush=True)
            urllib.request.urlretrieve(BASE+fn,p)
        got=sha256(p)
        if got!=expected: raise RuntimeError(f'SHA mismatch {fn}: {got}')
    return root

def read_images(path):
    with gzip.open(path,'rb') as f:
        magic,n,r,c=struct.unpack('>IIII',f.read(16))
        if magic!=2051: raise ValueError('bad image magic')
        x=np.frombuffer(f.read(),dtype=np.uint8).reshape(n,r,c)
    return x

def read_labels(path):
    with gzip.open(path,'rb') as f:
        magic,n=struct.unpack('>II',f.read(8))
        if magic!=2049: raise ValueError('bad label magic')
        y=np.frombuffer(f.read(),dtype=np.uint8)
    if len(y)!=n: raise ValueError('bad label count')
    return y

def block_means(x):
    n=len(x)
    return x.reshape(n,7,4,7,4).mean(axis=(2,4)).reshape(n,49)

def quantize(means,q,mode):
    if mode=='floor256':
        return np.minimum(q-1, np.floor(means*q/256.0)).astype(np.uint8)
    if mode=='round255':
        return np.rint(means*(q-1)/255.0).clip(0,q-1).astype(np.uint8)
    if mode=='floor255':
        return np.floor(means*q/255.0000001).clip(0,q-1).astype(np.uint8)
    raise ValueError(mode)

def signature_stats(sig,y):
    d={}
    for row,label in zip(sig,y):
        k=row.tobytes()
        if k not in d: d[k]=[0,0]
        d[k][0]+=1; d[k][1] |= 1<<int(label)
    ambiguous_classes=sum(1 for c,m in d.values() if m & (m-1))
    ambiguous_rows=sum(c for c,m in d.values() if m & (m-1))
    max_class=max(c for c,m in d.values())
    return {'obs_classes':len(d),'ambiguous_classes':ambiguous_classes,'ambiguous_rows':ambiguous_rows,'max_class':max_class}

def identify_quantizer(means,y):
    modes=['floor256','round255','floor255']
    matches=[]; audits={}
    for mode in modes:
        audits[mode]={}
        ok=True
        for q in Q_VALUES:
            s=signature_stats(quantize(means,q,mode),y)
            audits[mode][q]=s
            if s!=EXPECTED_V3[q]: ok=False
        if ok: matches.append(mode)
    if len(matches)!=1:
        raise RuntimeError('Could not uniquely reproduce V3 quantizer: '+json.dumps(audits,sort_keys=True))
    return matches[0],audits

def stratified_split(y):
    out={'A':[],'B':[],'cal':[],'sealed':[]}
    for c in range(10):
        idx=np.flatnonzero(y==c)
        if len(idx)!=6000: raise RuntimeError(f'class {c} count {len(idx)}')
        out['A'].extend(idx[:2000]); out['B'].extend(idx[2000:4000]); out['cal'].extend(idx[4000:5000]); out['sealed'].extend(idx[5000:6000])
    return {k:np.array(v,dtype=np.int32) for k,v in out.items()}

def orders():
    pts=[(r,c,r*7+c) for r in range(7) for c in range(7)]
    center=sorted(pts,key=lambda t:((t[0]-3)**2+(t[1]-3)**2, abs(t[0]-3)+abs(t[1]-3),t[0],t[1]))
    row=pts
    coarse_set={(r,c) for r in [0,2,4,6] for c in [0,2,4,6]}
    coarse=[t for t in center if (t[0],t[1]) in coarse_set]
    rest=[t for t in center if (t[0],t[1]) not in coarse_set]
    return {
      'center_out':np.array([t[2] for t in center],dtype=np.int32),
      'row_major':np.array([t[2] for t in row],dtype=np.int32),
      'coarse_center':np.array([t[2] for t in coarse+rest],dtype=np.int32),
    }

def build_map(sig,y,k):
    d={}
    for row,label in zip(sig,y):
        key=row[:k].tobytes()
        v=d.get(key)
        if v is None: d[key]=[1,1<<int(label)]
        else: v[0]+=1; v[1] |= 1<<int(label)
    return d

def singleton_label(mask):
    if mask and not (mask & (mask-1)):
        return mask.bit_length()-1
    return -1

def evaluate_order(sigA,yA,sigB,yB, evalsets, order):
    A=sigA[:,order]; B=sigB[:,order]
    E={name:s[:,order] for name,(s,_) in evalsets.items()}
    Y={name:y for name,(_,y) in evalsets.items()}
    n={name:len(s) for name,s in E.items()}
    earliest={m:{name:np.zeros(n[name],dtype=np.uint8) for name in E} for m in M_VALUES}
    pred={m:{name:np.full(n[name],255,dtype=np.uint8) for name in E} for m in M_VALUES}
    for k in range(1,50):
        mapA=build_map(A,yA,k); mapB=build_map(B,yB,k)
        for name,S in E.items():
            keys=[row[:k].tobytes() for row in S]
            witnesses=[]
            for key in keys:
                a=mapA.get(key); b=mapB.get(key)
                if a is None or b is None:
                    witnesses.append((-1,0)); continue
                la=singleton_label(a[1]); lb=singleton_label(b[1])
                if la>=0 and la==lb:
                    witnesses.append((la,min(a[0],b[0])))
                else: witnesses.append((-1,0))
            labels=np.fromiter((z[0] for z in witnesses),dtype=np.int16,count=len(witnesses))
            supports=np.fromiter((z[1] for z in witnesses),dtype=np.int32,count=len(witnesses))
            for m in M_VALUES:
                unresolved=earliest[m][name]==0
                hit=unresolved & (labels>=0) & (supports>=m)
                earliest[m][name][hit]=k
                pred[m][name][hit]=labels[hit].astype(np.uint8)
    metrics={}
    for m in M_VALUES:
        metrics[m]={}
        for name in E:
            yy=Y[name]; depth=earliest[m][name]; pp=pred[m][name]
            rows=[]
            for Bgt in BUDGETS:
                act=(depth>0)&(depth<=Bgt)
                actn=int(act.sum()); err=int(((pp!=yy)&act).sum()); corr=actn-err
                probes=np.where(act,depth,Bgt)
                rows.append({
                  'budget':Bgt,'act':actn,'refuse':int(len(yy)-actn),'coverage':actn/len(yy),
                  'correct':corr,'error':err,'accuracy_on_act':(corr/actn if actn else None),
                  'mean_probes_all':float(probes.mean()),
                  'mean_probes_act':(float(depth[act].mean()) if actn else None),
                  'mean_fraction_image_read':float(probes.mean()/49.0),
                })
            metrics[m][name]=rows
    return metrics

def select_candidates(all_results):
    cands=[]
    for key,metrics in all_results.items():
        q,order=key
        for m in M_VALUES:
            cal_by_B={r['budget']:r for r in metrics[m]['cal']}
            for B in BUDGETS:
                r=cal_by_B[B]
                if r['error']==0 and r['act']>=100:
                    score=r['coverage']/r['mean_probes_all']
                    cands.append({'q':q,'order':order,'min_support_each_half':m,'budget':B,'score':score,**r})
    cands.sort(key=lambda z:(-z['coverage'],z['mean_probes_all'],-z['min_support_each_half'],z['q'],z['order'],z['budget']))
    return cands

def get_row(metrics,m,name,budget):
    for r in metrics[m][name]:
        if r['budget']==budget:return r
    raise KeyError

def main():
    root=ensure_data()
    xt=read_images(os.path.join(root,'train-images-idx3-ubyte.gz')); yt=read_labels(os.path.join(root,'train-labels-idx1-ubyte.gz'))
    xh=read_images(os.path.join(root,'t10k-images-idx3-ubyte.gz')); yh=read_labels(os.path.join(root,'t10k-labels-idx1-ubyte.gz'))
    print('DATASET',xt.shape,xh.shape,flush=True)
    means=block_means(xt); means_h=block_means(xh)
    mode,audits=identify_quantizer(means,yt)
    print('V3_QUANTIZER_REPRODUCED',mode,json.dumps(audits,sort_keys=True),flush=True)
    split=stratified_split(yt)
    print('SPLIT',{k:len(v) for k,v in split.items()},flush=True)
    ords=orders(); all_results={}
    for q in Q_VALUES:
        sig=quantize(means,q,mode); sigh=quantize(means_h,q,mode)
        for oname,order in ords.items():
            print('RUN',q,oname,flush=True)
            metrics=evaluate_order(sig[split['A']],yt[split['A']],sig[split['B']],yt[split['B']],{
              'cal':(sig[split['cal']],yt[split['cal']]),
              'sealed':(sig[split['sealed']],yt[split['sealed']]),
              'official':(sigh,yh),
            },order)
            all_results[(q,oname)]=metrics
    cands=select_candidates(all_results)
    if not cands:
        selected=None
    else:
        selected=cands[0]
        key=(selected['q'],selected['order']); m=selected['min_support_each_half']; B=selected['budget']
        selected['sealed']=get_row(all_results[key],m,'sealed',B)
        selected['official']=get_row(all_results[key],m,'official',B)
    top=[]
    for c in cands[:20]:
        key=(c['q'],c['order']); m=c['min_support_each_half']; B=c['budget']
        cc=dict(c)
        cc['sealed']=get_row(all_results[key],m,'sealed',B)
        cc['official']=get_row(all_results[key],m,'official',B)
        top.append(cc)
    result={
      'experiment':'INSACERMO_FASHION_MIN_INFORMATION_CONTRACT_V1',
      'protocol':{
        'probe_family':'49 non-overlapping 4x4 mean-intensity blocks',
        'quantizer_reproduced_from_V3':mode,
        'reference_A_per_class':2000,'reference_B_per_class':2000,'calibration_per_class':1000,'sealed_per_class':1000,
        'dual_witness_rule':'ACT only when both disjoint reference halves have >=m matching worlds and are each pure for the same action under the observed prefix',
        'probe_orders':'fixed geometric orders; no learned vision model',
        'selection':'among calibration candidates with zero false ACT and >=100 ACT, maximize calibration coverage; ties: fewer mean probes, larger support, lower q, deterministic name/budget',
        'official_test_note':'secondary replication only; prior V3 aggregate official-test results already existed, so the internal sealed 10k is the cleaner prospective evaluation for this new protocol',
      },
      'v3_reproduction':audits,
      'selected':selected,
      'top20_calibration_selected_before_sealed_interpretation':top,
    }
    with open('FASHION_MIN_INFORMATION_CONTRACT_V1.json','w') as f: json.dump(result,f,indent=2,sort_keys=True)
    print('===RESULT_JSON===')
    print(json.dumps(result,indent=2,sort_keys=True))
    print('===END_RESULT_JSON===')

if __name__=='__main__': main()
