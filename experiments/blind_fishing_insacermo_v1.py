import csv, io, math, urllib.request
from itertools import combinations, product

URL = 'https://raw.githubusercontent.com/vincentarelbundock/Rdatasets/master/csv/Ecdat/Fishing.csv'
ACTIONS = ['beach','pier','boat','charter']
TOLS = [0.0,0.10,0.25,0.50,1.0,2.0,3.0]

text = urllib.request.urlopen(URL, timeout=60).read().decode('utf-8')
rows = list(csv.DictReader(io.StringIO(text)))
assert len(rows) == 1182, len(rows)

price_cols = {'beach':'pbeach','pier':'ppier','boat':'pboat','charter':'pcharter'}
catch_cols = {'beach':'cbeach','pier':'cpier','boat':'cboat','charter':'ccharter'}

def good_price(r,t):
    vals={a:float(r[price_cols[a]]) for a in ACTIONS}
    m=min(vals.values())
    return {a for a,v in vals.items() if v <= (1+t)*m + 1e-12}

def good_catch(r,t):
    vals={a:float(r[catch_cols[a]]) for a in ACTIONS}
    m=max(vals.values())
    return {a for a,v in vals.items() if v + 1e-12 >= m/(1+t)}

# BLIND protocol fixed before seeing results:
# 14 nested futures = 7 price-near-min + 7 catch-near-max contracts.
# Strict generators t=0 imply all looser members of each family.
strict_price=[good_price(r,0.0) for r in rows]
strict_catch=[good_catch(r,0.0) for r in rows]

# Candidate representation code = pair of common actions (price action, catch action).
# A row can live in a code iff both actions satisfy its two strict contracts.
candidates=[]
for ap,ac in product(ACTIONS,ACTIONS):
    covered={i for i,(gp,gc) in enumerate(zip(strict_price,strict_catch)) if ap in gp and ac in gc}
    if covered:
        candidates.append(((ap,ac),covered))

U=set(range(len(rows)))
best_codes=None
for k in range(1,len(candidates)+1):
    for idxs in combinations(range(len(candidates)),k):
        cov=set()
        for j in idxs: cov |= candidates[j][1]
        if cov==U:
            best_codes=[candidates[j][0] for j in idxs]
            break
    if best_codes is not None: break
assert best_codes is not None

# Lower-bound witnesses: a row with a unique feasible pair forces that code.
forced={}
for i,(gp,gc) in enumerate(zip(strict_price,strict_catch), start=1):
    pairs=list(product(sorted(gp),sorted(gc)))
    if len(pairs)==1:
        forced.setdefault(pairs[0], i)

# Assign each row to first compatible selected code.
counts={c:0 for c in best_codes}
assign=[]
for gp,gc in zip(strict_price,strict_catch):
    c=next(c for c in best_codes if c[0] in gp and c[1] in gc)
    assign.append(c)
    counts[c]+=1

# Check all 14 contracts under this codebook.
all_contracts=[]
for kind in ('PRICE','CATCH'):
    for t in TOLS:
        good=[good_price(r,t) if kind=='PRICE' else good_catch(r,t) for r in rows]
        ok=True
        for code in best_codes:
            ids=[i for i,c in enumerate(assign) if c==code]
            common=set(ACTIONS)
            for i in ids: common &= good[i]
            if not common:
                ok=False; break
        all_contracts.append((kind,t,ok))

# Natural income-only representation comparison.
incomes=[float(r['income']) for r in rows]
order=sorted(range(len(rows)), key=lambda i:(incomes[i],i))
quart=[None]*len(rows)
for rank,i in enumerate(order): quart[i]=min(3,4*rank//len(rows))

def safe_for_labels(good, labels):
    groups={}
    for i,l in enumerate(labels): groups.setdefault(l,[]).append(i)
    for ids in groups.values():
        common=set(ACTIONS)
        for i in ids: common &= good[i]
        if not common: return False
    return True

none_labels=[0]*len(rows)
id_labels=list(range(len(rows)))
natural=[]
for name,labels in [('NONE',none_labels),('INCOME_QUARTILE',quart),('IDENTITY',id_labels)]:
    n_ok=0
    for kind,t in [(k,t) for k in ('PRICE','CATCH') for t in TOLS]:
        good=[good_price(r,t) if kind=='PRICE' else good_catch(r,t) for r in rows]
        n_ok += int(safe_for_labels(good, labels))
    natural.append((name,len(set(labels)),n_ok))

print('INSACERMO_BLIND_FISHING_V1')
print('ROWS',len(rows))
print('ACTIONS',','.join(ACTIONS))
print('CONTRACTS',len(all_contracts))
print('MIN_SAFE_CODES',len(best_codes))
print('NOMINAL_BITS',round(math.log2(len(best_codes)),6))
print('IDENTITY_BITS',round(math.log2(len(rows)),6))
print('CODE_COUNT_COMPRESSION',round(len(rows)/len(best_codes),6))
print('BEST_CODES')
for c in best_codes: print(c[0],c[1],counts[c])
print('FORCED_TYPES',len(forced))
for c,i in sorted(forced.items()): print('FORCED',c[0],c[1],'ROW',i)
print('ALL_14_PRESERVED',all(ok for _,_,ok in all_contracts))
for kind,t,ok in all_contracts: print('CONTRACT',kind,t,ok)
print('NATURAL_REPRESENTATIONS')
for x in natural: print(*x)
