import csv, io, math, urllib.request
from collections import Counter, defaultdict

URL = 'https://raw.githubusercontent.com/vincentarelbundock/Rdatasets/master/csv/Ecdat/Heating.csv'
ACTIONS = ['gc','gr','ec','er','hp']
HORIZONS = [1,2,5,10,15,20,30,40]
# Fixed before result: deterministic tie-break order = ACTIONS above.

text = urllib.request.urlopen(URL, timeout=60).read().decode('utf-8')
rows = list(csv.DictReader(io.StringIO(text)))
assert len(rows) == 900, len(rows)

ic_cols = {a:f'ic.{a}' for a in ACTIONS}
oc_cols = {a:f'oc.{a}' for a in ACTIONS}

def required_action(r, H):
    vals = {a: float(r[ic_cols[a]]) + H * float(r[oc_cols[a]]) for a in ACTIONS}
    m = min(vals.values())
    # Fixed deterministic tie-break; tolerance only for floating representation of exact CSV decimals.
    return next(a for a in ACTIONS if abs(vals[a]-m) <= 1e-12)

# Eight non-nested future contracts: exact minimum lifetime cost at each declared horizon.
signatures = [tuple(required_action(r,H) for H in HORIZONS) for r in rows]
counts = Counter(signatures)
min_safe_codes = len(counts)  # exact under deterministic contract: each safe fiber must have one signature.

# Natural coarse representations, fixed before result.
incomes=[float(r['income']) for r in rows]
order=sorted(range(len(rows)), key=lambda i:(incomes[i],i))
quart=[None]*len(rows)
for rank,i in enumerate(order): quart[i]=min(3,4*rank//len(rows))
rooms=[r['rooms'] for r in rows]
age_decade=[int(float(r['agehed']))//10 for r in rows]
labels={
    'NONE':[0]*len(rows),
    'INCOME_QUARTILE':quart,
    'ROOMS':rooms,
    'AGE_DECADE':age_decade,
    'INCOME_Q+ROOMS':[f'{quart[i]}|{rooms[i]}' for i in range(len(rows))],
    'IDENTITY':list(range(len(rows))),
}

def contracts_preserved(lbls):
    groups=defaultdict(list)
    for i,l in enumerate(lbls): groups[l].append(i)
    ok=0
    perH=[]
    for j,H in enumerate(HORIZONS):
        good=True
        for ids in groups.values():
            acts={signatures[i][j] for i in ids}
            if len(acts) != 1:
                good=False; break
        perH.append(good)
        ok += int(good)
    return ok, perH

print('INSACERMO_BLIND_HEATING_ADVERSARIAL_V1')
print('ROWS',len(rows))
print('ACTIONS',','.join(ACTIONS))
print('HORIZONS',','.join(map(str,HORIZONS)))
print('CONTRACTS',len(HORIZONS))
print('MIN_SAFE_CODES_EXACT',min_safe_codes)
print('NOMINAL_BITS',round(math.log2(min_safe_codes),6))
print('IDENTITY_BITS',round(math.log2(len(rows)),6))
print('CODE_COUNT_COMPRESSION',round(len(rows)/min_safe_codes,6))
print('TOP_SIGNATURES')
for sig,n in counts.most_common(20):
    print('/'.join(sig),n)
print('NATURAL_REPRESENTATIONS')
for name,lbl in labels.items():
    ok,perH=contracts_preserved(lbl)
    print(name,'CELLS',len(set(lbl)),'PRESERVED',ok,'OF',len(HORIZONS),'MASK',''.join('1' if x else '0' for x in perH))
print('SIGNATURE_SINGLETONS',sum(1 for n in counts.values() if n==1))
print('LARGEST_SIGNATURE_CLASS',max(counts.values()))
