import io, math, re, urllib.request, zipfile
from bisect import bisect_left
from collections import Counter, defaultdict

URL = 'https://archive.ics.uci.edu/static/public/602/dry+bean+dataset.zip'
BINS = 10
# Fixed before result: exact class + 8 morphology futures.
SELECTED_NUMERIC_INDICES = [0,1,2,3,4,5,10,11]

raw = urllib.request.urlopen(URL, timeout=60).read()
zf = zipfile.ZipFile(io.BytesIO(raw))
arff_name = next(n for n in zf.namelist() if n.lower().endswith('.arff'))
text = zf.read(arff_name).decode('utf-8', errors='replace')

attrs=[]
data=[]
in_data=False
for line in text.splitlines():
    s=line.strip()
    if not s or s.startswith('%'):
        continue
    if not in_data:
        if s.lower().startswith('@attribute'):
            m=re.match(r"@attribute\s+(?:'([^']+)'|\"([^\"]+)\"|([^\s]+))\s+(.+)$", s, flags=re.I)
            if m:
                attrs.append(m.group(1) or m.group(2) or m.group(3))
        elif s.lower().startswith('@data'):
            in_data=True
    else:
        parts=[x.strip() for x in s.split(',')]
        if parts:
            data.append(parts)

assert len(data) == 13611, len(data)
assert len(attrs) >= 17, attrs
class_idx=len(attrs)-1
num_names=[attrs[i] for i in SELECTED_NUMERIC_INDICES]

num_values={i:[float(r[i]) for r in data] for i in SELECTED_NUMERIC_INDICES}

def thresholds(values,bins=BINS):
    s=sorted(values); n=len(s); out=[]
    for k in range(1,bins):
        idx=math.ceil(k*n/bins)-1
        out.append(s[idx])
    return out

th={i:thresholds(vs) for i,vs in num_values.items()}

def bin_answer(i,v):
    return bisect_left(th[i], float(v))

# Contract answers: registered variety + 8 morphology classes.
answers={}
answers['Class']=[r[class_idx] for r in data]
for i in SELECTED_NUMERIC_INDICES:
    answers[attrs[i]]=[bin_answer(i,r[i]) for r in data]
queries=['Class']+num_names
signatures=[tuple(answers[q][j] for q in queries) for j in range(len(data))]
counts=Counter(signatures)
min_safe_codes=len(counts)

# Natural/coarse representations fixed before result.
area_q=num_names[0]
perim_q=num_names[1]
reps={
    'NONE':[0]*len(data),
    'CLASS_ONLY':answers['Class'],
    'AREA10':answers[area_q],
    'AREA10+PERIM10':[(answers[area_q][j],answers[perim_q][j]) for j in range(len(data))],
    'CLASS+AREA10':[(answers['Class'][j],answers[area_q][j]) for j in range(len(data))],
    'IDENTITY':list(range(len(data))),
}

def preserved_queries(labels):
    groups=defaultdict(list)
    for j,l in enumerate(labels): groups[l].append(j)
    out=[]
    for q in queries:
        vals=answers[q]
        ok=True
        for ids in groups.values():
            v0=vals[ids[0]]
            if any(vals[k] != v0 for k in ids[1:]):
                ok=False; break
        out.append(ok)
    return out

print('INSACERMO_BLIND_DRYBEAN_V1')
print('ROWS',len(data))
print('CONTRACTS',len(queries))
print('QUERIES','|'.join(queries))
print('BINS_REQUESTED',BINS)
print('MIN_SAFE_CODES_EXACT',min_safe_codes)
print('NOMINAL_BITS',round(math.log2(min_safe_codes),6))
print('IDENTITY_BITS',round(math.log2(len(data)),6))
print('CODE_COUNT_COMPRESSION',round(len(data)/min_safe_codes,6))
print('SAFE_CODE_FRACTION_OF_IDENTITY',round(min_safe_codes/len(data),6))
print('SIGNATURE_SINGLETONS',sum(1 for n in counts.values() if n==1))
print('SINGLETON_ROW_FRACTION',round(sum(1 for n in counts.values() if n==1)/len(data),6))
print('LARGEST_SIGNATURE_CLASS',max(counts.values()))
print('REALIZED_ANSWER_ALPHABETS')
for q in queries: print(q,len(set(answers[q])))
print('NATURAL_REPRESENTATIONS')
for name,lbl in reps.items():
    ok=preserved_queries(lbl)
    print(name,'CELLS',len(set(lbl)),'PRESERVED',sum(ok),'OF',len(queries),'MASK',''.join('1' if x else '0' for x in ok))
print('TOP_SIGNATURE_CLASS_SIZES')
for _,n in counts.most_common(20): print(n)
