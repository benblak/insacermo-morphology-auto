import csv, io, math, urllib.request
from bisect import bisect_left
from collections import Counter, defaultdict

URL = 'https://raw.githubusercontent.com/vincentarelbundock/Rdatasets/master/csv/ggplot2/diamonds.csv'
BINS = 20
CAT = ['cut','color','clarity']
NUM = ['carat','price','x','y','z','depth','table']
QUERIES = CAT + NUM

text = urllib.request.urlopen(URL, timeout=60).read().decode('utf-8')
rows = list(csv.DictReader(io.StringIO(text)))
assert len(rows) == 53940, len(rows)

# Fixed-before-result protocol:
# - 3 exact categorical future questions (cut, color, clarity)
# - 7 exact 20-bin future questions for numeric attributes
# - numeric bins are empirical equal-frequency threshold bins with ties never split
# - the minimal safe representation is the exact joint-answer equivalence relation.

def thresholds(values, bins=BINS):
    s = sorted(values)
    n = len(s)
    out=[]
    for k in range(1,bins):
        idx = math.ceil(k*n/bins) - 1
        out.append(s[idx])
    return out

num_values = {q:[float(r[q]) for r in rows] for q in NUM}
num_thresholds = {q:thresholds(vs) for q,vs in num_values.items()}

def num_answer(q, value):
    # equal values always get equal answers; duplicate quantile thresholds simply
    # reduce the number of realized bins.
    return bisect_left(num_thresholds[q], float(value))

def answer_signature(r):
    return tuple([r[q] for q in CAT] + [num_answer(q,r[q]) for q in NUM])

signatures = [answer_signature(r) for r in rows]
counts = Counter(signatures)
min_safe_codes = len(counts)  # exact by joint-answer equivalence.

# Realized answer alphabets for each future query.
answers = {}
for q in CAT:
    answers[q] = [r[q] for r in rows]
for q in NUM:
    answers[q] = [num_answer(q,r[q]) for r in rows]

# Natural/coarse representations fixed before result.
reps = {
    'NONE':[0]*len(rows),
    'CATEGORICAL':[(r['cut'],r['color'],r['clarity']) for r in rows],
    'CARAT20':answers['carat'],
    'PRICE20':answers['price'],
    'CATEGORICAL+CARAT20':[(r['cut'],r['color'],r['clarity'],answers['carat'][i]) for i,r in enumerate(rows)],
    'IDENTITY':list(range(len(rows))),
}

def preserved_queries(labels):
    groups=defaultdict(list)
    for i,l in enumerate(labels): groups[l].append(i)
    ok=[]
    for q in QUERIES:
        vals=answers[q]
        good=True
        for ids in groups.values():
            first=vals[ids[0]]
            if any(vals[i] != first for i in ids[1:]):
                good=False; break
        ok.append(good)
    return ok

print('INSACERMO_BLIND_DIAMONDS_NEAR_IDENTITY_V1')
print('ROWS',len(rows))
print('CONTRACTS',len(QUERIES))
print('BINS_REQUESTED',BINS)
print('MIN_SAFE_CODES_EXACT',min_safe_codes)
print('NOMINAL_BITS',round(math.log2(min_safe_codes),6))
print('IDENTITY_BITS',round(math.log2(len(rows)),6))
print('CODE_COUNT_COMPRESSION',round(len(rows)/min_safe_codes,6))
print('SAFE_CODE_FRACTION_OF_IDENTITY',round(min_safe_codes/len(rows),6))
print('SIGNATURE_SINGLETONS',sum(1 for n in counts.values() if n==1))
print('SINGLETON_ROW_FRACTION',round(sum(1 for n in counts.values() if n==1)/len(rows),6))
print('LARGEST_SIGNATURE_CLASS',max(counts.values()))
print('REALIZED_ANSWER_ALPHABETS')
for q in QUERIES:
    print(q,len(set(answers[q])))
print('NATURAL_REPRESENTATIONS')
for name,lbl in reps.items():
    ok=preserved_queries(lbl)
    print(name,'CELLS',len(set(lbl)),'PRESERVED',sum(ok),'OF',len(QUERIES),'MASK',''.join('1' if x else '0' for x in ok))
print('TOP_SIGNATURE_CLASS_SIZES')
for _,n in counts.most_common(20): print(n)
