import csv, io, hashlib, json, urllib.request
from collections import defaultdict
from decimal import Decimal

URL="https://raw.githubusercontent.com/CUNY-CISC-3225/datasets/main/wine_quality/winequality-red.csv"
SHA="9bb4e3cd10475593334526fd8deb9e809800f061"
raw=urllib.request.urlopen(URL, timeout=30).read()
assert hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()==SHA
rows=list(csv.DictReader(io.StringIO(raw.decode()),delimiter=";"))
assert len(rows)==1599
train,test=rows[:1119],rows[1119:]
def is_high(r): return Decimal(r["volatile acidity"])>=Decimal("0.60")
groups=defaultdict(set)
for r in train: groups[r["pH"]].add(is_high(r))
pure={p:next(iter(v)) for p,v in groups.items() if len(v)==1}
accepted=[(i,r,pure[r["pH"]]) for i,r in enumerate(test) if r["pH"] in pure]
wrong=[(i,r) for i,r,pred in accepted if pred!=is_high(r)]
print(json.dumps({"train":len(train),"holdout":len(test),"naive_pH_decisions":len(accepted),"naive_pH_wrong":len(wrong),"strict_open_world_ACT_from_pH_only":0,"strict_open_world_REFUSE_or_direct_AV":len(test),"zero_direct_AV_savings_eur":0,"input_git_blob":SHA}, indent=2))
assert len(accepted)==28 and len(wrong)==10
