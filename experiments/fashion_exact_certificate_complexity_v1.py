#!/usr/bin/env python3
import json,time,importlib.util
import numpy as np
from collections import Counter

spec=importlib.util.spec_from_file_location("base","experiments/fashion_instance_certificates_v1.py")
base=importlib.util.module_from_spec(spec); spec.loader.exec_module(base)

def prep():
 r=base.ensure(); x=base.images(r+"/train-images-idx3-ubyte.gz"); y=base.labels(r+"/train-labels-idx1-ubyte.gz"); S=base.q8(x)
 allmask,cls,match=base.build_bitsets(S,y)
 return S,y,allmask,cls,match

def exact_one(i,S,y,allmask,cls,match):
 xv=S[i]; rem0=allmask ^ cls[int(y[i])]
 rem=rem0; chosen=[]
 while rem:
  best=min(range(49),key=lambda p:(rem & match[p][int(xv[p])]).bit_count())
  nr=rem & match[best][int(xv[best])]
  if nr==rem:return None,0
  chosen.append(best); rem=nr
 upper=len(chosen)
 nodes=0
 def ok(rem,d,memo):
  nonlocal nodes
  nodes+=1
  if rem==0:return True
  if d==0:return False
  key=(rem,d)
  if key in memo:return memo[key]
  # pick an uncovered conflicting world with fewest distinguishing probes
  bits=rem; bestcand=None
  for _ in range(16):
   if not bits:break
   b=bits & -bits; j=b.bit_length()-1; bits^=b
   cand=[p for p in range(49) if S[j,p]!=xv[p]]
   if not cand:memo[key]=False;return False
   if bestcand is None or len(cand)<len(bestcand):bestcand=cand
  # valid elimination bound
  n=rem.bit_count(); mx=0
  for p in range(49):
   mx=max(mx,n-(rem & match[p][int(xv[p])]).bit_count())
  if mx==0 or (n+mx-1)//mx>d:memo[key]=False;return False
  seen=set()
  opts=[]
  for p in bestcand:
   nr=rem & match[p][int(xv[p])]
   if nr not in seen:seen.add(nr);opts.append((nr.bit_count(),p,nr))
  for _,p,nr in sorted(opts):
   if ok(nr,d-1,memo):memo[key]=True;return True
  memo[key]=False;return False
 for k in range(1,upper):
  if ok(rem0,k,{}):return k,nodes
 return upper,nodes

def main():
 S,y,allmask,cls,match=prep(); hist=Counter(); bad=[]; nodes=0;t=time.time()
 for i in range(len(y)):
  k,n=exact_one(i,S,y,allmask,cls,match);nodes+=n
  if k is None:bad.append(i)
  else:hist[k]+=1
  if (i+1)%2000==0:print("P",i+1,dict(sorted(hist.items())),len(bad),nodes,round(time.time()-t,1),flush=True)
 vals=[]
 for k,v in hist.items():vals += [k]*v
 a=np.array(vals,dtype=float)
 out={"experiment":"INSACERMO_FASHION_EXACT_CERTIFICATE_COMPLEXITY_V1",
 "contract":"60000 declared Fashion-MNIST train worlds; block4_q8",
 "law":"C(x)=minimum hitting-set cardinality over all opposite-action conflict sets D(x,y)={p:p(x)!=p(y)}",
 "certifiable":int(len(a)),"uncertifiable":len(bad),"uncertifiable_indices":bad,
 "histogram":{str(k):v for k,v in sorted(hist.items())},
 "mean_exact_probes":float(a.mean()),"median_exact_probes":float(np.median(a)),"max_exact_probes":int(a.max()),
 "mean_fraction_49":float(a.mean()/49),"unused_fraction":float(1-a.mean()/49),
 "compression_vs_full49":float(49/a.mean()),"search_nodes":nodes,"seconds":time.time()-t,
 "comparisons":{"greedy_irredundant_mean":3.7221203533922322,"shared_tree_mean":5.522566666666667}}
 out["comparisons"]["tree_over_exact"]=out["comparisons"]["shared_tree_mean"]/out["mean_exact_probes"]
 with open("FASHION_EXACT_CERTIFICATE_COMPLEXITY_V1.json","w") as f:json.dump(out,f,indent=2,sort_keys=True)
 print("RESULT",json.dumps(out,sort_keys=True))
if __name__=="__main__":main()
