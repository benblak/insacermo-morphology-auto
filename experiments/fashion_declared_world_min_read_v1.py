#!/usr/bin/env python3
import gzip, hashlib, json, os, struct, urllib.request
import numpy as np
from collections import Counter
BASE='https://raw.githubusercontent.com/zalandoresearch/fashion-mnist/master/data/fashion/'
FILES={
 'train-images-idx3-ubyte.gz':'3aede38d61863908ad78613f6a32ed271626dd12800ba2636569512369268a84',
 'train-labels-idx1-ubyte.gz':'a04f17134ac03560a47e3764e11b92fc97de4d1bfaf8ba1a3aa29af54cc90845'}

def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def ensure(root='fashion_data'):
 os.makedirs(root,exist_ok=True)
 for fn,s in FILES.items():
  p=os.path.join(root,fn)
  if not os.path.exists(p) or sha(p)!=s: urllib.request.urlretrieve(BASE+fn,p)
  assert sha(p)==s
 return root
def images(p):
 with gzip.open(p,'rb') as f:
  magic,n,r,c=struct.unpack('>IIII',f.read(16)); assert magic==2051
  return np.frombuffer(f.read(),dtype=np.uint8).reshape(n,r,c)
def labels(p):
 with gzip.open(p,'rb') as f:
  magic,n=struct.unpack('>II',f.read(8)); assert magic==2049
  y=np.frombuffer(f.read(),dtype=np.uint8); assert len(y)==n; return y
def sigs(x,q):
 m=x.reshape(len(x),7,4,7,4).mean(axis=(2,4)).reshape(len(x),49)
 return np.minimum(q-1,np.floor(m*q/256.0)).astype(np.uint8)

def impurity(y):
 c=np.bincount(y,minlength=10).astype(np.int64)
 n=len(y)
 return (n*n - int((c*c).sum()))//2

def build_tree(S,y,q):
 N=len(y); depths=np.zeros(N,dtype=np.uint8); leaf_kind=np.zeros(N,dtype=np.uint8)
 nodes=0; maxdepth=0
 stack=[(np.arange(N,dtype=np.int32), tuple(range(49)), 0)]
 while stack:
  idx,probes,d=stack.pop(); nodes+=1; maxdepth=max(maxdepth,d)
  labs=y[idx]
  if np.all(labs==labs[0]):
   depths[idx]=d; leaf_kind[idx]=1; continue
  if not probes:
   depths[idx]=d; leaf_kind[idx]=2; continue
  base=impurity(labs)
  best=None; bestscore=None
  for p in probes:
   vals=S[idx,p]
   score=0
   for v in range(q):
    sub=idx[vals==v]
    if len(sub)>1: score += impurity(y[sub])
   key=(score,p)
   if bestscore is None or key<bestscore: bestscore=key; best=p
  if bestscore[0] >= base:
   depths[idx]=d; leaf_kind[idx]=2; continue
  vals=S[idx,best]
  rem=tuple(p for p in probes if p!=best)
  for v in range(q):
   sub=idx[vals==v]
   if len(sub): stack.append((sub,rem,d+1))
 return depths,leaf_kind,nodes,maxdepth

def summarize(depths,kind):
 act=kind==1; refuse=kind==2
 return {
  'n':len(kind),'act':int(act.sum()),'refuse':int(refuse.sum()),'coverage':float(act.mean()),
  'mean_probes_all':float(depths.mean()),'mean_fraction_49':float(depths.mean()/49),
  'max_probes':int(depths.max()),'mean_probes_act':float(depths[act].mean()) if act.any() else None,
  'mean_probes_refuse':float(depths[refuse].mean()) if refuse.any() else None,
  'act_depth_hist':{str(int(k)):int(v) for k,v in sorted(Counter(depths[act].tolist()).items())},
  'refuse_depth_hist':{str(int(k)):int(v) for k,v in sorted(Counter(depths[refuse].tolist()).items())},
 }

def verify(depths,kind):
 assert np.all(kind>0)
 return {'all_rows_terminal':True,'act_plus_refuse':int((kind>0).sum()),'zero_probe_act':int(((kind==1)&(depths==0)).sum())}

def main():
 root=ensure(); x=images(os.path.join(root,'train-images-idx3-ubyte.gz')); y=labels(os.path.join(root,'train-labels-idx1-ubyte.gz'))
 result={'experiment':'INSACERMO_FASHION_DECLARED_WORLD_MIN_READ_V1','world_contract':'exactly the 60,000 declared Fashion-MNIST training worlds; no claim on unseen images','planner':'deterministic greedy ambiguity-reduction tree; ACT leaves are label-pure, REFUSE when remaining probes cannot reduce ambiguity','families':{}}
 for q in [2,4,8]:
  print('Q',q,flush=True); S=sigs(x,q); d,k,nodes,md=build_tree(S,y,q); s=summarize(d,k); s['nodes']=nodes;s['tree_max_depth']=md;s['verification']=verify(d,k); result['families'][f'block4_q{q}']=s; print(json.dumps(s,sort_keys=True),flush=True)
 with open('FASHION_DECLARED_WORLD_MIN_READ_V1.json','w') as f: json.dump(result,f,indent=2,sort_keys=True)
 print('RESULT',json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
