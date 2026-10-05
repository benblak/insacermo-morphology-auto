#!/usr/bin/env python3
import gzip, hashlib, json, os, struct, urllib.request, itertools
import numpy as np
from collections import Counter

BASE='https://raw.githubusercontent.com/zalandoresearch/fashion-mnist/master/data/fashion/'
FILES={
 'train-images-idx3-ubyte.gz':'3aede38d61863908ad78613f6a32ed271626dd12800ba2636569512369268a84',
 'train-labels-idx1-ubyte.gz':'a04f17134ac03560a47e3764e11b92fc97de4d1bfaf8ba1a3aa29af54cc90845'
}

def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''): h.update(b)
 return h.hexdigest()

def ensure(root='fashion_data'):
 os.makedirs(root,exist_ok=True)
 for fn,s in FILES.items():
  p=os.path.join(root,fn)
  if not os.path.exists(p) or sha(p)!=s:
   urllib.request.urlretrieve(BASE+fn,p)
  assert sha(p)==s
 return root

def images(p):
 with gzip.open(p,'rb') as f:
  magic,n,r,c=struct.unpack('>IIII',f.read(16)); assert magic==2051
  return np.frombuffer(f.read(),dtype=np.uint8).reshape(n,r,c)

def labels(p):
 with gzip.open(p,'rb') as f:
  magic,n=struct.unpack('>II',f.read(8)); assert magic==2049
  y=np.frombuffer(f.read(),dtype=np.uint8); assert len(y)==n
 return y

def q8(x):
 m=x.reshape(len(x),7,4,7,4).mean(axis=(2,4)).reshape(len(x),49)
 return np.minimum(7,np.floor(m*8/256.0)).astype(np.uint8)

def exact_1_2(S,y):
 n,p=S.shape
 exact1=np.zeros(n,dtype=bool); exact2=np.zeros(n,dtype=bool)
 # 1-probe purity
 for a in range(p):
  code=S[:,a].astype(np.int16)
  for v in range(8):
   idx=np.flatnonzero(code==v)
   if len(idx) and np.all(y[idx]==y[idx[0]]): exact1[idx]=True
 # 2-probe purity (also marks 1-probe ones)
 exact2 |= exact1
 for a in range(p):
  for b in range(a+1,p):
   code=(S[:,a].astype(np.int16)*8+S[:,b].astype(np.int16))
   # vectorized purity per 64 codes
   for z in range(64):
    idx=np.flatnonzero(code==z)
    if len(idx) and np.all(y[idx]==y[idx[0]]): exact2[idx]=True
 return exact1,exact2

def build_bitsets(S,y):
 n,p=S.shape
 allmask=(1<<n)-1
 label_masks=[]
 for c in range(10):
  m=0
  for i in np.flatnonzero(y==c): m |= 1<<int(i)
  label_masks.append(m)
 match=[[0]*8 for _ in range(p)]
 for j in range(p):
  for v in range(8):
   m=0
   for i in np.flatnonzero(S[:,j]==v): m |= 1<<int(i)
   match[j][v]=m
 return allmask,label_masks,match

def greedy_certificates(S,y):
 n,p=S.shape
 allmask,label_masks,match=build_bitsets(S,y)
 sizes=np.zeros(n,dtype=np.uint8)
 unresolved=np.zeros(n,dtype=bool)
 max_steps=0
 examples=[]
 for i in range(n):
  rem=allmask ^ label_masks[int(y[i])]
  selected=[]
  unused=list(range(p))
  while rem:
   best=None; bestcnt=rem.bit_count()
   for j in unused:
    nr=rem & match[j][int(S[i,j])]
    c=nr.bit_count()
    if c<bestcnt:
     bestcnt=c; best=j
     if c==0: break
   if best is None:
    unresolved[i]=True; break
   selected.append(best); unused.remove(best)
   rem &= match[best][int(S[i,best])]
   if len(selected)>=49: break
  if not unresolved[i]:
   # irreducibility pruning: every retained probe is necessary w.r.t the rest
   changed=True
   while changed:
    changed=False
    for j in selected.copy():
     rem2=allmask ^ label_masks[int(y[i])]
     for k in selected:
      if k!=j: rem2 &= match[k][int(S[i,k])]
     if rem2==0:
      selected.remove(j); changed=True
   sizes[i]=len(selected)
   max_steps=max(max_steps,len(selected))
   if len(examples)<20 and len(selected)<=3:
    examples.append({'index':int(i),'label':int(y[i]),'probes':[int(z) for z in selected],'size':len(selected)})
 return sizes,unresolved,examples

def main():
 root=ensure()
 x=images(os.path.join(root,'train-images-idx3-ubyte.gz'))
 y=labels(os.path.join(root,'train-labels-idx1-ubyte.gz'))
 S=q8(x)
 e1,e2=exact_1_2(S,y)
 sizes,unresolved,examples=greedy_certificates(S,y)
 resolved=~unresolved
 out={
  'experiment':'INSACERMO_FASHION_INSTANCE_CERTIFICATES_V1',
  'world_contract':'exactly the 60,000 declared Fashion-MNIST training worlds',
  'probe_family':'49 non-overlapping 4x4 block means, q=8 floor256',
  'semantics':'a certificate for image i is a subset of probes whose observed values eliminate every declared world carrying a different label',
  'exact_minimum_checks':{
    'minimum_le_1':int(e1.sum()),
    'minimum_le_2':int(e2.sum()),
    'minimum_exactly_1':int(e1.sum()),
    'minimum_exactly_2':int((e2 & ~e1).sum()),
    'minimum_gt_2':int((~e2).sum())
  },
  'greedy_irredundant_upper_bound':{
    'resolved':int(resolved.sum()),
    'unresolved':int(unresolved.sum()),
    'mean_certificate_size_resolved':float(sizes[resolved].mean()) if resolved.any() else None,
    'median_certificate_size_resolved':float(np.median(sizes[resolved])) if resolved.any() else None,
    'max_certificate_size_resolved':int(sizes[resolved].max()) if resolved.any() else None,
    'mean_fraction_49_resolved':float(sizes[resolved].mean()/49) if resolved.any() else None,
    'histogram':{str(int(k)):int(v) for k,v in sorted(Counter(sizes[resolved].tolist()).items())}
  },
  'examples':examples,
  'important_scope_note':'Greedy irredundant certificates are valid exact certificates for the declared finite world set, but are upper bounds on the globally smallest certificate size unless covered by the exact 1/2-probe checks.'
 }
 with open('FASHION_INSTANCE_CERTIFICATES_V1.json','w') as f: json.dump(out,f,indent=2,sort_keys=True)
 print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__': main()
