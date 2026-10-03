from __future__ import annotations
from dataclasses import dataclass, asdict
from pathlib import Path
import json, hashlib, itertools

VERSION="INSACERMO_AUTONOMOUS_EXPLORER_MAX_0"

def h(obj):
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()).hexdigest()

def triples_upto(n:int):
    out=[]
    for b in range(1,n+1):
        for c in range(b+1,n+1):
            q,r=divmod(b*c,b+c)
            if r==0 and 1<=q<b:
                out.append((q,b,c))
    return out

def valid_removed(R:set[int], edges):
    return all(any(x in R for x in e) for e in edges)

def witness_from_removed(n,R):
    return {x for x in range(1,n+1) if x not in R}

@dataclass
class Step:
    phase:str
    n:int
    operator:str
    status:str
    details:dict
    def payload(self):
        d=asdict(self); d["event_hash"]=h(d); return d

class FreeExplorer:
    """
    Autonomous operator portfolio around a certified frontier.
    No target endpoint is supplied. The explorer:
      1. selects next unresolved frontier point,
      2. probes exact new constraints,
      3. tries a portfolio of increasingly expensive certificate-producing operators,
      4. accepts only globally reverified witnesses,
      5. refuses when its current grammar/budget cannot certify a continuation.

    This is bounded symbolic autonomy, not unrestricted general intelligence.
    """
    def __init__(self,n:int,k:int,witness:set[int],max_swap_depth:int=4):
        self.n=n; self.k=k; self.W=set(witness); self.max_swap_depth=max_swap_depth
        self.trace=[]

    def emit(self,phase,n,operator,status,details):
        e=Step(phase,n,operator,status,details).payload(); self.trace.append(e); return e

    def probe(self,n):
        edges=triples_upto(n)
        old_edges=[e for e in edges if e[2] < n]
        new_edges=[e for e in edges if e[2] == n]
        R={x for x in range(1,n) if x not in self.W}
        active=[e for e in new_edges if not any(x in R for x in e)]
        self.emit("PROBE",n,"EXACT_ENDPOINT_ENUMERATION","OBSERVED",{
            "new_edges":[list(e) for e in new_edges],
            "active_obstructions":[list(e) for e in active],
            "removed_size":len(R),
        })
        return edges,old_edges,new_edges,R,active

    def safe_add(self,n,edges,R,active):
        if active: return None
        R2=set(R)
        if not valid_removed(R2,edges): return None
        W2=witness_from_removed(n,R2)
        return ("SAFE_ADD",R2,W2,{"swap_depth":0})

    def repair_k(self,n,edges,R,active,k):
        if not active: return None
        Wold=set(self.W)
        # A: witness vertices to remove. Must hit every currently active new edge.
        candidate_sets=[]
        first=active[0]
        first_candidates=[x for x in first if x != n and x in Wold]
        for a0 in first_candidates:
            if k==1:
                As=[(a0,)]
            else:
                pool=sorted(Wold-{a0})
                As=((a0,)+rest for rest in itertools.combinations(pool,k-1))
            for A in As:
                A=set(A)
                if not all(any(x in A for x in e) for e in active):
                    continue
                Rplus=set(R)|A
                # B: previously removed vertices to restore. Need |B|=|A|.
                # Only vertices whose removal from Rplus could possibly stay covered are considered.
                restorable=[]
                for b in sorted(R):
                    ok=True
                    for e in edges:
                        if b in e:
                            hits=[x for x in e if x in Rplus]
                            if hits==[b] or (len(hits)==1 and hits[0]==b):
                                ok=False; break
                    if ok: restorable.append(b)
                if len(restorable)<k: continue
                for B in itertools.combinations(restorable,k):
                    R2=set(Rplus)
                    for b in B: R2.remove(b)
                    if len(R2)!=len(R): continue
                    if valid_removed(R2,edges):
                        W2=witness_from_removed(n,R2)
                        if len(W2)==self.k+1:
                            return (f"REPAIR_{k}SWAP",R2,W2,{
                                "swap_depth":k,
                                "remove_from_witness":sorted(A),
                                "restore_to_witness":list(B),
                            })
        return None

    def step(self):
        n=self.n+1
        edges,old_edges,new_edges,R,active=self.probe(n)

        portfolio=[("SAFE_ADD",lambda:self.safe_add(n,edges,R,active))]
        for k in range(1,self.max_swap_depth+1):
            portfolio.append((f"REPAIR_{k}SWAP",lambda k=k:self.repair_k(n,edges,R,active,k)))

        for name,op in portfolio:
            self.emit("PLAN",n,name,"TRY",{"active_obstruction_count":len(active)})
            ans=op()
            if ans is None:
                self.emit("PLAN",n,name,"NO_CERTIFICATE",{})
                continue
            opname,R2,W2,detail=ans
            # independent global replay before ACT
            if not valid_removed(R2,edges):
                self.emit("PLAN",n,opname,"REJECTED_BY_GLOBAL_REPLAY",detail)
                continue
            self.W=W2; self.n=n; self.k+=1
            return self.emit("ACT",n,opname,"EXACT_FRONTIER_EXTENDED",{
                **detail,
                "new_exact_n":self.n,
                "new_exact_k":self.k,
                "witness_size":len(self.W),
                "global_edge_count":len(edges),
                "global_replay":"PASS",
                "upper_rule":"f(n) <= f(n-1)+1",
            })

        return self.emit("REFUSE",n,"PORTFOLIO_EXHAUSTED","EXACTNESS_NOT_CERTIFIED",{
            "max_swap_depth":self.max_swap_depth,
            "active_obstructions":[list(e) for e in active],
            "next_question":"EXPAND_OPERATOR_GRAMMAR_OR_PROVE_STRONGER_BOUND",
            "frontier_preserved":[self.n,self.k],
        })

    def run(self,max_frontier_steps=8):
        for _ in range(max_frontier_steps):
            e=self.step()
            if e["phase"]=="REFUSE": break
        out={"version":VERSION,"final_exact_n":self.n,"final_exact_k":self.k,"trace":self.trace}
        out["run_hash"]=h(out)
        return out

def verify_run(out):
    body={k:v for k,v in out.items() if k!="run_hash"}
    if out.get("run_hash")!=h(body): return False
    for e in out.get("trace",[]):
        eb={k:v for k,v in e.items() if k!="event_hash"}
        if e.get("event_hash")!=h(eb): return False
    return True
