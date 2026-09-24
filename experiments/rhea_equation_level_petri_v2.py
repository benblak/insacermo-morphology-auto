# INSACERMO — Rhea equation-level finite-inventory Petri stress test V2
#
# Motivation:
#   V1 depended on reaction-SMILES -> ChEBI-SMILES resolution and fully parsed
#   only 1,412 LR reactions. V2 uses Rhea's public REST equation export plus the
#   official LR-ID mapping, avoiding the SMILES participant-resolution bottleneck.
#
# Semantics remain deliberately local:
#   selected explicit LR reactions form a finite-inventory Petri module;
#   one shared participant P is consumed once by each selected branch;
#   baseline has k units of P; destruction removes one unit.
#
# Search:
#   find a clean witness up to MAX_K where every selected reaction has a distinct
#   target product and no selected reaction regenerates P. All non-empty proper
#   subbundles are executed and checked. This is NOT a whole-cell/global-Rhea
#   impossibility claim.

from __future__ import annotations
import csv, hashlib, io, itertools, re, urllib.parse, urllib.request
from collections import Counter, defaultdict

DIRECTIONS_URL="https://ftp.expasy.org/databases/rhea/tsv/rhea-directions.tsv"
NAMES_URL="https://ftp.expasy.org/databases/rhea/tsv/chebiId_name.tsv"
REST_URL="https://www.rhea-db.org/rhea/?query=&columns=rhea-id,equation&format=tsv&limit=100000"
MAX_K=10
MAX_RESOURCE_FREQ=30

CURRENCY=(
 "water","h2o","proton","hydron","dioxygen","oxygen","phosphate","diphosphate",
 "pyrophosphate","carbon dioxide","co2","ammonium","nad+","nadh","nadp+","nadph",
 "atp","adp","amp","coa","coenzyme a"
)

def dl(url):
    req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO/1.0"})
    with urllib.request.urlopen(req,timeout=240) as r: return r.read()

def tsv(raw):
    return list(csv.reader(io.StringIO(raw.decode("utf-8-sig",errors="replace")),delimiter="\t"))

def parse_dirs(raw):
    rows=tsv(raw); h={x:i for i,x in enumerate(rows[0])}
    out={}
    for r in rows[1:]:
        if len(r)<2: continue
        master=r[h["RHEA_ID_MASTER"]].replace("RHEA:","").strip()
        lr=r[h["RHEA_ID_LR"]].replace("RHEA:","").strip()
        if master and lr: out[lr]=master
    return out

def parse_names(raw):
    rows=tsv(raw); name_to_ids=defaultdict(list)
    for r in rows:
        if len(r)<2: continue
        cid=r[0].strip()
        if cid.isdigit(): cid="CHEBI:"+cid
        name=r[1].strip()
        if name: name_to_ids[name].append(cid)
    return name_to_ids

def split_equation(eq):
    # Directed rows usually contain => or <=; accept all documented separators.
    for sep in (" <=> "," => "," <= "," = "):
        if sep in eq:
            a,b=eq.split(sep,1)
            return a.strip(),b.strip(),sep.strip()
    return None

def parse_term(term):
    term=term.strip()
    # Integer stoichiometry is sufficient for this resource audit.
    m=re.match(r"^(\d+)\s+(.+)$",term)
    if m: return m.group(2).strip(),int(m.group(1))
    # Reject variable/polymer coefficients rather than guessing.
    if re.match(r"^\([^)]*[nN][^)]*\)\s+",term):
        return None
    return term,1

def parse_side(side):
    c=Counter()
    for term in side.split(" + "):
        p=parse_term(term)
        if p is None: return None
        name,coef=p
        if not name or coef<=0: return None
        c[name]+=coef
    return c

def parse_rest(raw,lr_to_master):
    rows=tsv(raw)
    if not rows: return [],0
    header=[x.lower().strip() for x in rows[0]]
    iid=next((i for i,x in enumerate(header) if "reaction" in x and "identifier" in x),0)
    ieq=next((i for i,x in enumerate(header) if "equation" in x),1)

    # The Rhea REST table exposes canonical/master reaction identifiers.
    # rhea-directions.tsv maps each master ID to its explicit LR sibling.
    master_to_lr={master:lr for lr,master in lr_to_master.items()}

    out=[]; rejected=0
    for r in rows[1:]:
        if len(r)<=max(iid,ieq): continue
        master=r[iid].replace("RHEA:","").strip()
        lr=master_to_lr.get(master)
        if lr is None:
            continue
        parts=split_equation(r[ieq].strip())
        if not parts:
            rejected+=1; continue
        lefts,rights,sep=parts
        left=parse_side(lefts); right=parse_side(rights)
        if not left or not right or left==right:
            rejected+=1; continue
        out.append({"lr":lr,"master":master,"left":left,"right":right,"equation":r[ieq].strip()})
    return out,rejected

def is_currency(name):
    n=name.lower()
    return any(x==n or x in n for x in CURRENCY)

def fire(inv,r):
    if any(inv[k]<v for k,v in r["left"].items()): return None
    z=inv.copy()
    for k,v in r["left"].items(): z[k]-=v
    for k,v in r["right"].items(): z[k]+=v
    return z

def execute(inv,rs):
    z=inv.copy()
    for r in rs:
        z=fire(z,r)
        if z is None: return None
    return z

def main():
    rawd=dl(DIRECTIONS_URL); rawn=dl(NAMES_URL); rawrest=dl(REST_URL)
    dirs=parse_dirs(rawd); name_ids=parse_names(rawn)
    reactions,rejected=parse_rest(rawrest,dirs)

    byres=defaultdict(list)
    for r in reactions:
        for p,coef in r["left"].items():
            if coef==1 and p not in r["right"] and not is_currency(p):
                byres[p].append(r)

    witnesses=[]
    for p,rs0 in byres.items():
        # one per master
        uniq=[]; seen=set()
        for r in sorted(rs0,key=lambda x:int(x["lr"])):
            if r["master"] not in seen:
                seen.add(r["master"]); uniq.append(r)
        if len(uniq)<3 or len(uniq)>MAX_RESOURCE_FREQ: continue

        # Strong clean-target filter: target is absent from every candidate left
        # and appears on the right of exactly one candidate reaction.
        left_union=set().union(*(set(r["left"]) for r in uniq))
        right_freq=Counter(x for r in uniq for x in r["right"])
        usable=[]
        for r in uniq:
            ts=sorted(x for x in r["right"] if x not in left_union and right_freq[x]==1)
            if ts: usable.append((r,ts[0]))
        if len(usable)<3: continue
        k=min(MAX_K,len(usable))
        chosen=usable[:k]
        rs=[x[0] for x in chosen]; targets=[x[1] for x in chosen]

        base=Counter()
        for r in rs: base+=r["left"]
        if base[p]!=k: continue
        dest=base.copy(); dest[p]-=1
        if execute(base,rs) is None or execute(dest,rs) is not None: continue

        proper_total=0; proper_ok=0
        for size in range(1,k):
            for idxs in itertools.combinations(range(k),size):
                proper_total+=1
                sub=[rs[i] for i in idxs]
                if execute(dest,sub) is not None: proper_ok+=1
        if proper_total!=proper_ok: continue
        repair=dest.copy(); repair[p]+=1
        if execute(repair,rs) is None: continue
        witnesses.append((-k,len(uniq),p,rs,targets,base,dest,proper_total))

    print("INSACERMO_RHEA_EQUATION_LEVEL_PETRI_V2")
    print("STATUS EXPLORATORY_BROADER_RHEA_RESOURCE_AUDIT")
    print("SEMANTICS FINITE_INVENTORY_LOCAL_PETRI_MODULE")
    print("SOURCE_DIRECTIONS_SHA256",hashlib.sha256(rawd).hexdigest())
    print("SOURCE_NAMES_SHA256",hashlib.sha256(rawn).hexdigest())
    print("SOURCE_REST_SHA256",hashlib.sha256(rawrest).hexdigest())
    print("LR_DIRECTION_IDS",len(dirs))
    print("PARSED_LR_EQUATIONS",len(reactions))
    print("REJECTED_OR_NONINTEGER_EQUATIONS",rejected)
    print("SEARCH_MAX_K",MAX_K)
    print("RESOURCES_WITH_CLEAN_WITNESS",len(witnesses))
    if not witnesses:
        print("RESULT NO_CLEAN_HIGH_ORDER_WITNESS_FOUND"); return
    witnesses.sort(key=lambda x:(x[0],x[1],x[2]))
    negk,freq,p,rs,targets,base,dest,proper_total=witnesses[0]; k=-negk
    ids=name_ids.get(p,[])
    print("WITNESS_ORDER",k)
    print("SHARED_LIMITING_RESOURCE",p)
    print("SHARED_LIMITING_RESOURCE_IDS",";".join(ids) if ids else "UNRESOLVED_NAME_ID")
    print("RESOURCE_REACTION_FREQUENCY",freq)
    print("BASELINE_RESOURCE_UNITS",base[p])
    print("AFTER_DESTRUCTION_RESOURCE_UNITS",dest[p])
    for i,(r,t) in enumerate(zip(rs,targets),1):
        print("BRANCH",i,"LR","RHEA:"+r["lr"],"MASTER","RHEA:"+r["master"])
        print("TARGET",i,t)
        print("EQUATION",i,r["equation"])
    print("FULL_BUNDLE_FEASIBLE_BEFORE",int(execute(base,rs) is not None))
    print("FULL_BUNDLE_FEASIBLE_AFTER",int(execute(dest,rs) is not None))
    print("PROPER_SUBBUNDLES_TOTAL",proper_total)
    print("PROPER_SUBBUNDLES_FEASIBLE_AFTER",proper_total)
    repair=dest.copy(); repair[p]+=1
    print("FULL_BUNDLE_FEASIBLE_AFTER_ADD_ONE_RESOURCE_REPAIR",int(execute(repair,rs) is not None))
    print("MINIMAL_LOST_BUNDLE_ORDER",k)
    print("LIMITATION local_selected_reaction_module_not_global_replenishment_or_whole_cell")
    print("RESULT COMPLETE")

if __name__=="__main__": main()
