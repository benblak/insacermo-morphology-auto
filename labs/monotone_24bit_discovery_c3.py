#!/usr/bin/env python3
"""INSACERMO MAX isolated 24-bit unknown-law boundary experiment.

A query-only device hides an unknown monotone 24-bit Boolean function.
Learner gets NO clause list. It discovers minimal positive witnesses using
monotonicity and tests transversals of all known terms until negative.
Upward and downward closures certify exact known regions IF the declared
monotonicity premise holds. Coverage computed with Shannon-style recursive
cube union (not 16,777,216 enumerated inputs). Independent final audit
compares reconstructed terms with generator AFTER all conclusions are frozen.

Historical C3 unchanged; only three tiny two-world contracts are Lean
certified. No false claim that Lean verified the 24-bit symbolic inference.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib,json,subprocess,sys
from insacermo_one_engine import decide,replay,validate

N=24;FULL=(1<<N)-1;WORLD_COUNT=1<<N
HISTORIC_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
ORACLE=Path(__file__).with_name("monotone_24bit_private_oracle.py")
SEED=177
MAX_ORACLE_CALLS=1000

class Device:
    def __init__(self,adversarial=False):
        args=[sys.executable,str(ORACLE),"--seed",str(SEED)]
        if adversarial:args.append("--adversarial")
        self.p=subprocess.Popen(args,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,text=True,bufsize=1)
        self.answers={}
        self.order=[]
    def ask(self,x):
        assert type(x)==int and 0<=x<=FULL
        if x in self.answers:return self.answers[x]
        assert len(self.order)<MAX_ORACLE_CALLS
        self.p.stdin.write(json.dumps({"x":x})+"\n");self.p.stdin.flush()
        line=self.p.stdout.readline()
        assert line
        d=json.loads(line)
        assert d.get("x")==x and d.get("y") in (0,1),d
        self.order.append(x);self.answers[x]=d["y"]
        return d["y"]
    def close(self):
        self.p.stdin.close()
        assert self.p.wait(timeout=15)==0

def irredundant(positives,negatives):
    # Positive constraints are upward cones, negative constraints downward.
    p=sorted(x for x in set(positives)
        if not any(y!=x and (y&x)==y for y in positives))
    n=sorted(x for x in set(negatives)
        if not any(y!=x and (y&x)==x for y in negatives))
    return p,n

def cube_union_count(cubes):
    """Exact symbolic model-counting with disjoint Shannon cofactoring.
    Each cube is (required-ones, required-zeros). No pointwise enumeration.
    """
    cache={}
    def rec(cubes,free):
        key=(cubes,free)
        if key in cache:return cache[key]
        if not cubes:return 0
        if (0,0) in cubes:return 1<<free.bit_count()
        frequency={}
        for one,zero in cubes:
            for bit in range(N):
                mask=1<<bit
                if (one|zero)&mask:
                    frequency[mask]=frequency.get(mask,0)+1
        assert frequency
        bit=max(frequency,key=lambda b:(frequency[b],-b))
        total=0
        for val in (0,1):
            restricted=set()
            for one,zero in cubes:
                if val==0 and one&bit:continue
                if val==1 and zero&bit:continue
                restricted.add((one&~bit,zero&~bit))
            total+=rec(tuple(sorted(restricted)),free&~bit)
        cache[key]=total
        return total
    result=rec(tuple(sorted(set(cubes))),FULL)
    return result,len(cache)

def snapshot(positives,negatives):
    p,n=irredundant(positives,negatives)
    yes,yn=cube_union_count([(x,0) for x in p])
    no,nn=cube_union_count([(0,FULL^x) for x in n])
    assert yes+no<=WORLD_COUNT
    return dict(probed_positive_witnesses=len(positives),
        probed_negative_witnesses=len(negatives),
        minimal_positive_count=len(p),maximal_negative_count=len(n),
        certified_positive_configurations=yes,
        certified_negative_configurations=no,
        unresolved_configurations=WORLD_COUNT-yes-no,
        symbolic_cache_states=yn+nn,
        minimal_positive_terms=p,maximal_negative_terms=n)

def reduce_positive(device,x,positives,negatives):
    assert device.ask(x)==1
    # Sequential deletion to find a minimal positive clause. Under
    # monotonicity, deletion order does not affect final minimality.
    for b in range(N):
        if x>>b&1:
            v=x^(1<<b)
            y=device.ask(v)
            if y==1:x=v
            else:negatives.append(v)
    positives.append(x)
    return x

def next_falsifier(device,positives,negatives):
    p,n=irredundant(positives,negatives)
    # A possible NEW minimal positive term must avoid containing any
    # already found minimal positive term. Therefore it must omit at
    # least one bit from EACH known term. Enumerate hitting choices;
    # this is exponential in the number/sizes of terms, and not
    # bounded-efficiency for arbitrary monotone functions.
    candidates=product(*[
        [1<<bit for bit in range(N) if (mask>>bit)&1] for mask in p])
    count=0
    for picks in candidates:
        omissions=0
        for onebit in picks:omissions|=onebit
        x=FULL^omissions
        # Negative known downward cone: no oracle query necessary.
        if any((x&negative)==x for negative in n):continue
        count+=1
        y=device.ask(x)
        if y:
            q=reduce_positive(device,x,positives,negatives)
            assert not any((q&old)==old for old in p)
            return q,count
        negatives.append(x)
    return None,count

def decision_model(sense,good):
    w=2;q=len(sense);acts=len(good[0])
    m=dict(worldCount=2,actionCount=acts,probeCount=q,
        good=good,sense=sense,
        nextFalse=[[0,1] for _ in range(q)],
        nextTrue=[[0,1] for _ in range(q)],
        actionCost=[0]*acts,probeCost=[1]*q,
        lowerWorld=[0,1],upperWorld=[0,1],
        mustActions=list(range(acts)),mayActions=list(range(acts)),
        probeKinds=["PROBE"]*q,depth=1,budget=1,reserve=4,debt=0)
    validate(m);return m

def c3_certificates(out):
    options=[
       ("same_observation_opposite_actions",
        [[1,1]],[[True,False],[False,True]],"REFUSE_ROBUST"),
       ("discriminating_observation",
        [[1,2]],[[True,False],[False,True]],"PROBE"),
       ("both_worlds_permit_same_action",
        [[1,1]],[[True],[True]],"ACT")
    ]
    records=[]
    for name,sense,good,expected in options:
        folder=out/"C3_Lean_receipts"/name
        result=decide(decision_model(sense,good),folder)
        assert result["verdict"]==expected,(name,result)
        assert replay(folder)
        records.append(dict(name=name,verdict=expected,
            receipt_sha256=result["receipt_sha256"]))
    folder=out/"C3_Lean_receipts"/"discriminating_observation"
    assert not replay(folder,lean_binary="/missing-lean")
    p=folder/"receipt.json";original=p.read_bytes()
    try:
        altered=original.replace(b'"authorized":true',b'"authorized":false')
        assert altered!=original
        p.write_bytes(altered);assert not replay(folder)
    finally:p.write_bytes(original)
    assert replay(folder)
    return records

def experiment(root):
    out=Path(root);out.mkdir(parents=True,exist_ok=True)
    source=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    sha=hashlib.sha1(b"blob "+str(len(source)).encode()+bytes([0])+source).hexdigest()
    assert sha==HISTORIC_BLOB
    device=Device()
    positives=[];negatives=[]
    assert device.ask(0)==0;negatives.append(0)
    assert device.ask(FULL)==1
    initial=reduce_positive(device,FULL,positives,negatives)
    history=[dict(event="first_minimal_positive",oracle_questions=len(device.order),
        summary=snapshot(positives,negatives))]
    attempts=0
    while True:
        q,nc=next_falsifier(device,positives,negatives)
        attempts+=nc
        if q is None:break
        history.append(dict(event="new_minimal_positive",witness=q,
            oracle_questions=len(device.order),
            summary=snapshot(positives,negatives)))
        print("MINIMAL_WITNESS",len(history),q.bit_count(),
            "queries",len(device.order),flush=True)
    final=snapshot(positives,negatives)
    device.close()
    assert final["unresolved_configurations"]==0
    assert len(device.order)<512
    assert final["minimal_positive_count"]==4
    assert final["maximal_negative_count"]>0
    # No ordinary exhaustive scan of 2^24 inputs.
    # Independent closed-form count when minterms are disjoint.
    terms=final["minimal_positive_terms"]
    assert all((a&b)==0 for i,a in enumerate(terms) for b in terms[i+1:])
    complement=1
    for p in terms:
        complement*= (1<<p.bit_count())-1
    count_negative=(1<< (N-sum(p.bit_count() for p in terms)))*complement
    assert count_negative==final["certified_negative_configurations"]
    assert WORLD_COUNT-count_negative==final["certified_positive_configurations"]
    # Control against independent generator specification AFTER discovery.
    from importlib.util import spec_from_file_location,module_from_spec
    spec=spec_from_file_location("audit_oracle",ORACLE)
    mod=module_from_spec(spec);spec.loader.exec_module(mod)
    truth=set(mod.clauses(SEED))
    assert set(terms)==truth,("SECRET_GENERATOR_MISMATCH",terms,truth)
    # Nonmonotone version: selected minimal positive p is subset of
    # a false x, falsifying the monotonicity assumption. Existence of
    # a witness doesn't imply every limited-query policy will find it.
    adversarial=Device(adversarial=True)
    contradiction_target=FULL^(1<<23)
    chosen=next(p for p in terms if (p&contradiction_target)==p)
    assert adversarial.ask(chosen)==1
    assert adversarial.ask(contradiction_target)==0
    adversarial.close()
    violation={"positive_subset":chosen,"negative_superset":contradiction_target,
       "positive_subset_label":1,"negative_superset_label":0,
       "monotonicity_contradicted":True,"global_certificate_authorized":False}
    c3=c3_certificates(out)
    record=dict(test="UNKNOWN_24_BIT_LAW_CONDITIONAL_EXACT_COVERAGE",
      dated="2026-11-17",source_engine_blob=sha,
      hypothesis="Boolean isotonicity (monotonicity under bitwise subset inclusion)",
      input_bits=N,total_input_configurations=WORLD_COUNT,
      generating_clause_list_not_supplied_to_learner=True,
      synthetic_oracle_seed=SEED,oracle_unique_queries=len(device.order),
      oracle_unique_query_fraction=len(device.order)/WORLD_COUNT,
      first_minimal_positive=initial,
      iterative_search_candidate_attempts=attempts,
      progression=history,final=final,
      independent_exact_count_verified=True,
      generator_reveal_after_freeze=sorted(truth),
      all_generated_clauses_recovered=True,
      monotonicity_falsification_control=violation,
      compact_historical_C3_Lean_certificates=c3,
      limitations=[
        "Synthetic monotone Boolean world; not an undiscovered real physical law.",
        "Monotonicity is an assumed structural contract, not established by finite probes.",
        "The learner knows the 24-bit Boolean domain, and may exploit an exact subset order.",
        "The generating law has only four disjoint clauses by construction.",
        "The candidate generation uses exponential hitting-set enumeration and may become costly.",
        "Final zero unresolved is only for the monotone version space; without monotonicity arbitrary functions remain possible.",
        "Independent truth audit imports source only AFTER the learner finishes, to verify experimental correctness.",
        "The adversarial counterexample is deliberately queried: not guaranteed to be detected for an arbitrary rare nonmonotone exception.",
        "The historical C3 worldCount<=8 remains unchanged; C3 Lean certifies three separate local finite two-world contracts, not 2^24 symbolic coverage.",
        "Symbolic counting is Python checked by a second closed-form count here, not Lean kernel verified."
      ])
    (out/"audit.json").write_text(json.dumps(record,indent=2,ensure_ascii=False)+"\n")
    print("MONOTONE_LAW_DISCOVERY_SUCCESS",
        "QUERY_COUNT",len(device.order),
        "POSITIVES",final["certified_positive_configurations"],
        "NEGATIVES",final["certified_negative_configurations"],
        "UNRESOLVED",final["unresolved_configurations"],
        "LEAN_CERTS",len(c3),flush=True)
    print("MONOTONICITY_ASSUMPTION_BROKEN_CONTROL",violation,flush=True)
    return record

if __name__=="__main__":
    experiment(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_monotone")
