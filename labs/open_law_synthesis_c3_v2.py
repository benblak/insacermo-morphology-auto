#!/usr/bin/env python3
"""INSACERMO MAX open-formula discovery LAB, with unchanged historical C3.

The learner is given NO explicit list of candidate laws or true coefficients:
a private process supplies membership-query answers from generated 6-variable
Boolean functions.  A declared REPRESENTATION grammar (algebraic normal form,
ANF) and degree-complexity ladder is still supplied: this is not unrestricted
scientific discovery. The deterministic evaluation design consists of all
subsets of each order 0,1,2,3,4,5,6. Every low-degree hypothesis receives
adversarial attempts at falsification on the next order. Higher-degree
monomials vanish on lower-Hamming-weight queries. This means absence of
counterexamples does NOT establish universality, a core boundary.

After 22 queries a degree<=2 law can be exactly reconstructed *conditional
on the degree bound*. Degree-3,4,6 counterexamples may require 42,57,64
total queries. A 6-way interaction is undetectable before x=63 when testing
weight <=5. The external ANF synthesizer is NOT the historical C3 solver.
C3 certifies a two-completion ambiguity and a single discriminating query
to safely decide the bit at x=63; it does not certify the learned law.
"""
from __future__ import annotations
import hashlib, itertools,json,subprocess,sys
from pathlib import Path
from insacermo_one_engine import decide,replay,validate

HISTORICAL_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
ORACLE=Path(__file__).with_name("open_law_private_oracle_v2.py")
N=6
DOMAIN=tuple(range(1<<N))
MAX_SUPPORTED_DEGREE=6

def hamming(x):return x.bit_count()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(",",":")).encode()

def enumerate_layers():
    return [tuple(x for x in DOMAIN if hamming(x)==k) for k in range(N+1)]

LAYERS=enumerate_layers()
assert [len(x) for x in LAYERS]==[1,6,15,20,15,6,1]
assert len({v for row in LAYERS for v in row})==64

class Oracle:
    def __init__(self,secret_path,case):
        self.process=subprocess.Popen(
            [sys.executable,str(ORACLE),"--secret-file",str(secret_path),"--case",case],
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            bufsize=1,text=True)
        self.memo={}
        self.queries=[]
    def ask(self,x):
        if x in self.memo:return self.memo[x]
        self.process.stdin.write(json.dumps({"x":x})+"\n")
        self.process.stdin.flush()
        line=self.process.stdout.readline()
        if not line:raise RuntimeError("ORACLE_DID_NOT_ANSWER")
        response=json.loads(line)
        assert response.get("x")==x and response.get("y") in (0,1),response
        self.memo[x]=response["y"]
        self.queries.append(x)
        return response["y"]
    def finish(self):
        self.process.stdin.close()
        assert self.process.wait(timeout=15)==0

def synthesize_degree(answers,degree):
    """Derive ANF coefficients by Möbius recursion on all subsets x<=degree."""
    coefs={}
    for k in range(degree+1):
        for x in LAYERS[k]:
            assert x in answers
            s=answers[x]
            for m,a in coefs.items():
                if m!=x and (m&x)==m:s^=a
            coefs[x]=s
    return tuple(sorted(k for k,v in coefs.items() if v))

def evaluate(terms,x):
    return sum((x&t)==t for t in terms)%2

def verify_up_to(answers,terms,maxdegree):
    return all(evaluate(terms,x)==answers[x]
        for x in DOMAIN if x in answers and hamming(x)<=maxdegree)

def two_completion_contract(probes,one_probe):
    """Identical on 7 irrelevant probes, diverging only on the final input."""
    assert len(probes)==7 and len(set(probes))==7
    assert all(q!=63 for q in probes)
    qs=probes+[63] if one_probe else probes
    # two potential worlds whose target output is 0 and 1
    observations=[[1,1] for _ in probes]+([[1,2]] if one_probe else [])
    m=dict(worldCount=2,actionCount=2,probeCount=len(qs),
        good=[[True,False],[False,True]],
        sense=observations,
        nextFalse=[[0,1] for _ in qs],
        nextTrue=[[0,1] for _ in qs],
        actionCost=[0,0],probeCost=[1]*len(qs),
        lowerWorld=[0,1],upperWorld=[0,1],
        mustActions=[0,1],mayActions=[0,1],
        probeKinds=["PROBE"]*len(qs),
        depth=1,budget=1,reserve=4,debt=0)
    validate(m)
    return m

def certified_local_decision(out):
    # A subtle but important test: after 63 possible observations, the last
    # bit remains underdetermined by arbitrary functions; the two completions
    # agree on EVERY previously queried input, not only 7 represented probes.
    # C3's 7 irrelevant binary probes are a bounded witness, NOT a proof
    # that all arbitrary 64-bit functions were formally quantified in Lean.
    others=[0,1,2,3,4,5,6]
    folder=out/"lean_receipts"/"unknown_bit_refuse"
    r=decide(two_completion_contract(others,False),folder)
    assert r["verdict"]=="REFUSE_ROBUST" and not r["authorized"]
    assert replay(folder)
    reject_hash=r["receipt_sha256"]
    folder=out/"lean_receipts"/"unknown_bit_probe"
    r=decide(two_completion_contract(others,True),folder)
    assert r["verdict"]=="PROBE" and r["authorized"] and r["first_step_only"]
    assert r["plan"]["probe"]==7
    assert replay(folder)
    p=folder/"receipt.json"
    pristine=p.read_bytes()
    try:
        broken=pristine.replace(b'"authorized":true',b'"authorized":false')
        assert broken!=pristine
        p.write_bytes(broken)
        assert not replay(folder)
    finally:p.write_bytes(pristine)
    assert replay(folder)
    assert not replay(folder,lean_binary="/missing-lean")
    return dict(refusal_sha256=reject_hash,probe_sha256=r["receipt_sha256"],
        lean_certificates_replayed=2)

def run(out,secret_path):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    git_blob=hashlib.sha1(b"blob "+str(len(engine)).encode()+bytes([0])+engine).hexdigest()
    assert git_blob==HISTORICAL_BLOB,("HISTORICAL_C3_CHANGED",git_blob)
    assert secret_path.exists()
    secret_commitment=hashlib.sha256(secret_path.read_bytes()).hexdigest()
    cases=[]
    for case_id in ("case_0","case_1","case_2","case_3"):
        oracle=Oracle(secret_path,case_id)
        evidence={}
        layers=[]
        cumulative=[]
        for d, layer in enumerate(LAYERS):
            mismatches=[]
            # Falsify previously derived formula with strictly UNQUERIED probes
            previous= synthesize_degree(evidence,d-1) if d>0 else ()
            for x in layer:
                assert x not in evidence
                y=oracle.ask(x)
                evidence[x]=y
                if d>0 and evaluate(previous,x)!=y:
                    mismatches.append(x)
            terms=synthesize_degree(evidence,d)
            assert verify_up_to(evidence,terms,d)
            cumulative.append(len(evidence))
            layers.append(dict(degree=d,layer_size=len(layer),
                newly_observed_contradictions=len(mismatches),
                first_counterexample=(mismatches[0] if mismatches else None),
                cumulative_unique_questions=len(evidence),
                synthesized_monomial_count=len(terms),
                synthesized_maximum_degree=max((hamming(t) for t in terms),default=0),
                provisional_model_sha256=hashlib.sha256(canonical(terms)).hexdigest()))
            if d in (2,3,4,5):
                print("BLIND_SYNTHESIS",case_id,"degree",d,
                    "counterexamples",len(mismatches),
                    "observed",len(evidence),"terms",len(terms),flush=True)
        oracle.finish()
        assert oracle.queries==[x for layer in LAYERS for x in layer]
        assert cumulative==[1,7,22,42,57,63,64]
        final_terms=synthesize_degree(evidence,6)
        assert all(evaluate(final_terms,x)==evidence[x] for x in DOMAIN)
        # Independent transform via standard iterative in-place GF(2)
        a=[evidence[i] for i in DOMAIN]
        for bit in range(N):
            for x in DOMAIN:
                if x&(1<<bit):a[x]^=a[x^(1<<bit)]
        independent_terms=[i for i in DOMAIN if a[i]]
        assert tuple(independent_terms)==final_terms
        after_63=synthesize_degree({x:evidence[x] for x in DOMAIN if x!=63},5)
        alternatives=(evaluate(after_63,63),1^evaluate(after_63,63))
        assert set(alternatives)=={0,1}
        cases.append(dict(id=case_id,secret_not_accessed_by_learner=True,
            layers=layers,final_terms=list(final_terms),
            max_identified_degree=max((hamming(i) for i in final_terms),default=0),
            last_point_undetermined_after_63_queries=True,
            final_observed_last_bit=evidence[63],
            additional_query_resolves_last_bit=True,
            output_table_sha256=hashlib.sha256(bytes(evidence[i] for i in DOMAIN)).hexdigest()))
        print("COMPLETED_ANF",case_id,"degree",cases[-1]["max_identified_degree"],
            "terms",len(final_terms),"queries",len(evidence),flush=True)
    formal=certified_local_decision(out)
    # A withheld secret reveal is deferred until AFTER all predicted outcomes
    # and verification checks. Because the test is retrospective, this audit
    # is not a future-law validation of arbitrary input beyond 0..63.
    secrets=json.loads(secret_path.read_text())
    revealed=[]
    for rec in cases:
        actual=secrets[rec["id"]]
        assert rec["final_terms"]==actual,(rec["id"],"SECRET_MISMATCH")
        revealed.append(dict(id=rec["id"],true_terms=actual,
            true_max_degree=rec["max_identified_degree"],
            discovered_equals_true=True))
    assert sorted(rec["max_identified_degree"] for rec in cases)==[2,3,4,6],cases
    result=dict(experiment="Open ANF synthesis without enumerated candidate laws",
        n_boolean_inputs=6,n_possible_input_settings=64,
        model_grammar="all Boolean polynomials in GF(2) ANF, degrees 0..6",
        predeclared_probe_ladder=[1,6,15,20,15,6,1],
        layer_cumulative_questions=[1,7,22,42,57,63,64],
        generated_secret_sha256=secret_commitment,
        cases=cases,independent_mobius_transform_verified=True,
        secret_reveal= revealed,
        historical_C3_git_blob=git_blob,
        historical_C3_certificates=formal,
        limitations=[
          "True laws are synthetic 6-input Boolean functions; they are not new physical discoveries.",
          "The learner has a supplied universal ANF representation and deterministic subset enumeration, not a fully self-invented language.",
          "The learner never enumerates a list of candidate formulas but reconstructs coefficients from measurements.",
          "The private oracle is a separate process with secret file; source code is accessible to anyone auditing the CI repository.",
          "No unrestricted finite-query algorithm can certify an arbitrary unseen Boolean input without assumptions; an isolated input may differ.",
          "C3 only certifies the small declared two-world ambiguity and action-probe contract, not global ANF synthesis or independent physical truth.",
          "This is exactly known GF(2) Möbius inversion, not a new mathematical theorem.",
          "No neural training, but explicit algebraic identification with query costs up to all 64 inputs.",
          "All 64 possible inputs are eventually queried, so final full-domain equality is exhaustive, not generalization."
        ])
    (out/"audit.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print("OPEN_LAW_NO_CATALOGUE_EXACT_SUCCESS",
        "degrees",[x["max_identified_degree"] for x in cases],
        "Lean",formal["lean_certificates_replayed"],flush=True)

if __name__=="__main__":
    if len(sys.argv)!=3:
        raise SystemExit("usage: script.py OUT_DIRECTORY SECRET_FILE")
    run(sys.argv[1],Path(sys.argv[2]))
