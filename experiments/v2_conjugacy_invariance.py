#!/usr/bin/env python3
import json, math, os
from collections import Counter

N=4096
K=16
TH=0.5

def h(y):
    return math.sin(math.pi*y/2.0)**2

def logistic(x,r):
    return r*x*(1.0-x)

def tent(y):
    return 1.0-abs(1.0-2.0*y)

def signature(seed, step):
    z=seed
    m=0
    for t in range(K):
        z=step(z)
        if z>=TH:
            m |= 1<<t
    return m

def observed(step,seeds):
    return [signature(z,step) for z in seeds]

def complex_bits(signatures):
    bits=0
    for m in set(signatures):
        s=m
        while True:
            bits |= 1<<s
            if s==0: break
            s=(s-1)&m
    return bits

def feasible(bits,m):
    return ((bits>>m)&1)==1

def minimal_obstructions(bits):
    rc=Counter(); obs=[]
    for m in range(1,1<<K):
        if feasible(bits,m): continue
        ok=True
        s=m
        while s:
            lsb=s & -s
            if not feasible(bits,m^lsb):
                ok=False; break
            s-=lsb
        if ok:
            k=m.bit_count()
            rc[k]+=1
            obs.append(m)
    return rc,obs

def facets_from_observed(signatures):
    uniq=sorted(set(signatures), key=lambda m:(-m.bit_count(),-m))
    facets=[]
    for m in uniq:
        if not any((m & f)==m for f in facets):
            facets.append(m)
    return sorted(facets)

def card_profile(bits):
    out=[0]*(K+1)
    for m in range(1<<K):
        if feasible(bits,m):
            out[m.bit_count()]+=1
    return out

def render_svg(a,b,c,outpath):
    # Three compact deterministic fingerprints: feasible bundle counts by cardinality.
    W,H=1800,800
    L,R,T,B=120,80,120,100
    pw=W-L-R; ph=H-T-B
    profiles=[("LOGISTIQUE r=4",a,"#56E0FF"),("TENTE pente 2",b,"#FFD166"),("LOGISTIQUE r=3.9",c,"#FF5C8A")]
    ymax=max(max(p) for _,p,_ in profiles)
    def x(k): return L+k/K*pw
    def y(v): return T+ph-v/ymax*ph if ymax else T+ph
    s=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    s.append('<rect width="100%" height="100%" fill="#05070c"/>')
    s.append('<text x="120" y="58" fill="#f5f7ff" font-family="Arial" font-size="38" font-weight="700">INSACERMO — INVARIANCE SOUS CONJUGAISON</text>')
    s.append('<text x="122" y="94" fill="#8c99b8" font-family="Arial" font-size="19">Profil exact du complexe : nombre de paquets futurs réalisables par cardinalité</text>')
    for k in range(K+1):
        xx=x(k)
        s.append(f'<line x1="{xx:.1f}" y1="{T}" x2="{xx:.1f}" y2="{T+ph}" stroke="#111927" stroke-width="1"/>')
        s.append(f'<text x="{xx:.1f}" y="{H-55}" text-anchor="middle" fill="#71809f" font-family="Arial" font-size="14">{k}</text>')
    for name,p,col in profiles:
        pts=" ".join(f"{x(k):.1f},{y(v):.1f}" for k,v in enumerate(p))
        s.append(f'<polyline points="{pts}" fill="none" stroke="{col}" stroke-width="4" opacity="0.9"/>')
    yy=135
    for name,p,col in profiles:
        s.append(f'<line x1="1280" y1="{yy-6}" x2="1340" y2="{yy-6}" stroke="{col}" stroke-width="5"/>')
        s.append(f'<text x="1355" y="{yy}" fill="#dce4f7" font-family="Arial" font-size="17">{name}</text>')
        yy+=34
    s.append(f'<text x="{L+pw/2:.1f}" y="{H-20}" text-anchor="middle" fill="#b8c3dc" font-family="Arial" font-size="18">cardinalité du paquet futur</text>')
    s.append('</svg>')
    open(outpath,"w",encoding="utf-8").write("\n".join(s))

def summarize(name,sigs,bits):
    rc,obs=minimal_obstructions(bits)
    facets=facets_from_observed(sigs)
    return {
        "name":name,
        "samples":len(sigs),
        "distinct_signatures":len(set(sigs)),
        "feasible_bundles":bits.bit_count(),
        "facets":len(facets),
        "facet_masks":facets,
        "minimal_obstruction_counts":dict(sorted(rc.items())),
        "minimal_obstructions_total":len(obs),
        "cardinality_profile":card_profile(bits),
    }

def main():
    outdir="out/conjugacy_invariance"
    os.makedirs(outdir,exist_ok=True)
    ys=[(i+0.5)/N for i in range(N)]
    xs=[h(y) for y in ys]

    sig_t=observed(tent,ys)
    sig_l4=observed(lambda x:logistic(x,4.0),xs)
    sig_l39=observed(lambda x:logistic(x,3.9),xs)

    bits_t=complex_bits(sig_t)
    bits_l4=complex_bits(sig_l4)
    bits_l39=complex_bits(sig_l39)

    mismatches=sum(a!=b for a,b in zip(sig_t,sig_l4))
    xor_conj=(bits_t^bits_l4).bit_count()
    xor_control=(bits_t^bits_l39).bit_count()

    st=summarize("tent_slope_2",sig_t,bits_t)
    sl4=summarize("logistic_r_4",sig_l4,bits_l4)
    sl39=summarize("logistic_r_3_9",sig_l39,bits_l39)

    report={
        "schema":"INSACERMO_CONJUGACY_INVARIANCE_V0_1",
        "settings":{"N":N,"K":K,"threshold":TH,"burn_in":0},
        "paired_signature_mismatches":mismatches,
        "conjugate_complex_xor_bundle_count":xor_conj,
        "control_complex_xor_bundle_count":xor_control,
        "conjugate_complex_exact_equal":bits_t==bits_l4,
        "negative_control_complex_different":bits_t!=bits_l39,
        "tent":st,"logistic_r4":sl4,"logistic_r39":sl39
    }
    json.dump(report,open(os.path.join(outdir,"conjugacy_report.json"),"w"),indent=2)

    render_svg(st["cardinality_profile"],sl4["cardinality_profile"],sl39["cardinality_profile"],
               os.path.join(outdir,"INSACERMO_CONJUGACY_FINGERPRINT.svg"))

    print("INSACERMO_CONJUGACY_INVARIANCE_V0_1")
    print("PAIRED_SIGNATURE_MISMATCHES",mismatches,"OF",N)
    print("TENT_DISTINCT_SIGNATURES",st["distinct_signatures"])
    print("LOGISTIC4_DISTINCT_SIGNATURES",sl4["distinct_signatures"])
    print("CONJUGATE_COMPLEX_XOR_BUNDLES",xor_conj)
    print("CONJUGATE_COMPLEX_EXACT_EQUAL",bits_t==bits_l4)
    print("TENT_FEASIBLE",st["feasible_bundles"],"L4_FEASIBLE",sl4["feasible_bundles"])
    print("TENT_MINOBS",st["minimal_obstruction_counts"])
    print("L4_MINOBS",sl4["minimal_obstruction_counts"])
    print("CONTROL_L39_FEASIBLE",sl39["feasible_bundles"])
    print("CONTROL_XOR_BUNDLES",xor_control)
    print("CONTROL_DIFFERENT",bits_t!=bits_l39)
    print("CONTROL_MINOBS",sl39["minimal_obstruction_counts"])
    print("RESULT","PASS" if (bits_t==bits_l4 and bits_t!=bits_l39) else "FAIL")

if __name__=="__main__":
    main()
