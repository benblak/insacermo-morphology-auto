#!/usr/bin/env python3
import csv, json, math, os
import numpy as np

R0, R1, STEP = 2.8, 4.0, 0.001
N_SEEDS = 1024
BURN = 1500
K = 12
THRESHOLDS = (0.4, 0.5, 0.6)
TOP_N = 25
SUPPRESS_RADIUS = 0.004
MATCH_TOL = 0.01

KNOWN = [
    ("r=3", 3.0),
    ("1+sqrt(6)", 1 + math.sqrt(6)),
    ("period-8 onset", 3.544090359),
    ("period-16 onset", 3.564407266),
    ("Feigenbaum accumulation", 3.569945672),
    ("period-3 window", 1 + math.sqrt(8)),
]

def precompute_downclosures():
    out=[0]*(1<<K)
    for m in range(1<<K):
        bits=0
        s=m
        while True:
            bits |= 1 << s
            if s==0: break
            s=(s-1)&m
        out[m]=bits
    return out

CLOSURE = precompute_downclosures()

def signatures_three_contracts(r):
    x=(np.arange(N_SEEDS,dtype=np.float64)+0.5)/N_SEEDS
    for _ in range(BURN):
        x=r*x*(1-x)
    masks={c:np.zeros(N_SEEDS,dtype=np.uint16) for c in THRESHOLDS}
    for t in range(K):
        x=r*x*(1-x)
        bit=np.uint16(1<<t)
        for c in THRESHOLDS:
            masks[c] |= ((x>=c).astype(np.uint16)*bit)
    return {c:np.unique(masks[c]) for c in THRESHOLDS}

def complex_bits(signatures):
    z=0
    for m in signatures:
        z |= CLOSURE[int(m)]
    return z

def local_maxima(rs, vals):
    out=[]
    for i in range(1,len(vals)-1):
        if vals[i] > 0 and vals[i] >= vals[i-1] and vals[i] >= vals[i+1]:
            # plateau handling: keep only leftmost strict entrance or unique max
            if vals[i] > vals[i-1] or vals[i] > vals[i+1]:
                out.append((vals[i], rs[i], i))
    return out

def select_peaks(rs, vals):
    cand=sorted(local_maxima(rs,vals), key=lambda z:(-z[0], z[1]))
    chosen=[]
    for score,r,i in cand:
        if all(abs(r-r2) > SUPPRESS_RADIUS+1e-12 for _,r2,_ in chosen):
            chosen.append((score,r,i))
            if len(chosen)>=TOP_N:
                break
    return chosen

def esc(s):
    return s.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")

def render(rs, consensus, peaks, outpath, with_refs):
    W,H=2200,1000
    L,R,T,B=140,90,130,130
    pw=W-L-R
    ph=H-T-B
    vmax=max(consensus) if max(consensus)>0 else 1.0
    def xc(r): return L+(r-R0)/(R1-R0)*pw
    def yc(v): return T+ph-(v/vmax)*ph
    s=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    s.append('<rect width="100%" height="100%" fill="#05070c"/>')
    title="INSACERMO — DÉTECTEUR AVEUGLE DE RUPTURES FUTURES"
    s.append(f'<text x="{L}" y="58" fill="#f5f7ff" font-family="Arial" font-size="38" font-weight="700">{title}</text>')
    sub="Distance exacte entre complexes de futurs adjacents • médiane des contrats c=0,4 / 0,5 / 0,6"
    s.append(f'<text x="{L}" y="94" fill="#8d99b7" font-family="Arial" font-size="19">{sub}</text>')
    for frac in [0,.25,.5,.75,1]:
        y=T+ph-frac*ph
        s.append(f'<line x1="{L}" y1="{y:.1f}" x2="{W-R}" y2="{y:.1f}" stroke="#162033" stroke-width="1"/>')
        s.append(f'<text x="{L-18}" y="{y+5:.1f}" text-anchor="end" fill="#74819e" font-family="Arial" font-size="15">{frac*vmax:.3f}</text>')
    pts=" ".join(f"{xc(r):.1f},{yc(v):.1f}" for r,v in zip(rs,consensus))
    s.append(f'<polyline points="{pts}" fill="none" stroke="#55E3FF" stroke-width="3"/>')
    # area under curve
    area=f"{xc(rs[0]):.1f},{T+ph:.1f} "+pts+f" {xc(rs[-1]):.1f},{T+ph:.1f}"
    s.append(f'<polygon points="{area}" fill="#126a8d" opacity="0.13"/>')
    for rank,(score,r,i) in enumerate(peaks,1):
        x=xc(r); y=yc(score)
        s.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="7" fill="#FFD166" stroke="#fff2b8" stroke-width="1.5"/>')
        if rank<=12:
            s.append(f'<text x="{x+8:.1f}" y="{y-9:.1f}" fill="#FFD166" font-family="Arial" font-size="14">{rank}</text>')
    if with_refs:
        for lab,rv in KNOWN:
            x=xc(rv)
            s.append(f'<line x1="{x:.1f}" y1="{T}" x2="{x:.1f}" y2="{T+ph}" stroke="#FF6B8A" stroke-width="1.5" stroke-dasharray="7 8" opacity="0.7"/>')
            s.append(f'<text x="{x+4:.1f}" y="{T+22}" fill="#FF8AA5" font-family="Arial" font-size="14" transform="rotate(-90 {x+4:.1f},{T+22})">{esc(lab)}</text>')
    for rv in np.arange(2.8,4.0001,0.1):
        x=xc(float(rv))
        s.append(f'<text x="{x:.1f}" y="{H-62}" text-anchor="middle" fill="#7f8ba7" font-family="Arial" font-size="14">{rv:.1f}</text>')
    s.append(f'<text x="{L+pw/2:.1f}" y="{H-26}" text-anchor="middle" fill="#b7c1d8" font-family="Arial" font-size="18">paramètre r</text>')
    foot=("Version AUDIT : repères classiques ajoutés après détection." if with_refs else
          "Version AVEUGLE : aucun repère classique n’est fourni au détecteur ni affiché.")
    s.append(f'<text x="{L}" y="{H-8}" fill="#5f6b83" font-family="Arial" font-size="13">{foot}</text>')
    s.append('</svg>')
    open(outpath,"w",encoding="utf-8").write("\n".join(s))

def main():
    outdir="out/logistic_blind_change"
    os.makedirs(outdir,exist_ok=True)
    rs=[round(R0+i*STEP,12) for i in range(int(round((R1-R0)/STEP))+1)]
    complexes={c:[] for c in THRESHOLDS}
    sigcounts={c:[] for c in THRESHOLDS}
    for idx,r in enumerate(rs):
        sigs=signatures_three_contracts(r)
        for c in THRESHOLDS:
            sigcounts[c].append(len(sigs[c]))
            complexes[c].append(complex_bits(sigs[c]))
        if idx % 100 == 0:
            print("PROGRESS",idx,"OF",len(rs)-1,"R",r)
    jumps={c:[] for c in THRESHOLDS}
    consensus=[]
    jump_rs=rs[:-1]
    for i in range(len(rs)-1):
        vals=[]
        for c in THRESHOLDS:
            j=(complexes[c][i]^complexes[c][i+1]).bit_count()/float(1<<K)
            jumps[c].append(j); vals.append(j)
        consensus.append(float(np.median(vals)))
    peaks=select_peaks(jump_rs,consensus)

    with open(os.path.join(outdir,"blind_change_series.csv"),"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f); w.writerow(["r_left","r_right","J_0.4","J_0.5","J_0.6","J_consensus"])
        for i,r in enumerate(jump_rs):
            w.writerow([r,rs[i+1],jumps[0.4][i],jumps[0.5][i],jumps[0.6][i],consensus[i]])
    with open(os.path.join(outdir,"blind_peaks.csv"),"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f); w.writerow(["rank","r","score"])
        for k,(score,r,i) in enumerate(peaks,1): w.writerow([k,r,score])

    matches=[]
    for lab,rv in KNOWN:
        nearest=min(peaks,key=lambda p:abs(p[1]-rv)) if peaks else None
        entry={"label":lab,"known_r":rv}
        if nearest:
            entry.update({"peak_r":nearest[1],"distance":abs(nearest[1]-rv),"score":nearest[0],"within_0.01":abs(nearest[1]-rv)<=MATCH_TOL})
        # separate contract scores at nearest grid-left interval to ref
        ii=min(range(len(jump_rs)),key=lambda i:abs(jump_rs[i]-rv))
        entry["contract_scores"]={str(c):jumps[c][ii] for c in THRESHOLDS}
        entry["consensus_at_nearest_grid"]=consensus[ii]
        entry["grid_r"]=jump_rs[ii]
        matches.append(entry)

    report={
        "schema":"INSACERMO_LOGISTIC_BLIND_CHANGE_V0_1",
        "settings":{"r0":R0,"r1":R1,"step":STEP,"n_seeds":N_SEEDS,"burn":BURN,"K":K,"thresholds":THRESHOLDS,"top_n":TOP_N,"suppression_radius":SUPPRESS_RADIUS,"match_tolerance":MATCH_TOL},
        "peaks":[{"rank":k,"r":r,"score":score} for k,(score,r,i) in enumerate(peaks,1)],
        "posthoc_reference_audit":matches,
    }
    json.dump(report,open(os.path.join(outdir,"blind_change_report.json"),"w",encoding="utf-8"),indent=2)

    render(jump_rs,consensus,peaks,os.path.join(outdir,"INSACERMO_LOGISTIC_BLIND_CHANGE.svg"),False)
    render(jump_rs,consensus,peaks,os.path.join(outdir,"INSACERMO_LOGISTIC_BLIND_CHANGE_AUDIT.svg"),True)

    print("TOP_PEAKS")
    for k,(score,r,i) in enumerate(peaks,1):
        print("PEAK",k,"R",f"{r:.6f}","SCORE",f"{score:.9f}",
              "J04",f"{jumps[0.4][i]:.9f}","J05",f"{jumps[0.5][i]:.9f}","J06",f"{jumps[0.6][i]:.9f}")
    print("REFERENCE_AUDIT")
    for m in matches:
        print("REF",m["label"],"KNOWN",f'{m["known_r"]:.9f}',"NEAREST_PEAK",f'{m.get("peak_r",float("nan")):.6f}',
              "DIST",f'{m.get("distance",float("nan")):.6f}',"MATCH",m.get("within_0.01",False),
              "GRID",f'{m["grid_r"]:.6f}',"CONS",f'{m["consensus_at_nearest_grid"]:.9f}')
    print("MATCH_COUNT",sum(m.get("within_0.01",False) for m in matches),"OF",len(matches))
    print("RESULT COMPLETE")

if __name__=="__main__":
    main()
