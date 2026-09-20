#!/usr/bin/env python3
import csv, json, math, os
from collections import Counter
import numpy as np

R0, R1, STEP = 2.8, 4.0, 0.002
N_SEEDS = 1024
BURN = 1500
K = 12
THRESH = 0.5

REFS = [
    ("r=3", 3.0),
    ("1+sqrt(6)", 1 + math.sqrt(6)),
    ("period-8 onset", 3.544090359),
    ("period-16 onset", 3.564407266),
    ("Feigenbaum accumulation", 3.569945672),
    ("period-3 window", 1 + math.sqrt(8)),
]

def signatures_for_r(r):
    x = (np.arange(N_SEEDS, dtype=np.float64) + 0.5) / N_SEEDS
    for _ in range(BURN):
        x = r*x*(1-x)
    masks = np.zeros(N_SEEDS, dtype=np.uint16)
    for t in range(K):
        x = r*x*(1-x)
        masks |= ((x >= THRESH).astype(np.uint16) << np.uint16(t))
    vals, counts = np.unique(masks, return_counts=True)
    return [int(v) for v in vals], [int(c) for c in counts]

def maximal_facets(signatures):
    return [m for m in signatures if not any(m != n and (m & n) == m for n in signatures)]

def feasible_table(facets):
    nmask = 1 << K
    feas = np.zeros(nmask, dtype=np.bool_)
    for m in range(nmask):
        feas[m] = any((m & f) == m for f in facets)
    return feas

def minimal_obstruction_counts(feas):
    out = Counter()
    for m in range(1, 1 << K):
        if feas[m]:
            continue
        bits = [i for i in range(K) if (m >> i) & 1]
        if all(feas[m & ~(1 << i)] for i in bits):
            out[len(bits)] += 1
    return out

def entropy(counts):
    n = sum(counts)
    h = 0.0
    for c in counts:
        p = c/n
        h -= p*math.log2(p)
    return h

def render_svg(rows, outpath):
    W,H = 2200,1200
    L,R,T,B = 140,80,120,170
    pw, ph = W-L-R, 700
    ymin,ymax = 1,12
    maxlog = max([math.log1p(max(row["rank_counts"].values(), default=0)) for row in rows] + [1.0])
    maxfac = max(row["facets"] for row in rows)
    def xcoord(r): return L + (r-R0)/(R1-R0)*pw
    def ycoord(k): return T + (ymax-k)/(ymax-ymin)*ph
    def esc(s): return s.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
    s=[]
    s.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">')
    s.append('<rect width="100%" height="100%" fill="#05070c"/>')
    s.append('<text x="140" y="62" fill="#f5f7ff" font-family="Arial" font-size="40" font-weight="700">INSACERMO — EMPREINTE FUTURE DE LA CARTE LOGISTIQUE</text>')
    s.append('<text x="142" y="98" fill="#8c99b8" font-family="Arial" font-size="20">Image déterministe du complexe des futurs : x(t+1)=r·x(t)·(1−x(t))</text>')
    # grid labels
    for k in range(1,13):
        y=ycoord(k)
        s.append(f'<line x1="{L}" y1="{y}" x2="{W-R}" y2="{y}" stroke="#151c2b" stroke-width="1"/>')
        s.append(f'<text x="{L-20}" y="{y+6}" text-anchor="end" fill="#8390ad" font-family="Arial" font-size="17">rang {k}</text>')
    # heat cells
    cellw = pw/len(rows)+0.5
    for row in rows:
        x=xcoord(row["r"])
        for k,c in row["rank_counts"].items():
            y=ycoord(k)-ph/(ymax-ymin)/2
            val=math.log1p(c)/maxlog
            # deterministic blue->magenta->gold interpolation
            if val < .5:
                t=val/.5
                a=(32,72,145); b=(196,42,153)
            else:
                t=(val-.5)/.5
                a=(196,42,153); b=(255,194,82)
            rgb=tuple(round(a[i]*(1-t)+b[i]*t) for i in range(3))
            hcell=ph/(ymax-ymin)*0.88
            s.append(f'<rect x="{x-cellw/2:.2f}" y="{y:.2f}" width="{cellw:.2f}" height="{hcell:.2f}" fill="rgb{rgb}" opacity="{0.25+0.75*val:.3f}"/>')
    # reference lines only annotations
    for lab,rv in REFS:
        x=xcoord(rv)
        s.append(f'<line x1="{x:.1f}" y1="{T}" x2="{x:.1f}" y2="{T+ph+140}" stroke="#ffffff" stroke-width="1.3" stroke-dasharray="7 8" opacity="0.35"/>')
        s.append(f'<text x="{x+5:.1f}" y="{T+18}" fill="#d5d9e5" font-family="Arial" font-size="15" transform="rotate(-90 {x+5:.1f},{T+18})">{esc(lab)}</text>')
    # facet trace lower area
    basey=T+ph+115
    s.append(f'<text x="{L}" y="{basey-38}" fill="#aeb9d2" font-family="Arial" font-size="18">nombre de facettes maximales du complexe</text>')
    pts=[]
    for row in rows:
        x=xcoord(row["r"])
        y=basey - 90*(row["facets"]/maxfac if maxfac else 0)
        pts.append(f"{x:.1f},{y:.1f}")
    s.append(f'<polyline points="{" ".join(pts)}" fill="none" stroke="#61e7ff" stroke-width="2.2" opacity="0.9"/>')
    # x ticks
    for rv in np.arange(2.8,4.0001,0.1):
        x=xcoord(float(rv))
        s.append(f'<line x1="{x:.1f}" y1="{T+ph}" x2="{x:.1f}" y2="{T+ph+8}" stroke="#69758f"/>')
        s.append(f'<text x="{x:.1f}" y="{T+ph+32}" text-anchor="middle" fill="#8995af" font-family="Arial" font-size="15">{rv:.1f}</text>')
    s.append(f'<text x="{L+pw/2:.1f}" y="{H-55}" text-anchor="middle" fill="#c4cbe0" font-family="Arial" font-size="20">paramètre r</text>')
    s.append(f'<text x="{L}" y="{H-20}" fill="#66728d" font-family="Arial" font-size="14">Couleur = log(1 + nombre d’obstructions minimales) par rang. Les lignes blanches sont des repères classiques ajoutés après calcul, jamais utilisés par le moteur.</text>')
    s.append('</svg>')
    data="\n".join(s)
    open(outpath,"w",encoding="utf-8").write(data)

def main():
    outdir="out/logistic_future_complex"
    os.makedirs(outdir,exist_ok=True)
    rs=[round(R0+i*STEP,12) for i in range(int(round((R1-R0)/STEP))+1)]
    rows=[]
    prev=None
    transitions=[]
    for r in rs:
        sig, counts=signatures_for_r(r)
        facets=maximal_facets(sig)
        feas=feasible_table(facets)
        rc=minimal_obstruction_counts(feas)
        row={
            "r":r,
            "distinct_signatures":len(sig),
            "facets":len(facets),
            "feasible_bundles":int(feas.sum()),
            "entropy_bits":entropy(counts),
            "rank_counts":dict(sorted(rc.items())),
            "min_rank":min(rc) if rc else None,
            "max_rank":max(rc) if rc else None,
        }
        fingerprint=(row["facets"],row["feasible_bundles"],tuple(row["rank_counts"].items()))
        if prev is None or fingerprint != prev[1]:
            transitions.append({"r":r,"from":None if prev is None else prev[0],"to":fingerprint})
        prev=(fingerprint,fingerprint)
        rows.append(row)
    # CSV
    with open(os.path.join(outdir,"logistic_future_complex.csv"),"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f)
        w.writerow(["r","distinct_signatures","facets","feasible_bundles","entropy_bits","min_rank","max_rank"]+[f"rank_{k}" for k in range(1,13)])
        for row in rows:
            w.writerow([row["r"],row["distinct_signatures"],row["facets"],row["feasible_bundles"],f'{row["entropy_bits"]:.12f}',row["min_rank"],row["max_rank"]]+[row["rank_counts"].get(k,0) for k in range(1,13)])
    # JSON
    with open(os.path.join(outdir,"logistic_future_complex.json"),"w",encoding="utf-8") as f:
        json.dump({"schema":"INSACERMO_LOGISTIC_FUTURE_COMPLEX_V0_1","settings":{"r0":R0,"r1":R1,"step":STEP,"n_seeds":N_SEEDS,"burn":BURN,"K":K,"threshold":THRESH},"references":REFS,"rows":rows},f,indent=2)
    render_svg(rows,os.path.join(outdir,"INSACERMO_LOGISTIC_FUTURE_COMPLEX.svg"))

    # summarize engine changes nearest to reference locations, without altering output
    def nearest_row(rv):
        return min(rows,key=lambda x:abs(x["r"]-rv))
    print("INSACERMO_LOGISTIC_FUTURE_COMPLEX_V0_1")
    print("GRID_POINTS",len(rows))
    for lab,rv in REFS:
        row=nearest_row(rv)
        print("REFERENCE",lab,"KNOWN_R",f"{rv:.12f}","GRID_R",f'{row["r"]:.3f}',"SIGNATURES",row["distinct_signatures"],"FACETS",row["facets"],"MIN_RANK",row["min_rank"],"RANK_COUNTS",row["rank_counts"])
    # coarse noteworthy rows
    for rv in [2.9,3.0,3.1,3.45,3.50,3.55,3.56,3.57,3.60,3.74,3.83,3.84,3.90,4.0]:
        row=nearest_row(rv)
        print("CHECK",f'{row["r"]:.3f}',"SIG",row["distinct_signatures"],"FACETS",row["facets"],"FEAS",row["feasible_bundles"],"MINR",row["min_rank"],"COUNTS",row["rank_counts"])
    print("RESULT COMPLETE")

if __name__=="__main__":
    main()
