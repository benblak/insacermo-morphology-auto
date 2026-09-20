#!/usr/bin/env python3
import argparse
import csv
import io
import itertools
import json
import math
import os
import urllib.request
from collections import defaultdict, deque
from hashlib import sha256

URL = "https://raw.githubusercontent.com/jpatokal/openflights/master/data/routes.dat"
START = "KEF"
TARGETS = [
    "LHR","CDG","FRA","AMS","MAD","FCO","ATH","IST","DXB","DOH",
    "JFK","YYZ","MEX","GRU","EZE","CPT","JNB","DEL","SIN","HKG",
    "NRT","SYD","AKL","LAX","SFO"
]
H = 3

W = HSVG = 1800
CX = CY = 900
RADII = {1: 390, 2: 565, 3: 735}
LABEL_RADIUS = 810

def keep_route(r, scenario):
    if len(r) < 5:
        return False
    airline, src, dst = r[0], r[2], r[4]
    if src == "\\N" or dst == "\\N":
        return False
    if scenario == "NO_FI" and airline == "FI":
        return False
    return True

def build_graph(rows, scenario):
    g = defaultdict(set)
    for r in rows:
        if keep_route(r, scenario):
            g[r[2]].add(r[4])
    return {u: tuple(sorted(vs)) for u, vs in g.items()}

def min_depth_covering(g, bundle, H=H):
    bundle = tuple(bundle)
    idx = {q:i for i,q in enumerate(bundle)}
    full = (1 << len(bundle)) - 1
    def add(mask, airport):
        j = idx.get(airport)
        return mask if j is None else mask | (1 << j)
    start_mask = add(0, START)
    q = deque([(START, start_mask, 0)])
    seen = {(START, start_mask): 0}
    while q:
        u, mask, d = q.popleft()
        if mask == full:
            return d
        if d == H:
            continue
        for v in g.get(u, ()):
            m2 = add(mask, v)
            s = (v, m2)
            d2 = d + 1
            if s not in seen or d2 < seen[s]:
                seen[s] = d2
                q.append((v, m2, d2))
    return None

def analyze(g):
    singleton_depth = {q:min_depth_covering(g,(q,)) for q in TARGETS}
    pair_depth = {}
    pair_min_obs = set()
    for a,b in itertools.combinations(TARGETS,2):
        d = min_depth_covering(g,(a,b))
        pair_depth[tuple(sorted((a,b)))] = d
        if singleton_depth[a] is not None and singleton_depth[b] is not None and d is None:
            pair_min_obs.add(tuple(sorted((a,b))))
    triple_min_obs = set()
    triple_depth = {}
    for tri in itertools.combinations(TARGETS,3):
        d = min_depth_covering(g,tri)
        triple_depth[tri] = d
        if d is not None:
            continue
        a,b,c = tri
        pairs = [tuple(sorted((a,b))), tuple(sorted((a,c))), tuple(sorted((b,c)))]
        if all(singleton_depth[x] is not None for x in tri) and all(pair_depth[p] is not None for p in pairs):
            triple_min_obs.add(tuple(sorted(tri)))
    return {
        "singleton_depth": singleton_depth,
        "pair_depth": pair_depth,
        "pair_min_obs": pair_min_obs,
        "triple_min_obs": triple_min_obs,
    }

def esc(s):
    return (s.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
             .replace('"',"&quot;"))

def pt(angle, radius):
    return (CX + radius*math.cos(angle), CY + radius*math.sin(angle))

def depth_radius(d):
    return 845 if d is None else RADII[d]

def color_for_depth(d):
    if d == 1: return "#8FE8FF"
    if d == 2: return "#36B4FF"
    if d == 3: return "#6A6BFF"
    return "#4A4A55"

def make_svg(base, after, out_path):
    angles = {}
    # Contract order is frozen; start at top and move clockwise.
    for i,q in enumerate(TARGETS):
        angles[q] = -math.pi/2 + (2*math.pi*i/len(TARGETS))

    base_pairs = base["pair_min_obs"]
    after_pairs = after["pair_min_obs"]
    base_tris = base["triple_min_obs"]
    after_tris = after["triple_min_obs"]
    new_pairs = after_pairs - base_pairs
    lost_pairs = base_pairs - after_pairs
    new_tris = after_tris - base_tris
    lost_tris = base_tris - after_tris

    base_depth = base["singleton_depth"]
    after_depth = after["singleton_depth"]

    s=[]
    s.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{HSVG}" viewBox="0 0 {W} {HSVG}">')
    s.append('<defs>')
    s.append('<radialGradient id="bg" cx="50%" cy="50%" r="70%"><stop offset="0%" stop-color="#10182B"/><stop offset="45%" stop-color="#070B15"/><stop offset="100%" stop-color="#020307"/></radialGradient>')
    s.append('<radialGradient id="core" cx="40%" cy="35%" r="70%"><stop offset="0%" stop-color="#FFFFFF"/><stop offset="22%" stop-color="#7AE7FF"/><stop offset="62%" stop-color="#2B4CFF"/><stop offset="100%" stop-color="#071128"/></radialGradient>')
    s.append('<filter id="glow"><feGaussianBlur stdDeviation="6" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>')
    s.append('<filter id="soft"><feGaussianBlur stdDeviation="2"/></filter>')
    s.append('</defs>')
    s.append(f'<rect width="{W}" height="{HSVG}" fill="url(#bg)"/>')

    # title
    s.append('<text x="90" y="110" fill="#F4F7FF" font-size="52" font-family="Arial,Helvetica,sans-serif" font-weight="700">EMPREINTE D’UNE DÉCISION</text>')
    s.append('<text x="92" y="158" fill="#9AA7C9" font-size="24" font-family="Arial,Helvetica,sans-serif">INSACERMO • OpenFlights • suppression de FI • sortie déterministe du moteur</text>')

    # rings = exact singleton depth
    for d,r in RADII.items():
        s.append(f'<circle cx="{CX}" cy="{CY}" r="{r}" fill="none" stroke="#293553" stroke-width="2" stroke-dasharray="8 14" opacity="0.7"/>')
        s.append(f'<text x="{CX+18}" y="{CY-r+28}" fill="#617099" font-size="18" font-family="Arial">D={d}</text>')

    # new order-3 obstructions: triangles behind everything.
    # Every triangle is data-derived; low opacity turns multiplicity into visible density.
    for tri in sorted(new_tris):
        coords=[]
        for q in tri:
            x,y=pt(angles[q], depth_radius(after_depth[q]))
            coords.append(f"{x:.1f},{y:.1f}")
        s.append(f'<polygon points="{" ".join(coords)}" fill="#FF2A78" opacity="0.028" stroke="#FF2A78" stroke-width="0.7" stroke-opacity="0.07"/>')

    # old order-3 obstructions that remain are shown as faint cyan structure.
    for tri in sorted(after_tris & base_tris):
        coords=[]
        for q in tri:
            x,y=pt(angles[q], depth_radius(after_depth[q]))
            coords.append(f"{x:.1f},{y:.1f}")
        s.append(f'<polygon points="{" ".join(coords)}" fill="#30D8FF" opacity="0.010" stroke="#30D8FF" stroke-width="0.5" stroke-opacity="0.035"/>')

    # baseline pair obstructions faint
    for a,b in sorted(base_pairs):
        xa,ya=pt(angles[a], depth_radius(after_depth[a]))
        xb,yb=pt(angles[b], depth_radius(after_depth[b]))
        s.append(f'<line x1="{xa:.1f}" y1="{ya:.1f}" x2="{xb:.1f}" y2="{yb:.1f}" stroke="#2E7FA1" stroke-width="1.4" opacity="0.20"/>')

    # new pair obstructions vivid
    for a,b in sorted(new_pairs):
        xa,ya=pt(angles[a], depth_radius(after_depth[a]))
        xb,yb=pt(angles[b], depth_radius(after_depth[b]))
        s.append(f'<line x1="{xa:.1f}" y1="{ya:.1f}" x2="{xb:.1f}" y2="{yb:.1f}" stroke="#FF456F" stroke-width="4.2" opacity="0.78" filter="url(#glow)"/>')

    # depth movement: baseline -> after
    for q in TARGETS:
        db, da = base_depth[q], after_depth[q]
        rb, ra = depth_radius(db), depth_radius(da)
        if rb != ra:
            x1,y1=pt(angles[q], rb)
            x2,y2=pt(angles[q], ra)
            s.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="#FFD166" stroke-width="6" opacity="0.9" filter="url(#glow)"/>')
            # arrow tip
            s.append(f'<circle cx="{x2:.1f}" cy="{y2:.1f}" r="8" fill="#FFD166"/>')

    # radial guides + after nodes + labels
    for q in TARGETS:
        a=angles[q]
        r=depth_radius(after_depth[q])
        x,y=pt(a,r)
        lx,ly=pt(a,LABEL_RADIUS)
        # guide ray
        s.append(f'<line x1="{CX:.1f}" y1="{CY:.1f}" x2="{x:.1f}" y2="{y:.1f}" stroke="#20304F" stroke-width="1" opacity="0.45"/>')
        # baseline ghost position if changed
        rb=depth_radius(base_depth[q])
        if rb != r:
            bx,by=pt(a,rb)
            s.append(f'<circle cx="{bx:.1f}" cy="{by:.1f}" r="8" fill="none" stroke="#B0BCD8" stroke-width="2" opacity="0.45"/>')
        # after node
        col=color_for_depth(after_depth[q])
        s.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="13" fill="{col}" stroke="#FFFFFF" stroke-width="2.2" opacity="0.98" filter="url(#glow)"/>')
        anchor="start" if math.cos(a)>=0 else "end"
        dx=12 if anchor=="start" else -12
        s.append(f'<text x="{lx+dx:.1f}" y="{ly+7:.1f}" text-anchor="{anchor}" fill="#DCE5FF" font-size="20" font-family="Arial,Helvetica,sans-serif" font-weight="700">{esc(q)}</text>')

    # core = action
    s.append(f'<circle cx="{CX}" cy="{CY}" r="126" fill="url(#core)" opacity="0.97" filter="url(#glow)"/>')
    s.append(f'<circle cx="{CX}" cy="{CY}" r="144" fill="none" stroke="#6D77FF" stroke-width="2" opacity="0.32"/>')
    s.append(f'<text x="{CX}" y="{CY-16}" text-anchor="middle" fill="#08101F" font-size="28" font-family="Arial" font-weight="900">T</text>')
    s.append(f'<text x="{CX}" y="{CY+20}" text-anchor="middle" fill="#08101F" font-size="27" font-family="Arial" font-weight="900">RETIRER FI</text>')
    s.append(f'<text x="{CX}" y="{CY+52}" text-anchor="middle" fill="#112147" font-size="16" font-family="Arial" font-weight="700">même contrat • même H=3</text>')

    # bottom factual receipt
    y0=1615
    s.append(f'<rect x="90" y="{y0-48}" width="1620" height="125" rx="24" fill="#08101F" stroke="#263757" stroke-width="2" opacity="0.95"/>')
    stats = [
        ("Futurs individuels finis", f"{sum(v is not None for v in base_depth.values())} → {sum(v is not None for v in after_depth.values())}"),
        ("Obstructions minimales ordre 2", f"{len(base_pairs)} → {len(after_pairs)}  (+{len(new_pairs)})"),
        ("Obstructions minimales ordre 3", f"{len(base_tris)} → {len(after_tris)}  (+{len(new_tris)})"),
        ("Futurs retardés", f"{sum((base_depth[q] or 99) < (after_depth[q] or 99) for q in TARGETS)}"),
    ]
    xx=125
    for k,(lab,val) in enumerate(stats):
        s.append(f'<text x="{xx}" y="{y0}" fill="#8594B8" font-size="17" font-family="Arial">{esc(lab)}</text>')
        s.append(f'<text x="{xx}" y="{y0+34}" fill="#F4F7FF" font-size="27" font-family="Arial" font-weight="700">{esc(val)}</text>')
        xx += [410,430,430,0][k]

    s.append('<text x="90" y="1760" fill="#647291" font-size="17" font-family="Arial">Lecture : anneaux = profondeur individuelle Dₓ(F) ; traits rouges = nouvelles obstructions de paires ; voile magenta = nouvelles obstructions minimales d’ordre 3 ; segments or = futurs retardés.</text>')
    s.append('<text x="90" y="1790" fill="#4E5B78" font-size="15" font-family="Arial">Aucun placement n’est optimisé pour “faire joli” : ordre angulaire = ordre contractuel figé ; rayon = profondeur calculée ; géométrie relationnelle = sorties exactes du moteur.</text>')
    s.append('</svg>')

    data = "\n".join(s)
    with open(out_path,"w",encoding="utf-8") as f:
        f.write(data)
    return {
        "new_pairs": len(new_pairs),
        "lost_pairs": len(lost_pairs),
        "new_triples": len(new_tris),
        "lost_triples": len(lost_tris),
        "svg_sha256": sha256(data.encode("utf-8")).hexdigest(),
    }

def pair_csv(base,after,path):
    new = after["pair_min_obs"] - base["pair_min_obs"]
    with open(path,"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f)
        w.writerow(["future_a","future_b","status"])
        for a,b in sorted(after["pair_min_obs"]):
            w.writerow([a,b,"NEW_AFTER_NO_FI" if (a,b) in new else "PRESENT_BEFORE_AND_AFTER"])

def triple_csv(base,after,path):
    new = after["triple_min_obs"] - base["triple_min_obs"]
    with open(path,"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f)
        w.writerow(["future_a","future_b","future_c","status"])
        for tri in sorted(after["triple_min_obs"]):
            w.writerow([*tri,"NEW_AFTER_NO_FI" if tri in new else "PRESENT_BEFORE_AND_AFTER"])

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--outdir",default="out")
    args=ap.parse_args()
    os.makedirs(args.outdir,exist_ok=True)

    raw=urllib.request.urlopen(URL,timeout=60).read()
    route_sha=sha256(raw).hexdigest()
    rows=list(csv.reader(io.StringIO(raw.decode("utf-8"))))
    print("ROUTES",len(rows),"SHA256",route_sha)

    base=analyze(build_graph(rows,"BASELINE"))
    after=analyze(build_graph(rows,"NO_FI"))

    svg_path=os.path.join(args.outdir,"INSACERMO_FUTURE_SHADOW_OPENFLIGHTS_NO_FI.svg")
    receipt=make_svg(base,after,svg_path)
    pair_csv(base,after,os.path.join(args.outdir,"pair_obstructions_after_no_fi.csv"))
    triple_csv(base,after,os.path.join(args.outdir,"triple_obstructions_after_no_fi.csv"))

    receipt.update({
        "schema":"INSACERMO_FUTURE_SHADOW_V0_1",
        "data_url":URL,
        "routes_rows":len(rows),
        "routes_sha256":route_sha,
        "start":START,
        "targets":TARGETS,
        "horizon":H,
        "transformation":"remove all routes whose airline code is FI",
        "baseline_singleton_depth":base["singleton_depth"],
        "after_singleton_depth":after["singleton_depth"],
        "baseline_pair_minimal_obstructions":len(base["pair_min_obs"]),
        "after_pair_minimal_obstructions":len(after["pair_min_obs"]),
        "baseline_triple_minimal_obstructions":len(base["triple_min_obs"]),
        "after_triple_minimal_obstructions":len(after["triple_min_obs"]),
        "renderer_semantics":{
            "angular_order":"frozen TARGETS list order",
            "radius":"singleton exact minimum route-segment depth 1..3",
            "baseline_pair_edges":"faint cyan chords",
            "new_pair_edges":"bright red chords",
            "persistent_triples":"faint cyan triangular veil",
            "new_triples":"magenta triangular veil",
            "depth_increase":"gold radial segment"
        }
    })
    with open(os.path.join(args.outdir,"future_shadow_receipt.json"),"w",encoding="utf-8") as f:
        json.dump(receipt,f,indent=2,sort_keys=True)

    print("BASE_PAIR",len(base["pair_min_obs"]))
    print("AFTER_PAIR",len(after["pair_min_obs"]))
    print("BASE_TRIPLE",len(base["triple_min_obs"]))
    print("AFTER_TRIPLE",len(after["triple_min_obs"]))
    print("NEW_PAIR",receipt["new_pairs"])
    print("NEW_TRIPLE",receipt["new_triples"])
    print("SVG_SHA256",receipt["svg_sha256"])
    print("RESULT COMPLETE")

if __name__=="__main__":
    main()
