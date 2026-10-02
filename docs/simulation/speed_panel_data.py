"""Data for the speed panel of docs/index.html: v*(d) and the minimum-angle envelope, d = 4..16.

Run from docs/simulation:  python3 speed_panel_data.py band.json
The last envelope point is the exact theta_NRS(d) at v = 1 (D48), not the optimizer's value.
"""
import sys, json, time
sys.path.insert(0, '.')
import numpy as np
from multiprocessing import Pool
from figures_velocity_band import vstar
from figures_threshold_cone import min_angle

def job(d):
    vs = vstar(d)
    rng = np.random.default_rng(d)
    pts = []
    for u in np.linspace(0, 1, 13)[1:]:
        v = vs + (1 - vs) * u
        a = min_angle(d, min(v, 1.0), rng, tries=14)
        pts.append([round(float(v), 5), round(float(a), 3)])
    n = d + 1.0
    c2 = 2 * (d - 1) / (n * np.cos(np.pi / n) ** 2) * (((n * n + 2) / 6) * np.sin(np.pi / n) ** 2 - 1)
    pts[-1][1] = round(float(np.degrees(np.arccos(1 / np.sqrt(c2)))), 3)  # exact theta_NRS(d), D48
    return d, round(float(vs), 6), pts

if __name__ == '__main__':
    t = time.time()
    with Pool(12) as p:
        res = p.map(job, range(4, 17))
    out = {d: {"vstar": vs, "env": pts} for d, vs, pts in res}
    json.dump(out, open(sys.argv[1], 'w'))
    for d, vs, pts in res: print(d, vs, pts[-1], pts[0])
    print('secs', round(time.time() - t))
