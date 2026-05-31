#!/usr/bin/env python3
"""
Reproducible simulation and plotting of the uniform Card-Duel Process (CDP).

Model (Definition 2): two decks of n cards, fixed n x n outcome table phi with
each entry i.i.d. uniform on {WA, WB, T, N} (uniform model, p = 1/4).
Canonical initial ordering DA=[0..n-1], DB=[0..n-1].
"""
import random
import math
from collections import deque
import matplotlib.pyplot as plt

WA, WB, T, N = 0, 1, 2, 3

def T_of(n):
    return n * (n * n + 2) // 3

def simulate_once(n, rng):
    table = [[rng.randrange(4) for _ in range(n)] for _ in range(n)]
    DA = deque(range(n))
    DB = deque(range(n))
    visited = set()          
    phase_seen = set()       
    duration = 0
    cur_stale_run = 0
    max_stale_run = 0
    while DA and DB:
        a = DA[0]; b = DB[0]
        key = a * n + b
        if key in phase_seen:
            return None  # tie-free cycle -> non-terminating
        phase_seen.add(key)
        if key in visited:
            cur_stale_run += 1
            if cur_stale_run > max_stale_run:
                max_stale_run = cur_stale_run
        else:
            visited.add(key)
            cur_stale_run = 0
        duration += 1
        o = table[a][b]
        if o == WA:
            DB.append(DB.popleft())
        elif o == WB:
            DA.append(DA.popleft())
        elif o == N:
            DA.append(DA.popleft()); DB.append(DB.popleft())
        else:  # T
            DA.popleft(); DB.popleft()
            phase_seen.clear()
            cur_stale_run = 0
    V = len(visited)
    S = duration - V
    return (duration, V, S, max_stale_run)

def run(n, trials, rng):
    Ds=[]; Vs=[]; Ss=[]; Ls=[]
    term = 0
    for _ in range(trials):
        r = simulate_once(n, rng)
        if r is not None:
            term += 1
            d,v,s,l = r
            Ds.append(d); Vs.append(v); Ss.append(s); Ls.append(l)
    return term, Ds, Vs, Ss, Ls

def mean(x): return sum(x)/len(x) if x else float('nan')

def loglog_fit(xs, ys):
    lx=[math.log(x) for x in xs]; ly=[math.log(y) for y in ys]
    mx=mean(lx); my=mean(ly)
    sxx=sum((a-mx)**2 for a in lx)
    sxy=sum((a-mx)*(b-my) for a,b in zip(lx,ly))
    slope=sxy/sxx
    intercept=my-slope*mx
    return slope, math.exp(intercept)

def main():
    SEED = 20260528
    rng = random.Random(SEED)
    
    # Using your specified test sizes
    ns = [4,6,8,10,12,14,16,18,20]
    trials_for = {4:200000, 6:250000, 8:300000, 10:350000, 12:400000,
                  14:450000, 16:500000, 18:600000, 20:700000}
    
    print(f"# Running CDP uniform simulation (seed={SEED})...")
    
    ns_f, pr_f, ed_f, edind_f = [], [], [], []
    
    for n in ns:
        tr = trials_for[n]
        term, Ds, Vs, Ss, Ls = run(n, tr, rng)
        pr = term / tr
        ED = mean(Ds)
        EDind = ED * pr
        
        ns_f.append(n)
        pr_f.append(pr)
        ed_f.append(ED)
        edind_f.append(EDind)
        print(f"n={n:2d} finished. Pr(Term)={pr:.5f}, E[D|Term]={ED:.2f}")

    # Calculate fits for the plots
    slope_pr, const_pr = loglog_fit(ns_f, pr_f)
    slope_ed, const_ed = loglog_fit(ns_f, ed_f)
    slope_edind, const_edind = loglog_fit(ns_f, edind_f)

    # --- PLOTTING SECTION FOR THE PAPER ---
    print("# Generating publication figures...")
    plt.style.use('seaborn-v0_8-whitegrid' if 'seaborn-v0_8-whitegrid' in plt.style.available else 'default')
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Panel A: Termination Probability Log-Log Plot
    ax1.loglog(ns_f, pr_f, 'o', color='crimson', markersize=8, label='Empirical Data')
    fit_pr_ys = [const_pr * (n**slope_pr) for n in ns_f]
    ax1.loglog(ns_f, fit_pr_ys, '--', color='black', alpha=0.7,
               label=f'Fit: ${const_pr:.2f} \\cdot n^{{{slope_pr:.2f}}}$')
    ax1.set_title('Panel A: Polynomial Decay of $\\Pr(\\mathrm{Term}_n)$', fontsize=12, fontweight='bold')
    ax1.set_xlabel('Deck Size ($n$)', fontsize=11)
    ax1.set_ylabel('Probability $\\Pr(\\mathrm{Term}_n)$', fontsize=11)
    ax1.set_xticks(ns_f)
    ax1.set_xticklabels([str(x) for x in ns_f])
    ax1.legend(frameon=True, fontsize=10)

    # Panel B: Expected Durations Scaling Log-Log Plot
    ax2.loglog(ns_f, ed_f, 's', color='royalblue', markersize=7, label='$\\mathbb{E}[D \\mid \\mathrm{Term}]$')
    fit_ed_ys = [const_ed * (n**slope_ed) for n in ns_f]
    ax2.loglog(ns_f, fit_ed_ys, '--', color='royalblue', alpha=0.6,
               label=f'Fit: $\\propto n^{{{slope_ed:.2f}}}$')

    ax2.loglog(ns_f, edind_f, '^', color='forestgreen', markersize=7, label='$\\mathbb{E}[D \\cdot \\mathbf{1}_{\\mathrm{Term}}]$')
    fit_edind_ys = [const_edind * (n**slope_edind) for n in ns_f]
    ax2.loglog(ns_f, fit_edind_ys, ':', color='forestgreen', alpha=0.6,
               label=f'Fit: $\\propto n^{{{slope_edind:.2f}}}$')

    ax2.set_title('Panel B: Scaling Asymptotics of Game Duration', fontsize=12, fontweight='bold')
    ax2.set_xlabel('Deck Size ($n$)', fontsize=11)
    ax2.set_ylabel('Duration (Steps)', fontsize=11)
    ax2.set_xticks(ns_f)
    ax2.set_xticklabels([str(x) for x in ns_f])
    ax2.legend(frameon=True, fontsize=10)

    plt.tight_layout()
    output_filename = "cdp_simulation_plots.png"
    plt.savefig(output_filename, dpi=300)
    print(f"# Plot successfully saved to '{output_filename}'")

if __name__=="__main__":
    main()