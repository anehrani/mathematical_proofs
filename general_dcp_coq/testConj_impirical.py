#!/usr/bin/env python3
"""
Reproducible simulation of the uniform Card-Duel Process (CDP).

Model (Definition 2): two decks of n cards, fixed n x n outcome table phi with
each entry i.i.d. uniform on {WA, WB, T, N} (uniform model, p = 1/4).
Canonical initial ordering DA=[0..n-1], DB=[0..n-1].

Rules:
  WA: a stays on top of A; b -> bottom of B.
  WB: b stays on top of B; a -> bottom of A.
  N : both -> bottom of their decks.
  T : both removed.
Termination: both decks empty.

Non-termination is detected exactly (not by a length cap): within a phase the
relative cyclic order is preserved, so the pair of top cards (a,b) determines the
phase state. A repeat of (a,b) since the last tie is a tie-free cycle => the game
cannot terminate (Lemma 5). This detection is lossless and is *independently*
consistent with the deterministic ceiling T(n) (Theorem 3): no terminating run
can exceed T(n) steps, so a length cap at T(n) would give identical statistics.

Statistics collected on terminating runs:
  D = duration (total duels)
  V = number of distinct cells (pairs) visited over the whole game
  S = D - V (stale re-traversals)
  Lrun = longest run of consecutive stale visits
"""
import random
import math
from collections import deque

WA, WB, T, N = 0, 1, 2, 3

def T_of(n):
    return n * (n * n + 2) // 3

def simulate_once(n, rng):
    # table[i][j] iid uniform over {WA,WB,T,N}
    table = [[rng.randrange(4) for _ in range(n)] for _ in range(n)]
    DA = deque(range(n))
    DB = deque(range(n))
    visited = set()          # global distinct cells (for V)
    phase_seen = set()       # cells seen since last tie (cycle detection)
    duration = 0
    cur_stale_run = 0
    max_stale_run = 0
    while DA and DB:
        a = DA[0]; b = DB[0]
        key = a * n + b
        # cycle detection within phase
        if key in phase_seen:
            return None  # tie-free cycle -> non-terminating
        phase_seen.add(key)
        # fresh vs stale (for S and runs)
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
    # terminated
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

def boot_ci(x, B=2000, rng=None, alpha=0.05):
    if not x: return (float('nan'), float('nan'))
    nx=len(x); means=[]
    for _ in range(B):
        s=0.0
        for _ in range(nx):
            s += x[rng.randrange(nx)]
        means.append(s/nx)
    means.sort()
    lo=means[int((alpha/2)*B)]; hi=means[int((1-alpha/2)*B)-1]
    return (lo,hi)

def wilson(k, nN, z=1.96):
    if nN==0: return (float('nan'),float('nan'))
    phat=k/nN
    den=1+z*z/nN
    centre=(phat+z*z/(2*nN))/den
    half=(z*math.sqrt(phat*(1-phat)/nN + z*z/(4*nN*nN)))/den
    return (centre-half, centre+half)

def main():
    SEED = 20260528
    rng = random.Random(SEED)
    boot_rng = random.Random(SEED+1)
    ns = [4,6,8,10,12,14,16,18,20]
    # more trials for larger n to keep enough terminating runs
    trials_for = {4:200000,6:250000,8:300000,10:350000,12:400000,
                  14:450000,16:500000,18:600000,20:700000}
    print(f"# CDP uniform simulation, seed={SEED}")
    print(f"# columns: n trials term Pr Pr_lo Pr_hi ED ED_lo ED_hi EV EV_lo EV_hi ES ES_lo ES_hi ELrun maxLrun EDind")
    rows=[]
    for n in ns:
        tr = trials_for[n]
        term, Ds, Vs, Ss, Ls = run(n, tr, rng)
        pr = term/tr
        plo,phi = wilson(term, tr)
        ED=mean(Ds); EV=mean(Vs); ES=mean(Ss); EL=mean(Ls)
        edlo,edhi = boot_ci(Ds, 2000, boot_rng)
        evlo,evhi = boot_ci(Vs, 2000, boot_rng)
        eslo,eshi = boot_ci(Ss, 2000, boot_rng)
        maxL = max(Ls) if Ls else float('nan')
        EDind = ED*pr  # E[D 1_Term]
        rows.append((n,tr,term,pr,plo,phi,ED,edlo,edhi,EV,evlo,evhi,ES,eslo,eshi,EL,maxL,EDind))
        print(f"{n} {tr} {term} {pr:.5f} [{plo:.5f},{phi:.5f}] "
              f"D={ED:.3f}[{edlo:.3f},{edhi:.3f}] V={EV:.3f}[{evlo:.3f},{evhi:.3f}] "
              f"S={ES:.3f}[{eslo:.3f},{eshi:.3f}] L={EL:.3f} maxL={maxL} Dind={EDind:.4f}",
              flush=True)
    # power-law fits (log-log least squares), with regression SE on the slope
    import statistics
    def loglog_fit(xs, ys):
        lx=[math.log(x) for x in xs]; ly=[math.log(y) for y in ys]
        mx=mean(lx); my=mean(ly)
        sxx=sum((a-mx)**2 for a in lx)
        sxy=sum((a-mx)*(b-my) for a,b in zip(lx,ly))
        slope=sxy/sxx
        intercept=my-slope*mx
        # residual SE of slope
        resid=[ly[i]-(intercept+slope*lx[i]) for i in range(len(lx))]
        s2=sum(r*r for r in resid)/(len(lx)-2)
        se=math.sqrt(s2/sxx)
        return slope, math.exp(intercept), se
    ns_f=[r[0] for r in rows]
    pr_f=[r[3] for r in rows]
    ed_f=[r[6] for r in rows]
    ev_f=[r[9] for r in rows]
    es_f=[r[12] for r in rows]
    edind_f=[r[17] for r in rows]
    print("\n# FITS (log-log least squares over simulated n)")
    for name, ys in [("Pr(Term)",pr_f),("E[D|Term]",ed_f),("E[V|Term]",ev_f),
                     ("E[S|Term]",es_f),("E[D 1_Term]",edind_f)]:
        sl,co,se = loglog_fit(ns_f, ys)
        print(f"{name:14s}: ~ {co:.3f} * n^{sl:.3f}   (slope SE {se:.3f})")
    # linear fit for V (affine)
    n_=ns_f; v_=ev_f
    mn=mean(n_); mv=mean(v_)
    b=sum((a-mn)*(c-mv) for a,c in zip(n_,v_))/sum((a-mn)**2 for a in n_)
    a0=mv-b*mn
    print(f"E[V|Term] affine fit: {b:.3f} n + ({a0:.3f})")
    # S/V ratio
    print("\n# S/V ratio by n:")
    for r in rows:
        print(f"n={r[0]:2d}  S/V={r[12]/r[9]:.4f}")

if __name__=="__main__":
    main()
