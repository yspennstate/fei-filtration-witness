"""Exact checks of the filtration witness statements, with Walsh-Hadamard transforms in float64.

f is a +-1 vector of length 2^n indexed by x in {0,1}^n (bit j of the index is coordinate j; bit 1 means x_j = -1).
p(T) = fhat(T)^2 and q(T) = fhat(T + i)^2 for T not containing i; Phi(p, q) = eta(p) + eta(q) - eta(p + q) in bits.
For an order pi of the other coordinates, lab(T) = last position of pi met by T (0 for the empty set),
A_k = sum_{lab = k} p, B_k = sum_{lab = k} q, L = sum_k Phi(A_k, B_k)."""
import itertools
import math
import numpy as np

LN2 = math.log(2)
rng = np.random.default_rng(20261111)


def wht(v):
    a = np.asarray(v, float).copy()
    h = 1
    while h < len(a):
        a = a.reshape(-1, 2 * h)
        x, y = a[:, :h].copy(), a[:, h:].copy()
        a[:, :h], a[:, h:] = x + y, x - y
        a = a.reshape(-1)
        h *= 2
    return a / len(a)


def eta(x):
    x = np.asarray(x, float)
    out = np.zeros_like(x)
    m = x > 1e-300
    out[m] = -x[m] * np.log2(x[m])
    return out


def Phi(p, q):
    return eta(p) + eta(q) - eta(np.asarray(p) + np.asarray(q))


def h2(d):
    return float(eta(d) + eta(1 - d))


def pq(f, n, i):
    """p, q indexed by subsets T of the other coordinates, encoded as n-1 bit masks over 'others'."""
    mu = wht(f) ** 2
    others = [j for j in range(n) if j != i]
    m = n - 1
    p = np.zeros(1 << m)
    q = np.zeros(1 << m)
    for t in range(1 << m):
        full = 0
        for b in range(m):
            if (t >> b) & 1:
                full |= 1 << others[b]
        p[t] = mu[full]
        q[t] = mu[full | (1 << i)]
    return p, q, others


def erasure(p, q):
    return float(Phi(p, q).sum())


def witness(p, q, order, r=1):
    """order: list of local bit indices (0..m-1); label = tuple of the last r revealed positions met by T."""
    m = len(order)
    pos = {b: k + 1 for k, b in enumerate(order)}
    A, B = {}, {}
    for t in range(len(p)):
        ks = sorted((pos[b] for b in range(m) if (t >> b) & 1), reverse=True)[:r]
        key = tuple(ks)
        A[key] = A.get(key, 0.0) + p[t]
        B[key] = B.get(key, 0.0) + q[t]
    keys = list(A)
    return float(Phi(np.array([A[k] for k in keys]), np.array([B[k] for k in keys])).sum())


def seqs(p, q, order):
    m = len(order)
    pos = {b: k + 1 for k, b in enumerate(order)}
    A = np.zeros(m + 1)
    B = np.zeros(m + 1)
    for t in range(len(p)):
        k = max([pos[b] for b in range(m) if (t >> b) & 1], default=0)
        A[k] += p[t]
        B[k] += q[t]
    return A, B


def zeta(v, m):
    a = v.copy()
    for b in range(m):
        idx = np.arange(1 << m)
        hi = idx[(idx >> b) & 1 == 1]
        a[hi] += a[hi ^ (1 << b)]
    return a


def best_order(p, q):
    """minimum of L over all orders, as a shortest path over subsets (revealed set grows one element at a time)."""
    m = int(round(math.log2(len(p))))
    a, b = zeta(p, m), zeta(q, m)
    best = np.full(1 << m, np.inf)
    best[0] = float(Phi(a[0], b[0]))
    for R in sorted(range(1, 1 << m), key=lambda t: bin(t).count("1")):
        js = [j for j in range(m) if (R >> j) & 1]
        S = np.array([R ^ (1 << j) for j in js])
        cand = best[S] + Phi(a[R] - a[S], b[R] - b[S])
        best[R] = float(cand.min())
    return best[(1 << m) - 1]


def restrict_cond(f, n, revealed):
    """E[f | x_revealed] as a vector over the cube."""
    v = f.astype(float).reshape([2] * n)  # axis 0 is the highest bit
    ax = tuple(n - 1 - j for j in range(n) if j not in revealed)
    if not ax:
        return f.astype(float)
    mean = v.mean(axis=ax, keepdims=True)
    return np.broadcast_to(mean, v.shape).reshape(-1)


def parts(f, n, i):
    x = np.arange(1 << n)
    up = f[x & ~(1 << i)].astype(float)    # x_i = 0  (+1)
    dn = f[x | (1 << i)].astype(float)     # x_i = 1  (-1)
    return (up + dn) / 2, (up - dn) / 2    # g = E_i f, h = D_i f (both functions of the other coordinates)


report = {}


def upd(k, v, mode="max"):
    if mode == "max":
        report[k] = max(report.get(k, -1e18), v)
    elif mode == "and":
        report[k] = report.get(k, True) and v


def tribes(w, s):
    n = w * s
    f = np.ones(1 << n, dtype=int)
    for j in range(1 << n):
        if any(all((j >> (b * w + k)) & 1 for k in range(w)) for b in range(s)):
            f[j] = -1
    return f, n


def maj(n):
    return np.array([1 if bin(j).count("1") < (n + 1) // 2 else -1 for j in range(1 << n)]), n


def andf(n):
    f = np.ones(1 << n, dtype=int)
    f[(1 << n) - 1] = -1
    return f, n


# ---- 1. Theorem A on random and structured functions, n <= 7: brute force over all orders --------------------
fams = []
for n in range(3, 8):
    for bias in (0.5, 0.2, 0.05):
        for _ in range(4):
            f = np.where(rng.random(1 << n) < bias, -1, 1)
            if not np.all(f == f[0]):
                fams.append(f)
for g, n in (andf(6), maj(5), maj(7), tribes(2, 3), tribes(3, 2)):
    fams.append(g)
for f in fams:
    n = int(round(math.log2(len(f))))
    for i in range(n):
        p, q, others = pq(f, n, i)
        d = float(q.sum())
        if d < 1e-15:
            continue
        E = erasure(p, q)
        m = n - 1
        orders = list(itertools.permutations(range(m)))
        if len(orders) > 120:
            orders = [list(rng.permutation(m)) for _ in range(150)]
        Ls = []
        for o in orders:
            o = list(o)
            L1 = witness(p, q, o, 1)
            Ls.append(L1)
            upd("A: E - L (<= 0)", E - L1)
            upd("A: L - h(Inf) (<= 0)", L1 - h2(d))
            L2 = witness(p, q, o, 2)
            L3 = witness(p, q, o, 3)
            upd("ladder: E - L3, L3 - L2, L2 - L1 (<= 0)", max(E - L3, L3 - L2, L2 - L1))
            upd("ladder: |L_m - E| (r = m, ~0)", abs(witness(p, q, o, m) - E))
            A, B = seqs(p, q, o)
            Ms = max(A[K:].sum() * B[:K + 1].sum() for K in range(m + 1)) / d ** 2
            bound = (1 / LN2 + 4 + 2 * math.log2(1 + 2 * Ms)) * d
            upd("B: L - two-sequence bound (<= 0)", L1 - bound)
        if len(orders) <= 120:
            upd("A: |shortest path - brute min|", abs(best_order(p, q) - min(Ls)))

# ---- 2. martingale form and the resampling identities, one order per function -----------------------------------
for f in fams[::3]:
    n = int(round(math.log2(len(f))))
    i = int(rng.integers(n))
    p, q, others = pq(f, n, i)
    if q.sum() < 1e-15:
        continue
    m = n - 1
    o = list(rng.permutation(m))
    A, B = seqs(p, q, o)
    g, h = parts(f, n, i)
    prev_g = restrict_cond(g, n, set())
    prev_h = restrict_cond(h, n, set())
    errs = [abs(A[0] - prev_g[0] ** 2), abs(B[0] - prev_h[0] ** 2)]
    revealed = set()
    for k, b in enumerate(o, start=1):
        revealed.add(others[b])
        cg, ch = restrict_cond(g, n, revealed), restrict_cond(h, n, revealed)
        errs += [abs(A[k] - float(((cg - prev_g) ** 2).mean())), abs(B[k] - float(((ch - prev_h) ** 2).mean()))]
        prev_g, prev_h = cg, ch
    upd("A: martingale form error", max(errs))
    # W(R) = E h(x) h(x^R) = B_{<=K}, V(R+) = E g^2 - E g(x) g(x^R+) = A_{>=K}; R = coordinates after stage K
    werr = 0.0
    for K in range(1, m + 1):
        Rset = [others[b] for b in o[K:]]
        Rplus = [others[b] for b in o[K - 1:]]
        # E h(x) h(x^R): average over x and an independent copy of the R coordinates = E (E[h | x off R])^2
        keep = [j for j in range(n) if j not in Rset]
        W = float((restrict_cond(h, n, set(keep)) ** 2).mean())
        keep2 = [j for j in range(n) if j not in Rplus]
        V = float((g ** 2).mean() - (restrict_cond(g, n, set(keep2)) ** 2).mean())
        werr = max(werr, abs(W - B[:K + 1].sum()), abs(V - A[K:].sum()))
    upd("B: resampling identities error", werr)

# ---- 3. composition formula ----------------------------------------------------------------------------------
for _ in range(60):
    k = int(rng.integers(2, 5))
    l = int(rng.integers(1, 5))
    gb = np.where(rng.random(1 << k) < rng.choice([0.5, 0.25]), -1, 1)
    if np.all(gb == gb[0]):
        continue
    Ft = np.where(rng.random(2 << l) < 0.5, -1, 1).reshape(2, 1 << l)   # Ft[0] = F(+1, z), Ft[1] = F(-1, z)
    n = k + l
    f = np.empty(1 << n, dtype=int)
    for xi in range(1 << n):
        xb, z = xi & ((1 << k) - 1), xi >> k
        f[xi] = Ft[0 if gb[xb] == 1 else 1, z]
    i = int(rng.integers(k))
    p, q, _ = pq(f, n, i)
    Ef, If = erasure(p, q), float(q.sum())
    pg, qg, _ = pq(gb, k, i)
    Eg, Ig = erasure(pg, qg), float(qg.sum())
    ghat = wht(gb)
    g0, gi = ghat[0], ghat[1 << i]
    F0 = wht((Ft[0] + Ft[1]) / 2)
    F1 = wht((Ft[0] - Ft[1]) / 2)
    n1 = float((F1 ** 2).sum())
    rhs = n1 * (Eg - float(Phi(g0 ** 2, gi ** 2))) + float(Phi((F0 + g0 * F1) ** 2, gi ** 2 * F1 ** 2).sum())
    upd("C: composition |E_i(f) - formula|", abs(Ef - rhs))
    upd("C: |Inf_i(f) - Inf_i(g) ||F1||^2|", abs(If - Ig * n1))

# ---- 4. private AND: f = F(v, AND(x_i, x_B)), order v first, B last ---------------------------------------------
for _ in range(80):
    k = int(rng.integers(1, 5))
    l = int(rng.integers(1, 5))
    Fv = np.where(rng.random((1 << l, 2)) < rng.choice([0.5, 0.2]), -1, 1)
    n = 1 + k + l       # coordinate 0 = i, 1..k = B, k+1.. = v
    f = np.empty(1 << n, dtype=int)
    for xi in range(1 << n):
        a = 1 if (xi & ((1 << (k + 1)) - 1)) == 0 else 0      # all of i, B at bit 0 (x = +1) means AND = 1
        f[xi] = Fv[xi >> (k + 1), a]
    p, q, others = pq(f, n, 0)
    d = float(q.sum())
    if d < 1e-15:
        continue
    E = erasure(p, q)
    m = n - 1
    vpos = [b for b in range(m) if others[b] > k]
    bpos = [b for b in range(m) if others[b] <= k]
    L = witness(p, q, vpos + bpos, 1)
    lo = 2 * (1 - 2.0 ** -k)
    hi = lo + 2.0 ** -k * math.log2(math.e * 2 ** k / d)
    upd("D: private AND, lo - E/Inf, E/Inf - L/Inf, L/Inf - hi (<= 0)", max(lo - E / d, (E - L) / d, L / d - hi))

# ---- 5. table values: min over coordinates and orders ------------------------------------------------------------
print("min over i and orders of L/Inf, and min over i of E/Inf:")
for name, (f, n) in [("AND_6", andf(6)), ("AND_8", andf(8)), ("AND_10", andf(10)), ("MAJ_3", maj(3)),
                     ("MAJ_5", maj(5)), ("MAJ_7", maj(7)), ("MAJ_9", maj(9)), ("MAJ_11", maj(11)),
                     ("TRIBES_2x3", tribes(2, 3)), ("TRIBES_2x4", tribes(2, 4)), ("TRIBES_2x5", tribes(2, 5)),
                     ("TRIBES_3x3", tribes(3, 3))]:
    F = math.inf
    Emin = math.inf
    for i in range(n):
        p, q, _ = pq(f, n, i)
        d = float(q.sum())
        if d < 1e-15:
            continue
        F = min(F, best_order(p, q) / d)
        Emin = min(Emin, erasure(p, q) / d)
        if name.startswith(("AND", "MAJ", "TRIBES")):
            break       # these are transitive (tribes up to block symmetry): coordinate 0 represents all
    print(f"  {name:11s} F = {F:.4f}   min E/Inf = {Emin:.4f}")

print(f"functions in sections 1-2: {len(fams)}")
for k, v in report.items():
    print(f"  {k}: {v}")
