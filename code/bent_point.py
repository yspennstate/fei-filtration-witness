"""Bent point replacement: h = inner product on k variables y, new coordinate i;
f(y, x_i) = h(y) except at y = 0, where f = x_i.  For every coordinate j: min over orders of L/Inf_j and E_j/Inf_j.
Same conventions as check_witness.py (functions repeated so that this script runs on its own)."""
import math
import numpy as np


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


def pq(mu, n, i):
    others = [j for j in range(n) if j != i]
    m = n - 1
    t = np.arange(1 << m)
    full = np.zeros(1 << m, dtype=np.int64)
    for b in range(m):
        full |= ((t >> b) & 1) << others[b]
    return mu[full], mu[full | (1 << i)]


def zeta(v, m):
    a = v.copy()
    idx = np.arange(1 << m)
    for b in range(m):
        hi = idx[(idx >> b) & 1 == 1]
        a[hi] += a[hi ^ (1 << b)]
    return a


def best_order(p, q):
    m = int(round(math.log2(len(p))))
    a, b = zeta(p, m), zeta(q, m)
    best = np.full(1 << m, np.inf)
    best[0] = float(Phi(a[0], b[0]))
    for R in sorted(range(1, 1 << m), key=lambda t: bin(t).count("1")):
        S = np.array([R ^ (1 << j) for j in range(m) if (R >> j) & 1])
        best[R] = float((best[S] + Phi(a[R] - a[S], b[R] - b[S])).min())
    return best[(1 << m) - 1]


for k in (2, 4, 6, 8, 10):
    n = k + 1
    x = np.arange(1 << n)
    y = x & ((1 << k) - 1)
    xi = (x >> k) & 1
    half = k // 2
    hy = np.array([(-1) ** bin((v & ((1 << half) - 1)) & (v >> half)).count("1") for v in range(1 << k)])
    f = hy[y].copy()
    f[y == 0] = 1 - 2 * xi[y == 0]
    mu = wht(f) ** 2
    F, E = [], []
    for j in range(n):
        p, q = pq(mu, n, j)
        d = float(q.sum())
        F.append(best_order(p, q) / d)
        E.append(float(Phi(p, q).sum()) / d)
    others = list(range(k))
    print(f"k={k:2d}: new coordinate F={F[k]:.4f} E/Inf={E[k]:.4f};  bent coordinates F min {min(F[j] for j in others):.4f}"
          f" max {max(F[j] for j in others):.4f}, E/Inf min {min(E[j] for j in others):.4f}"
          f" max {max(E[j] for j in others):.4f};  best F over all {min(F):.4f}", flush=True)
