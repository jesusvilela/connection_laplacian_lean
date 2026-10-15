# -*- coding: utf-8 -*-
"""
selftest.py -- internal sanity checks for independent_impl.py.

Everything checked here is either
  (a) a theorem of paper/paper.tex (cited by label + paper.tex line range
      in each check name), or
  (b) a hand-derived matrix/spectrum for a graph small enough to verify
      with pencil and paper (marked "hand").
No Lean code and no prior fuzzers are used.  Run:  python selftest.py
Exit code 0 iff all checks pass.
"""

import os
import sys
import itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np

from independent_impl import (
    I2, SIGMA_X, HADAMARD, TOL,
    validate_adjacency, normalise_wrap, edges, connected_components,
    scalar_laplacian, signed_laplacian, connection_laplacian,
    flat_laplacian, orientation_cover_adjacency, spectrum, kernel_dim,
    is_balanced_component, beta, fibre_sheets, cover_component_fibres,
)

FAILURES = []
NCHECKS = [0]


def check(name, ok, detail=""):
    NCHECKS[0] += 1
    if not ok:
        FAILURES.append(name)
        print("  FAIL  %s   %s" % (name, detail))
    return bool(ok)


# --------------------------------------------------------------- test graphs

def cycle_adj(n):
    A = np.zeros((n, n))
    for i in range(n):
        A[i, (i + 1) % n] = 1.0
        A[(i + 1) % n, i] = 1.0
    return A


def path_adj(n):
    A = np.zeros((n, n))
    for i in range(n - 1):
        A[i, i + 1] = 1.0
        A[i + 1, i] = 1.0
    return A


def star_adj(n_leaves):
    n = n_leaves + 1
    A = np.zeros((n, n))
    for i in range(1, n):
        A[0, i] = 1.0
        A[i, 0] = 1.0
    return A


def complete_adj(n):
    return np.ones((n, n)) - np.eye(n)


def empty_adj(n):
    return np.zeros((n, n))


def fs(*pairs):
    return set(frozenset(p) for p in pairs)


def W_of(adj, idxs):
    E = edges(adj)
    return set(E[i] for i in idxs)


# ------------------------------------------------- structural battery (paper)

def hadamard_blocks(M):
    """(1/2) P M P with P = kron(I, R^); returns (i=0 block, i=1 block,
    off block) in the V x {0,1} slicing.  Thm 3.1 proof (lines 331-338) and
    Thm 4.4 proof (lines 473-509) both claim these are (Lsc, Lsg, 0)."""
    m = M.shape[0] // 2
    P = np.kron(np.eye(m), HADAMARD)
    Mp = 0.5 * (P @ M @ P)
    return Mp[0::2, 0::2], Mp[1::2, 1::2], Mp[0::2, 1::2]


def structural_battery(tag, adj, wrap_e):
    """All paper theorems that hold for EVERY connection graph (G, W):
    spectral unions, kernel-dimension formulas, Hadamard decompositions,
    Kronecker-sum formula, traces, fibre cardinalities, inequalities."""
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    n = A.shape[0]
    comps = connected_components(A)
    nc = len(comps)
    bal = [is_balanced_component(A, W, c) for c in comps]
    b = int(sum(bal))
    mE = len(edges(A))

    Lsc = scalar_laplacian(A)
    Lsg = signed_laplacian(A, W)
    Lmob = connection_laplacian(A, W)
    Lflat = flat_laplacian(A)
    Lcov = scalar_laplacian(orientation_cover_adjacency(A, W))

    s_sc, s_sg = spectrum(Lsc), spectrum(Lsg)
    union = np.sort(np.concatenate([s_sc, s_sg]))
    dup_sc = np.sort(np.concatenate([s_sc, s_sc]))

    # --- spectral unions -------------------------------------------------
    check("%s: Spec(L_Mob)=Spec(Lsc)+Spec(Lsg) [Rem 8.7 direct-bundle]"
          % tag, np.allclose(spectrum(Lmob), union, atol=1e-7))
    check("%s: Spec(L_flat)=Spec(Lsc)+Spec(Lsc) [flat=2 copies, l.157-159]"
          % tag, np.allclose(spectrum(Lflat), dup_sc, atol=1e-7))
    check("%s: Spec(L_cov)=Spec(Lsc)+Spec(Lsg) [Thm 8.6 cover-charpoly]"
          % tag, np.allclose(spectrum(Lcov), union, atol=1e-7))

    # --- kernel dimensions [Thms 6.1, 6.2, 6.3; Cor 4.5] -----------------
    check("%s: dim ker Lsc = #comp [Thm 6.1]" % tag, kernel_dim(Lsc) == nc,
          "got %d want %d" % (kernel_dim(Lsc), nc))
    check("%s: dim ker Lsg = beta [Thm 6.2]" % tag, kernel_dim(Lsg) == b,
          "got %d want %d" % (kernel_dim(Lsg), b))
    check("%s: dim ker L_Mob = #comp+beta [Thm 6.3]" % tag,
          kernel_dim(Lmob) == nc + b,
          "got %d want %d" % (kernel_dim(Lmob), nc + b))
    check("%s: dim ker L_flat = 2#comp [Thm 6.3]" % tag,
          kernel_dim(Lflat) == 2 * nc)
    check("%s: dim ker L_cov = ker Lsc + ker Lsg [Cor 4.5]" % tag,
          kernel_dim(Lcov) == kernel_dim(Lsc) + kernel_dim(Lsg))

    # --- Hadamard decompositions [Thm 3.1; Thm 4.4] ----------------------
    a_, b_, o_ = hadamard_blocks(Lmob)
    check("%s: (1/2)PL_Mob P -> (Lsc, Lsg, 0) [Thm 3.1]" % tag,
          np.allclose(a_, Lsc, atol=1e-9) and np.allclose(b_, Lsg, atol=1e-9)
          and np.allclose(o_, 0, atol=1e-9))
    a_, b_, o_ = hadamard_blocks(Lflat)
    check("%s: (1/2)PL_flat P -> (Lsc, Lsc, 0) [Thm 3.1 flat]" % tag,
          np.allclose(a_, Lsc, atol=1e-9) and np.allclose(b_, Lsc, atol=1e-9)
          and np.allclose(o_, 0, atol=1e-9))
    a_, b_, o_ = hadamard_blocks(Lcov)
    check("%s: (1/2)P L_cov P -> (Lsc, Lsg, 0) [Thm 4.4]" % tag,
          np.allclose(a_, Lsc, atol=1e-9) and np.allclose(b_, Lsg, atol=1e-9)
          and np.allclose(o_, 0, atol=1e-9))

    # --- Kronecker-sum formula for L_Mob (paper line 154-156) -----------
    # NOTE on ordering: the paper writes D (x) I2 (vertex-major, index
    # (u,i) -> 2u+i) but Phi(e) (x) 1_e (fibre-major); the literal sum
    # mixes Kronecker conventions.  In the vertex-major order of the
    # operative display eq. (1) the edge term is kron(1_e, Phi(e)).
    D = np.diag(A.sum(axis=1))
    K = np.kron(D, I2)
    for e in edges(A):
        u, v = sorted(e)
        ind = np.zeros((n, n))
        ind[u, v] = 1.0
        ind[v, u] = 1.0
        K -= np.kron(ind, SIGMA_X if e in W else I2)
    check("%s: L_Mob = kron(D,I2)-sum kron(Phi(e),1_e) [l.154-156]" % tag,
          np.allclose(Lmob, K, atol=1e-12))
    check("%s: L_flat = kron(Lsc, I2) [l.157-159]" % tag,
          np.allclose(Lflat, np.kron(Lsc, I2), atol=1e-12))

    # --- traces [Prop 8.1; Prop 8.2] --------------------------------------
    check("%s: tr Lsc = 2#E [Prop 8.1]" % tag,
          abs(np.trace(Lsc) - 2 * mE) < 1e-8)
    check("%s: tr Lsg = 2#E [Prop 8.1]" % tag,
          abs(np.trace(Lsg) - 2 * mE) < 1e-8)
    check("%s: tr L_flat = 4#E [Prop 8.1]" % tag,
          abs(np.trace(Lflat) - 4 * mE) < 1e-8)
    check("%s: tr L_Mob = 4#E [Prop 8.1]" % tag,
          abs(np.trace(Lmob) - 4 * mE) < 1e-8)
    check("%s: tr(L_Mob^2)=tr(Lsc^2)+tr(Lsg^2) [Prop 8.2]" % tag,
          abs(np.trace(Lmob @ Lmob)
              - np.trace(Lsc @ Lsc) - np.trace(Lsg @ Lsg)) < 1e-7)
    check("%s: ||L_Mob||_F^2=||Lsc||_F^2+||Lsg||_F^2 [Prop 8.2]" % tag,
          abs(np.sum(Lmob * Lmob) - np.sum(Lsc * Lsc) - np.sum(Lsg * Lsg))
          < 1e-7)

    # --- fibres [Thm 5.3; Cor 5.7] ----------------------------------------
    fsh = fibre_sheets(A, W)
    check("%s: sheets = 2/1 per balance [Thm 5.3]" % tag,
          fsh["sheets"] == [2 if x else 1 for x in bal])
    fibres, cov_total = cover_component_fibres(A, W)
    check("%s: measured cover fibres = sheets [Thm 5.3]" % tag,
          fibres == fsh["sheets"], "fibres=%s sheets=%s" % (fibres, fsh["sheets"]))
    check("%s: #comp(cover) = #comp + beta [Cor 5.7]" % tag,
          cov_total == nc + b and fsh["total_cover_components"] == cov_total)

    # --- inequalities [Prop 8.3; Thm 6.4] ---------------------------------
    check("%s: ker Lsg <= ker Lsc [Prop 8.3]" % tag,
          kernel_dim(Lsg) <= kernel_dim(Lsc))
    check("%s: ker L_flat - ker L_Mob = #comp - beta [Prop 8.3]" % tag,
          kernel_dim(Lflat) - kernel_dim(Lmob) == nc - b)
    check("%s: ker L_Mob < ker L_flat iff beta < #comp [Thm 6.4]" % tag,
          (kernel_dim(Lmob) < kernel_dim(Lflat)) == (b < nc))


# =================================================================== tests ==

def test_hand_matrices():
    print("[1] Hand-written matrices (triangle, P3)")
    TRI = cycle_adj(3)
    W1 = fs((0, 1))

    Lsc3 = scalar_laplacian(TRI)
    check("hand: Lsc(C3) entrywise",
          np.array_equal(Lsc3, np.array([[2, -1, -1], [-1, 2, -1],
                                         [-1, -1, 2]], float)))
    check("hand: Lsg(C3, W=empty) = Lsc",
          np.array_equal(signed_laplacian(TRI, set()), Lsc3))
    check("hand: Lsg(C3, W={01}) entrywise",
          np.array_equal(signed_laplacian(TRI, W1),
                         np.array([[2, 1, -1], [1, 2, -1], [-1, -1, 2]],
                                  float)))
    check("hand: Lsg(C3, W={01,02}) entrywise",
          np.array_equal(signed_laplacian(TRI, fs((0, 1), (0, 2))),
                         np.array([[2, 1, 1], [1, 2, -1], [1, -1, 2]],
                                  float)))
    check("hand: Lsg(C3, W=all) entrywise",
          np.array_equal(signed_laplacian(TRI, fs((0, 1), (1, 2), (0, 2))),
                         np.array([[2, 1, 1], [1, 2, 1], [1, 1, 2]], float)))

    # L_Mob(C3, W={01}) written out by hand: blocks 2*I2 (diag),
    # -sigma_x on {0,1}, -I2 on {0,2} and {1,2}; index 2u+i.
    Lmob3 = np.array([
        [2, 0, 0, -1, -1, 0],
        [0, 2, -1, 0, 0, -1],
        [0, -1, 2, 0, -1, 0],
        [-1, 0, 0, 2, 0, -1],
        [-1, 0, -1, 0, 2, 0],
        [0, -1, 0, -1, 0, 2]], float)
    check("hand: L_Mob(C3, W={01}) entrywise",
          np.array_equal(connection_laplacian(TRI, W1), Lmob3))
    check("hand: L_Mob(C3, W=empty) = kron(Lsc, I2)",
          np.array_equal(connection_laplacian(TRI, set()),
                         np.kron(Lsc3, I2)))

    P3 = path_adj(3)
    # L_Mob(P3, W={01}) by hand: deg blocks 1,2,1; -sigma_x on {0,1};
    # -I2 on {1,2}.
    LmobP3 = np.array([
        [1, 0, 0, -1, 0, 0],
        [0, 1, -1, 0, 0, 0],
        [0, -1, 2, 0, -1, 0],
        [-1, 0, 0, 2, 0, -1],
        [0, 0, -1, 0, 1, 0],
        [0, 0, 0, -1, 0, 1]], float)
    check("hand: L_Mob(P3, W={01}) entrywise",
          np.array_equal(connection_laplacian(P3, fs((0, 1))), LmobP3))

    # cover adjacency, hand: C3 with one wrap: cover = C6 (single 6-cycle)
    cov = orientation_cover_adjacency(TRI, W1)
    degs = cov.sum(axis=1)
    check("hand: cover(C3,W={01}) is 2-regular on 6 vertices [Lem 4.3]",
          cov.shape == (6, 6) and np.allclose(degs, 2)
          and int(cov.sum()) == 12)
    check("hand: cover(C3,W={01}) is a single 6-cycle [Thm 5.3, beta=0]",
          len(connected_components(cov)) == 1
          and connected_components(cov) == [(0, 1, 2, 3, 4, 5)])
    cov0 = orientation_cover_adjacency(TRI, set())
    check("hand: cover(C3,W=empty) = two disjoint triangles [Thm 5.3]",
          len(connected_components(cov0)) == 2
          and set(connected_components(cov0)) == {(0, 2, 4), (1, 3, 5)})


def test_hand_spectra():
    print("[2] Hand-derived spectra")
    C3, C4, P3 = cycle_adj(3), cycle_adj(4), path_adj(3)
    Wall3 = fs((0, 1), (1, 2), (0, 2))
    r2 = np.sqrt(2.0)

    def spec_lsc(adj):
        return spectrum(scalar_laplacian(adj))

    def spec_lsg(adj, W):
        return spectrum(signed_laplacian(adj, W))

    check("hand: Spec Lsc(C3) = {0,3,3}",
          np.allclose(spec_lsc(C3), [0, 3, 3]))
    check("hand: Spec Lsg(C3,W=empty) = {0,3,3}",
          np.allclose(spec_lsg(C3, set()), [0, 3, 3]))
    check("hand: Spec Lsg(C3,W={01}) = {1,1,4}  (char poly (l-1)^2(l-4))",
          np.allclose(spec_lsg(C3, fs((0, 1))), [1, 1, 4]))
    check("hand: Spec Lsg(C3,W=2 edges) = {0,3,3}  (char poly l(l-3)^2)",
          np.allclose(spec_lsg(C3, fs((0, 1), (0, 2))), [0, 3, 3]))
    check("hand: Spec Lsg(C3,W=all) = {1,1,4}",
          np.allclose(spec_lsg(C3, Wall3), [1, 1, 4]))

    check("hand: Spec Lsc(C4) = {0,2,2,4}",
          np.allclose(spec_lsc(C4), [0, 2, 2, 4]))
    check("hand: Spec Lsg(C4,W={01}) = {2-sqrt2 x2, 2+sqrt2 x2}",
          np.allclose(spec_lsg(C4, fs((0, 1))),
                      [2 - r2, 2 - r2, 2 + r2, 2 + r2]))
    # 2-wrap cases switch to W=empty on a cycle (hand check: explicit
    # diagonal +-1 conjugation exhibited in each case)
    check("hand: Spec Lsg(C4,W={01,12}) = {0,2,2,4}",
          np.allclose(spec_lsg(C4, fs((0, 1), (1, 2))), [0, 2, 2, 4]))
    check("hand: Spec Lsg(C4,W={01,23}) = {0,2,2,4}",
          np.allclose(spec_lsg(C4, fs((0, 1), (2, 3))), [0, 2, 2, 4]))

    check("hand: Spec Lsc(P3) = {0,1,3}",
          np.allclose(spec_lsc(P3), [0, 1, 3]))
    check("hand: Spec Lsg(P3,W={01}) = {0,1,3}  (char poly l(l-1)(l-3))",
          np.allclose(spec_lsg(P3, fs((0, 1))), [0, 1, 3]))

    # explicit switching conjugation D Lsc D = Lsg for P3, W={01}
    # (d_u d_v = -1 exactly on wrap edges; matches the paper's Example
    #  10.2 witness eps(v0)=top, eps(v1)=eps(v2)=bot)
    D = np.diag([1.0, -1.0, -1.0])
    check("hand: Lsg(P3,W={01}) = D Lsc D with D=diag(1,-1,-1)",
          np.allclose(signed_laplacian(P3, fs((0, 1))),
                      D @ scalar_laplacian(P3) @ D))


def test_hand_kernel_dims():
    print("[3] Hand-derived kernel dimensions (via Cor 9.4 parity + Thms 6.x)")
    C3, C4, P3 = cycle_adj(3), cycle_adj(4), path_adj(3)

    def ker_all(adj, W):
        Lsg = signed_laplacian(adj, W)
        return (kernel_dim(Lsg), kernel_dim(connection_laplacian(adj, W)))

    cases = [
        ("C3 W=empty (beta=1)", cycle_adj(3), set(), (1, 2)),
        ("C3 W={01} (beta=0)", C3, fs((0, 1)), (0, 1)),
        ("C3 W={01,02} (beta=1)", C3, fs((0, 1), (0, 2)), (1, 2)),
        ("C3 W=all (beta=0)", C3, fs((0, 1), (1, 2), (0, 2)), (0, 1)),
        ("C4 W=empty (beta=1)", C4, set(), (1, 2)),
        ("C4 W={01} (beta=0)", C4, fs((0, 1)), (0, 1)),
        ("C4 W={01,12} (beta=1)", C4, fs((0, 1), (1, 2)), (1, 2)),
        ("C4 W={01,23} (beta=1)", C4, fs((0, 1), (2, 3)), (1, 2)),
    ]
    for tag, adj, W, (ksg, kmob) in cases:
        got = ker_all(adj, W)
        check("hand kernels: %s -> ker Lsg=%d, ker L_Mob=%d" % (tag, ksg, kmob),
              got == (ksg, kmob), "got %s" % (got,))
    for W in [set(), fs((0, 1)), fs((1, 2)), fs((0, 1), (1, 2))]:
        got = ker_all(P3, W)
        check("hand kernels: P3 (tree, beta=1) ker Lsg=1 ker L_Mob=2 "
              "[Thm 9.1 / Cor 9.2], W=%s" % (sorted(map(sorted, W)),),
              got == (1, 2), "got %s" % (got,))


def test_paper_examples():
    print("[4] The paper's own examples and remarks")
    # Remark 6.5 (lines 784-802): K4 with wrap matching {{1,2},{3,4}}
    # (paper labels 1..4 -> 0..3 here): beta = 0, dim ker Lsg = 0.
    K4 = complete_adj(4)
    Wm = fs((0, 1), (2, 3))
    check("Rem 6.5: K4 + wrap matching is UNbalanced", beta(K4, Wm) == 0)
    check("Rem 6.5: dim ker Lsg(K4, matching) = 0",
          kernel_dim(signed_laplacian(K4, Wm)) == 0)
    check("Rem 6.5: dim ker L_Mob(K4, matching) = 1 (one component)",
          kernel_dim(connection_laplacian(K4, Wm)) == 1)
    # the false formula (star) would predict 1 for ker Lsg:
    check("Rem 6.5: parity formula (star) would give 1, we must NOT",
          kernel_dim(signed_laplacian(K4, Wm)) != 1)

    # Example 10.1 (lines 1343-1360): empty graph on n=3: every component
    # balanced (vacuous), dim ker L_Mob = 6.
    E3 = empty_adj(3)
    check("Ex 10.1: beta(empty3) = 3 (vacuous balance)",
          beta(E3, set()) == 3)
    check("Ex 10.1: dim ker L_Mob(empty3) = 6",
          kernel_dim(connection_laplacian(E3, set())) == 6)
    check("Ex 10.1: dim ker Lsg(empty3) = 3",
          kernel_dim(signed_laplacian(E3, set())) == 3)

    # Example 10.3 (lines 1376-1392): 3 isolated vertices beta=3; adding a
    # non-wrap edge {v0,v1} drops beta to 2.
    G = empty_adj(3)
    G[0, 1] = G[1, 0] = 1.0
    check("Ex 10.3: beta(3 isolated + edge {0,1}) = 2", beta(G, set()) == 2)

    # Example 10.2 (lines 1362-1374): P3 with single wrap {v0,v1} IS balanced
    P3 = path_adj(3)
    check("Ex 10.2: P3 + wrap {0,1} balanced (bridge wrap)",
          is_balanced_component(P3, fs((0, 1)), (0, 1, 2)))

    # Example 10.4 (lines 1394-1402): K3 with W={{v0,v1}}: ker Lsg = 0.
    check("Ex 10.4: dim ker Lsg(K3, W={01}) = 0",
          kernel_dim(signed_laplacian(cycle_adj(3), fs((0, 1)))) == 0)

    # Remark 7.5 (lines 887-891): C_n with W = E(C_n) balanced iff n even.
    for n, want in [(3, 0), (4, 1), (5, 0), (6, 1)]:
        Cn = cycle_adj(n)
        Wall = set(edges(Cn))
        check("Rem 7.5: beta(C%d, all wrap) = %d" % (n, want),
              beta(Cn, Wall) == want)

    # Corollary 7.4 (lines 867-875): C_n, single wrap edge: ker Lsg = 0 and
    # ker L_Mob = 1 < 2 = ker L_flat for all n >= 3.
    for n in range(3, 7):
        Cn = cycle_adj(n)
        W1 = fs((0, 1))
        check("Cor 7.4: ker Lsg(C%d, {0,1}) = 0" % n,
              kernel_dim(signed_laplacian(Cn, W1)) == 0)
        check("Cor 7.4: ker L_Mob(C%d,{0,1})=1 < 2=ker L_flat" % n,
              kernel_dim(connection_laplacian(Cn, W1)) == 1
              and kernel_dim(flat_laplacian(Cn)) == 2)

    # isolated vertex vacuously balanced (Remark 5.2b)
    check("Rem 5.2b: isolated vertex vacuously balanced",
          is_balanced_component(empty_adj(3), set(), (1,)))


def test_corrected_parity_scope():
    """Regression checks for the corrected Remark 6.5.

    On connected graphs the parity shortcut agrees with the kernel formula
    exactly when balance is equivalent to an even number of wrapped edges.
    These examples explicitly cover both failure directions and cases that
    invalidate the former necessity claim.
    """
    print("[5a] Corrected Remark 6.5: both directions and non-necessity")

    def check_case(tag, A, W, expect):
        B = beta(A, W) == 1
        parity = len(W) % 2 == 0
        shortcut_holds = (B == parity)
        check("Rem 6.5: " + tag, shortcut_holds == expect,
              "balance=%s, even-wrap=%s" % (B, parity))

    K4 = complete_adj(4)
    P3 = path_adj(3)
    bowtie = np.zeros((5, 5))
    for u, v in [(0, 1), (1, 2), (0, 2),
                 (2, 3), (3, 4), (2, 4)]:
        bowtie[u, v] = bowtie[v, u] = 1
    check_case("K4 empty wraps: high H1, shortcut holds",
               K4, set(), True)
    check_case("K4 wrapped matching: unbalanced/even, fails",
               K4, fs((0, 1), (2, 3)), False)
    check_case("K4 single wrapped triangle: unbalanced/odd, holds",
               K4, fs((0, 1), (1, 2), (0, 2)), True)
    check_case("P3 two wrapped bridges: balanced/even, holds",
               P3, fs((0, 1), (1, 2)), True)
    check_case("P3 one wrapped bridge: balanced/odd, fails",
               P3, fs((0, 1)), False)
    check_case("bowtie one wrap per triangle: unbalanced/even, fails",
               bowtie, fs((0, 1), (2, 3)), False)


def test_cycle_spectrum_theorems():
    print("[5] Cycle spectra [Thm 7.1 flat-cycle; Thm 7.2 mobius-cycle]")
    for n in range(3, 7):
        Cn = cycle_adj(n)
        exp_sc = np.sort([2 - 2 * np.cos(2 * np.pi * k / n) for k in range(n)])
        check("Thm 7.1: Spec Lsc(C%d) = {2-2cos(2pi k/n)}" % n,
              np.allclose(spectrum(scalar_laplacian(Cn)),
                          np.round(exp_sc, 8), atol=1e-7))
        exp_sg = np.sort([2 - 2 * np.cos((2 * k + 1) * np.pi / n)
                          for k in range(n)])
        check("Thm 7.2: Spec Lsg(C%d, W={0,1}) = {2-2cos((2k+1)pi/n)}" % n,
              np.allclose(spectrum(signed_laplacian(Cn, fs((0, 1)))),
                          np.round(exp_sg, 8), atol=1e-7))


def test_structural_on_named():
    print("[6] Structural battery on named configurations")
    C3, C4, C5 = cycle_adj(3), cycle_adj(4), cycle_adj(5)
    P3, P4, S3 = path_adj(3), path_adj(4), star_adj(3)
    K4 = complete_adj(4)
    E3p = empty_adj(3)
    E3p[0, 1] = E3p[1, 0] = 1.0
    # disconnected mixed graph: (triangle w/ 1 wrap) + (isolated v) + (P2 w/ wrap)
    MIX = np.zeros((6, 6))
    MIX[0:3, 0:3] = C3
    MIX[4, 5] = MIX[5, 4] = 1.0
    MIXW = fs((0, 1), (4, 5))

    named = [
        ("C3 W=empty", C3, set()),
        ("C3 W={01}", C3, fs((0, 1))),
        ("C3 W={01,02}", C3, fs((0, 1), (0, 2))),
        ("C3 W=all", C3, fs((0, 1), (1, 2), (0, 2))),
        ("C4 W=empty", C4, set()),
        ("C4 W={01}", C4, fs((0, 1))),
        ("C4 W=adj2{01,12}", C4, fs((0, 1), (1, 2))),
        ("C4 W=opp2{01,23}", C4, fs((0, 1), (2, 3))),
        ("C4 W=3 edges", C4, fs((0, 1), (1, 2), (2, 3))),
        ("C4 W=all", C4, fs((0, 1), (1, 2), (2, 3), (0, 3))),
        ("P3 W={01}", P3, fs((0, 1))),
        ("P4 W={01,23}", P4, fs((0, 1), (2, 3))),
        ("P4 W=all", P4, set(edges(P4))),
        ("K1,3 W={01}", S3, fs((0, 1))),
        ("K1,3 W=all", S3, set(edges(S3))),
        ("K4 W=matching", K4, fs((0, 1), (2, 3))),
        ("K4 W=empty", K4, set()),
        ("K4 W=all", K4, set(edges(K4))),
        ("C5 W={01}", C5, fs((0, 1))),
        ("C5 W=all", C5, set(edges(C5))),
        ("empty3", empty_adj(3), set()),
        ("empty3+edge01", E3p, set()),
        ("mixed disconnected", MIX, MIXW),
    ]
    for tag, adj, W in named:
        structural_battery(tag, adj, W)
    print("  ...battery done for %d named configs (%d checks each)"
          % (len(named), 25))


def test_exhaustive_cycles():
    print("[7] Exhaustive wrap subsets on cycles C3, C4, C5 [Cor 9.4]")
    total = 0
    for n in (3, 4, 5):
        Cn = cycle_adj(n)
        E = edges(Cn)
        for r in range(len(E) + 1):
            for combo in itertools.combinations(E, r):
                W = set(combo)
                bal = 1 if len(W) % 2 == 0 else 0
                ok = check("Cor 9.4: beta(C%d) = parity(#W) for |W|=%d"
                           % (n, r), beta(Cn, W) == bal)
                structural_battery("C%d|W|=%d" % (n, r), Cn, W)
                total += 1
    print("  ...%d cycle configurations, all structural checks" % total)


def test_exhaustive_trees():
    print("[8] Exhaustive wrap subsets on trees P3, P4, K1,3 [Thm 9.1]")
    total = 0
    for tag, T in [("P3", path_adj(3)), ("P4", path_adj(4)),
                   ("K1,3", star_adj(3))]:
        E = edges(T)
        for r in range(len(E) + 1):
            for combo in itertools.combinations(E, r):
                W = set(combo)
                check("Thm 9.1: %s always balanced (|W|=%d)" % (tag, r),
                      beta(T, W) == 1)
                check("Cor 9.2: ker L_Mob(%s) = 2 (|W|=%d)" % (tag, r),
                      kernel_dim(connection_laplacian(T, W)) == 2)
                structural_battery("%s|W|=%d" % (tag, r), T, W)
                total += 1
    print("  ...%d tree configurations, all structural checks" % total)


def test_random_sweep():
    print("[9] Seeded random sweep, n in 2..6 (Thms 6.2, 6.3, 8.6, 5.3)")
    rng = np.random.default_rng(20260815)
    total = 0
    for t in range(250):
        n = int(rng.integers(2, 7))
        U = np.triu((rng.random((n, n)) < 0.5).astype(float), 1)
        A = U + U.T
        E = edges(A)
        pick = rng.random()
        if pick < 0.1:
            W = set(E)                       # force all-wrap sometimes
        elif pick < 0.2:
            W = set()                        # force empty sometimes
        else:
            W = {e for e in E if rng.random() < 0.4}
        structural_battery("rand%03d(n=%d)" % (t, n), A, W)
        total += 1
    print("  ...%d random configurations, all structural checks" % total)


def main():
    print("=" * 72)
    print("selftest.py -- internal sanity checks for independent_impl.py")
    print("sources of truth: paper/paper.tex theorems + hand computations")
    print("=" * 72)
    test_hand_matrices()
    test_hand_spectra()
    test_hand_kernel_dims()
    test_paper_examples()
    test_corrected_parity_scope()
    test_cycle_spectrum_theorems()
    test_structural_on_named()
    test_exhaustive_cycles()
    test_exhaustive_trees()
    test_random_sweep()
    print("=" * 72)
    print("TOTAL individual checks: %d" % NCHECKS[0])
    if FAILURES:
        print("FAILURES: %d" % len(FAILURES))
        for f in FAILURES[:40]:
            print("   - %s" % f)
        sys.exit(1)
    print("ALL CHECKS PASSED")
    sys.exit(0)


if __name__ == "__main__":
    main()
