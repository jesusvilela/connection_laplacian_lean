"""Deterministic finite-graph experiments for covariant observability.

Research code, not part of the submitted Z/2 Lean manuscript. Requires numpy.
Run: python research/covariant_observability/experiment.py --verify
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass

import numpy as np


@dataclass
class Connection:
    vertices: int
    edges: list[tuple[int, int]]
    transport: list[np.ndarray]  # U_uv maps fiber at v to fiber at u
    rank: int | None = None       # mandatory on graphs with no edges

    def fiber_rank(self) -> int:
        if self.rank is not None:
            if self.rank < 1:
                raise ValueError("fiber rank must be positive")
            return self.rank
        if not self.transport:
            raise ValueError("specify the fiber rank for an edgeless graph")
        shape = self.transport[0].shape
        if len(shape) != 2 or shape[0] != shape[1] or shape[0] < 1:
            raise ValueError("transport must be a nonempty square matrix")
        return int(shape[0])

    def incidence(self) -> np.ndarray:
        if self.vertices < 1:
            raise ValueError("this numerical harness requires at least one vertex")
        if len(self.edges) != len(self.transport):
            raise ValueError("each edge must have exactly one transport")
        if len(set(self.edges)) != len(self.edges):
            raise ValueError("duplicate edges violate the simple-graph contract")
        rank = self.fiber_rank()
        mat = np.zeros((len(self.edges) * rank, self.vertices * rank), dtype=complex)
        for ei, ((u, v), U) in enumerate(zip(self.edges, self.transport)):
            if not (0 <= u < v < self.vertices):
                raise ValueError("edges must be distinct oriented pairs u < v")
            if U.shape != (rank, rank) or not np.allclose(U.conj().T @ U, np.eye(rank), atol=1e-11):
                raise ValueError("parallel transport must be unitary")
            mat[ei * rank:(ei + 1) * rank, u * rank:(u + 1) * rank] = np.eye(rank)
            mat[ei * rank:(ei + 1) * rank, v * rank:(v + 1) * rank] = -U
        return mat

    def gauge(self, gs: list[np.ndarray]) -> "Connection":
        r = self.fiber_rank()
        if len(gs) != self.vertices or any(
            g.shape != (r, r) or not np.allclose(g.conj().T @ g, np.eye(r), atol=1e-11)
            for g in gs
        ):
            raise ValueError("provide one unitary gauge per vertex")
        return Connection(self.vertices, self.edges[:],
                          [gs[u] @ U @ gs[v].conj().T
                           for (u, v), U in zip(self.edges, self.transport)],
                          rank=r)


def cycle(n: int, phase: float = 0.0, rank: int = 1) -> Connection:
    if n < 3:
        raise ValueError("simple cycles have n >= 3")
    edges = [(i, i + 1) for i in range(n - 1)] + [(0, n - 1)]
    transports = [np.eye(rank, dtype=complex) for _ in edges]
    transports[-1][0, 0] = np.exp(1j * phase)
    return Connection(n, edges, transports, rank=rank)


def z2_bundle(vertices: int, edges: list[tuple[int, int]],
              wrapped: set[tuple[int, int]]) -> Connection:
    swap = np.array([[0, 1], [1, 0]], dtype=complex)
    if not wrapped.issubset(set(edges)):
        raise ValueError("all wrapped edges must exist")
    return Connection(vertices, edges,
                      [swap.copy() if edge in wrapped else np.eye(2, dtype=complex)
                       for edge in edges], rank=2)


def random_unitary(rank: int, rng: np.random.Generator) -> np.ndarray:
    z = rng.normal(size=(rank, rank)) + 1j * rng.normal(size=(rank, rank))
    q, r = np.linalg.qr(z)
    diagonal = np.diag(r)
    return q * (diagonal / np.abs(diagonal))[np.newaxis, :]


def block_diagonal(blocks: list[np.ndarray]) -> np.ndarray:
    rank = blocks[0].shape[0]
    out = np.zeros((len(blocks) * rank, len(blocks) * rank), dtype=complex)
    for k, block in enumerate(blocks):
        out[k * rank:(k + 1) * rank, k * rank:(k + 1) * rank] = block
    return out


def norm_inf(M: np.ndarray) -> float:
    return float(np.max(np.abs(M))) if M.size else 0.0


def observables(D: np.ndarray) -> dict:
    """Finite spectral calculus. Eigenvalues <= 1e-10*max(1,lambda_max) are zero."""
    L = D.conj().T @ D
    vals, Q = np.linalg.eigh(L)
    cutoff = 1e-10 * max(1.0, float(np.max(vals)))
    active = vals > cutoff
    Qa, eig = Q[:, active], vals[active]
    Qz = Q[:, ~active]
    P0 = Qz @ Qz.conj().T
    Pin = Qa @ Qa.conj().T
    S = (Qa * (1.0 / np.sqrt(eig))) @ Qa.conj().T if len(eig) else np.zeros_like(L)
    R = D @ S
    assert norm_inf(R.conj().T @ R - Pin) < 2e-8
    assert norm_inf(P0 + Pin - np.eye(L.shape[0])) < 2e-8
    # Finite Littlewood-Paley: squared partition on strictly positive spectrum.
    filters = []
    if len(eig):
        log_eig = np.log2(eig)
        js = np.arange(math.floor(float(np.min(log_eig))) - 2,
                       math.ceil(float(np.max(log_eig))) + 3)
        w = np.exp(-0.5 * ((log_eig[np.newaxis, :] - js[:, np.newaxis]) / 0.85) ** 2)
        w /= np.sqrt(np.sum(w * w, axis=0))[np.newaxis, :]
        filters = [(Qa * w[j, :]) @ Qa.conj().T for j in range(len(js))]
    LP = P0.copy()
    for F in filters:
        LP += F.conj().T @ F
    assert norm_inf(LP - np.eye(L.shape[0])) < 2e-8
    return {"L": L, "P0": P0, "R": R, "filters": filters,
            "eigenvalues": vals, "nullity": int(len(vals) - len(eig)),
            "riesz_error": norm_inf(R.conj().T @ R - (np.eye(L.shape[0]) - P0)),
            "LP_error": norm_inf(LP - np.eye(L.shape[0]))}


def holonomy_fixed_dimension(conn: Connection) -> tuple[int, list[np.ndarray]]:
    """Spanning-tree holonomies: common fixed vectors determine parallel sections.

    Requires a connected graph. Tree-edge constraints cancel by construction.
    """
    r = conn.fiber_rank()
    adj = [[] for _ in range(conn.vertices)]
    for ei, ((u, v), U) in enumerate(zip(conn.edges, conn.transport)):
        adj[u].append((v, U.conj().T, ei))
        adj[v].append((u, U, ei))
    T = [None] * conn.vertices
    T[0] = np.eye(r, dtype=complex)
    queue = [0]
    tree_edges = set()
    for vertex in queue:
        for next_v, transfer, ei in adj[vertex]:
            if T[next_v] is None:
                T[next_v] = transfer @ T[vertex]
                tree_edges.add(ei)
                queue.append(next_v)
    if any(t is None for t in T):
        raise ValueError("holonomy-fixed calculation requires connected graph")
    holonomies = [T[u].conj().T @ U @ T[v]
                  for ei, ((u, v), U) in enumerate(zip(conn.edges, conn.transport))
                  if ei not in tree_edges]
    equations = ([H - np.eye(r) for H in holonomies])
    if not equations:
        return r, holonomies
    singular = np.linalg.svd(np.concatenate(equations, axis=0), compute_uv=False)
    rank_constraints = int(np.count_nonzero(singular > 1e-9))
    return r - rank_constraints, holonomies


def verify_case(name: str, conn: Connection, rng: np.random.Generator,
                expected_nullity: int) -> dict:
    D = conn.incidence()
    out = observables(D)
    holonomy_dim, holonomies = holonomy_fixed_dimension(conn)
    assert holonomy_dim == out["nullity"], (name, holonomy_dim, out["nullity"])
    if out["nullity"] != expected_nullity:
        raise AssertionError(f"{name}: nullity {out['nullity']} != {expected_nullity}")
    f = rng.normal(size=D.shape[1]) + 1j * rng.normal(size=D.shape[1])
    lhs = np.vdot(f, f).real
    rhs = np.vdot(out["P0"] @ f, out["P0"] @ f).real + sum(
        np.vdot(F @ f, F @ f).real for F in out["filters"])
    energy_err = abs(lhs - rhs) / max(1, abs(lhs))
    assert energy_err < 2e-9
    rank = conn.fiber_rank()
    gs = [random_unitary(rank, rng) for _ in range(conn.vertices)]
    G = block_diagonal(gs)
    H = block_diagonal([gs[u] for u, _ in conn.edges])
    gauged = conn.gauge(gs)
    Dp = gauged.incidence()
    gauge_incidence_err = norm_inf(Dp @ G - H @ D)
    gp = observables(Dp)
    gauged_holonomy_dim, gauged_holonomies = holonomy_fixed_dimension(gauged)
    assert gauged_holonomy_dim == holonomy_dim
    for H0, H1 in zip(holonomies, gauged_holonomies):
        assert norm_inf(H1 - gs[0] @ H0 @ gs[0].conj().T) < 2e-8
    gauge_laplacian_err = norm_inf(gp["L"] @ G - G @ out["L"])
    gauge_riesz_err = norm_inf(gp["R"] @ G - H @ out["R"])
    gauge_spectral_err = float(np.max(np.abs(gp["eigenvalues"] - out["eigenvalues"])))
    assert max(gauge_incidence_err, gauge_laplacian_err,
               gauge_riesz_err, gauge_spectral_err) < 2e-8
    return {"case": name, "vertices": conn.vertices, "edges": len(conn.edges),
            "rank": rank, "nullity": out["nullity"],
            "spanning_tree_holonomy_fixed_dim": holonomy_dim,
            "fundamental_cycles": len(holonomies),
            "riesz_error": out["riesz_error"], "LP_error": out["LP_error"],
            "energy_error": float(energy_err),
            "gauge_incidence_error": gauge_incidence_err,
            "gauge_laplacian_error": gauge_laplacian_err,
            "gauge_riesz_error": gauge_riesz_err,
            "gauge_spectral_error": gauge_spectral_err}


def run(seed: int = 20261028) -> dict:
    rng = np.random.default_rng(seed)
    cases = []
    edges_tree = [(i, i + 1) for i in range(5)]
    edges_triangle = [(0, 1), (1, 2), (0, 2)]
    cases.append(verify_case("flat Z2 cycle", z2_bundle(9, cycle(9).edges, set()), rng, 2))
    cases.append(verify_case("single-wrap Z2 cycle", z2_bundle(3, edges_triangle, {(0, 2)}), rng, 1))
    # Important counterexample to raw wrap-cardinality parity: a tree has no holonomy cycles.
    cases.append(verify_case("one-wrap tree still balanced", z2_bundle(6, edges_tree, {(1, 2)}), rng, 2))
    theta = 1.2
    cases.append(verify_case("U1 twisted cycle", cycle(13, theta), rng, 0))
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    sz = np.diag([1, np.exp(0.7j)])
    assert norm_inf(sx @ sz - sz @ sx) > 0.1
    noncomm = Connection(4, [(0, 1), (1, 2), (0, 2), (0, 3), (2, 3)],
                         [sx, sz, np.eye(2), np.eye(2), sz])
    cases.append(verify_case("noncommuting U2 transport", noncomm, rng, 0))
    # Paired controls: same connected topology and compute, identity vs generic U(2) transports.
    # Their differences are not evidence of faster computation, only of observable holonomy.
    paired = []
    for n in [4, 6, 8]:
        edges = [(i, i + 1) for i in range(n - 1)]
        edges += [(i, j) for i in range(n) for j in range(i + 2, n)
                  if rng.random() < 0.35]
        flat = Connection(n, edges, [np.eye(2, dtype=complex) for _ in edges])
        twisted = Connection(n, edges, [random_unitary(2, rng) for _ in edges])
        flat_result = verify_case(f"paired flat n={n}", flat, rng, 2)
        # This expected answer is structural, NOT obtained from the holonomy
        # routine being tested. On a tree every U(2) connection has two
        # parallel modes; with a cycle, continuously sampled generic U(2)
        # transport has no fixed vector with probability one.
        expected_twisted_nullity = 2 if len(edges) == n - 1 else 0
        twisted_result = verify_case(f"paired U2 n={n}", twisted, rng, expected_twisted_nullity)
        paired.append({"vertices": n, "edges": len(edges),
                       "flat_nullity": flat_result["nullity"],
                       "twisted_nullity": twisted_result["nullity"],
                       "expected_twisted_nullity": expected_twisted_nullity,
                       "flat_LP_error": flat_result["LP_error"],
                       "twisted_LP_error": twisted_result["LP_error"]})
    # Analytical finite-cycle spectrum and controlled shrinking gap.
    gaps = []
    for n in [8, 16, 32, 64, 128]:
        out = observables(cycle(n, theta).incidence())
        expected = np.sort([2 - 2 * np.cos((2 * np.pi * k + theta) / n)
                            for k in range(n)])
        error = float(np.max(np.abs(np.sort(out["eigenvalues"]) - expected)))
        assert error < 2e-10, (n, error)
        gap = float(np.min(out["eigenvalues"]))
        # Coordinate ell-infinity norm, meaningful for rank-one unitary fibers only.
        # This is a finite-size endpoint diagnostic, not an asymptotic proof.
        endpoint_inf_norm = float(np.max(np.sum(np.abs(out["R"]), axis=1)))
        gaps.append({"n": n, "gap": gap, "closed_form_error": error,
                     "rescaled_gap": gap * n * n / (theta * theta),
                     "inverse_sqrt_norm": 1.0 / math.sqrt(gap),
                     "riesz_linf_operator_norm": endpoint_inf_norm})
    slope = float(np.polyfit(np.log([x["n"] for x in gaps]),
                            np.log([x["gap"] for x in gaps]), 1)[0])
    assert abs(slope + 2) < 0.03, slope
    assert abs(gaps[-1]["rescaled_gap"] - 1) < 0.01
    assert all(b["riesz_linf_operator_norm"] > a["riesz_linf_operator_norm"]
               for a, b in zip(gaps, gaps[1:]))
    endpoint_slope = float(np.polyfit(np.log2([x["n"] for x in gaps]),
                                      [x["riesz_linf_operator_norm"] for x in gaps], 1)[0])
    # Reject a nonunitary transport: otherwise the covariant energy interpretation breaks.
    nonunitary_rejected = False
    try:
        Connection(2, [(0, 1)], [np.array([[2.0 + 0j]])]).incidence()
    except ValueError:
        nonunitary_rejected = True
    assert nonunitary_rejected
    return {"experiment": "finite covariant observability / prereg-v0",
            "seed": seed, "numpy_version": np.__version__,
            "cases": cases, "paired_controls": paired, "cycle_theta": theta, "cycle_gaps": gaps,
            "log_log_gap_slope": slope, "endpoint_linf_growth_per_doubling": endpoint_slope,
            "nonunitary_rejected": nonunitary_rejected,
            "claims": {"P": "finite Hilbert-space identities (mathematical proof in README)",
                       "M": "floating-point checks for listed cases; not a Lean proof",
                       "H": "uniform Lp bounds over graph families (not tested here)"}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", action="store_true", help="run all deterministic assertions")
    parser.add_argument("--seed", type=int, default=20261028)
    args = parser.parse_args()
    print(json.dumps(run(seed=args.seed), indent=2))
