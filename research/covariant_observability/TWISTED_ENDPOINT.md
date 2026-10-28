# Exact endpoint norm of a twisted rank-one cycle

**Date:** 2026-10-28. **Scope:** finite scalar \(U(1)\) graph bundles; \(C_n\), \(n\ge 3\), with nontrivial holonomy \(e^{i\theta}\), \(0<\theta<2\pi\). **Status:** elementary finite Fourier derivation (P in ordinary mathematics) and a separately implemented spectral numerical cross-check (M). **No Lean theorem for this identity yet.** This is a post-submission development on \`dev\`, not part of the HAL/arXiv candidate and not represented as novel harmonic analysis.

## The uniform gauge

Every rank-one cycle with total holonomy \(e^{i\theta}\) is gauge-equivalent, up to reversing the winding orientation, to the uniformly distributed twist

\[
(D_\theta f)(j)=f(j)-e^{i\theta/n}f(j+1\bmod n),\quad
L_\theta=D_\theta^*D_\theta,\quad
R_\theta=D_\theta L_\theta^{-1/2}.
\]

Here \(L_\theta\) is **invertible** for \(0<\theta<2\pi\), so the ordinary inverse square root exists. For \(\theta=0\), a zero eigenvalue appears and \(L^\dagger\), not \(L^{-1}\), must be used.

Gauge transformations multiply the vertex and edge spaces by diagonal unitary matrices. They preserve the induced \(\ell^1\), \(\ell^2\) and \(\ell^\infty\) matrix norms because their diagonal entries have modulus one. The repository's \`cycle(n, phase)\` has the twist concentrated on the closing edge, with the stored orientation reversed; it is covered by this gauge argument.

## Fourier calculation

For \(e_k(j)=e^{2\pi i kj/n}\), \(0\le k<n\), define \(\phi_k=(2\pi k+\theta)/n\). Then

\[
D_\theta e_k=(1-e^{i\phi_k})e_k,\qquad
L_\theta e_k=4\sin^2(\phi_k/2)e_k.
\]

Because \(0<\phi_k<2\pi\), each sine \(\sin(\phi_k/2)\) is strictly positive. Consequently the normalized multiplier is

\[
m_k=\frac{1-e^{i\phi_k}}{|1-e^{i\phi_k}|}
=-i\,e^{i\phi_k/2},\quad |m_k|=1.
\]

Writing \(d=j-\ell\) and \(q=e^{2\pi i(d+1/2)/n}\), we have \(q^n=-1\) and \(q\ne1\). The inverse Fourier series is

\[
(R_\theta)_{j\ell}
=-\frac{i\,e^{i\theta/(2n)}}{n}
\sum_{k=0}^{n-1}q^k
=-\frac{2i\,e^{i\theta/(2n)}}{n(1-q)}.
\]

Therefore **every absolute matrix entry is independent of the twist angle**:

\[
\boxed{\quad
|(R_\theta)_{j\ell}|=
\frac1{n\,|\sin(\pi(j-\ell+1/2)/n)|}.
\quad}
\]

The absolute row and column sums are equal by cyclicity, hence

\[
\boxed{
\|R_\theta\|_{\ell^\infty\to\ell^\infty}
=\|R_\theta\|_{\ell^1\to\ell^1}
=\frac1n\sum_{d=0}^{n-1}
\csc\left(\frac{\pi(d+1/2)}{n}\right)
=\frac2\pi\log n+O(1).
}
\]

At the same time, \(\|R_\theta\|_{\ell^2\to\ell^2}=1\), by the unimodular Fourier multipliers. The phase-independent endpoint norm coexists with a **phase-dependent spectral gap**

\[
\lambda_{\min}=2-2\cos\left(\frac{\operatorname{dist}(\theta,2\pi\mathbb Z)}{n}\right),
\]

which shows that a collapsing spectral gap alone does not determine the Riesz norm.

## Exact relation to the untwisted case

Let \(F(n)=\|R_0(C_n)\|_{\ell^\infty\to\ell^\infty}\), using the pseudoinverse and zero-mode projection. The existing [ENDPOINT.md](ENDPOINT.md) derives

\[
F(n)=\frac1n\sum_{d=0}^{n-1}
\left|\cot\left(\frac{\pi(d+1/2)}n\right)\right|.
\]

For every \(n\ge3\) and every **nonzero** twist \(\theta\pmod{2\pi}\),

\[
\boxed{\quad\|R_\theta(C_n)\|_{\infty\to\infty}=F(2n).\quad}
\]

Proof: the symmetry of the cotangent around \(\pi/2\) gives

\[
F(2n)=\frac1n\sum_{d=0}^{n-1}
\cot\left(\frac{\pi(d+1/2)}{2n}\right).
\]

Use the identity \(\cot(x/2)=\csc x+\cot x\), and note that
\(\sum_{d=0}^{n-1}\cot(\pi(d+1/2)/n)=0\) by pairing \(d\) with \(n-1-d\). The claim follows.

**Subtlety:** at \(\theta=0\), the kernel suddenly acquires a constant parallel section; the Moore-Penrose partial isometry loses one Fourier mode. Thus the norm at *exactly* trivial holonomy need not equal the limit from nontrivial holonomy. This is a spectral-rank discontinuity, not an indication of computational advantage.

## Independent checks and boundaries

Run \`python research/covariant_observability/test_twisted_endpoint.py\`. It checks **24 configurations**: six graph sizes \(n=5,8,16,32,64,128\) and four phases \(\theta=0.1,1.2,3.1,5.8\). For each it compares:

1. the closed-form Fourier matrix entries;
2. independent dense diagonalization of \(D_\theta^*D_\theta\) with uniformly distributed phase;
3. the existing \`experiment.cycle\` convention, which concentrates the phase on one edge;
4. the exact \(F(2n)\) identity.

A local NumPy 2.3.5 run showed a maximum Fourier-kernel entry error below \(8\times10^{-13}\). This is a bounded numerical check; the derivation above is the mathematical evidence.

This result **does not** transfer classical Euclidean Calderón–Zygmund estimates to general finite graph bundles, prove any dimension-uniform interior \(L^p\) bound, imply asymptotic computational speedups, or establish novelty beyond existing discrete Fourier analysis. A next meaningful Lean step would formalize this elementary finite Fourier identity, but the **higher priority remains the actual \(\mathbb Z/2\) global incidence identity \(D^\mathsf{T}D=L\)**.
