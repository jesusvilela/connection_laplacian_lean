# Exact endpoint obstruction on flat cycles

**Status:** elementary mathematical derivation, written after the paper submission, and independent floating-point regression. **Not a Lean theorem yet.** This result is classical in spirit and is not claimed to be new discrete harmonic analysis.

## Statement

For the cycle \(C_n\), \(n\ge3\), orient all edges cyclically and take the flat rank-one connection. Write \(S f(j)=f(j+1\bmod n)\), \(D=I-S\), \(L=D^*D\), and \(R=D(L^\dagger)^{1/2}\), with the positive-spectrum inverse square root.

Then the real matrix kernel is

\[
R_{j\ell}=\frac1n\cot\left(\frac{\pi(2(j-\ell)+1)}{2n}\right).
\]

In particular,

\[
\boxed{
\|R\|_{\ell^\infty(C_n)\to\ell^\infty(E_n)}
=\|R\|_{\ell^1(C_n)\to\ell^1(E_n)}
=\frac1n\sum_{d=0}^{n-1}
\left|\cot\frac{\pi(d+\tfrac12)}{n}\right|
=\frac2\pi\log n+O(1)
}
\]

while \(\|R\|_{\ell^2\to\ell^2}=1\) for every \(n\). Thus **there is no graph-size-independent \(\ell^\infty\) or \(\ell^1\) bound for the covariant Riesz transforms over all flat degree-two cycles**, even though their \(L^2\) norm is universally one.

Here the edge space has exactly \(n\) edges, so these are the usual induced matrix operator norms. Arbitrarily reversing edge orientations multiplies corresponding rows by \(-1\), leaving these endpoint norms unchanged.

## Derivation (P, finite-dimensional mathematics)

The Fourier vectors \(e_k(j)=\exp(2\pi i k j/n)\), \(0\le k<n\), are eigenvectors of \(S\). Hence

\[
De_k=(1-e^{2\pi i k/n})e_k,\qquad
Le_k=4\sin^2(\pi k/n)e_k.
\]

At \(k=0\), \(R e_0=0\). For \(1\le k<n\), \(\sin(\pi k/n)>0\), so

\[
Re_k=m_ke_k,\qquad
m_k=\frac{1-e^{2\pi i k/n}}{2\sin(\pi k/n)}
=-i e^{\pi i k/n}.
\]

The inverse discrete Fourier transform yields, with \(d=j-\ell\),

\[
R_{j\ell}=-\frac{i}{n}\sum_{k=1}^{n-1}
\exp\left(\frac{\pi i k(2d+1)}{n}\right).
\]

Set \(q=\exp(\pi i(2d+1)/n)\). Since \(q^n=-1\) and \(q\ne1\),

\[
\sum_{k=1}^{n-1}q^k
=\frac{1+q}{1-q}
=i\cot\left(\frac{\pi(2d+1)}{2n}\right).
\]

This proves the displayed kernel. Each row is a cyclic shift of every other row; so the induced \(\ell^\infty\) norm is the absolute row sum, and the induced \(\ell^1\) norm is the identical absolute column sum.

For the asymptotic, write \(x_d=\pi(d+\tfrac12)/n\). On \(0<x\le\pi/4\), the Taylor estimate \(\cot x=1/x+O(x)\) is uniform. Consequently the first \(n/4\) terms contribute

\[
\frac1n\sum_{0\le d\lesssim n/4}\cot x_d
=\frac1\pi\sum_{0\le d\lesssim n/4}\frac1{d+\tfrac12}+O(1)
=\frac1\pi\log n+O(1).
\]

By symmetry the terms near \(\pi\) contribute the same; the central terms have bounded cotangent and contribute \(O(1)\) after division by \(n\). Therefore the full sum is \((2/\pi)\log n+O(1)\), as claimed.

Finally, \(\|R\|_{2\to2}=\max_{k\ne0}|m_k|=1\). This is also a special case of \(R^*R=I-P_0\).

## Independent numerical cross-check (M)

The separate *test_endpoint.py* file computes \(R\) by a Hermitian eigendecomposition of \(D^*D\), then compares **every** matrix entry against the closed-form cotangent kernel for \(n=5,8,16,32,64,128\). It corrects the closing-edge sign because the shared incidence generator stores edges as pairs \(u<v\), whereas the derivation orients the last edge cyclically.

At \(n=128\), the maximum entrywise disagreement in the pinned local NumPy experiment was approximately \(8.6\times10^{-15}\); the measured endpoint norm was approximately \(3.61016\), versus an exactly predicted cotangent sum of \(3.61016\). These are machine-precision cross-checks, **not** the evidence for the theorem: the derivation above is.

## Implications and honest frontier

- **P:** dimension-uniform \(\ell^\infty\) and \(\ell^1\) boundedness fail for this graph class. Uniform \(\ell^2\) boundedness holds exactly.
- **H:** identify restrictions under which the discrete \(1<p<\infty\) norms stay bounded independently of graph size and fiber rank. The flat cycle does not falsify these interior-\(p\) possibilities.
- **H:** seek suitable matrix-valued Calderon-Zygmund or heat-kernel hypotheses on **specified** graph families. Euclidean statements from Tao's notes cannot simply be quoted for arbitrary graphs.
- **S:** an observability hierarchy is useful only when each new operator has an explicit invariant, hypothesis and failure mode.

**Do not merge this analysis into the submitted paper without a distinct revision and attribution check.**