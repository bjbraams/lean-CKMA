# Synopsis: Wavelets, frames, time–frequency analysis, and sampling

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKMA-bib.md#ckma-29);
[MSC2020 correspondence and cross-subject index](CKMA-MSC2020.md).

This synopsis selects recurring mathematical content in Section 29 of
[CKMA-bib.md](CKMA-bib.md#ckma-29). It covers
stable expansions in Hilbert spaces, multiresolution and wavelets, continuous
and discrete time–frequency analysis, sampling, and the basic sparse-recovery
principles shared by the later references. Algorithmic and engineering
details are outside its scope.

Inner products are linear in the first variable. Use
$\widehat f(\xi)=\int f(t)e^{-2\pi it\cdot\xi}dt$,
$T_xf(t)=f(t-x)$, and $M_\omega f(t)=e^{2\pi i\omega\cdot t}f(t)$.
Wavelet and sampling formulas are one dimensional unless stated otherwise;
frame and short-time Fourier-transform results apply in arbitrary dimension.

## Frames, bases, and stable reconstruction

A sequence $(f_k)$ in a Hilbert space $H$ is a **frame** if
$A\|f\|^2\leq\sum_k|\langle f,f_k\rangle|^2\leq B\|f\|^2$
for constants $0<A\leq B<\infty$. The upper bound alone defines a
**Bessel sequence**. A **Riesz basis** is the image of an orthonormal
basis under a bounded invertible operator. A frame is **tight** if $A=B$,
and **Parseval** if $A=B=1$. A **Riesz sequence** is a Riesz basis
for its closed linear span.

* **1. Analysis and synthesis.** The analysis operator
  $Cf=(\langle f,f_k\rangle)_k$ is bounded exactly when $(f_k)$
  is Bessel. Its adjoint is synthesis,
  $C^*c=\sum_kc_kf_k$, with unconditional convergence for $c\in\ell^2$.
* **2. Frame operator criterion.** A Bessel sequence is a frame exactly
  when $S=C^*C$ is boundedly invertible; equivalently
  $AI\leq S\leq BI$. It is also equivalent to synthesis being onto $H$.
* **3. Canonical dual reconstruction.** The sequence
  $\widetilde f_k=S^{-1}f_k$ is a frame, and
  $f=\sum_k\langle f,\widetilde f_k\rangle f_k
  =\sum_k\langle f,f_k\rangle\widetilde f_k$ unconditionally in $H$.
  Its optimal bounds are the reciprocals of the original optimal bounds,
  in reverse order.
* **4. Parseval normalization.** $(S^{-1/2}f_k)$ is a Parseval frame.
  For an $A$-tight frame,
  $f=A^{-1}\sum_k\langle f,f_k\rangle f_k$.
* **5. Minimal coefficient norm.** Among all $c\in\ell^2$ satisfying
  $C^*c=f$, the canonical coefficients
  $(\langle f,S^{-1}f_k\rangle)$ uniquely minimize $\|c\|_2$;
  they are the unique solution in $\operatorname{ran}C=(\ker C^*)^\perp$.
* **6. Riesz basis characterization.** A complete sequence is a Riesz
  basis exactly when
  $A\sum|c_k|^2\leq\|\sum c_kf_k\|^2\leq B\sum|c_k|^2$
  for finite scalar sequences. It has a unique biorthogonal dual and
  unique expansion coefficients.
* **7. Exact frames.** A frame is a Riesz basis exactly when removal
  of any single vector destroys the frame property. General frames may
  be redundant and have many duals.
* **8. Dual-frame criterion.** Bessel sequences $(f_k),(g_k)$ are dual
  exactly when $D_fC_g=I$, where $D_f$ denotes synthesis. Then also
  $D_gC_f=I$, and both reconstruction formulas hold unconditionally.
* **9. Frame perturbation.** If $(f_k)$ is a frame with bounds $A,B$ and
  $\sum_k|\langle f,f_k-g_k\rangle|^2\leq\varepsilon\|f\|^2$
  with $\varepsilon<A$, then $(g_k)$ is a frame with bounds
  $(\sqrt A-\sqrt\varepsilon)^2$ and
  $(\sqrt B+\sqrt\varepsilon)^2$.
* **10. Naimark dilation.** Every Parseval frame is the orthogonal
  projection of an orthonormal basis in a larger Hilbert space.
  Conversely such projections always form Parseval frames.
* **11. Finite tight-frame criterion.** Vectors $f_1,\ldots,f_N$ in
  $\mathbb C^d$ are $A$-tight exactly when
  $\sum_k f_kf_k^*=AI$. If all have norm one, then $A=N/d$.
* **12. Welch bound.** For $N>d$ unit vectors in $\mathbb C^d$,
  $\max_{j\ne k}|\langle f_j,f_k\rangle|^2\geq(N-d)/(d(N-1))$.
  Equality is equivalent to a tight frame with constant absolute
  off-diagonal inner products.

## Multiresolution and orthonormal wavelets

An **orthonormal dyadic wavelet** is a function $\psi$ for which
$\psi_{j,k}(t)=2^{j/2}\psi(2^jt-k)$, $j,k\in\mathbb Z$, is an
orthonormal basis of $L^2(\mathbb R)$. A **multiresolution analysis**
(MRA) is a nested family $V_j$ with dense union, zero intersection,
$f\in V_j\iff f(2\cdot)\in V_{j+1}$, and an orthonormal basis
$(\phi(\cdot-k))_k$ of $V_0$.

* **13. Orthogonal multiresolution decomposition.** With
  $W_j=V_{j+1}\ominus V_j$, one has
  $L^2=\bigoplus_{j\in\mathbb Z}W_j$ and
  $L^2=V_J\oplus\bigoplus_{j\geq J}W_j$.
* **14. Refinement equation.** An MRA scaling function satisfies
  $\phi(t)=\sqrt2\sum_kh_k\phi(2t-k)$ with $(h_k)\in\ell^2$.
  Thus $\widehat\phi(2\xi)=m_0(\xi)\widehat\phi(\xi)$,
  $m_0(\xi)=2^{-1/2}\sum_kh_ke^{-2\pi ik\xi}$.
* **15. Quadrature mirror identities.** Orthonormality gives
  $\sum_kh_k\overline{h_{k-2n}}=\delta_{n0}$, equivalently
  $|m_0(\xi)|^2+|m_0(\xi+1/2)|^2=1$ almost everywhere.
  For the usual integrable normalized scaling function,
  $\widehat\phi(0)=1$ and $m_0(0)=1$.
* **16. Scaling functions from filters.** Let $m_0$ be a trigonometric
  polynomial with $m_0(0)=1$ satisfying the quadrature mirror identity,
  with $h_k=0$ outside $N_1\leq k\leq N_2$. Then
  $\widehat\phi(\xi)=\prod_{j\geq1}m_0(2^{-j}\xi)$ converges locally
  uniformly and defines $\phi\in L^2$ supported in $[N_1,N_2]$.
  If moreover $m_0$ has no zero on $[-1/6,1/6]$ (Cohen's condition;
  Lawton's eigenvalue condition is necessary and sufficient), the
  translates $\phi(\cdot-k)$ are orthonormal and $\phi$ generates an MRA.
  Without such a condition $\phi$ may fail this, as for
  $m_0(\xi)=(1+e^{-6\pi i\xi})/2$, $\phi=\frac13 1_{[0,3)}$.
* **17. Wavelet construction from an MRA.** Setting
  $g_k=(-1)^k\overline{h_{1-k}}$ and
  $\psi(t)=\sqrt2\sum_kg_k\phi(2t-k)$ gives an orthonormal
  basis $(\psi(\cdot-k))_k$ of $W_0$ and hence an orthonormal wavelet.
* **18. Characterization of orthonormal wavelets.** A function
  $\psi\in L^2(\mathbb R)$ with $\|\psi\|_2=1$ is an orthonormal wavelet
  exactly when, almost everywhere,
  $\sum_{j\in\mathbb Z}|\widehat\psi(2^j\xi)|^2=1$ and
  $\sum_{j\geq0}\widehat\psi(2^j\xi)\overline{\widehat\psi(2^j(\xi+q))}=0$
  for every odd integer $q$. It arises from an MRA exactly when
  $\sum_{j\geq1}\sum_{k\in\mathbb Z}|\widehat\psi(2^j(\xi+k))|^2=1$
  almost everywhere (Gripenberg–Wang); non-MRA wavelets exist.
* **19. Haar basis.** The functions
  $\phi=1_{[0,1)}$ and $\psi=1_{[0,1/2)}-1_{[1/2,1)}$
  generate an MRA and the Haar orthonormal basis of $L^2(\mathbb R)$.
  On $[0,1]$, add the constant function to the nonnegative-scale Haar
  functions.
* **20. Smooth wavelet existence.** There are orthonormal wavelets in
  $\mathcal S(\mathbb R)$ whose Fourier transforms are smooth and
  supported in an annulus. They have vanishing moments of every order.
* **21. Daubechies wavelets.** For every integer $N\geq1$ there is a
  real orthonormal wavelet with support of length $2N-1$ and $N$
  vanishing moments, from a filter $h_0,\ldots,h_{2N-1}$; $N=1$ gives
  Haar. Its Hölder regularity grows like $\mu N$ with
  $\mu=1-\log3/(2\log2)\approx0.21$. A compactly supported orthonormal
  wavelet cannot be $C^\infty$, and among real compactly supported
  orthonormal wavelets only the Haar wavelet is symmetric or
  antisymmetric about some point.
* **22. Vanishing moments and polynomial cancellation.** If
  $\int t^m\psi(t)dt=0$ for $0\leq m<N$, then every wavelet
  coefficient of a polynomial of degree below $N$ is zero wherever the
  pairing is defined. Equivalently $\widehat\psi$ vanishes to order
  at least $N$ at zero when the moments exist. Conversely, an orthonormal
  wavelet in $C^{N-1}$ with bounded derivatives and
  $|\psi(t)|\leq C(1+|t|)^{-N-\varepsilon}$ has $N$ vanishing moments.
* **23. Coefficient decay for smooth functions.** If $f\in C^N$ near
  the support of a compactly supported $N$-moment wavelet, then
  $|\langle f,\psi_{j,k}\rangle|
  \leq C2^{-j(N+1/2)}\sup_{\operatorname{supp}\psi_{j,k}}|f^{(N)}|$.
  For the orthogonal projection $P_j$ onto $V_j$ of such an MRA,
  $\|f-P_jf\|_2\leq C2^{-jN}\|f^{(N)}\|_2$ for $f\in H^N(\mathbb R)$.
* **24. Perfect reconstruction filter banks.** The low- and high-pass
  filters arising from an orthonormal MRA define a unitary map from
  fine-scale scaling coefficients to coarse scaling and detail
  coefficients. Its adjoint reconstructs the fine-scale coefficients,
  preserving the sum of squared coefficients.
* **25. Biorthogonal wavelets.** Dual multiresolutions with
  biorthogonal scaling and wavelet systems, and uniform Riesz bounds,
  yield dual Riesz bases. Each function is reconstructed by pairing
  with one system and synthesizing with the other; compact support and
  symmetry need not be tied to orthogonality.
* **26. Tensor products.** Tensoring a one-dimensional MRA gives an
  MRA on $\mathbb R^d$ with $2^d-1$ wavelet types per dyadic scale.
  The resulting translates and dilates form an orthonormal basis.
* **70. Unitary extension principle.** Let $\varphi\in L^2(\mathbb R)$
  satisfy $\widehat\varphi(2\xi)=\tau_0(\xi)\widehat\varphi(\xi)$, with
  $\widehat\varphi$ continuous at $0$ and $\widehat\varphi(0)=1$, and
  define $\widehat{\psi_j}(2\xi)=\tau_j(\xi)\widehat\varphi(\xi)$,
  $1\leq j\leq r$, for bounded $1$-periodic masks $\tau_j$. If
  $\sum_{j=0}^r|\tau_j(\xi)|^2=1$ and
  $\sum_{j=0}^r\tau_j(\xi)\overline{\tau_j(\xi+1/2)}=0$ almost
  everywhere, then $\{2^{k/2}\psi_j(2^k\cdot-n)\}_{j,k,n}$ is a Parseval
  frame (tight framelet) of $L^2(\mathbb R)$ (Ron–Shen). Unlike
  orthonormal wavelets, such framelets can be compactly supported,
  symmetric, and spline-based at once.

## Function spaces and approximation through wavelets

Use an inhomogeneous system consisting of scaling functions at scale zero
and wavelets for $j\geq0$. The following statements require smoothness,
decay, and vanishing moments sufficiently large for the indicated parameters.
Compactly supported wavelets with more than $|s|$ derivatives and moments
suffice in the Banach ranges below.

* **27. Unconditional $L^p$ bases.** A sufficiently regular orthonormal
  wavelet basis is unconditional in $L^p(\mathbb R)$ for $1<p<\infty$.
  Its square function
  $(\sum_{j,k}|c_{j,k}|^2 2^j1_{[2^{-j}k,2^{-j}(k+1))})^{1/2}$
  has norm equivalent to $\|f\|_p$, with the low-frequency part added.
* **28. Sobolev coefficient norms.** For real $s$ in the wavelet's
  regularity range,
  $\|f\|_{H^s}^2\asymp\sum_k|a_k|^2+
  \sum_{j\geq0,k}2^{2js}|c_{j,k}|^2$.
* **29. Besov characterization.** For $1\leq p,q\leq\infty$,
  $$
  \|f\|_{B^s_{p,q}}\asymp\|(a_k)\|_{\ell^p}
  +\left\|\left(2^{j(s+1/2-1/p)}
        \|(c_{j,k})_k\|_{\ell^p}\right)_{j\geq0}\right\|_{\ell^q}.
  $$
  This describes expansions in the distributional sense at endpoints.
* **30. Triebel–Lizorkin characterization.** For $1<p<\infty$,
  $1\leq q<\infty$, the $F^s_{p,q}$ norm is equivalent to the
  low-frequency norm plus
  $\|(\sum_{j,k}(2^{j(s+1/2)}|c_{j,k}|1_{I_{j,k}})^q)^{1/q}\|_p$,
  where $I_{j,k}=[2^{-j}k,2^{-j}(k+1))$.
* **31. Hardy-space square functions.** For sufficiently regular
  wavelets, the $L^1$ norm of the wavelet square function is equivalent
  to the real $H^1$ norm. Cancellation is built into the expansion.
* **32. BMO coefficient condition.** For a regular homogeneous wavelet
  basis, coefficients $c_I$ represent a BMO function, unique modulo
  constants, exactly when
  $\sup_J|J|^{-1}\sum_{I\subset J}|c_I|^2<\infty$ over dyadic
  intervals $J$. Its square root is an equivalent BMO seminorm.

## Continuous wavelets and short-time Fourier analysis

The **short-time Fourier transform** (STFT) with window $g$ is
$V_gf(x,\omega)=\langle f,M_\omega T_xg\rangle$.
For continuous wavelets write
$\psi_{a,b}(t)=|a|^{-1/2}\psi((t-b)/a)$ with $a\ne0$.

* **35. Continuous wavelet isometry.** If
  $0<C_\psi=\int_{\mathbb R}|\widehat\psi(\xi)|^2d\xi/|\xi|<\infty$,
  then
  $\int_{\mathbb R^*}\int_{\mathbb R}|\langle f,\psi_{a,b}\rangle|^2
  db\,da/a^2=C_\psi\|f\|_2^2$.
  Both signs of $a$ are included in this normalization.
* **36. Calderón reconstruction.** Under that admissibility condition,
  $f=C_\psi^{-1}\int\int\langle f,\psi_{a,b}\rangle\psi_{a,b}
  db\,da/a^2$, as a weak $L^2$ integral and as a limit of suitable
  truncated integrals.
* **37. Uncertainty principles.** For $f\in L^2(\mathbb R)$ and
  $a,b\in\mathbb R$,
  $\|f\|_2^2\leq4\pi\|(x-a)f\|_2\|(\xi-b)\widehat f\|_2$, with equality
  exactly for $f=cM_bT_ae^{-\pi\alpha x^2}$, $\alpha>0$ (Heisenberg).
  If $\{f\ne0\}$ and $\{\widehat f\ne0\}$ both have finite measure,
  then $f=0$ (Benedicks). If $|f(x)|\leq Ce^{-\pi\alpha x^2}$ and
  $|\widehat f(\xi)|\leq Ce^{-\pi\beta\xi^2}$, then $f=0$ when
  $\alpha\beta>1$ and $f=ce^{-\pi\alpha x^2}$ when $\alpha\beta=1$ (Hardy).
* **38. STFT orthogonality.** For $f,h,g,k\in L^2(\mathbb R^d)$,
  $\int V_gf\overline{V_kh}=\langle f,h\rangle\langle k,g\rangle$.
  In particular $\|V_gf\|_2=\|g\|_2\|f\|_2$.
* **39. STFT inversion.** If $\langle k,g\rangle\ne0$, then
  $f=\langle k,g\rangle^{-1}\int V_gf(x,\omega)M_\omega T_xk
  \,dx\,d\omega$ weakly in $L^2$.
* **40. Time–frequency covariance.** The identity
  $M_\omega T_x=e^{2\pi ix\cdot\omega}T_xM_\omega$ gives
  $|V_g(M_\eta T_yf)(x,\omega)|=|V_gf(x-y,\omega-\eta)|$.
  Time–frequency concentration is transported by phase-space translations.
* **41. Wigner marginals and Moyal identity.** For Schwartz functions,
  $$
  W(f,g)(x,\omega)=\int f(x+t/2)\overline{g(x-t/2)}e^{-2\pi it\cdot\omega}dt
  $$
  satisfies $\int W(f,f)d\omega=|f(x)|^2$,
  $\int W(f,f)dx=|\widehat f(\omega)|^2$, and
  $\langle W(f,g),W(h,k)\rangle=\langle f,h\rangle\langle k,g\rangle$.
* **42. Lieb's STFT inequality.** For $2\leq r\leq\infty$,
  $\|V_gf\|_r\leq(2/r)^{d/r}\|f\|_2\|g\|_2$, with the
  usual limiting constant at infinity. Gaussian functions attain the
  sharp finite-exponent constants.
* **71. Bargmann transform.** With
  $\mathcal Bf(z)=2^{d/4}\int f(t)e^{2\pi t\cdot z-\pi t^2-\pi z^2/2}dt$,
  $z\in\mathbb C^d$, $\mathcal B$ is unitary from $L^2(\mathbb R^d)$
  onto the Fock space $\mathcal F^2(\mathbb C^d)$ of entire $F$ with
  $\int|F(z)|^2e^{-\pi|z|^2}dz<\infty$. For the normalized Gaussian
  $\varphi(t)=2^{d/4}e^{-\pi t^2}$ and $z=x+i\omega$,
  $V_\varphi f(x,-\omega)=e^{\pi ix\cdot\omega}\mathcal Bf(z)
  e^{-\pi|z|^2/2}$. The Hermite functions are the preimages of the
  orthonormal basis $(\pi^{|\alpha|}/\alpha!)^{1/2}z^\alpha$ and are
  eigenfunctions of the Fourier transform with eigenvalues $(-i)^{|\alpha|}$.

## Gabor systems and modulation spaces

A rectangular **Gabor system** is
$\mathcal G(g,a,b)=\{M_{bn}T_{ak}g:k,n\in\mathbb Z^d\}$,
where $a,b>0$.

* **43. Gabor duality and commutation.** If $\mathcal G(g,a,b)$
  is a frame with operator $S$, its canonical dual is
  $\mathcal G(S^{-1}g,a,b)$. This follows because $S$ commutes
  with the lattice time–frequency shifts.
* **44. Painless expansions.** If $g\in L^\infty(\mathbb R^d)$ is
  supported in $[0,L]^d$, $a\leq L$ and $b\leq1/L$, then the frame
  operator of $\mathcal G(g,a,b)$ is multiplication by
  $b^{-d}\sum_{k\in\mathbb Z^d}|g(x-ak)|^2$. Hence it is a frame with
  bounds $b^{-d}A,b^{-d}B$ exactly when
  $A\leq\sum_k|g(x-ak)|^2\leq B$ almost everywhere.
* **45. Frames for dense lattices.** If $g$ belongs to the Wiener
  amalgam space $W(L^\infty,\ell^1)$ and
  $A\leq\sum_k|g(x-ak)|^2\leq B$ almost everywhere with $A>0$, then
  $\mathcal G(g,a,b)$ is a frame for all sufficiently small $b>0$
  (Walnut). In particular every nonzero $g\in S_0$ generates Gabor frames
  for all sufficiently small $a,b$.
* **46. Density obstruction.** A rectangular single-window Gabor
  frame requires $(ab)^d\leq1$; a Gabor Riesz sequence requires
  $(ab)^d\geq1$. A Gabor Riesz basis therefore has $ab=1$.
* **47. Gaussian frame set.** In dimension one, for a Gaussian window
  $g(t)=e^{-\pi t^2}$, $\mathcal G(g,a,b)$ is a frame exactly when
  $ab<1$ (Lyubarskii; Seip–Wallstén). At $ab=1$ it is complete but is not a frame.
* **72. Gaussian Gabor systems at arbitrary points.** For the Gaussian
  window and a separated set $\Lambda\subset\mathbb R^2$, identified with
  a subset of $\mathbb C$, $\{M_\omega T_xg\}_{(x,\omega)\in\Lambda}$
  is a frame of $L^2(\mathbb R)$ exactly when $D^-(\Lambda)>1$, and a
  Riesz sequence exactly when $D^+(\Lambda)<1$, with densities in points
  per unit area. This follows from the Bargmann transform and Fock-space
  sampling and interpolation (SYNOPSIS42, items 81–82; Lyubarskii,
  Seip–Wallstén). No Gaussian Gabor system is a Riesz basis.
* **48. Wexler–Raz relations.** Two Bessel Gabor systems with windows
  $g,\gamma$ are dual frames exactly when
  $\langle\gamma,M_{n/a}T_{k/b}g\rangle
  =(ab)^d\delta_{k0}\delta_{n0}$ for every $k,n\in\mathbb Z^d$.
* **49. Duality principle.** $\mathcal G(g,a,b)$ is a frame exactly
  when the adjoint-lattice system
  $\{M_{n/a}T_{k/b}g\}_{k,n}$ is a Riesz sequence.
  Its Riesz bounds are $(ab)^d$ times the frame bounds.
* **50. Zak-transform criterion.** With
  $Zf(x,\omega)=\sum_{k\in\mathbb Z}f(x-k)e^{2\pi ik\omega}$,
  $Z:L^2(\mathbb R)\to L^2([0,1)^2)$ is unitary.
  $\mathcal G(g,1,1)$ is a frame exactly when
  $0<A\leq|Zg|^2\leq B<\infty$ almost everywhere, and is
  orthonormal exactly when $|Zg|=1$ almost everywhere.
* **51. Balian–Low theorem.** If $\mathcal G(g,a,b)$ is a Riesz
  basis of $L^2(\mathbb R)$, then $tg(t)$ and
  $\xi\widehat g(\xi)$ cannot both belong to $L^2$.
* **52. Modulation-space window independence.** For a nonzero Schwartz
  window, $M^{p,q}$ consists of tempered distributions with
  $V_gf\in L^{p,q}(dx\,d\omega)$, taking the $L^p$ norm in $x$
  first. Different nonzero Schwartz windows give equivalent norms,
  for $1\leq p,q\leq\infty$; these spaces are Banach.
* **53. Basic modulation-space identities.** $M^{2,2}=L^2$ with
  equivalent norms. Fourier transformation preserves $M^{p,p}$ and
  all time–frequency shifts act isometrically for the fixed-window norm.
  The space $M^{1,1}$ is the Feichtinger algebra $S_0$ and embeds in
  $C_0\cap L^1$.
* **54. Gabor expansions of modulation spaces.** If $g\in S_0$ generates
  a lattice Gabor frame, its canonical dual belongs to $S_0$.
  Analysis identifies $M^{p,q}$ with its coefficient range in
  $\ell^{p,q}$, with equivalent norms and reconstruction by the dual
  window. Convergence is unconditional for finite $p,q$; endpoints
  use the corresponding weak topology.

## Time–frequency localization and Weyl operators

For a symbol $a$ on $\mathbb R^{2d}$ and windows
$\varphi_1,\varphi_2\in L^2(\mathbb R^d)$, the **localization operator**
$A_a^{\varphi_1,\varphi_2}$ is defined weakly by
$\langle A_a^{\varphi_1,\varphi_2}f,h\rangle
=\int a\,V_{\varphi_1}f\,\overline{V_{\varphi_2}h}\,dx\,d\omega$.
The **Weyl operator** $L_\sigma$ with symbol $\sigma\in\mathcal S'(\mathbb R^{2d})$
is defined by $\langle L_\sigma f,h\rangle=\langle\sigma,W(h,f)\rangle$.

* **73. Localization operators.** If $a\in L^p(\mathbb R^{2d})$,
  $1\leq p\leq\infty$, then $A_a^{\varphi_1,\varphi_2}$ belongs to the
  Schatten class $\mathcal S_p$, with norm at most
  $\|a\|_p\|\varphi_1\|_2\|\varphi_2\|_2$ ($p=\infty$: bounded
  operators). For $a\in L^1$ its trace is
  $\langle\varphi_2,\varphi_1\rangle\int a$. If $a\geq0$ and
  $\varphi_1=\varphi_2$, the operator is positive. Its Weyl symbol is
  $a*W(\varphi_2,\varphi_1)$; for Gaussian windows these are the
  anti-Wick operators.
* **74. Radial symbols with Gaussian windows.** In dimension one, with
  the normalized Gaussian window and $a(z)=a_0(|z|)$ radial and bounded,
  $A_a$ is diagonal in the Hermite basis with eigenvalues
  $\lambda_k=\int_0^\infty a_0(\sqrt{s/\pi})e^{-s}s^k/k!\,ds$
  (Daubechies). For $a$ the indicator of a disc of area $R$, the
  eigenvalues are $1-e^{-R}\sum_{j\leq k}R^j/j!$, so about $R$ of them
  are near one: the phase-space analogue of 76–77.
* **75. Sjöstrand class.** If $\sigma\in M^{\infty,1}(\mathbb R^{2d})$,
  then $L_\sigma$ is bounded on every $M^{p,q}(\mathbb R^d)$,
  $1\leq p,q\leq\infty$, in particular on $L^2$, with operator norm
  at most a constant times $\|\sigma\|_{M^{\infty,1}}$ (Sjöstrand;
  Gröchenig–Heil). Bounded derivatives of order at most $2d+1$ place
  $\sigma$ in $M^{\infty,1}$, giving a Calderón–Vaillancourt theorem;
  unlike smooth symbol classes, $M^{\infty,1}$ is invariant under
  time–frequency shifts and requires no smoothness.

## Bandlimited and nonuniform sampling

Let $PW_B=\{f\in L^2(\mathbb R):\operatorname{supp}\widehat f
\subset[-B,B]\}$, $B>0$, with its continuous entire representative.
Sampling is **stable** on a set $\Lambda$ if
$A\|f\|_2^2\leq\sum_{\lambda\in\Lambda}|f(\lambda)|^2\leq B_0\|f\|_2^2$.

* **56. Reproducing kernels.** Point evaluation on $PW_B$ is bounded,
  with kernel $K_x(t)=2B\operatorname{sinc}(2B(t-x))$,
  $\operatorname{sinc}u=\sin(\pi u)/(\pi u)$. In particular
  $|f(x)|\leq\sqrt{2B}\|f\|_2$.
* **57. Bernstein and Plancherel–Pólya inequalities.** For $f\in PW_B$,
  $f'\in PW_B$ and $\|f'\|_2\leq2\pi B\|f\|_2$; the same holds in
  $L^p$, $1\leq p\leq\infty$, for entire functions of exponential type
  at most $2\pi B$ in $L^p(\mathbb R)$. If
  $\inf_{\lambda\ne\mu\in\Lambda}|\lambda-\mu|=\delta>0$, then
  $\sum_{\lambda\in\Lambda}|f(\lambda)|^2\leq C(\delta,B)\|f\|_2^2$
  on $PW_B$, so for separated sets only the lower sampling bound is at issue.
* **58. Shannon sampling theorem.** For $f\in PW_B$,
  $$
  f(t)=\sum_{k\in\mathbb Z}f(k/(2B))\operatorname{sinc}(2Bt-k),
  \qquad \|f\|_2^2=(2B)^{-1}\sum_k|f(k/(2B))|^2.
  $$
  The series converges in $L^2$ and uniformly on the real axis.
  For $B=1/2$ the series
  $f(z)=\sum_nf(n)\sin\pi(z-n)/(\pi(z-n))$ also converges locally
  uniformly in $\mathbb C$.
* **59. Sampling as a frame problem.** Stable sampling on $\Lambda$
  is equivalent to the kernels $(K_\lambda)$ forming a frame in
  $PW_B$, and to the corresponding exponentials forming a frame in
  $L^2([-B,B])$. Dual frames give stable reconstruction formulas.
* **60. Interpolation and Riesz sequences.** Every $\ell^2(\Lambda)$
  data sequence has a $PW_B$ interpolant with bounded solution norm
  exactly when $(K_\lambda)$ is a Riesz sequence. Complete stable
  interpolation corresponds to a Riesz basis.
* **61. Kadec's one-quarter theorem.** If
  $\sup_{k\in\mathbb Z}|2B\lambda_k-k|<1/4$ (equivalently $\leq L$ for
  some $L<1/4$), the sampling kernels
  at $\lambda_k$ form a Riesz basis of $PW_B$. The universal
  constant $1/4$ cannot be enlarged.
* **62. Landau's necessary densities.** For a uniformly separated set,
  stable sampling for $PW_B$ requires $D^-(\Lambda)\geq2B$;
  stable interpolation requires $D^+(\Lambda)\leq2B$, where
  $D^-=\liminf_{R\to\infty}\inf_x\#(\Lambda\cap[x,x+R])/R$
  and $D^+$ uses $\limsup$ and $\sup$.
* **63. Strict-density sufficiency in one dimension.** For uniformly
  separated $\Lambda\subset\mathbb R$, $D^-(\Lambda)>2B$ implies
  stable sampling for $PW_B$, and $D^+(\Lambda)<2B$ implies
  stable interpolation (Beurling). Density alone does not settle the equality case.
  These strict and non-strict thresholds are compared in
  [Olevskii–Ulanovskii, *On the duality between sampling and interpolation*, Theorem 2](https://arxiv.org/pdf/1512.01437).
* **64. Aliasing threshold.** Uniform samples with spacing $h>1/(2B)$
  do not determine all of $PW_B$: overlapping frequency translates
  produce nonzero functions with every sample zero. Oversampling with
  strict bandwidth margin permits smooth reconstruction kernels with
  faster decay than sinc.
* **76. Time–band limiting and prolate spheroidal functions.** For
  $T>0$ the concentration operator
  $Qf=P_B(1_{[-T,T]}f)$ on $PW_B$, with $P_B$ the orthogonal projection
  onto $PW_B$, is positive and trace class with trace $4TB$. Its
  eigenvalues $1>\lambda_0>\lambda_1>\cdots>0$ are simple, and
  $\lambda_0=\max\{\int_{-T}^T|f|^2/\|f\|_2^2:0\ne f\in PW_B\}$
  (Landau–Pollak–Slepian). The eigenfunctions are the prolate spheroidal
  wave functions: they are also eigenfunctions of a commuting
  second-order differential operator (Slepian–Pollak), form an
  orthonormal basis of $PW_B$, and their restrictions are orthogonal and complete in $L^2([-T,T])$.
* **77. Eigenvalue plunge.** For each fixed $0<\gamma<1$, as
  $TB\to\infty$,
  $\#\{k:\lambda_k>\gamma\}=4TB+\pi^{-2}\log((1-\gamma)/\gamma)
  \log(TB)+o(\log(TB))$ (Landau–Widom). Thus about $4TB$ eigenvalues are
  close to one and only $O(\log(TB))$ lie in $(\gamma,1-\gamma)$: the
  time–frequency rectangle of area $4TB$ has that many degrees of freedom.

## Sparse recovery and redundant dictionaries

For $A\in\mathbb C^{m\times N}$, a vector is **$s$-sparse** if it has
at most $s$ nonzero coordinates. Write
$\sigma_s(x)_1=\inf_{\#\operatorname{supp}z\leq s}\|x-z\|_1$.
The **restricted isometry constant** $\delta_s$ is the least $\delta$
with $(1-\delta)\|x\|_2^2\leq\|Ax\|_2^2\leq(1+\delta)\|x\|_2^2$
for every $s$-sparse $x$.

* **65. Sparse uniqueness.** Every $s$-sparse vector is determined
  uniquely among $s$-sparse vectors by $Ax$ exactly when $\ker A$
  contains no nonzero $2s$-sparse vector.
* **66. Null-space characterization of basis pursuit.** Every
  $s$-sparse $x$ uniquely minimizes $\|z\|_1$ subject to $Az=Ax$
  exactly when $\|h_S\|_1<\|h_{S^c}\|_1$ for every nonzero
  $h\in\ker A$ and every $|S|\leq s$.
* **67. Coherence criterion.** If the columns have norm one and
  $\mu=\max_{j\ne k}|\langle A_j,A_k\rangle|$, then
  $s<(1+\mu^{-1})/2$ guarantees exact basis-pursuit recovery of
  every $s$-sparse vector.
* **68. Stable recovery from restricted isometry.** The condition
  $\delta_{2s}<4/\sqrt{41}\approx0.62$ guarantees that every minimizer
  $\widehat x$ of $\|z\|_1$ subject to $\|Az-y\|_2\leq\eta$,
  with $\|Ax-y\|_2\leq\eta$, obeys
  $\|x-\widehat x\|_2\leq C\sigma_s(x)_1/\sqrt s+D\eta$.
  Constants depend only on the restricted isometry bound.

## Reference guide

Christensen, Heil, and Young supply the common frame, basis, and nonharmonic
Fourier-series foundations. Meyer, Daubechies, Hernández–Weiss, and
Wojtaszczyk overlap on multiresolution, filters, cancellation, and function
spaces; Mallat and Cohen connect these to approximation. Gröchenig,
Christensen, and the Gabor references supply the time–frequency and density
theory; Gröchenig, M. W. Wong, and Cordero–Rodino treat localization and
Weyl operators, and Seip the Bargmann–Fock route to Gaussian Gabor frames.
Han covers framelets and the unitary extension principle, and
Osipov–Rokhlin–Xiao the prolate spheroidal functions.
Young, Seip, Christensen, and Eldar provide the sampling viewpoint.
The final sparse-recovery statements are the core shared by Foucart–Rauhut
and Adcock–Hansen, rather than a general inventory of numerical algorithms.
Directional systems, multivariate mask design, and sampling of specific
structured nonlinear models are further specializations.

Local source copies consulted:

* [Christensen, *An Introduction to Frames and Riesz Bases*](References/Christensen2016IntroductionFramesRieszBases2ndEd-BirkhaeuserANHA.pdf).
* [Gröchenig, *Foundations of Time-Frequency Analysis*](References/Gröchenig2001FoundationsTimeFrequencyAnalysis-SpringerANHA.pdf).
* [Meyer, *Wavelets and Operators*](References/Meyer1993WaveletsOperators-CambridgeStudiesAM37.pdf).
* [Wojtaszczyk, *A Mathematical Introduction to Wavelets*](References/Wojtaszczyk1997MathematicalIntroductionWavelets-CambridgeLMSST37.pdf).
* [Foucart–Rauhut, *A Mathematical Introduction to Compressive Sensing*](References/FoucartRauhut2013MathematicalIntroductionCompressiveSensing-BirkhäuserANHA.pdf).
