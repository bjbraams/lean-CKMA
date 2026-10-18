# Revision record for the synopses SYNOPSIS04–SYNOPSIS53

This file records the critical revision of the fifty synopses carried out on 2026-10-18.
The synopses themselves contain no remarks about their development; this record
replaces such remarks.

## Scope and method

Each synopsis was read in full against its section of [CKMA-bib.md](CKMA-bib.md) and
[CKMA-bib2.md](CKMA-bib2.md). Selected statements were checked against local copies in
`References/` and `ReferencesSuppl/`. Corrections include missing or superfluous
hypotheses, wrong constants or normalizations, false-as-stated claims and
misattributions. Core results that recur across the main texts were added, and
padding, redundant entries and methodological remarks were removed or merged.
Each file grew by 0–22%, within the 0–50% limit. The number of numbered entries
rose from 3,368 to 3,493.

Entries were renumbered consecutively within each file. A numbering map for each
section is given below. The citations `xx.N` in [GAPS.md](GAPS.md), both entry
headings and references in the prose, were updated from these maps. Each updated
heading was checked against the title of the renumbered synopsis entry. Seven
entries whose title changed but whose content did not are 14.3, 19.51, 22.61,
29.21, 30.31, 36.12 and 49.45. No GAPS.md entry pointed to a removed synopsis entry.
Entry counts in [SYNOPSIS.md](SYNOPSIS.md) were updated.

## Statements recommended for spot-checking

The following statements were added or reformulated from standard knowledge, without
confirmation in a local source. Numbers refer to the revised files.

* 05: Aleksandrov (38), De Giorgi structure (48) and Federer–Vol'pert (in 49) rest on
  an incomplete local Evans–Gariepy. The claim in 35 that the Fréchet exceptional set
  "need not be Haar-null" is hedged.
* 08: the additions on one-dimensional diffusions, Yamada–Watanabe, Lévy's
  $(S-B,S)$ theorem and Stroock–Varadhan. Karatzas–Shreve and Revuz–Yor are not local.
* 09.40, the $C_0$-semigroup version of mild solutions with $L^p$ data for $p>2$.
  12.48, Moreau-envelope convergence "for every $\gamma>0$" in Attouch's theorem.
  12.63, Douglas–Rachford convergence.
* 14.11, whether $1/4$ is the optimal boundary Hardy constant for every convex domain.
  16.55, the constant in the Fourier transform of $|x|^{-a}$. 18.19, the exact form of
  Burkholder's $\zeta$-convexity.
* 19, the KB and Lozanovsky criteria and the Beurling–Deny criteria. 19.35 and 23.54.
  22, the HVZ and short-range scattering entries. 21.52 calls the invariant subspace
  problem on separable Hilbert space open; Enflo's 2023 preprint is not treated as settling it.
* 24, Prüss's resolvent-family existence result and $s(A)=\omega_0$ for positive
  semigroups on $C_0(\Omega)$. 25, Verchota's $L^2$ invertibility. 27, Lerner's sparse
  domination.
* 29.69, a reference link kept inside the entry text. 30.43, the sign convention of
  condition $(\Psi)$. 32, the Tychonoff and Petrowsky statements.
* 34.34, attributions for the Morawetz estimates. 34.76, the hypotheses of
  Golse–Saint-Raymond. 38.36, the "σ-finite length" clause attributed to Makarov.
  37.67–68 and 38.66–67 overlap on analytic capacity.
* 39.16, Heinonen–Koskela, in a cautious qualitative form. 43.47, the constants in the
  Ahlfors distortion theorem.
* 44, Royden's theorem and the Bers-embedding radii 2 and 6. 47.20, the Favard
  constants. 48, the Killip–Simon conditions and the Golinskii–Ibragimov attribution.
* 51.33–34, the conventions of the defocusing NLS Riemann–Hilbert problem and the
  Deift–Zhou asymptotic formula.

## Per-section records

### Section 04: Real analysis, measure, and integration

Size: 24162 → 25826 bytes; entries: 64 → 64.

Sources consulted: Folland, *Real Analysis* (local PDF; Theorem 7.2 Riesz representation and regularity results 7.8, 7.12; Chapter 3 maximal function and differentiation); CKMA-bib.md and CKMA-bib2.md Section 4; existing local anchors Cohn and Stein–Shakarchi.

Changes:
- 5: added the existence of non-Lebesgue-measurable sets (Vitali), and the fact that the completed product of $\mathcal L^n$ and $\mathcal L^k$ is $\mathcal L^{n+k}$.
- 14 (Jensen): replaced the vague "whenever the latter integral is defined" with the observation that the right side is always defined, possibly $+\infty$, because $\Phi$ has an affine minorant. Stated the conditional form explicitly.
- Modes-of-convergence intro: removed a vague sentence about infinite measure spaces. Its content now appears precisely in 21.
- 21 (Vitali): added the $L^p$ version on arbitrary measure spaces, with uniform integrability of $|f_n|^p$ plus tightness.
- 22: extended Scheffé's lemma by the Brezis–Lieb lemma and the Riesz criterion: a.e. convergence plus convergence of norms gives $L^p$ convergence for $0<p<\infty$.
- 34: removed the meaningless phrase "with compatible versions on zero-density sets". Added the change-of-measure integral formula, and stated $|h\mu|=|h|\mu$ precisely.
- 36: stated $1\le p<\infty$ for Minkowski's integral inequality.
- 39: noted that $\sigma$-finiteness is needed only for $p=1$, and that $(L^\infty)^*$ is in general strictly larger than $L^1$.
- 40: added the Eberlein–Šmulian remark (weak compactness equals weak sequential compactness).
- 44: added the Hardy–Littlewood maximal inequality as the key estimate, with a cross-reference to Section 05.
- 46: replaced the imprecise remark about singular parts with Lebesgue's monotone differentiation theorem ($F'\in L^1$, $\int F'\le F(b)-F(a)$). Equality on all subintervals holds exactly for absolutely continuous $F$; the Cantor function is the counterexample.
- 50 (Riesz representation): correction. The old version needlessly restricted to second-countable spaces and was vague about regularity. It is now the general LCH statement: a unique measure that is outer regular on Borel sets and inner regular on open sets. Inner regularity on all Borel sets holds for $\sigma$-compact $X$, and uniqueness among all locally finite Borel measures holds when every open set is $\sigma$-compact (Folland 7.2, 7.8, 7.12).
- 63: corrected an inconsistency. The entry said "for $s>0$" and then discussed $s=0$; it now says $s\ge0$.

Numbering map (old → new):
unchanged

### Section 05: Differentiation and the fine structure of real functions

Size: 23513 → 26264 bytes; entries: 58 → 61.

Sources consulted: Evans–Gariepy (local incomplete PDF; table of contents for Sections 5.7 and 6.4: reduced boundary, structure theorem, Aleksandrov's theorem); CKMA-bib.md and CKMA-bib2.md Section 5 (including Lindenstrauss–Preiss–Tišer and Pfeffer); existing anchors Bruckner, De Guzmán, and Federer.

Changes:
- 9 (Dini criterion): strengthened to the standard form. It now needs only $D^+f\ge0$ off a countable set (the old version needed $D_+f\ge0$ everywhere). Added the Cantor-function counterexample for a.e. hypotheses.
- 12 (Jordan): corrected the awkward and partly inaccurate wording "all of jump type for the appropriate one-sided representative". The discontinuities are jumps or removable. Added that continuous BV functions have continuous variation function.
- 13: added Fubini's termwise differentiation theorem for series of monotone functions.
- New 35: Lipschitz maps on Banach spaces, i.e. the infinite-dimensional Rademacher theorem (Aronszajn/Christensen/Mankiewicz), Gâteaux differentiability off Aronszajn-null sets, and Preiss's Fréchet theorem. This is core given the bibliography's Lindenstrauss–Preiss–Tišer entry.
- New 38: convex functions are locally Lipschitz, plus Aleksandrov's a.e. second-order differentiability (Evans–Gariepy 6.4). This entry overlaps SYNOPSIS12.15 but belongs to the fine-properties core.
- Lipschitz-section intro: shortened a padded explanation of approximate differentiability.
- New 48: De Giorgi's structure theorem for sets of finite perimeter, with the reduced boundary, rectifiability, $|D1_E|=\mathcal H^{n-1}\llcorner\partial^*E$, the generalized Gauss–Green formula, and Federer's comparison with the measure-theoretic boundary.
- 49 (old 46): added the Federer–Vol'pert decomposition $Du=\nabla u\,\mathcal L^n+$ jump part $+$ Cantor part, with properties of each part.
- 53 (old 50): extended to derivatives existing off a countable set. Added the consequence that everywhere differentiability with $F'\in L^1$ implies absolute continuity, and the example $x^2\sin(x^{-2})$.
- 56 (old 53, Whitney extension): removed a redundant trailing sentence.
- 58 (old 55): replaced the restricted, vaguely qualified indicatrix statement with Banach's indicatrix theorem $\operatorname{Var}F=\int N_F(y)\,dy$, valid for every continuous $F$.
- Reference guide: added pointers for the structure theorem, Aleksandrov, Federer–Vol'pert (Ambrosio–Fusco–Pallara), and Lindenstrauss–Preiss–Tišer.

Numbering map (old → new):
35→36, 36→37, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→49, 47→50, 48→51, 49→52, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61 (new entries: 35, 38, 48)

### Section 06: Probability: measure-theoretic foundations and limit theory

Size: 26287 → 26480 bytes; entries: 66 → 66.

Sources consulted: Durrett (Theorem 4.2.10 upcrossing form; pairwise-independence Borel–Cantelli and Etemadi SLLN); Billingsley, *Probability and Measure*, Theorem 30.2 (method of moments; local PDF checked); Klenke and Kallenberg (existing anchors); CKMA-bib.md and CKMA-bib2.md Section 6.

Changes:
- Reorganization: dissolved the miscellaneous final section "Approximation principles and extensions of the limit theorems" and moved each entry to its thematic home:
  - converging together → convergence section, as 20;
  - Le Cam → after the Poisson limit, as 39;
  - Gaussian integration by parts/Stein → Gaussian section, as 50;
  - de Finetti → random-measure section, as 55;
  - contraction principle and Gärtner–Ellis → large-deviation section, as 63–64.
  The total-variation definition moved to the convergence-section intro and was corrected ("on the real line" → on any measurable space).
- Merged the redundant old 51 (de Finetti for Bernoulli sequences) into the general de Finetti theorem (old 64 → 55) as its special case.
- New 32: method of moments, i.e. moment determinacy plus moment convergence gives weak convergence (Billingsley Theorem 30.2). This is core and was missing.
- 4: second Borel–Cantelli under pairwise independence, with the a.s. ratio limit.
- 12: added that convergence in distribution to a constant implies convergence in probability.
- 22 (old 21): added Lévy's equivalence theorem for series of independent summands.
- 25 (old 24): added Etemadi's pairwise version of the SLLN and the converse for $\mathbb E|X_1|=\infty$.
- 41 (old 38, upcrossing): replaced the non-standard, admittedly non-sharp bound and its apologetic sentence with Durrett's form $(b-a)\mathbb EU_N\le\mathbb E(X_N-a)^+-\mathbb E(X_0-a)^+$.
- 47 (old 44): added Wald's identity.
- 53 (old 49): added the existence of Poisson random measures for $\sigma$-finite intensity.
- 60 (old 56, Cramér): noted that on $\mathbb R$ the principle holds without moment assumptions, though the rate need not be good.
- 66 (old 60, Kesten–Stigum): stated the dichotomy fully (otherwise the limit is 0 a.s.).
- Removed padding:
  - intro sentence on "distinctions matter";
  - the long LD-intro paragraph comparing LDP, CLT, and Berry–Esseen, plus the remark on densities;
  - trailing sentences in Donsker, Le Cam, Stein, and the contraction principle.
- 35 (Lyapunov): internal cross-reference updated to the Lindeberg–Feller entry, now 34.
- Reference guide: updated to the new organization; added Billingsley, *Probability and Measure* as a consulted local text.

Numbering map (old → new):
20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→30, 30→31, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→47, 45→48, 46→49, 47→51, 48→52, 49→53, 50→54, 51→55 (merged), 52→56, 53→57, 54→58, 55→59, 56→60, 57→61, 58→62, 59→65, 60→66, 61→20, 62→39, 63→50, 64→55, 65→63, 66→64 (new entry: 32)

### Section 07: Concentration, high-dimensional probability, and empirical processes

Size: 24999 → 25263 bytes; entries: 60 → 62.

Sources consulted: Bai–Silverstein (local PDF; Theorems 2.5, 3.6, 5.1, 5.8, 5.10–5.11 for the exact hypotheses of the semicircle, Marchenko–Pastur, and edge laws); Ledoux, *The Concentration of Measure Phenomenon* (local PDF; Corollary 3.2, Poincaré implies exponential concentration); Vershynin, Van Handel, and Giné–Nickl (existing anchors); CKMA-bib.md and CKMA-bib2.md Section 7.

Changes:
- New 11: Khintchine–Kahane inequalities. This is core and recurs in Vershynin, Ledoux–Talagrand, and Banach-space probability.
- New 18: Bakry–Émery criterion ($\nabla^2V\ge\kappa I$ gives LSI with constant $1/\kappa$) and the Holley–Stroock perturbation. These are the standard sources of LSI beyond the Gaussian case.
- 19 (old 17, Herbst): added the Poincaré case, which gives only exponential concentration (Gromov–Milman, Ledoux Corollary 3.2).
- 23 (old 21, Talagrand $T_2$): added Marton's transport-to-concentration argument, tensorization, and Otto–Villani (LSI implies $T_2$).
- 50–51 (old 48–49, semicircle and Marchenko–Pastur): correction. Finite fourth moment is not needed; finite variance suffices (Bai–Silverstein 2.5, 3.6). The hypotheses are restated accordingly, with the diagonal Wigner entries only i.i.d.
- 52 (old 50, edges): finite fourth moment is now an explicit extra hypothesis, with its sharpness noted (Bai–Silverstein 5.1, 5.8).
- Reference guide sentence on "convenient sufficient assumptions" replaced by precise theorem citations.
- Removed padding:
  - the long sub-Gaussian intro paragraph (condensed);
  - trailing sentences in Paley–Zygmund, the majorizing measure theorem, the Gaussian-width paragraph, Freedman, convex distance, Slepian, and Anderson.
- 57 (old 55): now notes that convex Lipschitz concentration (24) follows from it.
- 60 (old 58): the trailing sentence is replaced by the actual derivation from Paley–Zygmund.

Numbering map (old → new):
11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62 (new entries: 11, 18)

### Section 08: Stochastic processes, martingales, and stochastic calculus

Size: 27802 → 28689 bytes; entries: 61 → 62.

Sources consulted: Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Baldi, Mörters–Peres, and Rogers–Williams II (existing anchors); standard statements as in Karatzas–Shreve, Chapter 5, and Revuz–Yor, Chapters VI, VII, and IX (not available locally); CKMA-bib.md and CKMA-bib2.md Section 8.

Changes:
- 2: added time inversion and Lévy's conformal invariance of planar Brownian motion.
- 3: added Blumenthal's zero–one law.
- 6: added Lévy's modulus of continuity.
- 23 (BDG): added the càdlàg version ($p\ge1$, with $[M]$) and clarified the stopping-time wording.
- 29 (Girsanov): replaced the vague "acquire the covariation drift prescribed by the logarithmic stochastic integral" with the precise general statement: $M-\langle M,L\rangle$ is a $\mathbb Q$-local martingale.
- 33 (Yamada–Watanabe): replaced a padding sentence with the one-dimensional Yamada–Watanabe pathwise-uniqueness criterion (Hölder-1/2 diffusion coefficients).
- 36 (Feynman–Kac): correction. $g$ must be bounded for $u$ to be the bounded classical solution; the old version had only bounded derivatives.
- New 38: one-dimensional diffusions, covering the scale function, exit probabilities, the recurrence criterion, and Feller's test with the speed measure. This is core and recurs in Karatzas–Shreve, Revuz–Yor, and Rogers–Williams.
- Local-time intro: replaced an obscure sentence ("right-local-time version… spatial versions coincide") with the precise regularity statement.
- 44 (old 43): added Lévy's theorem $(S-B,S)\overset d=(|B|,L^0)$.
- 47 (old 46): added the Stroock–Varadhan well-posedness theorem.
- 57 (old 56): shortened the trailing sentence on Euler interpolation.
- 60 (old 59): made the convergence claim for the Doléans product precise (absolute convergence).
- Removed padding:
  - trailing sentences in the u.c.p. paragraph and the bracket paragraph;
  - Lévy generators 56 (old 55), $h$-transform 59 (old 58), and gradient diffusions 62 (old 61);
  - the closing Ornstein–Uhlenbeck remark.
- Reference guide: added the pointer for one-dimensional diffusions.

Numbering map (old → new):
38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→53, 53→54, 54→55, 55→56, 56→57, 57→58, 58→59, 59→60, 60→61, 61→62 (new entry: 38)

### Section 09: Malliavin Calculus, Rough Paths, and Stochastic PDE

Size: 25404 → 28450 bytes; entries: 57 → 60.

Sources consulted: Nualart, *The Malliavin Calculus and Related Topics* (References/, Section 2.3, condition (H) and Theorems 2.3.2–2.3.3); Friz–Hairer, *A Course on Rough Paths* (References/, table of contents, Chapters 3 and 13–15); CKMA-bib.md and CKMA-bib2.md Section 9 entries (Da Prato–Zabczyk, *Ergodicity*; Hairer, *A Theory of Regularity Structures*; Nourdin–Peccati).

Changes:
- Entry 2 (multiple-integral isometry): replaced a vague closing sentence by the precise isometry $I_q/\sqrt{q!}$ onto the $q$th chaos and the identification with iterated Itô integrals on Wiener space.
- Entry 4: closability of $D$ holds for $1\leq p<\infty$, not only $p>1$.
- Entry 6: added Stroock's formula $f_q=\mathbb E[D^qF]/q!$.
- New entry 10 (Cameron–Martin theorem): quasi-invariance of Wiener measure under Cameron–Martin shifts and singularity otherwise; foundational in every Gaussian-analysis text in the section and missing.
- Entry 14 (Clark–Ocone, old 13): removed a padding sentence.
- Entry 18 (Hörmander, old 17): correction. Hörmander's condition is needed only at the starting point $x_0$ (Nualart Thm 2.3.3), not at every point; the coefficients need bounded derivatives of all orders, not to be $C_b^\infty$. Equation and bracket condition now written explicitly.
- Entry 24 (Lyons extension, old 23): correction/precision. The extension theorem holds for multiplicative functionals of finite $p$-variation (geometricity not needed); stated the factorial decay $\omega^{n/p}/(n/p)!$; added Hambly–Lyons uniqueness of the signature up to tree-like equivalence.
- Entry 31 (Brownian lifts, old 30): added the Kolmogorov criterion as the construction and the key consistency fact that RDEs driven by the Itô/Stratonovich lifts reproduce Itô/Stratonovich SDE solutions a.s.
- Entry 36 (trace-class Wiener processes, old 35): fixed the space (the $Q$-Wiener process is $U$-valued, not $H$-valued), stated eigenpairs, added that a cylindrical Wiener process lives in any larger space with Hilbert–Schmidt embedding.
- Entry 40 (Lipschitz mild equations, old 39): noted the general $C_0$-semigroup version with $L^p$ data, $p>2$, via factorization (contraction is only needed for the $p=2$ path-continuity statement).
- New entry 47 (Doob–Khasminskii uniqueness): strong Feller plus irreducibility gives uniqueness of invariant measures; the standard companion to Krylov–Bogoliubov existence (Da Prato–Zabczyk, *Ergodicity*).
- Entry 53 (comparison, old 51): the positivity sentence was circular; replaced by Mueller's theorem (with $\sigma(0)=0$, nonnegative nonzero data give strictly positive solutions).
- Entry 59 (KPZ, old 57): added that the regularity-structure solution of KPZ coincides with the Cole–Hopf solution (Friz–Hairer Ch. 15).
- New entry 60 (subcritical well-posedness): Hairer's general convergence theorem for renormalized locally subcritical equations, with $\Phi^4_3$ as example; the central theorem of the singular-SPDE part was missing.
- Internal cross-reference "result 39" in the Hilbert-space introduction updated to "result 40".
- Reference guide: mentioned Da Prato–Zabczyk, *Ergodicity*, and Hairer, *A Theory of Regularity Structures*, for the new entries.

Numbering map (old → new):
10→11, 11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→20, 20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→30, 30→31, 31→32, 32→33, 33→34, 34→35, 35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→46, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59 (new entries: 10, 47, 60)

### Section 10: Ergodic Theory and Measurable Dynamics

Size: 23766 → 25306 bytes; entries: 63 → 64.

Sources consulted: Viana–Oliveira, *Foundations of Ergodic Theory* (References/; generator theorems incl. the Krieger statement in Section 9.2, ergodicity of toral automorphisms); CKMA-bib.md and CKMA-bib2.md Section 10 entries (Walters, Glasner, Morris, Downarowicz, Eisner–Farkas–Haase–Nagel).

Changes:
- Introduction: removed a padding sentence about periodic orbits and mixing models; tightened the remaining remark.
- Entry 10 (natural extension): replaced the imprecise "past coordinates generate" description by the minimality/generation characterization; added preservation of mixing properties.
- Entry 12: removed a redundant trailing sentence.
- Entry 17: merged old 56 (spectral splitting) into the Kronecker-factor entry, which duplicated it; dropped the vague phrase on "two-term nonconventional averages" (covered by entry 52).
- Entry 20: noted the one-sided generator version for noninvertible maps.
- New entry 21 (Krieger generator theorem): a standard entropy result in Viana–Oliveira, Downarowicz, Walters; finite generators link measurable systems to symbolic ones.
- Entry 28 (old 27): extended Pinsker factor to K-systems (trivial Pinsker factor, mixing of all orders, countable Lebesgue spectrum, K not implying Bernoulli).
- Entry 29 (old 28): grammar fix ("its extreme points" referred to the wrong noun); named Krylov–Bogoliubov.
- Entry 31 (old 30): added Weyl's polynomial equidistribution via unique ergodicity of toral skew products.
- New entry 32 (toral automorphisms): ergodicity criterion (no eigenvalue a root of unity), mixing/Bernoulli, entropy $\sum_{|\lambda|>1}\log|\lambda|$; the basic algebraic example class in all the main texts.
- New entry 33 (Ratner's theorems): measure classification, orbit closures, and equidistribution for unipotent flows (Morris is in the bibliography; Einsiedler–Ward, Witte Morris); a central theorem of modern measurable dynamics absent before.
- Entry 38 (old 35) and entry 54 (old 52): removed padding trailing sentences.
- Entry 41 (Oseledets, old 38): added two-sided convergence, the determinant identity $\sum m_i\lambda_i=\int\log|\det A|$, and the filtration version for noninvertible bases.
- Entry 43 (Pesin, old 40): replaced a vague closing sentence by the Ledrappier–Young characterization (equality iff SRB).
- Entry 44 (old 41): misattribution corrected. Ergodicity of geodesic flows in variable negative curvature in all dimensions is due to Anosov; Hopf proved surfaces and constant curvature. Entry renamed "Ergodicity of geodesic flows"; added mixing/Bernoulli and the unit tangent bundle.
- Entry 45: merged old 43 (ergodic decomposition of joinings) into old 42.
- Entry 47 (old 45): replaced a padding sentence by the characterization of weak mixing as disjointness from all ergodic rotations.
- Entry 61 (old 60): replaced a padding sentence by Jacobs' attribution and upper semicontinuity of entropy for expansive maps (existence of equilibrium states).
- Internal cross-references "result 39" and "result 49" updated to 42 and 51.
- Reference guide: Morris named for Ratner's theorems.

Numbering map (old → new):
21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→30, 30→31, 31→34, 32→35, 33→36, 34→37, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→45 (merged), 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→17 (merged), 57→58, 58→59, 59→60, 60→61, 61→62, 62→63, 63→64 (new entries: 21, 32, 33)

### Section 11: Classical Inequalities, Means, Majorization, and Rearrangement

Size: 22746 → 23846 bytes; entries: 68 → 70.

Sources consulted: Bullen, *Handbook of Means and Their Inequalities* (References/; logarithmic mean and $L<M_{1/3}$); Hardy–Littlewood–Pólya, *Inequalities* (References/; quasi-arithmetic means); CKMA-bib.md and CKMA-bib2.md Section 11 entries (Lieb–Loss, Baernstein–Drasin–Laugesen, Garling).

Changes:
- Introduction: removed a contentless sentence on homogeneity and translation invariance; the actual characterization moved into entry 10.
- Entries 3, 7, 68 (old 66), 67 (old 65): removed padding trailing sentences.
- Entry 9 (Newton–Maclaurin): precision. Newton's inequalities hold for all real $x_i$; only Maclaurin's chain needs nonnegativity.
- Entry 10 (comparison of quasi-arithmetic means): added the uniqueness of generators up to affine change and the classical theorem that the homogeneous quasi-arithmetic means are exactly the power means.
- New entry 11 (logarithmic mean): $G<L<M_{1/3}<A$ with $1/3$ optimal (Lin); the standard non-quasi-arithmetic mean in Bullen and Hardy–Littlewood–Pólya-type texts, absent before.
- Entry 21 (Muirhead, old 20): added the converse (the inequality for all positive $x$ forces $\alpha\prec\beta$).
- Entry 40 (Grönwall, old 39): added the missing continuity hypothesis on $u$.
- Entry 47 (Pólya–Szegő, old 46): replaced a padding sentence by the Brothers–Ziemer equality case.
- New entry 48 (Steiner symmetrization): the basic symmetrization operation and its convergence to the ball, the standard route to isoperimetric and Riesz inequalities in Lieb–Loss and Baernstein–Drasin–Laugesen.
- Entry 51 (HLS, old 49): added Lieb's sharp constant and extremals in the diagonal case.
- Entry 52 (Sobolev, old 50): replaced "closely equivalent" by the precise equivalence of the sharp $p=1$ case with isoperimetry, and added the Aubin–Talenti extremals for $1<p<n$.
- Entry 67 (Khintchine, old 65): added which constants equal one, Szarek's $A_1=1/\sqrt2$, and Haagerup's determination of the optimal constants.
- Internal cross-reference "result 55" (sharp Young) updated to "result 57".

Numbering map (old → new):
11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→20, 20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→30, 30→31, 31→32, 32→33, 33→34, 34→35, 35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→46, 46→47, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68, 67→69, 68→70 (new entries: 11, 48)

### Section 12: Convexity, Convex Analysis, and Variational Analysis

Size: 23687 → 25770 bytes; entries: 66 → 69.

Sources consulted: Nesterov, *Lectures on Convex Optimization* (References/; Theorem 2.1.7 and Assumption 2.1.4 for the lower complexity bound); CKMA-bib.md and CKMA-bib2.md Section 12 entries (Rockafellar, Bauschke–Combettes, Rockafellar–Wets, Attouch, Clarke, Phelps); standard statements checked against these.

Changes:
- Entry 2 (supporting hyperplanes): the second sentence was garbled ("boundary point belonging to its closure"). Rewritten: every boundary point of a convex set in $\mathbb R^n$ is supported; nonempty interior suffices in a TVS; added Bishop–Phelps density of support points and support functionals.
- New entry 7 (Minkowski–Weyl): polyhedra = finitely generated (convex hull + cone); a basic theorem of finite-dimensional convexity in Rockafellar, Barvinok, Boyd–Vandenberghe, absent before.
- Entry 15 (differentiability, old 14): replaced a vague sentence by a.e. differentiability and continuity of the gradient on the differentiability set; added the monotone-gradient and Hessian convexity criteria.
- New entry 20 (Legendre-type functions): essential smoothness/strict convexity duality and the gradient bijection (Rockafellar Thm 26.5); core of conjugacy theory.
- Entry 33 (Moreau envelope, old 31): added monotone convergence to $f$ and equality of infima/minimizers.
- Entry 46 (Berge, old 44), 63 (Douglas–Rachford, old 60), 65 (perspectives, old 62), 66 (tangent cones, old 63): removed padding trailing sentences (Douglas–Rachford now notes weak convergence in Hilbert space).
- Entry 48 (old 46): reformulated as Attouch's theorem, an equivalence (Mosco convergence ⇔ convergence of Moreau envelopes ⇔ convergence of proximal maps plus normalization) rather than a one-way statement with a vague caveat.
- Entry 52 (Clarke chain rule, old 50): replaced a vague caveat by the equality cases (regularity or surjective derivative) and the Clarke sum rule.
- New entry 56 (Krasnosel'skiĭ–Mann iteration): Browder–Göhde–Kirk fixed points and weak convergence of KM iterations via Fejér monotonicity and Opial's lemma; the common principle behind entries 57–63 (Bauschke–Combettes Ch. 4–5).
- Entry 57 (proximal point, old 54): noted Güler's failure of strong convergence and Rockafellar's maximal-monotone version.
- Entry 60 (accelerated gradient, old 57): added Nesterov's matching lower bound $3L\|x_0-x_*\|^2/(32(k+1)^2)$.
- Entry 68 (Brøndsted–Rockafellar, old 65): replaced a padding sentence by density of $\operatorname{dom}\partial f$ in $\operatorname{dom}f$.
- Entry 69 (Rockafellar cyclic monotonicity, old 66): added uniqueness of the potential up to constants and a concrete counterexample (skew linear maps); removed padding.
- Internal cross-reference "result 30" (proximal mapping) updated to "result 32".

Numbering map (old → new):
7→8, 8→9, 9→10, 10→11, 11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63, 61→64, 62→65, 63→66, 64→67, 65→68, 66→69 (new entries: 7, 20, 56)

### Section 13: Matrix Analysis, Operator Monotonicity, and Noncommutative Inequalities

Size: 22847 → 23745 bytes; entries: 74 → 76.

Sources consulted: Bhatia, *Matrix Analysis* (References/; Section III.4, Theorem III.4.1 and Corollary III.4.2 on Lidskii–Wielandt); Horn–Johnson, *Matrix Analysis* and *Topics in Matrix Analysis* (References/, for Gershgorin, Perron–Frobenius, numerical range); CKMA-bib.md and CKMA-bib2.md Section 13 entries (Bhatia, *Positive Definite Matrices*; Carlen; Watrous).

Changes:
- Introduction: condensed the paragraph on products, congruence, and trace cyclicity.
- Entry 5 (Courant–Fischer): added Weyl monotonicity ($A\leq B\Rightarrow\lambda_k(A)\leq\lambda_k(B)$), which was wrongly presented as a consequence of Ky Fan's principle in entry 6.
- Entry 6 (Ky Fan): replaced that sentence by the actual consequence (convexity of the sum of the $k$ largest eigenvalues).
- Entry 9 (spectral majorization): misattribution/weak formulation corrected. $\lambda(A+B)\prec\lambda(A)+\lambda(B)$ is Ky Fan's inequality; Lidskii–Wielandt is the stronger $\lambda(A+B)-\lambda(A)\prec\lambda(B)$ (Bhatia Cor. III.4.2).
- New entry 11 (Gershgorin and Perron–Frobenius): eigenvalue localization and the theory of nonnegative matrices are core in Horn–Johnson and were missing.
- New entry 12 (numerical range): Toeplitz–Hausdorff convexity and numerical-radius norm equivalence (Horn–Johnson, *Topics*, Ch. 1).
- Entry 42 (old 40): correction. Ando's inequality $\Phi(A\sigma B)\leq\Phi(A)\sigma\Phi(B)$ holds for positive (not only completely positive) linear maps and every operator mean; the garbled phrase "positive definite output inputs" removed.
- Entry 46 (Golden–Thompson, old 44): added the equality case and failure for three exponentials.
- Entry 60 (strong subadditivity, old 58): attributed to Lieb–Ruskai; noted equivalence with data processing under partial trace.
- Entry 65 ($\det_2$, old 63): replaced a padding sentence by the zero set of $z\mapsto\det_2(I+zT)$.
- Entry 66 (Sylvester, old 64): replaced a padding sentence by the operator-norm constant $\pi/(2\delta)$ (Bhatia–Davis–McIntosh).
- Entry 67 (Davis–Kahan, old 65): identified $\|(I-P)X\|_2$ with the canonical-angle sines.
- Entries 69–74 (old 67–72): removed padding trailing sentences; log-det barrier stated as self-concordant; Lieb's concavity linked to Tropp's matrix MGF bounds; Bhatia–Kittaneh attribution added.
- Entry 75 (convex spectral functions, old 73): replaced a padding sentence by the conjugacy and subdifferential formulas (Davis, Lewis).
- Reference guide: Horn–Johnson chapters for the two new entries.

Numbering map (old → new):
11→13, 12→14, 13→15, 14→16, 15→17, 16→18, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68, 67→69, 68→70, 69→71, 70→72, 71→73, 72→74, 73→75, 74→76 (new entries: 11, 12)

### Section 14: Functional, isoperimetric, and geometric inequalities

Size: 26021 → 28185 bytes; entries: 70 → 73.

Sources consulted: CKMA-bib.md and CKMA-bib2.md Section 14 (Maz'ya, Bakry–Gentil–Ledoux, Saloff-Coste, Grigor'yan, Aubin, Hebey, Ghoussoub–Moradifam, Baernstein, Henrot, Maggi/Fusco, Lieb–Seiringer, Frank–Laptev–Weidl); local index of References/ (Bakry–Gentil–Ledoux, Ledoux, Lieb–Seiringer, Frank–Laptev–Weidl) to confirm sources; constants checked by direct computation (Euclidean log-Sobolev optimization, entropy decay rate, weak Poincaré polynomial rate via the Liggett argument).

Changes:
- New entry 12, Caffarelli–Kohn–Nirenberg inequality (n≥3, a<(n−2)/2, a≤b≤a+1): core weighted Sobolev family interpolating Sobolev and Hardy; a main topic of Ghoussoub–Moradifam in the bibliography.
- New entry 19, Pólya–Szegő inequality (rearrangement decreases ‖∇u‖_p): the standard tool behind sharp Sobolev, Moser–Trudinger and Faber–Krahn; was missing.
- New entry 53, Grigor'yan–Saloff-Coste theorem (doubling + scale-invariant Poincaré ⇔ parabolic Harnack ⇔ two-sided Gaussian heat-kernel bounds): central result of the Saloff-Coste/Grigor'yan strand; was missing.
- Entry 3 retitled "Sharp Sobolev inequality (Aubin, Talenti)" and extended with the general-p extremal profile.
- Entry 5 (Poincaré): the zero-boundary-value statement now correctly says it needs only finite measure (or boundedness in one direction), no Lipschitz/connectedness; previous wording implied the Lipschitz connected setting.
- Entry 11 (boundary Hardy): "sharp in the standard smooth-boundary cases" replaced by the correct statement that 1/4 is the best constant for every convex domain.
- Entry 13 (HLS, old 12): added Lieb's sharp constant/extremizers for the diagonal case; entry 14 cross-reference updated ("result 13").
- Entry 21 (Faber–Krahn): added uniqueness up to capacity-zero sets and the Krahn–Szegő result for λ₂.
- Entry 24 (quantitative isoperimetry): attributed to Fusco–Maggi–Pratelli.
- Entry 26 (Gaussian isoperimetry): attribution (Borell, Sudakov–Tsirelson) and the equivalent neighbourhood/concentration form added.
- Entry 41 (Nash/heat kernel): padded trailing sentence replaced by a precise remark (only local or defective versions on probability spaces).
- Entry 52 (Bishop–Gromov): added Buser's local Poincaré inequality, linking to new entry 53.
- Entry 63 (Aubin/Yamabe): attribution of the Yamabe problem solution added.
- Entry 70 (Bianchi–Egnell): removed redundant trailing sentence.
- Entry 71 (old 68): misattribution corrected; the ratio inequality is the Ashbaugh–Benguria theorem (the Payne–Pólya–Weinberger conjecture); padded sentence removed.
- Entry 72 (Berezin–Li–Yau): tightened wording.
- Reference guide: added Caffarelli–Kohn–Nirenberg, Baernstein/Lieb–Loss rearrangement route, and the Grigor'yan–Saloff-Coste equivalence.

Numbering map (old → new):
12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63, 61→64, 62→65, 63→66, 64→67, 65→68, 66→69, 67→70, 68→71, 69→72, 70→73 (new entries: 12, 19, 53)

### Section 15: Core Banach and Hilbert space theory

Size: 20382 → 21974 bytes; entries: 66 → 69.

Sources consulted: CKMA-bib.md and CKMA-bib2.md Section 15; Conway, *A Course in Functional Analysis* (table of contents: V.8 Stone–Weierstrass, XI Fredholm theory and index); Brezis and Einsiedler–Ward as listed in the reference guide.

Changes:
- New entry 8, Stone–Weierstrass theorem (real and complex forms): basic density theorem for C(K), in Conway V.8 and every graduate course; was missing.
- New entry 55, Fredholm operators and index (Atkinson's theorem, openness, local constancy, multiplicativity, compact-perturbation invariance): core structure theorem extending the Riesz–Fredholm alternative; was missing.
- New entry 58, Courant–Fischer min–max principle with Weyl's perturbation bound and interlacing: standard variational characterization of eigenvalues of compact self-adjoint operators; was missing.
- Entry 5: replaced the vague "uniform limits preserve continuity…; absolutely summable series in a Banach space converge" with the actual criterion (a normed space is complete iff absolutely summable series converge).
- Entry 6: corrected/strengthened hypotheses — (L^p)^* = L^{p'} for 1<p<∞ holds for every measure, σ-finiteness is needed only for p=1; (L^∞)^* described (bounded finitely additive measures).
- Entry 12 (separation): strict separation stated for a compact convex set and a disjoint closed convex set (the standard form), with the point case as corollary.
- Entry 16 (Goldstine): padded sentence replaced by the precise consequence.
- Entry 33: Clarkson's inequalities named as the reason L^p is uniformly convex.
- Entry 35 (direct method): removed the redundant proviso "provided that infimum is finite" (automatic under properness and coercivity).
- Entry 47 (closed range): Banach-space annihilator form ran T = (ker T*)_⊥, ran T* = (ker T)^⊥ stated generally rather than only for Hilbert spaces; surjectivity ⇔ T* bounded below added.
- Entry 48 (old 47): retitled Gantmacher theorem; added T weakly compact ⇔ T* weakly compact and the Davis–Figiel–Johnson–Pełczyński converse factorization.
- Entry 54: cross-reference updated to "result 53".
- Entry 59 (SVD): singular values now ordered nonincreasingly (needed for the best-approximation claim) and identified with eigenvalues of T*T.
- Entry 69 (Arzelà–Ascoli): padded trailing sentence removed.
- Reference guide: Conway V.8 and Chapter XI added.

Numbering map (old → new):
8→9, 9→10, 10→11, 11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→20, 20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→30, 30→31, 31→32, 32→33, 33→34, 34→35, 35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→53, 53→54, 54→56, 55→57, 56→59, 57→60, 58→61, 59→62, 60→63, 61→64, 62→65, 63→66, 64→67, 65→68, 66→69 (new entries: 8, 55, 58)

### Section 16: Locally convex spaces, duality, and distributions

Size: 21920 → 23212 bytes; entries: 65 → 67.

Sources consulted: CKMA-bib.md and CKMA-bib2.md Section 16; Schaefer–Wolff, Osborne, Ryan, Duistermaat–Kolk (local copies listed in the reference guide); Fourier constants checked by direct computation from the stated normalization.

Changes:
- New entry 55, basic Fourier pairs and singular distributions (Gaussian, |x|^{-a} with explicit constant, p.v. 1/x and its transform, Sokhotski–Plemelj): standard working examples used throughout the distribution texts; were missing.
- New entry 64, classical fundamental solutions (Laplacian in n=2 and n≥3, heat operator, ∂/∂z̄): core explicit content accompanying Malgrange–Ehrenpreis; was missing.
- Entry 63 (Malgrange–Ehrenpreis): the remark "the solution need not be tempered" was misleading — a tempered fundamental solution always exists (Hörmander, Łojasiewicz); replaced accordingly.
- Entry 4: Kolmogorov attribution; vague "weak topologies are generally not norm topologies" replaced by the exact statement (never normable, not even metrizable, in infinite dimension).
- Entry 17: generalized from Banach spaces to metrizable, barrelled, and bornological spaces (Mackey spaces).
- Entry 19: padded sentence replaced by the precise statement (kernel of restriction, weak homeomorphisms).
- Entry 20 (Krein–Milman): padded sentence replaced by Milman's converse.
- Entry 21: "pointwise limits … are continuous when they exist" corrected to pointwise limits of sequences (false for nets).
- Entry 28 (Montel): added that the strong dual is Montel and that weak-star convergent sequences in D', E', S' converge strongly; previous last sentence was vague.
- Entry 33: padded sentence replaced by separability of nuclear Fréchet spaces.
- Entry 42: padded sentence replaced by the order bound m = order of T.
- Entry 43: added the global structure of compactly supported distributions; padded sentence removed.
- Entry 44: unclear "no unrecorded boundary term" replaced by the jump formula.
- Entry 52: added the structure theorem for tempered distributions (finite sum of derivatives of continuous polynomially bounded functions).
- Entry 67 (Weyl lemma): padded trailing sentence removed.

Numbering map (old → new):
55→56, 56→57, 57→58, 58→59, 59→60, 60→61, 61→62, 62→63, 63→65, 64→66, 65→67 (new entries: 55, 64)

### Section 17: Banach space geometry, bases, and operator ideals

Size: 20332 → 23662 bytes; entries: 64 → 69.

Sources consulted: CKMA-bib.md and CKMA-bib2.md Section 17; Albiac–Kalton, *Topics in Banach Space Theory* (table of contents: Chapters 7–12, uniqueness of unconditional bases, Rosenthal, Tsirelson); Diestel, Diestel–Jarchow–Tonge, Ryan as listed in the reference guide.

Changes:
- New entry 22, James distortion theorem for c_0 and ℓ^1, with the Odell–Schlumprecht contrast for ℓ^p: standard structural result in Albiac–Kalton/Lindenstrauss–Tzafriri; was missing.
- New entry 29, Pełczyński decomposition method, primeness of ℓ^p and c_0, and uniqueness of unconditional bases (Lindenstrauss–Pełczyński, Lindenstrauss–Zippin): core isomorphic-classification tools; were missing.
- New entry 31, subspaces of L^p (Khintchine/Rademacher copy of ℓ^2, Kadec–Pełczyński dichotomy for p>2, L^p ≇ ℓ^p for p≠2): core classical-space structure; was missing.
- New entry 34, Tsirelson space, Gowers–Maurey hereditarily indecomposable spaces, Gowers dichotomy, homogeneous space problem: the modern structural landmarks behind the "exotic spaces" mentioned in the reference guide; were missing.
- New entry 69, Bourgain embedding theorem with optimality: core result of the metric-embedding strand (Ostrovskii in CKMA-bib2).
- Entry 5: corrected — complementability is not preserved under the stated perturbation condition alone; the correct condition ‖P‖Σ‖x_n*‖‖x_n−y_n‖<1 is now stated.
- Entry 6: Mazur attribution; trailing sentence replaced by cross-reference to Enflo (result 32).
- Entry 7: added the consequence that seminormalized weakly null sequences have basic subsequences in every Banach space.
- Entry 30 (Haar, old 28): Paley/Marcinkiewicz attribution; strengthened to "L^1 has no unconditional basis and does not embed in a space with one".
- Entry 39 (Dvoretzky, old 35): added the quantitative log n dimension bound and its optimality for ℓ_∞^n.
- Entry 40 (John, old 36): proof sketch replaced by the precise inclusion E ⊂ B_X ⊂ √n E.
- Entry 46 (old 42): Enflo/James attribution and Pisier's power-type renorming added.
- Reference guide: Albiac–Kalton Chapters 9 and 11 and Ostrovskii mentioned.

Numbering map (old → new):
22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→30, 29→32, 30→33, 31→35, 32→36, 33→37, 34→38, 35→39, 36→40, 37→41, 38→42, 39→43, 40→44, 41→45, 42→46, 43→47, 44→48, 45→49, 46→50, 47→51, 48→52, 49→53, 50→54, 51→55, 52→56, 53→57, 54→58, 55→59, 56→60, 57→61, 58→62, 59→63, 60→64, 61→65, 62→66, 63→67, 64→68 (new entries: 22, 29, 31, 34, 69)

### Section 18: Vector-valued analysis and analysis in Banach spaces

Size: 22292 → 24516 bytes; entries: 62 → 66.

Sources consulted: CKMA-bib.md and CKMA-bib2.md Section 18; Arendt–Batty–Hieber–Neubrander (table of contents: Chapter 2 Widder theorem, Appendix A vector-valued holomorphic functions); Hytönen–van Neerven–Veraar–Weis Vol. II (table of contents); Pisier and Kunstmann–Weis as listed in the reference guide.

Changes:
- New entry 35, vector-valued Calderón–Zygmund theorem (Benedek–Calderón–Panzone): the standard extrapolation tool for operator-valued kernels; was missing.
- New entry 53, vector-valued holomorphy (Dunford's weak-implies-strong theorem, Cauchy formula, Liouville, Vitali): foundational and used throughout the Laplace-transform and functional-calculus entries; was missing.
- New entry 56, Widder–Arendt theorem: central Laplace-transform characterization in Arendt–Batty–Hieber–Neubrander, giving Hille–Yosida and integrated semigroups; was missing.
- New entry 60, Dore–Venni operator-sum theorem: classical route to maximal regularity on UMD spaces via bounded imaginary powers; was missing.
- Entry 11: obscure trailing sentence ("stronger than a formal scalarization…") replaced by concrete facts (L^1[0,1], C[0,1] fail RNP; RNP separably determined, not inherited by quotients).
- Entry 19: awkward converse ("detects UMD when it contains a copy of X") replaced by "exactly when"; Burkholder's ζ-convexity characterization of UMD added.
- Entry 61 (Weis, old 57): sharpened — R-sectoriality is necessary on every Banach space (Clément–Prüss) and sufficient on UMD spaces (Weis); p-independence of maximal regularity holds in every Banach space.
- Entry 66 (old 62): padded trailing sentence removed.
- Reference guide: vector-valued holomorphy and Widder–Arendt noted for Arendt–Batty–Hieber–Neubrander.

Numbering map (old → new):
35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→54, 53→55, 54→57, 55→58, 56→59, 57→61, 58→62, 59→63, 60→64, 61→65, 62→66 (new entries: 35, 53, 56, 60)

### Section 19: Banach Lattices, Positive Operators, and Ordered Structures

Size: 19321 → 23283 bytes; entries: 60 → 63.

Sources consulted: Aliprantis–Burkinshaw, Positive Operators (References/AliprantisBirkinshaw2006PositiveOperators-Springer.pdf: Thms 5.10, 5.13–5.15, 5.20, 5.31, 5.32, Examples 5.17–5.19); Bátkai–Kramar Fijavž–Rhandi, Positive Operator Semigroups (References/BatkaiFijavzRhandi2017...pdf: Thms 12.7, 12.15, 12.17, Cor. 12.9, Cor. 15.11, Example 12.16, Thm A.38); bibliography entries for Meyer-Nieberg, Schaefer, Luxemburg–Zaanen, Engel–Nagel.

Changes:
- 1: added the basic inequalities $|x+y|\le|x|+|y|$, $||x|-|y||\le|x-y|$; stated distributivity precisely.
- 3: replaced vague "corresponding formulas" by the infinite distributive law.
- 4: made explicit that $A^d$ is a band in every vector lattice (Archimedean needed only for $A^{dd}$).
- 5: added that Dedekind $\sigma$-complete spaces have principal band projections.
- 6: corrected scope: bands form a complete Boolean algebra already in Archimedean vector lattices; projection statements for the Dedekind complete case.
- 8 (Freudenthal): hypothesis weakened to the principal projection property (the standard hypothesis).
- 10: quotient map stated as a lattice homomorphism.
- 11: expanded to the standard list of equivalent order-continuity criteria (Meyer-Nieberg 2.4.2) and removed padding sentence; added that order continuous Banach lattices are Dedekind complete.
- 14 (KB): added weak sequential completeness and the subspace (not only sublattice) form of the $c_0$ criterion.
- 15 (Lozanovsky): stated with subspace copies, noting lattice copies suffice.
- 16: replaced "infinite $\ell^\infty$" by $\ell^\infty$ and $C(K)$, $K$ infinite.
- 25: replaced "positive Hahn–Banach on majorizing sublattice" by the Kantorovich extension theorem (majorizing subspace, Dedekind complete target), of which the old statement is a special case.
- 28: replaced the vague trailing sentence by a precise caveat.
- New 30 (Bohnenblust–Nakano–Kakutani abstract $L^p$ spaces): core representation theorem, missing.
- 33 (Krivine): added the $p$-sums and transfer of scalar inequalities.
- New 34 (p-convexity, q-concavity, Maurey's finite cotype characterization, square function vs Rademacher averages): core Banach-lattice geometry, missing.
- New 35 (lattice homomorphisms: adjoint interval-preserving; weighted compositions on $C(K)$; Kaplansky): core, missing; definition of lattice homomorphism added to section intro.
- Weak compactness section intro: added definitions of L-weakly compact operators (used in old 37 but undefined) and AM-compact operators.
- 41 (old 38): attributed to Wickstead, added necessity of the hypothesis and the Aliprantis–Burkinshaw square theorem for weak compactness (AB Thms 5.31–5.32).
- 42 (old 39): "finite rank" sharpened to "rank one" (AB Example 5.17).
- 45 (old 42): the vague/imprecise "modulus" statement replaced by the actual Dodds–Fremlin theorem: AM-compact operators into a Dedekind complete space with order continuous norm form a band (AB Thm 5.10), with modulus and domination consequences.
- Spectral section intro: strong positivity defined on ordered Banach spaces with solid cone (a Banach lattice with solid cone is essentially $C(K)$, so the old formulation was too narrow for the PDE use).
- 46: specified Banach lattice and Neumann series for the positive resolvent.
- 48 (Perron–Frobenius): added $n\ge2$ (the $1\times1$ zero matrix), uniqueness of the positive eigenvector, and the precise peripheral spectrum with simplicity.
- 50 (Krein–Rutman): noted ordered Banach spaces with total cone.
- 51 (old 48): restated as the strong Krein–Rutman theorem on ordered Banach spaces with solid cone; added uniqueness of positive eigenvector and typical spaces $C(\overline\Omega)$, $C^1_0(\overline\Omega)$.
- 52 (old 49): removed the superfluous hypothesis $r(T)>0$, replaced by de Pagter's theorem (dimension > 1); peripheral spectrum stated precisely.
- Removed old 50 (positive continuous kernel example): illustrative, not a principal result.
- 54 (old 52): proof sketch condensed to the Laplace/Euler formulas.
- New 57 (spectral bound of positive semigroups: $s(A)\in\sigma(A)$, Laplace representation for Re λ > s(A), $s=\omega_0$ on AL, $C_0(\Omega)$, Hilbert lattices, $L^p$ (Derndinger, Weis), failure in general): the growth and spectral bounds were defined but no theorem used them; this is core.
- New 58 (Beurling–Deny criteria for positivity and sub-Markov property of form semigroups): core link to PDE.
- 60 (old 56): removed padded semigroup sentence.
- 62 (old 58): merged Bernstein approximation (old 59), with the explicit test-function computation.
- Reference guide: added Lindenstrauss–Tzafriri II / Meyer-Nieberg for convexity, and Ouhabaz for Beurling–Deny (not local copies).

Numbering map (old → new):
30→31, 31→32, 32→33, 33→36, 34→37, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→47, 45→48, 46→49, 47→50, 48→51, 49→52, 50→removed, 51→53, 52→54, 53→55, 54→56, 55→59, 56→60, 57→61, 58→62, 59→62 (merged), 60→63

### Section 20: Banach Algebras and Commutative Harmonic Analysis of Algebras

Size: 21157 → 22482 bytes; entries: 64 → 63.

Sources consulted: Kaniuth, A Course in Commutative Banach Algebras (References/Kaniuth2009...pdf: ToC, Thm 1.2.9 and notes, §3.2 and notes on Arens–Royden and Arens–Calderón, Ch. 5 introduction on Ditkin sets and coset-ring hulls); Bonsall–Duncan and Runde (as in the existing guide); bibliography entries for Gamelin, Dales, Palmer.

Changes:
- 1: replaced the redundant last clause by explicit continuity of inversion.
- 2: added Newburgh upper semicontinuity of the spectrum.
- 6 (Gelfand–Mazur): corrected a false claim. Completeness is not essential, since the theorem holds for complex normed division algebras (Mazur). Added the real case ($\mathbb R,\mathbb C,\mathbb H$).
- 7: added continuity of the calculus and the composition rule.
- 9: replaced "lies in the polynomial hull" by the sharper standard statement $\partial\sigma_B\subset\partial\sigma_A$ (holes filled in), and added spectral permanence for C*-subalgebras.
- 10: "converse requires commutativity" made precise: it holds for commutative algebras and fails in general (matrices).
- New 17 (several-variable holomorphic calculus, Shilov–Arens–Calderón; $\exp A$ is the identity component; Arens–Royden): core commutative Banach algebra theory, missing. It also underlies the Shilov idempotent theorem.
- 18 (old 17): added Johnson's uniqueness-of-norm theorem for semisimple algebras.
- 28 (old 27): removed the meaningless trailing sentence and added Poisson representing measures and $P(\mathbb T)$.
- New 29 (Carleson corona theorem): core result on uniform algebras and $H^\infty$ (Gamelin, Mortini–Rupp in the bibliography), missing.
- 40 (old 38): attributed the holomorphic extension to Lévy.
- 43 (old 41): Malliavin entry broadened to a spectral-synthesis entry with positive results (points, closed subgroups, coset-ring sets are Ditkin sets) and Schwartz's sphere example.
- 45 (old 43): made precise (nondiscrete $G$; spectrum strictly larger than the closure of the range of $\widehat\mu$).
- 46 (old 44): added the characterization of hulls of ideals with bounded approximate identities (coset ring).
- 47 (old 45): merged old 46 (approximate identities in modules) and sharpened the factorization statement ($y\in\overline{Ax}$ close to $x$).
- 48 (old 47): trimmed padding.
- Removed old 48 (derivations and exponentials): elementary and peripheral.
- 49: added Thomas's theorem (continuity not needed) and Johnson's theorem that derivations on commutative semisimple algebras vanish.
- 61: merged old 62 (double-limit criterion) into old 61, attributed to Grothendieck.
- 62 (old 63): removed padding and named the enveloping von Neumann algebra.
- 63 (old 64): attributed to Young.
- Reference guide: noted Kaniuth's several-variable calculus and Gamelin for corona.

Numbering map (old → new):
17→18, 18→19, 19→20, 20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→47 (merged), 47→48, 48→removed, 62→61 (merged), 63→62, 64→63

### Section 21: Operator Theory: Bounded Operators, Spectra, and Model Theory

Size: 19981 → 22655 bytes; entries: 62 → 66.

Sources consulted: existing local copies in the reference guide, in particular Gohberg–Goldberg–Kaashoek (Fredholm and trace ideals), Sz.-Nagy–Foiaş–Bercovici–Kérchy (dilations, models, commutant lifting), Nikolski, Toeplitz Matrices and Operators (Toeplitz/Szegő); bibliography entries for Conway, Douglas, Radjavi–Rosenthal, Chalendar–Partington. Statements were checked against standard formulations. No new local copy was added.

Changes:
- New 7 (Fuglede–Putnam theorem): basic core tool for normal operators, missing.
- New 9 (numerical range: Toeplitz–Hausdorff, spectral inclusion, $w\le\|T\|\le2w$, normal case): core, missing.
- 13 (old 11): index of the adjoint holds for Banach-space adjoints too (the old version restricted it to Hilbert space without reason).
- New 18 (Weyl–von Neumann–Berg and Brown–Douglas–Fillmore): essential unitary equivalence is core Calkin-algebra theory (Conway, Douglas), missing.
- New 20 (Calkin's theorem on ideals of $\mathcal B(H)$): core, missing.
- 21 (old 17): indexing convention $s_1\ge s_2\ge\cdots$ made explicit (needed for the formula with rank $<n$).
- 24 (old 20): added continuity and multiplicativity of the Fredholm determinant.
- New 25 (Weyl inequalities between eigenvalues and singular values): core trace-ideal theory (GGK, Simon), missing.
- 32 (old 27): failure for three contractions made precise (Parrott for dilation, Varopoulos for the inequality).
- 37 (old 32): added Sarason's theorem as the scalar case of commutant lifting and its consequences (Pick, Nehari).
- 38 (old 33): added Pisier's counterexample to Halmos's similarity problem.
- 48 (old 43): retitled "Szegő limit theorems" and added the first Szegő (Szegő–Kolmogorov–Krein) theorem.
- 52 (old 47): retitled and supplemented with Aronszajn–Smith, S. Brown (subnormal), Enflo/Read counterexamples on Banach spaces, and the open Hilbert-space problem.
- 61 (old 56): merged old 57 (local spectral subspaces of normal operators), which is a direct restatement of 56.
- Reference guide: added Conway and Douglas for Calkin algebra and BDF.

Numbering map (old → new):
7→8, 8→10, 9→11, 10→12, 11→13, 12→14, 13→15, 14→16, 15→17, 16→19, 17→21, 18→22, 19→23, 20→24, 21→26, 22→27, 23→28, 24→29, 25→30, 26→31, 27→32, 28→33, 29→34, 30→35, 31→36, 32→37, 33→38, 34→39, 35→40, 36→41, 37→42, 38→43, 39→44, 40→45, 41→46, 42→47, 43→48, 44→49, 45→50, 46→51, 47→52, 48→53, 49→54, 50→55, 51→56, 52→57, 53→58, 54→59, 55→60, 56→61, 57→61 (merged), 58→62, 59→63, 60→64, 61→65, 62→66

### Section 22: Unbounded Operators, Spectral Theory, and Mathematical Physics

Size: 21420 → 23859 bytes; entries: 66 → 68.

Sources consulted: existing local copies in the reference guide (Kato; Borthwick; Hall; Frank–Laptev–Weidl; Davies, Linear Operators and Their Spectra), used to check statement wording; bibliography entries for Reed–Simon, Cycon–Froese–Kirsch–Simon, Hislop–Sigal, Trefethen–Embree, Marchenko. No new local copy was added.

Changes:
- 28: merged old 32 (Dirichlet bracketing consequences) into old 28. The old 32 stated only the weak, partial inequality "pieces-Neumann below Ω-Dirichlet". It is replaced by the full standard chain $\oplus N_{\Omega_k}\le N_\Omega\le D_\Omega\le\oplus D_{\Omega_k}$.
- 38 (old 39, Birman–Schwinger): fixed an ambiguous wording ("one is an eigenvalue", meaning the number 1). The counting statement is now in words.
- New 39 (Trotter product formula, unitary and form-sum semigroup versions): core tool, basis of Feynman–Kac, missing.
- 42 (old 42): Coulomb entry broadened to Kato's theorem ($V\in L^2+L^\infty$ on $\mathbb R^3$, atomic Hamiltonians). Added the hydrogen spectrum $-c^2/(4n^2)$ with multiplicity $n^2$.
- New 44 (HVZ theorem): the core essential-spectrum theorem for N-body operators, missing.
- 45 (old 44): removed the proof sketch. Added the harmonic oscillator spectrum.
- 55 (old 54): added Borg–Marchenko uniqueness.
- New 60 (short-range scattering: limiting absorption principle, absence of embedded and singular continuous spectrum, asymptotic completeness, Agmon–Kato–Kuroda/Enss/Mourre): core of Schrödinger scattering, missing.
- 61 (old 59): added Birman–Kuroda (trace-class resolvent difference) and retitled.
- 68 (old 66): added the Kreiss matrix theorem as the converse quantitative statement.
- Reference guide: named Reed–Simon III–IV, CFKS, and Hislop–Sigal for HVZ and short-range scattering.

Numbering map (old → new):
32→28 (merged), 33→32, 34→33, 35→34, 36→35, 37→36, 38→37, 39→38, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→53, 53→54, 54→55, 55→56, 56→57, 57→58, 58→59, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68

### Section 23: Operator Algebras, Operator Spaces, Free Probability, and Noncommutative Geometry

Size: 23730 → 26388 bytes; entries: 77 → 81.

Sources consulted: Strung, An Introduction to C*-algebras and the Classification Program (References/Strung2021...pdf; Kirchberg–Phillips passages); the other local copies already listed (Blackadar, Paulsen, Nica–Speicher, Mingo–Speicher, Gracia-Bondía–Várilly–Figueroa), used to check statements; bibliography entries for Takesaki, Kadison–Ringrose, Connes.

Changes:
- 23: added Sakai's characterization of von Neumann algebras as C*-algebras with a Banach predual.
- New 30 (group von Neumann algebras, ICC criterion, uniqueness of the hyperfinite II$_1$ factor, $L(\mathbb F_2)\not\cong R$, Connes's theorem that injective equals hyperfinite): core von Neumann algebra theory, missing.
- New 34 (derivations: Sakai automatic continuity, Kadison–Sakai innerness): core, missing.
- New 39 (Connes cocycle derivative and the III$_0$/III$_\lambda$/III$_1$ classification via $S(M)$): central result of modular theory, missing.
- 46 (old 43): removed padding sentence and added attribution (Connes, Haagerup).
- New 54 (Cuntz algebras and their K-theory, Kirchberg–Phillips classification, $\mathcal O_2$-absorption, Elliott classification in the stably finite case): core of the classification program (Strung is a local reference), missing.
- 60 (old 56): added the Haagerup–Paulsen–Wittstock factorization $\Phi=V^*\pi(\cdot)W$ with $\|V\|\|W\|=\|\Phi\|_{\rm cb}$ and retitled.
- 67 (old 63): added the Marchenko–Pastur identification of the free Poisson law (normalization checked by first two moments).
- 81 (old 77): replaced padding sentence by the attribution to Atiyah–Singer.
- Reference guide: Takesaki for the Connes cocycle and type III; Strung for classification.

Numbering map (old → new):
30→31, 31→32, 32→33, 33→35, 34→36, 35→37, 36→38, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→47, 45→48, 46→49, 47→50, 48→51, 49→52, 50→53, 51→55, 52→56, 53→57, 54→58, 55→59, 56→60, 57→61, 58→62, 59→63, 60→64, 61→65, 62→66, 63→67, 64→68, 65→69, 66→70, 67→71, 68→72, 69→73, 70→74, 71→75, 72→76, 73→77, 74→78, 75→79, 76→80, 77→81

### Section 24: Semigroups, evolution equations, and functional calculus

Size: 18695 → 22133 bytes; entries: 60 → 63.

Sources consulted: Engel–Nagel, A Short Course on Operator Semigroups (compact semigroups, exponential formula, essential growth bound); Prüss, Evolutionary Integral Equations (Ch. 1, Sec. 4.3 subordination principle, Thm 4.1); bib entries Pazy, Tanabe, Yagi, Ouhabaz, Amann, Lunardi, Henry-type semilinear theory (via Pazy Ch. 6).

Changes:
- Correction (10): the exponential formula $T(t)x=\lim(I-tA/n)^{-n}x$ holds for every $C_0$-semigroup, not only for contraction generators.
- Reformulation (11): Stone's theorem stated precisely ($A=iH$, $H$ self-adjoint, exactly the unitary groups).
- Addition to 12: converse well-posedness theorem (closed $A$ gives a well-posed Cauchy problem exactly when it is a generator).
- Addition to 20: characterization of bounded analytic semigroups via $T(t)X\subset D(A)$ and $\sup\|tAT(t)\|<\infty$.
- Addition to 29: m-accretive operators on Hilbert space have a contractive $H^\infty$ calculus on the right half-plane (von Neumann inequality).
- Correction/precision (31): independence of $p$ of maximal regularity holds on every Banach space (Dore), and maximal regularity forces analytic generation; previously suggested as a UMD-only fact.
- New entry 37 (compact semigroups): immediately compact iff immediately norm continuous with compact resolvent; spectral consequences. Core in Pazy and Engel–Nagel.
- Reformulation (41, quasicompact asymptotics): the vague "part in a far right half-plane" replaced by the precise statement $\omega_0=\max(\omega_{\rm ess},s(A))$, finitely many poles with finite-rank residues beyond any $w>\omega_{\rm ess}$, explicit expansion with remainder $O(e^{wt})$.
- New entry 44 (spectral bound of positive semigroups): $s(A)\in\sigma(A)$, Laplace representation for $\operatorname{Re}\lambda>s(A)$, $s(A)=\omega_0$ on $L^p$ (Weis) and $C_0(\Omega)$. Core of positive semigroup theory (Engel–Nagel, Bátkai–Kramar Fijavž–Rhandi).
- New entry 49 (J.-L. Lions' theorem for nonautonomous forms): the basic $L^2(V)\cap H^1(V')$ well-posedness theorem for parabolic problems.
- Merge: old 48 (fractional heat evolution, an example) merged into the Bernstein subordination entry (now 50).
- Precision (52, Crandall–Liggett): removed redundant trailing sentence; convergence stated uniformly on bounded intervals for every $x\in\overline{D(B)}$.
- Addition to 53: Brezis regularizing effect for subgradient flows (minimal-section right derivative, $u(t)\in D(\partial\Phi)$ for $t>0$).
- Addition to 55: semilinear parabolic theory in $D(B^\alpha)$ (Henry, Pazy).
- New entry 56 (parabolic evolution families, Sobolevskii–Tanabe): core nonautonomous result in Pazy, Tanabe, Yagi, Lunardi.
- Reformulation (57, Volterra): replaced the bounded-operator-only statement with the resolvent-family/well-posedness equivalence for closed $A$, the bounded case, and Prüss's subordination result for completely positive kernels.
- Reference guide: updated the final sentences for Volterra and nonautonomous coverage; added Prüss to local copies.
- Heading "Nonlinear and Volterra evolution" renamed "Nonlinear, nonautonomous, and Volterra evolution".

Numbering map (old → new):
37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→45, 44→46, 45→47, 46→48, 47→50, 48→50 (merged), 49→51, 50→52, 51→53, 52→54, 53→55, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63

### Section 25: Integral equations and classical operator methods

Size: 18176 → 21268 bytes; entries: 56 → 60.

Sources consulted: Gohberg–Goldberg–Kaashoek, Classes of Linear Operators I, Ch. XII (Wiener–Hopf integral operators, symbol and index convention, Thm XII.3.1); Kress and Zemyan (existing local copies) for Fredholm determinant and Volterra material; bib entries Gakhov, Muskhelishvili, Gohberg–Krupnik, Kenig, Medková.

Changes:
- New entry 13 (Fredholm determinant): Fredholm's entire determinant and minor series for continuous kernels, zeros = exceptional parameters, trace-class product formula. Classical core in Kress, Zemyan, Hochstadt, Kanwal.
- Tightening (16, old 15): removed the redundant second sentence; stated that the range of a compact injective operator on infinite-dimensional Hilbert space is not closed.
- New entry 21 (Paley–Wiener theorem for convolution Volterra equations on the half-line): $L^1$ resolvent iff $\hat k(z)\neq1$ on $\operatorname{Re}z\geq0$. Core of Volterra theory (Gripenberg–Londen–Staffans, Brunner).
- Correction (24, old 22): the weakly singular Volterra solvability and Mittag-Leffler solution hold for all $\alpha>0$, not only $0<\alpha\leq1$.
- New entry 28 (scalar Riemann–Hilbert problem): solvability according to the index $\kappa$, canonical function. Core of the Muskhelishvili/Gakhov literature in the bibliography, previously absent.
- Extension (30, old 27, retitled "Toeplitz and Wiener–Hopf operators"): added Krein's Fredholm criterion and index formula for Wiener–Hopf integral operators, with the symbol convention of Gohberg–Goldberg–Kaashoek.
- New entry 41 (Verchota): invertibility of $-\frac12I+K$ on $L^2$ and $\frac12I+K'$ on $L^2_0$ on Lipschitz domains via Rellich identities; core of the Kenig/Calderón-programme references in the bibliography.
- Precision (44, old 40): stated that the combined-field equation is for the exterior Dirichlet problem; attributed to Brakhage–Werner.
- Correction/precision (49, old 45, Nyström): "consistent positive quadratures" replaced by quadratures convergent for every continuous function (the actual hypothesis); added the error estimate $\|u_n-u\|\leq C\|(K_n-K)u\|$.
- Precision (58, old 54, discrepancy principle): added that it attains the optimal rate only for source exponents $\nu\leq1/2$; trimmed the trailing sentence.
- Reference guide: added Riemann–Hilbert, Wiener–Hopf/Toeplitz and Lipschitz-boundary sources; added Gohberg–Goldberg–Kaashoek to local copies.

Numbering map (old → new):
13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→20, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→29, 27→30, 28→31, 29→32, 30→33, 31→34, 32→35, 33→36, 34→37, 35→38, 36→39, 37→40, 38→42, 39→43, 40→44, 41→45, 42→46, 43→47, 44→48, 45→49, 46→50, 47→51, 48→52, 49→53, 50→54, 51→55, 52→56, 53→57, 54→58, 55→59, 56→60

### Section 26: Sobolev spaces, smoothness scales, and interpolation

Size: 22535 → 23307 bytes; entries: 72 → 74.

Sources consulted: Leoni, A First Course in Sobolev Spaces, 2nd ed. (Ch. 18 traces: Gagliardo's theorem $\operatorname{Tr}W^{1,1}=L^1(\partial\Omega)$, Peetre's counterexample; App. C.6 Hardy's inequality); existing local copies (Tartar, Lunardi, Triebel, Maz'ya) as background; bib entries Brezis, Evans–Gariepy, Bourgain–Brezis–Mironescu literature.

Changes:
- New entry 11 (difference quotients and Lipschitz functions): characterization of $W^{1,p}$, $1<p\leq\infty$, by translation estimates; $W^{1,\infty}_{\rm loc}$ = locally Lipschitz; Rademacher; $BV$ at $p=1$. Core in Brezis, Evans, Leoni.
- Tightening (19, old 18, Poincaré): replaced the padding sentence by the correct scope of the $W_0^{1,p}$ inequality (every bounded open set).
- Extension (24, old 23, trace theorem): added the $p=1$ case — trace onto $L^1(\partial\Omega)$ (Gagliardo) without bounded linear right inverse (Peetre).
- Correction (26, old 25): $W_0^{1,p}=\ker\gamma$ on Lipschitz domains holds for $1\leq p<\infty$, not only $1<p<\infty$.
- New entry 30 (Hardy inequality near the boundary for $W_0^{1,p}$, sharp constant on convex domains): standard core tool (Leoni, Maz'ya, Kufner).
- Retitle (33, old 31): attributed the quasi-everywhere characterization of $W_0^{1,p}$ to Havin–Bagby.
- Removed padding sentences in old 30 (now 32), old 33 (now 35), old 72 (now 74).
- Extension (34, old 32): a.e. classical differentiability of $W^{1,p}_{\rm loc}$ for $p>d$ (Calderón), replacing a vague trailing sentence.
- Extension (42, old 40, BBM): added the converse characterization of $W^{1,p}$ ($1<p<\infty$) and of $BV$ ($p=1$, Dávila) by the normalized Gagliardo energies, replacing a padding sentence.
- Correction of attribution (65, old 63): Lions–Peetre proved compactness interpolation only when source or target spaces coincide; the general real-method statement as given is Cwikel's theorem.

Numbering map (old → new):
11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→20, 20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68, 67→69, 68→70, 69→71, 70→72, 71→73, 72→74

### Section 27: Fourier analysis and real-variable harmonic analysis

Size: 20239 → 21181 bytes; entries: 68 → 68.

Sources consulted: Grafakos, Modern Fourier Analysis, 2nd ed., §7.4 (sharp maximal function, interpolation with BMO) and related notes; existing local copies Grafakos Classical, Stein–Shakarchi, Muscalu–Schlag as background; bib entries Stein, Duoandikoetxea, Cruz-Uribe–Martell–Pérez (sparse domination, sharp weighted bounds).

Changes:
- Extension (14): added the $L^2$ Paley–Wiener theorem (band-limited $L^2$ functions = entire functions of exponential type).
- Correction/precision (23): Kolmogorov's example diverges everywhere (not merely almost everywhere); replaced the padding sentence by du Bois-Reymond's continuous counterexample.
- Reformulation (41, Cotlar–Stein): stated with the precise hypotheses $\sup_j\sum_k\|T_j^*T_k\|^{1/2}\leq A$ etc. and the conclusion $\|\sum T_j\|\leq A$; removed the vague trailing sentence.
- Extension (47): sharp weighted bound $[w]_{A_p}^{\max(1,1/(p-1))}$ (Hytönen's $A_2$ theorem) and Lerner's sparse domination — now standard core in the advanced texts.
- New entry 51 (Fefferman–Stein sharp maximal function inequality $\|f\|_p\leq C\|M^\#f\|_p$): core tool for BMO interpolation and weighted theory.
- Extension (52, old 51): equivalence of Poisson, smooth and grand maximal characterizations of $H^p$, $0<p<\infty$, and $H^p=L^p$ for $p>1$.
- Extension (55, old 54): converse of the commutator theorem (Coifman–Rochberg–Weiss: bounded $[b,R_j]$ forces $b\in\mathrm{BMO}$).
- Merge: old 56 (randomization, a proof device) merged into the Littlewood–Paley entry 56 (old 55), which also now records the one-dimensional sharp-cutoff version.
- Tightening (68): removed padding sentence; attributed the ball multiplier theorem to C. Fefferman (Besicovitch sets).

Numbering map (old → new):
51→52, 52→53, 53→54, 54→55, 55→56, 56→56 (merged)

### Section 28: Abstract harmonic analysis on groups

Size: 20008 → 22526 bytes; entries: 60 → 63.

Sources consulted: Folland, A Course in Abstract Harmonic Analysis, 2nd ed. (Thm 3.34 Gelfand–Raikov; §6.6 Mackey machine for regular semidirect products); Faraut, Analysis on Lie Groups (Ch. 11 Weyl integration and character formulas; Gelfand pairs); existing local copies Hewitt–Ross II, Kaniuth–Taylor, Deitmar–Echterhoff as background; bib entries Rudin (spectral synthesis), Kaniuth–Lau (Eymard's Fourier algebra).

Changes:
- New entry 19 (Gelfand–Raikov theorem): irreducible unitary representations separate points of any locally compact group; basic existence theorem in Folland, Hewitt–Ross, Dixmier.
- Precision (31, old 30): named the SNAG theorem and gave the explicit formula for the integrated operators instead of a vague sentence.
- Extension (32, old 31): failure of spectral synthesis on every noncompact LCA group (Malliavin), the essential complement to Wiener's Tauberian theorem.
- New entry 46 (Weyl's formulas for compact connected Lie groups: highest weights, character and dimension formulas, integration formula): core of harmonic analysis on compact Lie groups (Faraut, Bump, Knapp).
- Precision (50, old 48): corrected the definition of type I (factor representations generate type I factors $\cong B(K)$; the previous wording referred to type-I von Neumann algebras being $\cong B(K)$, which is false for non-factors) and listed which standard groups are or are not type I (Glimm, Thoma).
- New entry 52 (Mackey's little-group method for regular semidirect products with abelian normal subgroup): standard classification tool (Folland §6.6, Kaniuth–Taylor).
- Extension (57, old 54): Eymard's description $A(G)=L^2*\check{L^2}$, spectrum $G$, dual $VN(G)$.
- Extension (58, old 55): amenability passes to quotients; non-amenability of groups with closed free subgroups, e.g. $SL_2(\mathbb R)$.
- Cleanup (61, old 58): external URL moved from the Leptin entry to the reference guide.
- Extension (62, old 59): Gelfand's involution criterion for Gelfand pairs, with symmetric-pair examples.
- Extension (63, old 60): Godement's spherical Plancherel theorem.

Numbering map (old → new):
19→20, 20→21, 21→22, 22→23, 23→24, 24→25, 25→26, 26→27, 27→28, 28→29, 29→30, 30→31, 31→32, 32→33, 33→34, 34→35, 35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→47, 46→48, 47→49, 48→50, 49→51, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63

### Section 29: Wavelets, Frames, Time–Frequency Analysis, and Sampling

Size: 20168 → 23388 bytes; entries: 63 → 69.

Sources consulted: Gröchenig, *Foundations of Time-Frequency Analysis* (Thm 2.2.1 Heisenberg, Thm 6.4.1 painless expansions, Thm 6.5.1 Walnut, Wexler–Raz and Zak statements); Foucart–Rauhut, *A Mathematical Introduction to Compressive Sensing* (Thm 6.12, RIP constant 4/√41); bibliography entries for Daubechies, Hernández–Weiss, Christensen (standard statements checked against these texts' known formulations).

Changes:
- Correction (old 9, frame perturbation): hypothesis said only "lower bound A" but the conclusion uses the upper bound B; now requires a frame with bounds A, B.
- Reformulation (old 5): replaced the trivial trailing sentence by the substantive characterization that the canonical coefficients are the unique solution in ran C = (ker C*)^⊥.
- New entry 16 (scaling functions from filters): infinite-product construction, support in [N1,N2], Cohen/Lawton condition, with the standard counterexample m0=(1+e^{-6πiξ})/2. Core of the Daubechies/Mallat construction, absent before.
- New entry 18 (characterization of orthonormal wavelets): Hernández–Weiss equations and the Gripenberg–Wang dimension-function criterion for MRA wavelets. Core in Hernández–Weiss.
- Reformulation (old 19 → 21, Daubechies wavelets): replaced vague "regularity tends to infinity" by support length 2N−1, filter length 2N, asymptotic regularity μN with μ≈0.21; added impossibility of C^∞ compact support and the Haar-only symmetry theorem.
- Addition to old 20 (→22): converse that smoothness plus decay of an orthonormal wavelet forces vanishing moments (Daubechies Thm 5.5.1 type).
- Addition to old 21 (→23): linear (Jackson-type) approximation estimate ‖f−P_j f‖ ≤ C2^{-jN}‖f^{(N)}‖.
- Removal of padding in old 30 (→32): dropped the trailing sentence on homogeneous expansions modulo polynomials.
- New entry 37 (uncertainty principles): Heisenberg with equality case, Benedicks, Hardy. Core time–frequency material (Gröchenig Ch. 2).
- New entries 44 (painless expansions) and 45 (frames for dense lattices: Walnut, Feichtinger–Gröchenig for S_0). Standard existence results for Gabor frames, previously missing.
- New entry 57 (Bernstein and Plancherel–Pólya inequalities): makes the upper sampling bound automatic for separated sets; standard in sampling theory.
- Correction/sharpening (old 62 → 68): replaced the "for example δ_{2s}<√2−1" condition by the Foucart–Rauhut condition δ_{2s}<4/√41≈0.62.

Numbering map (old → new):
16→17, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→46, 42→47, 43→48, 44→49, 45→50, 46→51, 47→52, 48→53, 49→54, 50→55, 51→56, 52→58, 53→59, 54→60, 55→61, 56→62, 57→63, 58→64, 59→65, 60→66, 61→67, 62→68, 63→69

### Section 30: Distributions, Pseudodifferential Operators, Microlocal and Semiclassical Analysis

Size: 21101 → 24108 bytes; entries: 62 → 65.

Sources consulted: Hörmander, *Analysis of Linear PDO* IV (Thms 26.1.1, 26.1.4, 26.1.5 on propagation and its sharpness; Section 26.3–26.4 and Definition 26.4.6 on condition (Ψ)); Hörmander III (Section 18 calculus, for conventions); bibliography entries Hörmander II (hypoellipticity), Zworski (Helffer–Sjöstrand, defect measures), Lerner (Carleman inequalities).

Changes:
- Addition to 9: Hörmander's characterization of hypoelliptic constant-coefficient operators (∂^αP/P → 0), a core result of Hörmander II.
- Correction to 10: the phase is now stated to be real (needed for both the nonstationary decay and the stationary-phase expansion).
- Reformulation of 31 (now "Gårding inequalities"): added the classical Gårding inequality for strongly elliptic operators alongside sharp Gårding.
- Addition to 36: homotopy invariance of the index of elliptic operators on closed manifolds and vanishing for self-adjoint operators.
- Addition to 38: Avakumović–Levitan–Hörmander remainder O(λ^{(d-1)/m}), sharp on spheres, and the Duistermaat–Guillemin improvement; replaces the redundant sentence on leading growth.
- Correction/reformulation of 40: the previous statement assumed principal type and described WF(u) as a union of bicharacteristics "in a region"; replaced by the Duistermaat–Hörmander formulation (WF(u)∖WF(Pu) ⊂ Char P, invariant under H_p, for real homogeneous principal symbol) plus the Sobolev version (Hörmander Thm 26.1.4).
- Replacement of 42 (former "Characteristic obstruction", an informal remark) by the sharpness theorem (Hörmander Thm 26.1.5): singularities on any compact bicharacteristic interval are realized.
- New entry 43 (local solvability): Lewy example, Nirenberg–Trèves condition (Ψ), Dencker's sufficiency, Hörmander's bracket condition. Core of microlocal theory, previously absent.
- New entry 44 (uniqueness and unique continuation): Holmgren, strong unique continuation for Lipschitz elliptic operators, Carleman estimates with pseudoconvex weights. Core; Lerner's Carleman monograph is in the bibliography.
- Trimmed padding in old 54 (→56, h-tempered definition) and replaced the vacuous trailing sentence of old 59 (→61) by the defect measure of WKB states.
- New entry 62 (functional calculus): Helffer–Sjöstrand formula and f(P_h) as a semiclassical pseudodifferential operator, a standard tool in Zworski and Dimassi–Sjöstrand.
- Reference guide: added Hörmander IV to local copies consulted.

Numbering map (old → new):
43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→63, 61→64, 62→65

### Section 31: Ordinary Differential Equations and Dynamical Systems

Size: 21315 → 23852 bytes; entries: 64 → 67.

Sources consulted: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems* (Denjoy Thm 12.1.1, Sharkovsky Thm 15.3.2, structural stability); bibliography entries Hartman, Perko, Chicone, Teschl, Kuznetsov, Arnold (standard formulations of linearization, Poincaré–Bendixson, Sturm–Liouville).

Changes:
- Reformulation of 11 (invariant regions): replaced the vague "regular boundary faces, inward-pointing or tangent" statement by the Nagumo/Bony–Brezis tangent-cone characterization, with the smooth single-inequality case.
- Correction of wording in 16: Lyapunov stability of ẋ=Ax now stated as the exact criterion (Re λ ≤ 0, imaginary-axis eigenvalues semisimple); the old phrasing was garbled.
- Addition to 21: Weyl-type eigenvalue asymptotics λ_k ∼ (kπ/L)², L=∫√(w/p).
- Addition to 24: converse Lyapunov theorem (Massera, Kurzweil).
- Addition to 28: Sternberg smooth linearization under nonresonance and Hartman's planar C¹ linearization.
- Addition to 33: Łojasiewicz convergence for analytic gradient flows.
- Reformulation of 38: replaced the padding sentence by the general Poincaré–Bendixson trichotomy (finitely many equilibria) and validity on the sphere.
- Addition to 43: Poincaré and Siegel–Brjuno convergence of analytic linearization.
- New entry 59 (structural stability): Palis–Smale for Morse–Smale fields, Peixoto on surfaces, Robbin–Robinson–Mañé characterization. Core of the hyperbolic theory in Katok–Hasselblatt and Robinson.
- New section "One-dimensional dynamics" with new entries 60 (Sharkovskii theorem) and 61 (circle homeomorphisms: rotation number, Poincaré classification, Denjoy theorem). Standard core in Katok–Hasselblatt, Robinson, Arnold; previously absent.

Numbering map (old → new):
59→62, 60→63, 61→64, 62→65, 63→66, 64→67

### Section 32: Partial Differential Equations: General and Linear Theory

Size: 20954 → 22122 bytes; entries: 66 → 66.

Sources consulted: Folland, *Introduction to Partial Differential Equations* (local PDF, searched for Perron/Holmgren/uniqueness passages); standard formulations in the bibliography texts Evans, John, Taylor I (Poisson kernel, Perron method, Tychonoff example, Schrödinger kernel, Petrowsky condition).

Changes:
- Merge: old 6 ("Analytic versus smooth well-posedness", a remark without its own content) folded into the Hadamard example (old 7 → 6).
- Reformulation of old 10 (→9): replaced the vague "explicit multipliers for elliptic spatial evolution models" by the Fourier solution of ∂_t u = a(D)u and the Petrowsky well-posedness criterion sup Re a < ∞.
- Strengthening of old 12 (→11): Hölder forcing gives C^{2,α} Newtonian potentials, with the warning that continuous forcing does not suffice (standard core fact, replaces a vague sentence).
- Addition to old 19 (→18): explicit Poisson kernel for the ball.
- New entry 23 (Perron's method and regular points): barriers, exterior cone condition, Wiener test, Lebesgue spine. Core classical potential theory, previously absent.
- Addition to 35: explicit strong maximum principle (previously only Hopf's lemma was stated).
- Addition to 40: Tychonoff's nonuniqueness example and uniqueness under Gaussian growth bounds.
- New entry 58 (free Schrödinger equation): unitary group, explicit kernel, dispersive L¹→L^∞ estimate; the basic linear Schrödinger equation was missing although it is among the model equations of the listed texts.
- Removal of old 66 ("Stability estimates as the mechanism of well-posedness"): a methodological remark rather than a theorem, redundant with the energy and duality entries.

Numbering map (old → new):
6→6 (merged into old 7), 7→6, 8→7, 9→8, 10→9, 11→10, 12→11, 13→12, 14→13, 15→14, 16→15, 17→16, 18→17, 19→18, 20→19, 21→20, 22→21, 23→22, 58→59, 59→60, 60→61, 61→62, 62→63, 63→64, 64→65, 65→66, 66→removed

### Section 33: Elliptic and Parabolic Equations: Regularity, Free Boundaries, and Viscosity Solutions

Size: 22966 → 24991 bytes; entries: 70 → 72.

Sources consulted: Velichkov, *Regularity of the One-phase Free Boundaries* (Remark 1.7 on the critical dimension: Caffarelli–Jerison–Kenig, Jerison–Savin, De Silva–Jerison); bibliography entries Gilbarg–Trudinger, Giaquinta, Caffarelli–Cabré, Figalli, Gutiérrez, Caffarelli–Salsa, Petrosyan–Shahgholian–Uraltseva (standard formulations of the added results).

Changes:
- New entry 8 (Hilbert's nineteenth problem): smoothness of scalar minimizers of uniformly convex integrals via De Giorgi–Nash. The main application of De Giorgi–Nash–Moser, recurring in Gilbarg–Trudinger, Giaquinta, Giusti; previously missing.
- Sharpening of old 9 (→10): De Giorgi's counterexample attributed, solutions can be unbounded, and the positive two-dimensional result (Morrey) added.
- Reformulation of old 10 (→11): replaced the vague closing sentence by attributions and the Nečas/Šverák–Yan singular minimizers.
- New entry 21 (symmetry and Liouville theorems): Gidas–Ni–Nirenberg moving planes, Gidas–Spruck Liouville theorem, Caffarelli–Gidas–Spruck classification. Core semilinear elliptic results, previously absent.
- Addition to old 28 (→30, Evans–Krylov): Nirenberg's two-dimensional C^{2,α} theorem and the Nadirashvili–Tkachev–Vlăduţ singular solutions showing convexity cannot be dropped in n ≥ 5.
- Addition to old 36 (→38): Pogorelov's non-strictly convex solutions for n ≥ 3 and automatic strict convexity in two dimensions.
- Addition to old 57 (→59): Weiss monotonicity gives homogeneity of blowups (needed for the classification in the next entry).
- Addition to old 66 (→68): De Silva–Jerison singular cone in dimension 7, so the critical dimension lies in {5,6,7}.
- Reformulation of old 70 (→72, now "Boundary Harnack principles"): added the local boundary Harnack principle in Lipschitz domains (Dahlberg, Kemper, Caffarelli–Fabes–Mortola–Salsa), which is core in free-boundary theory, alongside the nonlocal version.

Numbering map (old → new):
8→9, 9→10, 10→11, 11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→20, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68, 67→69, 68→70, 69→71, 70→72

### Section 34: Hyperbolic Equations, Conservation Laws, Dispersive PDE, Fluids, and Kinetic Theory

Size: 25308 → 28793 bytes; entries: 78 → 82.

Sources consulted: Dafermos, *Hyperbolic Conservation Laws in Continuum Physics* (preface/chapter plan, incl. Ch. XVII compensated compactness); Linares–Ponce, *Introduction to Nonlinear Dispersive Equations* (ToC, Ch. 4 smoothing effects); Robinson–Rodrigo–Sadowski, *The Three-Dimensional Navier–Stokes Equations* (ToC: Serrin condition, L^infty L^3 endpoint, BKM); CKMA-bib.md and CKMA-bib2.md Section 34 entries (Saint-Raymond, Bressan, Tao, Cazenave).

Changes:
- 4 (scalar breakdown): reformulated with explicit hypotheses ($f\in C^2$, $u_0\in C^1$ with bounded derivative) and the exact lifespan $T^*=-1/\inf\partial_\xi f'(u_0)$, plus global existence when the infimum is nonnegative; previous wording ("at the reciprocal of the negative minimum") was imprecise (min need not be attained, sign of reciprocal).
- 14 (Hopf–Lax): replaced "solves ... almost everywhere" by the correct statement that $v_x$ is the entropy solution with data $v_0'$ (Lax–Oleinik).
- 20 (standard Riemann semigroup): replaced vague uniqueness sentence by Bressan's uniqueness of the semigroup and the Bressan–Goatin / Bressan–LeFloch uniqueness of small-BV entropy solutions under tame oscillation/variation conditions.
- New 22 (compensated compactness: div–curl lemma, Tartar's Young-measure reduction, DiPerna's isentropic gas dynamics): core $L^\infty$ method treated in Dafermos and Serre, previously absent.
- 25 (old 24, retarded Strichartz): correction. The restriction "both time exponents strictly greater than two" was unnecessary; Keel–Tao prove the inhomogeneous estimate for all admissible pairs including endpoints; Christ–Kiselev route noted.
- New 26 (local smoothing / Kato smoothing for Schrödinger and Airy): core dispersive estimate (Linares–Ponce Ch. 4, Kenig–Ponce–Vega), basis of KdV-type well-posedness.
- 33 (old 31): added sharpness of the mass-critical threshold via the pseudo-conformal blowup solution of mass $\|Q\|_2$.
- New 34 (Morawetz estimate and intercritical defocusing $H^1$ scattering, Lin–Strauss, Ginibre–Velo): standard global theory result, previously absent.
- 39 (old 36, null condition): attributed (Klainerman, Christodoulou) and added the contrast: John's blowup for $\square u=u_t^2$ and almost global existence for general quadratic nonlinearities.
- 41 (old 38, KdV solitons): replaced padded sentence ("amplitude and speed are linked") with orbital stability (Benjamin, Bona, Weinstein).
- 57 (old 54, Prodi–Serrin): added the Escauriaza–Seregin–Šverák endpoint $L^\infty_tL^3_x$.
- 63 (old 60, renormalized continuity equation): tightened the definition of renormalized solutions.
- New 76 (Golse–Saint-Raymond incompressible Navier–Stokes–Fourier limit of the Boltzmann equation): central theorem of the listed hydrodynamic-limit monograph (Saint-Raymond), previously absent.
- 78 (old 74, energy equality): attributed to Constantin–E–Titi and added the converse (Isett; Buckmaster–De Lellis–Székelyhidi–Vicol) settling Onsager's conjecture.
- Reference guide: noted compensated compactness in Dafermos/Serre; added the local copy of Robinson–Rodrigo–Sadowski.

Numbering map (old → new):
22→23, 23→24, 24→25, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→35, 33→36, 34→37, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→47, 45→48, 46→49, 47→50, 48→51, 49→52, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63, 61→64, 62→65, 63→66, 64→67, 65→68, 66→69, 67→70, 68→71, 69→72, 70→73, 71→74, 72→75, 73→77, 74→78, 75→79, 76→80, 77→81, 78→82 (new entries: 22, 26, 34, 76; 1–21 unchanged)

### Section 35: Nonlinear Functional Analysis, Monotone Operators, and Fixed Points

Size: 18575 → 21121 bytes; entries: 60 → 64.

Sources consulted: Kielhöfer, *Bifurcation Theory* (ToC; Section I.21, Theorem I.21.2 and counterexample I.21.36; Section I.8 Hopf bifurcation); Granas–Dugundji, Zeidler, Brezis, Barbu (as listed in the existing reference guide, for standard formulations); CKMA-bib.md and CKMA-bib2.md Section 35.

Changes:
- New 8 (Sard–Smale theorem): basic genericity result for nonlinear Fredholm maps, recurring in Zeidler/Deimling-type texts; previously absent.
- 9 (old 8, Newton–Kantorovich): allowed the standard borderline $L\eta\leq1/2$, added localization of iterates and uniqueness; removed padded remark on the degenerate case $L=0$.
- 10 (old 9, Nemytskii): replaced filler sentence with Krasnosel'skii's converse (mapping $L^p\to L^q$ forces continuity, boundedness, and the growth bound).
- 12 (old 11, Brouwer): added the equivalent acute-angle lemma used for Galerkin approximations.
- New 20 (monotone iteration in ordered Banach spaces, Amann): core order-theoretic fixed-point principle behind sub/supersolution methods; previously absent.
- New 31 (Krasnosel'skii cone compression–expansion theorem): standard fixed-point index result for positive solutions; previously absent.
- 36 (old 33): added convexity of $\overline{D(A)}$ for maximal monotone $A$.
- 40 (old 37, Browder–Minty): removed the unnecessary hypothesis "bounded on bounded sets".
- 41 (old 38, strong monotonicity): removed the vague and unnecessary reference to "preceding local boundedness hypotheses" (Zarantonello: hemicontinuous strongly monotone maps on $H$ are bijective with $1/m$-Lipschitz inverse).
- 52 (old 49, energy dissipation): replaced the hedged hypothesis and filler with Brezis's regularizing effect for subgradient flows ($u(t)\in D(\partial\phi)$ for $t>0$, $\phi(u(t))\leq\phi(v)+\|u_0-v\|^2/(2t)$, $u'\in L^2$ for $u_0\in D(\phi)$).
- Removed old 56 (projection and obstacle interpretation): a restatement of the sum rule and normal-cone formulation (already in old 43), not a principal result.
- New 63 (bifurcation for potential operators, Böhme–Marino; Kielhöfer Thm I.21.2): every isolated finite-multiplicity eigenvalue is a bifurcation point for gradient problems, with the non-gradient counterexample.
- New 64 (Hopf bifurcation): central local bifurcation theorem (Kielhöfer I.8), previously absent.
- Reference guide: noted Hopf and variational bifurcation in the bifurcation texts.

Numbering map (old → new):
8→9, 9→10, 10→11, 11→12, 12→13, 13→14, 14→15, 15→16, 16→17, 17→18, 18→19, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→32, 30→33, 31→34, 32→35, 33→36, 34→37, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→47, 45→48, 46→49, 47→50, 48→51, 49→52, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→removed, 57→59, 58→60, 59→61, 60→62 (new entries: 8, 20, 31, 63, 64; 1–7 unchanged)

### Section 36: Calculus of Variations, Γ-Convergence, and Homogenization

Size: 21395 → 23199 bytes; entries: 64 → 65.

Sources consulted: Dacorogna, *Direct Methods in the Calculus of Variations* (ToC: regularity sections, Šverák's example, rank-one convexity); Struwe, *Variational Methods* (ToC: Ch. III, limit cases of Palais–Smale, Brezis–Nirenberg result); CKMA-bib.md and CKMA-bib2.md Section 36 (Giaquinta–Hildebrandt, Giusti, Jikov–Kozlov–Oleinik, Braides, Dal Maso).

Changes:
- 7 (Jacobi condition): replaced vague trailing sentence with the classical sufficiency theorem (strengthened Legendre plus no conjugate point in the closed interval gives a strict weak minimum; Weierstrass field theory with nonnegative excess gives a strong minimum).
- 12 (merged old 12 and 13): old 12 required "standard $p$-growth" and old 13 "suitable $p$-growth", both unnecessary for nonnegative integrands; replaced by the De Giorgi–Ioffe lower semicontinuity theorem ($f\geq0$, lsc in $(u,F)$, convex in $F$; strong $L^1$ convergence of $u_j$, weak $L^1$ of $Du_j$), which subsumes both.
- New 15 (regularity of minimizers): scalar $C^\infty$ regularity via De Giorgi–Nash–Moser (Hilbert's 19th problem), vectorial counterexamples (De Giorgi, Šverák–Yan), partial regularity for quasiconvex integrands (Evans, Acerbi–Fusco); core material of Giaquinta/Giusti, previously absent.
- 16 (convexity hierarchy): correction/precision. "The reverse implications fail in general vectorial dimensions" was imprecise; now states coincidence for $m=1$ or $d=1$, Šverák's counterexample (rank-one convex not quasiconvex) for $m\geq3$, and that $m=2$ is open.
- 17 (Morrey): added Acerbi–Fusco attribution and the $(x,u)$-dependent version.
- 21 (quasiconvex relaxation): replaced "two-sided coercive $p$-growth" by the actual hypothesis $0\leq f\leq C(1+|F|^p)$ (coercivity not needed).
- 33 (Ekeland): restated precisely with the parameters $\varepsilon,\lambda$; the previous formulation was ambiguous about which point satisfies the inequality and omitted $I(u)\leq I(u_0)$ and the distance bound.
- New 42 (critical exponent, Palais–Smale below $S^{d/2}/d$, Brezis–Nirenberg existence for $d\geq4$ and the $d=3$ restriction): standard limit case of critical-point theory (Struwe Ch. III), previously absent.
- 44 (old 43, fundamental theorem of Γ-convergence): reformulated; the previous text had a confusing clause about existence of minimizers depending on lower semicontinuity of the $F_j$ (the Γ-limit is automatically lsc and attains its minimum under equicoercivity).
- 57 (old 56, corrector convergence): replaced vague sentence on boundary-corrected expansions by the standard rates $O(\varepsilon^{1/2})$ in $H^1$ (boundary layer) and $O(\varepsilon)$ in $L^2$.
- Reference guide: noted regularity in Giaquinta–Hildebrandt and Giusti, and Struwe's treatment of the limit cases of Palais–Smale.

Numbering map (old → new):
13→12 (merged), 14→13, 15→14, 42→43, 43→44, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→53, 53→54, 54→55, 55→56, 56→57, 57→58, 58→59, 59→60, 60→61, 61→62, 62→63, 63→64, 64→65 (new entries: 15, 42; 1–12 and 16–41 unchanged)

### Section 37: Geometric Measure Theory, BV, Rectifiability, and Currents

Size: 20644 → 22861 bytes; entries: 66 → 69.

Sources consulted: Tolsa, *Analytic Capacity, the Cauchy Transform, and Non-homogeneous Calderón–Zygmund Theory* (ToC: curvature of measures, semiadditivity of γ and γ+); Mattila, *Rectifiability: A Survey* (local copy, as in existing guide); Simon's author-posted GMT notes (Allard's theorem hypotheses, as in existing guide); CKMA-bib.md and CKMA-bib2.md Section 37 (Falconer, Mattila, Giusti, Ambrosio–Fusco–Pallara, David–Semmes).

Changes:
- 7 (density bounds): replaced "positive and finite" by the precise bounds: upper density in $[2^{-k},1]$ $\mathcal H^k$-a.e. on $E$, zero a.e. off $E$.
- New 9 (self-similar sets; Hausdorff ≤ box dimensions; Moran–Hutchinson formula under the open set condition): the introduction announces fractal dimension as a foundation but no dimension computation was stated.
- 10 (old 9, Rademacher): replaced filler sentence with the Lusin-type $C^1$ approximation of Lipschitz maps.
- New 11 (Lipschitz extension: McShane, Kirszbraun): basic GMT tool (Federer 2.10), previously absent.
- 29 (old 27, BV chain rule): trimmed a padded sentence on the normalization $F(0)=0$.
- 31 (old 29, BV Sobolev): added the sharp constant and its equivalence with the isoperimetric inequality.
- 35 (old 33, Mumford–Shah): added De Giorgi–Carriero–Leaci closure of the jump set, linking the SBV problem to the original formulation with closed discontinuity sets.
- 45 (old 43, regularity of minimizing boundaries): added sharpness (Simons cone, Bombieri–De Giorgi–Giusti) and the Bernstein theorem for entire minimal graphs ($n\leq7$).
- 62 (old 60, Allard regularity): correction. "Sufficiently small tilt excess" is not a hypothesis of Allard's theorem; restated with the actual hypotheses ($\Theta\geq1$, mass ratio $\leq1+\delta$, small scaled $L^p$ mean curvature, $p>m$).
- 63 (old 61, Michael–Simon): trimmed trailing sentence to the precise varifold extension.
- 64 (old 62): replaced the near-vacuous "big pieces and rectifiability" entry by the David–Semmes singular-integral characterization of uniform rectifiability and the Nazarov–Tolsa–Volberg (Riesz transform) and Mattila–Melnikov–Verdera (Cauchy transform) theorems; the old content (uniform implies countable rectifiability) is kept as its first sentence.
- New 68 (Tolsa's theorem: analytic capacity comparable to curvature capacity, semiadditivity): central theorem of the listed Tolsa monograph, previously absent.
- Reference guide: noted Falconer and Mattila for self-similar sets.

Numbering map (old → new):
9→10, 10→12, 11→13, 12→14, 13→15, 14→16, 15→17, 16→18, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64 (content replaced: singular-integral characterization), 63→65, 64→66, 65→67, 66→69 (new entries: 9, 11, 68; 1–8 unchanged)

### Section 38: Potential Theory and Capacity

Size: 20939 → 22616 bytes; entries: 64 → 67.

Sources consulted: local texts listed in the existing reference guide (Helms, Armitage–Gardiner, Axler–Bourdon–Ramey, Doob, Tolsa) for standard formulations; CKMA-bib.md and CKMA-bib2.md Section 38 (Landkof, Heinonen–Kilpeläinen–Martio, Adams–Hedberg, Ransford, Capogna–Kenig–Lanzani on harmonic measure).

Changes:
- 1 (mean values): added Weyl's lemma (harmonic distributions are harmonic functions).
- New 3 (Fatou's theorem, with the Hunt–Wheeden extension to Lipschitz domains): core boundary-behaviour theorem for harmonic functions, previously absent.
- 4 (old 3, Harnack): added Liouville's theorem for harmonic functions bounded on one side.
- 5 (old 4, Harnack convergence): correction. Removed the spurious hypothesis "assuming a common lower harmonic bound"; for an increasing sequence the first term is already a lower bound and the dichotomy holds without extra assumptions.
- New 15 (Evans–Vasilesco continuity principle): standard classical potential-theory principle (Landkof, Helms, Armitage–Gardiner), previously absent.
- 30 (old 28, Wiener's criterion): added the equivalence of regularity with non-thinness of the complement, linking the criterion to the fine topology of entry 24.
- New 36 (planar harmonic measure: F. and M. Riesz theorem, Makarov's theorem, Jones–Wolff): core planar harmonic-measure results, complementing Dahlberg's theorem; previously absent.
- 47 (old 44, nonlinear Wiener criterion): added attribution (Maz'ya sufficiency, Kilpeläinen–Malý necessity).
- 51 (old 48, dimension thresholds): replaced the vague closing sentence by the sharp Hausdorff-measure statements ($\mathcal H^{n-p}(E)<\infty$ implies zero $p$-capacity; zero capacity implies $\mathcal H^s(E)=0$ for $s>n-p$), covering the Newtonian case $p=2$.

Numbering map (old → new):
3→4, 4→5, 5→6, 6→7, 7→8, 8→9, 9→10, 10→11, 11→12, 12→13, 13→14, 14→16, 15→17, 16→18, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→37, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→47, 45→48, 46→49, 47→50, 48→51, 49→52, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63, 61→64, 62→65, 63→66, 64→67 (new entries: 3, 15, 36; 1–2 unchanged)

### Section 39: Metric Measure Spaces, Dirichlet Forms, Heat Kernels, Optimal Transport, and Fractals

Size: 25507 → 28990 bytes; entries: 74 → 80.

Sources consulted: Heinonen, Lectures on Analysis on Metric Spaces (local PDF; Theorems 9.6–9.10 on Loewner spaces and Poincaré inequalities, Ch. 11–12); Villani, Optimal Transport: Old and New (local PDF; Theorem 5.10 for duality and cyclical monotonicity); CKMA-bib.md and CKMA-bib2.md Section 39 (scope: Gromov–Hausdorff convergence via Ambrosio–Tilli, Burago–Burago–Ivanov, Gromov; Assouad and conformal dimension via Fraser, Mackay–Tyson).

Changes:
- New heading "Embeddings, quasisymmetry, and Gromov–Hausdorff convergence", with definitions of quasisymmetry, Loewner spaces, and Gromov–Hausdorff distance.
- New entry 15 (Assouad embedding): a basic theorem of metric analysis (Heinonen Ch. 12); the bibliography lists Assouad dimension.
- New entry 16 (Loewner spaces and quasisymmetry): the Heinonen–Koskela theorem (Loewner if and only if (1,Q)-Poincaré) is central in Heinonen and was missing.
- New entry 17 (Gromov precompactness): Gromov–Hausdorff convergence is explicitly in scope (Ambrosio–Tilli, BBI, Gromov) and was missing entirely.
- Old 22 (now 25): added Grigor'yan's volume test for stochastic completeness.
- Old 23 (now 26), correction: the recurrence criterion does not need irreducibility; added the transience characterization (the extended Dirichlet space is Hilbert) and the recurrent/transient dichotomy for irreducible forms; dropped the vague Green-operator sentence.
- Old 29 (now 32), strengthened: stated the full Grigor'yan–Saloff-Coste–Sturm equivalence (doubling plus Poincaré, parabolic Harnack, two-sided Gaussian bounds); made the Harnack constant explicit.
- New entry 38 (Gross hypercontractivity): the equivalence of log-Sobolev and hypercontractivity is core in Bakry–Gentil–Ledoux.
- Old 37 (now 41), correction/strengthening: under Villani Thm 5.10 hypotheses (real-valued lsc cost, finite optimal cost), c-cyclical monotonicity is necessary and sufficient for optimality in general; the old text suggested the converse only for quadratic cost.
- New entry 54 (transport–entropy inequalities: Otto–Villani, Talagrand): core in Villani and Bakry–Gentil–Ledoux.
- New entry 55 (Lott–Sturm–Villani CD(K,N)): stability under measured GH convergence, Bishop–Gromov, Brunn–Minkowski, Bonnet–Myers, Bakry–Émery N-Ricci equivalence; only CD(K,∞) was mentioned before.
- Old 8 (now 8): removed the vague trailing sentence about compactly supported approximation.
- Old 59 (now 65): removed a padding clause about the extension by closure.
- Reference guide: added pointers for Assouad, Loewner, and Gromov–Hausdorff material.

Numbering map (old → new):
15→18, 16→19, 17→20, 18→21, 19→22, 20→23, 21→24, 22→25, 23→26, 24→27, 25→28, 26→29, 27→30, 28→31, 29→32, 30→33, 31→34, 32→35, 33→36, 34→37, 35→39, 36→40, 37→41, 38→42, 39→43, 40→44, 41→45, 42→46, 43→47, 44→48, 45→49, 46→50, 47→51, 48→52, 49→53, 50→56, 51→57, 52→58, 53→59, 54→60, 55→61, 56→62, 57→63, 58→64, 59→65, 60→66, 61→67, 62→68, 63→69, 64→70, 65→71, 66→72, 67→73, 68→74, 69→75, 70→76, 71→77, 72→78, 73→79, 74→80 (new entries: 15, 16, 17, 38, 54, 55)

### Section 40: One Complex Variable: Graduate Courses

Size: 20616 → 22393 bytes; entries: 74 → 78.

Sources consulted: Conway, Functions of One Complex Variable I (local PDF; Ch. X on the Dirichlet problem and Perron method); CKMA-bib.md and CKMA-bib2.md Section 40 (Ahlfors, Conway, Rudin, Stein–Shakarchi, Lang, Freitag–Busam, and others for the recurring core).

Changes:
- Old 18 (Minimum modulus), correction: the old wording ("cannot have an interior strict positive minimum") was weaker than the standard statement and awkward; it now says a zero-free holomorphic function whose modulus has a local minimum is constant, and gives the boundary-minimum consequence.
- Old 37 (Jensen's formula), correction: the hypothesis "no zeros on $|z|=r$" is unnecessary; it is removed and the reason is given.
- New entry 47 (Perron method and regular boundary points): the Dirichlet problem on general domains is a standard part of Ahlfors and Conway and was missing; only Jordan domains were covered.
- New entry 52 (Characterizations of simple connectivity): the standard equivalence theorem (Conway VIII.2.2, Rudin 13.11) ties together the separate statements in old 4, 21, 38, and 50.
- New entry 54 (Finite Blaschke products and proper self-maps of the disk): this recurs in Conway, Gamelin, and Rudin.
- New entry 77 (Weierstrass ℘-function, differential equation, and the field of elliptic functions): this recurs in Ahlfors, Stein–Shakarchi, Lang, and Freitag–Busam; only the residue constraint was stated before.
- Old 74 (now 78): added the Cauchy–Pompeiu formula, the source of the ∂̄-solution, in place of a descriptive trailing sentence.
- Old 64 and old 67 (now 67 and 70): removed padding sentences.

Numbering map (old → new):
47→48, 48→49, 49→50, 50→51, 51→53, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61, 59→62, 60→63, 61→64, 62→65, 63→66, 64→67, 65→68, 66→69, 67→70, 68→71, 69→72, 70→73, 71→74, 72→75, 73→76, 74→78 (new entries: 47, 52, 54, 77)

### Section 41: Classical Function Theory: Entire and Meromorphic Functions, Value Distribution

Size: 19550 → 21340 bytes; entries: 64 → 69.

Sources consulted: Gonchar–Havin–Nikolski (eds.), Complex Analysis I (local supplementary PDF; the Gol'dberg–Levin–Ostrovskii survey for the Denjoy–Carleman–Ahlfors theorem and asymptotic values); CKMA-bib.md and CKMA-bib2.md Section 41 (Boas, Levin, Hayman, Nevanlinna, Gol'dberg–Ostrovskii, Laine, Koosis) for the recurring core.

Changes:
- New entry 13 (Lindelöf's theorem on finite type and zero distribution at integer order): standard in Boas and Levin.
- New entry 16 (the cos πρ minimum-modulus theorem, including Wiman's case ρ<1/2): standard in Hayman, Levin, and Boas; it was missing.
- Old 17 (now 19), strengthened: the old entry only said that the indicator is the support function of some convex set. It is replaced by Pólya's theorem identifying the indicator diagram with the conjugate convex hull of the Borel transform's singularities, together with the Pólya representation.
- New entry 20 (Denjoy–Carleman–Ahlfors bound on asymptotic values): a classical core theorem of value distribution (Nevanlinna, Gol'dberg–Ostrovskii).
- New entry 47 (Hayman's alternative and the $f^nf'$ result): a central theorem in Hayman's book.
- Old 52 (now 56), reformulation: replaced the "convenient global form" with the actual Carlson theorem (half-plane, exponential type, type less than π on the imaginary axis), with the sharpness example.
- Old 53 (now 57): added Fabry's gap theorem and removed a padding sentence.
- New entry 62 (Clunie's lemma): the basic tool in Laine's treatment of complex differential equations.
- Reference guide: noted that asymptotic values were compared with the Gonchar–Havin–Nikolski survey.

Numbering map (old → new):
13→14, 14→15, 15→17, 16→18, 17→19, 18→21, 19→22, 20→23, 21→24, 22→25, 23→26, 24→27, 25→28, 26→29, 27→30, 28→31, 29→32, 30→33, 31→34, 32→35, 33→36, 34→37, 35→38, 36→39, 37→40, 38→41, 39→42, 40→43, 41→44, 42→45, 43→46, 44→48, 45→49, 46→50, 47→51, 48→52, 49→53, 50→54, 51→55, 52→56, 53→57, 54→58, 55→59, 56→60, 57→61, 58→63, 59→64, 60→65, 61→66, 62→67, 63→68, 64→69 (new entries: 13, 16, 20, 47, 62)

### Section 42: Hardy, Bergman, and Model Spaces; Operators on Analytic Function Spaces

Size: 22216 → 24025 bytes; entries: 78 → 83.

Sources consulted: CKMA-bib.md and CKMA-bib2.md Section 42 (Garnett, Duren, Koosis, Nikolski, Böttcher–Silbermann, Garcia–Mashreghi–Ross, Hedenmalm–Korenblum–Zhu, Cowen–MacCluer, Zhu); the local copies listed in the existing reference guide (Garnett, Nikolski, El-Fallah–Kellay–Mashreghi–Ransford) were used to check normalizations (Dirichlet kernel, Douglas formula, Bergman kernel, Hankel Hilbert–Schmidt norm) and statement forms. No new local PDFs were added.

Changes:
- Old 2: the point-evaluation bound now has the sharp constant, $|f(z)|\leq(1-|z|^2)^{-1/p}\|f\|_p$.
- New entry 3 (Hardy convexity of integral means; Hardy–Littlewood nontangential maximal theorem): basic $H^p$ tools in Duren and Garnett that were missing.
- New entry 8 (Frostman's theorem; density of Blaschke products among inner functions): standard in Garnett and Nikolski.
- Old 25 (Corona, now 27), correction: the claim that the bounds depend "only on the stated data" was incomplete without a normalization of $\|f_j\|_\infty$. Added $\|f_j\|_\infty\leq1$, the dependence on $n$ and δ, and the maximal-ideal-space formulation.
- New entry 33 (Toeplitz spectra: continuous symbols, Hartman–Wintner, Widom connectedness): core Toeplitz theory (Böttcher–Silbermann, Nikolski), beyond the Fredholm index entry.
- New entry 34 (Szegő's first and strong limit theorems for Toeplitz determinants): central in Böttcher–Silbermann and in the Toeplitz literature.
- New entry 45 (Sarason's commutant theorem for compressed shifts): the basic operator-theoretic interpolation theorem for model spaces (Garcia–Mashreghi–Ross, Nikolski).
- Old 60 and old 63 (now 65 and 68): removed or condensed padding sentences.

Numbering map (old → new):
3→4, 4→5, 5→6, 6→7, 7→9, 8→10, 9→11, 10→12, 11→13, 12→14, 13→15, 14→16, 15→17, 16→18, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→35, 32→36, 33→37, 34→38, 35→39, 36→40, 37→41, 38→42, 39→43, 40→44, 41→46, 42→47, 43→48, 44→49, 45→50, 46→51, 47→52, 48→53, 49→54, 50→55, 51→56, 52→57, 53→58, 54→59, 55→60, 56→61, 57→62, 58→63, 59→64, 60→65, 61→66, 62→67, 63→68, 64→69, 65→70, 66→71, 67→72, 68→73, 69→74, 70→75, 71→76, 72→77, 73→78, 74→79, 75→80, 76→81, 77→82, 78→83 (new entries: 3, 8, 33, 34, 45)

### Section 43: Univalent Functions, Conformal Mapping, and Extremal Methods

Size: 19151 → 21017 bytes; entries: 68 → 72.

Sources consulted: Pommerenke, Boundary Behaviour of Conformal Maps (local PDF; Theorem 1.11 for Becker's criterion, §11.4 for the Ahlfors distortion theorem); CKMA-bib.md and CKMA-bib2.md Section 43 (Duren, Pommerenke, Goluzin, Nehari, Ahlfors's Conformal Invariants, Garnett–Marshall) for the recurring core.

Changes:
- Old 22 (radial embedding): added Loewner's density of slit maps in $\mathcal S$, the reduction behind Loewner's method.
- New entry 32 (Becker's univalence criterion): the standard pre-Schwarzian counterpart to Nehari's criterion (Pommerenke).
- Old 32 (Grunsky, now 33), correction of an imprecise claim: the bilinear (weak) Grunsky inequalities do not by themselves "contain" the area theorem. The entry now states the strong (contraction) form for univalent maps, whose first row gives the area theorem.
- New entry 42 (Grötzsch and Teichmüller extremal rings, with the bound $\log(4/r)$): basic extremal-length results in Ahlfors's Conformal Invariants and Lehto–Virtanen.
- Old 41 (now 43): added the Fekete–Szegő identification of capacity, transfinite diameter, and Chebyshev constant.
- Old 42 and old 43 (now 44 and 45): removed padding clauses.
- New entry 47 (Ahlfors distortion theorem and harmonic-measure decay in strips): central in Ahlfors, Garnett–Marshall, and Pommerenke.
- New entry 62 (Koebe circle domains and parallel-slit maps, with the extremal property): conformal mapping of multiply connected domains was missing (Goluzin, Nehari). The heading is renamed "Multiply connected domains and explicit polygonal mapping".
- Reference guide: added a pointer to Goluzin and Nehari for canonical domains.

Numbering map (old → new):
32→33, 33→34, 34→35, 35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→43, 42→44, 43→45, 44→46, 45→48, 46→49, 47→50, 48→51, 49→52, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→60, 58→61, 59→63, 60→64, 61→65, 62→66, 63→67, 64→68, 65→69, 66→70, 67→71, 68→72 (new entries: 32, 42, 47, 62)

### Section 44: Riemann Surfaces, Quasiconformal Mappings, and Teichmüller Theory

Size: 22077 → 24043 bytes; entries: 76 → 77.

Sources consulted: Hencl–Koskela, *Lectures on Mappings of Finite Distortion* (References/HenclKoskela2014MappingsFiniteDistortion-Springer.LNM2096.pdf; Theorems 2.3, 2.4, 3.4, 3.5 and Examples 3.3ff); bibliography entries of Section 44 in CKMA-bib.md and CKMA-bib2.md (Ahlfors, Lehto–Virtanen, Imayoshi–Taniguchi, Gardiner–Lakic, Farb–Margalit) for standard statements.

Changes:
- Uniformization (7): replaced the loose "quotients by freely acting deck groups" by the precise statement (free, properly discontinuous automorphism groups) and added the classification of exceptional surfaces (only the sphere covered by the sphere; only C, C*, tori covered by C; all others hyperbolic).
- Removal: old 19 (genus-zero classification) was redundant with 8 and 16; its content folded into 16 as one sentence.
- Weierstrass gap theorem (now 21): added the weighted count g^3-g of Weierstrass points and the bounds 2g+2 ≤ #W ≤ g^3-g, with equality in the lower bound exactly for hyperelliptic surfaces (core recurring fact in Farkas–Kra, Miranda).
- Hodge theorem (now 24): corrected the confusing phrase "real parts of holomorphic differentials and their conjugate partners"; now states that real harmonic 1-forms are exactly Re of holomorphic 1-forms and gives the Hodge decomposition H^1(X,C)=H^0(K)⊕conj H^0(K).
- Parameter dependence (now 43): removed padded trailing sentence; attributed to Ahlfors–Bers and stated pointwise holomorphy precisely.
- Mori distortion (now 44): replaced unspecified C(K) by the standard constant 16 (independent of K).
- Quasisymmetric boundary maps (now 45): named Beurling–Ahlfors and added the Douady–Earle conformally natural extension (standard tool in Teichmüller theory).
- Finite distortion (old 52, now 51, retitled "Mappings of finite distortion"): replaced the vague negative statement by the standard positive theorems from Hencl–Koskela: continuity for W^{1,n} maps of finite distortion; openness/discreteness when K ∈ L^p, p>n-1 (p≥1 in the plane), or exp(λK) ∈ L^1; sharpness via Lipschitz examples with K ∈ L^p for p<n-1.
- Bers embedding (now 60): added the Ahlfors–Weill/Nehari–Kraus inclusions (ball of radius 2 inside, ball of radius 6 outside, in the disk norm sup (1-|z|^2)^2|q|).
- New entry 61 (universal Teichmüller space T(1)): central object in Lehto, Gardiner–Lakic, Imayoshi–Taniguchi; quasisymmetric model, Bers embedding, containment of T_g.
- New entry 67 (Royden's theorem): Teichmüller = Kobayashi metric, biholomorphisms come from mapping classes; standard in Hubbard, Gardiner–Lakic, Imayoshi–Taniguchi.
- New entry 69 (Dehn–Lickorish theorem): Dehn twist generation (Lickorish 3g-1, Humphries 2g+1), finite presentation, surjection onto Sp(2g,Z); core of Farb–Margalit.
- Merge: old 76 (hyperbolic pants rigidity) folded into Fenchel–Nielsen coordinates (now 62) as one sentence, removing redundancy.

Numbering map (old → new):
19→16 (merged), 20→19, 21→20, 22→21, 23→22, 24→23, 25→24, 26→25, 27→26, 28→27, 29→28, 30→29, 31→30, 32→31, 33→32, 34→33, 35→34, 36→35, 37→36, 38→37, 39→38, 40→39, 41→40, 42→41, 43→42, 44→43, 45→44, 46→45, 47→46, 48→47, 49→48, 50→49, 51→50, 52→51, 53→52, 54→53, 55→54, 56→55, 57→56, 58→57, 59→58, 60→59, 61→60, 67→68, 68→70, 69→71, 70→72, 71→73, 72→74, 73→75, 74→76, 75→77, 76→62 (merged). New entries: 61, 67, 69. Old 1–18 and 62–66 unchanged.

### Section 45: Several Complex Variables, Complex Manifolds, Pluripotential Theory, and CR Analysis

Size: 23875 → 25388 bytes; entries: 80 → 82.

Sources consulted: Ohsawa, *L² Approaches in Several Complex Variables*, 2nd ed. (References/Ohsawa2018L2ApproachesSeveralComplexVariables2ndEd-Springer.SMM.pdf; Theorem 3.26, Błocki's optimal Ohsawa–Takegoshi constant); Forstnerič, *Stein Manifolds and Holomorphic Mappings*, 2nd ed. (References/Forstnerič2017SteinManifoldsHolomorphicMappingsHomotopyPrincipleComplexAnalysis2ndEd-SpringerErgebMath3.pdf; Theorem 9.3.1 on optimal embedding dimension); bibliography entries of Section 45 in CKMA-bib.md and CKMA-bib2.md (Klimek, Demailly, Straube, Huybrechts, Krantz) for standard statements.

Changes:
- Stein embedding (28): replaced the padded sentence "Stronger dimension bounds are available but are not needed" by the actual optimal result: proper embedding into C^{⌊3n/2⌋+1} for n≥2 (Eliashberg–Gromov, Schürmann), and C^3 for open Riemann surfaces (Bishop–Narasimhan).
- Finite type (40): removed padded trailing sentence; attributed to Catlin.
- New entry 41 (Global regularity and Condition R): Bell–Ligocka smooth extension of biholomorphisms, Boas–Straube for convex domains, Kohn–Nirenberg compactness ⇒ regularity, Barrett/Christ worm-domain counterexamples; central to the d-bar-Neumann literature (Straube, Chen–Shaw, Haslinger).
- Ohsawa–Takegoshi (now 42): replaced the vague "C depends on a bound for the transverse coordinate" by the sharp constant C = πr^2 when |z_n|<r on Ω (Błocki, Guan–Zhou).
- Kołodziej attribution added to the L^p Monge–Ampère statement (now 56).
- New entry 57 (Pluripolar sets): Josefson's theorem, capacity characterization, Bedford–Taylor negligible sets; core in Klimek and Guedj–Zeriahi and previously absent.
- Calabi–Yau (now 58): added the Aubin–Yau Kähler–Einstein theorem for c_1<0 and Ricci-flat metrics for c_1=0.
- Merge: old 67 (holomorphic maps to projective space; a definition-level statement with a padded closing sentence) folded into Kodaira embedding (now 68) as one sentence.
- New entry 69 (Chow's theorem and GAGA): core link between compact complex geometry and algebraic geometry, recurring in Huybrechts, Wells, Griffiths–Harris.
- Bergman transformation (now 74): added the explicit Bergman kernel of the ball.
- Cartan uniqueness (now 75): replaced the garbled second sentence by the standard statement (origin-preserving biholomorphisms between bounded circular domains are linear) and added Poincaré's inequivalence of ball and polydisk for n≥2.

Numbering map (old → new):
41→42, 42→43, 43→44, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→53, 53→54, 54→55, 55→56, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68, 67→68 (merged), 68→70, 69→71, 70→72, 71→73, 72→74, 73→75, 74→76, 75→77, 76→78, 77→79, 78→80, 79→81, 80→82. New entries: 41, 57, 69. Old 1–40 unchanged.

### Section 46: Complex Dynamics

Size: 19505 → 20350 bytes; entries: 68 → 68.

Sources consulted: McMullen, *Complex Dynamics and Renormalization* (References/McMullen1995ComplexDynamicsRenormalization-PrincetonAnnalsMathStud135.pdf; Ch. 7–8 on renormalization and the Yoccoz–Lyubich–Shishikura results); bibliography entries of Section 46 in CKMA-bib.md and CKMA-bib2.md (Milnor, Carleson–Gamelin, Bedford–Smillie and the CIME volume) for standard statements.

Changes:
- Holomorphic fixed-point formula (9): moved the inline Milnor lecture link out of the theorem statement into the reference guide.
- Blowing-up property (5): trimmed padded trailing sentence to a parenthetical attribution to Montel.
- No wandering domains (20): added Fatou's count of Fatou components (0, 1, 2, or ∞), a standard core fact.
- Hyperbolicity criteria (23): grammatical rewording; now also serves as the definition of hyperbolic maps.
- Subhyperbolic local connectivity (27): reformulated with an explicit definition of subhyperbolicity (the former wording mixed a redundant "no parabolic cycles" hypothesis with a conditional clause); noted hyperbolic and postcritically finite special cases.
- Escape of all critical points (30): replaced the padded disclaimer by the standard conclusion (p on J is conjugate to the one-sided d-shift) and the quadratic connected/Cantor dichotomy.
- Merge: old 46 (renormalization; vague "control the applicability" phrasing) merged into hybrid straightening (45), with the precise definition and the small copies of M.
- New entry 46 (Yoccoz and Shishikura theorems): Yoccoz local connectivity for finitely renormalizable maps without indifferent cycles, dim ∂M = 2, MLC ⇒ density of hyperbolicity, real density (Lyubich, Graczyk–Świątek); core results of the quadratic family treated in McMullen, Milnor, Carleson–Gamelin.
- Transcendental Julia theory (57): replaced padded sentence by the fact that J(f) is unbounded.
- Eremenko escaping theorem (58): replaced the negative disclaimer by the positive results of Rippon–Stallard (unbounded component of I(f)) and Rottenfusser–Rückert–Rempe–Schleicher (escaping curves for finite-order class B).
- Hénon equilibrium measure (67): added uniqueness as measure of maximal entropy and saddle-point equidistribution (Bedford–Lyubich–Smillie).

Numbering map (old → new):
46→45 (merged). New entry 46 (Yoccoz and Shishikura theorems). All other numbers unchanged.

### Section 47: Approximation Theory

Size: 19308 → 20224 bytes; entries: 70 → 71.

Sources consulted: Trefethen, *Approximation Theory and Approximation Practice* (References/Trefethen2013ApproximationTheoryApproximationPractice-AuthorManuscript.pdf; Theorems 7.1–7.2, 8.1–8.2 and the chapter on |x|, including Stahl's asymptotic); Pinkus, *n-Widths in Approximation Theory* (References/Pinkus1985NWidthsApproximationTheory-SpringerErgebMath3.pdf; Ch. VI–VII on Kashin and Gluskin widths); bibliography entries of Section 47 in CKMA-bib.md and CKMA-bib2.md (Achieser, DeVore–Lorentz, de Boor, Saff–Totik) for standard statements.

Changes:
- Jackson's trigonometric theorem (20): added the sharp Favard–Akhiezer–Krein form with explicit Favard constants K_r (classical core in Achieser, Korneichuk, DeVore–Lorentz).
- Finite smoothness and coefficients (34): removed redundant repeated hypothesis "For ν≥1".
- Bernstein–Walsh inequality (37): replaced the vague closing sentence by Walsh's maximal convergence theorem (geometric rate ⇔ holomorphic extension to Green level region), the general form of entry 33.
- Newman's theorem (40): added Stahl's sharp asymptotic E_{n,n}(|x|) ~ 8e^{-π√n}.
- Spline Jackson estimates (48): corrected the unnecessary quasiuniformity / mesh-ratio hypothesis (the direct estimate holds for arbitrary knot sequences with C = C_k), fixed the clash between the smoothness index s and the spline s_h, and added the Besov characterization of spline approximation spaces for uniform knots.
- Sobolev-native-space rates (55) and multivariate polynomial dimension (now 69): removed padded trailing phrases.
- New entry 65 (widths of finite-dimensional balls): Kashin and Garnaev–Gluskin Gelfand widths of the ℓ^1 ball and their dual Kolmogorov widths; a central widths result (Pinkus, Lorentz–Golitschek–Makovoz, Temlyakov) underlying Sobolev widths for q>2 and compressed sensing.

Numbering map (old → new):
65→66, 66→67, 67→68, 68→69, 69→70, 70→71. New entry 65. Old 1–64 unchanged.

### Section 48: Orthogonal Polynomials, Moment Problems, and Spectral Recurrences

Size: 19754 → 21137 bytes; entries: 72 → 75.

Sources consulted: Levin–Lubinsky, *Orthogonal Polynomials for Exponential Weights* (References/LevinLubinsky2001OrthogonalPolynomialsExponentialWeights-Springer.CMS.pdf; Freud conjecture and Mhaskar–Rakhmanov–Saff numbers); bibliography entries of Section 48 in CKMA-bib.md and CKMA-bib2.md (Simon's OPUC and Szegő's Theorem and Its Descendants, Szegő, Stahl–Totik, Deift) for standard statements.

Changes:
- Markov–Stieltjes inequalities (18) and product measures (now 72): removed padded trailing sentences.
- New entry 31 (essential spectrum, Blumenthal–Weyl): σ_ess = [b−2a, b+2a] when a_n→a, b_n→b; the basic link between recurrence asymptotics and spectra, recurring in Simon, Chihara, Teschl.
- Szegő function (now 55): corrected the unexplained notation |D^*|^2 = w to boundary values |D|^2 = w.
- Toeplitz determinants (now 56): made the product formula explicit and tightened the closing sentence.
- Strong Szegő theorem (now 57): replaced the vague "Sobolev-1/2 condition is the natural sharp condition" by the precise Ibragimov hypothesis (L ∈ L^1, Σ k|L̂(k)|^2 < ∞) and the Golinskii–Ibragimov characterization Σ n|α_n|^2 < ∞.
- Real-line Rakhmanov theorem (now 63): added Denisov's extension (only σ_ess = [−2,2] and a.e. positive a.c. density needed).
- New entry 64 (Killip–Simon theorem): Hilbert–Schmidt perturbations of the free Jacobi matrix characterized spectrally via Case sum rules; central in Simon's spectral theory of orthogonal polynomials.
- New entry 68 (exponential weights): Mhaskar–Rakhmanov–Saff numbers, external-field zero distribution, Freud's conjecture (Lubinsky–Mhaskar–Saff); core of Levin–Lubinsky and of the Freud-weight theory listed in the section.

Numbering map (old → new):
31→32, 32→33, 33→34, 34→35, 35→36, 36→37, 37→38, 38→39, 39→40, 40→41, 41→42, 42→43, 43→44, 44→45, 45→46, 46→47, 47→48, 48→49, 49→50, 50→51, 51→52, 52→53, 53→54, 54→55, 55→56, 56→57, 57→58, 58→59, 59→60, 60→61, 61→62, 62→63, 63→65, 64→66, 65→67, 66→69, 67→70, 68→71, 69→72, 70→73, 71→74, 72→75. New entries: 31, 64, 68. Old 1–30 unchanged.

### Section 49: Special functions, integral transforms, and classical formulae

Size: 18960 → 23131 bytes; entries: 74 → 78.

Sources consulted: Andrews–Askey–Roy, *Special Functions* (local PDF: table of contents, Chapters 1–4 organization; Bohr–Mollerup §1.9, Barnes integral §2.4, Bessel/Fourier §4.9); DLMF conventions for Bessel, Airy, Hermite, Whittaker and theta functions (checked from standard normalizations); bibliography entries of CKMA-bib.md and CKMA-bib2.md §49.

Changes:
- New entry 4 (Bohr–Mollerup theorem): standard characterization of Γ, a chapter in Andrews–Askey–Roy and Artin-style treatments; core.
- Entry 3 (Weierstrass product): added Euler's limit formula for Γ.
- Entry 9 (Stirling): Bernoulli numbers and polynomials, used there and in entries 10–11, were undefined; definitions added.
- Entry 10 (Hurwitz zeta): added values at nonpositive integers, $\zeta(-n,a)=-B_{n+1}(a)/(n+1)$.
- New entry 11 (Riemann zeta function): Euler product, functional equation of the completed function, values at even integers and trivial zeros; the section heading names zeta but only the Hurwitz Mellin representation was stated.
- Entry 13 (Gauss equation): normalization made precise ($c\notin-\mathbb N_0$, unique solution holomorphic at 0); added local exponents at $0,1,\infty$, the second solution at 0, and Riemann's $P$-symbol reduction / Kummer's 24 solutions.
- Entry 22 (Kummer transformation): replaced vague trailing sentence on confluence by the precise confluence limit $M(a,b,z)=\lim F(a,\beta;b;z/\beta)$.
- Entry 29 (modified Bessel functions): $K_\nu$ was used without definition; definition via $I_{\pm\nu}$ and positivity added.
- Entry 30 (generating function): added Bessel's integral for integer order.
- Entry 31 (Poisson integral): removed a DLMF pointer sentence.
- Entry 32 (Hankel transform): added the formula expressing the Fourier transform of a radial function on $\mathbb R^d$ as a Hankel transform (core use of Bessel functions in harmonic analysis).
- Entry 37 (Airy asymptotics): added the oscillatory asymptotics of Ai on the negative axis.
- Entry 43 (Hermite): added Hermite functions as complete orthogonal basis, harmonic-oscillator eigenfunctions, and Fourier eigenfunctions.
- Entry 45 (spherical harmonics): generalized from $S^2$ to $S^{d-1}$: degree-$\ell$ harmonics as Laplace–Beltrami eigenspaces, dimension formula, $L^2$ decomposition, and the Gegenbauer addition theorem, with the $S^2$ case retained.
- Entry 50 (Jacobi elliptic functions): definition by inversion made explicit (sn, cn, dn) and periods $4K$, $2iK'$ of sn added.
- Entry 51 (Weierstrass ℘): added the addition theorem.
- New entry 52 (Liouville theorems for elliptic functions, field $\mathbb C(\wp,\wp')$): basic structure theorems of elliptic functions, missing.
- New entry 60 (Rogers–Ramanujan identities): central q-series identities treated in Andrews–Askey–Roy and Gasper–Rahman.
- Entry 70 (formerly Mellin–Barnes representation of $(1+x)^{-a}$): replaced by Barnes's integral for ${}_2F_1$, keeping the old statement as the special case $b=c$ (Mellin pair).
- Fractional-calculus introduction: defined the Riemann–Liouville derivative (used in entry 74 but undefined) and its relation to the Caputo derivative.
- Entry 74 (fractional semigroup): vague "left inverse on the range" sentence replaced by the precise identity $D^\alpha I^\alpha f=f$ a.e.

Numbering map (old → new):
4→5, 5→6, 6→7, 7→8, 8→9, 9→10, 10→12, 11→13, 12→14, 13→15, 14→16, 15→17, 16→18, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→53, 51→54, 52→55, 53→56, 54→57, 55→58, 56→59, 57→61, 58→62, 59→63, 60→64, 61→65, 62→66, 63→67, 64→68, 65→69, 66→70, 67→71, 68→72, 69→73, 70→74, 71→75, 72→76, 73→77, 74→78 (new entries: 4, 11, 52, 60)

### Section 50: Asymptotic analysis, resurgence, and perturbation

Size: 22981 → 24416 bytes; entries: 66 → 68.

Sources consulted: bibliography entries of CKMA-bib.md and CKMA-bib2.md §50 (Olver, Wong, Bender–Orszag, Nayfeh, Kevorkian–Cole, Sanders–Verhulst–Murdock, Kato via Section 22); standard formulations checked by direct computation (Euler–Maclaurin remainder and bound, Mellin pole residues, WKB recursion, Borel transforms, Euler example, connection formula, second-order averaging).

Changes:
- Entry 5 (Borel's realization theorem): removed a trailing sentence that only restated the theorem.
- Entry 13 (nonstationary phase): added the endpoint expansion for Fourier-type integrals on a compact interval without stationary points (core in Olver and Wong), replacing a generic sentence on integration by parts.
- Entry 25 (Poisson summation): removed padding sentence.
- Entry 29 (Karamata): removed padding sentence.
- Entry 39 (Bohr–Sommerfeld): the operator normalization was missing (the stated quantization rule depends on it); now stated for hmtBc\varepsilon^2y''+Vy=Ey$, with the turning-point hypothesis made explicit.
- Entry 65 (second-order averaging): the second-order averaged equation was not stated; now gives the near-identity change and $\dot y=\varepsilon^2\overline{D_xf\,u}(y)$ with its error bound.
- New entry 67 (Poincaré–Lindstedt method / secular terms, Duffing frequency correction): standard core of perturbation methods in Bender–Orszag, Nayfeh, Kevorkian–Cole; previously absent.
- New entry 68 (Rayleigh–Schrödinger eigenvalue perturbation with first- and second-order formulas): core regular-perturbation result; analytic families left to Section 22.
- Introduction: scope sentence updated to mention averaging and eigenvalue perturbation.

Numbering map (old → new):
unchanged (new entries 67, 68 appended)

### Section 51: Integrable systems and Riemann–Hilbert methods

Size: 24974 → 25685 bytes; entries: 68 → 67.

Sources consulted: bibliography entries of CKMA-bib.md and CKMA-bib2.md §51 (Deift; Fokas–Its–Kapaev–Novokshenov; Ablowitz–Fokas; Faddeev–Takhtajan; Deift–Zhou papers; Trogdon–Olver); formulas verified by direct computation (KdV trace identity via the dispersion relation for /T$, Lax/Hamiltonian/Miura identities, Toda Flaschka equations and Moser's spectral-measure evolution, Schlesinger equations, heat-equation global relation, semicircle Euler–Lagrange condition, linear limit of the NLS Riemann–Hilbert reconstruction).

Changes:
- Entry 1 (Sokhotski–Plemelj): made precise as \pm=\pm\frac12I+\frac12S$ with the principal-value operator, and added the Plemelj–Privalov Hölder boundedness used in the classical Hölder theory of entries 3–4.
- Entry 8 (small-norm theorem): absorbed old entry 9 (perturbation stability), a routine operator-theory consequence not warranting its own entry.
- Old entry 9 removed (merged into 8).
- New entry 33 (Riemann–Hilbert problem for defocusing NLS): explicit jump matrix, unique solvability via the vanishing lemma, and reconstruction formula; the central example of the Riemann–Hilbert formulation of inverse scattering, previously only implicit in the long-time entry.
- Entry 34 (nonlinear stationary phase): vague statement replaced by the Deift–Zhou asymptotic formula with explicit modulus $|\alpha|^2=\nu/2$, logarithmic phase $\nu\log(8t)$, and error (t^{-1}\log t)$.
- Entry 35 (Liouville–Arnold): absorbed the elementary content of old entry 36 (conservation iff $\{F,H\}=0$; commuting flows); Poisson-bracket axioms dropped as definitional.
- Old entry 36 removed (merged into 35).
- Entry 60 (equilibrium measure): added the semicircle law as the equilibrium measure for (x)=2x^2$ in the stated normalization.

Numbering map (old → new):
9→8 (merged), 10→9, 11→10, 12→11, 13→12, 14→13, 15→14, 16→15, 17→16, 18→17, 19→18, 20→19, 21→20, 22→21, 23→22, 24→23, 25→24, 26→25, 27→26, 28→27, 29→28, 30→29, 31→30, 32→31, 33→32, 36→35 (merged), 37→36, 38→37, 39→38, 40→39, 41→40, 42→41, 43→42, 44→43, 45→44, 46→45, 47→46, 48→47, 49→48, 50→49, 51→50, 52→51, 53→52, 54→53, 55→54, 56→55, 57→56, 58→57, 59→58, 60→59, 61→60, 62→61, 63→62, 64→63, 65→64, 66→65, 67→66, 68→67 (new entry: 33; old 34 and 35 keep their numbers)

### Section 52: Geometric analysis on manifolds

Size: 31667 → 32924 bytes; entries: 90 → 92.

Sources consulted: bibliography entries of CKMA-bib.md and CKMA-bib2.md §52 (Cheeger–Ebin, Petersen, Chavel, Schoen–Yau, Aubin, Hebey, Li, Dierkes–Hildebrandt–Sauvigny); SYNOPSIS53.md checked for overlap (Gauss–Bonnet and Hodge theory are there and were not duplicated). Statements reviewed against standard formulations; Petersen, *Riemannian Geometry*, 3rd ed. (local PDF; Toponogov theorem, maximal diameter rigidity, Gromov precompactness sections) consulted.

Changes:
- New entry 6 (Toponogov comparison): the basic triangle/hinge comparison theorem for lower sectional curvature bounds, core in Cheeger–Ebin and Petersen; previously absent although Rauch comparison was included.
- Entry 7 (Bonnet–Myers): added Cheng's maximal-diameter rigidity.
- New entry 12 (Gromov precompactness under a Ricci lower bound): central compactness theorem of modern comparison geometry, complementing the bounded-curvature compactness of entry 11.
- Entry 28 (diameter eigenvalue bound): added the sharp Zhong–Yang estimate $\lambda_1\geq\pi^2/D^2$; removed padding sentence.
- Entry 31 (Yamabe theorem): added the Aubin–Schoen criterion (M,[g])<Y(S^n)$ and its verification, the analytic heart of the solution.
- Entry 52 (Douglas–Radó): added absence of interior branch points for least-area disks in $\mathbb R^3$ (Osserman, Gulliver, Alt).

Numbering map (old → new):
6→7, 7→8, 8→9, 9→10, 10→11, 11→13, 12→14, 13→15, 14→16, 15→17, 16→18, 17→19, 18→20, 19→21, 20→22, 21→23, 22→24, 23→25, 24→26, 25→27, 26→28, 27→29, 28→30, 29→31, 30→32, 31→33, 32→34, 33→35, 34→36, 35→37, 36→38, 37→39, 38→40, 39→41, 40→42, 41→43, 42→44, 43→45, 44→46, 45→47, 46→48, 47→49, 48→50, 49→51, 50→52, 51→53, 52→54, 53→55, 54→56, 55→57, 56→58, 57→59, 58→60, 59→61, 60→62, 61→63, 62→64, 63→65, 64→66, 65→67, 66→68, 67→69, 68→70, 69→71, 70→72, 71→73, 72→74, 73→75, 74→76, 75→77, 76→78, 77→79, 78→80, 79→81, 80→82, 81→83, 82→84, 83→85, 84→86, 85→87, 86→88, 87→89, 88→90, 89→91, 90→92 (new entries: 6, 12)

### Section 53: Elliptic operators on manifolds, index theory, and spectral geometry

Size: 28346 → 28877 bytes; entries: 80 → 80.

Sources consulted: Zelditch, *Eigenfunctions of the Laplacian on a Riemannian Manifold* (local author copy; nodal-set chapter for Donnelly–Fefferman and Logunov, Pleijel discussion); bibliography entries of CKMA-bib.md and CKMA-bib2.md §53 (Chavel, Bérard, Bergeron, Gilkey, Roe, Berline–Getzler–Vergne); SYNOPSIS45.md and SYNOPSIS52.md checked for overlap. The four-dimensional Gauss–Bonnet–Chern formula was checked on the round ^4$.

Changes:
- Entry 27 (nonperiodic improvement): replaced an uninformative trailing sentence by the attribution (Duistermaat–Guillemin, Ivrii).
- Entry 46 (Chern–Gauss–Bonnet): added the Gauss–Bonnet formula for compact surfaces with boundary and the explicit four-dimensional curvature integrand for $\chi$.
- Entry 65 (Szegő–Weinberger): removed padding sentence.
- Entry 67 (curvature eigenvalue bound): replaced a proof sketch by the attributions (Lichnerowicz, Obata).
- Entry 69 (Courant): added Pleijel's theorem (Courant sharpness for only finitely many eigenvalues).
- Entry 71 (nodal volume): replaced the vague closing remark by the current smooth-case status: Logunov's lower bound and polynomial upper bound; Donnelly–Fefferman attributed for the analytic case.
- Entry 78 (Selberg trace formula): added its standard consequences, Huber's theorem (Laplace spectrum ⇔ length spectrum) and the prime geodesic theorem.
- Entry 80 (spectral nonuniqueness): added attributions and Sunada's method with the Gordon–Webb–Wolpert isospectral planar domains.

Numbering map (old → new):
unchanged

