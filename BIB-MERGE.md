# Merging CKMA-bib2.md into CKMA-bib.md

This file records how the former supplementary bibliography `CKMA-bib2.md` was merged
into `CKMA-bib.md` on 2026-10-18. `CKMA-bib2.md` was then removed; it can be recovered
from git history (commit 90f5bb6).

## Method

* Every section 1–55 of `CKMA-bib.md` now has the subheadings "Foundational works" and
  "More recent works". Longer parts are divided further by `####` group headings.
* Classification rule: a work belongs under "Foundational works" if its first edition
  (or the original-language edition of a translation) appeared before 2010. Otherwise it goes under
  "More recent works". Foundational entries carry no edition data or links. Recent entries
  carry year, publisher and a DOI link where one is available.
* Entries listed in both sources were merged into one entry. The section introductions
  were rewritten to cover both parts. The front matter of `CKMA-bib.md` was rewritten. It now
  includes the guidance formerly at the end of `CKMA-bib2.md`.
* Entry count: 1,853 entries in the two sources, 1,848 after merging duplicates and splitting
  a few combined entries.

## Moves between sections

* Applebaum, *Lévy Processes and Stochastic Calculus*: Section 6 → Section 8.
* Schuster–Kaltenbacher–Hofmann–Kazimierski, *Regularization Methods in Banach Spaces*:
  Section 22 → Section 25.
* Kapitula–Promislow, *Spectral and Dynamical Stability of Nonlinear Waves*:
  Section 22 → Section 34.
* Choulli, *Applications of Elliptic Carleman Inequalities to Cauchy and Inverse Problems*:
  Section 24 → Section 33.
* Lindquist–Picci, *Linear Stochastic Systems*: Section 24 → Section 8.
* Brémaud, *Fourier Analysis and Stochastic Processes*: Section 27 → Section 8.
* Coornaert, *Topological Dimension and Dynamical Systems*: Section 31 → Section 10.
* Roubíček, *Nonlinear Partial Differential Equations with Applications*:
  Section 32 → Section 35.
* Brazitikos et al. moved from Section 13 to Section 17, Bovier–den Hollander from 39 to 38,
  Seiler from 30 to 32. Aiena moved from 20 to 21, with a pointer left in 20.
* The inverse-problems group stays in Section 22 under its own heading.

## Removals after review

At the user's request, all the "Candidates for removal" in the logs below were acted on
(2026-10-18). 71 entries were deleted. 13 combined entries were cut down to the sound part:
Dieudonné (§2), Einsiedler–Ward (§10), Kawohl and Gardner (§11), Strătilă–Zsidó (§23),
Olevskii–Ulanovskii (§29), Lloyd and Mawhin (§35), Fonseca–Leoni (§36), Whitney (§37),
Valiron (§41), Henrot (§53), Steele (§54), and the Coq/Rocq libraries (§55).

* The Mawhin phrase now names *Topological Degree Methods in Nonlinear Boundary Value
  Problems* (CBMS 40).
* The doubtful "companion volume" phrases (Einsiedler–Ward, Fonseca–Leoni) were dropped.
* Arnold's *Lectures on Partial Differential Equations*, formerly bundled with *Problems for
  Children* in §54, was moved to §32 (Foundational).
* Lerner–Nazarov was removed from the reading paths.
* In a second round, Unser–Tafti (§9), Heinosaari–Ziman (§13), *Inside Out II* (§22),
  Seiler (§32), and Kunstmann–Weis's lecture notes (§24) were removed. Sauzin's lecture notes
  were dropped from the Mitschi–Sauzin entry (§50). Simon's historical notes (§2) and the
  Mathlib entry (§55) were kept.

The entry count is now 1,773.

## Additions from ReferencesSuppl

On 2026-10-18 the 1,060 PDF files in `ReferencesSuppl/` were reviewed. Books were added if they
are standard graduate or research references in analysis and were not already listed. Most files
were not added, mainly for these reasons:

* numerical analysis and scientific computing;
* statistics, Monte Carlo methods and simulation;
* optimization and operations research, control engineering, and mathematical biology;
* conference proceedings and festschrifts;
* undergraduate texts, and narrow or minor monographs.

134 entries were added. 130 went under "Foundational works". Four went under "More recent works":
Salamon, Bakonyi–Woerdeman, Garrett, and Fibich. The entry count is now 1,907.

* §1: Dautray, Lions, *Mathematical Analysis and Numerical Methods for Science and Technology*.
* §2: Lützen, *The Prehistory of the Theory of Distributions*; Goldstine, *A History of the Calculus of Variations from the 17th through the 19th Century*; Steffens, *The History of Approximation Theory*.
* §4: Knapp, *Basic Real Analysis*; Benedetto, Czaja, *Integration and Modern Analysis*; Doob, *Measure Theory*; Bourbaki, *Functions of a Real Variable*; Salamon, *Measure and Integration* (more recent).
* §6: Loève, *Probability Theory I–II*; Fristedt, Gray, *A Modern Approach to Probability Theory*; Koralov, Sinai, *Theory of Probability and Random Processes*; Kallenberg, *Probabilistic Symmetries and Invariance Principles*; Ellis, *Entropy, Large Deviations, and Statistical Mechanics*.
* §8: Dynkin, *Markov Processes I–II*; Gikhman, Skorokhod, *The Theory of Stochastic Processes I–III*; Chung, Williams, *Introduction to Stochastic Integration*; Liptser, Shiryaev, *Theory of Martingales*; Freidlin, Wentzell, *Random Perturbations of Dynamical Systems*; Freidlin, *Functional Integration and Partial Differential Equations*; Stroock, *Markov Processes from K. Itô's Perspective*; Stroock, *Partial Differential Equations for Probabilists*; Peskir, Shiryaev, *Optimal Stopping and Free-Boundary Problems*; Liggett, *Interacting Particle Systems*; Kipnis, Landim, *Scaling Limits of Interacting Particle Systems*; Spohn, *Large Scale Dynamics of Interacting Particles*.
* §9: Kuo, *Gaussian Measures in Banach Spaces*.
* §10: Sinai, *Topics in Ergodic Theory*; Keller, *Equilibrium States in Ergodic Theory*; Schmidt, *Dynamical Systems of Algebraic Origin*.
* §11: Walter, *Differential and Integral Inequalities*; Santaló, *Integral Geometry and Geometric Probability*; Schneider, Weil, *Stochastic and Integral Geometry*; Groemer, *Geometric Applications of Fourier Series and Spherical Harmonics*; Matheron, *Random Sets and Integral Geometry*.
* §12: Aubin, Frankowska, *Set-Valued Analysis*.
* §13: Zhan, *Matrix Inequalities*; Varga, *Geršgorin and His Circles*; Gustafson, Rao, *Numerical Range*; Bakonyi, Woerdeman, *Matrix Completions, Moments, and Sums of Hermitian Squares* (more recent).
* §15: Bhatia, *Notes on Functional Analysis*; Neumann, *Functional Operators I–II*.
* §16: Kelley, Namioka, *Linear Topological Spaces*.
* §17: Day, *Normed Linear Spaces*; Carothers, *A Short Course on Banach Space Theory*; Kadets, Kadets, *Series in Banach Spaces*; Wells, Williams, *Embeddings and Extensions in Analysis*.
* §21: Bognár, *Indefinite Inner Product Spaces*; Ball, Gohberg, Rodman, *Interpolation of Rational Matrix Functions*.
* §22: Amrein, Monvel, Georgescu, *C₀-Groups, Commutator Methods and Spectral Theory of N-Body Hamiltonians*; Baumgärtel, Wollenberg, *Mathematical Scattering Theory*; Berezin, Shubin, *The Schrödinger Equation*; Simon, *Quantum Mechanics for Hamiltonians Defined as Quadratic Forms*; Thaller, *The Dirac Equation*; Blank, Exner, Havlíček, *Hilbert Space Operators in Quantum Physics*; Chadan, Sabatier, *Inverse Problems in Quantum Scattering Theory*; Kuchment, *Floquet Theory for Partial Differential Equations*; Bourgain, *Green's Function Estimates for Lattice Schrödinger Operators and Applications*.
* §23: Sakai, *C\*-Algebras and W\*-Algebras*; Meyer, *Quantum Probability for Probabilists*.
* §24: Diekmann, Gils, Lunel, Walther, *Delay Equations*; Lasiecka, Triggiani, *Control Theory for Partial Differential Equations*.
* §25: Gripenberg, Londen, Staffans, *Volterra Integral and Functional Equations*; Halmos, Sunder, *Bounded Integral Operators on L² Spaces*; Nédélec, *Acoustic and Electromagnetic Equations*.
* §26: Triebel, *The Structure of Functions*.
* §27: Helson, *Harmonic Analysis*; Bochner, *Lectures on Fourier Integrals*; Bochner, Chandrasekharan, *Fourier Transforms*; Edwards, Gaudry, *Littlewood–Paley and Multiplier Theory*; King, *Hilbert Transforms I–II*; Golubov, Efimov, Skvortsov, *Walsh Series and Transforms*; Gilbert, Murray, *Clifford Algebras and Dirac Operators in Harmonic Analysis*.
* §28: Gangolli, Varadarajan, *Harmonic Analysis of Spherical Functions on Real Reductive Groups*; Warner, *Harmonic Analysis on Semi-Simple Lie Groups I–II*; Heckman, Schlichtkrull, *Harmonic Analysis and Special Functions on Symmetric Spaces*; Thangavelu, *Harmonic Analysis on the Heisenberg Group*; Graham, McGehee, *Essays in Commutative Harmonic Analysis*; Heyer, *Probability Measures on Locally Compact Groups*; Lax, Phillips, *Scattering Theory for Automorphic Functions*; Garrett, *Modern Analysis of Automorphic Forms by Example I–II* (more recent).
* §30: Kashiwara, Kawai, Kimura, *Foundations of Algebraic Analysis*; Maslov, Fedoriuk, *Semi-Classical Approximation in Quantum Mechanics*.
* §31: Nemytskii, Stepanov, *Qualitative Theory of Differential Equations*; Cesari, *Asymptotic Behavior and Stability Problems in Ordinary Differential Equations*; Siegel, Moser, *Lectures on Celestial Mechanics*; Wiggins, *Normally Hyperbolic Invariant Manifolds in Dynamical Systems*.
* §32: Olver, *Applications of Lie Groups to Differential Equations*; Nečas, *Direct Methods in the Theory of Elliptic Equations*.
* §34: Smoller, *Shock Waves and Reaction–Diffusion Equations*; Racke, *Lectures on Nonlinear Evolution Equations*; Fibich, *The Nonlinear Schrödinger Equation* (more recent); Doering, Gibbon, *Applied Analysis of the Navier–Stokes Equations*; Chorin, Marsden, *A Mathematical Introduction to Fluid Mechanics*.
* §36: Ekeland, *Convexity Methods in Hamiltonian Mechanics*; Bakhvalov, Panasenko, *Homogenisation*; Moser, *Selected Chapters in the Calculus of Variations*.
* §38: Kellogg, *Foundations of Potential Theory*; Gardiner, *Harmonic Approximation*; Pinsky, *Positive Harmonic Functions and Diffusion*.
* §40: Kodaira, *Complex Analysis*.
* §41: Sheil-Small, *Complex Polynomials*.
* §43: Hayman, *Multivalent Functions*.
* §45: Chirka, *Complex Analytic Sets*; Stout, *Polynomial Convexity*; Lieb, Michel, *The Cauchy–Riemann Complex*.
* §47: Jr., Graves-Morris, *Padé Approximants*; Borwein, Erdélyi, *Polynomials and Polynomial Inequalities*; Lai, Schumaker, *Spline Functions on Triangulations*; Mastroianni, Milovanović, *Interpolation Processes*; Sewell, *Degree of Approximation by Polynomials in the Complex Domain*; Lorentzen, Waadeland, *Continued Fractions, Volume 1*; Buhmann, *Radial Basis Functions*.
* §48: Khrushchev, *Orthogonal Polynomials and Continued Fractions*; Bultheel, González-Vera, Hendriksen, Njåstad, *Orthogonal Rational Functions*; Nikiforov, Suslov, Uvarov, *Classical Orthogonal Polynomials of a Discrete Variable*.
* §49: Nikiforov, Uvarov, *Special Functions of Mathematical Physics*; Müller, *Spherical Harmonics*; Jr., *Lie Theory and Special Functions*; Vilenkin, Klimyk, *Representation of Lie Groups and Special Functions I–III*; Weil, *Elliptic Functions according to Eisenstein and Kronecker*; Oberhettinger, *Tables of Bessel Transforms*; Iwasaki, Kimura, Shimomura, Yoshida, *From Gauss to Painlevé*; Hirschman, Widder, *The Convolution Transform*.
* §50: Arnold, Gusein-Zade, Varchenko, *Singularities of Differentiable Maps, Volume II*; Korevaar, *Tauberian Theory*; Wasow, *Linear Turning Point Theory*; Jr., *Singular Perturbation Methods for Ordinary Differential Equations*; Lagerstrom, *Matched Asymptotic Expansions*.
* §51: Ablowitz, Clarkson, *Solitons, Nonlinear Evolution Equations and Inverse Scattering*; Rogers, Schief, *Bäcklund and Darboux Transformations*; Toda, *Theory of Nonlinear Lattices*.
* §53: Rosenberg, *The Laplacian on a Riemannian Manifold*.
* §55: Goldblatt, *Lectures on the Hyperreals*.

## Per-section logs

The logs below were written during the merge. The "Proposed cross-section moves" lines are
proposals. The list above shows which were carried out. The "Candidates for removal" lines
are suggestions only. No entry was deleted.

### Section 1: Broad Courses, Encyclopedias, and Maps of Analysis
Entries: 17 + 11 → foundational 21, more recent 7 (duplicates merged 0).
Moved to More recent works: Simon, *A Comprehensive Course in Analysis* (2015; added "(5 volumes, 2015, American Mathematical Society)").
Moved to Foundational works: Godement, *Analysis I–IV* (French original 1998–2003); Amann–Escher, *Analysis I–III* (German original 1998–2001, English 2005–2009); Zorich, *Mathematical Analysis I–II* (Russian original 1981–1984); Bogachev–Smolyanov, *Real and Functional Analysis* (Russian original 2009); Choimet–Queffélec, *Twelve Landmarks of Twentieth-Century Analysis* (French original 2009).
Duplicates merged: none
Corrections: Godement: "French editions 2001–2003, English translations through 2015" corrected to "French editions 1998–2003, English translations 2004–2015" (Analyse mathématique I–II appeared 1998; English vol. I 2004).
Proposed cross-section moves: none
Candidates for removal: Reinhold Remmert and others, *Numbers* and the Springer *Readings in Mathematics* tradition: vague (a series "tradition" rather than a book), and *Numbers* is by Ebbinghaus et al. with Remmert as one of eight authors; marginal for a graduate analysis list.
Dates uncertain: Bogachev–Smolyanov (Russian university course believed 2009; the 2020 English edition is expanded and might count by its own date); Choimet–Queffélec (2015 English is an expanded translation of the 2009 French book; placed by the French date).

### Section 2: History, Perspective, and Essays
Entries: 11 + 17 → foundational 14, more recent 14 (duplicates merged 0).
Moved to More recent works: Barry Simon's historical notes (the works cited, *Szegő's Theorem and Its Descendants* 2011 and *A Comprehensive Course in Analysis* 2015, are post-2010).
Moved to Foundational works: Jahnke (ed.), *A History of Analysis* (2003; German original 1999); Bressoud, *A Radical Approach to Lebesgue's Theory of Integration* (2008); Mauldin (ed.), *The Scottish Book* (1st ed. 1981; added "1st ed. 1981;" to the entry); Siegmund-Schultze, *Mathematicians Fleeing from Nazi Germany* (2009; German original 1998).
Duplicates merged: none
Corrections: Gray, *The Real and the Complex* (2015): publisher "Oxford University Press" corrected to "Springer" (Springer Undergraduate Mathematics Series; the DOI is a Springer DOI).
Proposed cross-section moves: none
Candidates for removal: Dieudonné, *A History of Algebraic and Differential Topology*: a history of topology, not analysis (the paired *Foundations of Modern Analysis* is fine). Siegmund-Schultze, *Mathematicians Fleeing from Nazi Germany*: social and political history of emigration, little analysis content. Aubin–Goldstein (eds.), *The War of Guns and Mathematics*: institutional history of mathematics in WWI, not specific to analysis. Audin, *Remembering Sofya Kovalevskaya*: largely a personal/literary biography, weak as an analysis reference. Barry Simon's historical notes: not a book entry (a pointer into other books); consider folding into the Simon entries.
Dates uncertain: Mauldin, *The Scottish Book*: the 2015 second edition is substantially expanded and could arguably count as a new book; placed by its 1981 first edition.

### Section 3: Set-Theoretic and Descriptive Foundations for Analysts
Entries: 11 + 10 → foundational 13, more recent 8 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Kechris–Miller, *Topics in Orbit Equivalence* (2004); Pestov, *Dynamics of Infinite-dimensional Groups* (2006).
Duplicates merged: none
Corrections: none
Proposed cross-section moves: none
Candidates for removal: none
Dates uncertain: Gao, *Invariant Descriptive Set Theory* (CRC, 2008/2009; foundational either way). Kanovei, *Borel Equivalence Relations* (AMS 2008; kept foundational).

### Section 4: Real Analysis, Measure, and Integration
Entries: 24 + 16 → foundational 24, more recent 16 (duplicates merged 0).
Moved to More recent works: Tao, *An Introduction to Measure Theory* (2011, AMS); Conway, *A Course in Abstract Analysis* (2012, AMS); Diestel–Spalsbury, *The Joys of Haar Measure* (2014, AMS); Bogachev, *Differentiable Measures and the Malliavin Calculus* (2010, AMS); Weaver, *Measure Theory and Functional Analysis* (2013, World Scientific). Year and publisher added to each. More recent works split into "#### Graduate courses" and "#### References and monographs".
Moved to Foundational works: Schilling, *Measures, Integrals and Martingales* (1st ed. 2005); DiBenedetto, *Real Analysis* (1st ed. 2002); Wheeden–Zygmund, *Measure and Integral* (1st ed. 1977); Cannarsa–D'Aprile (Italian original 2008); Ziemer, *Modern Real Analysis* (1st ed. PWS, 1995). All placed under "#### Graduate foundations".
Duplicates merged: none
Corrections: Ziemer entry: "in the classics list" replaced by a pointer "(Section 26)", where *Weakly Differentiable Functions* is listed.
Proposed cross-section moves: none (Bogachev, *Differentiable Measures and the Malliavin Calculus* is already cross-listed in Section 9; Parthasarathy is cross-listed in Section 6; both kept).
Candidates for removal: V. S. Varadarajan, *Measures on Topological Spaces*: this is a long journal article (Mat. Sbornik 1961; AMS Translations 1965), not a book. Bellow and others (eds.), *Measure Theory Oberwolfach* volumes: conference proceedings (Springer LNM), not a book; the editor attribution is loose (the series was edited by D. Kölzow and others; Bellow co-edited only the 1975 volume). Ovchinnikov, *Measure, Integral, Derivative*: short bridge text at advanced-undergraduate level, arguably too elementary.
Dates uncertain: Ziemer, *Modern Real Analysis* (first edition believed PWS 1995); Bass (1st ed. 2011, kept recent).

### Section 5: Differentiation and the Fine Structure of Real Functions
Entries: 12 + 9 → foundational 14, more recent 7 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Krantz–Parks, *The Implicit Function Theorem* (2002); Kharazishvili, *Strange Functions in Real Analysis* (1st ed. 2000).
Duplicates merged: none
Corrections: Brian S. Thomson entry: *Differentiation of Integrals in R^n* is Guzmán's title, not a Thomson book; removed it from the Thomson entry, which now reads "Brian S. Thomson, *Real Functions* (to be read with Guzmán's monograph below)".
Proposed cross-section moves: none
Candidates for removal: none
Dates uncertain: Makarov–Podkorytov, *Smooth Functions and Maps* (English 2021; Russian original date not verified, kept recent). Heinonen, *Lectures on Lipschitz Analysis* (Jyväskylä lecture notes, 2005; kept foundational).

### Section 6: Probability: Measure-Theoretic Foundations and Limit Theory
Entries: 24 + 29 → foundational 31, more recent 22 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Gut, *Probability: A Graduate Course* (1st ed. 2005); Kyprianou, *Fluctuations of Lévy Processes* (1st ed. 2006); Applebaum, *Lévy Processes and Stochastic Calculus* (1st ed. 2004); Daley–Vere-Jones, *An Introduction to the Theory of Point Processes* (1st ed. 1988); Georgii, *Gibbs Measures and Phase Transitions* (1st ed. 1988); Feng–Kurtz, *Large Deviations for Stochastic Processes* (2006); Woess, *Denumerable Markov Chains* (2009). More recent works grouped under four "####" headings (graduate courses; limit theorems, approximation, large deviations and Gaussian measures; random measures, point processes and random walk; graphs, networks and statistical mechanics).
Duplicates merged: none
Corrections: Georgii entry: "The first edition (1988) would sit equally well in the classics list" replaced by "The first edition appeared in 1988."
Proposed cross-section moves: David Applebaum, *Lévy Processes and Stochastic Calculus* → Section 8 (Stochastic Processes, Martingales, and Stochastic Calculus): a stochastic-calculus text rather than measure-theoretic foundations or limit theory; could stay as a cross-listing here.
```
* **David Applebaum, *Lévy Processes and Stochastic Calculus*** (2nd ed.,
  2009, [Cambridge University Press](https://doi.org/10.1017/CBO9780511809781)). Stochastic integration for
  processes with jumps, the usual companion to the pathwise theory.
```
Candidates for removal: van der Hofstad, *Random Graphs and Complex Networks*: random-graph and network theory, combinatorial probability with little analytic content. Venkatesh, *The Theory of Probability: Explorations and Applications*: essentially an advanced-undergraduate text. Roch, *Modern Discrete Probability*: discrete probability toolkit, peripheral to analysis.
Dates uncertain: Kallenberg, *Random Measures, Theory and Applications* (2017) treated as a new book distinct from his *Random Measures* (1975); Talagrand, *Mean Field Models for Spin Glasses* (2011) treated as distinct from *Spin Glasses: A Challenge for Mathematicians* (2003); Grimmett, *Probability on Graphs* (1st ed. 2010, kept recent).

### Section 7: Concentration, High-Dimensional Probability, and Empirical Processes
Entries: 15 + 18 → foundational 10, more recent 23 (duplicates merged 0).
Moved to More recent works: Boucheron–Lugosi–Massart *Concentration Inequalities* (2013), Vershynin *High-Dimensional Probability* (2018), Talagrand *Upper and Lower Bounds for Stochastic Processes* (2014), Artstein-Avidan–Giannopoulos–Milman *Asymptotic Geometric Analysis I–II* (2015, 2021), Bobkov–Ledoux *One-dimensional Empirical Measures* (2019), Anderson–Guionnet–Zeitouni *An Introduction to Random Matrices* (2010), Tao *Topics in Random Matrix Theory* (2012). Each given "(year, publisher)"; no links added.
Moved to Foundational works: Bai–Silverstein *Spectral Analysis of Large Dimensional Random Matrices* (first ed. 2006; "first ed. 2006" added), Dudley *Uniform Central Limit Theorems* (first ed. 1999; "first ed. 1999" added).
Duplicates merged: none
Corrections: none. Minor wording: Talagrand *The Generic Chaining* annotation now names *Upper and Lower Bounds* explicitly (the two entries are no longer adjacent); Bai–Silverstein "books already listed" → "books listed in this section". Intro merged; "already in the classics list" removed. "More recent works" grouped into #### Concentration, chaining, and empirical processes / Random matrices / Related directions.
Proposed cross-section moves: none
Candidates for removal: none strong. Borderline: van Handel *Probability in High Dimension* (online lecture notes, not a book; deliberately included by the source file); Koltchinskii and van de Geer (statistics-oriented Lecture Notes volumes).
Dates uncertain: none

### Section 8: Stochastic Processes, Martingales, and Stochastic Calculus
Entries: 21 + 35 → foundational 24, more recent 32 (duplicates merged 0).
Moved to More recent works: Mörters–Peres *Brownian Motion* (2010, Cambridge University Press), Barlow *Random Walks and Heat Kernels on Graphs* (2017, Cambridge University Press).
Moved to Foundational works: Fleming–Soner *Controlled Markov Processes and Viscosity Solutions* (first ed. 1993; "first ed. 1993" added), Delbaen–Schachermayer *The Mathematics of Arbitrage* (2006), Hsu *Stochastic Analysis on Manifolds* (2002), Marcus–Rosen *Markov Processes, Gaussian Processes, and Local Times* (2006), Jacob *Pseudo Differential Operators and Markov Processes* (2001–2005).
Duplicates merged: none
Corrections: none. Intro merged ("remain the references" → "remain the standard references"). "More recent works" grouped into #### Courses and general theory / Markov processes, ergodicity, and random geometry / Stochastic control, backward equations, and mean-field games.
Proposed cross-section moves: none
Candidates for removal: Särkkä–Solin *Applied Stochastic Differential Equations* (2019): engineering/filtering-oriented applied text, below the analytic level of the rest of the section. Shiryaev *Stochastic Disorder Problems* (2019): specialised statistical change-point detection, marginal for an analysis bibliography. Brémaud *Probability Theory and Stochastic Processes* (2020): broad applied-oriented introduction, largely redundant with the courses listed (weak case).
Dates uncertain: Bass, *Stochastic Processes* (2011) and *Diffusions and Elliptic Operators* (1998) form a single classics entry; kept in Foundational works on the strength of the 1998 book. Levin–Peres *Markov Chains and Mixing Times*: first ed. 2009 (with Wilmer), so Foundational.

### Section 9: Malliavin Calculus, Rough Paths, and Stochastic PDE
Entries: 14 + 19 → foundational 13, more recent 20 (duplicates merged 0).
Moved to More recent works: Bogachev *Differentiable Measures and the Malliavin Calculus* (2010, American Mathematical Society), Friz–Victoir *Multidimensional Stochastic Processes as Rough Paths* (2010, Cambridge University Press), Friz–Hairer *A Course on Rough Paths* (2014, Springer; 2nd ed. 2020), Hairer *A Theory of Regularity Structures* (2014; marked as a paper in Inventiones Mathematicae), Zambotti/Gubinelli lecture notes on paracontrolled distributions (paracontrolled calculus dates from 2012 onward).
Moved to Foundational works: Da Prato *Introduction to Stochastic Analysis and Malliavin Calculus* (DOI is the 3rd ed., 2014; first ed. 2007; marked "3rd ed., 2014 … first ed. 2007"), Lyons–Caruana–Lévy *Differential Equations Driven by Rough Paths* (2007), Dalang et al. *A Minicourse on SPDE* (2009), Holden–Øksendal–Ubøe–Zhang *Stochastic PDE: A Modeling, White Noise Functional Approach* (first ed. 1996; "first ed. 1996" added).
Duplicates merged: none
Corrections: Bally–Caramellino *Stochastic Integration by Parts and Functional Itô Calculus* — the book has three authors: Vlad Bally, Lucia Caramellino, and Rama Cont (confirmed by the PDF filename in References/); Rama Cont added. Intro merged. "More recent works" grouped into #### Malliavin calculus and Gaussian analysis / Rough paths and singular stochastic PDE / Stochastic PDE.
Proposed cross-section moves: none
Candidates for removal: "Lorenzo Zambotti, Massimiliano Gubinelli, and collaborators' lecture notes on paracontrolled distributions": names no specific book, and the attribution to Zambotti is doubtful (paracontrolled calculus is due to Gubinelli, Imkeller, and Perkowski). Suggest replacing with a definite item such as Massimiliano Gubinelli and Nicolas Perkowski, *Lectures on Singular Stochastic PDEs* (2015, Ensaios Matemáticos, Sociedade Brasileira de Matemática). Hairer *A Theory of Regularity Structures*: a journal paper, not a book (kept, since the entry says so). Unser–Tafti *An Introduction to Sparse Stochastic Processes*: signal-processing orientation (weak case).
Dates uncertain: Da Prato first edition 2007 (fairly confident; moved on that basis).

### Section 10: Ergodic Theory and Measurable Dynamics
Entries: 19 + 24 → foundational 22, more recent 21 (duplicates merged 0; one duplicate resolved by splitting, see below).
Moved to More recent works: Einsiedler–Ward *Ergodic Theory with a View Towards Number Theory* (2011, Springer), Eisner–Farkas–Haase–Nagel *Operator Theoretic Aspects of Ergodic Theory* (2015, Springer), Host–Kra *Nilpotent Structures in Ergodic Theory* (2018, American Mathematical Society), Barreira–Pesin *Introduction to Smooth Ergodic Theory* (2013, American Mathematical Society).
Moved to Foundational works: Lind–Marcus *An Introduction to Symbolic Dynamics and Coding* (first ed. 1995; "first ed. 1995" added), Barreira–Pesin *Nonuniform Hyperbolicity* (2007), Bonatti–Díaz–Viana *Dynamics Beyond Uniform Hyperbolicity* (2005), Chernov–Markarian *Chaotic Billiards* (2006), Bekka–Mayer *Ergodic Theory and Topological Dynamics of Group Actions on Homogeneous Spaces* (2000), Morris *Ratner's Theorems on Unipotent Flows* (2005), Zimmer–Morris *Ergodic Theory, Groups, and Geometry* (2008).
Duplicates merged: Baladi. The classics entry covered both *Positive Transfer Operators and Decay of Correlations* (2000) and *Dynamical Zeta Functions and Dynamical Determinants for Hyperbolic Maps* (2018); the latter was also the CKMA-bib2.md entry. Resolved by splitting: the classics entry now lists only *Positive Transfer Operators* (Foundational), with a pointer to the 2018 book; the CKMA-bib2.md entry for the 2018 book (with DOI) stands in More recent works.
Corrections: Barreira–Pesin *Nonuniform Hyperbolicity* annotation "their introduction in the classics list" → "their *Introduction to Smooth Ergodic Theory*, listed under More recent works". Intro merged. "More recent works" grouped into #### Textbooks and general theory / Smooth and hyperbolic dynamics / Group actions, homogeneous dynamics, and combinatorics.
Proposed cross-section moves: none
Candidates for removal: none. Note: the Einsiedler–Ward "companion volume *Homogeneous Dynamics and Applications*" has, to my knowledge, not appeared as a published book (draft chapters only); consider rewording to "and the forthcoming companion volume".
Dates uncertain: Coudène (English 2016; French original 2012) — More recent either way.

### Section 11: Classical Inequalities, Means, Majorization, and Rearrangement
Entries: 19 + 7 → foundational 21, more recent 5 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Garling *Inequalities: A Journey into Linear Analysis* (2007), Kufner–Persson–Samko *Weighted Inequalities of Hardy Type* (2nd ed. 2017; first ed. by Kufner and Persson, 2003; note added).
Duplicates merged: none
Corrections: none. Intro taken from CKMA-bib.md-supplement intro ("remain the references" → "remain the central references"). The Part III introductory paragraph of CKMA-bib.md sits above Section 11 and is not part of S11.md; the assembler should keep it under the `# Part III` heading.
Proposed cross-section moves: none (Burago–Zalgaller, Schneider, Gardner overlap Sections 12/14 but cross-listing is deliberate).
Candidates for removal: "Erwin Lutwak, Richard Gardner's *Geometric Tomography*, and Gardner's survey on the Brunn–Minkowski inequality": Lutwak is named with no work, and Gardner's survey is a paper (Bull. AMS 2002); suggest dropping Lutwak's name or citing a specific item. "Almut Burchard's lecture notes on rearrangement inequalities": lecture notes, not a book (paired with Kawohl; weak case).
Dates uncertain: none

### Section 12: Convexity, Convex Analysis, and Variational Analysis
Entries: 17 + 23 → foundational 23, more recent 17 (duplicates merged 0).
Moved to More recent works: Borwein–Vanderwerff *Convex Functions* (2010, CUP; year/publisher added); Bauschke–Combettes *Convex Analysis and Monotone Operator Theory* (2011, 2nd ed. 2017, Springer; added); Simon *Convexity: An Analytic Viewpoint* (2011, CUP; added).
Moved to Foundational works: Boyd–Vandenberghe *Convex Optimization* (2004); Simons *From Hahn–Banach to Monotonicity* (2008); Burachik–Iusem *Set-Valued Mappings* (2008); Borwein–Zhu *Techniques of Variational Analysis* (2005); Zălinescu *Convex Analysis in General Vector Spaces* (2002); Gruber *Convex and Discrete Geometry* (2007); Barvinok *A Course in Convexity* (2002); Dontchev–Rockafellar *Implicit Functions and Solution Mappings* (1st ed. 2009; "2009;" added to the bibliographic note); Attouch–Buttazzo–Michaille *Variational Analysis in Sobolev and BV Spaces* (1st ed. 2006; "2006;" added).
Duplicates merged: none.
Corrections: Boyd–Vandenberghe annotation: removed "Earlier than the nominal boundary" (supplement-specific wording). First-edition years added for Dontchev–Rockafellar and Attouch–Buttazzo–Michaille.
Proposed cross-section moves: none (Hug–Weil, Gruber, and Barvinok are convex geometry and could also sit beside Schneider in Section 11, but they fit here).
Candidates for removal: Boumal, *An Introduction to Optimization on Smooth Manifolds*: optimization/numerical text, peripheral to convex or variational analysis. Bonnans, *Convex and Stochastic Optimization*: mainly optimization, borderline.
Dates uncertain: Nesterov *Lectures on Convex Optimization* (2018) is the much expanded 2nd ed. of *Introductory Lectures on Convex Optimization* (2004); kept in More recent works as essentially a new book. Kılınç-Karzan–Nemirovski (2025) kept as given; could not verify against a PDF.

### Section 13: Matrix Analysis, Operator Monotonicity, and Noncommutative Inequalities
Entries: 14 + 13 → foundational 14, more recent 12 (duplicates merged 0; 1 entry moved to Section 17).
Moved to More recent works: Hiai–Petz *Introduction to Matrix Analysis and Applications* (2014, Springer; added); Simon *Loewner's Theorem on Monotone Matrix Functions* (2019, Springer; added); Carlen *Trace Inequalities and Quantum Entropy* (2010, AMS; added; lecture notes in Contemp. Math. 529).
Moved to Foundational works: Zhang *Matrix Theory* (1st ed. 1999; "1999;" added); Higham *Functions of Matrices* (2008); Bengtsson–Życzkowski *Geometry of Quantum States* (1st ed. 2006; "2006;" added).
Duplicates merged: none.
Corrections: *Quantum Entropy and Its Use* is by Masanori Ohya and Dénes Petz (1993), not Hiai and Petz; author corrected. Intro: dropped "the asymptotic theory of high-dimensional convex bodies" after moving Brazitikos et al.
Moves within my sections: Brazitikos–Giannopoulos–Valettas–Vritsiou, *Geometry of Isotropic Convex Bodies* moved to Section 17 (asymptotic geometric analysis, not matrix analysis), where it replaces the pointer "Listed in Section 13".
Proposed cross-section moves: none.
Candidates for removal: Xian-Da Zhang, *Matrix Analysis and Applications*: engineering/signal-processing oriented text, not graduate analysis. Busch–Lahti–Pellonpää–Ylinen, *Quantum Measurement*: foundations of quantum physics, marginal to matrix analysis. Heinosaari–Ziman: borderline for the same reason.
Dates uncertain: none.

### Section 14: Functional, Isoperimetric, and Geometric Inequalities
Entries: 12 + 10 → foundational 11, more recent 11 (duplicates merged 0).
Moved to More recent works: Bakry–Gentil–Ledoux *Analysis and Geometry of Markov Diffusion Operators* (2014, Springer Grundlehren; added); quantitative-isoperimetry entry with Maggi *Sets of Finite Perimeter and Geometric Variational Problems* (2012, CUP; added).
Moved to Foundational works: Koldobsky *Fourier Analysis in Convex Geometry* (2005).
Duplicates merged: none (the bib2 entry "Francesco Maggi's quantitative isoperimetry is already represented ... Velichkov" is really a pointer to Velichkov; rewritten as a Velichkov entry, "Listed in full in Section 33", without reference to the classics list).
Corrections: Quantitative-isoperimetry entry: "Giovanni Alberti, Luigi Ambrosio and others" replaced by "Nicola Fusco, Francesco Maggi, Aldo Pratelli, and others" (the sharp quantitative isoperimetric inequality is Fusco–Maggi–Pratelli, 2008). Henrot (ed.) annotation: "in the classics list" → "above".
Proposed cross-section moves: none. Pointers checked: Lieb–Seiringer and Baernstein in Section 11, Serfaty in full in Section 36, Velichkov in full in Section 33 (also in 37).
Candidates for removal: none firm. Alías–Mastrolia–Rigoli, *Maximum Principles and Geometric Applications* fits better in geometric analysis (Section 52) than here.
Dates uncertain: none.

### Section 15: Core Banach and Hilbert Space Theory
Entries: 16 + 14 → foundational 16, more recent 14 (duplicates merged 0).
Moved to More recent works: Fabian–Habala–Hájek–Montesinos–Zizler *Banach Space Theory* (2011, Springer; added).
Moved to Foundational works: Kadets *A Course in Functional Analysis and Measure Theory* (Russian original 2006; English translation 2018).
Duplicates merged: none.
Corrections: Kadets year note changed from "(2018; English translation, ...)" to "(Russian original 2006; English translation 2018, ...)".
Proposed cross-section moves: none. Lukić pointer to Section 22 checked.
Candidates for removal: Jacques Simon, *Banach, Fréchet, Hilbert and Neumann Spaces* (ISTE/Wiley): little-used, borderline. Ovchinnikov, *Functional Analysis: An Introductory Course*: elementary, one of many similar introductions.
Dates uncertain: Brezis kept in Foundational works (French *Analyse fonctionnelle* 1983; the 2011 English book is a much expanded version). Willem *Functional Analysis* (2013) may derive from his French *Analyse fonctionnelle élémentaire* (2003); kept in More recent works. MacCluer (2009) kept in Foundational works.

### Section 16: Locally Convex Spaces, Duality, and Distributions
Entries: 19 + 11 → foundational 23, more recent 7 (duplicates merged 0).
Moved to More recent works: none.
Moved to Foundational works: Narici–Beckenstein *Topological Vector Spaces* (1st ed. 1985; "1985;" added); Haroske–Triebel *Distributions, Sobolev Spaces, Elliptic Equations* (2008); Grubb *Distributions and Operators* (2009); Wengenroth *Derived Functors in Functional Analysis* (2003).
Duplicates merged: none.
Corrections: first-edition year added for Narici–Beckenstein.
Proposed cross-section moves: none. (Diestel–Uhl, *Vector Measures*, and Pachl, *Uniform Spaces and Measures*, could live in Sections 18 and 4 respectively, but cross-listing is deliberate.)
Candidates for removal: none.
Dates uncertain: Bogachev–Smolyanov (2017) has a Russian original of about 2012; still after 2010, so kept in More recent works. Mitrea 2nd ed. 2018 (1st ed. 2013), recent either way.

### Section 17: Banach Space Geometry, Bases, and Operator Ideals
Entries: 18 + 17 → foundational 22, more recent 13 (duplicates merged 0; Brazitikos et al. from Section 13 merged with its pointer here).
Moved to More recent works: none.
Moved to Foundational works: Argyros–Todorčević *Ramsey Methods in Analysis* (2005); Li–Queffélec *Introduction to Banach Spaces: Analysis and Probability* (French original 2004; expanded English translation 2018); Hájek–Montesinos–Vanderwerff–Zizler *Biorthogonal Systems in Banach Spaces* (2008); Diestel–Fourie–Swart *The Metric Theory of Tensor Products* (2008).
Duplicates merged: Brazitikos–Giannopoulos–Valettas–Vritsiou, *Geometry of Isotropic Convex Bodies*: full entry moved here from Section 13, replacing the pointer "Listed in Section 13".
Corrections: Li–Queffélec bibliographic note reordered to state the 2004 French original first.
Proposed cross-section moves: none. Pointers checked: Lindenstrauss–Preiss–Tišer in Section 5, Dodos and Rosendal in Section 3, Aubrun–Szarek in Section 13.
Candidates for removal: none.
Dates uncertain: Li–Queffélec placed in Foundational works by the first-publication rule (2004 French); it is an expanded translation, so it could also be counted by its 2018 date.

### Section 18: Vector-Valued Analysis and Analysis in Banach Spaces
Entries: 8 + 5 → foundational 8, more recent 4 (duplicates merged 1).
Moved to More recent works: Hytönen–van Neerven–Veraar–Weis *Analysis in Banach Spaces I–III* (2016/2017/2023; added "(2016, 2017, 2023, Springer)").
Moved to Foundational works: Denk–Hieber–Prüss *R-boundedness, Fourier Multipliers...* (2003, AMS Memoirs).
Duplicates merged: Arendt–Batty–Hieber–Neubrander *Vector-Valued Laplace Transforms* (classics entry kept; added "(2001; 2nd ed., 2011, Birkhäuser)" with the DOI and the Section 24 pointer from the supplement's pointer entry).
Corrections: none (Kunstmann–Weis annotation "before the treatise above appeared" reworded to "before the treatise of Hytönen et al. appeared", since the treatise is now in the other part).
Proposed cross-section moves: none
Candidates for removal: Avilés et al., *Separably Injective Banach Spaces*: a pointer to Section 17 with no annotation; injective Banach spaces are Banach space geometry, not vector-valued analysis, so the cross-listing is weak. Jan van Neerven, *Stochastic Evolution Equations* lecture notes "and the γ-radonifying operator literature": not a book (ISEM lecture notes plus a body of papers); vague as an entry.
Dates uncertain: van Neerven ISEM lecture notes (2007/08), left in Foundational; Kunstmann–Weis lecture notes (LNM 1855, 2004), Foundational.

### Section 19: Banach Lattices, Positive Operators, and Ordered Structures
Entries: 10 + 5 → foundational 11, more recent 4 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Aliprantis–Tourky *Cones and Duality* (2007).
Duplicates merged: none
Corrections: none
Proposed cross-section moves: none
Candidates for removal: Avilés et al., *Separably Injective Banach Spaces* (pointer to Section 17): the claim that injectivity questions are "often lattice-theoretic in origin" is a stretch; the book is Banach space geometry (C(K)-spaces, ultraproducts), so the cross-listing in Section 19 is weak.
Dates uncertain: none

### Section 20: Banach Algebras and Commutative Harmonic Analysis of Algebras
Entries: 16 + 7 → foundational 16, more recent 7 (duplicates merged 0).
Moved to More recent works: Kaniuth–Lau *Fourier and Fourier–Stieltjes Algebras on Locally Compact Groups* (2018; added "(2018, American Mathematical Society)").
Moved to Foundational works: Dales–Aiena–Eschmeier–Laursen–Willis *Introduction to Banach Algebras, Operators, and Harmonic Analysis* (2003; removed "Earlier than the nominal boundary").
Duplicates merged: none
Corrections: none
Moves between own sections: Aiena, *Fredholm and Local Spectral Theory II* (2018): full entry moved from Section 20 to Section 21 (local spectral theory and Fredholm perturbation theory are operator theory); Section 20 now carries the short pointer "Listed in Section 21" and Section 21's former pointer was replaced by the full entry.
Proposed cross-section moves: none
Candidates for removal: Nicholas Young, *An Introduction to Hilbert Space*: not a book on Banach algebras; it is already listed in Section 15 (Core Banach and Hilbert Space Theory), where it belongs, so the Section 20 listing is redundant.
Dates uncertain: Weaver *Lipschitz Algebras* (1st ed. 1999; 2nd ed. 2018 described as a substantial rewriting), left in More recent works as the supplement placed it under the "essentially a new book" rule.

### Section 21: Operator Theory: Bounded Operators, Spectra, and Model Theory
Entries: 17 + 19 → foundational 18, more recent 18 (duplicates merged 0).
Moved to More recent works: Agler–McCarthy–Young *Operator Analysis* (2020, Cambridge University Press); Paulsen–Raghupathi *RKHS* (2016, Cambridge University Press); Simon *Operator Theory* (2015, American Mathematical Society). Year/publisher added to each.
Moved to Foundational works: Laursen–Neumann *Local Spectral Theory* (2000); Müller *Spectral Theory of Linear Operators* (1st ed. 2003, 2nd ed. 2007); Bayart–Matheron *Dynamics of Linear Operators* (2009); Martínez-Avendaño–Rosenthal *Operators on the Hardy–Hilbert Space* (2007).
Duplicates merged: none
Corrections: none. Aiena II pointer ("Listed in Section 20") replaced by the full entry moved from Section 20 (see L20). Kubrusly 2020 annotation "already listed" changed to "listed above".
Proposed cross-section moves: none
Candidates for removal: none
Dates uncertain: Sz.-Nagy–Foiaş(–Bercovici–Kérchy) *Harmonic Analysis of Operators on Hilbert Space*: first published 1967 (French), revised and enlarged edition 2010; kept in Foundational. Nikolski *Toeplitz Matrices and Operators*: supplement says 2020, PDF filename in References says 2019 (online Dec 2019, print 2020); left as 2020. Recent part grouped into "Courses and textbooks", "Function-theoretic operator theory and model spaces", "Spectral theory, Fredholm theory, and linear dynamics"; foundational part reordered so entry-level texts (Douglas, Conway Course, Halmos, Arveson, Martínez-Avendaño–Rosenthal) come first.

### Section 22: Unbounded Operators, Spectral Theory, and Mathematical Physics
Entries: 19 + 36 → foundational 23, more recent 31 (duplicates merged 1).
Moved to More recent works: Schmüdgen *Unbounded Self-adjoint Operators on Hilbert Space* (2012, Springer); Berkolaiko–Kuchment *Introduction to Quantum Graphs* (2013, American Mathematical Society). Year/publisher added.
Moved to Foundational works: Borthwick *Spectral Theory of Infinite-Area Hyperbolic Surfaces* (1st ed. 2007); Isakov *Inverse Problems for PDE* (1st ed. 1998); Kirsch *Introduction to the Mathematical Theory of Inverse Problems* (1st ed. 1996); Gustafson–Sigal *Mathematical Concepts of Quantum Mechanics* (1st ed. 2003); Takhtajan *Quantum Mechanics for Mathematicians* (2008); Folland *Quantum Field Theory* (2008). For the first four, "first ed. YYYY;" was added before the existing edition data.
Duplicates merged: Exner/Berkolaiko–Kuchment quantum-graphs entry (classics) with the supplement's pointer entry "Gregory Berkolaiko and Peter Kuchment are already in the classics list. Later graph monographs are Post ... and Mugnolo ..."; merged into one entry in More recent works carrying Post (2012) and Mugnolo (2014, listed in Section 24).
Corrections: none. Borthwick 2020 annotation "already listed" changed to "listed above".
Proposed cross-section moves:
Kapitula–Promislow, *Spectral and Dynamical Stability of Nonlinear Waves* → Section 34 (or 31): stability of nonlinear waves is nonlinear PDE/dynamics; the spectral theory is a tool.
```
* **Todd Kapitula and Keith Promislow, *Spectral and Dynamical Stability of
  Nonlinear Waves*** (2013,
  [Springer](https://doi.org/10.1007/978-1-4614-6995-7)). Evans functions,
  Hamiltonian spectral theory, and orbital stability. A systematic bridge from
  linearized spectra to the dynamics of nonlinear waves.
```
Isakov, *Inverse Problems for Partial Differential Equations* → Section 32: inverse boundary problems for PDE (no dedicated inverse-problems section exists; Section 22 is a poor fit). Could also be kept here as a cross-listing.
```
* **Victor Isakov, *Inverse Problems for Partial Differential
  Equations*** (first ed. 1998; 3rd ed., 2017, [Springer](https://doi.org/10.1007/978-3-319-51658-5)). The research reference for
  uniqueness and stability in inverse boundary problems.
```
Feldman–Salo–Uhlmann, *The Calderón Problem* → Section 32: inverse conductivity problem for an elliptic PDE.
```
* **Joel Feldman, Mikko Salo, and Gunther Uhlmann, *The Calderón
  Problem: An Introduction*** (2025, [American Mathematical Society](https://doi.org/10.1090/gsm/253),
  Graduate Studies in Mathematics). A graduate introduction to the
  inverse conductivity problem.
```
Kirsch, *An Introduction to the Mathematical Theory of Inverse Problems* → Section 25: ill-posed operator equations and regularisation, the classical-operator-methods setting of Section 25 (which already discusses integral equations and inverse problems).
```
* **Andreas Kirsch, *An Introduction to the Mathematical Theory of
  Inverse Problems*** (first ed. 1996; 3rd ed., 2021, [Springer](https://doi.org/10.1007/978-3-030-63343-1)). A graduate course in
  regularisation and inverse eigenvalue and scattering problems.
```
Schuster–Kaltenbacher–Hofmann–Kazimierski, *Regularization Methods in Banach Spaces* → Section 25: regularization of ill-posed operator equations, not spectral theory or mathematical physics.
```
* **Thomas Schuster, Barbara Kaltenbacher, Bernd Hofmann, and Kamil S.
  Kazimierski, *Regularization Methods in Banach Spaces*** (2012, [De
  Gruyter](https://doi.org/10.1515/9783110255720)). Inverse problems, convex
  regularization, and convergence rates in Banach spaces. Develops the
  geometry-dependent theory needed beyond Hilbert-space least squares.
```
(The rest of the inverse-problems cluster — Cakoni–Colton, Paternain–Salo–Uhlmann, Uhlmann (ed.) *Inside Out II*, Kirsch–Hettlich — is grouped under "#### Inverse problems and scattering" and could move to Section 32 with the above if the user prefers a single home.)
Candidates for removal: Barry Simon's survey *Schrödinger operators in the twenty-first century*: a survey article (in *Mathematical Physics 2000*), not a book. Uhlmann (ed.), *Inverse Problems and Applications: Inside Out II*: a conference/survey volume, weaker as a bibliography entry.
Dates uncertain: Teschl *Mathematical Methods in Quantum Mechanics* (1st ed. 2009, AMS GSM 99), kept in Foundational. Recent part grouped into "Courses and spectral theory", "Schrödinger operators, random and ergodic operators, and quantum graphs", "Quantum fields and many-body dynamics", "Inverse problems and scattering".

### Section 23: Operator Algebras, Operator Spaces, Free Probability, and Noncommutative Geometry
Entries: 22 + 25 → foundational 31, more recent 16 (duplicates merged 0).
Moved to More recent works: Pisier *Tensor Products of C*-Algebras and Operator Spaces* (2020, Cambridge University Press); Mingo–Speicher *Free Probability and Random Matrices* (2017, Springer). Year/publisher added.
Moved to Foundational works: Williams *Crossed Products* (2007); Blecher–Le Merdy (2004); Higson–Roe (2000); Raeburn *Graph Algebras* (2005); Khalkhali *Basic Noncommutative Geometry* (1st ed. 2009; "first ed. 2009;" added); Connes–Marcolli (2008); Roe *Lectures on Coarse Geometry* (2003); Rørdam–Larsen–Laustsen (2000); Sinclair–Smith (2008); Timmermann (2008); Rørdam–Størmer (2002).
Duplicates merged: none
Corrections: removed references to the other file / nominal boundary: Williams ("Slightly before the nominal boundary"), Blecher–Le Merdy ("and absent from the classics list"), Higson–Roe ("Earlier than the nominal boundary, and still the book" → "Still the book").
Proposed cross-section moves: none
Candidates for removal: "Masamichi Takesaki's modular theory" (part of the Strătilă–Zsidó entry): not a specific book (presumably Takesaki's LNM 128, *Tomita's Theory of Modular Hilbert Algebras*, 1970); vague as written. Jorgensen–Tian *Non-Commutative Analysis*: specialised and loosely focused; marginal for a core bibliography.
Dates uncertain: none. Foundational part reordered by topic (C*/von Neumann basics, K-theory and crossed products, subfactors and quantum groups, operator spaces, free probability, NCG and index theory); recent part grouped into "C*-algebras, classification, and dynamics", "Operator spaces, tensor products, and free probability", "Index theory, quantum symmetry, and noncommutative geometry".

### Section 24: Semigroups, Evolution Equations, and Functional Calculus
Entries: 14 + 13 → foundational 16, more recent 11 (duplicates merged 0).
Moved to More recent works: Prüss–Simonett *Moving Interfaces* (2016); Hytönen–van Neerven–Veraar–Weis *Analysis in Banach Spaces II–III* (2017, 2023).
Moved to Foundational works: Engel–Nagel *A Short Course on Operator Semigroups* (2006); Ouhabaz *Analysis of Heat Equations on Domains* (2005); Tucsnak–Weiss *Observation and Control for Operator Semigroups* (2009); Coron *Control and Nonlinearity* (2007).
Duplicates merged: none.
Corrections: Barbu (2010) annotation "Updates Barbu's earlier book in the classics list" reworded to name the earlier book; intro paragraph rewritten (classics section had no intro).
Proposed cross-section moves: Choulli *Applications of Elliptic Carleman Inequalities* → Section 33: elliptic unique continuation and inverse problems, not semigroup theory. Lindquist–Picci *Linear Stochastic Systems* → Section 8: stationary processes and stochastic systems (alternatively a removal candidate, see below).
```
* **Mourad Choulli, *Applications of Elliptic Carleman Inequalities to
  Cauchy and Inverse Problems*** (2016, [Springer](https://doi.org/10.1007/978-3-319-33642-8)). Carleman estimates
  as a tool for unique continuation and inverse problems.
* **Anders Lindquist and Giorgio Picci, *Linear Stochastic Systems: A
  Geometric Approach to Modeling, Estimation and Identification*** (2015,
  [Springer](https://doi.org/10.1007/978-3-662-45750-4)). Stationary
  processes, realization, prediction, and state-space geometry. Included for
  its Hilbert-space and operator-theoretic foundations of stochastic systems.
```
Candidates for removal: "Jerome A. Goldstein and others on nonlinear semigroups": a vague pointer rather than a book (the Barbu book it points to is listed in Section 35). Lindquist–Picci: systems/estimation engineering monograph, marginal for an analysis bibliography.
Dates uncertain: none.

### Section 25: Integral Equations and Classical Operator Methods
Entries: 11 + 15 → foundational 17, more recent 9 (duplicates merged 0).
Moved to More recent works: none.
Moved to Foundational works: Hsiao–Wendland *Boundary Integral Equations* (1st ed. 2008; 2nd ed. 2021 data kept); Sauter–Schwab *Boundary Element Methods* (German *Randelementmethoden*, 2004; English 2011); Capogna–Kenig–Lanzani *Harmonic Measure* (2005); Ammari–Kang–Lee *Layer Potential Techniques in Spectral Analysis* (2009); Fokas *A Unified Approach to Boundary Value Problems* (2008); Hackbusch *Hierarchical Matrices* (German *Hierarchische Matrizen*, 2009; English 2015).
Duplicates merged: none.
Corrections: added first-edition / original-language dates to Hsiao–Wendland, Sauter–Schwab, and Hackbusch to explain their placement.
Proposed cross-section moves: none.
Candidates for removal: "Vladimir Maz'ya and others on boundary integral methods in nonsmooth domains": a vague pointer, not a book. Hackbusch *Hierarchical Matrices* and Sauter–Schwab *Boundary Element Methods*: primarily numerical analysis; retain only if numerical boundary-element theory is in scope.
Dates uncertain: Hackbusch and Sauter–Schwab placed by the date of the German original; the English editions are substantially expanded and could be argued to count as new books (2015, 2011), in which case they would go back to More recent works.

### Section 26: Sobolev Spaces, Smoothness Scales, and Interpolation
Entries: 25 + 15 → foundational 24, more recent 16 (duplicates merged 0).
Moved to More recent works: Sawano *Theory of Besov Spaces* (2018); Harjulehto–Hästö *Orlicz Spaces and Generalized Orlicz Spaces* (2019); Diening–Harjulehto–Hästö–Růžička *Lebesgue and Sobolev Spaces with Variable Exponents* (2011); Di Nezza–Palatucci–Valdinoci *Hitchhiker's Guide* (2012).
Moved to Foundational works: Haroske–Triebel *Distributions, Sobolev Spaces, Elliptic Equations* (2008); Demengel–Demengel *Functional Spaces* (French original 2007); Maz'ya–Shaposhnikova *Theory of Sobolev Multipliers* (2009).
Duplicates merged: none.
Corrections: intro paragraph written (classics section had none). Leoni *First Course in Sobolev Spaces* (1st ed. 2009) and Brezis (French *Analyse fonctionnelle*, 1983) kept in Foundational works by first-publication date.
Proposed cross-section moves: none.
Candidates for removal: Di Nezza–Palatucci–Valdinoci *Hitchhiker's Guide*: a survey article in a journal, not a book (influential; keep if articles are admitted). Kosmol–Müller-Wichards *Optimization in Function Spaces*: specialist optimization monograph, marginal for this section.
Dates uncertain: Pick–Kufner–John–Fučík *Function Spaces* left in More recent works as a substantially new 2nd edition (2013); the first edition (Kufner–John–Fučík) dates from 1977. Kosmol–Müller-Wichards (2011) left in More recent works; not certain whether it reworks an earlier German book.

### Section 27: Fourier Analysis and Real-Variable Harmonic Analysis
Entries: 29 + 17 → foundational 24, more recent 22 (duplicates merged 0).
Moved to More recent works: Cruz-Uribe–Martell–Pérez *Weights, Extrapolation* (2011); Lerner–Nazarov *Intuitive Dyadic Calculus* (2019); Muscalu–Schlag *Classical and Multilinear Harmonic Analysis* (2013); Demeter *Fourier Restriction, Decoupling* (2020); Mattila *Fourier Analysis and Hausdorff Dimension* (2015); Hytönen–van Neerven–Veraar–Weis *Analysis in Banach Spaces I–III* (2016–2023).
Moved to Foundational works: Tao–Vu *Additive Combinatorics* (2006).
Duplicates merged: none.
Corrections: classics subheadings became `####`; "Foundational and research monographs" renamed "Research monographs and references" to avoid clashing with the new `###` heading. Recent part grouped under three `####` headings (Courses; Real-variable theory: research monographs; Restriction, geometric, and additive-combinatorial methods). Removed "in the classics list" from the Grafakos *Fundamentals* annotation and changed "the dyadic methods of the classics list" to "the dyadic methods listed below" in Pereyra–Ward. Intro rewritten to drop "already in the classics list".
Proposed cross-section moves: Brémaud *Fourier Analysis and Stochastic Processes* → Section 8: stationary processes and spectral representation are probability.
```
* **Pierre Brémaud, *Fourier Analysis and Stochastic Processes*** (2014,
  [Springer](https://doi.org/10.1007/978-3-319-09590-5)). Spectral
  representations of stationary processes, random signals, and Fourier methods
  in probability. Connects abstract stochastic-process theory with transform
  techniques.
```
Candidates for removal: Tointon *Introduction to Approximate Groups*, Tao *Hilbert's Fifth Problem*, Tao *Expansion in Finite Simple Groups of Lie Type*: group theory and combinatorics rather than real-variable harmonic analysis (if kept, Section 28 is a more natural home for the first two; Section 28 already points to *Expansion* here). Lerner–Nazarov *Intuitive Dyadic Calculus*: a survey article (Expositiones Mathematicae), not a book. Pereyra–Ward: Student Mathematical Library, close to undergraduate level.
Dates uncertain: none.

### Section 28: Abstract Harmonic Analysis on Groups
Entries: 16 + 25 → foundational 22, more recent 19 (duplicates merged 0).
Moved to More recent works: Kaniuth–Lau *Fourier and Fourier–Stieltjes Algebras on Locally Compact Groups* (2018).
Moved to Foundational works: Bekka–de la Harpe–Valette *Kazhdan's Property (T)* (2008); Hall *Lie Groups, Lie Algebras, and Representations* (1st ed. 2003); Bump *Lie Groups* (1st ed. 2004); Goodman–Wallach *Symmetry, Representations, and Invariants* (2009); Terras *Harmonic Analysis on Symmetric Spaces* (1st ed. 1985–1988); Faraut *Analysis on Lie Groups* (2008); Kirillov *Lectures on the Orbit Method* (2004).
Duplicates merged: none.
Corrections: added first-edition dates to Hall, Bump, and Terras (*Harmonic Analysis on Symmetric Spaces*) to explain their placement; intro written from both sources (classics section had none).
Proposed cross-section moves: none.
Candidates for removal: Terras *Zeta Functions of Graphs*: spectral graph theory, marginal to harmonic analysis on groups. Meinrenken *Clifford Algebras and Lie Theory*: algebraic Lie theory rather than harmonic analysis.
Dates uncertain: Terras *Zeta Functions of Graphs* is dated 2011 in the entry; Cambridge gives the print publication year as 2010 (and the local PDF filename has 2010). Left unchanged; either date puts it in More recent works.

### Section 29: Wavelets, Frames, Time–Frequency Analysis, and Sampling
Entries: 14 + 12 → foundational 11, more recent 14 (duplicates merged 1).
Moved to More recent works: Olevskii–Ulanovskii *Functions with Disconnected Spectrum* pointer entry (2016); Candès–Donoho / Kutyniok–Labate *Shearlets* pointer entry (2012, merged); Foucart–Rauhut *A Mathematical Introduction to Compressive Sensing* (2013).
Moved to Foundational works: none.
Duplicates merged: Kutyniok–Labate (eds.) *Shearlets*: the classics pointer entry "Emmanuel Candès, David Donoho, and the curvelet/shearlet literature, accessible through Kutyniok–Labate" was merged into the full CKMA-bib2.md entry (data, link and annotation kept; the curvelet/shearlet pointer appended to the annotation).
Corrections: added (2016, American Mathematical Society, University Lecture Series) to Olevskii–Ulanovskii and (2013, Birkhäuser, Applied and Numerical Harmonic Analysis) to Foucart–Rauhut; intro written from both sources (classics section had none).
Proposed cross-section moves: none.
Candidates for removal: "Yurii Lyubarskii, Alexander Olevskii, and the Russian sampling literature": a pointer rather than a book entry (the Olevskii–Ulanovskii book inside it is fine). Adcock–Hansen *Compressive Imaging* and Flandrin *Explorations in Time-Frequency Analysis*: largely signal processing; marginal for an analysis bibliography.
Dates uncertain: none.

### Section 30: Distributions, Pseudodifferential Operators, Microlocal and Semiclassical Analysis
Entries: 19 + 16 → foundational 20, more recent 14 (duplicates merged 0). One entry (Seiler) moved to Section 32.
Moved to More recent works: Lerner *Metrics on the Phase Space* (2010, Birkhäuser); Zworski *Semiclassical Analysis* (2012, AMS); Dyatlov–Zworski *Mathematical Theory of Scattering Resonances* (2019, AMS); Bony / Bahouri–Chemin–Danchin *Fourier Analysis and Nonlinear PDE* (2011, Springer).
Moved to Foundational works: Métivier *Para-Differential Calculus* (2008); Pham *Singularities of Integrals* (French original 2005); Alinhac–Gérard *Pseudo-differential Operators and the Nash–Moser Theorem* (French original 1991, English 2007); Helffer–Nier *Hypoelliptic Estimates* (2005); Villani *Hypocoercivity* (2009).
Duplicates merged: none
Corrections: Ivrii 2019 entry: "the 1998 book already listed in the classics bibliography" replaced by an explicit pointer to Ivrii's 1998 *Microlocal Analysis and Precise Spectral Asymptotics*, listed in Sections 50 and 53. Lerner *Carleman Inequalities*: "in the classics bibliography" replaced by "listed above". Paternain–Salo–Uhlmann pointer to Section 22 checked (correct; it is also mentioned in Section 53).
Moves within own sections: Seiler *Involution: The Formal Theory of Differential Equations* (2010) moved from Section 30 to Section 32 ("More recent works"): formal integrability and involution are general PDE theory, not microlocal analysis.
Proposed cross-section moves: Smirnov *Analytic Tools for Feynman Integrals* → Section 50: if kept at all, its content (parameter integrals, Mellin–Barnes representations, asymptotic expansion) fits asymptotic analysis better than microlocal analysis.
```
* **Vladimir A. Smirnov, *Analytic Tools for Feynman Integrals*** (2012,
  [Springer](https://doi.org/10.1007/978-3-642-34886-0)). Parameter integrals,
  dimensional regularization, Mellin–Barnes representations, and asymptotic
  expansion. A specialised analytic reference for integrals arising in quantum
  field theory.
```
Candidates for removal: Smirnov *Analytic Tools for Feynman Integrals*: a physics-oriented computational handbook for quantum field theory integrals, not a book of mathematical analysis at graduate/research level in the CKMA sense. Seiler *Involution* (now in Section 32): weak candidate; largely formal/algebraic theory of differential systems with computer-algebra emphasis.
Dates uncertain: Guillemin–Sternberg combined entry (*Geometric Asymptotics* 1977, *Semi-Classical Analysis* 2013) kept in Foundational by the earlier book.

### Section 31: Ordinary Differential Equations and Dynamical Systems
Entries: 21 + 31 → foundational 31, more recent 21 (duplicates merged 0).
Moved to More recent works: Teschl *Ordinary Differential Equations and Dynamical Systems* (2012, AMS).
Moved to Foundational works: Meiss *Differential Dynamical Systems* (1st ed. 2007); Bonatti–Díaz–Viana *Dynamics Beyond Uniform Hyperbolicity* (2005); Hanßmann *Local and Semi-Local Bifurcations* (2007); Coornaert *Topological Dimension and Dynamical Systems* (French original 2005); J. C. Robinson *Infinite-Dimensional Dynamical Systems* (2001); Chepyzhov–Vishik *Attractors* (2002); Arnold–Kozlov–Neishtadt *Mathematical Aspects of Classical and Celestial Mechanics* (1st ed. 1985 Russian / 1988 English); Kuksin *Analysis of Hamiltonian PDEs* (2000); Berti *Nonlinear Oscillations of Hamiltonian PDEs* (2007); Moser–Zehnder *Notes on Dynamical Systems* (2005); Sanders–Verhulst–Murdock *Averaging Methods* (1st ed. 1985).
Duplicates merged: none
Corrections: none. Pointers to Section 10 (Fisher–Hasselblatt, Alves, Bonatti–Díaz–Viana, Viana, Katok–Niţică) and to Section 50 (Sanders–Verhulst–Murdock) checked: correct.
Proposed cross-section moves: Coornaert *Topological Dimension and Dynamical Systems* → Section 10: dimension theory, mean dimension and topological dynamics belong with ergodic theory and dynamics rather than ODE.
```
* **Michel Coornaert, *Topological Dimension and Dynamical Systems*** (2015;
  English translation, [Springer](https://doi.org/10.1007/978-3-319-19794-4)).
  Dimension theory, mean dimension, and topological dynamics. Useful for
  analysts studying infinite-dimensional phenomena in dynamical systems.
```
Candidates for removal: Hydon *Difference Equations by Differential Equation Methods*: weak candidate; symmetry/integrability methods for difference equations are peripheral to graduate analysis. Jeffrey *Modeling with Nonsmooth Dynamics*: weak candidate; modelling-oriented.
Dates uncertain: Coornaert: French original *Dimension topologique et systèmes dynamiques* (SMF, 2005) used for classification; if the 2015 English edition is taken as the date, move to More recent works. Meiss classified by first edition (2007), not the cited revised edition (2017).

### Section 32: Partial Differential Equations: General and Linear Theory
Entries: 17 + 9 (+1 moved in from Section 30) → foundational 19, more recent 8 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Sauvigny *Partial Differential Equations* (German original 2004–2005, 1st English ed. 2006); Roubíček *Nonlinear Partial Differential Equations with Applications* (1st ed. 2005).
Duplicates merged: none
Corrections: none. Pointers to Section 16 (Mitrea) and Section 33 (Fernández-Real–Ros-Oton) checked: correct.
Moves within own sections: Seiler *Involution* (2010) received from Section 30 into "More recent works".
Proposed cross-section moves: Roubíček *Nonlinear Partial Differential Equations with Applications* → Section 35: a monotone-operator, nonlinear functional-analytic treatment, out of place under "General and Linear Theory".
```
* **Tomáš Roubíček, *Nonlinear Partial Differential Equations with
  Applications*** (2nd ed., 2013,
  [Birkhäuser](https://doi.org/10.1007/978-3-0348-0513-1)). Monotone
  operators, weak solutions, compactness, and nonlinear evolution with
  applications. A graduate-to-research synthesis of functional-analytic PDE
  methods.
```
Candidates for removal: Seiler *Involution*: weak candidate (formal/algebraic theory with computer-algebra emphasis; see L30).
Dates uncertain: none

### Section 33: Elliptic and Parabolic Equations: Regularity, Free Boundaries, and Viscosity Solutions
Entries: 26 + 26 → foundational 29, more recent 23 (duplicates merged 0).
Moved to More recent works: Petrosyan–Shahgholian–Uraltseva *Regularity of Free Boundaries in Obstacle-Type Problems* (2012, AMS); Figalli *The Monge–Ampère Equation and Its Applications* (2017, EMS).
Moved to Foundational works: Vázquez *The Porous Medium Equation* (2007); Vázquez *Smoothing and Decay Estimates* (2006); Urbano *The Method of Intrinsic Scaling* (2008); Quittner–Souplet *Superlinear Parabolic Problems* (1st ed. 2007); Cannarsa–Sinestrari *Semiconcave Functions* (2004).
Duplicates merged: none
Corrections: Nam Q. Le entry: "the graduate treatments already in the classics bibliography" replaced by "the graduate treatments of Gutiérrez and Figalli listed in this section". Pointers to Sections 8, 25, 26, 32 checked: correct.
Proposed cross-section moves: none
Candidates for removal: none
Dates uncertain: Le Dret: French original 2013, English 2018; classified as recent either way. Lindqvist *Notes on the p-Laplace Equation*: first circulated 2006 (Jyväskylä report), kept in Foundational.

### Section 34: Hyperbolic Equations, Conservation Laws, Dispersive PDE, Fluids, and Kinetic Theory
Entries: 27 + 27 → foundational 35, more recent 19 (duplicates merged 0).
Moved to More recent works: Bahouri–Chemin–Danchin *Fourier Analysis and Nonlinear PDE* (2011, Springer); Koch–Tataru–Vişan *Dispersive Equations and Nonlinear Waves* (2014, Birkhäuser); Lemarié-Rieusset *The Navier–Stokes Problem in the 21st Century* (2016, CRC Press).
Moved to Foundational works: Chemin–Desjardins–Gallagher–Grenier *Mathematical Geophysics* (2006); Holden–Risebro *Front Tracking* (1st ed. 2002); Saint-Raymond *Hydrodynamic Limits* (2009); Perthame *Transport Equations in Biology* (2007) with *Parabolic Equations in Biology* (2015); Benzoni-Gavage–Serre *Multidimensional Hyperbolic PDE* (2007); Christodoulou *Formation of Black Holes* (2009); Ringström *Cauchy Problem in General Relativity* (2009); Choquet-Bruhat *General Relativity and the Einstein Equations* (2009); Feireisl–Novotný *Singular Limits* (1st ed. 2009); Foias–Manley–Rosa–Temam *Navier–Stokes Equations and Turbulence* (2001); LeFloch *Hyperbolic Systems of Conservation Laws* (2002).
Duplicates merged: none
Corrections: Perthame entry: removed "and is not in the classics list". The three classics subheadings became `####` groups in Foundational works; the same three groups are used in More recent works.
Proposed cross-section moves: none
Candidates for removal: Majda *Introduction to Turbulent Dynamical Systems in Complex Systems*: weak candidate; applied/complex-systems modelling rather than mathematical analysis of PDE.
Dates uncertain: Perthame combined entry (2007 and 2015) classified by the earlier book. Alinhac combined entry (*Geometric Analysis of Hyperbolic Differential Equations* 1995, *Hyperbolic PDE* 2009) kept in Foundational. Boyer–Fabrie (2013) kept recent although a shorter French precursor appeared in 2006; the English book is substantially expanded. Gallagher–Saint-Raymond–Texier: printed date 2014 retained (possibly late 2013); recent either way.

### Section 35: Nonlinear Functional Analysis, Monotone Operators, and Fixed Points
Entries: 14 + 13 → foundational 19, more recent 8 (duplicates merged 0).
Moved to More recent works: Bauschke–Combettes *Convex Analysis and Monotone Operator Theory in Hilbert Spaces* (2011; "(2011, Springer)" added).
Moved to Foundational works: Simons *From Hahn–Banach to Monotonicity* (1st ed. 1998), Burachik–Iusem *Set-Valued Mappings* (2008), Drábek–Milota *Methods of Nonlinear Analysis* (1st ed. 2007), Kielhöfer *Bifurcation Theory* (1st ed. 2004), Buffoni–Toland *Analytic Theory of Global Bifurcation* (2003), Chang *Methods in Nonlinear Analysis* (2005).
Duplicates merged: none
Corrections: none (removed "already in the classics list" wording from the intro; cross-pointers to Section 12 checked).
Proposed cross-section moves: none
Candidates for removal: "Jean Mawhin's work on coincidence degree" (inside the Lloyd entry): not a specific book; consider replacing by Mawhin, *Topological Degree Methods in Nonlinear Boundary Value Problems* (CBMS 40, 1979).
Dates uncertain: Barbu entry combines *Nonlinear Semigroups and Differential Equations in Banach Spaces* (1976) with *Nonlinear Differential Equations of Monotone Types in Banach Spaces* (2010); kept in Foundational by the earlier book.

### Section 36: Calculus of Variations, Γ-Convergence, and Homogenization
Entries: 23 + 15 → foundational 29, more recent 9 (duplicates merged 0).
Moved to More recent works: Armstrong–Kuusi–Mourrat *Quantitative Stochastic Homogenization* (2019; "(2019, Springer)" added).
Moved to Foundational works: Attouch–Buttazzo–Michaille *Variational Analysis in Sobolev and BV Spaces* (1st ed. 2006), Sandier–Serfaty *Vortices* (2007), Tarantello *Selfdual Gauge Field Vortices* (2008), Henrot–Pierre *Shape Variation and Optimization* (French original *Variation et optimisation de formes*, 2005), Pavliotis–Stuart *Multiscale Methods* (2008), Milton *The Theory of Composites* (2002), Agrachev–Sachkov *Control Theory from the Geometric Viewpoint* (2004).
Duplicates merged: none
Corrections: none (intro rewritten without "already in the classics list").
Proposed cross-section moves: none
Candidates for removal: the phrase "and the companion on Sobolev spaces" in the Fonseca–Leoni entry: no companion Sobolev volume by Fonseca–Leoni has appeared as far as I know (Leoni's separate *A First Course in Sobolev Spaces* exists); keep the entry, drop or fix the phrase.
Dates uncertain: Tartar *The General Theory of Homogenization* (Springer UMI Lecture Notes 7; copyright 2009, often cited 2010) kept in Foundational. Henrot–Pierre moved by its 2005 French original; the 2018 English edition is substantially expanded, so it could alternatively stay in More recent works.

### Section 37: Geometric Measure Theory, BV, Rectifiability, and Currents
Entries: 17 + 6 → foundational 14, more recent 9 (duplicates merged 0).
Moved to More recent works: Maggi *Sets of Finite Perimeter* (2012, CUP), Tolsa *Analytic Capacity* (2014, Birkhäuser), Mattila *Fourier Analysis and Hausdorff Dimension* (2015, CUP), Bishop–Peres *Fractals in Probability and Analysis* (2017, CUP); year/publisher added.
Moved to Foundational works: David *Singular Sets of Minimizers for the Mumford–Shah Functional* (2005).
Duplicates merged: none
Corrections: none (intro rewritten without "already in the classics list").
Proposed cross-section moves: none
Candidates for removal: "Wendell H. Fleming's notes and papers" (first half of the Fleming/Whitney entry): not a book; the Whitney half is fine.
Dates uncertain: none

### Section 38: Potential Theory and Capacity
Entries: 16 + 8 → foundational 17, more recent 7 (duplicates merged 1; plus 1 entry moved in from Section 39).
Moved to More recent works: Björn–Björn *Nonlinear Potential Theory on Metric Spaces* (2011, EMS; DOI taken from CKMA-bib2.md).
Moved to Foundational works: Capogna–Kenig–Lanzani *Harmonic Measure* (2005), Bogdan et al. *Potential Analysis of Stable Processes* (2009).
Duplicates merged: Björn–Björn (classics entry + CKMA-bib2.md pointer entry "already in the classics list"); the pointer's remark "The heat-kernel side is in Section 39" moved into the intro.
Moved between own sections: Bovier–den Hollander *Metastability: A Potential-Theoretic Approach* (2015) moved here from Section 39 (its annotation stresses capacities and potential theory).
Corrections: none
Proposed cross-section moves: none
Candidates for removal: "Alexander Volberg and others on analytic capacity; see Tolsa in Section 37": not a book entry, only a pointer.
Dates uncertain: Helms *Potential Theory* is the 2009 Universitext book (2nd ed. 2014), largely distinct from his 1969 *Introduction to Potential Theory*; Foundational either way.

### Section 39: Metric Measure Spaces, Dirichlet Forms, Heat Kernels, Optimal Transport, and Fractals
Entries: 24 + 16 → foundational 16, more recent 23 (duplicates merged 0; 1 entry moved to Section 38).
Moved to More recent works: Heinonen–Koskela–Shanmugalingam–Tyson (2015, CUP), Björn–Björn (2011, EMS, DOI from CKMA-bib2.md), Chen–Fukushima (2012, Princeton UP), Bakry–Gentil–Ledoux (2014, Springer), Santambrogio (2015, Birkhäuser), Ambrosio–Brué–Semola (2021, Springer), Gigli–Pasqualetto (2020, Springer), Figalli–Glaudo (2021, EMS), Figalli *Monge–Ampère* (2017, EMS), Peyré–Cuturi (2019, Now Publishers); year/publisher added.
Moved to Foundational works: Falconer *Fractal Geometry* (1st ed. 1990), Lapidus–van Frankenhuijsen *Fractal Geometry, Complex Dimensions and Zeta Functions* (1st ed. 2006).
Duplicates merged: none
Moved between own sections: Bovier–den Hollander *Metastability* → Section 38.
Corrections: none (intro rewritten without "already in the classics list"). The three existing ### subheadings became #### in Foundational works; the same three groups (second renamed "Dirichlet forms, heat kernels, graphs, and fractals") are used in More recent works.
Proposed cross-section moves: none
Candidates for removal: none
Dates uncertain: Barlow entry combines *Diffusions on Fractals* (1998) with *Random Walks and Heat Kernels on Graphs* (2017); kept in Foundational by the earlier book.

### Section 40: One Complex Variable: Graduate Courses
Entries: 19 + 9 → foundational 22, more recent 6 (duplicates merged 0).
Moved to More recent works: Simon *Basic/Advanced Complex Analysis* (2015, AMS; added).
Moved to Foundational works: Ullrich *Complex Made Simple* (2008), Freitag–Busam *Complex Analysis* (German original 1993), Rodríguez–Kra–Gilman (1st ed. 2002), Freitag *Complex Analysis 2* (German original *Funktionentheorie 2*, 2009).
Duplicates merged: none
Corrections: none (intro rewritten).
Proposed cross-section moves: none
Candidates for removal: none
Dates uncertain: Burckel entry combines *An Introduction to Classical Complex Analysis* (1979) with *Classical Analysis in the Complex Plane* (2021); kept in Foundational by the earlier book. Freitag *Complex Analysis 2* moved by the 2009 German original (fairly confident).

### Section 41: Classical Function Theory: Entire and Meromorphic Functions, Value Distribution
Entries: 18 + 7 → foundational 20, more recent 5 (duplicates merged 0).
Moved to More recent works: none
Moved to Foundational works: Gromak–Laine–Shimomura *Painlevé Differential Equations in the Complex Plane* (2002), Hough–Krishnapur–Peres–Virág *Zeros of Gaussian Analytic Functions* (2009).
Duplicates merged: none
Corrections: Gromak–Laine–Shimomura annotation: "the Riemann–Hilbert treatise already in the classics list" → "the Riemann–Hilbert treatise of Fokas, Its, Kapaev, and Novokshenov (Section 51)". Intro rewritten without "already in the classics list".
Proposed cross-section moves: none
Candidates for removal: "Aleksandr Ostrowski's and Gábor Halász's collected papers": Ostrowski's *Collected Mathematical Papers* exist, but I know of no published collected papers of Halász (dubious); also not a book of function theory as such. "Wilhelm Blaschke, Georges Valiron, and the classical French and German monographs": vague; only Valiron's *Lectures on the General Theory of Integral Functions* is a specific book.
Dates uncertain: none

### Section 42: Hardy, Bergman, and Model Spaces; Operators on Analytic Function Spaces
Entries: 18 + 14 → foundational 20, more recent 15 (duplicates merged 0). Three paired classics entries were split into two entries each (18 classics lines → 21 books), because their two halves fall on different sides of 2010.
Moved to More recent works: Nikolski *Hardy Spaces* (2019; French original 2012); Garcia–Mashreghi–Ross *Introduction to Model Spaces and Their Operators* (2016; split from the Cima–Matheson–Ross entry); Paulsen–Raghupathi *Introduction to the Theory of RKHS* (2016; split from the Aronszajn entry); Zhu *Analysis on Fock Spaces* (2012; split from the Zhu *Operator Theory in Function Spaces* entry).
Moved to Foundational works: Mashreghi *Representation Theorems in Hardy Spaces* (2009); Duren–Schuster *Bergman Spaces* (2004); Zhu *Spaces of Holomorphic Functions in the Unit Ball* (2005).
Duplicates merged: none.
Corrections: "Nathan Aronszajn" corrected to "Nachman Aronszajn"; this item is the 1950 Trans. Amer. Math. Soc. memoir, not a book, which the entry now says. Removed "slightly earlier than the nominal boundary" (Duren–Schuster) and "already listed" (Arcozzi et al.), which referred to the two-file setup. Split entries got short adjusted annotations that point to each other.
Proposed cross-section moves: none.
Candidates for removal: Nachman Aronszajn, *Theory of Reproducing Kernels*: a journal memoir, not a book; keep only if articles are acceptable as an exception (it is the founding paper).
Dates uncertain: none.

### Section 43: Univalent Functions, Conformal Mapping, and Extremal Methods
Entries: 14 + 8 → foundational 14, more recent 8 (duplicates merged 0).
Moved to More recent works: Marshall *Complex Analysis* (2019); Kang–Makarov lecture notes (identified as Astérisque 353, 2013).
Moved to Foundational works: Graham–Kohr *Geometric Function Theory in One and Higher Dimensions* (2003); Stephenson *Introduction to Circle Packing* (2005).
Duplicates merged: none.
Corrections: Marshall annotation "by an author of the preceding" changed to "by a coauthor of *Harmonic Measure*", because the entry no longer follows Garnett–Marshall. The Kang–Makarov entry now names the Astérisque volume.
Proposed cross-section moves: none.
Candidates for removal: Ranjan Roy, *Elliptic and Modular Functions from Gauss to Dedekind to Hecke*: the link to Section 43 is weak (a history of elliptic and modular functions; the annotation's claim that they "still organise extremal problems" is thin). The cross-listing pointer could be dropped and the book kept in Section 2. Kang–Makarov "lecture notes": not a book; vague reference.
Dates uncertain: Kang–Makarov: the date assumes the intended notes are *Gaussian Free Field and Conformal Field Theory*, Astérisque 353 (2013); their later notes on Riemann surfaces are also post-2010.

### Section 44: Riemann Surfaces, Quasiconformal Mappings, and Teichmüller Theory
Entries: 20 + 13 → foundational 20, more recent 13 (duplicates merged 0).
Moved to More recent works: Donaldson *Riemann Surfaces* (2011); Farb–Margalit *A Primer on Mapping Class Groups* (2012).
Moved to Foundational works: Papadopoulos (ed.) *Handbook of Teichmüller Theory* (vol. I 2007; continuing); Kapovich *Hyperbolic Manifolds and Discrete Groups* (2001).
Duplicates merged: none. Hubbard volume 1 (classics) and volume 2 (2016, from the supplement) are kept as separate entries because the volumes appeared ten years apart. Volume 2's note now reads "Volume 1 is listed under Foundational works".
Corrections: "Volume 1 is in the classics list" reworded (see above). Section-intro phrases about "the classics list" removed.
Proposed cross-section moves: none. (Branner–Fagella and Bonk–Meyer belong to both 44 and 46; Bonk–Meyer is already cross-listed from 46.)
Candidates for removal: "Juha Heinonen and Pekka Koskela's work on quasiconformality in metric spaces": not a book entry; it points to a research programme, and Heinonen's *Lectures on Analysis on Metric Spaces* is listed in full in Section 39. Could be reduced to a pointer.
Dates uncertain: Marden *Hyperbolic Manifolds* (2016) is substantially a revised second edition of his *Outer Circles* (2007). It is kept in More recent works as an essentially new book. The Buser/Bergeron entry is kept in More recent works because its listed book is Bergeron (2016); Buser (1992) is only mentioned.

### Section 45: Several Complex Variables, Complex Manifolds, Pluripotential Theory, and CR Analysis
Entries: 38 + 16 → foundational 37, more recent 17 (duplicates merged 1). The classics entry pairing Ohsawa's *Analysis of Several Complex Variables* with *L^2 Approaches* was split, so 38 classics lines → 39 books; the *L^2 Approaches* half was merged with the supplement's entry.
Moved to More recent works: Lebl *Tasty Bits of Several Complex Variables* (online notes, 2010s); Straube *Lectures on the L^2-Sobolev Theory of the d-bar-Neumann Problem* (2010); Ohsawa *L^2 Approaches* (2015); Forstnerič *Stein Manifolds and Holomorphic Mappings* (2011); Guedj–Zeriahi *Degenerate Complex Monge–Ampère Equations* (2017); Noguchi–Winkelmann *Nevanlinna Theory in Several Complex Variables and Diophantine Approximation* (2014).
Moved to Foundational works: Berhanu–Cordaro–Hounie *An Introduction to Involutive Structures* (2008) → CR subsection; Jarnicki–Pflug *First Steps in SCV: Reinhardt Domains* (2008) → Foundations subsection; Tian *Canonical Metrics in Kähler Geometry* (2000) and Kołodziej *The Complex Monge–Ampère Equation and Pluripotential Theory* (2005) → complex manifolds/pluripotential subsection.
Duplicates merged: Ohsawa *L^2 Approaches in Several Complex Variables* (classics paired entry + supplement 2nd ed. 2018 entry). The merged entry keeps the supplement's data and link, notes the 2015 first edition, and keeps the classics description.
Corrections: Haslinger title "∂-Neumann" corrected to "∂̄-Neumann" (d-bar; the bar was missing). The existing ### subheadings were demoted to ####. The More recent works part was grouped under four #### headings: Graduate courses; The d-bar equation and L^2 methods; Oka theory, pluripotential theory, and Kähler geometry; CR geometry.
Proposed cross-section moves: none. (Székelyhidi, Boucksom–Eyssidieux–Guedj, Guedj (ed.) and Tian are Kähler geometry and could also sit in Section 52, but they fit here as well.)
Candidates for removal: Wiegerinck–Korevaar and Boas lecture notes: unpublished lecture notes without stable bibliographic data, so the entry is hard to verify. Keep only if freely available notes are acceptable as an exception.
Dates uncertain: Lebl *Tasty Bits* (first public version around 2014; no year added). Demailly *Analytic Methods in Algebraic Geometry* (book 2012, Higher Education Press/International Press, but a version of the notes circulated from the 1990s) and Demailly *Complex Analytic and Differential Geometry* (online since 1997; never formally published): both left in Foundational works as in the source. Laurent-Thiébaut *Holomorphic Function Theory in Several Variables* (English 2011; French original 1997): kept Foundational by first publication. Wiegerinck–Korevaar and Boas notes: undated, left in Foundational works.

### Section 46: Complex Dynamics
Entries: 10 + 10 → foundational 8, more recent 11 (duplicates merged 1).
Moved to More recent works: Przytycki–Urbański *Conformal Fractals* (2010); Urbański–Roy–Munday *Non-Invertible Dynamical Systems* (2022–); *Holomorphic Dynamical Systems* (2010; merged, see below); Abate *Holomorphic Dynamics on Hyperbolic Riemann Surfaces* (De Gruyter, 2020s).
Moved to Foundational works: Mauldin–Urbański *Graph Directed Markov Systems* (2003); Silverman *The Arithmetic of Dynamical Systems* (2007).
Duplicates merged: classics "Nessim Sibony, Dierk Schleicher, and others (eds.), *Holomorphic Dynamical Systems*" = supplement "Abate, Bedford, Brunella, Dinh, Schleicher, Sibony, *Holomorphic Dynamical Systems*" (2010, Springer LNM 1998, CIME). Kept the supplement's data and link and added the classics phrase "the standard survey volume for the several-variable theory".
Corrections: the classics entry wrongly called Sibony and Schleicher the editors of *Holomorphic Dynamical Systems*. They are two of the six lecturers; the CIME volume's editors are G. Gentili, J. Guenot and G. Patrizio. The merged entry now lists the six authors. "Earlier than the nominal boundary, and" removed from Mauldin–Urbański.
Proposed cross-section moves: none.
Candidates for removal: Nalini Joshi, *Discrete Painlevé Equations*: only loosely related to complex dynamics ("adjacent"); the pointer from Section 46 could be dropped and the book kept in Section 51. "Buff, Douady, Hubbard, and the Orsay notes tradition": not a book entry; it points to Hubbard vol. 2 and Milnor.
Dates uncertain: Abate *Holomorphic Dynamics on Hyperbolic Riemann Surfaces*: believed to be De Gruyter Studies in Mathematics, 2022/2023; no year given in the entry.

### Section 47: Approximation Theory
Entries: 19 + 19 → foundational 21, more recent 16 (duplicates merged 1).
Moved to More recent works: Trefethen *Approximation Theory and Approximation Practice* (2013); Temlyakov *Greedy Approximation* (2011) and *Multivariate Approximation* (2018) (merged, see below).
Moved to Foundational works: Novak–Woźniakowski *Tractability of Multivariate Problems* (vol. I 2008); Bogatyrev *Extremal Polynomials and Riemann Surfaces* (Russian original 2005; English 2012); Wendland *Scattered Data Approximation* (2005); Rahman–Schmeisser *Analytic Theory of Polynomials* (2002).
Duplicates merged: Temlyakov *Multivariate Approximation*. It appeared in the classics entry (paired with *Greedy Approximation*) and as a separate supplement entry. The two were merged into one paired entry that keeps the supplement's link and both annotations.
Corrections: "already in the classics list" removed from Temlyakov *Sparse Approximation with Bases*. More recent works grouped under three #### headings: Constructive and polynomial approximation; Approximation on spheres and balls; High-dimensional, sparse, and nonlinear approximation.
Proposed cross-section moves: none. (Stahl–Totik and Saff–Totik are cross-listed with Sections 48/38 by design. Dick–Pillichshammer could also sit with discrepancy material elsewhere, but it fits here.)
Candidates for removal: Philipp Grohs and Gitta Kutyniok (eds.), *Mathematical Aspects of Deep Learning*: an edited survey collection on machine-learning theory; marginal for a core analysis bibliography. Armin Iske, *Approximation Theory and Algorithms for Data Analysis*: an undergraduate/early-graduate textbook with an algorithmic emphasis; arguably too elementary. Vijay Gupta and Gancho Tachev, *Approximation with Positive Linear Operators and Linear Combinations*: a narrow specialist monograph, not a common reference point. Ronald A. DeVore, "Nonlinear Approximation": an Acta Numerica survey article, not a book (kept deliberately in the source).
Dates uncertain: Pinkus *Totally Positive Matrices*: Cambridge Tracts 181, publication year given as 2009 (References PDF filename) or 2010 depending on the source. Kept in Foundational works, following the filename.

### Section 48: Orthogonal Polynomials, Moment Problems, and Spectral Recurrences
Entries: 15 + 12 → foundational 16, more recent 11 (duplicates merged 0).
Moved to More recent works: Simon *Szegő's Theorem and Its Descendants* (2011); Schmüdgen *The Moment Problem* (2017); Van Assche *Orthogonal Polynomials and Painlevé Equations* (2017; title page 2018).
Moved to Foundational works: Levin–Lubinsky *Orthogonal Polynomials for Exponential Weights* (2001); Gautschi *Orthogonal Polynomials: Computation and Approximation* (2004); Teschl *Jacobi Operators and Completely Integrable Nonlinear Lattices* (2000); Marshall *Positive Polynomials and Sums of Squares* (2008).
Duplicates merged: none. The supplement entry "Walter Van Assche's ... is already in the classics list. The discrete Painlevé companion is Nalini Joshi, *Discrete Painlevé Equations*" was rewritten as a Joshi pointer entry ("Listed in Section 51. The discrete Painlevé companion to Van Assche's book."); the Van Assche classics entry received "(2017, Cambridge University Press)".
Corrections: none.
Proposed cross-section moves: none.
Candidates for removal: "Jan Stochel, Franciszek Szafraniec, and the operator-theoretic moment literature": not a book; a pointer to a body of papers with no title.
Dates uncertain: Van Assche (Cambridge online December 2017, print 2018; PDF filename says 2017); either way more recent.

### Section 49: Special Functions, Integral Transforms, and Classical Formulae
Entries: 23 + 18 → foundational 26, more recent 15 (duplicates merged 0).
Moved to More recent works: NIST *Handbook of Mathematical Functions* / DLMF (2010); Beals–Wong *Special Functions and Orthogonal Polynomials* (2016; predecessor *Special Functions: A Graduate Text*, 2010).
Moved to Foundational works: Cuyt et al. *Handbook of Continued Fractions for Special Functions* (2008); Gil–Segura–Temme *Numerical Methods for Special Functions* (2007); Aomoto–Kita *Theory of Hypergeometric Functions* (English 2011, Japanese original 1994; note "Japanese original 1994" added); Kilbas–Srivastava–Trujillo *Theory and Applications of Fractional Differential Equations* (2006); Andrews–Berndt *Ramanujan's Lost Notebook* (Part I 2005).
Duplicates merged: none.
Corrections: Askey–Bateman *Encyclopedia of Special Functions*: year changed from "2020" to "2020–2021" (volume II, *Multivariable Special Functions*, appeared in 2021).
Other edits: foundational part grouped under four #### headings (Graduate texts; Handbooks, tables, and computation; Hypergeometric series and Bessel functions; Integral transforms, fractional calculus, and complete monotonicity).
Proposed cross-section moves: none. (Estrada–Kanwal, *A Distributional Approach to Asymptotics*, would also fit Section 50; left in place.)
Candidates for removal: Masjed-Jamei, *Special Functions and Generalized Sturm–Liouville Problems* (2020): specialist and little cited, marginal for a core bibliography. Freeden–Gutting, *Special Functions of Mathematical (Geo-)Physics* (2013): applied/geophysical orientation, marginal. Meerschaert–Sikorskii, *Stochastic Models for Fractional Calculus*: more applied probability than special functions (would fit better in Section 8 if kept).
Dates uncertain: Schilling–Song–Vondraček *Bernstein Functions*: first edition dated 2009/2010 (PDF filename says 2009); left in Foundational works as in the source.

### Section 50: Asymptotic Analysis, Resurgence, and Perturbation
Entries: 19 + 14 → foundational 23, more recent 10 (duplicates merged 0).
Moved to More recent works: Mitschi–Sauzin *Divergent Series, Summability and Resurgence I* together with Sauzin's lecture notes (2016, Springer LNM).
Moved to Foundational works: Conte–Musette *The Painlevé Handbook* (1st ed. 2008; "first edition 2008" added); White *Asymptotic Analysis of Differential Equations* (1st ed. 2005; "first edition 2005" added); Flajolet–Sedgewick *Analytic Combinatorics* (2009); Kawai–Takei *Algebraic Analysis of Singular Perturbation Theory* (2005; Japanese original 1998); Sanders–Verhulst–Murdock *Averaging Methods* (1st ed. 1985).
Duplicates merged: none. (Ivrii 1998 *Microlocal Analysis and Precise Spectral Asymptotics* and Ivrii 2019 *Microlocal Analysis, Sharp Spectral Asymptotics and Applications* are different works; both kept.)
Corrections: "Johannes Sjöstrand and Mouez Dimassi" corrected to the book's author order "Mouez Dimassi and Johannes Sjöstrand". Loday-Richaud entry: "whose first volume, by Mitschi and Sauzin, is already in the classics list" changed to "whose first volume is by Mitschi and Sauzin".
Other edits: foundational part grouped under four #### headings (Asymptotic expansions and integrals; Differential equations, summability, and resurgence; Perturbation methods and averaging; Spectral asymptotics).
Proposed cross-section moves: none.
Candidates for removal: none (Bender–Orszag and Nayfeh are applied but annotated as such and historically central).
Dates uncertain: none.

### Section 51: Integrable Systems and Riemann–Hilbert Methods
Entries: 8 + 16 → foundational 15, more recent 9 (duplicates merged 0).
Moved to More recent works: none.
Moved to Foundational works: Gesztesy–Holden(–Michor–Teschl) *Soliton Equations and Their Algebro-Geometric Solutions* (2003/2008); Gromak–Laine–Shimomura *Painlevé Differential Equations in the Complex Plane* (2002); Conte–Musette *The Painlevé Handbook* (1st ed. 2008); Babelon–Bernard–Talon *Introduction to Classical Integrable Systems* (2003); Bobenko–Suris *Discrete Differential Geometry* (2008); Kamvissis–McLaughlin–Miller *Semiclassical Soliton Ensembles* (2003); Baik–Kriecherbauer–McLaughlin–Miller *Discrete Orthogonal Polynomials* (2007).
Duplicates merged: none.
Corrections: none.
Proposed cross-section moves: none.
Candidates for removal: "Alexander Its and others' surveys on the Riemann–Hilbert method": not a book, no specific title. "Percy Deift and Xin Zhou's papers on nonlinear steepest descent": papers, not a book (could be kept as a note in the intro paragraph instead).
Dates uncertain: none.

### Section 52: Geometric Analysis on Manifolds
Entries: 24 + 25 → foundational 31, more recent 18 (duplicates merged 0).
Moved to More recent works: Peter Li *Geometric Analysis* (2012); Andrews–Hopper *The Ricci Flow in Riemannian Geometry* (2011); Mantegazza *Lecture Notes on Mean Curvature Flow* (2011); Colding–Minicozzi *A Course in Minimal Surfaces* (2011; treated as a new book relative to their 1999 Courant notes); De Lellis–Spadaro work on Almgren regularity (papers 2011 onward; no year added).
Moved to Foundational works: Morgan–Tian *Ricci Flow and the Poincaré Conjecture* (2007) with *The Geometrization Conjecture* (2014); Chow et al. *The Ricci Flow: Techniques and Applications* (vol. I 2007); Capogna–Danielli–Pauls–Tyson (2007); Druet–Hebey–Robert (2004); McDuff–Salamon *J-holomorphic Curves* (1st ed. 2004); Kronheimer–Mrowka (2007); Nicolaescu *An Invitation to Morse Theory* (1st ed. 2007); McDuff–Salamon *Introduction to Symplectic Topology* (1st ed. 1995); Wehrheim *Uhlenbeck Compactness* (2004); Chang *Non-linear Elliptic Equations in Conformal Geometry* (2004); J. M. Lee *Introduction to Riemannian Manifolds* (1st ed. 1997); Bär–Ginoux–Pfäffle (2007). For the later editions, "first edition YYYY" was added to the bibliographic parenthesis.
Duplicates merged: none.
Corrections: none.
Other edits: both parts grouped under #### headings (Foundational: Riemannian geometry, comparison, and heat kernels; Nonlinear elliptic problems and harmonic maps; Geometric flows; Minimal surfaces; Symplectic, gauge-theoretic, and Lorentzian analysis. More recent: Riemannian, sub-Riemannian, and conformal analysis; Geometric flows; Minimal surfaces; Symplectic and gauge-theoretic analysis).
Proposed cross-section moves: none.
Candidates for removal: "Camillo De Lellis and Emanuele Spadaro's work on Almgren regularity": not a book (papers and survey lectures). Rudolph–Schmidt *Differential Geometry and Mathematical Physics*: a mathematical-physics geometry textbook with little analysis; marginal.
Dates uncertain: Dierkes–Hildebrandt–Sauvigny *Minimal Surfaces* (2010, revised edition of Dierkes–Hildebrandt–Küster–Wohlrab 1992); kept in Foundational works. Morgan–Tian combined entry placed by its earlier volume (2007).

### Section 53: Elliptic Operators on Manifolds, Index Theory, and Spectral Geometry
Entries: 17 + 15 → foundational 25, more recent 7 (duplicates merged 0).
Moved to More recent works: Zelditch *Eigenfunctions of the Laplacian on a Riemannian Manifold* (2017, AMS CBMS).
Moved to Foundational works: Higson–Roe *Analytic K-Homology* (2000); Ma–Marinescu *Holomorphic Morse Inequalities and Bergman Kernels* (2007); Bismut–Lebeau *The Hypoelliptic Laplacian and Ray–Singer Metrics* (2008); Borthwick *Spectral Theory of Infinite-Area Hyperbolic Surfaces* (1st ed. 2007; note added); Henrot–Pierre *Shape Variation and Optimization* (French original *Variation et optimisation de formes*, 2005; note added); Iwaniec *Spectral Methods of Automorphic Forms* (1st ed. 1995; note added); Friedrich *Dirac Operators in Riemannian Geometry* (2000); Gilkey *Asymptotic Formulae in Spectral Geometry* (2004); Lück *L²-Invariants* (2002).
Duplicates merged: none. The supplement entry "Steve Zelditch's eigenfunction book is already in the classics list. The inverse spectral direction is in Paternain, Salo, and Uhlmann, *Geometric Inverse Problems*" was rewritten as a Paternain–Salo–Uhlmann pointer entry ("Listed in Section 22. The inverse spectral direction, complementing Zelditch's eigenfunction book.").
Corrections: Bismut–Lebeau year corrected from 2011 to 2008 (Annals of Mathematics Studies 167, Princeton 2008).
Other edits: foundational part grouped under three #### headings (Elliptic operators, Hodge theory, and partial differential relations; Index theory and Dirac operators; Spectral geometry).
Proposed cross-section moves: none. (Gromov, *Partial Differential Relations*, would arguably sit better in Section 52; left in place.)
Candidates for removal: "Alexandre Girouard and Iosif Polterovich's surveys on the Steklov problem": the survey half of a combined entry is not a book (Henrot's *Extremum Problems* is).
Dates uncertain: Sogge combined entry (*Hangzhou Lectures*, 2014, with *Fourier Integrals in Classical Analysis*, 1993) left in Foundational works by the earlier book.

### Section 54: Problem Books, Counterexamples, and Reference Tables
Entries: 18 + 9 → foundational 20, more recent 7 (duplicates merged 1). The CKMA-bib2.md DLMF entry also contained Koekoek–Lesky–Swarttouw; after merging the DLMF, Koekoek–Lesky–Swarttouw became its own entry, so 27 entry lines go in and 27 come out.
Moved to More recent works: Simon, A Comprehensive Course in Analysis (2015, AMS); NIST DLMF (2010).
Moved to Foundational works: Shiryaev, Problems in Probability (Russian original 2006; Springer translation 2012); Rădulescu–Rădulescu–Andreescu, Problems in Real Analysis (2009); Stoyanov, Counterexamples in Probability (1st ed. 1987; 3rd ed. 2013); Borodin–Salminen, Handbook of Brownian Motion (1st ed. 1996; 2nd ed. 2002).
Duplicates merged: NIST DLMF (classics annotation kept; link and year 2010 from CKMA-bib2.md; dropped the CKMA-bib2.md wording "the tables already listed in the classics bibliography remain the formula references"). Koekoek–Lesky–Swarttouw now has its own entry, with the Section 48 pointer.
Corrections: none (the intro was rewritten to drop "The classical problem books remain those in CKMA-bib.md").
Proposed cross-section moves: none
Candidates for removal: Arnold, Problems for Children from 5 to 15: elementary (a problem book for school pupils); the bundled Lectures on PDE belongs to Section 32 rather than to a problem-book section. "Titu Andreescu and Dorin Andrica's inequality collections": vague, with no specific title, olympiad level, and I cannot confirm a joint Andreescu–Andrica inequality book (Andreescu's inequality books are mostly with other coauthors, such as Cîrtoaje and Mortici); the Steele half of the entry is sound.
Dates uncertain: Shiryaev, Problems in Probability: I classified it by the 2006 Russian edition (MCCME), which I am fairly but not fully sure of; if that edition is not counted, the entry goes back to More recent works.

### Section 55: Foundations, Constructive Analysis, and Machine-Formalized Mathematics
Entries: 18 + 18 → foundational 15, more recent 20 (duplicates merged 1).
Moved to More recent works: Hirschfeldt, Slicing the Truth (2014, World Scientific); Avigad, Mathematical Logic and Computation (2022, CUP); Avigad–de Moura–Kong–Ullrich, Theorem Proving in Lean, and Avigad–Massot, Mathematics in Lean (online, 2015 onwards); the Mathlib library (2017 onwards); Buzzard's writing and the Zulip archives; Chlipala, Certified Programming with Dependent Types (2013, MIT Press), with Coquelicot and MathComp-Analysis; Gonthier's papers, the Palomar Registry, and Lean Pool ("emerging infrastructure").
Moved to Foundational works: Kohlenbach, Applied Proof Theory (2008); Nies, Computability and Randomness (2009); Harrison, Handbook of Practical Logic and Automated Reasoning (2009); Loeb–Wolff (eds.), Nonstandard Analysis for the Working Mathematician (1st ed. 2000; 2nd ed. 2015).
Duplicates merged: Avigad, Mathematical Logic and Computation (classics annotation kept, with year and DOI link from CKMA-bib2.md; dropped "and the Lean tutorials already listed in CKMA-bib.md ... continuations").
Corrections: none. Wording changes only: in Mahboubi–Tassi, "the other ecosystem named in the classics list" became "the main ecosystem besides Lean". The intro was merged, dropping "already in the classics list". In More recent works I added three #### groups: constructive/computability/reverse mathematics; logic, type theory, and proof assistants; validated numerics.
Proposed cross-section moves: none
Candidates for removal: Kevin Buzzard's expository writing and the Lean Zulip archives: not books, and not stable citable references. Gonthier's formalization papers, the Palomar Registry, and Lean Pool: not books, and I cannot verify that a "Palomar Registry" or a "Lean Pool" archive exists. Chlipala, Certified Programming with Dependent Types: a programming and type-theory text with no analysis content (the Coquelicot/MathComp-Analysis half of the entry is relevant). The Mathlib library is not a book but is kept as clearly intended; flagged only for awareness.
Dates uncertain: Avigad, Mathematical Logic and Computation: online in 2022, print copyright possibly 2023 (the local PDF is named 2023); I used 2022. Chlipala: drafts online from about 2008, MIT Press book 2013; I used 2013. Gonthier entry: mixed dates (four-colour theorem 2005/2008, Feit–Thompson 2013); placed in More recent works because of the "emerging infrastructure" wording. Hitchhiker's Guide: I cannot verify the author list (Généreux) or the 2026-edition repository link; left as in the source.
