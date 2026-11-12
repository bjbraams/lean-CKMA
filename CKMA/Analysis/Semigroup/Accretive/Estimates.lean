/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Accretive resolvents and nonlinear contraction semigroups

Accretive and m-accretive multivalued graphs on real normed spaces, their nonlinear
resolvents and implicit Euler products. The resolvent is the identity at scale zero
and a contraction at positive scales. In a Banach space the product estimates below
feed the Crandall–Liggett semigroup constructed in
`CKMA.Analysis.Semigroup.Accretive`. Source: GAPS 24.52.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Finset Function Topology
open scoped NNReal BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The domain of a possibly multivalued operator graph. -/
def accretiveGraphDomain (G : Set (X × X)) : Set X := {x | ∃ u, (x, u) ∈ G}

/-- Accretivity of a graph in a real Banach space, stated by the resolvent norm inequality. -/
def IsAccretiveGraph (G : Set (X × X)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, ∀ t : ℝ, 0 < t → ‖p.1 - q.1‖ ≤ ‖p.1 - q.1 + t • (p.2 - q.2)‖

/-- Maximal accretivity includes surjectivity of every positive resolvent. -/
def IsMAccretiveGraph (G : Set (X × X)) : Prop :=
  IsAccretiveGraph G ∧ ∀ t : ℝ, 0 < t → ∀ x : X, ∃ y u : X, (y, u) ∈ G ∧ x = y + t • u

/-- The nonlinear resolvent, with explicit totalizations: the identity at zero scale, and
zero if no graph preimage exists. Under maximal accretivity the latter branch is never used. -/
def accretiveResolvent (G : Set (X × X)) (t : ℝ) (x : X) : X := by
  classical
  exact if t = 0 then x else
    if h : ∃ y u : X, (y, u) ∈ G ∧ x = y + t • u then Classical.choose h else 0

/-- The implicit Euler product with `n+1` resolvent steps, including exact zero-time identity. -/
def accretiveEulerProduct (G : Set (X × X)) (t : ℝ≥0) (n : ℕ) (x : X) : X :=
  (accretiveResolvent G ((t : ℝ) / (n + 1 : ℝ)))^[n + 1] x

omit [CompleteSpace X] in
/-- The zero-scale totalization is the identity. -/
theorem accretiveResolvent_zero (G : Set (X × X)) (x : X) : accretiveResolvent G 0 x = x := by
  classical
  simp [accretiveResolvent]

omit [CompleteSpace X] in
/-- The resolvent of an m-accretive graph is a contraction at every positive scale. -/
theorem accretiveResolvent_lipschitz {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {t : ℝ} (ht : 0 < t) : LipschitzWith 1 (accretiveResolvent G t) := by
  classical
  have hr (x : X) : ∃ u, (accretiveResolvent G t x, u) ∈ G ∧
      x = accretiveResolvent G t x + t • u := by
    have hx := hG.2 t ht x
    simpa only [accretiveResolvent, ht.ne', ite_false, dite_eq_left hx] using
      Classical.choose_spec hx
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  obtain ⟨u, hu, hx⟩ := hr x
  obtain ⟨v, hv, hy⟩ := hr y
  have h := hG.1 _ hu _ hv t ht
  calc ‖accretiveResolvent G t x - accretiveResolvent G t y‖ ≤
      ‖accretiveResolvent G t x - accretiveResolvent G t y + t • (u - v)‖ := h
    _ = ‖x - y‖ := by
      congr 1
      calc accretiveResolvent G t x - accretiveResolvent G t y + t • (u-v) =
          (accretiveResolvent G t x + t • u) - (accretiveResolvent G t y + t • v) := by module
        _ = x-y := by rw [← hx, ← hy]

omit [CompleteSpace X] in
/-- A positive resolvent value is witnessed by a graph slope. -/
private lemma accretiveResolvent_spec {G : Set (X × X)} (hG : IsMAccretiveGraph G) {t : ℝ}
    (ht : 0 < t) (x : X) :
    ∃ u, (accretiveResolvent G t x, u) ∈ G ∧ x = accretiveResolvent G t x + t • u := by
  classical
  have hx := hG.2 t ht x
  simpa only [accretiveResolvent, ht.ne', ite_false, dite_eq_left hx] using
    Classical.choose_spec hx

omit [CompleteSpace X] in
/-- Accretivity makes the positive resolvent preimage unique. -/
private lemma accretiveResolvent_unique {G : Set (X × X)} (hG : IsMAccretiveGraph G) {t : ℝ}
    (ht : 0 < t) {x y y' u u' : X} (hy : (y, u) ∈ G) (hx : x = y + t • u) (hy' : (y', u') ∈ G)
    (hx' : x = y' + t • u') : y = y' := by
  have hsub : y - y' + t • (u - u') = (y + t • u) - (y' + t • u') := by module
  rw [← hx, ← hx'] at hsub
  have hle : ‖y - y'‖ ≤ ‖y - y' + t • (u - u')‖ := hG.1 _ hy _ hy' t ht
  have : ‖y - y'‖ ≤ 0 := by simpa [hsub] using hle
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

omit [CompleteSpace X] in
/-- Moving one resolvent step costs at most the scale times a graph slope at the input. -/
private lemma norm_sub_accretiveResolvent_le {G : Set (X × X)} (hG : IsMAccretiveGraph G) {t : ℝ}
    (ht : 0 < t) {x u : X} (hx : (x, u) ∈ G) :
    ‖x - accretiveResolvent G t x‖ ≤ t * ‖u‖ := by
  obtain ⟨v, hv, hxeq⟩ := accretiveResolvent_spec hG ht x
  calc ‖x - accretiveResolvent G t x‖
      ≤ ‖x - accretiveResolvent G t x + t • (u - v)‖ := hG.1 _ hx _ hv t ht
    _ = ‖t • u‖ := by
        congr 1
        have hzero : x - (accretiveResolvent G t x + t • v) = 0 := sub_eq_zero.mpr hxeq
        calc x - accretiveResolvent G t x + t • (u - v)
            = (x - (accretiveResolvent G t x + t • v)) + t • u := by module
          _ = t • u := by rw [hzero, zero_add]
    _ = t * ‖u‖ := by simp [norm_smul, abs_of_pos ht]

omit [CompleteSpace X] in
/-- Every positive resolvent value lies in the graph domain. -/
private lemma accretiveResolvent_mem_domain {G : Set (X × X)} (hG : IsMAccretiveGraph G) {t : ℝ}
    (ht : 0 < t) (x : X) : accretiveResolvent G t x ∈ accretiveGraphDomain G := by
  obtain ⟨u, hu, _⟩ := accretiveResolvent_spec hG ht x
  exact ⟨u, hu⟩

omit [CompleteSpace X] in
/-- Iterates of a positive resolvent stay within `n` steps of a graph point. -/
private lemma norm_accretiveResolvent_iterate_sub_le {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {t : ℝ} (ht : 0 < t) {x u : X} (hx : (x, u) ∈ G) (n : ℕ) :
    ‖(accretiveResolvent G t)^[n] x - x‖ ≤ n * t * ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ‖(accretiveResolvent G t)^[n + 1] x - (accretiveResolvent G t)^[n] x‖ ≤
          ‖accretiveResolvent G t x - x‖ := by
        have hLip := ((accretiveResolvent_lipschitz hG ht).iterate n).dist_le_mul
          (accretiveResolvent G t x) x
        simpa [dist_eq_norm, iterate_succ_apply, NNReal.coe_pow, NNReal.coe_one, one_pow, one_mul]
          using hLip
      have hrev : ‖accretiveResolvent G t x - x‖ =
          ‖x - accretiveResolvent G t x‖ := norm_sub_rev _ _
      calc ‖(accretiveResolvent G t)^[n + 1] x - x‖
          ≤ ‖(accretiveResolvent G t)^[n + 1] x - (accretiveResolvent G t)^[n] x‖ +
              ‖(accretiveResolvent G t)^[n] x - x‖ := by
            simpa [sub_add_sub_cancel] using
              norm_add_le ((accretiveResolvent G t)^[n + 1] x - (accretiveResolvent G t)^[n] x)
                ((accretiveResolvent G t)^[n] x - x)
        _ ≤ ‖accretiveResolvent G t x - x‖ + n * t * ‖u‖ := by gcongr
        _ ≤ t * ‖u‖ + n * t * ‖u‖ := by
            gcongr
            rw [hrev]
            exact norm_sub_accretiveResolvent_le hG ht hx
        _ = ↑(n + 1) * t * ‖u‖ := by
            rw [Nat.cast_succ]
            ring

omit [CompleteSpace X] in
/-- The resolvent identity: a coarser step is one finer step on a convex combination. -/
private lemma accretiveResolvent_formula {G : Set (X × X)} (hG : IsMAccretiveGraph G) {h k : ℝ}
    (hh : 0 < h) (hk : 0 < k) (x : X) :
    accretiveResolvent G h ((h / k) • x + ((k - h) / k) • accretiveResolvent G k x) =
      accretiveResolvent G k x := by
  obtain ⟨v, hv, hx⟩ := accretiveResolvent_spec hG hk x
  set y := accretiveResolvent G k x
  have hcomb : (h / k) • x + ((k - h) / k) • y = y + h • v := by
    rw [hx]
    have hc : h / k * k = h := div_mul_cancel₀ h hk.ne'
    have hcoeff : h / k + (k - h) / k = 1 := by field_simp; ring
    calc (h / k) • (y + k • v) + ((k - h) / k) • y
        = (h / k) • y + (h / k * k) • v + ((k - h) / k) • y := by rw [smul_add, smul_smul]
      _ = (h / k) • y + h • v + ((k - h) / k) • y := by rw [hc]
      _ = h • v + ((h / k) • y + ((k - h) / k) • y) := by abel
      _ = h • v + (h / k + (k - h) / k) • y := by rw [← add_smul]
      _ = h • v + (1 : ℝ) • y := by rw [hcoeff]
      _ = y + h • v := by rw [one_smul]; abel
  obtain ⟨v', hv', hx'⟩ := accretiveResolvent_spec hG hh ((h / k) • x + ((k - h) / k) • y)
  exact accretiveResolvent_unique hG hh hv' hx' hv (by rw [← hcomb])

omit [CompleteSpace X] in
/-- One peeling step for resolvent iterates, at the finer positive scale. -/
private lemma accretiveResolvent_iterate_recur {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {h k : ℝ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (x : X) :
    ‖(accretiveResolvent G h)^[n] x - (accretiveResolvent G k)^[m] x‖ ≤
      (h / k) * ‖(accretiveResolvent G h)^[n - 1] x - (accretiveResolvent G k)^[m - 1] x‖ +
        (1 - h / k) *
          ‖(accretiveResolvent G h)^[n - 1] x - (accretiveResolvent G k)^[m] x‖ := by
  have hpos : 0 < h / k := div_pos hh hk
  have hq : 0 ≤ 1 - h / k := by
    rw [sub_nonneg, div_le_one hk]
    exact hhk
  set J : ℝ → X → X := accretiveResolvent G
  have hm1 : (m - 1) + 1 = m := Nat.sub_add_cancel hm
  have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hleft : (J h)^[n] x = J h ((J h)^[n - 1] x) := by
    have hidx : (J h)^[n] x = (J h)^[(n - 1) + 1] x := by rw [hn1]
    rw [hidx, iterate_succ_apply']
  have hright : (J k)^[m] x = J k ((J k)^[m - 1] x) := by
    have hidx : (J k)^[m] x = (J k)^[(m - 1) + 1] x := by rw [hm1]
    rw [hidx, iterate_succ_apply']
  have hqeq : (k - h) / k = 1 - h / k := by field_simp
  have hform : (J k)^[m] x =
      J h ((h / k) • (J k)^[m - 1] x + (1 - h / k) • (J k)^[m] x) := by
    rw [hright, ← hqeq]
    exact (accretiveResolvent_formula hG hh hk ((J k)^[m - 1] x)).symm
  rw [hleft]
  conv_lhs => rw [hform]
  set z := (J h)^[n - 1] x
  set a := (J k)^[m - 1] x
  set b := (J k)^[m] x
  set p : ℝ := h / k
  set q : ℝ := 1 - h / k
  have hpq : p + q = 1 := by simp [p, q]
  have hLip : ‖J h z - J h (p • a + q • b)‖ ≤ ‖z - (p • a + q • b)‖ := by
    simpa [dist_eq_norm, p, q, a, b, z] using
      (accretiveResolvent_lipschitz hG hh).dist_le_mul z (p • a + q • b)
  refine hLip.trans ?_
  have hsplit : z - (p • a + q • b) = p • (z - a) + q • (z - b) := by
    calc z - (p • a + q • b) = (p + q) • z - (p • a + q • b) := by rw [hpq, one_smul]
      _ = p • z + q • z - p • a - q • b := by rw [add_smul]; abel
      _ = p • (z - a) + q • (z - b) := by rw [smul_sub, smul_sub]; abel
  rw [hsplit]
  calc ‖p • (z - a) + q • (z - b)‖ ≤ ‖p • (z - a)‖ + ‖q • (z - b)‖ := norm_add_le _ _
    _ = |p| * ‖z - a‖ + |q| * ‖z - b‖ := by simp [norm_smul]
    _ = p * ‖z - a‖ + q * ‖z - b‖ := by simp [abs_of_pos hpos, abs_of_nonneg hq]

omit [CompleteSpace X] in
/-- Two resolvent values satisfy the convex-combination form of accretivity. -/
private lemma norm_accretiveResolvent_convex {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (x w : X) :
    ‖accretiveResolvent G lam x - accretiveResolvent G mu w‖ ≤
      (mu / (lam + mu)) * ‖x - accretiveResolvent G mu w‖ +
        (lam / (lam + mu)) * ‖accretiveResolvent G lam x - w‖ := by
  obtain ⟨u, hu, hx⟩ := accretiveResolvent_spec hG hl x
  obtain ⟨v, hv, hw⟩ := accretiveResolvent_spec hG hm w
  set y := accretiveResolvent G lam x
  set z := accretiveResolvent G mu w
  set a : ℝ := mu / (lam + mu)
  set b : ℝ := lam / (lam + mu)
  set τ : ℝ := lam * mu / (lam + mu)
  have hτ : 0 < τ := by positivity
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hab : a + b = 1 := by unfold a b; field_simp; ring
  have hx' : lam • u = x - y := by rw [hx]; abel
  have hw' : mu • v = w - z := by rw [hw]; abel
  have hτu : τ • u = a • (x - y) := by
    have hτα : τ = a * lam := by unfold τ a; field_simp
    rw [hτα, mul_smul, hx']
  have hτv : τ • v = b • (w - z) := by
    have hτb : τ = b * mu := by unfold τ b; field_simp
    rw [hτb, mul_smul, hw']
  have hcomb : y - z + τ • (u - v) = a • (x - z) + b • (y - w) := by
    rw [smul_sub, hτu, hτv]
    have hba : b = 1 - a := by unfold a b; field_simp; ring
    rw [hba]
    module
  have hacc : ‖y - z‖ ≤ ‖y - z + τ • (u - v)‖ := hG.1 _ hu _ hv τ hτ
  calc ‖y - z‖ ≤ ‖a • (x - z) + b • (y - w)‖ := by simpa [hcomb] using hacc
    _ ≤ ‖a • (x - z)‖ + ‖b • (y - w)‖ := norm_add_le _ _
    _ = |a| * ‖x - z‖ + |b| * ‖y - w‖ := by simp [norm_smul]
    _ = a * ‖x - z‖ + b * ‖y - w‖ := by simp [abs_of_nonneg ha, abs_of_nonneg hb]

omit [CompleteSpace X] in
/-- An iterate of a positive resolvent carries a graph slope no larger than the input slope. -/
lemma accretiveResolvent_iterate_slope {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {t : ℝ} (ht : 0 < t) {x u : X} (hx : (x, u) ∈ G) {n : ℕ} (hn : 0 < n) :
    ∃ v, ((accretiveResolvent G t)^[n] x, v) ∈ G ∧ ‖v‖ ≤ ‖u‖ ∧
      (accretiveResolvent G t)^[n - 1] x =
        (accretiveResolvent G t)^[n] x + t • v := by
  set J : ℝ → X → X := accretiveResolvent G
  have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hidx : (J t)^[n] x = J t ((J t)^[n - 1] x) := by
    rw [show (J t)^[n] x = (J t)^[(n - 1) + 1] x by rw [hn'], iterate_succ_apply']
  obtain ⟨v, hv, heq⟩ := accretiveResolvent_spec hG ht ((J t)^[n - 1] x)
  have hmem : ((J t)^[n] x, v) ∈ G := by simpa [hidx] using hv
  have hstep : ‖(J t)^[n] x - (J t)^[n - 1] x‖ ≤ ‖J t x - x‖ := by
    have hLip := ((accretiveResolvent_lipschitz hG ht).iterate (n - 1)).dist_le_mul (J t x) x
    have hpow : (J t)^[n] x = (J t)^[(n - 1) + 1] x := by rw [hn']
    simpa [hpow, dist_eq_norm, iterate_succ_apply, NNReal.coe_pow, NNReal.coe_one, one_pow,
      one_mul] using hLip
  have heq' : (J t)^[n - 1] x = (J t)^[n] x + t • v := by
    rw [hidx]
    exact heq
  have hdiff : (J t)^[n - 1] x - (J t)^[n] x = t • v := (sub_eq_iff_eq_add').mpr heq'
  have hnorm : ‖v‖ ≤ ‖u‖ := by
    have htmul : t * ‖v‖ ≤ t * ‖u‖ := by
      calc t * ‖v‖ = ‖t • v‖ := by simp [norm_smul, abs_of_pos ht]
        _ = ‖(J t)^[n - 1] x - (J t)^[n] x‖ := by rw [← hdiff]
        _ = ‖(J t)^[n] x - (J t)^[n - 1] x‖ := norm_sub_rev _ _
        _ ≤ ‖J t x - x‖ := hstep
        _ = ‖x - J t x‖ := norm_sub_rev _ _
        _ ≤ t * ‖u‖ := norm_sub_accretiveResolvent_le hG ht hx
    exact (mul_le_mul_iff_right₀ ht).mp htmul
  exact ⟨v, hmem, hnorm, heq'⟩

omit [CompleteSpace X] in
/-- Resolvents of one graph point at two scales differ by at most the scale gap. -/
private lemma norm_accretiveResolvent_scale_le {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (hlm : lam ≤ mu) {z v : X} (hz : (z, v) ∈ G) :
    ‖accretiveResolvent G lam z - accretiveResolvent G mu z‖ ≤ (mu - lam) * ‖v‖ := by
  set J : ℝ → X → X := accretiveResolvent G
  set a : ℝ := lam / mu
  set b : ℝ := (mu - lam) / mu
  have hab : a + b = 1 := by unfold a b; field_simp; ring
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hlm) hm.le
  have hform : J mu z = J lam (a • z + b • J mu z) :=
    (accretiveResolvent_formula hG hl hm z).symm
  have hLip : ‖J lam z - J mu z‖ ≤ ‖z - (a • z + b • J mu z)‖ := by
    conv_lhs => rw [hform]
    simpa [dist_eq_norm] using
      (accretiveResolvent_lipschitz hG hl).dist_le_mul z (a • z + b • J mu z)
  have hsplit : z - (a • z + b • J mu z) = b • (z - J mu z) := by
    calc z - (a • z + b • J mu z)
        = (a + b) • z - (a • z + b • J mu z) := by rw [hab, one_smul]
      _ = b • z - b • J mu z := by rw [add_smul]; abel
      _ = b • (z - J mu z) := by rw [← smul_sub]
  calc ‖J lam z - J mu z‖ ≤ ‖b • (z - J mu z)‖ := by simpa [hsplit] using hLip
    _ = b * ‖z - J mu z‖ := by simp [norm_smul, abs_of_nonneg hb]
    _ ≤ b * (mu * ‖v‖) := by
        gcongr
        exact norm_sub_accretiveResolvent_le hG hm hz
    _ = (mu - lam) * ‖v‖ := by unfold b; field_simp

omit [CompleteSpace X] in
/-- Equal iteration counts at two scales differ by the total scale gap times a slope. -/
private lemma norm_accretiveResolvent_iterate_same_count {G : Set (X × X)}
    (hG : IsMAccretiveGraph G) {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (hlm : lam ≤ mu)
    {x u : X} (hx : (x, u) ∈ G) (n : ℕ) :
    ‖(accretiveResolvent G lam)^[n] x - (accretiveResolvent G mu)^[n] x‖ ≤
      (n : ℝ) * (mu - lam) * ‖u‖ := by
  set J : ℝ → X → X := accretiveResolvent G
  induction n with
  | zero => simp
  | succ n ih =>
      set y := (J mu)^[n] x
      obtain ⟨v, hv, hvn⟩ : ∃ v, (y, v) ∈ G ∧ ‖v‖ ≤ ‖u‖ := by
        cases n with
        | zero => exact ⟨u, by simpa [y] using hx, le_rfl⟩
        | succ n =>
            obtain ⟨v, hv, hvn, _⟩ := accretiveResolvent_iterate_slope hG hm hx (Nat.succ_pos n)
            exact ⟨v, by simpa [y] using hv, hvn⟩
      have hLip : ‖(J lam)^[n + 1] x - J lam y‖ ≤ ‖(J lam)^[n] x - y‖ := by
        have hdist := (accretiveResolvent_lipschitz hG hl).dist_le_mul ((J lam)^[n] x) y
        simpa [dist_eq_norm, iterate_succ_apply', NNReal.coe_one, one_mul] using hdist
      have hscale : ‖J lam y - (J mu)^[n + 1] x‖ ≤ (mu - lam) * ‖v‖ := by
        simpa [iterate_succ_apply', y] using norm_accretiveResolvent_scale_le hG hl hm hlm hv
      calc ‖(J lam)^[n + 1] x - (J mu)^[n + 1] x‖
          ≤ ‖(J lam)^[n + 1] x - J lam y‖ + ‖J lam y - (J mu)^[n + 1] x‖ := by
            simpa [sub_add_sub_cancel] using
              norm_add_le ((J lam)^[n + 1] x - J lam y) (J lam y - (J mu)^[n + 1] x)
        _ ≤ ‖(J lam)^[n] x - y‖ + (mu - lam) * ‖v‖ := by gcongr
        _ ≤ (n : ℝ) * (mu - lam) * ‖u‖ + (mu - lam) * ‖u‖ := by
            refine add_le_add ?_ ?_
            · simpa [y] using ih
            · exact mul_le_mul_of_nonneg_left hvn (sub_nonneg.mpr hlm)
        _ = ↑(n + 1) * (mu - lam) * ‖u‖ := by
            rw [Nat.cast_succ]
            ring

/-- Squared scale in the Banach-space product estimate. -/
private def resolventStepSq (h k : ℝ) (n m : ℕ) : ℝ :=
  ((n : ℝ) * h - (m : ℝ) * k) ^ 2 + (n : ℝ) * h ^ 2 + (m : ℝ) * k ^ 2

omit [CompleteSpace X] in
/-- The squared scale is a sum of squares, hence nonnegative. -/
private lemma resolventStepSq_nonneg (h k : ℝ) (n m : ℕ) : 0 ≤ resolventStepSq h k n m := by
  unfold resolventStepSq
  positivity

omit [CompleteSpace X] in
/-- One convex step does not increase the Crandall–Liggett square-root scale. -/
private lemma resolventStepSq_sqrt_step {h k : ℝ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (h / k) * Real.sqrt (resolventStepSq h k (n - 1) (m - 1)) +
        (1 - h / k) * Real.sqrt (resolventStepSq h k (n - 1) m) ≤
      Real.sqrt (resolventStepSq h k n m) := by
  set p : ℝ := h / k
  set q : ℝ := 1 - h / k
  have hp : 0 ≤ p := div_nonneg hh.le hk.le
  have hq : 0 ≤ q := sub_nonneg.mpr ((div_le_one hk).mpr hhk)
  set A := Real.sqrt (resolventStepSq h k (n - 1) (m - 1))
  set B := Real.sqrt (resolventStepSq h k (n - 1) m)
  have hAsq : A ^ 2 = resolventStepSq h k (n - 1) (m - 1) :=
    Real.sq_sqrt (resolventStepSq_nonneg _ _ _ _)
  have hBsq : B ^ 2 = resolventStepSq h k (n - 1) m :=
    Real.sq_sqrt (resolventStepSq_nonneg _ _ _ _)
  have hpoly : resolventStepSq h k n m =
      p * resolventStepSq h k (n - 1) (m - 1) +
        q * resolventStepSq h k (n - 1) m + 2 * h ^ 2 := by
    unfold resolventStepSq p q
    rw [Nat.cast_sub hn, Nat.cast_sub hm, Nat.cast_one]
    field_simp
    ring
  have hquad : p * A ^ 2 + q * B ^ 2 - (p * A + q * B) ^ 2 = p * q * (A - B) ^ 2 := by ring
  have hle : (p * A + q * B) ^ 2 ≤ p * A ^ 2 + q * B ^ 2 := by
    have hdiff : 0 ≤ p * q * (A - B) ^ 2 := by positivity
    linarith [hquad]
  rw [hAsq, hBsq] at hle
  have hextra : 0 ≤ 2 * h ^ 2 := by positivity
  have hsum : (p * A + q * B) ^ 2 ≤ resolventStepSq h k n m := by linarith [hpoly]
  have hnn : 0 ≤ p * A + q * B := by positivity
  exact (Real.le_sqrt hnn (resolventStepSq_nonneg _ _ _ _)).2 hsum

omit [CompleteSpace X] in
/-- Iterates from one graph point obey the Crandall–Liggett square-root bound. -/
private lemma norm_accretiveResolvent_iterate_cross {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {h k : ℝ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k) {x u : X} (hx : (x, u) ∈ G) (n m : ℕ) :
    ‖(accretiveResolvent G h)^[n] x - (accretiveResolvent G k)^[m] x‖ ≤
      Real.sqrt (resolventStepSq h k n m) * ‖u‖ := by
  set J : ℝ → X → X := accretiveResolvent G
  induction n generalizing m with
  | zero =>
      rw [iterate_zero, id_eq, norm_sub_rev]
      refine (norm_accretiveResolvent_iterate_sub_le hG hk hx m).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
      refine (Real.le_sqrt (by positivity) (resolventStepSq_nonneg h k 0 m)).2 ?_
      unfold resolventStepSq
      simp only [Nat.cast_zero, zero_mul, zero_sub, neg_sq]
      have hmk : 0 ≤ (m : ℝ) * k ^ 2 := by positivity
      linarith
  | succ n ih =>
      cases m with
      | zero =>
          rw [iterate_zero, id_eq]
          refine (norm_accretiveResolvent_iterate_sub_le hG hh hx (n + 1)).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
          have hcast : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
          rw [hcast]
          refine (Real.le_sqrt (by positivity) (resolventStepSq_nonneg h k (n + 1) 0)).2 ?_
          unfold resolventStepSq
          simp only [Nat.cast_zero, zero_mul, sub_zero]
          rw [Nat.cast_add, Nat.cast_one]
          have hnh : 0 ≤ ((n : ℝ) + 1) * h ^ 2 := by positivity
          linarith
      | succ m =>
          have hp : 0 ≤ h / k := div_nonneg hh.le hk.le
          have hq : 0 ≤ 1 - h / k := sub_nonneg.mpr ((div_le_one hk).mpr hhk)
          have hrec := accretiveResolvent_iterate_recur (n := n + 1) (m := m + 1) hG hh hk hhk
            (Nat.succ_pos n) (Nat.succ_pos m) x
          have h1 : (n + 1) - 1 = n := by omega
          have h2 : (m + 1) - 1 = m := by omega
          have hstep : ‖(J h)^[n + 1] x - (J k)^[m + 1] x‖ ≤
              (h / k) * ‖(J h)^[n] x - (J k)^[m] x‖ +
                (1 - h / k) * ‖(J h)^[n] x - (J k)^[m + 1] x‖ := by
            simpa [h1, h2, J] using hrec
          calc ‖(J h)^[n + 1] x - (J k)^[m + 1] x‖
              ≤ (h / k) * ‖(J h)^[n] x - (J k)^[m] x‖ +
                  (1 - h / k) * ‖(J h)^[n] x - (J k)^[m + 1] x‖ := hstep
            _ ≤ (h / k) * (Real.sqrt (resolventStepSq h k n m) * ‖u‖) +
                  (1 - h / k) * (Real.sqrt (resolventStepSq h k n (m + 1)) * ‖u‖) := by
                refine add_le_add ?_ ?_
                · exact mul_le_mul_of_nonneg_left (ih m) hp
                · exact mul_le_mul_of_nonneg_left (ih (m + 1)) hq
            _ = ((h / k) * Real.sqrt (resolventStepSq h k n m) +
                  (1 - h / k) * Real.sqrt (resolventStepSq h k n (m + 1))) * ‖u‖ := by ring
            _ ≤ Real.sqrt (resolventStepSq h k (n + 1) (m + 1)) * ‖u‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
                simpa [h1, h2] using
                  resolventStepSq_sqrt_step hh hk hhk (Nat.succ_pos n) (Nat.succ_pos m)

omit [CompleteSpace X] in
/-- At time zero every Euler product is the identity. -/
lemma accretiveEulerProduct_zero (G : Set (X × X)) (n : ℕ) (x : X) :
    accretiveEulerProduct G 0 n x = x := by
  simp only [accretiveEulerProduct, NNReal.coe_zero, zero_div]
  exact iterate_fixed (accretiveResolvent_zero G x) (n + 1)

omit [CompleteSpace X] in
/-- Every Euler product is a contraction. -/
lemma accretiveEulerProduct_lipschitz {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    (t : ℝ≥0) (n : ℕ) : LipschitzWith 1 (accretiveEulerProduct G t n) := by
  by_cases ht : (t : ℝ) = 0
  · have hid : accretiveEulerProduct G t n = id := by
      ext x
      rw [NNReal.coe_eq_zero.mp ht]
      exact accretiveEulerProduct_zero G n x
    rw [hid]
    exact LipschitzWith.id
  · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht)
    have hpos : 0 < (t : ℝ) / (↑n + 1) := div_pos ht0 (by positivity)
    have hfun : accretiveEulerProduct G t n =
        (accretiveResolvent G ((t : ℝ) / (↑n + 1)))^[n + 1] := by
      ext x
      rfl
    simpa [hfun, one_pow] using (accretiveResolvent_lipschitz hG hpos).iterate (n + 1)

omit [CompleteSpace X] in
/-- An Euler product stays within time times a graph slope of its initial value. -/
lemma norm_accretiveEulerProduct_sub {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (n : ℕ) (t : ℝ≥0) :
    ‖accretiveEulerProduct G t n x - x‖ ≤ (t : ℝ) * ‖u‖ := by
  by_cases ht : (t : ℝ) = 0
  · rw [NNReal.coe_eq_zero.mp ht, accretiveEulerProduct_zero]
    simp
  · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht)
    have hpos : 0 < (t : ℝ) / (↑n + 1) := div_pos ht0 (by positivity)
    have hle := norm_accretiveResolvent_iterate_sub_le hG hpos hx (n + 1)
    have hcoe : (↑(n + 1) : ℝ) * ((t : ℝ) / (↑n + 1)) = (t : ℝ) := by
      rw [Nat.cast_succ, mul_div_cancel₀ _ (by positivity)]
    calc ‖accretiveEulerProduct G t n x - x‖
        = ‖(accretiveResolvent G ((t : ℝ) / (↑n + 1)))^[n + 1] x - x‖ := by
          simp [accretiveEulerProduct]
      _ ≤ ↑(n + 1) * ((t : ℝ) / (↑n + 1)) * ‖u‖ := hle
      _ = (t : ℝ) * ‖u‖ := by rw [hcoe]

omit [CompleteSpace X] in
/-- Equal-time Euler products from a graph point approach one another at a square-root rate. -/
lemma norm_accretiveEulerProduct_cross {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) {a b : ℕ} (hab : b ≤ a) (t : ℝ≥0) :
    ‖accretiveEulerProduct G t a x - accretiveEulerProduct G t b x‖ ≤
      (t : ℝ) * ‖u‖ * Real.sqrt (1 / (a + 1) + 1 / (b + 1)) := by
  by_cases ht : (t : ℝ) = 0
  · rw [NNReal.coe_eq_zero.mp ht, accretiveEulerProduct_zero, accretiveEulerProduct_zero]
    simp
  · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht)
    set N : ℕ := a + 1
    set M : ℕ := b + 1
    have hMleN : M ≤ N := Nat.succ_le_succ hab
    set h : ℝ := (t : ℝ) / N
    set k : ℝ := (t : ℝ) / M
    have hh : 0 < h := by positivity
    have hk : 0 < k := by positivity
    have hhk : h ≤ k := by
      unfold h k
      gcongr
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    have hNh : (N : ℝ) * h = (t : ℝ) := by
      unfold h
      exact mul_div_cancel₀ _ hN0
    have hMk : (M : ℝ) * k = (t : ℝ) := by
      unfold k
      exact mul_div_cancel₀ _ hM0
    have hsq : resolventStepSq h k N M = (t : ℝ) ^ 2 * (1 / (N : ℝ) + 1 / (M : ℝ)) := by
      unfold resolventStepSq
      rw [show h = (t : ℝ) / N by rfl, show k = (t : ℝ) / M by rfl]
      field_simp [hN0, hM0]
      ring
    have hsqrt : Real.sqrt (resolventStepSq h k N M) =
        (t : ℝ) * Real.sqrt (1 / (N : ℝ) + 1 / (M : ℝ)) := by
      rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht0.le]
    have hstep := norm_accretiveResolvent_iterate_cross hG hh hk hhk hx N M
    calc ‖accretiveEulerProduct G t a x - accretiveEulerProduct G t b x‖
        = ‖(accretiveResolvent G h)^[N] x - (accretiveResolvent G k)^[M] x‖ := by
          simp [accretiveEulerProduct, h, k, N, M]
      _ ≤ Real.sqrt (resolventStepSq h k N M) * ‖u‖ := hstep
      _ = (t : ℝ) * Real.sqrt (1 / (N : ℝ) + 1 / (M : ℝ)) * ‖u‖ := by rw [hsqrt]
      _ = (t : ℝ) * ‖u‖ * Real.sqrt (1 / (a + 1) + 1 / (b + 1)) := by
          rw [mul_right_comm]
          simp [N, M]

omit [CompleteSpace X] in
/-- Euler products at two times differ by at most the time gap times a graph slope. -/
lemma norm_accretiveEulerProduct_time {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (n : ℕ) (s t : ℝ≥0) :
    ‖accretiveEulerProduct G s n x - accretiveEulerProduct G t n x‖ ≤
      |(s : ℝ) - (t : ℝ)| * ‖u‖ := by
  by_cases hs : (s : ℝ) = 0
  · rw [NNReal.coe_eq_zero.mp hs, accretiveEulerProduct_zero, norm_sub_rev]
    have hsub := norm_accretiveEulerProduct_sub hG hx n t
    simpa [sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)] using hsub
  · by_cases ht : (t : ℝ) = 0
    · rw [NNReal.coe_eq_zero.mp ht, accretiveEulerProduct_zero]
      have hsub := norm_accretiveEulerProduct_sub hG hx n s
      simpa [zero_sub, abs_neg, abs_of_nonneg (NNReal.coe_nonneg s)] using hsub
    · have hs0 : 0 < (s : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg s) (Ne.symm hs)
      have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht)
      set N : ℕ := n + 1
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      rcases le_total (s : ℝ) (t : ℝ) with hst | hts
      · set lam : ℝ := (s : ℝ) / N
        set mu : ℝ := (t : ℝ) / N
        have hlam : 0 < lam := by positivity
        have hmu : 0 < mu := by positivity
        have hle : lam ≤ mu := by unfold lam mu; gcongr
        have hstep := norm_accretiveResolvent_iterate_same_count hG hlam hmu hle hx N
        have hgap : (N : ℝ) * (mu - lam) = (t : ℝ) - (s : ℝ) := by
          unfold lam mu
          rw [div_sub_div_same, mul_div_cancel₀ _ hN0]
        calc ‖accretiveEulerProduct G s n x - accretiveEulerProduct G t n x‖
            = ‖(accretiveResolvent G lam)^[N] x - (accretiveResolvent G mu)^[N] x‖ := by
              simp [accretiveEulerProduct, lam, mu, N]
          _ ≤ (N : ℝ) * (mu - lam) * ‖u‖ := hstep
          _ = ((t : ℝ) - (s : ℝ)) * ‖u‖ := by rw [hgap]
          _ = |(s : ℝ) - (t : ℝ)| * ‖u‖ := by
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
      · set lam : ℝ := (t : ℝ) / N
        set mu : ℝ := (s : ℝ) / N
        have hlam : 0 < lam := by positivity
        have hmu : 0 < mu := by positivity
        have hle : lam ≤ mu := by unfold lam mu; gcongr
        have hstep := norm_accretiveResolvent_iterate_same_count hG hlam hmu hle hx N
        have hgap : (N : ℝ) * (mu - lam) = (s : ℝ) - (t : ℝ) := by
          unfold lam mu
          rw [div_sub_div_same, mul_div_cancel₀ _ hN0]
        calc ‖accretiveEulerProduct G s n x - accretiveEulerProduct G t n x‖
            = ‖(accretiveResolvent G lam)^[N] x - (accretiveResolvent G mu)^[N] x‖ := by
              rw [norm_sub_rev]
              simp [accretiveEulerProduct, lam, mu, N]
          _ ≤ (N : ℝ) * (mu - lam) * ‖u‖ := hstep
          _ = ((s : ℝ) - (t : ℝ)) * ‖u‖ := by rw [hgap]
          _ = |(s : ℝ) - (t : ℝ)| * ‖u‖ := by rw [abs_of_nonneg (sub_nonneg.mpr hts)]

omit [CompleteSpace X] in
/-- A positive-time Euler product lands in the graph domain. -/
lemma accretiveEulerProduct_mem_domain {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {t : ℝ≥0} (ht : 0 < (t : ℝ)) (n : ℕ) (x : X) :
    accretiveEulerProduct G t n x ∈ accretiveGraphDomain G := by
  have hpos : 0 < (t : ℝ) / (↑n + 1) := div_pos ht (by positivity)
  have hstep : accretiveEulerProduct G t n x =
      accretiveResolvent G ((t : ℝ) / (↑n + 1))
        ((accretiveResolvent G ((t : ℝ) / (↑n + 1)))^[n] x) := by
    simp [accretiveEulerProduct, iterate_succ_apply']
  rw [hstep]
  exact accretiveResolvent_mem_domain hG hpos _

omit [CompleteSpace X] in
/-- Euler products from a graph point are Cauchy, at a square-root rate uniform on bounded time. -/
lemma accretiveEulerProduct_cauchy_domain {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (t : ℝ≥0) :
    CauchySeq (fun n => accretiveEulerProduct G t n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => (t : ℝ) * ‖u‖ * Real.sqrt (2 / ((N : ℝ) + 1))) atTop
      (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => (2 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have hmul := (tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simp only [mul_zero] at hmul
      refine hmul.congr fun N => ?_
      ring
    have hsq : Tendsto (fun N : ℕ => Real.sqrt (2 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hinv
      simp only [Real.sqrt_zero] at hcomp
      exact hcomp
    have hmul := (tendsto_const_nhds (x := (t : ℝ) * ‖u‖)).mul hsq
    simp only [mul_zero] at hmul
    exact hmul
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  have hsmall : (t : ℝ) * ‖u‖ * Real.sqrt (2 / ((N : ℝ) + 1)) < ε := by
    have hdist := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
  refine ⟨N, fun m hm n hn => ?_⟩
  have hpair (p q : ℕ) (hp : N ≤ p) (hq : N ≤ q) :
      (t : ℝ) * ‖u‖ * Real.sqrt (1 / ((p : ℝ) + 1) + 1 / ((q : ℝ) + 1)) ≤
        (t : ℝ) * ‖u‖ * Real.sqrt (2 / ((N : ℝ) + 1)) := by
    have hinvk {k : ℕ} (hk : N ≤ k) : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      have hk' : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by gcongr
      have hposN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      simpa [one_div] using inv_anti₀ hposN hk'
    have hsum : (1 : ℝ) / ((p : ℝ) + 1) + 1 / ((q : ℝ) + 1) ≤ 2 / ((N : ℝ) + 1) := by
      have htwo : (2 : ℝ) / ((N : ℝ) + 1) =
          1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
      linarith [hinvk hp, hinvk hq]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum)
      (mul_nonneg (NNReal.coe_nonneg t) (norm_nonneg u))
  rw [dist_eq_norm]
  rcases le_total n m with hnm | hmn
  · exact lt_of_le_of_lt
      ((norm_accretiveEulerProduct_cross hG hx hnm t).trans (hpair m n hm hn)) hsmall
  · rw [norm_sub_rev]
    exact lt_of_le_of_lt
      ((norm_accretiveEulerProduct_cross hG hx hmn t).trans (hpair n m hn hm)) hsmall


end CKMA
