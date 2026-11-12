/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.DyadicHolder

/-!
# Hölder control from dyadic increments

Consecutive dyadic increments on each integer interval determine a Hölder bound on the dyadic
points of a compact time interval. Dyadic floors of two real times stay within one mesh of the
times themselves, so the same bound passes to every uniform limit of the floors.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset

/-- Consecutive increments of `f` on the integer interval starting at `j` obey a dyadic bound. -/
def HasDyadicIncrements (f : ℝ → ℝ) (α K : ℝ) (j : ℕ) : Prop :=
  ∀ n, ∀ i : ℕ, i < 2 ^ n →
    |f (↑j + (↑i + 1) / 2 ^ n) - f (↑j + (↑i : ℝ) / 2 ^ n)| ≤
      K * ((1 : ℝ) / 2 ^ n) ^ α

/-- Absolute size of one dyadic increment, scaled by the mesh to the power `α`. -/
def incrementRatio (f : ℝ → ℝ) (α : ℝ) (j n i : ℕ) : ℝ :=
  |f (↑j + (↑i + 1) / 2 ^ n) - f (↑j + (↑i : ℝ) / 2 ^ n)| * (2 : ℝ) ^ (α * ↑n)

/-- Ratios of the increments of level strictly less than `N` on the interval starting at `j`. -/
def ratioList (f : ℝ → ℝ) (α : ℝ) (j N : ℕ) : List ℝ :=
  (List.range N).flatMap fun n =>
    (List.range (2 ^ n)).map fun i => incrementRatio f α j n i

/-- A constant dominating `1` and every increment ratio of level less than `N`. -/
def holderConstFrom (f : ℝ → ℝ) (α : ℝ) (j N : ℕ) : ℝ :=
  (ratioList f α j N).foldr max 1

/-- Every entry of a list is at most the maximum against a fixed seed. -/
lemma le_foldr_max {l : List ℝ} {a x : ℝ} (hx : x ∈ l) : x ≤ l.foldr max a := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.foldr_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

/-- The seed of a maximum is at most the maximum. -/
lemma le_foldr_max_self {l : List ℝ} {a : ℝ} : a ≤ l.foldr max a := by
  induction l with
  | nil => simp
  | cons _ ys ih =>
    rw [List.foldr_cons]
    exact ih.trans (le_max_right _ _)

/-- The constant built from increment ratios is at least `1`. -/
lemma one_le_holderConstFrom (f : ℝ → ℝ) (α : ℝ) (j N : ℕ) : 1 ≤ holderConstFrom f α j N :=
  le_foldr_max_self

/-- The constant built from increment ratios is nonnegative. -/
lemma holderConstFrom_nonneg (f : ℝ → ℝ) (α : ℝ) (j N : ℕ) : 0 ≤ holderConstFrom f α j N :=
  le_trans (by norm_num) (one_le_holderConstFrom f α j N)

/-- An early increment ratio appears in the list used to build the constant. -/
lemma mem_ratioList {f : ℝ → ℝ} {α : ℝ} {j N n i : ℕ} (hn : n < N) (hi : i < 2 ^ n) :
    incrementRatio f α j n i ∈ ratioList f α j N := by
  refine List.mem_flatMap.2 ⟨n, List.mem_range.2 hn, ?_⟩
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

/-- `(1 / 2 ^ n) ^ α` is the negative real power `2 ^ (-α n)`. -/
lemma one_div_two_pow_rpow {α : ℝ} (_hα : 0 ≤ α) (n : ℕ) :
    ((1 : ℝ) / 2 ^ n) ^ α = (2 : ℝ) ^ (-(α * ↑n)) := by
  have h2 : (0 : ℝ) ≤ 2 := by positivity
  calc
    ((1 : ℝ) / 2 ^ n) ^ α = (((2 : ℝ) ^ n)⁻¹) ^ α := by rw [one_div]
    _ = (((2 : ℝ) ^ (n : ℝ))⁻¹) ^ α := by rw [← Real.rpow_natCast]
    _ = ((2 : ℝ) ^ (-(n : ℝ))) ^ α := by rw [← Real.rpow_neg h2]
    _ = (2 : ℝ) ^ ((-(n : ℝ)) * α) := by rw [← Real.rpow_mul h2]
    _ = (2 : ℝ) ^ (-(α * ↑n)) := by ring_nf

/-- Eventual unit increment bounds produce a finite dyadic Hölder constant. -/
lemma hasDyadicIncrements_of_eventually {f : ℝ → ℝ} {α : ℝ} {j N : ℕ} (hα : 0 ≤ α)
    (hN : ∀ n, N ≤ n → ∀ i : ℕ, i < 2 ^ n →
      |f (↑j + (↑i + 1) / 2 ^ n) - f (↑j + (↑i : ℝ) / 2 ^ n)| ≤ ((1 : ℝ) / 2 ^ n) ^ α) :
    HasDyadicIncrements f α (holderConstFrom f α j N) j := by
  intro n i hi
  have hK : 1 ≤ holderConstFrom f α j N := one_le_holderConstFrom f α j N
  by_cases hn : n < N
  · have hratio : incrementRatio f α j n i ≤ holderConstFrom f α j N :=
      le_foldr_max (mem_ratioList hn hi)
    have hpow : 0 < (2 : ℝ) ^ (α * ↑n) := Real.rpow_pos_of_pos (by norm_num) _
    have hΔ : |f (↑j + (↑i + 1) / 2 ^ n) - f (↑j + (↑i : ℝ) / 2 ^ n)| ≤
        holderConstFrom f α j N / (2 : ℝ) ^ (α * ↑n) :=
      (le_div_iff₀ hpow).2 hratio
    calc
      |f (↑j + (↑i + 1) / 2 ^ n) - f (↑j + (↑i : ℝ) / 2 ^ n)| ≤
          holderConstFrom f α j N / (2 : ℝ) ^ (α * ↑n) := hΔ
      _ = holderConstFrom f α j N * (2 : ℝ) ^ (-(α * ↑n)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
      _ = holderConstFrom f α j N * ((1 : ℝ) / 2 ^ n) ^ α := by rw [one_div_two_pow_rpow hα]
  · have hn' : N ≤ n := by omega
    exact (hN n hn' i hi).trans <| by
      nth_rw 1 [← one_mul (((1 : ℝ) / 2 ^ n) ^ α)]
      exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (by positivity) _)

/-- Dividing an integer decomposition `m * 2 ^ L + k` recovers the integer and the remainder. -/
lemma nat_cast_div_mul_add (m k L : ℕ) :
    ((m * 2 ^ L + k : ℕ) : ℝ) / 2 ^ L = (m : ℝ) + (k : ℝ) / 2 ^ L := by
  have hpow : (2 : ℝ) ^ L ≠ 0 := by positivity
  rw [Nat.cast_add, Nat.cast_mul]
  push_cast
  rw [add_div, mul_div_cancel_right₀ _ hpow]

/-- Increments on one integer interval control every dyadic pair inside that interval. -/
lemma abs_sub_on_unit {f : ℝ → ℝ} {α K : ℝ} {j L a b : ℕ}
    (hα : 0 < α) (hK : 0 ≤ K) (hinc : HasDyadicIncrements f α K j)
    (hab : a ≤ b) (hb : b ≤ 2 ^ L) :
    |f (↑j + (b : ℝ) / 2 ^ L) - f (↑j + (a : ℝ) / 2 ^ L)| ≤
      dyadicHolderFactor α * K * (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α := by
  exact abs_sub_le_of_dyadic_grid (f := fun u => f (↑j + u)) hα hK
    (fun n _ i hi => hinc n i hi) hab hb

/-- Dyadic increments on `[0, N]` control every pair of dyadic points in that interval. -/
lemma abs_sub_on_units {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N : ℕ} (hα : 0 < α)
    (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j) :
    ∀ L a b, a ≤ b → b ≤ N * 2 ^ L →
      |f ((b : ℝ) / 2 ^ L) - f ((a : ℝ) / 2 ^ L)| ≤
        dyadicHolderFactor α * (∑ j ∈ range N, K j) *
          (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α := by
  induction N with
  | zero =>
    intro L a b hab hb
    have hb0 : b = 0 := by simpa using hb
    have ha0 : a = 0 := by omega
    subst ha0
    subst hb0
    simp [Real.zero_rpow hα.ne', abs_zero]
  | succ N ih =>
    intro L a b hab hb
    have hfact : 0 ≤ dyadicHolderFactor α := le_of_lt (dyadicHolderFactor_pos hα)
    have hpow : 0 ≤ (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α := Real.rpow_nonneg (by positivity) _
    have hsplit : ∑ j ∈ range (N + 1), K j = (∑ j ∈ range N, K j) + K N := by
      simp [Finset.sum_range_succ]
    have hsumN : 0 ≤ ∑ j ∈ range N, K j :=
      Finset.sum_nonneg fun j hj => hK j (by rw [mem_range] at hj; omega)
    have hKN : 0 ≤ K N := hK N (by omega)
    have hpivot : (N + 1) * 2 ^ L = N * 2 ^ L + 2 ^ L := by ring
    set pivot : ℕ := N * 2 ^ L
    have hb_last : b ≤ pivot + 2 ^ L := by simpa [pivot, hpivot] using hb
    by_cases hble : b ≤ pivot
    · have hleft := ih (fun j hj => hK j (Nat.lt_succ_of_lt hj))
        (fun j hj => hinc j (Nat.lt_succ_of_lt hj)) L a b hab hble
      have hsum_le : ∑ j ∈ range N, K j ≤ ∑ j ∈ range (N + 1), K j := by
        rw [hsplit]
        exact le_add_of_nonneg_right hKN
      exact hleft.trans <| mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum_le hfact) hpow
    · by_cases hage : pivot ≤ a
      · set a0 : ℕ := a - pivot
        set b0 : ℕ := b - pivot
        have hab0 : a0 ≤ b0 := by omega
        have hb0 : b0 ≤ 2 ^ L := by omega
        have hunit := abs_sub_on_unit hα hKN (hinc N (by omega)) hab0 hb0
        have hpa : (a : ℝ) / 2 ^ L = (N : ℝ) + (a0 : ℝ) / 2 ^ L := by
          have haeq : a = N * 2 ^ L + a0 := by omega
          rw [haeq]
          simpa [Nat.cast_pow] using nat_cast_div_mul_add N a0 L
        have hpb : (b : ℝ) / 2 ^ L = (N : ℝ) + (b0 : ℝ) / 2 ^ L := by
          have hbeq : b = N * 2 ^ L + b0 := by omega
          rw [hbeq]
          simpa [Nat.cast_pow] using nat_cast_div_mul_add N b0 L
        have hgap : b0 - a0 = b - a := by omega
        rw [hpa, hpb]
        have hsum_le : K N ≤ ∑ j ∈ range (N + 1), K j := by
          rw [hsplit]
          exact le_add_of_nonneg_left hsumN
        calc
          |f ((N : ℝ) + (b0 : ℝ) / 2 ^ L) - f ((N : ℝ) + (a0 : ℝ) / 2 ^ L)| ≤
              dyadicHolderFactor α * K N * (((b0 - a0 : ℕ) : ℝ) / 2 ^ L) ^ α := hunit
          _ = dyadicHolderFactor α * K N * (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α := by rw [hgap]
          _ ≤ dyadicHolderFactor α * (∑ j ∈ range (N + 1), K j) *
              (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le hfact) hpow
      · have hap : a ≤ pivot := by omega
        have hpb : pivot ≤ b := by omega
        set b0 : ℕ := b - pivot
        have hleft := ih (fun j hj => hK j (Nat.lt_succ_of_lt hj))
          (fun j hj => hinc j (Nat.lt_succ_of_lt hj)) L a pivot hap le_rfl
        have hright := abs_sub_on_unit hα hKN (hinc N (by omega))
          (by omega : 0 ≤ b0) (by omega : b0 ≤ 2 ^ L)
        have hpa : (pivot : ℝ) / 2 ^ L = (N : ℝ) := by
          dsimp [pivot]
          rw [Nat.cast_mul, Nat.cast_pow]
          exact mul_div_cancel_right₀ (N : ℝ) (by positivity)
        have hpb' : (b : ℝ) / 2 ^ L = (N : ℝ) + (b0 : ℝ) / 2 ^ L := by
          have hbeq : b = N * 2 ^ L + b0 := by omega
          nth_rw 1 [hbeq]
          exact nat_cast_div_mul_add N b0 L
        have hgapL : pivot - a ≤ b - a := by omega
        have hgapR : b0 ≤ b - a := by omega
        have hdistL : (((pivot - a : ℕ) : ℝ) / 2 ^ L) ^ α ≤
            (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α :=
          Real.rpow_le_rpow (by positivity) (by gcongr) hα.le
        have hdistR : ((b0 : ℝ) / 2 ^ L) ^ α ≤
            (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α :=
          Real.rpow_le_rpow (by positivity) (by gcongr) hα.le
        have hleft' : |f ((pivot : ℝ) / 2 ^ L) - f ((a : ℝ) / 2 ^ L)| ≤
            dyadicHolderFactor α * (∑ j ∈ range N, K j) *
              (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α :=
          hleft.trans (mul_le_mul_of_nonneg_left hdistL (mul_nonneg hfact hsumN))
        have hright' : |f ((b : ℝ) / 2 ^ L) - f ((pivot : ℝ) / 2 ^ L)| ≤
            dyadicHolderFactor α * K N * (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α := by
          rw [Nat.cast_zero, zero_div, add_zero, Nat.sub_zero] at hright
          rw [hpa, hpb']
          exact hright.trans (mul_le_mul_of_nonneg_left hdistR (mul_nonneg hfact hKN))
        have habs := abs_sub_le (f ((b : ℝ) / 2 ^ L)) (f ((pivot : ℝ) / 2 ^ L))
          (f ((a : ℝ) / 2 ^ L))
        calc
          |f ((b : ℝ) / 2 ^ L) - f ((a : ℝ) / 2 ^ L)| ≤
              |f ((b : ℝ) / 2 ^ L) - f ((pivot : ℝ) / 2 ^ L)| +
                |f ((pivot : ℝ) / 2 ^ L) - f ((a : ℝ) / 2 ^ L)| := habs
          _ ≤ dyadicHolderFactor α * K N * (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α +
                dyadicHolderFactor α * (∑ j ∈ range N, K j) *
                  (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α :=
            add_le_add hright' hleft'
          _ = dyadicHolderFactor α * (∑ j ∈ range (N + 1), K j) *
                (((b - a : ℕ) : ℝ) / 2 ^ L) ^ α := by
            rw [hsplit]
            ring

/-- Left dyadic floor of a nonnegative real, at mesh `2 ^ (-n)`. -/
def dyadicFloorReal (n : ℕ) (t : ℝ) : ℝ :=
  (Nat.floor (t * 2 ^ n) : ℝ) / 2 ^ n

/-- The dyadic floor of a nonnegative real is nonnegative. -/
lemma dyadicFloorReal_nonneg {n : ℕ} {t : ℝ} (_ht : 0 ≤ t) : 0 ≤ dyadicFloorReal n t := by
  dsimp [dyadicFloorReal]
  positivity

/-- The dyadic floor does not exceed its argument. -/
lemma dyadicFloorReal_le {n : ℕ} {t : ℝ} (ht : 0 ≤ t) : dyadicFloorReal n t ≤ t := by
  dsimp [dyadicFloorReal]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
  exact_mod_cast Nat.floor_le (mul_nonneg ht (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))

/-- A nonnegative real lies strictly below its dyadic floor plus one mesh. -/
lemma lt_dyadicFloorReal_add {n : ℕ} {t : ℝ} (_ht : 0 ≤ t) :
    t < dyadicFloorReal n t + 1 / 2 ^ n := by
  dsimp [dyadicFloorReal]
  have hlt : t * 2 ^ n < (Nat.floor (t * 2 ^ n) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [← add_div]
  exact (lt_div_iff₀ hpow).2 hlt

/-- Dyadic floors of two nonnegative reals differ by at most the times plus one mesh. -/
lemma abs_dyadicFloorReal_sub {n : ℕ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |dyadicFloorReal n s - dyadicFloorReal n t| ≤ |s - t| + 1 / 2 ^ n := by
  have hsle : dyadicFloorReal n s ≤ s := dyadicFloorReal_le (n := n) hs
  have htle : dyadicFloorReal n t ≤ t := dyadicFloorReal_le (n := n) ht
  have hsge : s - 1 / 2 ^ n ≤ dyadicFloorReal n s :=
    le_of_lt (by linarith [lt_dyadicFloorReal_add (n := n) hs])
  have htge : t - 1 / 2 ^ n ≤ dyadicFloorReal n t :=
    le_of_lt (by linarith [lt_dyadicFloorReal_add (n := n) ht])
  refine abs_le.2 ⟨?_, ?_⟩
  · calc
      -( |s - t| + 1 / 2 ^ n) ≤ (s - 1 / 2 ^ n) - t := by
        have hsabs : -|s - t| ≤ s - t := neg_abs_le _
        linarith
      _ ≤ dyadicFloorReal n s - dyadicFloorReal n t := by linarith
  · calc
      dyadicFloorReal n s - dyadicFloorReal n t ≤ s - (t - 1 / 2 ^ n) := by linarith
      _ ≤ |s - t| + 1 / 2 ^ n := by
        have hsabs : s - t ≤ |s - t| := le_abs_self _
        linarith

/-- The numerator of a dyadic floor on `[0, N]` is at most `N * 2 ^ n`. -/
lemma dyadicFloorReal_num_le {n N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ N) :
    Nat.floor (t * 2 ^ n) ≤ N * 2 ^ n := by
  have hx : t * 2 ^ n ≤ ((N * 2 ^ n : ℕ) : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using
      mul_le_mul_of_nonneg_right htN (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hlt : t * 2 ^ n < ((N * 2 ^ n + 1 : ℕ) : ℝ) :=
    hx.trans_lt (by exact_mod_cast Nat.lt_succ_self (N * 2 ^ n))
  exact Nat.lt_succ_iff.mp ((Nat.floor_lt (by positivity)).2 hlt)

/-- Values of `f` at dyadic floors obey the Hölder bound of the underlying increments. -/
lemma abs_sub_dyadicFloor_le {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N n : ℕ}
    (hα : 0 < α) (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j)
    {s t : ℝ} (hs0 : 0 ≤ s) (hsN : s ≤ ↑N) (ht0 : 0 ≤ t) (htN : t ≤ ↑N) :
    |f (dyadicFloorReal n t) - f (dyadicFloorReal n s)| ≤
      dyadicHolderFactor α * (∑ j ∈ range N, K j) * (|s - t| + 1 / 2 ^ n) ^ α := by
  set as : ℕ := Nat.floor (s * 2 ^ n)
  set bt : ℕ := Nat.floor (t * 2 ^ n)
  have has_le : as ≤ N * 2 ^ n := dyadicFloorReal_num_le hs0 hsN
  have hbt_le : bt ≤ N * 2 ^ n := dyadicFloorReal_num_le ht0 htN
  have hfloor_s : dyadicFloorReal n s = (as : ℝ) / 2 ^ n := rfl
  have hfloor_t : dyadicFloorReal n t = (bt : ℝ) / 2 ^ n := rfl
  have hmesh : |(as : ℝ) / 2 ^ n - (bt : ℝ) / 2 ^ n| ≤ |s - t| + 1 / 2 ^ n := by
    simpa [hfloor_s, hfloor_t] using abs_dyadicFloorReal_sub (n := n) hs0 ht0
  have hlo : min as bt ≤ max as bt := min_le_max
  have hhi : max as bt ≤ N * 2 ^ n := max_le has_le hbt_le
  have hbound := abs_sub_on_units hα hK hinc n (min as bt) (max as bt) hlo hhi
  have hgap : ((max as bt - min as bt : ℕ) : ℝ) / 2 ^ n =
      |(as : ℝ) / 2 ^ n - (bt : ℝ) / 2 ^ n| := by
    rcases le_total as bt with hab | hba
    · rw [max_eq_right hab, min_eq_left hab]
      have hnonneg : 0 ≤ (bt : ℝ) / 2 ^ n - (as : ℝ) / 2 ^ n := by
        rw [← sub_div]
        exact div_nonneg (sub_nonneg.2 (by exact_mod_cast hab)) (by positivity)
      calc
        ((bt - as : ℕ) : ℝ) / 2 ^ n = ((bt : ℝ) - (as : ℝ)) / 2 ^ n := by
          rw [Nat.cast_sub hab]
        _ = (bt : ℝ) / 2 ^ n - (as : ℝ) / 2 ^ n := sub_div _ _ _
        _ = |(as : ℝ) / 2 ^ n - (bt : ℝ) / 2 ^ n| := by
          rw [abs_sub_comm]
          exact (abs_of_nonneg hnonneg).symm
    · rw [max_eq_left hba, min_eq_right hba]
      have hnonneg : 0 ≤ (as : ℝ) / 2 ^ n - (bt : ℝ) / 2 ^ n := by
        rw [← sub_div]
        exact div_nonneg (sub_nonneg.2 (by exact_mod_cast hba)) (by positivity)
      calc
        ((as - bt : ℕ) : ℝ) / 2 ^ n = ((as : ℝ) - (bt : ℝ)) / 2 ^ n := by
          rw [Nat.cast_sub hba]
        _ = (as : ℝ) / 2 ^ n - (bt : ℝ) / 2 ^ n := sub_div _ _ _
        _ = |(as : ℝ) / 2 ^ n - (bt : ℝ) / 2 ^ n| := (abs_of_nonneg hnonneg).symm
  have hdist : (((max as bt - min as bt : ℕ) : ℝ) / 2 ^ n) ^ α ≤
      (|s - t| + 1 / 2 ^ n) ^ α := by
    rw [hgap]
    exact Real.rpow_le_rpow (by positivity) hmesh hα.le
  have hsym : |f ((bt : ℝ) / 2 ^ n) - f ((as : ℝ) / 2 ^ n)| =
      |f (((max as bt : ℕ) : ℝ) / 2 ^ n) - f (((min as bt : ℕ) : ℝ) / 2 ^ n)| := by
    rcases le_total as bt with hab | hba
    · rw [max_eq_right hab, min_eq_left hab]
    · rw [max_eq_left hba, min_eq_right hba, abs_sub_comm]
  rw [hfloor_s, hfloor_t, hsym]
  exact hbound.trans <| mul_le_mul_of_nonneg_left hdist <|
    mul_nonneg (le_of_lt (dyadicHolderFactor_pos hα))
      (Finset.sum_nonneg fun j hj => hK j (mem_range.mp hj))

/-- The distance between two dyadic rationals equals the normalized numerator gap. -/
lemma abs_natCast_div_sub (L a b : ℕ) :
    ((max a b - min a b : ℕ) : ℝ) / 2 ^ L =
      |(a : ℝ) / 2 ^ L - (b : ℝ) / 2 ^ L| := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_left hab]
    have hnonneg : 0 ≤ (b : ℝ) / 2 ^ L - (a : ℝ) / 2 ^ L := by
      rw [← sub_div]
      exact div_nonneg (sub_nonneg.2 (by exact_mod_cast hab)) (by positivity)
    calc
      ((b - a : ℕ) : ℝ) / 2 ^ L = ((b : ℝ) - (a : ℝ)) / 2 ^ L := by rw [Nat.cast_sub hab]
      _ = (b : ℝ) / 2 ^ L - (a : ℝ) / 2 ^ L := sub_div _ _ _
      _ = |(a : ℝ) / 2 ^ L - (b : ℝ) / 2 ^ L| := by
        rw [abs_sub_comm]
        exact (abs_of_nonneg hnonneg).symm
  · rw [max_eq_left hba, min_eq_right hba]
    have hnonneg : 0 ≤ (a : ℝ) / 2 ^ L - (b : ℝ) / 2 ^ L := by
      rw [← sub_div]
      exact div_nonneg (sub_nonneg.2 (by exact_mod_cast hba)) (by positivity)
    calc
      ((a - b : ℕ) : ℝ) / 2 ^ L = ((a : ℝ) - (b : ℝ)) / 2 ^ L := by rw [Nat.cast_sub hba]
      _ = (a : ℝ) / 2 ^ L - (b : ℝ) / 2 ^ L := sub_div _ _ _
      _ = |(a : ℝ) / 2 ^ L - (b : ℝ) / 2 ^ L| := (abs_of_nonneg hnonneg).symm

/-- Values at two points of one dyadic grid obey the summed Hölder bound. -/
lemma abs_sub_dyadic_num {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N L a b : ℕ}
    (hα : 0 < α) (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j)
    (ha : a ≤ N * 2 ^ L) (hb : b ≤ N * 2 ^ L) :
    |f ((b : ℝ) / 2 ^ L) - f ((a : ℝ) / 2 ^ L)| ≤
      dyadicHolderFactor α * (∑ j ∈ range N, K j) *
        |(a : ℝ) / 2 ^ L - (b : ℝ) / 2 ^ L| ^ α := by
  have hlo : min a b ≤ max a b := min_le_max
  have hhi : max a b ≤ N * 2 ^ L := max_le ha hb
  have hbound := abs_sub_on_units hα hK hinc L (min a b) (max a b) hlo hhi
  have hgap := abs_natCast_div_sub L a b
  have hsym : |f ((b : ℝ) / 2 ^ L) - f ((a : ℝ) / 2 ^ L)| =
      |f (((max a b : ℕ) : ℝ) / 2 ^ L) - f (((min a b : ℕ) : ℝ) / 2 ^ L)| := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, min_eq_left hab]
    · rw [max_eq_left hba, min_eq_right hba, abs_sub_comm]
  rw [hsym]
  refine hbound.trans <| mul_le_mul_of_nonneg_left ?_ ?_
  · rw [← hgap]
  · exact mul_nonneg (le_of_lt (dyadicHolderFactor_pos hα))
      (Finset.sum_nonneg fun j hj => hK j (mem_range.mp hj))

/-- A coarser dyadic floor, written on a finer dyadic grid. -/
lemma dyadicFloorReal_refine {n m : ℕ} {t : ℝ} (_ht : 0 ≤ t) (hnm : n ≤ m) :
    dyadicFloorReal n t =
      ((Nat.floor (t * 2 ^ n) * 2 ^ (m - n) : ℕ) : ℝ) / 2 ^ m := by
  have hpos : (2 : ℝ) ^ (m - n) ≠ 0 := by positivity
  calc
    dyadicFloorReal n t = (Nat.floor (t * 2 ^ n) : ℝ) / 2 ^ n := rfl
    _ = ((Nat.floor (t * 2 ^ n) : ℝ) * (2 : ℝ) ^ (m - n)) /
          ((2 : ℝ) ^ n * (2 : ℝ) ^ (m - n)) := by
      rw [mul_div_mul_right _ _ hpos]
    _ = ((Nat.floor (t * 2 ^ n) : ℝ) * (2 : ℝ) ^ (m - n)) / 2 ^ m := by
      rw [← pow_add, Nat.add_sub_of_le hnm]
    _ = ((Nat.floor (t * 2 ^ n) * 2 ^ (m - n) : ℕ) : ℝ) / 2 ^ m := by
      rw [Nat.cast_mul, Nat.cast_pow]
      push_cast
      rfl

/-- The refined numerator of a dyadic floor on `[0, N]` stays inside that grid. -/
lemma dyadicFloorReal_refine_num_le {n m N : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (htN : t ≤ N) (hnm : n ≤ m) :
    Nat.floor (t * 2 ^ n) * 2 ^ (m - n) ≤ N * 2 ^ m := by
  have hnum := dyadicFloorReal_num_le (n := n) (N := N) ht0 htN
  calc
    Nat.floor (t * 2 ^ n) * 2 ^ (m - n) ≤ N * 2 ^ n * 2 ^ (m - n) :=
      Nat.mul_le_mul_right _ hnum
    _ = N * (2 ^ n * 2 ^ (m - n)) := by rw [Nat.mul_assoc]
    _ = N * 2 ^ m := by rw [← pow_add, Nat.add_sub_of_le hnm]

/-- Dyadic floors of one nonnegative real, at two meshes, differ by at most those meshes. -/
lemma abs_dyadicFloorReal_levels {n m : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    |dyadicFloorReal n t - dyadicFloorReal m t| ≤ 1 / 2 ^ n + 1 / 2 ^ m := by
  have hdist (k : ℕ) : |t - dyadicFloorReal k t| ≤ 1 / 2 ^ k := by
    have hle : dyadicFloorReal k t ≤ t := dyadicFloorReal_le ht
    have hlt : t < dyadicFloorReal k t + 1 / 2 ^ k := lt_dyadicFloorReal_add ht
    rw [abs_of_nonneg (sub_nonneg.2 hle)]
    exact le_of_lt (by linarith)
  have hn : |dyadicFloorReal n t - t| ≤ 1 / 2 ^ n := by
    rw [abs_sub_comm]
    exact hdist n
  exact (abs_sub_le (dyadicFloorReal n t) t (dyadicFloorReal m t)).trans
    (add_le_add hn (hdist m))

/-- Values at dyadic floors of two meshes obey the Hölder bound of the increments. -/
lemma abs_sub_dyadicFloor_levels {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N n m : ℕ}
    (hα : 0 < α) (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j) (hnm : n ≤ m)
    {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ ↑N) :
    |f (dyadicFloorReal m t) - f (dyadicFloorReal n t)| ≤
      dyadicHolderFactor α * (∑ j ∈ range N, K j) *
        (1 / 2 ^ n + 1 / 2 ^ m) ^ α := by
  set a : ℕ := Nat.floor (t * 2 ^ n) * 2 ^ (m - n)
  set b : ℕ := Nat.floor (t * 2 ^ m)
  have ha : dyadicFloorReal n t = (a : ℝ) / 2 ^ m := by
    simpa [a] using dyadicFloorReal_refine ht0 hnm
  have hb : dyadicFloorReal m t = (b : ℝ) / 2 ^ m := rfl
  have ha_le : a ≤ N * 2 ^ m := dyadicFloorReal_refine_num_le ht0 htN hnm
  have hb_le : b ≤ N * 2 ^ m := dyadicFloorReal_num_le ht0 htN
  have hpair := abs_sub_dyadic_num hα hK hinc ha_le hb_le
  have hmesh : |(a : ℝ) / 2 ^ m - (b : ℝ) / 2 ^ m| ≤ 1 / 2 ^ n + 1 / 2 ^ m := by
    simpa [ha, hb] using abs_dyadicFloorReal_levels (n := n) (m := m) ht0
  rw [ha, hb]
  exact hpair.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hmesh hα.le) <|
    mul_nonneg (le_of_lt (dyadicHolderFactor_pos hα))
      (Finset.sum_nonneg fun j hj => hK j (mem_range.mp hj))

end CKMA
