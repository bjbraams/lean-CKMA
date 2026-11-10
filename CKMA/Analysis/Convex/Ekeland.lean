/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import TauCeti.Topology.MetricSpace.Ekeland

/-!
# Ekeland's variational principle

The objective is extended-real valued, lower semicontinuous, and bounded below by a real
constant on a complete metric space. A finite approximate minimizer and positive error and
distance scales determine a nearby finite point satisfying a strict penalized variational
inequality. The real lower bound and finite initial value already imply properness.
The proof applies TauCeti's real-valued variational principle on the complete closed sublevel
through the initial point, then extends the strict inequality to the full space.
Source: GAPS 12.45.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set

/-- Ekeland's strict variational inequality at a selected point. -/
def IsEkelandPoint {X : Type*} [MetricSpace X] (f : X → EReal) (a : ℝ) (x : X) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ y, y ≠ x → f x - (a * dist y x : ℝ) < f y

/-- **12.45**: Ekeland's variational principle with explicit positive error and distance scales.
Properness, a finite initial value and a real lower bound prevent arithmetic with `-∞`. -/
theorem exists_isEkelandPoint {X : Type*} [MetricSpace X] [CompleteSpace X]
    (f : X → EReal) (hl : LowerSemicontinuous f)
    (hbelow : ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) {x₀ : X}
    (hfinite : f x₀ ≠ ⊤) (happrox : f x₀ ≤ (⨅ x, f x) + (ε : ℝ)) :
    ∃ x, dist x x₀ ≤ r ∧ f x ≤ f x₀ ∧ IsEkelandPoint f (ε / r) x := by
  rcases hbelow with ⟨b, hb⟩
  have hbot (x : X) : f x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) (hb x)
  let S := {x : X | f x ≤ f x₀}
  have hS : IsClosed S := hl.isClosed_preimage _
  let : IsClosed S := hS
  let : CompleteSpace S := IsClosed.completeSpace_coe
  let z₀ : S := ⟨x₀, by dsimp [S]; exact le_rfl⟩
  have htop (z : S) : f z ≠ ⊤ := ne_top_of_le_ne_top hfinite z.property
  have hreal (z : S) : ((f z).toReal : EReal) = f z :=
    EReal.coe_toReal (htop z) (hbot z)
  have hgl : LowerSemicontinuous (fun z : S => (f z).toReal) := by
    refine lowerSemicontinuous_iff_isClosed_preimage.2 fun a => ?_
    have hc : IsClosed {z : S | f z ≤ (a : EReal)} :=
      (hl.comp (g := fun z : S => (z : X)) continuous_subtype_val).isClosed_preimage _
    convert hc using 1
    ext z
    change (f z).toReal ≤ a ↔ f z ≤ (a : EReal)
    rw [← hreal z]
    simp only [EReal.toReal_coe, EReal.coe_le_coe_iff]
  have hgb : BddBelow (range fun z : S => (f z).toReal) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hh := hb z
    rw [← hreal z, EReal.coe_le_coe_iff] at hh
    exact hh
  obtain ⟨z, hz, hstrict⟩ :=
    hgl.exists_add_mul_dist_le_and_lt_add_mul_dist hgb (div_pos hε hr) z₀
  have happrox' : (f x₀).toReal ≤ (f z).toReal + ε := by
    have hh := happrox.trans (add_le_add (iInf_le f (z : X)) (le_refl (ε : EReal)))
    rw [← EReal.coe_toReal hfinite (hbot x₀), ← hreal z,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
    exact hh
  have hdist : dist (z : X) x₀ ≤ r := by
    change (f z).toReal + ε / r * dist (z : X) x₀ ≤ (f x₀).toReal at hz
    have hh : ε / r * dist (z : X) x₀ ≤ ε := by linarith
    apply (mul_le_mul_iff_right₀ (div_pos hε hr)).mp
    convert hh using 1; field_simp
  refine ⟨z, hdist, z.property, hbot z, htop z, fun y hy => ?_⟩
  by_cases hyS : y ∈ S
  · have hs := hstrict (⟨y, hyS⟩ : S) (by intro heq; exact hy (congrArg Subtype.val heq))
    change (f z).toReal < (f y).toReal + ε / r * dist y (z : X) at hs
    rw [← hreal z, ← hreal (⟨y, hyS⟩ : S), ← EReal.coe_sub, EReal.coe_lt_coe_iff]
    linarith
  · have hygt : f x₀ < f y := lt_of_not_ge hyS
    apply lt_of_le_of_lt _ hygt
    have ha : (0 : EReal) ≤ ((ε / r * dist y (z : X) : ℝ) : EReal) :=
      EReal.coe_nonneg.2 (mul_nonneg (div_pos hε hr).le dist_nonneg)
    calc
      _ ≤ f z := by simpa only [sub_zero] using EReal.sub_le_sub (le_refl (f z)) ha
      _ ≤ f x₀ := z.property


end CKMA
