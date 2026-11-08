/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.KatoRellich

/-!
# Cores of relatively bounded self-adjoint perturbations

The Kato–Rellich perturbation acts on an explicit linear partial-map domain. TauCeti's convention
is `‖Bx‖ ≤ a‖x‖ + b‖Ax‖`, so the coefficient restricted below one is `b`. Every core of the
unperturbed self-adjoint operator remains a core after perturbation, and restriction to such a
core is essentially self-adjoint. The closure corollary uses TauCeti's self-adjoint perturbation
theorem together with the core identity. Source: GAPS 22.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **22.32**: every core of `A` is a core of its Kato–Rellich perturbation.
TauCeti uses `‖Bx‖ ≤ a‖x‖ + b‖Ax‖`, so `b`, rather than `a`, must be less than one. -/
theorem hasCore_add_of_isRelativelyBounded {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) {a b : ℝ}
    (hAB : B.IsRelativelyBounded A a b) (hb : b < 1) {D : Submodule 𝕜 H}
    (hD : A.HasCore D) : (A + B).HasCore D := by
  sorry

/-- The restriction to any original core is essentially self-adjoint. -/
theorem isSelfAdjoint_closure_domRestrict_add {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) {a b : ℝ}
    (hAB : B.IsRelativelyBounded A a b) (hb : b < 1) {D : Submodule 𝕜 H}
    (hD : A.HasCore D) : IsSelfAdjoint ((A + B).domRestrict D).closure := by
  rw [(hasCore_add_of_isRelativelyBounded hA hB hAB hb hD).closure_eq]
  exact hA.add_of_isRelativelyBounded hB hAB hb

end CKMA
