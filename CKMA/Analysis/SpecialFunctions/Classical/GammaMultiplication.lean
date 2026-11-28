/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication

/-!
# Gauss's Gamma multiplication formula

Gauss multiplication relates a finite product of shifted Gamma values to a single Gamma value at
the multiplied argument:
`∏_{j<m} Γ(z + j/m) = (2π)^{(m-1)/2} m^{1/2 - mz} Γ(mz)` for every `m > 0` and every `z : ℂ`.
Under Mathlib's convention `Γ(-n) = 0` both sides vanish at the poles, so no hypothesis on `z` is
needed. The positive real bases fix the principal-power branches.

The formula is TauCeti's `Complex.prod_Gamma_add_div` (DLMF 5.5.6), stated there as a product over
`Finset.range m`; this file restates it as a product over `Fin m`.

## Main results

* `CKMA.gamma_multiplication`: Gauss's multiplication formula for every complex parameter
  (**49.6**).
-/

public section

namespace CKMA

open Complex

/-- **49.6**: Gauss's multiplication formula
`∏_{j : Fin m} Γ(z + j/m) = (2π)^{(m-1)/2} m^{1/2 - mz} Γ(mz)` for every `z : ℂ`. At the poles
`mz ∈ -ℕ` both sides are `0`. This is TauCeti's `Complex.prod_Gamma_add_div` with the product over
`Fin m`. -/
theorem gamma_multiplication (m : ℕ) (hm : 0 < m) (z : ℂ) :
    (∏ j : Fin m, Complex.Gamma (z + (j.val : ℂ) / m)) =
      (2 * Real.pi : ℂ) ^ (((m : ℂ) - 1) / 2) *
      (m : ℂ) ^ ((1 / 2 : ℂ) - (m : ℂ) * z) * Complex.Gamma ((m : ℂ) * z) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => Complex.Gamma (z + (j : ℂ) / m))]
  exact Complex.prod_Gamma_add_div hm z

end CKMA
