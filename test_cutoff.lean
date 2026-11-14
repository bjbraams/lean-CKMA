
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def heisenbergBaseBump : ContDiffBump (0 : V) := ⟨1, 2, zero_lt_one, one_lt_two⟩
def heisenbergFreqBump (n : ℕ) (x : V) : ℝ := (heisenbergBaseBump : ContDiffBump (0 : V)) (((n : ℝ) + 1)⁻¹ • x)

def freqBumpScaled (n : ℕ) : V → ℂ := fun x ↦ (heisenbergFreqBump n x : ℂ)

private lemma freqBumpScaled_hasTemperateGrowth (n : ℕ) :
    Function.HasTemperateGrowth (freqBumpScaled n : V → ℂ) := by
  have hEq : (freqBumpScaled n : V → ℂ) = Complex.ofReal ∘ (heisenbergFreqBump n : V → ℝ) := by funext x; rfl
  sorry
