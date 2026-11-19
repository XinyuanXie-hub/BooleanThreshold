module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.UniformOn

public section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- Affine threshold functions on the sign cube, with `false` for −1 and `true` for 1. -/
def BooleanThresholdFunction (n : ℕ) :=
  {f : (Fin n → Bool) → Bool //
    ∃ (bias : ℝ) (weights : Fin n → ℝ), ∀ x,
      f x = true ↔ 0 < bias + ∑ i, weights i * (if x i then 1 else -1)}

/-- Theorem 1 (Counting Boolean threshold functions). -/
theorem theorem1 :
    ∃ C > (0 : ℝ), ∀ n ≥ (1 : ℕ),
      let T : ℝ := Nat.card (BooleanThresholdFunction n)
      let main : ℝ := 2 * ((2 ^ n - 1).choose n : ℝ)
      |T - main| ≤ C * main / (n : ℝ) ^ 99 := by
  sorry

/-- Theorem 7 (Linear dependence). -/
theorem theorem7 :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n r : ℕ, 1 ≤ r → r < n →
      let cube : Set (Fin n → ℝ) := {x | ∀ i, x i = -1 ∨ x i = 1}
      let law := Measure.pi (fun _ : Fin r => uniformOn cube)
      let p := law.real {v | ¬ LinearIndependent ℝ v}
      |p - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  sorry

end BooleanThreshold
