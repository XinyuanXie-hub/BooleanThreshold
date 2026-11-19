module

public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

open scoped BigOperators

namespace BooleanThreshold

/-- Affine threshold functions on the sign cube, with `false` for −1 and `true` for 1. -/
def BooleanThresholdFunction (n : ℕ) :=
  {f : (Fin n → Bool) → Bool //
    ∃ (bias : ℝ) (weights : Fin n → ℝ), ∀ x,
      f x = true ↔ 0 < bias + ∑ i, weights i * (if x i then 1 else -1)}

end BooleanThreshold
