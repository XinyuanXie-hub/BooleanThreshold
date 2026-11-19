module

public import BooleanThreshold.CokernelLogMoment
public import Mathlib.Data.Fin.Embedding

public noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- The probability that the square binary determinant is divisible by
each of the selected prime powers. -/
@[expose] def squareDetJointProbability (N K : ℕ) (s : Finset (Nat.primesLE (N ^ K))) (j : s → ℕ) : ℝ :=
  (uniformOn Set.univ).real {A : Fin (N + 1) → Fin (N + 1) → Bool |
    ∀ i : s, i.val.val ^ j i ∣ ((Matrix.of A).map zeroOneBit).det.natAbs}

theorem smallPrimeJointProbability_le_square (N K : ℕ)
    (s : Finset (Nat.primesLE (N ^ K))) (j : s → ℕ) :
    smallPrimeJointProbability N K s j ≤ squareDetJointProbability N K s j := by
  let X := Fin N → Fin (N + 1) → Bool
  let Y := Fin (N + 1) → Fin (N + 1) → Bool
  let S : Set X := {B | ∀ i : s, j i ≤ (binaryCokernelIndex B).factorization i.val.val}
  let T : Set Y := {A | ∀ i : s, i.val.val ^ j i ∣ ((Matrix.of A).map zeroOneBit).det.natAbs}
  have hmap : (uniformOn (Set.univ : Set Y)).map (Fin.tail : Y → X) = uniformOn Set.univ := by
    have heq : (fun x : Y => fun i : Fin N => x (Fin.succEmb N i)) = (Fin.tail : Y → X) := rfl
    rw [← heq]
    simpa only [pi_uniformOn_univ] using
      pi_map_restrict_embedding (uniformOn (Set.univ : Set (Fin (N + 1) → Bool))) (Fin.succEmb N)
  have hS : MeasurableSet S := (Set.toFinite _).measurableSet
  have hpro : (uniformOn (Set.univ : Set X)).real S =
      (uniformOn (Set.univ : Set Y)).real ((Fin.tail : Y → X) ⁻¹' S) := by
    rw [← hmap, measureReal_def, Measure.map_apply (measurable_of_finite _) hS, ← measureReal_def]
  unfold smallPrimeJointProbability squareDetJointProbability
  change (uniformOn Set.univ).real S ≤ (uniformOn Set.univ).real T
  rw [hpro]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro A hA i
  let m := binaryCokernelIndex (Fin.tail A)
  let p := i.val.val
  have hp : p.Prime := Nat.prime_of_mem_primesLE i.val.2
  have hdiv : p ^ j i ∣ m := by
    by_cases hm : m = 0
    · rw [hm]
      exact dvd_zero _
    · exact (hp.pow_dvd_iff_le_factorization hm).mpr (hA i)
  exact hdiv.trans (binaryCokernelIndex_tail_dvd_det A)

/-- The small-prime logarithmic moment follows from the joint upper bound
on divisibility of the appended square determinant. -/
theorem smallPrimeLogMoment_of_square_divisibility {K : ℕ} (hK : 1 ≤ K)
    {A E c : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) (hc : 0 < c)
    (htail : ∀ᶠ N : ℕ in atTop, ∀ s : Finset (Nat.primesLE (N ^ K)), s.card ≤ 102 →
      ∀ j : s → Fin (N ^ 3),
        squareDetJointProbability N K s (fun i => (j i : ℕ) + 1) ≤
          A * (∏ i : s, 1 / (i.val.val : ℝ) ^ ((j i : ℕ) + 1)) + E * Real.exp (-c * (N : ℝ))) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      smallPrimeLogMoment N K ≤ C * Real.log (N : ℝ) ^ 102 :=
  smallPrimeLogMoment_of_joint_divisibility hK hA hE hc
    (htail.mono fun N h s hs j => (smallPrimeJointProbability_le_square N K s _).trans (h s hs j))

end BooleanThreshold
