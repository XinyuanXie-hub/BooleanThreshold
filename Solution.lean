module

public import BooleanThreshold.ArrangementSpan
public import BooleanThreshold.CokernelLargeDirect
public import BooleanThreshold.CokernelMaplesPolynomial
public import BooleanThreshold.CokernelPrimes
public import BooleanThreshold.DependenceBounds
public import BooleanThreshold.JSSConditionalEstimate
public import BooleanThreshold.JSSConditionalFinal
public import BooleanThreshold.JSSCorankReduction
public import BooleanThreshold.JSSStructured
public import BooleanThreshold.KKSLargeSupport
public import BooleanThreshold.SpanEndpoint
public import BooleanThreshold.SpanSmallRelations
public import BooleanThreshold.ThresholdBounds

public section

open Filter MeasureTheory Module ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanThreshold

/-- Theorem 1 reduces to the endpoint estimate on spans of random sign vectors. -/
theorem theorem1_of_sign_span_bound
    (span_bound : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Nat.card {v : Fin n → Fin (n + 1) → Bool // ¬ SignSpanGood v} : ℝ) ≤
        (C / (n : ℝ) ^ 99) * ((2 : ℝ) ^ (n + 1)) ^ n) :
    ∃ C > (0 : ℝ), ∀ n ≥ (1 : ℕ),
      let T : ℝ := Nat.card (BooleanThresholdFunction n)
      let main : ℝ := 2 * ((2 ^ n - 1).choose n : ℝ)
      |T - main| ≤ C * main / (n : ℝ) ^ 99 := by
  obtain ⟨B, hB⟩ := span_bound
  obtain ⟨A, _, hA⟩ := polynomial_div_pow_bounded 100 (show (1 : ℝ) < 2 by norm_num)
  refine threshold_asymptotic_of_bounds (fun n _ => threshold_count_le_binomial_sum n)
    ⟨B + A, (hB.and (eventually_ge_atTop 1)).mono ?_⟩
  intro n hn
  have hgeom := threshold_count_lower_of_bad_signSpan_card n hn.2 (B / (n : ℝ) ^ 99) hn.1
  change (1 - B / (n : ℝ) ^ 99 - (n : ℝ) / 2 ^ n) * thresholdMainTerm n ≤
    (Nat.card (BooleanThresholdFunction n) : ℝ) at hgeom
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have htail : (n : ℝ) / 2 ^ n ≤ A / (n : ℝ) ^ 99 := by
    apply (le_div_iff₀ (pow_pos hnpos _)).2
    rw [div_mul_eq_mul_div, ← pow_succ']
    exact hA n
  calc
    thresholdMainTerm n - (Nat.card (BooleanThresholdFunction n) : ℝ) ≤
        thresholdMainTerm n - (1 - B / (n : ℝ) ^ 99 - (n : ℝ) / 2 ^ n) * thresholdMainTerm n :=
      sub_le_sub_left hgeom _
    _ = (B / (n : ℝ) ^ 99 + (n : ℝ) / 2 ^ n) * thresholdMainTerm n := by ring
    _ ≤ (B / (n : ℝ) ^ 99 + A / (n : ℝ) ^ 99) * thresholdMainTerm n :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl htail) (thresholdMainTerm_pos hn.2).le
    _ = (B + A) * (thresholdMainTerm n / (n : ℝ) ^ 99) := by ring

/-- A determinant comparison over polynomial moduli suffices for Theorem 1. -/
theorem theorem1_of_polynomial_det_zero_comparisons
    {K : ℕ} (hK : 105 ≤ K)
    (comparison : ∀ᶠ N : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
      q ≤ N ^ (((3 + K) * 102 + K) * 102) → q.primeFactors.card ≤ 102 →
      binaryModularDetZeroComparison (N + 1) q (1 / (N : ℝ) ^ ((3 + K) * 102))) :
    ∃ A > (0 : ℝ), ∀ n ≥ (1 : ℕ),
      let T : ℝ := Nat.card (BooleanThresholdFunction n)
      let main : ℝ := 2 * ((2 ^ n - 1).choose n : ℝ)
      |T - main| ≤ A * main / (n : ℝ) ^ 99 := by
  obtain ⟨η, hη, s₀, hlarge⟩ := kks_large_support_atom_bound
  have hb : 0 < η / 2 := by positivity
  have hmoment := smallPrimeLogMoment_of_polynomial_det_zero_comparisons (by omega) comparison
  have hprimes := polynomial_prime_bound_direct hK
  have hcokernel := cokernel_bound_of_log_moment_and_large_primes hb hmoment hprimes
  exact theorem1_of_sign_span_bound (sign_span_bound_of_cokernel_and_small_relations hb hcokernel
    (small_relation_fraction_poly_of_large_support hη s₀ hlarge))

/-- Theorem 1 (Counting Boolean threshold functions). -/
theorem theorem1 :
    ∃ C > (0 : ℝ), ∀ n ≥ (1 : ℕ),
      let T : ℝ := Nat.card (BooleanThresholdFunction n)
      let main : ℝ := 2 * ((2 ^ n - 1).choose n : ℝ)
      |T - main| ≤ C * main / (n : ℝ) ^ 99 := by
  exact theorem1_of_polynomial_det_zero_comparisons (K := 105) le_rfl
    (eventually_binaryModularDetZeroComparison_succ _ _)

/-- Theorem 7 reduces to the square-matrix estimate of Lemma 13. -/
theorem theorem7_of_large_atom_bound
    (large_atom_bound : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ r : ℕ in atTop,
      (signLaw r r).real {v | largeAtomDependence v} ≤ C * Real.exp (-c * (r : ℝ)) / 2 ^ r) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n r : ℕ, 1 ≤ r → r < n →
      let cube : Set (Fin n → ℝ) := {x | ∀ i, x i = -1 ∨ x i = 1}
      let law := Measure.pi (fun _ : Fin r => uniformOn cube)
      let p := law.real {v | ¬ LinearIndependent ℝ v}
      |p - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n :=
  dependence_asymptotic_of_large_atom_bound large_atom_bound

/-- Theorem 7 follows from the structured-null and the conditional atom
estimates. The same conditional estimate also controls corank two. -/
theorem theorem7_of_uniform_conditional_and_structured_estimates
    (conditional : UniformConditionalAtomEstimate)
    {δ ρ a D : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (ha : 0 ≤ a) (ha' : a < 1 / 2) (hD : 0 ≤ D)
    (structured : ∀ᶠ r : ℕ in atTop, (uniformOn Set.univ).real
      (structuredNullEvent (r + 1) (almostConstantUnitVectors (r + 1) δ ρ)) ≤
        2 * ((r + 1).choose 2 : ℝ) / 2 ^ (r + 1) + D * a ^ (r + 1)) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n r : ℕ, 1 ≤ r → r < n →
      let cube : Set (Fin n → ℝ) := {x | ∀ i, x i = -1 ∨ x i = 1}
      let law := Measure.pi (fun _ : Fin r => uniformOn cube)
      let p := law.real {v | ¬ LinearIndependent ℝ v}
      |p - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  apply theorem7_of_large_atom_bound
  simpa only [largeAtomDependence, isLargeAtomVector, and_assoc] using
    signLaw_squareLargeAtom_asymptotic_of_uniform_conditional conditional hδ hδ' hρ hρ'
      ha ha' hD structured

/-- Theorem 7 follows from the conditional small-ball count for integer
vectors. The almost-constant estimate is unconditional. -/
theorem theorem7_of_conditional_small_ball_count
    (count_bound : ConditionalSmallBallCountEstimate) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n r : ℕ, 1 ≤ r → r < n →
      let cube : Set (Fin n → ℝ) := {x | ∀ i, x i = -1 ∨ x i = 1}
      let law := Measure.pi (fun _ : Fin r => uniformOn cube)
      let p := law.real {v | ¬ LinearIndependent ℝ v}
      |p - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  obtain ⟨δ, hδ, hδ', ρ, hρ, hρ', a, ha, ha', D, hD, hstructured⟩ :=
    almostConstant_null_probability
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstructured
  exact theorem7_of_uniform_conditional_and_structured_estimates
    (uniformConditionalAtomEstimate_of_count count_bound) hδ hδ' hρ hρ'
    ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans ha) ha' hD.le
    (eventually_atTop.mpr ⟨N, fun r hr => hN (r + 1) (by omega)⟩)

/-- Theorem 7 (Linear dependence). -/
theorem theorem7 :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n r : ℕ, 1 ≤ r → r < n →
      let cube : Set (Fin n → ℝ) := {x | ∀ i, x i = -1 ∨ x i = 1}
      let law := Measure.pi (fun _ : Fin r => uniformOn cube)
      let p := law.real {v | ¬ LinearIndependent ℝ v}
      |p - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n :=
  theorem7_of_conditional_small_ball_count
    (conditionalSmallBallCountEstimate_of_slice oppositeBandSliceEstimate)

end BooleanThreshold
