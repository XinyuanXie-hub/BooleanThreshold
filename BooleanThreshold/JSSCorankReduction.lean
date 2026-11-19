module

public import BooleanThreshold.JSSCorankConditional
public import BooleanThreshold.NonPairAsymptotic

public section

open Filter MeasureTheory ProbabilityTheory Module
open scoped BigOperators ENNReal NNReal

namespace BooleanThreshold

private theorem exists_unit_sign_null {r : ℕ} (A : Fin r → Fin (r + 1) → Bool) :
    ∃ a : Fin (r + 1) → ℝ, (∑ i, a i ^ 2) = 1 ∧ ∀ j, ∑ i, a i * realSigns (A j) i = 0 := by
  obtain ⟨a, ha, hnull⟩ := exists_nonzero_common_null (fun j => realSigns (A j))
  obtain ⟨t, _, hunit⟩ := exists_unit_smul a ha
  refine ⟨t • a, hunit, fun j => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hnull j, mul_zero]

/-- The square large-atom estimate follows from the structured-null bound
and the uniform conditional atom estimate. -/
theorem signLaw_squareLargeAtom_asymptotic_of_uniform_conditional
    (hCond : UniformConditionalAtomEstimate)
    {δ ρ a D : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (ha : 0 ≤ a) (ha' : a < 1 / 2) (hD : 0 ≤ D)
    (hstructured : ∀ᶠ r : ℕ in atTop, (uniformOn Set.univ).real
      (structuredNullEvent (r + 1) (almostConstantUnitVectors (r + 1) δ ρ)) ≤
        2 * ((r + 1).choose 2 : ℝ) / 2 ^ (r + 1) + D * a ^ (r + 1)) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (signLaw n n).real {v | ∃ b, isLargeAtomVector ((2 / 3 : ℝ≥0∞) ^ n) b ∧
        ∀ j, ∑ k, b k * v k j = 0} ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  classical
  obtain ⟨b, hb, hb', B, hB, hcorank⟩ := square_corank_two_geometric_from_conditional hCond
  obtain ⟨γ, hγ, L, hF⟩ := hCond δ ρ hδ hδ' hρ hρ'
  let d := max a b
  let X := max D B
  have hquarter : (1 / 4 : ℝ) ≤ d := hb.trans (le_max_right _ _)
  have hd : d < 1 / 2 := max_lt ha' hb'
  have hX : 0 ≤ X := hD.trans (le_max_left _ _)
  have hb0 : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hb
  refine signLaw_squareLargeAtom_asymptotic_of_estimates hδ hρ.le hγ hquarter hd hX L ?_ ?_ ?_
  · filter_upwards [hcorank] with r hr
    exact hr.trans (mul_le_mul (le_max_right D B)
      (pow_le_pow_left₀ hb0 (le_max_right a b) _) (by positivity) hX)
  · filter_upwards [hstructured] with r hr
    refine hr.trans (add_le_add (le_refl _) ?_)
    exact mul_le_mul (le_max_left D B)
      (pow_le_pow_left₀ ha (le_max_left a b) _) (by positivity) hX
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hF
    refine eventually_atTop.mpr ⟨N + 1, fun r hr => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    let S := almostConstantUnitVectors (m + 2) δ ρ
    let W := balancedSignWindow (m + 2) γ
    let θ := (L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ (m + 2) * uniformOn Set.univ W
    let F := exceptionalConditionalNormalEvent (m + 1) (m + 2) S W θ
    choose normal hunit horth using fun A : Fin (m + 1) → Fin (m + 2) → Bool =>
      exists_unit_sign_null A
    have hmass : (uniformOn Set.univ).real F ≤ 1 / (4 : ℝ) ^ (m + 2) := by
      exact (hN m (by omega)).trans_eq (by rw [div_pow, one_pow])
    refine ⟨normal, hunit, horth, F, hmass, fun A hA ha' => ?_⟩
    change windowAtom (normal A) W ≤ θ
    by_contra! h
    exact hA ⟨normal A, hunit A, ha', horth A, h⟩

end BooleanThreshold
