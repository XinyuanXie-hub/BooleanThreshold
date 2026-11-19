module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.NonPairSquare
public import BooleanThreshold.SignWindow

@[expose] public section

open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter Module

namespace BooleanThreshold

private theorem concentration_base_split :
    (3 / 5 : ℝ≥0∞) = (9 / 10 : ℝ≥0∞) * (2 / 3 : ℝ≥0∞) := by
  have h : (3 / 5 : ℝ≥0) = (9 / 10 : ℝ≥0) * (2 / 3 : ℝ≥0) := by
    apply NNReal.eq
    norm_num
  simpa only [ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_mul, ENNReal.coe_ofNat] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h

private theorem contraction_eventually (L : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, (L : ℝ≥0∞) * (9 / 10 : ℝ≥0∞) ^ n ≤ 1 / 2 := by
  have hbase : (9 / 10 : ℝ≥0∞) < 1 := by
    have h : (9 / 10 : ℝ≥0) < 1 := by
      apply NNReal.coe_lt_coe.mp
      norm_num
    simpa only [ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_lt_one_iff.mpr h
  have hlimit := ENNReal.Tendsto.const_mul (a := (L : ℝ≥0∞))
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase) (Or.inr ENNReal.coe_ne_top)
  apply (by simpa only [mul_zero] using hlimit :
    Tendsto (fun n : ℕ => (L : ℝ≥0∞) * (9 / 10 : ℝ≥0∞) ^ n) atTop (𝓝 0)).eventually_le_const
  exact ENNReal.div_pos one_ne_zero (by simp)

private theorem window_eventually (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ uniformOn Set.univ (balancedSignWindow n γ) := by
  obtain ⟨N, hN⟩ := balancedWindow_mass_ge_half hγ
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  apply (ENNReal.toReal_le_toReal (by simp) (measure_ne_top _ _)).mp
  simpa only [balancedSignWindow, measureReal_def, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat] using hN n hn

private theorem support_two_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ δ * (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / δ : ℝ)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  rw [mul_comm]
  apply (div_le_iff₀ hδ).mp
  exact hN.trans (by exact_mod_cast hn)

/-- Reduction of Lemma 13 to the square corank and structured-vector estimates
and the conditional estimate for a unit normal to the retained rows.
The two square estimates use a common geometric rate strictly below one half. -/
theorem signLaw_squareLargeAtom_asymptotic_of_estimates
    {δ ρ γ a D : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hγ : 0 < γ)
    (ha₀ : 1 / 4 ≤ a) (ha : a < 1 / 2) (hD : 0 ≤ D) (L : ℝ≥0)
    (hcorank : ∀ᶠ r : ℕ in atTop, (uniformOn Set.univ).real
      {v : BooleanSquareMatrix (r + 1) |
        finrank ℝ (Submodule.span ℝ (Set.range (fun i => realSigns (v i)))) < r} ≤
          D * a ^ (r + 1))
    (hstructured : ∀ᶠ r : ℕ in atTop, (uniformOn Set.univ).real
      (structuredNullEvent (r + 1) (almostConstantUnitVectors (r + 1) δ ρ)) ≤
        2 * ((r + 1).choose 2 : ℝ) / 2 ^ (r + 1) + D * a ^ (r + 1))
    (hdichotomy : ∀ᶠ r : ℕ in atTop,
      ∃ normal : (Fin r → Fin (r + 1) → Bool) → Fin (r + 1) → ℝ,
        (∀ A, ∑ k, normal A k ^ 2 = 1) ∧
        (∀ A j, ∑ k, normal A k * realSigns (A j) k = 0) ∧
        ∃ exceptional : Set (Fin r → Fin (r + 1) → Bool),
          (uniformOn Set.univ).real exceptional ≤ 1 / 4 ^ (r + 1) ∧
          ∀ A ∉ exceptional, normal A ∉ almostConstantUnitVectors (r + 1) δ ρ →
            uniformOn Set.univ
              {b | (∑ k, normal A k * realSigns b k = 0) ∧ b ∈ balancedSignWindow (r + 1) γ} ≤
              (L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ (r + 1) *
                uniformOn Set.univ (balancedSignWindow (r + 1) γ)) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (signLaw n n).real {v | ∃ b, isLargeAtomVector ((2 / 3 : ℝ≥0∞) ^ n) b ∧
        ∀ j, ∑ k, b k * v k j = 0} ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  have ha_pos : 0 < a := (by norm_num : (0 : ℝ) < 1 / 4).trans_le ha₀
  obtain ⟨c, hc, C, hC, hgeom⟩ := polynomial_mul_pow_exponential_gain 5 ha_pos ha
  refine ⟨c, hc, (5 * D + 10) * C, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hcorank.and (hstructured.and hdichotomy))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    ((contraction_eventually L).and ((window_eventually γ hγ).and (support_two_eventually δ hδ)))
  apply eventually_atTop.mpr
  refine ⟨max (N₁ + 1) N₂, fun n hn => ?_⟩
  have hn₁ := le_trans (le_max_left _ _) hn
  have hn₂ := le_trans (le_max_right _ _) hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨hcor, hstr, normal, hnormal, horth, exceptional, hexception, hcomparison⟩ :=
    hN₁ r (by omega)
  obtain ⟨hθ, hW, hsize⟩ := hN₂ (r + 1) hn₂
  let cutoff := (2 / 3 : ℝ≥0∞) ^ (r + 1)
  let θ := (L : ℝ≥0∞) * (9 / 10 : ℝ≥0∞) ^ (r + 1)
  have hratio (w : ℝ≥0∞) : (L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ (r + 1) * w = θ * w * cutoff := by
    rw [concentration_base_split, mul_pow]
    simp only [θ, cutoff, mul_left_comm, mul_comm]
  have hnz (A : Fin r → Fin (r + 1) → Bool) : normal A ≠ 0 := by
    intro h
    have ha := hnormal A
    simp [h] at ha
  have hs (x : Fin (r + 1) → ℝ) (hx : (Finset.univ.filter fun k => x k ≠ 0).card = 2) :
      ∃ t : ℝ, t ≠ 0 ∧ t • x ∈ almostConstantUnitVectors (r + 1) δ ρ :=
    supportTwo_scaled_almostConstant hsize hρ x hx
  have hpair := pairCollision_probability_error_le (r + 1) (r + 1) le_rfl
  rw [← squarePair_probability] at hpair
  have hpair' : 2 * ((r + 1).choose 2 : ℝ) / 2 ^ (r + 1) -
      2 * ((r + 1 : ℕ) : ℝ) ^ 4 / 4 ^ (r + 1) ≤
      (uniformOn Set.univ).real (squarePairEvent (r + 1)) := by
    have hp := (abs_sub_le_iff.mp hpair).2
    linarith only [hp]
  have h := squareLargeAtom_probability_le_of_concentration cutoff normal hnz horth
    (almostConstantUnitVectors (r + 1) δ ρ) hs exceptional (balancedSignWindow (r + 1) γ)
    hθ hW (fun A hE hS => (hcomparison A hE hS).trans_eq (hratio _))
    hcor hexception hstr hpair'
  have hpow : 1 / (4 : ℝ) ^ (r + 1) ≤ a ^ (r + 1) := by
    rw [← one_pow (r + 1), ← div_pow]
    exact pow_le_pow_left₀ (by norm_num) ha₀ _
  have hx : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
  have hx5 : (((r + 1 : ℕ) : ℝ)) ≤ ((r + 1 : ℕ) : ℝ) ^ 5 := by
    conv_lhs => rw [← pow_one (((r + 1 : ℕ) : ℝ))]
    exact pow_le_pow_right₀ hx (by norm_num)
  have h15 := hx.trans hx5
  have hb : 0 ≤ a ^ (r + 1) := by positivity
  have hmul₁ := mul_le_mul_of_nonneg_left h15 (mul_nonneg hD hb)
  have hmul₂ := mul_le_mul_of_nonneg_left hx5 hb
  have hmul₃ := mul_le_mul_of_nonneg_left hx5 (mul_nonneg hD hb)
  rw [signLaw_squareLargeAtom_probability]
  calc
    _ ≤ D * a ^ (r + 1) + (r + 1 : ℝ) * (2 * (1 / 4 ^ (r + 1)) +
          4 * (D * a ^ (r + 1) + 2 * ((r + 1 : ℕ) : ℝ) ^ 4 / 4 ^ (r + 1))) := h
    _ ≤ D * a ^ (r + 1) + (r + 1 : ℝ) * (2 * a ^ (r + 1) +
          4 * (D * a ^ (r + 1) + 2 * ((r + 1 : ℕ) : ℝ) ^ 4 * a ^ (r + 1))) := by
      simp only [div_eq_mul_inv, one_mul] at hpow ⊢
      gcongr
    _ ≤ (5 * D + 10) * (((r + 1 : ℕ) : ℝ) ^ 5 * a ^ (r + 1)) := by
      push_cast at hmul₁ hmul₂ hmul₃ ⊢
      nlinarith only [hmul₁, hmul₂, hmul₃]
    _ ≤ _ := by
      have hgeom' := mul_le_mul_of_nonneg_left (hgeom (r + 1)) (show 0 ≤ 5 * D + 10 by positivity)
      simpa only [mul_div_assoc, mul_assoc] using hgeom'

end BooleanThreshold
