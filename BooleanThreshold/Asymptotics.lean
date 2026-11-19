module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

open Filter
open scoped BigOperators Topology

namespace BooleanThreshold

/-- An eventually bounded real sequence is bounded above on all natural indices. -/
theorem uniform_upper_bound_of_eventually {f : ℕ → ℝ} {B : ℝ}
    (h : ∀ᶠ n in atTop, f n ≤ B) : ∃ C > (0 : ℝ), ∀ n, f n ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let small := ∑ n ∈ Finset.range N, |f n|
  refine ⟨max 1 (max B small), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans ((le_max_left B small).trans (le_max_right _ _))
  · have hsum : |f n| ≤ small :=
      Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (le_abs_self (f n)).trans (hsum.trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- A polynomial divided by a geometric sequence with base greater than one is bounded. -/
theorem polynomial_div_pow_bounded (k : ℕ) {b : ℝ} (hb : 1 < b) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (n : ℝ) ^ k / b ^ n ≤ C :=
  uniform_upper_bound_of_eventually
    ((tendsto_pow_const_div_const_pow_of_one_lt k hb).eventually_le_const
      (show (0 : ℝ) < 1 from zero_lt_one))

/-- Any positive exponential decay is bounded by a constant times an inverse power. -/
theorem exp_neg_nat_mul_le_inv_pow (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C > (0 : ℝ), ∀ n ≥ (1 : ℕ), Real.exp (-c * (n : ℝ)) ≤ C / (n : ℝ) ^ k := by
  obtain ⟨C, hC, hpow⟩ := polynomial_div_pow_bounded k (Real.one_lt_exp_iff.mpr hc)
  refine ⟨C, hC, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ (pow_pos hnpos _)).2
  rw [neg_mul, Real.exp_neg, mul_comm c, Real.exp_nat_mul, inv_mul_eq_div]
  exact hpow n

/-- A fixed subtraction in the index changes an inverse power by at most a
factor of `2^k` once the index is at least twice the shift. -/
theorem inv_pow_nat_sub_le {n d : ℕ} (hn : 0 < n) (hd : 2 * d ≤ n) (k : ℕ) :
    1 / ((n - d : ℕ) : ℝ) ^ k ≤ (2 : ℝ) ^ k / (n : ℝ) ^ k := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 < ((n - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - d by omega)
  apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hnpos _)).2
  rw [one_mul, ← mul_pow]
  exact pow_le_pow_left₀ hnpos.le (by exact_mod_cast (show n ≤ 2 * (n - d) by omega)) _

/-- An eventual relative bound can be extended to all positive natural indices. -/
theorem relative_bound_of_eventually {f g : ℕ → ℝ} (hg : ∀ n ≥ 1, 0 < g n)
    (h : ∃ B : ℝ, ∀ᶠ n in atTop, f n ≤ B * g n) :
    ∃ C > (0 : ℝ), ∀ n ≥ 1, f n ≤ C * g n := by
  obtain ⟨B, hB⟩ := h
  have hr : ∀ᶠ n in atTop, f n / g n ≤ B :=
    (hB.and (eventually_ge_atTop 1)).mono fun n hn => (div_le_iff₀ (hg n hn.2)).mpr hn.1
  obtain ⟨C, hC, hbound⟩ := uniform_upper_bound_of_eventually hr
  exact ⟨C, hC, fun n hn => (div_le_iff₀ (hg n hn)).mp (hbound n)⟩

/-- A polynomial times a geometric sequence with base less than one half
has an exponential gain over the rate `2⁻ⁿ`. -/
theorem polynomial_mul_pow_exponential_gain (k : ℕ) {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ,
      (n : ℝ) ^ k * a ^ n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  let ρ := (1 + 2 * a) / 2
  have hρpos : 0 < ρ := by dsimp [ρ]; linarith
  have hρlt : ρ < 1 := by dsimp [ρ]; linarith
  let b := ρ / (2 * a)
  have hbpos : 0 < 2 * a := by positivity
  have hb : 1 < b := by
    dsimp [b]
    apply (lt_div_iff₀ hbpos).2
    dsimp [ρ]
    linarith
  obtain ⟨C, hC, hbound⟩ := polynomial_div_pow_bounded k hb
  refine ⟨-Real.log ρ, neg_pos.mpr (Real.log_neg hρpos hρlt), C, hC, fun n => ?_⟩
  have hExp : Real.exp (-(-Real.log ρ) * (n : ℝ)) = ρ ^ n := by
    rw [neg_neg, mul_comm (Real.log ρ), Real.exp_nat_mul, Real.exp_log hρpos]
  have hba : b * a = ρ / 2 := by
    dsimp [b]
    field_simp [ha.ne']
  have hpow : b ^ n * a ^ n = ρ ^ n / 2 ^ n := by
    rw [← mul_pow, hba, div_pow]
  rw [hExp, mul_div_assoc, ← hpow]
  calc
    (n : ℝ) ^ k * a ^ n = ((n : ℝ) ^ k / b ^ n) * (b ^ n * a ^ n) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ (zero_lt_one.trans hb).ne')]
    _ ≤ C * (b ^ n * a ^ n) := by gcongr; exact hbound n

/-- A polynomial times `4⁻ⁿ` has an exponential gain over `2⁻ⁿ`. -/
theorem polynomial_div_four_pow_bound (k : ℕ) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ,
      (n : ℝ) ^ k / 4 ^ n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_pow] using
    polynomial_mul_pow_exponential_gain k (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 / 2 by norm_num)

/-- Two gains over `2⁻ⁿ` can be combined by taking the smaller exponential rate. -/
theorem add_exponential_gains {f g : ℕ → ℝ}
    (hf : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      f n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n)
    (hg : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      g n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      f n + g n ≤ C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  obtain ⟨cf, hcf, Cf, hCf, hF⟩ := hf
  obtain ⟨cg, hcg, Cg, hCg, hG⟩ := hg
  let c := min cf cg
  refine ⟨c, lt_min hcf hcg, Cf + Cg, by positivity, (hF.and hG).mono ?_⟩
  intro n h
  calc
    f n + g n ≤ Cf * Real.exp (-cf * (n : ℝ)) / 2 ^ n +
        Cg * Real.exp (-cg * (n : ℝ)) / 2 ^ n := add_le_add h.1 h.2
    _ ≤ Cf * Real.exp (-c * (n : ℝ)) / 2 ^ n +
        Cg * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
      gcongr
      · exact min_le_left _ _
      · exact min_le_right _ _
    _ = (Cf + Cg) * Real.exp (-c * (n : ℝ)) / 2 ^ n := by ring

end BooleanThreshold
