module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.CokernelLargeExposure
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Filter MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- The exposed prefix leaves about twice the fourth root of the dimension
for the remaining columns. -/
@[expose] noncomputable def binaryInitialLength (N : ℕ) : ℕ :=
  N - ⌈2 * (N : ℝ) ^ (1 / 4 : ℝ)⌉₊

theorem binaryInitialLength_le (N : ℕ) : binaryInitialLength N ≤ N := Nat.sub_le _ _

theorem quarter_root_le_remaining {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 / 4 : ℝ) ≤ ((N - binaryInitialLength N : ℕ) : ℝ) := by
  let t := ⌈2 * (N : ℝ) ^ (1 / 4 : ℝ)⌉₊
  change (N : ℝ) ^ (1 / 4 : ℝ) ≤ ((N - (N - t) : ℕ) : ℝ)
  by_cases ht : t ≤ N
  · rw [Nat.sub_sub_self ht]
    have hnon : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
    exact (show (N : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 4 : ℝ) by linarith).trans
      (Nat.le_ceil _)
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge ht), Nat.sub_zero]
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast hN) (by norm_num)

/-- The chance terms from the early columns decay faster than any fixed inverse power. -/
theorem remaining_binary_columns_pow_le_inv_pow (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ N ≥ (1 : ℕ),
      (1 / 2 : ℝ) ^ (N - binaryInitialLength N) ≤ C / (N : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := polynomial_div_pow_bounded (4 * k) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨C, hC, fun N hN => ?_⟩
  let t := N - binaryInitialLength N
  have hroot : (N : ℝ) ≤ (t : ℝ) ^ 4 := by
    calc
      (N : ℝ) = ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
        norm_num
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (quarter_root_le_remaining hN) _
  apply (le_div_iff₀ (by positivity : 0 < (N : ℝ) ^ k)).2
  calc
    (1 / 2 : ℝ) ^ t * (N : ℝ) ^ k = (N : ℝ) ^ k / 2 ^ t := by
      rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul]
    _ ≤ ((t : ℝ) ^ 4) ^ k / 2 ^ t :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hroot _) (by positivity)
    _ ≤ C := by rw [← pow_mul]; exact hbound t

/-- The large-prime assertion of Lemma 10 follows from the prefix control
estimate of Lemma 11 with concentration threshold `N⁻¹⁰²`. -/
theorem large_prime_bound_of_prefix_control {δ : ℝ} (hδ : 0 < δ)
    (hprefix : ∃ A > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {R : Fin (binaryInitialLength N) → Fin N → Bool |
          ¬ BinaryPrefixControl ⌊Real.exp (δ * (N : ℝ))⌋₊ (1 / (N : ℝ) ^ 102) R} ≤
        A / (N : ℝ) ^ 99) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {B : Fin N → Fin (N + 1) → Bool |
          hasLargePrimeDivisor ⌊Real.exp (δ * (N : ℝ))⌋₊ (binaryCokernelIndex B)} ≤
        C / (N : ℝ) ^ 99 := by
  obtain ⟨A, hA, hprefix⟩ := hprefix
  obtain ⟨D, hD, hD'⟩ := remaining_binary_columns_pow_le_inv_pow 101
  refine ⟨2 * A + 2 * (1 / δ + 1) * (D + 1), by positivity,
    (hprefix.and (eventually_ge_atTop 1)).mono ?_⟩
  intro N hN
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.2
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hN'
  have h := large_prime_probability_le_prefix_failure (by omega : 0 < N)
    (binaryInitialLength_le N) hδ (show 0 ≤ 1 / (N : ℝ) ^ 102 by positivity)
  have hlog : Real.log (N : ℝ) / δ + 1 ≤ (N : ℝ) * (1 / δ + 1) := by
    have hl : Real.log (N : ℝ) ≤ (N : ℝ) := (Real.log_le_sub_one_of_pos hNpos).trans (by linarith)
    rw [mul_add, mul_one, mul_one_div]
    exact add_le_add (div_le_div_of_nonneg_right hl hδ.le) hN'
  have hpow : 1 / (N : ℝ) ^ 102 ≤ 1 / (N : ℝ) ^ 101 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hN' (by decide))
  have hcols : (1 / 2 : ℝ) ^ (N - binaryInitialLength N) + 1 / (N : ℝ) ^ 102 ≤
      (D + 1) / (N : ℝ) ^ 101 := by
    rw [add_div]
    exact add_le_add (hD' N hN.2) hpow
  refine h.trans ?_
  calc
    _ ≤ 2 * (A / (N : ℝ) ^ 99) + (2 * (N : ℝ)) *
        ((N : ℝ) * (1 / δ + 1)) * ((D + 1) / (N : ℝ) ^ 101) := by
      gcongr
      · exact hN.1
      · rw [Nat.cast_add, Nat.cast_one]
        linarith
    _ = _ := by
      have hs : (N : ℝ) ^ 101 = (N : ℝ) ^ 99 * (N : ℝ) ^ 2 := by rw [← pow_add]
      rw [hs]
      field_simp


/-- Simultaneous prefix control above a polynomial cutoff also gives the
large-prime divisor estimate, without a separate intermediate-prime range. -/
theorem polynomial_prime_bound_of_prefix_control {K : ℕ} (hK : 1 ≤ K)
    (hprefix : ∃ A > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {R : Fin (binaryInitialLength N) → Fin N → Bool |
          ¬ BinaryPrefixControl (N ^ K) (1 / (N : ℝ) ^ 102) R} ≤
        A / (N : ℝ) ^ 99) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {B : Fin N → Fin (N + 1) → Bool | hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)} ≤
        C / (N : ℝ) ^ 99 := by
  obtain ⟨A, hA, hprefix⟩ := hprefix
  obtain ⟨D, hD, hD'⟩ := remaining_binary_columns_pow_le_inv_pow 102
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * A + 2 * (1 / Real.log 2 + 1) * (D + 1), by positivity,
    (hprefix.and (eventually_ge_atTop 2)).mono ?_⟩
  intro N hN
  have hNnat : 1 ≤ N := by omega
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNnat
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hN'
  have hcut : 2 ≤ N ^ K := hN.2.trans (by
    simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0 < N) hK))
  have h := large_prime_probability_le_prefix_failure_of_candidate_bound
    (cutoff := N ^ K) (binaryInitialLength_le N) (show 0 ≤ 1 / (N : ℝ) ^ 102 by positivity)
    (fun _ hj => prefixPrimeCandidates_card_le_all (by omega : 0 < N) hj hcut)
  have hlog : (N : ℝ) * Real.log (N : ℝ) / Real.log 2 + 1 ≤
      (N : ℝ) ^ 2 * (1 / Real.log 2 + 1) := by
    have hl : Real.log (N : ℝ) ≤ (N : ℝ) := (Real.log_le_sub_one_of_pos hNpos).trans (by linarith)
    rw [mul_add, mul_one, mul_one_div]
    have hmul := mul_le_mul_of_nonneg_left hl hNpos.le
    rw [← pow_two] at hmul
    exact add_le_add (div_le_div_of_nonneg_right hmul hlog2.le) (one_le_pow₀ hN')
  have hcols : (1 / 2 : ℝ) ^ (N - binaryInitialLength N) + 1 / (N : ℝ) ^ 102 ≤
      (D + 1) / (N : ℝ) ^ 102 := by
    rw [add_div]
    exact add_le_add (hD' N hNnat) le_rfl
  refine h.trans ?_
  calc
    _ ≤ 2 * (A / (N : ℝ) ^ 99) + (2 * (N : ℝ)) *
        ((N : ℝ) ^ 2 * (1 / Real.log 2 + 1)) * ((D + 1) / (N : ℝ) ^ 102) := by
      gcongr
      · exact hN.1
      · rw [Nat.cast_add, Nat.cast_one]
        linarith
    _ = _ := by
      have hs : (N : ℝ) ^ 102 = (N : ℝ) ^ 99 * (N : ℝ) ^ 3 := by rw [← pow_add]
      rw [hs]
      field_simp

end BooleanThreshold
