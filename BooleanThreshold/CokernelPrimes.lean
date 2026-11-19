module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.CokernelModulo

public section

open Filter MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- Combining the per-prime rank bound with the estimate beyond the
exponential cutoff bounds all prime divisors above the polynomial cutoff. -/
theorem large_prime_divisor_bound_of_rank_estimates
    {K : ℕ} (hK : 99 ≤ K) {δ c A : ℝ} (hδc : δ < c) (hA : 0 < A)
    (mid : ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → N ^ K < p →
      p ≤ ⌊Real.exp (δ * (N : ℝ))⌋₊ →
      (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool | modularRankDeficient p B} ≤
        A / (p : ℝ) ^ 2 + A * Real.exp (-c * (N : ℝ)))
    (large : ∃ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
        hasLargePrimeDivisor ⌊Real.exp (δ * (N : ℝ))⌋₊ (binaryCokernelIndex B)} ≤ D / (N : ℝ) ^ 99) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
        hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)} ≤ C / (N : ℝ) ^ 99 := by
  obtain ⟨D, hDpos, hD⟩ := large
  obtain ⟨B, hBpos, hB⟩ := exp_neg_nat_mul_le_inv_pow 99 (sub_pos.mpr hδc)
  refine ⟨A + A * B + D, by positivity, ((mid.and hD).and (eventually_ge_atTop 1)).mono ?_⟩
  intro N h
  let Ω := Fin N → Fin (N + 1) → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let upper := ⌊Real.exp (δ * (N : ℝ))⌋₊
  let P : Set Ω := {B | hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)}
  let I : Set Ω := {B | ∃ p : ℕ, p.Prime ∧ N ^ K < p ∧ p ≤ upper ∧ p ∣ binaryCokernelIndex B}
  let L : Set Ω := {B | hasLargePrimeDivisor upper (binaryCokernelIndex B)}
  change μ.real P ≤ (A + A * B + D) / (N : ℝ) ^ 99
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one h.2
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast h.2
  have hP : P ⊆ I ∪ L := by
    rintro x ⟨p, hprime, hgt, hdvd⟩
    by_cases hp : p ≤ upper
    · exact Or.inl ⟨p, hprime, hgt, hp, hdvd⟩
    · exact Or.inr ⟨p, hprime, lt_of_not_ge hp, hdvd⟩
  have hI : μ.real I ≤ A / ((N ^ K : ℕ) : ℝ) + (upper : ℝ) * (A * Real.exp (-c * (N : ℝ))) :=
    intermediate_prime_probability_le (pow_pos hNpos _) hA.le (by positivity) h.1.1
  have hpow : A / ((N ^ K : ℕ) : ℝ) ≤ A / (N : ℝ) ^ 99 := by
    rw [Nat.cast_pow]
    exact div_le_div_of_nonneg_left hA.le (pow_pos (zero_lt_one.trans_le hN) _)
      (pow_le_pow_right₀ hN hK)
  have hExp : (upper : ℝ) * (A * Real.exp (-c * (N : ℝ))) ≤ A * B / (N : ℝ) ^ 99 := by
    calc
      (upper : ℝ) * (A * Real.exp (-c * (N : ℝ))) ≤
          Real.exp (δ * (N : ℝ)) * (A * Real.exp (-c * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
      _ = A * Real.exp (-(c - δ) * (N : ℝ)) := by
        rw [mul_left_comm (Real.exp (δ * (N : ℝ))) A, ← Real.exp_add]
        congr 2
        ring
      _ ≤ A * (B / (N : ℝ) ^ 99) := mul_le_mul_of_nonneg_left (hB N h.2) hA.le
      _ = _ := by ring
  calc
    μ.real P ≤ μ.real (I ∪ L) := measureReal_mono hP
    _ ≤ μ.real I + μ.real L := measureReal_union_le _ _
    _ ≤ (A / (N : ℝ) ^ 99 + A * B / (N : ℝ) ^ 99) + D / (N : ℝ) ^ 99 :=
      add_le_add (hI.trans (add_le_add hpow hExp)) h.1.2
    _ = _ := by ring

end BooleanThreshold
