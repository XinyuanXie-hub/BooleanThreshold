module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.PairsSmallSupport
public import Mathlib.Data.Nat.Choose.Bounds

public section

open Finset MeasureTheory
open scoped ENNReal BigOperators Classical

namespace BooleanThreshold

/-- Column families that admit a relation involving between three and `s₀` columns. -/
@[expose] def smallSupportNull (n s₀ : ℕ) : Set (Fin n → Fin n → ℝ) :=
  {v | ∃ a : Fin n → ℝ, 3 ≤ (univ.filter fun i => a i ≠ 0).card ∧
    (univ.filter fun i => a i ≠ 0).card ≤ s₀ ∧ ∀ j, ∑ i, a i * v i j = 0}

/-- Union bound for all relations supported on at least three and at most `s₀` columns. -/
theorem signLaw_null_small_support_le (n s₀ : ℕ) :
    signLaw n n (smallSupportNull n s₀) ≤
      ∑ s ∈ Icc 3 (min s₀ n), (n.choose s : ℝ≥0∞) * (n.choose (s - 1) : ℝ≥0∞) *
        (3 / 8 : ℝ≥0∞) ^ (n - (s - 1)) := by
  let E (s : ℕ) : Set (Fin n → Fin n → ℝ) :=
    {v | ∃ a : Fin n → ℝ, (univ.filter fun i => a i ≠ 0).card = s ∧
      ∀ j, ∑ i, a i * v i j = 0}
  have hsubset : smallSupportNull n s₀ ⊆ ⋃ s ∈ Icc 3 (min s₀ n), E s := by
    rintro v ⟨a, ha₃, ha₀, hv⟩
    have han : (univ.filter fun i => a i ≠ 0).card ≤ n := by
      simpa using card_le_univ (univ.filter fun i => a i ≠ 0)
    have hmem : (univ.filter fun i => a i ≠ 0).card ∈ Icc 3 (min s₀ n) :=
      mem_Icc.mpr ⟨ha₃, le_min ha₀ han⟩
    exact Set.mem_iUnion₂.mpr ⟨_, hmem, ⟨a, rfl, hv⟩⟩
  calc
    _ ≤ signLaw n n (⋃ s ∈ Icc 3 (min s₀ n), E s) := measure_mono hsubset
    _ ≤ ∑ s ∈ Icc 3 (min s₀ n), signLaw n n (E s) :=
      measure_biUnion_finset_le _ E
    _ ≤ _ := by
      apply sum_le_sum
      intro s hs
      have h := mem_Icc.mp hs
      exact signLaw_null_vector_support_card_le h.1 <| (Nat.sub_le _ _).trans <|
        h.2.trans (min_le_right _ _)

/-- For fixed support bound, the probability of such a relation gains an exponential
factor over `2⁻ⁿ`. -/
theorem signLaw_small_support_null_exponential (s₀ : ℕ) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n ≥ 1,
      (signLaw n n).real (smallSupportNull n s₀) ≤
        C * Real.exp (-c * (n : ℝ)) / 2 ^ n := by
  let a : ℝ := 3 / 8
  have ha : 0 < a := by norm_num [a]
  have ha₁ : a ≤ 1 := by norm_num [a]
  let B : ℝ := (s₀ + 1) / a ^ s₀
  obtain ⟨c, hc, C, hC, hpoly⟩ :=
    polynomial_mul_pow_exponential_gain (2 * s₀) ha (by norm_num [a])
  refine ⟨c, hc, B * C, by dsimp [B]; positivity, ?_⟩
  intro n hn
  let J := Icc 3 (min s₀ n)
  let summand (s : ℕ) : ℝ≥0∞ := (n.choose s : ℝ≥0∞) * (n.choose (s - 1) : ℝ≥0∞) *
    (3 / 8 : ℝ≥0∞) ^ (n - (s - 1))
  have hsummand (s : ℕ) : summand s ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
      (ENNReal.pow_ne_top (by simp [ENNReal.div_ne_top]))
  have hraw := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun s _ => hsummand s)
    (signLaw_null_small_support_le n s₀)
  have hreal :
      (signLaw n n).real (smallSupportNull n s₀) ≤
        ∑ s ∈ J, (n.choose s : ℝ) * (n.choose (s - 1) : ℝ) * a ^ (n - (s - 1)) := by
    change (signLaw n n (smallSupportNull n s₀)).toReal ≤ _
    rw [show (Icc 3 (min s₀ n)) = J from rfl,
      show (fun s => (n.choose s : ℝ≥0∞) * (n.choose (s - 1) : ℝ≥0∞) *
        (3 / 8 : ℝ≥0∞) ^ (n - (s - 1))) = summand from rfl,
      ENNReal.toReal_sum (fun s _ => hsummand s)] at hraw
    simpa only [summand, a, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat] using hraw
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hterm (s : ℕ) (hs : s ∈ J) :
      (n.choose s : ℝ) * (n.choose (s - 1) : ℝ) * a ^ (n - (s - 1)) ≤
        ((n : ℝ) ^ (2 * s₀) * a ^ n) / a ^ s₀ := by
    have hs₀ : s ≤ s₀ := (mem_Icc.mp hs).2.trans (min_le_left _ _)
    have hsn : s ≤ n := (mem_Icc.mp hs).2.trans (min_le_right _ _)
    have hchoose₁ : (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by
      exact_mod_cast Nat.choose_le_pow n s
    have hchoose₂ : (n.choose (s - 1) : ℝ) ≤ (n : ℝ) ^ (s - 1) := by
      exact_mod_cast Nat.choose_le_pow n (s - 1)
    have hchoose : (n.choose s : ℝ) * (n.choose (s - 1) : ℝ) ≤ (n : ℝ) ^ (2 * s₀) := by
      calc
        _ ≤ (n : ℝ) ^ s * (n : ℝ) ^ (s - 1) :=
          mul_le_mul hchoose₁ hchoose₂ (by positivity) (by positivity)
        _ = (n : ℝ) ^ (s + (s - 1)) := (pow_add ..).symm
        _ ≤ _ := pow_le_pow_right₀ hnR (by omega)
    have hexp : a ^ (n - (s - 1)) ≤ a ^ n / a ^ s₀ := by
      apply (le_div_iff₀ (pow_pos ha _)).mpr
      rw [← pow_add]
      exact pow_le_pow_of_le_one ha.le ha₁ (by omega)
    calc
      _ ≤ (n : ℝ) ^ (2 * s₀) * (a ^ n / a ^ s₀) :=
        mul_le_mul hchoose hexp (by positivity) (by positivity)
      _ = _ := by rw [mul_div_assoc]
  have hcount : J.card ≤ s₀ + 1 := by
    refine (card_le_card (t := range (s₀ + 1)) ?_).trans (by simp)
    intro s hs
    exact mem_range.mpr (Nat.lt_succ_of_le ((mem_Icc.mp hs).2.trans (min_le_left _ _)))
  have hcount' : (J.card : ℝ) ≤ s₀ + 1 := by exact_mod_cast hcount
  calc
    _ ≤ ∑ s ∈ J, (n.choose s : ℝ) * (n.choose (s - 1) : ℝ) * a ^ (n - (s - 1)) := hreal
    _ ≤ ∑ _ ∈ J, ((n : ℝ) ^ (2 * s₀) * a ^ n) / a ^ s₀ := sum_le_sum hterm
    _ = (J.card : ℝ) * (((n : ℝ) ^ (2 * s₀) * a ^ n) / a ^ s₀) := by simp
    _ ≤ (s₀ + 1 : ℝ) * (((n : ℝ) ^ (2 * s₀) * a ^ n) / a ^ s₀) :=
      mul_le_mul_of_nonneg_right hcount' (by positivity)
    _ = B * ((n : ℝ) ^ (2 * s₀) * a ^ n) := by dsimp [B]; ring
    _ ≤ B * (C * Real.exp (-c * (n : ℝ)) / 2 ^ n) :=
      mul_le_mul_of_nonneg_left (hpoly n) (by dsimp [B]; positivity)
    _ = _ := by ring

end BooleanThreshold
