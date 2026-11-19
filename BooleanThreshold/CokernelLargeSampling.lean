module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Finset
open scoped BigOperators

namespace BooleanThreshold

private theorem exp_le_unit_chord (u x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.exp (u * x) ≤ 1 + (Real.exp u - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ u)
    (sub_nonneg.mpr hx₁) hx₀ (show (1 - x) + x = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have hexp : u * x = x * u := mul_comm _ _
  rw [hexp]
  refine h.trans_eq ?_
  ring

private theorem average_exp_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (u v : ℝ) :
    (∑ x, Real.exp (u * f x + v)) / Fintype.card Ω ≤
      Real.exp (v + (Real.exp u - 1) * ((∑ x, f x) / Fintype.card Ω)) := by
  have hc : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ x, Real.exp (u * f x)) ≤
      (Fintype.card Ω : ℝ) + (Real.exp u - 1) * ∑ x, f x := by
    convert sum_le_sum (s := univ)
      (fun x _ => exp_le_unit_chord u (f x) (hf x).1 (hf x).2) using 1
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, mul_sum]
  have h := (div_le_iff₀ hc).mpr
    (show (∑ x, Real.exp (u * f x)) ≤
        (1 + (Real.exp u - 1) * ((∑ x, f x) / Fintype.card Ω)) * Fintype.card Ω by
      convert hsum using 1
      field_simp)
  calc
    _ = Real.exp v * ((∑ x, Real.exp (u * f x)) / Fintype.card Ω) := by
      simp_rw [Real.exp_add, ← sum_mul]
      ring
    _ ≤ Real.exp v * (1 + (Real.exp u - 1) * ((∑ x, f x) / Fintype.card Ω)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.add_one_le_exp _ |>.trans_eq' (add_comm _ _))
        (Real.exp_nonneg _)

private theorem average_exp_trials_eq {Ω : Type*} [Fintype Ω] (L : ℕ) (f : Ω → ℝ) :
    (∑ s : Fin L → Ω, Real.exp (∑ i, f (s i))) / Fintype.card (Fin L → Ω) =
      ((∑ x, Real.exp (f x)) / Fintype.card Ω) ^ L := by
  simp_rw [Real.exp_sum]
  rw [← Fintype.sum_pow (fun x => Real.exp (f x)) L, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, div_pow]

/-- A frequency sample simultaneously distinguishes low and high mean defects.
The logarithm of the number of tested coefficients controls its length. -/
theorem exists_sample_distinguishes_means {U Ω : Type*} [Fintype U] [Fintype Ω] [Nonempty Ω]
    (f : U → Ω → ℝ) (hf : ∀ u x, f u x ∈ Set.Icc (0 : ℝ) 1)
    {L : ℕ} {b : ℝ} (hb : 0 < b)
    (hL : 2 * (Fintype.card U : ℝ) * Real.exp (-(L : ℝ) * b / 2) < 1) :
    ∃ s : Fin L → Ω, ∀ u,
      (((∑ x, f u x) / Fintype.card Ω ≤ b / 4) →
        (∑ i, f u (s i)) ≤ (L : ℝ) * b) ∧
      (((∑ i, f u (s i)) ≤ (L : ℝ) * b) →
        (∑ x, f u x) / Fintype.card Ω < 4 * b) := by
  classical
  let μ (u : U) : ℝ := (∑ x, f u x) / Fintype.card Ω
  let C : ℝ := Fintype.card (Fin L → Ω)
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Fintype.card_pos
  let low (u : U) (s : Fin L → Ω) : ℝ :=
    if μ u ≤ b / 4 then Real.exp (∑ i, (f u (s i) - b)) else 0
  let high (u : U) (s : Fin L → Ω) : ℝ :=
    if 4 * b ≤ μ u then Real.exp (∑ i, (b - f u (s i))) else 0
  have hLowNN (u : U) (s : Fin L → Ω) : 0 ≤ low u s := by
    unfold low
    split <;> positivity
  have hHighNN (u : U) (s : Fin L → Ω) : 0 ≤ high u s := by
    unfold high
    split <;> positivity
  have hμ (u : U) : 0 ≤ μ u :=
    div_nonneg (sum_nonneg (fun x _ => (hf u x).1)) (Nat.cast_nonneg _)
  have hPow : Real.exp (-(L : ℝ) * b / 2) = Real.exp (-b / 2) ^ L := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hLow (u : U) : (∑ s, low u s) / C ≤ Real.exp (-(L : ℝ) * b / 2) := by
    by_cases hu : μ u ≤ b / 4
    · have hf₁ : (∑ x, Real.exp (f u x - b)) / Fintype.card Ω ≤ Real.exp (-b / 2) := by
        have h := average_exp_le (f u) (hf u) 1 (-b)
        simp only [one_mul, ← sub_eq_add_neg] at h
        apply h.trans (Real.exp_le_exp.mpr _)
        have hmul := mul_le_mul_of_nonneg_right
          (show Real.exp 1 - 1 ≤ 2 by linarith [Real.exp_one_lt_three]) (hμ u)
        change -b + (Real.exp 1 - 1) * μ u ≤ _
        linarith
      simp only [low, ite_eq_left hu, C]
      rw [average_exp_trials_eq L (fun x => f u x - b), hPow]
      exact pow_le_pow_left₀ (div_nonneg (sum_nonneg (fun _ _ => Real.exp_nonneg _))
        (Nat.cast_nonneg _)) hf₁ L
    · simp only [low, ite_eq_right hu, sum_const_zero, zero_div]
      exact Real.exp_nonneg _
  have hHigh (u : U) : (∑ s, high u s) / C ≤ Real.exp (-(L : ℝ) * b / 2) := by
    by_cases hu : 4 * b ≤ μ u
    · have hf₁ : (∑ x, Real.exp (b - f u x)) / Fintype.card Ω ≤ Real.exp (-b / 2) := by
        have h := average_exp_le (f u) (hf u) (-1) b
        have hEq (x : Ω) : (-1 : ℝ) * f u x + b = b - f u x := by ring
        simp only [hEq] at h
        apply h.trans (Real.exp_le_exp.mpr _)
        have he : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg]
          exact inv_le_of_inv_le₀ (by norm_num) (by simpa using Real.exp_one_gt_two.le)
        have hmul := mul_le_mul_of_nonneg_right
          (show Real.exp (-1) - 1 ≤ -(1 / 2) by linarith) (hμ u)
        change b + (Real.exp (-1) - 1) * μ u ≤ _
        linarith
      simp only [high, ite_eq_left hu, C]
      rw [average_exp_trials_eq L (fun x => b - f u x), hPow]
      exact pow_le_pow_left₀ (div_nonneg (sum_nonneg (fun _ _ => Real.exp_nonneg _))
        (Nat.cast_nonneg _)) hf₁ L
    · simp only [high, ite_eq_right hu, sum_const_zero, zero_div]
      exact Real.exp_nonneg _
  let W (s : Fin L → Ω) : ℝ := ∑ u, (low u s + high u s)
  have hW : (∑ s, W s) / C < 1 := by
    calc
      _ = ∑ u, ((∑ s, low u s) / C + (∑ s, high u s) / C) := by
        simp only [W, ← sum_add_distrib, ← add_div, ← Finset.sum_div]
        exact congrArg (fun z : ℝ => z / C) Finset.sum_comm
      _ ≤ ∑ _ : U, 2 * Real.exp (-(L : ℝ) * b / 2) := by
        refine sum_le_sum fun u _ => ?_
        linarith [hLow u, hHigh u]
      _ < 1 := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        convert hL using 1
        ring
  obtain ⟨s, hs⟩ : ∃ s, W s < 1 := by
    by_contra! h
    have hsum := sum_le_sum (s := (univ : Finset (Fin L → Ω))) (fun s _ => h s)
    have hCsum : C ≤ ∑ s, W s := by
      simpa only [C, sum_const, card_univ, nsmul_eq_mul, mul_one] using hsum
    exact (not_lt_of_ge ((le_div_iff₀ hC).mpr (by simpa using hCsum))) hW
  have hsingle (u : U) : low u s + high u s ≤ W s :=
    single_le_sum (fun v _ => add_nonneg (hLowNN v s) (hHighNN v s)) (mem_univ u)
  refine ⟨s, fun u => ⟨?_, ?_⟩⟩
  · intro hu
    change μ u ≤ b / 4 at hu
    have hlt := ((le_add_of_nonneg_right (hHighNN u s)).trans (hsingle u)).trans_lt hs
    simp only [low, ite_eq_left hu, Real.exp_lt_one_iff, sum_sub_distrib, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    linarith
  · intro hu
    by_contra! hμbad
    change 4 * b ≤ μ u at hμbad
    have hlt := ((le_add_of_nonneg_left (hLowNN u s)).trans (hsingle u)).trans_lt hs
    simp only [high, ite_eq_left hμbad, Real.exp_lt_one_iff, sum_sub_distrib, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    linarith

end BooleanThreshold
