module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

open Finset AddChar
open scoped BigOperators

namespace BooleanThreshold

/-- Orthogonality of the standard character of a cyclic group. -/
theorem sum_standard_mul_character {P : ℕ} [NeZero P] (a : ZMod P) :
    ∑ t : ZMod P, ZMod.stdAddChar (a * t) = if a = 0 then (P : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar P h)

theorem map_sum_standard {P : ℕ} [NeZero P] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod P) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => simp [hx, map_add_eq_mul, ih]

/-- Fourier inversion at zero for a weighted sum of independent finite choices. -/
theorem weighted_zero_sum_fourier {P n : ℕ} [NeZero P] {Ω : Type*} [Fintype Ω]
    (a : Fin n → ℤ) (choice : Ω → ℤ) (w : Ω → ℂ)
    (hfaithful : ∀ x : Fin n → Ω,
      ((∑ i, a i * choice (x i) : ℤ) : ZMod P) = 0 ↔ ∑ i, a i * choice (x i) = 0) :
    (∑ t : ZMod P, ∏ i, ∑ z, w z * ZMod.stdAddChar (((a i * choice z : ℤ) : ZMod P) * t)) =
      (P : ℂ) * ∑ x : Fin n → Ω, if ∑ i, a i * choice (x i) = 0 then
        ∏ i, w (x i) else 0 := by
  classical
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib, ← map_sum_standard,
    ← Finset.sum_mul, ← Int.cast_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_standard_mul_character, hfaithful]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [mul_comm]

/-- Fourier inversion at an integer target for a weighted sum. -/
theorem weighted_sum_at_fourier {P n : ℕ} [NeZero P] {Ω : Type*} [Fintype Ω]
    (a : Fin n → ℤ) (choice : Ω → ℤ) (w : Ω → ℂ) (s : ℤ)
    (hfaithful : ∀ x : Fin n → Ω,
      ((∑ i, a i * choice (x i) : ℤ) : ZMod P) - (s : ZMod P) = 0 ↔
        ∑ i, a i * choice (x i) = s) :
    (∑ t : ZMod P, ZMod.stdAddChar (-(s : ZMod P) * t) *
      ∏ i, ∑ z, w z * ZMod.stdAddChar (((a i * choice z : ℤ) : ZMod P) * t)) =
      (P : ℂ) * ∑ x : Fin n → Ω, if ∑ i, a i * choice (x i) = s then
        ∏ i, w (x i) else 0 := by
  classical
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib, ← map_sum_standard,
    ← Finset.sum_mul, ← Int.cast_sum, Finset.mul_sum]
  have hphase (t : ZMod P) (x : Fin n → Ω) :
      ZMod.stdAddChar (-(s : ZMod P) * t) *
          ((∏ i, w (x i)) * ZMod.stdAddChar (((∑ i, a i * choice (x i) : ℤ) : ZMod P) * t)) =
        (∏ i, w (x i)) * ZMod.stdAddChar
          ((((∑ i, a i * choice (x i) : ℤ) : ZMod P) - (s : ZMod P)) * t) := by
    rw [mul_left_comm, ← map_add_eq_mul]
    congr 2
    ring
  simp_rw [hphase]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_standard_mul_character, hfaithful]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [mul_comm]

end BooleanThreshold
