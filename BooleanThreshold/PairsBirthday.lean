module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

open scoped BigOperators

namespace BooleanThreshold

private theorem nonInjective_card (α : Type*) [Fintype α] (r : ℕ) :
    Nat.card {f : Fin r → α // ¬ Function.Injective f} =
      Fintype.card α ^ r - (Fintype.card α).descFactorial r := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_pi_const,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin r) α),
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- The collision probability for a tuple sampled uniformly from a finite alphabet. -/
theorem nonInjective_card_div (α : Type*) [Fintype α] [Nonempty α] (r : ℕ)
    (hr : r ≤ Fintype.card α) :
    (Nat.card {f : Fin r → α // ¬ Function.Injective f} : ℝ) / (Fintype.card α : ℝ) ^ r =
      1 - ∏ i ∈ Finset.range r, (1 - (i : ℝ) / (Fintype.card α : ℝ)) := by
  let q := Fintype.card α
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := α)
  have hsub : q.descFactorial r ≤ q ^ r := by
    rw [Nat.descFactorial_eq_prod_range]
    calc
      _ ≤ ∏ _i ∈ Finset.range r, q := Finset.prod_le_prod fun i _ => Nat.sub_le q i
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  have hprod : (q.descFactorial r : ℝ) / (q : ℝ) ^ r =
      ∏ i ∈ Finset.range r, (1 - (i : ℝ) / (q : ℝ)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    calc
      _ = (∏ i ∈ Finset.range r, (↑(q - i) : ℝ)) / (∏ _i ∈ Finset.range r, (q : ℝ)) := by
        rw [Finset.prod_const, Finset.card_range]
      _ = _ := by
        rw [← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Nat.cast_sub ((Finset.mem_range.mp hi).le.trans hr), sub_div, div_self hq]
  rw [nonInjective_card]
  change ((q ^ r - q.descFactorial r : ℕ) : ℝ) / (q : ℝ) ^ r = _
  rw [Nat.cast_sub hsub, Nat.cast_pow, sub_div, div_self (pow_ne_zero _ hq), hprod]

private theorem collision_expansion {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    0 ≤ (∑ i ∈ s, a i) - (1 - ∏ i ∈ s, (1 - a i)) ∧
      (∑ i ∈ s, a i) - (1 - ∏ i ∈ s, (1 - a i)) ≤ (∑ i ∈ s, a i) ^ 2 / 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hnot ih =>
    have hrest : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨hi, _⟩ := ha i (Finset.mem_insert_self _ _)
    obtain ⟨hlower, hupper⟩ := ih hrest
    have hprod_le : (∏ j ∈ s, (1 - a j)) ≤ 1 :=
      Finset.prod_le_one₀ (fun j hj => sub_nonneg.mpr (hrest j hj).2)
        (fun j hj => sub_le_self _ (hrest j hj).1)
    have hnonneg := mul_nonneg hi (sub_nonneg.mpr hprod_le)
    have hmul := mul_le_mul_of_nonneg_left (sub_nonneg.mp hlower) hi
    simp only [Finset.sum_insert hnot, Finset.prod_insert hnot]
    constructor
    · linarith
    · nlinarith [sq_nonneg (a i)]

/-- The leading term of the birthday collision probability and its quadratic error bound. -/
theorem nonInjective_card_div_bounds (α : Type*) [Fintype α] [Nonempty α] (r : ℕ)
    (hr : r ≤ Fintype.card α) :
    let p := (Nat.card {f : Fin r → α // ¬ Function.Injective f} : ℝ) /
      (Fintype.card α : ℝ) ^ r
    let main := (r.choose 2 : ℝ) / (Fintype.card α : ℝ)
    0 ≤ main - p ∧ main - p ≤ main ^ 2 / 2 := by
  dsimp only
  rw [nonInjective_card_div α r hr]
  have hq : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have ha (i) (hi : i ∈ Finset.range r) :
      (0 : ℝ) ≤ (i : ℝ) / Fintype.card α ∧ (i : ℝ) / Fintype.card α ≤ 1 := by
    refine ⟨by positivity, (div_le_one hq).mpr ?_⟩
    exact_mod_cast (Finset.mem_range.mp hi).le.trans hr
  have hsum :
      (∑ i ∈ Finset.range r, (i : ℝ) / (Fintype.card α : ℝ)) =
        (r.choose 2 : ℝ) / Fintype.card α := by
    rw [← Finset.sum_div, ← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]
  simpa only [hsum] using collision_expansion (Finset.range r)
    (fun i => (i : ℝ) / (Fintype.card α : ℝ)) ha

end BooleanThreshold
