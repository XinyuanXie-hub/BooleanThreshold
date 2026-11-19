module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Function

namespace BooleanThreshold

private theorem sum_indicator_eq_card {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (∑ x, if p x then (1 : ℝ) else 0) = (Nat.card {x // p x} : ℝ) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

private theorem sum_cons {α M : Type*} [Fintype α] [AddCommMonoid M] {k : ℕ}
    (f : (Fin (k + 1) → α) → M) :
    (∑ R : Fin k → α, ∑ x : α, f (Fin.cons x R)) = ∑ v, f v := by
  classical
  let e : (Fin k → α) × α ≃ (Fin (k + 1) → α) :=
    { toFun := fun q => Fin.cons q.2 q.1
      invFun := fun v => (Fin.tail v, v 0)
      left_inv := by intro q; simp
      right_inv := Fin.cons_self_tail }
  calc
    _ = ∑ q, f (e q) := (Fintype.sum_prod_type (fun q => f (e q))).symm
    _ = _ := Fintype.sum_equiv e _ _ fun _ => rfl

/-- A symmetric extension weight gives a factor-two bound for exceptional base families
if every positive weight marks at least half of the coordinates. -/
theorem card_le_twice_card_of_symmetric_weight {α : Type*} [Fintype α] {k : ℕ}
    (weight : (Fin (k + 1) → α) → ℝ) (marked : (Fin (k + 1) → α) → Fin (k + 1) → Prop)
    [∀ v, DecidablePred (marked v)]
    (bad large : (Fin k → α) → Prop) [DecidablePred bad] [DecidablePred large]
    (h_nonneg : ∀ v, 0 ≤ weight v)
    (h_symm : ∀ (e : Equiv.Perm (Fin (k + 1))) v, weight (v ∘ e) = weight v)
    (h_marked : ∀ (e : Equiv.Perm (Fin (k + 1))) v i, marked (v ∘ e) i ↔ marked v (e i))
    (h_majority : ∀ v, 0 < weight v →
      k + 1 ≤ 2 * (Finset.univ.filter (marked v)).card)
    (h_cover : ∀ R, bad R → 1 ≤ ∑ x, weight (Fin.cons x R))
    (h_bound : ∀ R, (∑ x, if marked (Fin.cons x R) 0 then weight (Fin.cons x R) else 0) ≤
      if large R then 1 else 0) :
    (Nat.card {R // bad R} : ℝ) ≤ 2 * (Nat.card {R // large R} : ℝ) := by
  let w (v : Fin (k + 1) → α) (i : Fin (k + 1)) : ℝ :=
    if marked v i then weight v else 0
  have h_exp_eq (i : Fin (k + 1)) : (∑ v, w v i) = ∑ v, w v 0 := by
    classical
    let e := Equiv.swap (0 : Fin (k + 1)) i
    let E : (Fin (k + 1) → α) ≃ (Fin (k + 1) → α) :=
      { toFun := fun v => v ∘ e
        invFun := fun v => v ∘ e.symm
        left_inv := fun v => funext fun j => by simp
        right_inv := fun v => funext fun j => by simp }
    refine Fintype.sum_equiv E _ _ (fun v => ?_)
    change w v i = w (v ∘ e) 0
    simp [w, h_symm, h_marked, e]
  have h_point (v : Fin (k + 1) → α) :
      ((k + 1 : ℕ) : ℝ) * weight v ≤ 2 * ∑ i, w v i := by
    rcases (h_nonneg v).eq_or_lt with h | h
    · simp [w, ← h]
    · have h' := h_majority v h
      have hn : ((k + 1 : ℕ) : ℝ) ≤ 2 * (((Finset.univ.filter (marked v)).card : ℕ) : ℝ) := by
        exact_mod_cast h'
      dsimp only [w]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hn (h_nonneg v)
  have h_point_sum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => h_point v)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at h_point_sum
  simp only [h_exp_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_point_sum
  have h_total : (∑ v, weight v) ≤ 2 * (∑ v, w v 0) := by
    have hpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_left ?_ hpos
    simpa only [mul_left_comm, mul_assoc] using h_point_sum
  calc
    _ = ∑ R, if bad R then 1 else 0 := (sum_indicator_eq_card bad).symm
    _ ≤ ∑ R, ∑ x, weight (Fin.cons x R) := by
      refine Finset.sum_le_sum fun R _ => ?_
      by_cases hb : bad R
      · simpa only [ite_eq_left hb] using h_cover R hb
      · rw [ite_eq_right hb]
        exact Finset.sum_nonneg fun x _ => h_nonneg _
    _ = ∑ v, weight v := sum_cons weight
    _ ≤ 2 * (∑ v, w v 0) := h_total
    _ = 2 * (∑ R, ∑ x, w (Fin.cons x R) 0) := by rw [sum_cons (fun v => w v 0)]
    _ ≤ 2 * (∑ R, if large R then 1 else 0) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R _ => h_bound R) (by positivity)
    _ = _ := by rw [sum_indicator_eq_card]

end BooleanThreshold
