module

public import BooleanThreshold.ArrangementSandwich
public import BooleanThreshold.Basic
public import BooleanThreshold.SpanReduction
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section

open Finset
open scoped BigOperators

namespace BooleanThreshold

noncomputable section

/-- The reference vertex of the sign cube. -/
def baseVertex (n : ℕ) : Fin n → Bool := fun _ => false

/-- Independent sets of `n` non-base vertices with no other vertex in their lifted span. -/
def arrangementGoodSets (n : ℕ) : Finset (Finset {x : Fin n → Bool // x ≠ baseVertex n}) := by
  classical
  exact univ.filter fun s =>
    s.card = n ∧ LinearIndependent ℝ (fun j : s => liftSignVertex j.val.val) ∧
      ∀ x, liftSignVertex x ∈ Submodule.span ℝ (Set.range (fun j : s => liftSignVertex j.val.val)) →
        ∃ j : s, j.val.val = x

@[simp]
theorem mem_arrangementGoodSets {n : ℕ} {s : Finset {x : Fin n → Bool // x ≠ baseVertex n}} :
    s ∈ arrangementGoodSets n ↔
      s.card = n ∧ LinearIndependent ℝ (fun j : s => liftSignVertex j.val.val) ∧
        ∀ x, liftSignVertex x ∈ Submodule.span ℝ (Set.range (fun j : s => liftSignVertex j.val.val)) →
          ∃ j : s, j.val.val = x := by
  simp [arrangementGoodSets]

private def strictScore {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ ℓ : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ, ∀ x,
    (f x = true → 0 < ℓ (liftSignVertex x)) ∧ (f x = false → ℓ (liftSignVertex x) < 0)

private theorem eval_liftSignVertex {n : ℕ} (ℓ : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → Bool) :
    ℓ (liftSignVertex x) =
      ℓ ((Pi.basisFun ℝ (Fin (n + 1))) 0) +
        ∑ i : Fin n, ℓ ((Pi.basisFun ℝ (Fin (n + 1))) i.succ) * (if x i then 1 else -1) := by
  let b := Pi.basisFun ℝ (Fin (n + 1))
  calc
    ℓ (liftSignVertex x) = (b.constr ℝ fun i => ℓ (b i)) (liftSignVertex x) := by
      rw [b.constr_self]
    _ = _ := by
      rw [Module.Basis.constr_apply_fintype, Fin.sum_univ_succ]
      simp [b, liftSignVertex, realSigns, mul_comm]

private theorem strictScore_of_threshold {n : ℕ} (f : BooleanThresholdFunction n) :
    strictScore f.val := by
  obtain ⟨bias, weights, h⟩ := f.prop
  let score (x : Fin n → Bool) := bias + ∑ i, weights i * (if x i then 1 else -1)
  obtain ⟨ε, hε, hperturb⟩ := exists_positive_preserving_signs score (fun _ => -1)
  let b := Pi.basisFun ℝ (Fin (n + 1))
  let ℓ := b.constr ℝ (Fin.cons (bias - ε) weights)
  have heval (x) : ℓ (liftSignVertex x) = score x - ε := by
    rw [eval_liftSignVertex]
    change ℓ (b 0) + ∑ i : Fin n, ℓ (b i.succ) * _ = _
    simp [ℓ, score]
    ring
  refine ⟨ℓ, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    rw [heval]
    simpa [sub_eq_add_neg] using (hperturb x).1 ((h x).mp hx)
  · intro hx
    rw [heval]
    have hs : score x ≤ 0 := le_of_not_gt fun hs => by
      have ht := (h x).mpr hs
      simp [hx] at ht
    exact sub_neg.mpr (hs.trans_lt hε)

private theorem threshold_of_strictScore {n : ℕ} {f : (Fin n → Bool) → Bool}
    (h : strictScore f) :
    ∃ (bias : ℝ) (weights : Fin n → ℝ), ∀ x,
      f x = true ↔ 0 < bias + ∑ i, weights i * (if x i then 1 else -1) := by
  obtain ⟨ℓ, hℓ⟩ := h
  let b := Pi.basisFun ℝ (Fin (n + 1))
  refine ⟨ℓ (b 0), fun i => ℓ (b i.succ), fun x => ?_⟩
  rw [← eval_liftSignVertex]
  constructor
  · exact (hℓ x).1
  · intro hx
    cases hfx : f x
    · exact (not_lt_of_ge ((hℓ x).2 hfx).le hx).elim
    · rfl

private def complementThreshold {n : ℕ} (f : BooleanThresholdFunction n) :
    BooleanThresholdFunction n := by
  refine ⟨(fun x => !f.val x), threshold_of_strictScore ?_⟩
  obtain ⟨ℓ, hℓ⟩ := strictScore_of_threshold f
  refine ⟨-ℓ, fun x => ⟨?_, ?_⟩⟩
  · simpa using (hℓ x).2
  · simpa using (hℓ x).1

private theorem complementThreshold_involution {n : ℕ} :
    Function.Involutive (@complementThreshold n) := by
  intro f
  apply Subtype.ext
  funext x
  simp [complementThreshold]

private def thresholdSideEquiv (n : ℕ) :
    {f : BooleanThresholdFunction n // f.val (baseVertex n) = true} ≃
      {f : BooleanThresholdFunction n // f.val (baseVertex n) ≠ true} where
  toFun f := ⟨complementThreshold f.val, by
    change (!f.val.val (baseVertex n)) ≠ true
    simp [f.prop]⟩
  invFun f := ⟨complementThreshold f.val, by
    change (!f.val.val (baseVertex n)) = true
    cases hx : f.val.val (baseVertex n)
    · rfl
    · exact (f.prop hx).elim⟩
  left_inv f := Subtype.ext (complementThreshold_involution f.val)
  right_inv f := Subtype.ext (complementThreshold_involution f.val)

private def patternsOfThreshold (n : ℕ)
    (f : {f : BooleanThresholdFunction n // f.val (baseVertex n) = true}) :
    ↥(positivePatterns (baseVertex n) (@liftSignVertex n)) := by
  classical
  refine ⟨univ.filter (fun x : {x : Fin n → Bool // x ≠ baseVertex n} => f.val.val x = true), ?_⟩
  obtain ⟨ℓ, hℓ⟩ := strictScore_of_threshold f.val
  refine mem_positivePatterns.mpr ⟨ℓ, (hℓ _).1 f.prop, fun i => ⟨?_, ?_⟩⟩
  · intro hi
    exact (hℓ _).1 (by simpa using hi)
  · intro hi
    apply (hℓ _).2
    cases hx : f.val.val i
    · rfl
    · exact (hi (by simp [hx])).elim

private def thresholdOfPatterns (n : ℕ)
    (u : ↥(positivePatterns (baseVertex n) (@liftSignVertex n))) :
    {f : BooleanThresholdFunction n // f.val (baseVertex n) = true} := by
  classical
  let f (x : Fin n → Bool) :=
    if h : x = baseVertex n then true else decide (⟨x, h⟩ ∈ u.val)
  refine ⟨⟨f, threshold_of_strictScore ?_⟩, by simp [f]⟩
  obtain ⟨ℓ, hbase, hℓ⟩ := mem_positivePatterns.mp u.prop
  refine ⟨ℓ, fun x => ?_⟩
  by_cases hx : x = baseVertex n
  · subst x
    simp [f, hbase]
  · simpa [f, hx] using hℓ ⟨x, hx⟩

private def thresholdPatternsEquiv (n : ℕ) :
    {f : BooleanThresholdFunction n // f.val (baseVertex n) = true} ≃
      ↥(positivePatterns (baseVertex n) (@liftSignVertex n)) where
  toFun := patternsOfThreshold n
  invFun := thresholdOfPatterns n
  left_inv f := by
    classical
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x = baseVertex n
    · subst x
      simpa [thresholdOfPatterns] using f.prop.symm
    · cases hfx : f.val.val x <;> simp [thresholdOfPatterns, patternsOfThreshold, hx, hfx]
  right_inv u := by
    classical
    apply Subtype.ext
    ext x
    simp [thresholdOfPatterns, patternsOfThreshold, x.prop]

/-- Count threshold functions by strict sign patterns on a designated side of the arrangement. -/
theorem threshold_count_eq_twice_patterns (n : ℕ) :
    Nat.card (BooleanThresholdFunction n) =
      2 * (positivePatterns (baseVertex n) (@liftSignVertex n)).card := by
  classical
  let p (f : BooleanThresholdFunction n) := f.val (baseVertex n) = true
  have hfin : Finite (BooleanThresholdFunction n) := by
    unfold BooleanThresholdFunction
    infer_instance
  have hsum := Nat.card_congr (Equiv.sumCompl p).symm
  rw [Nat.card_sum, ← Nat.card_congr (thresholdSideEquiv n)] at hsum
  rw [hsum, Nat.card_congr (thresholdPatternsEquiv n), Nat.card_eq_fintype_card, Fintype.card_coe]
  omega

/-- The chamber upper bound specialized to the threshold-function count. -/
theorem threshold_count_le_binomial_sum (n : ℕ) :
    Nat.card (BooleanThresholdFunction n) ≤ 2 * ∑ k ∈ Iic n, (2 ^ n - 1).choose k := by
  classical
  have h := card_positivePatterns_le (baseVertex n) (@liftSignVertex n)
    (d := n) (by simp [Module.finrank_fintype_fun_eq_card])
  have hcard : Fintype.card {x : Fin n → Bool // x ≠ baseVertex n} = 2 ^ n - 1 := by
    rw [Fintype.card_subtype_compl (· = baseVertex n), Fintype.card_subtype_eq]
    simp
  rw [hcard] at h
  rw [threshold_count_eq_twice_patterns]
  exact Nat.mul_le_mul_left 2 h

/-- The chamber lower bound from independent vertex sets with closed lifted span. -/
theorem twice_good_sets_le_threshold_count (n : ℕ) :
    2 * (arrangementGoodSets n).card ≤ Nat.card (BooleanThresholdFunction n) := by
  classical
  rw [threshold_count_eq_twice_patterns]
  refine Nat.mul_le_mul_left 2 <| card_le_of_strong_patterns _ _ fun s hs => ?_
  obtain ⟨hcard, hind, hspan⟩ := mem_arrangementGoodSets.mp hs
  refine strong_patterns_of_span (by simp [hcard, Module.finrank_fintype_fun_eq_card]) hind ?_ ?_
  · intro hb
    obtain ⟨j, hj⟩ := hspan _ hb
    exact j.val.prop hj
  · intro i hi
    obtain ⟨j, hj⟩ := hspan _ hi
    have hji : j.val = i := Subtype.ext hj
    rw [← hji]
    exact j.prop

end

end BooleanThreshold
