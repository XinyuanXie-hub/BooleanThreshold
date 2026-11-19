module

public import BooleanThreshold.PairsBirthday
public import BooleanThreshold.SignMeasure
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- Two differently indexed vectors agree up to a simultaneous change of sign. -/
def pairCollision {n r : ℕ} (v : Fin r → Fin n → ℝ) : Prop :=
  ∃ i j, i < j ∧ (v i = v j ∨ v i = -v j)

theorem pairCollision_not_linearIndependent {n r : ℕ} {v : Fin r → Fin n → ℝ}
    (h : pairCollision v) : ¬ LinearIndependent ℝ v := by
  rintro hind
  obtain ⟨i, j, hij, heq⟩ := h
  have hj : v j ∈ Submodule.span ℝ (v '' (Set.univ \ {i})) :=
    Submodule.subset_span ⟨j, by simp [hij.ne.symm], rfl⟩
  apply linearIndependent_iff_notMem_span.mp hind i
  rcases heq with heq | heq
  · rw [heq]
    exact hj
  · rw [heq]
    exact Submodule.neg_mem _ hj

private def normalizeRow {n : ℕ} (x : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun i => x 0 ^^ x i.succ

private theorem normalizeRow_not {n : ℕ} (x : Fin (n + 1) → Bool) :
    normalizeRow (fun i => !(x i)) = normalizeRow x := by
  funext i
  exact Bool.not_xor_not _ _

private def splitRow (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun x := (x 0, normalizeRow x)
  invFun p := Fin.cons p.1 (fun i => p.1 ^^ p.2 i)
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [normalizeRow]
  right_inv p := by
    refine Prod.ext (by simp) (funext fun i => ?_)
    simp [normalizeRow]

private theorem normalizeRow_eq_iff {n : ℕ} (x y : Fin (n + 1) → Bool) :
    normalizeRow x = normalizeRow y ↔ x = y ∨ x = fun i => !(y i) := by
  constructor
  · intro heq
    by_cases hfirst : x 0 = y 0
    · exact Or.inl ((splitRow n).injective (Prod.ext hfirst heq))
    · have hflip : x 0 = !(y 0) := by
        cases hx : x 0 <;> cases hy : y 0 <;> simp_all
      exact Or.inr ((splitRow n).injective (Prod.ext hflip
        (heq.trans (normalizeRow_not y).symm)))
  · rintro (rfl | h)
    · rfl
    · rw [h, normalizeRow_not]

private theorem realSigns_not {n : ℕ} (x : Fin n → Bool) :
    realSigns (fun i => !(x i)) = -realSigns x := by
  funext i
  cases hi : x i <;> simp [realSigns, hi]

private theorem realSigns_eq_or_neg_iff {n : ℕ} (x y : Fin (n + 1) → Bool) :
    (realSigns x = realSigns y ∨ realSigns x = -realSigns y) ↔
      normalizeRow x = normalizeRow y := by
  rw [← realSigns_not, (realSigns_injective _).eq_iff, (realSigns_injective _).eq_iff,
    normalizeRow_eq_iff]

private theorem pairCollision_realSigns_iff {n r : ℕ} (x : Fin r → Fin (n + 1) → Bool) :
    pairCollision (fun i => realSigns (x i)) ↔
      ¬ Function.Injective (fun i => normalizeRow (x i)) := by
  rw [Function.not_injective_iff]
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact ⟨i, j, (realSigns_eq_or_neg_iff _ _).mp h, hij.ne⟩
  · rintro ⟨i, j, h, hij⟩
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨i, j, hlt, (realSigns_eq_or_neg_iff _ _).mpr h⟩
    · exact ⟨j, i, hlt, (realSigns_eq_or_neg_iff _ _).mpr h.symm⟩

private def splitMatrix (n r : ℕ) :
    (Fin r → Fin (n + 1) → Bool) ≃ (Fin r → Bool) × (Fin r → Fin n → Bool) :=
  (Equiv.piCongrRight (fun _ : Fin r => splitRow n)).trans
    (Equiv.arrowProdEquivProdArrow (Fin r) (fun _ => Bool) (fun _ => Fin n → Bool))

private theorem pairCollision_card (n r : ℕ) :
    Nat.card {x : Fin r → Fin (n + 1) → Bool // pairCollision (fun i => realSigns (x i))} =
      2 ^ r * Nat.card {x : Fin r → Fin n → Bool // ¬ Function.Injective x} := by
  let e := (splitMatrix n r).subtypeEquiv (q := fun p => ¬ Function.Injective p.2)
    pairCollision_realSigns_iff
  let e' : {p : (Fin r → Bool) × (Fin r → Fin n → Bool) // ¬ Function.Injective p.2} ≃
      (Fin r → Bool) × {x : Fin r → Fin n → Bool // ¬ Function.Injective x} :=
    { toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
      invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans e'), Nat.card_prod, Nat.card_eq_fintype_card (α := Fin r → Bool),
    Fintype.card_pi_const, Fintype.card_bool]

private theorem pairCollision_real_eq_cardFraction (n r : ℕ) :
    (signLaw (n + 1) r).real {v | pairCollision v} =
      (Nat.card {x : Fin r → Fin n → Bool // ¬ Function.Injective x} : ℝ) / ((2 : ℝ) ^ n) ^ r := by
  rw [signLaw_real_apply, uniformOn_univ_real_eq_card]
  change (Nat.card {x : Fin r → Fin (n + 1) → Bool //
      pairCollision (fun i => realSigns (x i))} : ℝ) /
    Fintype.card (Fin r → Fin (n + 1) → Bool) = _
  rw [pairCollision_card]
  simp only [Fintype.card_pi_const, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_succ' (2 : ℝ) n, mul_pow, mul_div_mul_left _ _ (by positivity : (2 : ℝ) ^ r ≠ 0)]

/-- Agreement up to sign has the birthday collision probability with an alphabet of size
`2 ^ n` for vectors with `n + 1` coordinates. -/
theorem pairCollision_probability_succ (n r : ℕ) (hr : r ≤ 2 ^ n) :
    (signLaw (n + 1) r).real {v | pairCollision v} =
      1 - ∏ i ∈ Finset.range r, (1 - (i : ℝ) / (2 : ℝ) ^ n) := by
  rw [pairCollision_real_eq_cardFraction]
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_pi_const, Fintype.card_bool]
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using
    nonInjective_card_div (Fin n → Bool) r (hcard.symm ▸ hr)

theorem pairCollision_main_sub_probability_le (n r : ℕ) (hr : r ≤ n) :
    let p := (signLaw n r).real {v | pairCollision v}
    let main := 2 * (r.choose 2 : ℝ) / 2 ^ n
    0 ≤ main - p ∧ main - p ≤ main ^ 2 / 2 := by
  cases n with
  | zero =>
    have hr0 : r = 0 := by omega
    subst r
    have hEmpty : {v : Fin 0 → Fin 0 → ℝ | pairCollision v} = ∅ := by
      ext v
      simp [pairCollision]
    simp [hEmpty, measureReal_def]
  | succ n =>
    have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by
      rw [Fintype.card_pi_const, Fintype.card_bool]
    have hr' := hr.trans (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := n)))
    have hmain : 2 * (r.choose 2 : ℝ) / 2 ^ (n + 1) = (r.choose 2 : ℝ) / 2 ^ n := by
      rw [pow_succ' (2 : ℝ) n, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    dsimp only
    rw [pairCollision_real_eq_cardFraction, hmain]
    simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using
      nonInjective_card_div_bounds (Fin n → Bool) r (hcard.symm ▸ hr')

/-- The pair contribution differs from its first-order term by at most
`2 * n ^ 4 / 4 ^ n` when the number of columns is at most the dimension. -/
theorem pairCollision_probability_error_le (n r : ℕ) (hr : r ≤ n) :
    |(signLaw n r).real {v | pairCollision v} - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤
      2 * (n : ℝ) ^ 4 / 4 ^ n := by
  obtain ⟨hnonneg, hbound⟩ := pairCollision_main_sub_probability_le n r hr
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  refine hbound.trans ?_
  have hchoose : (r.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (Nat.choose_le_pow r 2).trans (Nat.pow_le_pow_left hr 2)
  have hpow : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  calc
    _ = 2 * (r.choose 2 : ℝ) ^ 2 / 4 ^ n := by
      rw [div_pow, hpow]
      ring
    _ ≤ _ := by
      gcongr
      calc
        _ ≤ ((n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hchoose 2
        _ = _ := by rw [← pow_mul]

theorem pairCollision_probability_error (n r : ℕ) (hr : r < n) :
    |(signLaw n r).real {v | pairCollision v} - 2 * (r.choose 2 : ℝ) / 2 ^ n| ≤
      2 * (n : ℝ) ^ 4 / 4 ^ n :=
  pairCollision_probability_error_le n r hr.le

end BooleanThreshold
