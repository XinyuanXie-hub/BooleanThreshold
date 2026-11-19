module

public import BooleanThreshold.SignMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- The weighted sum of independent signs encoded as Booleans. -/
noncomputable def signSum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, a i * (if x i then 1 else -1)

theorem uniformOn_univ_real_le_weighted_sum {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (s : Set Ω) (f : Ω → ℝ) {c : ℝ} (hc : 0 < c) (hpos : ∀ x, 0 ≤ f x)
    (hlower : ∀ x ∈ s, c ≤ f x) :
    (uniformOn Set.univ).real s ≤ ((∑ x, f x) / Fintype.card Ω) / c := by
  classical
  let T := s.toFinite.toFinset
  have hcard : T.card = s.ncard := Set.ncard_eq_toFinset_card _ s.toFinite |>.symm
  have hsum : (s.ncard : ℝ) * c ≤ ∑ x, f x := by
    calc
      _ = ∑ x ∈ T, c := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ x ∈ T, f x := Finset.sum_le_sum fun x hx =>
        hlower x (by simpa [T] using hx)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hpos x)
  rw [uniformOn_univ_real_eq_card]
  apply (le_div_iff₀ hc).mpr
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- Exponential moment bound for a weighted sum of independent uniform signs. -/
theorem signSum_mgf_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (t : ℝ) :
    (∑ x : ι → Bool, Real.exp (t * signSum a x)) / Fintype.card (ι → Bool) ≤
      Real.exp (t ^ 2 / 2 * ∑ i, a i ^ 2) := by
  classical
  let g (i : ι) (b : Bool) := Real.exp (t * (a i * (if b then 1 else -1)))
  have hsum : (∑ x : ι → Bool, Real.exp (t * signSum a x)) =
      ∏ i, ∑ b : Bool, g i b := by
    simp only [signSum, Finset.mul_sum, Real.exp_sum]
    simpa only [Fintype.piFinset_univ] using
      Finset.sum_prod_piFinset (Finset.univ : Finset Bool) g
  rw [hsum, Fintype.card_pi]
  push_cast
  rw [← Finset.prod_div_distrib]
  have hz (i : ι) : (∑ b : Bool, g i b) / (Fintype.card Bool : ℝ) = Real.cosh (t * a i) := by
    simp [g, Real.cosh_eq]
  simp only [hz]
  calc
    _ ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 2) := Finset.prod_le_prod₀
      (fun i _ => (Real.cosh_pos (t * a i)).le) (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- One-sided tail bound for a weighted sign sum with unit sum of squared weights. -/
theorem signSum_tail_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) {u : ℝ} (hu : 0 ≤ u) :
    (uniformOn Set.univ).real {x : ι → Bool | u ≤ signSum a x} ≤ Real.exp (-u ^ 2 / 2) := by
  have hmin (x : ι → Bool) (hx : x ∈ {x | u ≤ signSum a x}) :
      Real.exp (u ^ 2) ≤ Real.exp (u * signSum a x) := by
    apply Real.exp_monotone
    simpa [pow_two] using mul_le_mul_of_nonneg_left hx hu
  have h := uniformOn_univ_real_le_weighted_sum {x | u ≤ signSum a x}
    (fun x => Real.exp (u * signSum a x)) (Real.exp_pos (u ^ 2))
    (fun _ => Real.exp_nonneg _) hmin
  have hm := signSum_mgf_le a u
  rw [ha, mul_one] at hm
  calc
    _ ≤ _ := h
    _ ≤ Real.exp (u ^ 2 / 2) / Real.exp (u ^ 2) := div_le_div_of_nonneg_right hm (by positivity)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- Two-sided tail bound for a weighted sign sum with sum of squared weights one. -/
theorem signSum_abs_tail_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) {u : ℝ} (hu : 0 ≤ u) :
    (uniformOn Set.univ).real {x : ι → Bool | u ≤ |signSum a x|} ≤ 2 * Real.exp (-u ^ 2 / 2) := by
  let μ : Measure (ι → Bool) := uniformOn Set.univ
  let A : Set (ι → Bool) := {x | u ≤ signSum a x}
  let B : Set (ι → Bool) := {x | u ≤ signSum (-a) x}
  have heq : {x | u ≤ |signSum a x|} = A ∪ B := by
    ext x
    have hneg : signSum (-a) x = -signSum a x := by
      simp only [signSum, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    change (u ≤ |signSum a x|) ↔ (u ≤ signSum a x ∨ u ≤ signSum (-a) x)
    rw [hneg, le_abs]
  have hb : ∑ i, (-a) i ^ 2 = 1 := by simpa using ha
  rw [heq]
  calc
    _ ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ Real.exp (-u ^ 2 / 2) + Real.exp (-u ^ 2 / 2) :=
      add_le_add (signSum_tail_le a ha hu) (signSum_tail_le (-a) hb hu)
    _ = _ := (two_mul _).symm

end BooleanThreshold
