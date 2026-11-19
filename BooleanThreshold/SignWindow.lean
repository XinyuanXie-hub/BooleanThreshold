module

public import BooleanThreshold.RankSelection
public import BooleanThreshold.SignMeasure
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Real

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

private theorem signPair_sum (r : ℕ) (i j : Fin r) :
    (∑ x : Fin r → Bool, realSigns x i * realSigns x j) =
      if i = j then (2 : ℝ) ^ r else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    calc
      _ = ∑ _x : Fin r → Bool, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        cases hi : x i <;> norm_num [realSigns, hi]
      _ = _ := by simp
  · simp only [ite_eq_right hij]
    let e : (Fin r → Bool) ≃ (Fin r → Bool) :=
      { toFun := fun x => Function.update x i (!(x i))
        invFun := fun x => Function.update x i (!(x i))
        left_inv := fun x => by simp
        right_inv := fun x => by simp }
    have hi (x : Fin r → Bool) : realSigns (e x) i = -realSigns x i := by
      cases hx : x i <;> norm_num [realSigns, e, hx]
    have hj (x : Fin r → Bool) : realSigns (e x) j = realSigns x j := by
      simp [realSigns, e, Ne.symm hij]
    have he := Fintype.sum_equiv e
      (fun x => realSigns (e x) i * realSigns (e x) j)
      (fun x => realSigns x i * realSigns x j) (fun _ => rfl)
    simp_rw [hi, hj, neg_mul, Finset.sum_neg_distrib] at he
    linarith

private theorem signSum_second_moment (r : ℕ) :
    (∑ x : Fin r → Bool, (∑ i, realSigns x i) ^ 2) = (r : ℝ) * 2 ^ r := by
  classical
  calc
    _ = ∑ x : Fin r → Bool, ∑ i, ∑ j, realSigns x i * realSigns x j := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i : Fin r, ∑ j : Fin r, ∑ x : Fin r → Bool, realSigns x i * realSigns x j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp [signPair_sum]

/-- A window of radius proportional to the dimension contains at least half
the sign cube for all sufficiently large dimensions. -/
theorem balancedWindow_mass_ge_half {γ : ℝ} (hγ : 0 < γ) :
    ∃ N : ℕ, ∀ r ≥ N,
      1 / 2 ≤ (uniformOn Set.univ).real
        {x : Fin r → Bool | |∑ i, realSigns x i| ≤ 2 * γ * (r : ℝ)} := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (1 / (2 * γ ^ 2)))
  refine ⟨N, fun r hr => ?_⟩
  let μ : Measure (Fin r → Bool) := uniformOn Set.univ
  let S (x : Fin r → Bool) : ℝ := ∑ i, realSigns x i
  let c := 2 * γ * (r : ℝ)
  let W : Set (Fin r → Bool) := {x | |S x| ≤ c}
  let bad := Finset.univ.filter (fun x => ¬ |S x| ≤ c)
  change 1 / 2 ≤ μ.real W
  have hrN : max 1 (1 / (2 * γ ^ 2)) ≤ (r : ℝ) := hN.trans (by exact_mod_cast hr)
  have hrpos : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hrN)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsum : (bad.card : ℝ) * c ^ 2 ≤ (r : ℝ) * 2 ^ r := by
    calc
      _ = ∑ x ∈ bad, c ^ 2 := by simp
      _ ≤ ∑ x ∈ bad, S x ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hx' : c ≤ |S x| := (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
        simpa only [sq_abs] using pow_le_pow_left₀ hc.le hx' 2
      _ ≤ ∑ x : Fin r → Bool, S x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ = _ := signSum_second_moment r
  have hcard : Wᶜ.ncard = bad.card := by
    rw [Set.ncard_eq_toFinset_card Wᶜ (Set.toFinite Wᶜ)]
    congr 1
    ext x
    simp [bad, W]
  have hratio : (r : ℝ) / c ^ 2 ≤ 1 / 2 := by
    have hpos : 0 < 2 * γ ^ 2 := by positivity
    have h := (div_le_iff₀ hpos).mp ((le_max_right _ _).trans hrN)
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_right h hrpos.le]
  have hbad : μ.real Wᶜ ≤ 1 / 2 := by
    apply le_trans _ hratio
    have hprob : μ.real Wᶜ = (bad.card : ℝ) / 2 ^ r := by
      change (uniformOn Set.univ).real Wᶜ = _
      rw [uniformOn_univ_real_eq_card, hcard]
      simp
    rw [hprob, div_le_div_iff₀ (by positivity) (sq_pos_of_pos hc)]
    exact hsum
  rw [probReal_compl_eq_one_sub (Set.toFinite W).measurableSet] at hbad
  linarith

open scoped Classical in
/-- A coefficient vector with at most two nonzero coordinates is close to the
constant zero in all but at most two coordinates. -/
theorem almostConstant_of_support_le_two {n : ℕ} {δ tolerance : ℝ}
    (hδ : 2 ≤ δ * (n : ℝ)) (htol : 0 ≤ tolerance) (a : Fin n → ℝ)
    (ha : (Finset.univ.filter fun i => a i ≠ 0).card ≤ 2) :
    ∃ center : ℝ, (1 - δ) * (n : ℝ) ≤
      ((Finset.univ.filter fun i => |a i - center| ≤ tolerance).card : ℝ) := by
  refine ⟨0, ?_⟩
  have hcard : (Finset.univ.filter fun i => a i = 0).card +
      (Finset.univ.filter fun i => a i ≠ 0).card = n := by
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => a i = 0)
  have hzero : (n : ℝ) ≤ ((Finset.univ.filter fun i => a i = 0).card : ℝ) + 2 := by
    exact_mod_cast (show n ≤ (Finset.univ.filter fun i => a i = 0).card + 2 by omega)
  have hincl : (Finset.univ.filter fun i => a i = 0) ⊆
      (Finset.univ.filter fun i => |a i - 0| ≤ tolerance) := by
    intro i hi
    have hz := (Finset.mem_filter.mp hi).2
    simp [hz, htol]
  have hle : ((Finset.univ.filter fun i => a i = 0).card : ℝ) ≤
      ((Finset.univ.filter fun i => |a i - 0| ≤ tolerance).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hincl)
  nlinarith

open scoped Classical in
/-- Unit coefficient vectors with at least `(1 - δ) * n` coordinates within
`ρ / √n` of a single real number. -/
@[expose] def almostConstantUnitVectors (n : ℕ) (δ ρ : ℝ) : Set (Fin n → ℝ) :=
  {a | (∑ i, a i ^ 2) = 1 ∧
    ∃ center : ℝ, (1 - δ) * (n : ℝ) ≤
      ((Finset.univ.filter fun i => |a i - center| ≤ ρ / Real.sqrt (n : ℝ)).card : ℝ)}

theorem exists_unit_smul {n : ℕ} (a : Fin n → ℝ) (ha : a ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ (∑ i, (t • a) i ^ 2) = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  let normSq : ℝ := ∑ i, a i ^ 2
  have hnorm : 0 < normSq := (sq_pos_of_ne_zero hj).trans_le
    (Finset.single_le_sum (f := fun i => a i ^ 2) (fun i _ => sq_nonneg (a i))
      (Finset.mem_univ j))
  have hsqrt := ne_of_gt (Real.sqrt_pos.mpr hnorm)
  let t := (Real.sqrt normSq)⁻¹
  have ht : t ≠ 0 := inv_ne_zero hsqrt
  refine ⟨t, ht, ?_⟩
  calc
    (∑ i, (t • a) i ^ 2) = ∑ i, t ^ 2 * a i ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    _ = t ^ 2 * normSq := by rw [Finset.mul_sum]
    _ = ((Real.sqrt normSq) ^ 2)⁻¹ * (Real.sqrt normSq) ^ 2 := by
      rw [Real.sq_sqrt hnorm.le]
      simp only [t, inv_pow, Real.sq_sqrt hnorm.le]
    _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hsqrt)

theorem exists_unit_common_null {r : ℕ} (rows : Fin r → Fin (r + 1) → ℝ) :
    ∃ a : Fin (r + 1) → ℝ, (∑ i, a i ^ 2) = 1 ∧ ∀ j, ∑ i, a i * rows j i = 0 := by
  obtain ⟨a, ha, horth⟩ := exists_nonzero_common_null rows
  obtain ⟨t, _, hunit⟩ := exists_unit_smul a ha
  refine ⟨t • a, hunit, fun j => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, horth j, mul_zero]

open scoped Classical in
theorem supportTwo_scaled_almostConstant {n : ℕ} {δ ρ : ℝ}
    (hδ : 2 ≤ δ * (n : ℝ)) (hρ : 0 ≤ ρ) (a : Fin n → ℝ)
    (ha : (Finset.univ.filter fun i => a i ≠ 0).card = 2) :
    ∃ t : ℝ, t ≠ 0 ∧ t • a ∈ almostConstantUnitVectors n δ ρ := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨t, ht, hunit⟩ := exists_unit_smul a ha0
  refine ⟨t, ht, hunit, almostConstant_of_support_le_two hδ (div_nonneg hρ (Real.sqrt_nonneg _)) _ ?_⟩
  simpa [Pi.smul_apply, smul_eq_mul, ht] using ha.le

/-- The window of sign rows with nearly equal numbers of positive and negative entries. -/
@[expose] def balancedSignWindow (n : ℕ) (γ : ℝ) : Set (Fin n → Bool) :=
  {x | |∑ i, realSigns x i| ≤ 2 * γ * (n : ℝ)}

end BooleanThreshold
