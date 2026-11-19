module

public import BooleanThreshold.DependenceEvents
public import BooleanThreshold.SpanCokernelReduction
public import BooleanThreshold.SpanSmallCoefficients
public import BooleanThreshold.SpanSmallSupport

public section

open Filter Finset MeasureTheory
open scoped ENNReal BigOperators Classical

namespace BooleanThreshold

/-- Relations outside the small-atom and bounded-support classes. -/
@[expose] def largeSupportAtomNull (n s₀ : ℕ) (q : ℝ≥0∞) : Set (Fin n → Fin n → ℝ) :=
  {v | ∃ a : Fin n → ℤ, s₀ < (univ.filter fun i => a i ≠ 0).card ∧
    q < zeroAtom (fun i => a i) ∧ ∀ j, ∑ i, (a i : ℝ) * v i j = 0}

private theorem support_ge_three_of_extra {n : ℕ} {R : Fin n → Fin (n + 1) → Bool}
    {x : Fin (n + 1) → Bool} (hx : IsExtraSign R x) {b : Fin (n + 1) → ℝ}
    (hb₀ : b 0 ≠ 0) (hnull : ∀ j, ∑ i, b i * realSigns ((Fin.cons x R : Fin (n + 1) → Fin (n + 1) → Bool) i) j = 0) :
    3 ≤ (univ.filter fun i => b i ≠ 0).card := by
  let v (i : Fin (n + 1)) := realSigns ((Fin.cons x R : Fin (n + 1) → Fin (n + 1) → Bool) i)
  let support := univ.filter fun i => b i ≠ 0
  have hmem (i : Fin (n + 1)) : i ∈ support ↔ b i ≠ 0 := by simp [support]
  have hzero : (0 : Fin (n + 1)) ∈ support := (hmem 0).mpr hb₀
  have hvecsum : ∑ i ∈ support, b i • v i = 0 := by
    have hsum : ∑ i, b i • v i = 0 := sum_smul_eq_zero_iff.mpr hnull
    rw [← hsum]
    exact sum_subset (subset_univ _) fun i _ hi => by
      have hbi : b i = 0 := not_not.mp fun hn => hi ((hmem i).mpr hn)
      rw [hbi, zero_smul]
  have hsign (i : Fin (n + 1)) : v i 0 = -1 ∨ v i 0 = 1 := realSigns_mem_signCube _ 0
  change 3 ≤ support.card
  by_contra! hlt
  have hpos : 0 < support.card := card_pos.mpr ⟨0, hzero⟩
  rcases (show support.card = 1 ∨ support.card = 2 by omega) with h₁ | h₂
  · obtain ⟨i, hi⟩ := card_eq_one.mp h₁
    have he : i = 0 := by simpa [hi, eq_comm] using hzero
    subst i
    rw [hi, sum_singleton, smul_eq_zero] at hvecsum
    have hz := hvecsum.resolve_left hb₀
    have hh : v 0 0 = 0 := congrFun hz 0
    rcases hsign 0 with hh' | hh' <;> linarith only [hh, hh']
  · have hrem : (support.erase 0).card = 1 := by rw [card_erase_of_mem hzero, h₂]
    obtain ⟨i, hi⟩ := card_eq_one.mp hrem
    have himem : i ∈ support.erase 0 := by simp [hi]
    have hine : i ≠ 0 := (mem_erase.mp himem).1
    have hset : support = {0, i} := by rw [← insert_erase hzero, hi]
    rw [hset, sum_pair hine.symm] at hvecsum
    let t := -b i / b 0
    have hvec : v 0 = t • v i := by
      have hterm : b 0 • v 0 = -(b i • v i) := eq_neg_of_add_eq_zero_left hvecsum
      simpa [t, smul_neg, smul_smul, div_eq_mul_inv, mul_comm] using
        (eq_inv_smul_iff₀ hb₀).mpr hterm
    have hcoord : v 0 0 = t * v i 0 := congrFun hvec 0
    have ht : t = 1 ∨ t = -1 := by
      rcases hsign 0 with h₀ | h₀ <;> rcases hsign i with hᵢ | hᵢ <;>
        rw [h₀, hᵢ] at hcoord <;> first | (left; linarith) | (right; linarith)
    cases i using Fin.cases with
    | zero => exact hine rfl
    | succ i =>
      rcases ht with he | he
      · exact (hx.2 i).1 (by simpa [v, he] using hvec)
      · exact (hx.2 i).2 (by simpa [v, he] using hvec)

private theorem small_relation_cons_mem {n s₀ B : ℕ} {q : ℝ≥0∞}
    {R : Fin n → Fin (n + 1) → Bool}
    {x : Fin (n + 1) → Bool} (hx : IsExtraSign R x)
    {a : Fin (n + 1) → ℤ} (ha₀ : a 0 ≠ 0) (ha : IsPrimitiveSignRelation (Fin.cons x R) a)
    (hsmall : 2 * (univ.filter fun i => B < (a i).natAbs).card ≤ n + 1) :
    (fun i => realSigns ((Fin.cons x R : Fin (n + 1) → Fin (n + 1) → Bool) i)) ∈
      smallSupportNull (n + 1) s₀ ∪
      smallCoefficientsNull (n + 1) ((n + 2) / 2) B q ∪ largeSupportAtomNull (n + 1) s₀ q := by
  let b (i : Fin (n + 1)) : ℝ := a i
  let v (i : Fin (n + 1)) := realSigns ((Fin.cons x R : Fin (n + 1) → Fin (n + 1) → Bool) i)
  have hb₀ : b 0 ≠ 0 := by
    change (a 0 : ℝ) ≠ 0
    exact_mod_cast ha₀
  have hb_ne : b ≠ 0 := fun h => hb₀ (congrFun h 0)
  have hcast (x : Bool) : (signedBit x : ℝ) = if x then 1 else -1 := by
    cases x <;> norm_num [signedBit]
  have hnull (j : Fin (n + 1)) : ∑ i, b i * v i j = 0 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (ha.1 j)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero, v, b, realSigns, hcast, mul_comm]
      using h
  have hsupport : 3 ≤ (univ.filter fun i => b i ≠ 0).card :=
    support_ge_three_of_extra hx hb₀ hnull
  by_cases hs : (univ.filter fun i => b i ≠ 0).card ≤ s₀
  · exact Or.inl (Or.inl ⟨b, hsupport, hs, hnull⟩)
  · by_cases hq : zeroAtom b ≤ q
    · have hpartition : (univ.filter fun i => (a i).natAbs ≤ B).card +
          (univ.filter fun i => B < (a i).natAbs).card = n + 1 := by
        simpa only [not_le, card_univ, Fintype.card_fin] using
          card_filter_add_card_filter_not (s := (univ : Finset (Fin (n + 1))))
            (p := fun i => (a i).natAbs ≤ B)
      exact Or.inl (Or.inr ⟨a, hb_ne, hq, by omega, hnull⟩)
    · have hsupport_eq : (univ.filter fun i => b i ≠ 0) =
          (univ.filter fun i => a i ≠ 0) := by
        ext i
        simp [b]
      rw [hsupport_eq] at hs
      exact Or.inr ⟨a, lt_of_not_ge hs, lt_of_not_ge hq, hnull⟩

/-- Appending a selected witness gives an injection from prefix matrices with a small relation
to square matrices in one of the three concentration classes. -/
theorem small_relation_card_le_square (n s₀ B : ℕ) (q : ℝ≥0∞) :
    Nat.card {R : Fin n → Fin (n + 1) → Bool //
      HasSmallSignRelation B R} ≤
    Nat.card {M : Fin (n + 1) → Fin (n + 1) → Bool //
      (fun i => realSigns (M i)) ∈ smallSupportNull (n + 1) s₀ ∪
        smallCoefficientsNull (n + 1) ((n + 2) / 2) B q ∪ largeSupportAtomNull (n + 1) s₀ q} := by
  let RType := {R : Fin n → Fin (n + 1) → Bool //
    HasSmallSignRelation B R}
  let event := smallSupportNull (n + 1) s₀ ∪
    smallCoefficientsNull (n + 1) ((n + 2) / 2) B q ∪ largeSupportAtomNull (n + 1) s₀ q
  let g : RType → {M : Fin (n + 1) → Fin (n + 1) → Bool //
      (fun i => realSigns (M i)) ∈ event} := fun R => by
    let x := Classical.choose R.prop
    refine ⟨Fin.cons x R.val, ?_⟩
    obtain ⟨hx, a, ha₀, ha, hsmall⟩ := Classical.choose_spec R.prop
    exact small_relation_cons_mem hx ha₀ ha hsmall
  apply Nat.card_le_card_of_injective g
  intro R S h
  apply Subtype.ext
  funext i
  exact congrArg (fun M => M.val i.succ) h

/-- A bound on the fraction of prefixes with a small-coefficient extra relation.
The factor (2^{n+1}) accounts for the encounter probability of a specified square-matrix
extension. -/
theorem small_relation_fraction_le (n s₀ B : ℕ) (q : ℝ≥0∞) :
    (Nat.card {R : Fin n → Fin (n + 1) → Bool //
        HasSmallSignRelation B R} : ℝ) /
      ((2 : ℝ) ^ (n + 1)) ^ n ≤
      (2 : ℝ) ^ (n + 1) * (
        (signLaw (n + 1) (n + 1)).real (smallSupportNull (n + 1) s₀) +
        (signLaw (n + 1) (n + 1)).real (smallCoefficientsNull (n + 1) ((n + 2) / 2) B q) +
        (signLaw (n + 1) (n + 1)).real (largeSupportAtomNull (n + 1) s₀ q)) := by
  let lowSupport := smallSupportNull (n + 1) s₀
  let lowAtom := smallCoefficientsNull (n + 1) ((n + 2) / 2) B q
  let high := largeSupportAtomNull (n + 1) s₀ q
  let event := lowSupport ∪ lowAtom ∪ high
  let eventBool := (fun M : Fin (n + 1) → Fin (n + 1) → Bool =>
    fun i => realSigns (M i)) ⁻¹' event
  let μ := signLaw (n + 1) (n + 1)
  have hcard :
      (Nat.card {R : Fin n → Fin (n + 1) → Bool //
          HasSmallSignRelation B R} : ℝ) ≤
        (eventBool.ncard : ℝ) := by
    exact_mod_cast small_relation_card_le_square n s₀ B q
  have hmass : μ.real event = (eventBool.ncard : ℝ) / ((2 : ℝ) ^ (n + 1)) ^ (n + 1) := by
    rw [signLaw_real_apply, uniformOn_univ_real_eq_card]
    simp only [eventBool, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  have hbound : μ.real event ≤ μ.real lowSupport + μ.real lowAtom + μ.real high := by
    exact (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
  calc
    _ ≤ (eventBool.ncard : ℝ) / ((2 : ℝ) ^ (n + 1)) ^ n :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = (2 : ℝ) ^ (n + 1) * μ.real event := by
      rw [hmass, pow_succ (a := (2 : ℝ) ^ (n + 1))]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

/-- Lemma 6 with its large-support, large-atom estimate as a hypothesis. -/
theorem small_relation_card_exponential_of_large_support {η : ℝ} (hη : 0 < η) (s₀ : ℕ)
    (hlarge : ∀ᶠ N : ℕ in atTop,
      (signLaw N N).real (largeSupportAtomNull N s₀ (ENNReal.ofReal (Real.exp (-η * (N : ℝ))))) ≤
        (1 / 8 : ℝ) ^ N) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (Nat.card {R : Fin n → Fin (n + 1) → Bool //
          HasSmallSignRelation ⌊Real.exp (η / 2 * (↑(n + 1) : ℝ))⌋₊ R} : ℝ) ≤
        C * Real.exp (-c * (n : ℝ)) * ((2 : ℝ) ^ (n + 1)) ^ n := by
  obtain ⟨cS, hcS, C, hC, hsupp⟩ := signLaw_small_support_null_exponential s₀
  obtain ⟨N₁, hsmall⟩ := eventually_atTop.mp (signLaw_small_coords_null_exponential hη)
  obtain ⟨N₂, hlarge⟩ := eventually_atTop.mp hlarge
  let c := min cS (min 1 (Real.log 4))
  have hc₄ : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc : 0 < c := lt_min hcS (lt_min zero_lt_one hc₄)
  refine ⟨c, hc, C + 2, by positivity, eventually_atTop.mpr ⟨max N₁ N₂, fun n hn => ?_⟩⟩
  let N := n + 1
  let B := ⌊Real.exp (η / 2 * (N : ℝ))⌋₊
  let q := ENNReal.ofReal (Real.exp (-η * (N : ℝ)))
  let pS := (signLaw N N).real (smallSupportNull N s₀)
  let pL := (signLaw N N).real (smallCoefficientsNull N ((N + 1) / 2) B q)
  let pH := (signLaw N N).real (largeSupportAtomNull N s₀ q)
  have hpos : 0 < (2 : ℝ) ^ N := by positivity
  have hcomp : ∀ d : ℝ, c ≤ d → Real.exp (-d * (N : ℝ)) ≤ Real.exp (-c * (n : ℝ)) := by
    intro d hd
    apply Real.exp_le_exp.mpr
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.le_succ n
    have hmul : c * (n : ℝ) ≤ d * (N : ℝ) :=
      (mul_le_mul_of_nonneg_left hnN hc.le).trans <|
        mul_le_mul_of_nonneg_right hd (by positivity)
    linarith
  have hS : (2 : ℝ) ^ N * pS ≤ C * Real.exp (-c * (n : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) ^ N * (C * Real.exp (-cS * (N : ℝ)) / 2 ^ N) :=
        mul_le_mul_of_nonneg_left (hsupp N (by dsimp [N]; omega)) hpos.le
      _ = C * Real.exp (-cS * (N : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcomp cS (min_le_left _ _)) hC.le
  have hL : (2 : ℝ) ^ N * pL ≤ Real.exp (-c * (n : ℝ)) := by
    have h₁ : N₁ ≤ N := (le_max_left _ _).trans (hn.trans (Nat.le_succ n))
    exact (hsmall N h₁).trans <| by
      simpa using (hcomp 1 ((min_le_right _ _).trans (min_le_left _ _)))
  have hH : (2 : ℝ) ^ N * pH ≤ Real.exp (-c * (n : ℝ)) := by
    have h₂ : N₂ ≤ N := (le_max_right _ _).trans (hn.trans (Nat.le_succ n))
    calc
      _ ≤ 2 ^ N * (1 / 8 : ℝ) ^ N := mul_le_mul_of_nonneg_left (hlarge N h₂) hpos.le
      _ = (1 / 4 : ℝ) ^ N := by rw [← mul_pow]; norm_num
      _ = Real.exp (-Real.log 4 * (N : ℝ)) := by
        rw [mul_comm (-Real.log 4), Real.exp_nat_mul, Real.exp_neg,
          Real.exp_log (by norm_num : (0 : ℝ) < 4), one_div]
      _ ≤ _ := hcomp (Real.log 4) ((min_le_right _ _).trans (min_le_right _ _))
  apply (div_le_iff₀ (pow_pos hpos n)).mp
  calc
    _ ≤ (2 : ℝ) ^ N * (pS + pL + pH) := small_relation_fraction_le n s₀ B q
    _ = (2 : ℝ) ^ N * pS + (2 : ℝ) ^ N * pL + (2 : ℝ) ^ N * pH := by ring
    _ ≤ (C + 2) * Real.exp (-c * (n : ℝ)) := by linarith only [hS, hL, hH]

/-- The high-atom input to Lemma 6 gives its small-relation estimate at the precision
needed in the threshold counting theorem. -/
theorem small_relation_fraction_poly_of_large_support {η : ℝ} (hη : 0 < η) (s₀ : ℕ)
    (hlarge : ∀ᶠ N : ℕ in atTop,
      (signLaw N N).real (largeSupportAtomNull N s₀ (ENNReal.ofReal (Real.exp (-η * (N : ℝ))))) ≤
        (1 / 8 : ℝ) ^ N) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (Nat.card {R : Fin n → Fin (n + 1) → Bool //
          HasSmallSignRelation ⌊Real.exp (η / 2 * (↑(n + 1) : ℝ))⌋₊ R} : ℝ) /
        ((2 : ℝ) ^ (n + 1)) ^ n ≤ C / (n : ℝ) ^ 99 := by
  obtain ⟨c, hc, C, hC, hbound⟩ := small_relation_card_exponential_of_large_support hη s₀ hlarge
  obtain ⟨A, hA, hdecay⟩ := exp_neg_nat_mul_le_inv_pow 99 hc
  refine ⟨C * A, by positivity, (hbound.and (eventually_ge_atTop 1)).mono ?_⟩
  intro n hn
  calc
    _ ≤ C * Real.exp (-c * (n : ℝ)) := (div_le_iff₀ (by positivity)).mpr hn.1
    _ ≤ C * (A / (n : ℝ) ^ 99) := mul_le_mul_of_nonneg_left (hdecay n hn.2) hC.le
    _ = _ := by ring

end BooleanThreshold
