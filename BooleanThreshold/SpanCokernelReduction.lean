module

public import BooleanThreshold.SpanReduction
public import BooleanThreshold.SpanRelations
public import BooleanThreshold.SpanWeight
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

open scoped Matrix
open Function Set Submodule Matrix

namespace BooleanThreshold

/-- A sign in the span which is neither a listed vector nor its negative. -/
@[expose] def IsExtraSign {ι : Type*} {n : ℕ} (R : ι → Fin n → Bool) (x : Fin n → Bool) : Prop :=
  realSigns x ∈ span ℝ (range (realSigns ∘ R)) ∧
    ∀ j, realSigns x ≠ realSigns (R j) ∧
      realSigns x ≠ -realSigns (R j)

/-- An integer sign relation, primitive in the sense of Bézout's identity. -/
@[expose] def IsPrimitiveSignRelation {ι : Type*} {n : ℕ} [Fintype ι]
    (R : ι → Fin n → Bool) (a : ι → ℤ) : Prop :=
  (∀ j, ∑ i, signedBit (R i j) * a i = 0) ∧ ∃ c : ι → ℤ, a ⬝ᵥ c = 1

@[expose] def largeSignCoefficients {r : ℕ} (cap : ℕ) (a : Fin r → ℤ) : Finset (Fin r) :=
  Finset.univ.filter fun i => cap < (a i).natAbs

/-- An additional sign has a primitive relation with at most half large coefficients. -/
@[expose] def HasSmallSignRelation {n r : ℕ} (cap : ℕ) (R : Fin r → Fin n → Bool) : Prop :=
  ∃ x, IsExtraSign R x ∧ ∃ a, a 0 ≠ 0 ∧ IsPrimitiveSignRelation (Fin.cons x R) a ∧
    2 * (largeSignCoefficients cap a).card ≤ r + 1

/-- Order of the cokernel of the normalized binary interior, zero for infinite cokernel. -/
@[expose] noncomputable def signCokernelIndex {n r : ℕ} (R : Fin (r + 1) → Fin (n + 1) → Bool) : ℕ :=
  (LinearMap.range (normalizedBinaryMatrix (fun i j => R j i)).mulVecLin).toAddSubgroup.index

private theorem signedBit_cast (x : Bool) : (signedBit x : ℝ) = if x then 1 else -1 := by
  cases x <;> norm_num [signedBit]

private theorem signSpan_cons_eq {n r : ℕ} (R : Fin r → Fin n → Bool) (x : Fin n → Bool)
    (hx : realSigns x ∈ span ℝ (range (realSigns ∘ R))) :
    span ℝ (range (realSigns ∘ Fin.cons x R)) = span ℝ (range (realSigns ∘ R)) := by
  have h : realSigns ∘ Fin.cons x R = Fin.cons (realSigns x) (realSigns ∘ R) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [h, Fin.range_cons, span_insert_eq_span hx]

private theorem primitive_cons_iff {n r : ℕ} (R : Fin r → Fin n → Bool)
    (x : Fin n → Bool) (a : Fin (r + 1) → ℤ) :
    IsPrimitiveSignRelation (Fin.cons x R) a ↔
      (∀ j, (∑ i : Fin r, signedBit (R i j) * a i.succ) + a 0 * signedBit (x j) = 0) ∧
        ∃ (c : Fin r → ℤ) (d : ℤ), (Fin.tail a) ⬝ᵥ c + a 0 * d = 1 := by
  constructor
  · rintro ⟨h, c, hc⟩
    refine ⟨fun j => ?_, Fin.tail c, c 0, ?_⟩
    · have hj := h j
      rwa [Fin.sum_univ_succ, Fin.cons_zero, mul_comm _ (a 0), add_comm] at hj
    · rw [dotProduct, Fin.sum_univ_succ] at hc
      simpa only [dotProduct, Fin.tail, add_comm] using hc
  · rintro ⟨h, c, d, hcd⟩
    refine ⟨fun j => ?_, Fin.cons d c, ?_⟩
    · rw [Fin.sum_univ_succ, Fin.cons_zero, mul_comm _ (a 0), add_comm]
      exact h j
    · rw [dotProduct, Fin.sum_univ_succ, Fin.cons_zero]
      simpa only [dotProduct, Fin.tail, Fin.cons_succ, add_comm] using hcd

private theorem IsPrimitiveSignRelation.reindex {ι : Type*} [Fintype ι] {n : ℕ}
    {R : ι → Fin n → Bool} {a : ι → ℤ} (h : IsPrimitiveSignRelation R a) (e : Equiv.Perm ι) :
    IsPrimitiveSignRelation (R ∘ e) (a ∘ e) := by
  obtain ⟨hr, c, hc⟩ := h
  refine ⟨fun j => ?_, c ∘ e, ?_⟩
  · rw [← hr j]
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  · rw [← hc, dotProduct, dotProduct]
    exact Fintype.sum_equiv e _ _ fun _ => rfl

private theorem exists_primitive_extra_relation {n r : ℕ} {R : Fin (r + 1) → Fin (n + 1) → Bool}
    {x : Fin (n + 1) → Bool} (hLI : LinearIndependent ℝ (realSigns ∘ R))
    (hx : IsExtraSign R x) :
    ∃ a : Fin (r + 2) → ℤ, a 0 ≠ 0 ∧ IsPrimitiveSignRelation (Fin.cons x R) a := by
  have hcast (v : Fin (n + 1) → Bool) :
      (fun j => (signedBit (v j) : ℝ)) = realSigns v :=
    funext fun j => signedBit_cast (v j)
  have hcastR : (fun i j => (signedBit (R i j) : ℝ)) = realSigns ∘ R :=
    funext fun i => hcast (R i)
  have hLI' : LinearIndependent ℝ (fun i j => (signedBit (R i j) : ℝ)) := hcastR ▸ hLI
  have hx' : (fun j => (signedBit (x j) : ℝ)) ∈
      span ℝ (range (fun i j => (signedBit (R i j) : ℝ))) := by
    rw [hcast, hcastR]
    exact hx.1
  obtain ⟨a, b, hb, hr⟩ := exists_primitive_sign_relation_of_mem_span
    (fun i j => R j i) x hLI' hx'
  refine ⟨Fin.cons b a, hb, (primitive_cons_iff _ _ _).2 ?_⟩
  exact hr

private theorem extra_mem_span_of_large_relation {n r : ℕ} {R : Fin r → Fin n → Bool}
    {x : Fin n → Bool} {a : Fin (r + 1) → ℤ}
    (h : IsPrimitiveSignRelation (Fin.cons x R) a) (ha : a 0 ≠ 0) :
    realSigns x ∈ span ℝ (range (realSigns ∘ R)) := by
  have hsum :
      (∑ i : Fin r, (a i.succ : ℝ) • realSigns (R i)) +
        (a 0 : ℝ) • realSigns x = 0 := by
    funext j
    have hj := congrArg (fun z : ℤ => (z : ℝ)) ((primitive_cons_iff _ _ _).1 h |>.1 j)
    simp only [Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_zero, signedBit_cast] at hj
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      realSigns, mul_comm (a _ : ℝ)] using hj
  let s := span ℝ (range (realSigns ∘ R))
  have hm : (∑ i : Fin r, (a i.succ : ℝ) • realSigns (R i)) ∈ s :=
    sum_mem fun i _ => smul_mem _ _ (subset_span (mem_range_self i))
  have hsmul : (a 0 : ℝ) • realSigns x ∈ s := by
    rw [eq_neg_of_add_eq_zero_right hsum]
    exact neg_mem hm
  have ha' : (a 0 : ℝ) ≠ 0 := by exact_mod_cast ha
  simpa [smul_smul, ha'] using smul_mem s (a 0 : ℝ)⁻¹ hsmul

private theorem signCokernelIndex_zero_or_large {n r cap : ℕ}
    {R : Fin (r + 1) → Fin (n + 1) → Bool} {x : Fin (n + 1) → Bool}
    {a : Fin (r + 2) → ℤ} (h : IsPrimitiveSignRelation (Fin.cons x R) a)
    (ha : cap < (a 0).natAbs) :
    signCokernelIndex R = 0 ∨ cap < signCokernelIndex R := by
  by_cases h0 : signCokernelIndex R = 0
  · exact Or.inl h0
  · have hr := (primitive_cons_iff _ _ _).1 h
    have hdvd : a 0 ∣ (signCokernelIndex R : ℤ) :=
      dvd_index_of_primitive_sign_relation (fun i j => R j i) (Fin.tail a) (a 0) x hr.1 hr.2
    have hdvd' := Int.natAbs_dvd_natAbs.2 hdvd
    rw [Int.natAbs_natCast] at hdvd'
    exact Or.inr (ha.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd'))

private def pairwiseSigns {ι : Type*} {n : ℕ} (R : ι → Fin n → Bool) : Prop :=
  ∀ i j, i ≠ j → realSigns (R i) ≠ realSigns (R j) ∧
    realSigns (R i) ≠ -realSigns (R j)

private theorem pairwiseSigns_of_linearIndependent {ι : Type*} {n : ℕ}
    {R : ι → Fin n → Bool} (h : LinearIndependent ℝ (realSigns ∘ R)) :
    pairwiseSigns R := by
  intro i j hij
  have hm : realSigns (R j) ∈ span ℝ ((realSigns ∘ R) '' {j}) :=
    subset_span ⟨j, rfl, rfl⟩
  have hnot : realSigns (R i) ∉ span ℝ ((realSigns ∘ R) '' {j}) :=
    h.notMem_span_image (fun h' => hij h')
  exact ⟨fun he => hnot (he ▸ hm), fun he => hnot (he ▸ neg_mem hm)⟩

private theorem pairwiseSigns_cons_of_extra {n r : ℕ} {R : Fin r → Fin n → Bool}
    {x : Fin n → Bool} (hR : pairwiseSigns R) (hx : IsExtraSign R x) :
    pairwiseSigns (Fin.cons x R) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · exact fun h => (h rfl).elim
  · exact fun _ => hx.2 j
  · intro _
    refine ⟨fun h => (hx.2 i).1 h.symm, fun h => (hx.2 i).2 ?_⟩
    simpa using (congrArg Neg.neg h).symm
  · intro h
    exact hR i j (fun he => h (congrArg Fin.succ he))


private def signedPartner {n : ℕ} (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  if b then x else fun j => !(x j)

private theorem realSigns_signedPartner {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    realSigns (signedPartner b x) = if b then realSigns x else -realSigns x := by
  cases b
  · funext j
    cases h : x j <;> norm_num [signedPartner, realSigns, h]
  · rfl

private theorem no_sign_is_own_negative {n : ℕ} (x : Fin (n + 1) → Bool) :
    realSigns x ≠ -realSigns x := by
  intro he
  have h := congrFun he 0
  cases h0 : x 0 <;> norm_num [realSigns, h0] at h

private noncomputable def signVerticesInSpan {ι : Type*} {n : ℕ} (R : ι → Fin n → Bool) :
    Finset (Fin n → Bool) :=
  open Classical in
  Finset.univ.filter (fun x => realSigns x ∈ span ℝ (range (realSigns ∘ R)))

private noncomputable def extraSigns {ι : Type*} {n : ℕ} (R : ι → Fin n → Bool) :
    Finset (Fin n → Bool) :=
  open Classical in
  Finset.univ.filter (IsExtraSign R)

@[simp] private theorem mem_extraSigns {ι : Type*} {n : ℕ} {R : ι → Fin n → Bool}
    {x : Fin n → Bool} : x ∈ extraSigns R ↔ IsExtraSign R x := by
  classical
  simp [extraSigns]

private theorem card_extraSigns_eq {n r : ℕ} (R : Fin r → Fin (n + 1) → Bool)
    (hR : pairwiseSigns R) : (extraSigns R).card = (signVerticesInSpan R).card - 2 * r := by
  classical
  let f (p : Fin r × Bool) := signedPartner p.2 (R p.1)
  let seen := Finset.univ.image f
  have hf : Injective f := by
    rintro ⟨i, b⟩ ⟨j, d⟩ h
    have h' := congrArg (fun x => realSigns x) h
    dsimp only [f] at h'
    simp only [realSigns_signedPartner] at h'
    have he : i = j := by
      by_contra hne
      have hh := hR i j hne
      cases b <;> cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true, neg_inj] at h'
      · exact hh.1 h'
      · exact hh.2 (by simpa using congrArg Neg.neg h')
      · exact hh.2 h'
      · exact hh.1 h'
    subst j
    cases b <;> cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h' <;>
      first | rfl | exact (no_sign_is_own_negative (R i) h').elim |
      exact (no_sign_is_own_negative (R i) h'.symm).elim
  have hc : seen.card = 2 * r := by
    simp only [seen, Finset.card_image_of_injective _ hf, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    exact mul_comm _ _
  have hm (x : Fin (n + 1) → Bool) : x ∈ seen ↔
      ∃ i, realSigns x = realSigns (R i) ∨
        realSigns x = -realSigns (R i) := by
    simp only [seen, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists, f]
    constructor
    · rintro ⟨i, b, rfl⟩
      cases b
      · exact ⟨i, Or.inr (realSigns_signedPartner false _ )⟩
      · exact ⟨i, Or.inl (realSigns_signedPartner true _ )⟩
    · rintro ⟨i, hi | hi⟩
      · exact ⟨i, true, realSigns_injective _ hi.symm⟩
      · refine ⟨i, false, realSigns_injective _ ?_⟩
        exact (realSigns_signedPartner false _).trans hi.symm
  have hsub : seen ⊆ signVerticesInSpan R := by
    intro x hx
    rw [hm] at hx
    obtain ⟨i, hi | hi⟩ := hx
    · simpa [signVerticesInSpan, hi] using
        (subset_span (R := ℝ) (mem_range_self (f := realSigns ∘ R) i))
    · simpa [signVerticesInSpan, hi] using
        (neg_mem (subset_span (R := ℝ) (mem_range_self (f := realSigns ∘ R) i)))
  have he : extraSigns R = signVerticesInSpan R \ seen := by
    ext x
    simp [hm, signVerticesInSpan, IsExtraSign]
  rw [he, Finset.card_sdiff_of_subset hsub, hc]


private def largeCoordinate {n r : ℕ} (cap : ℕ) (M : Fin (r + 1) → Fin n → Bool)
    (i : Fin (r + 1)) : Prop :=
  ∃ a, IsPrimitiveSignRelation M a ∧ cap < (a i).natAbs

private theorem largeCoordinate_reindex {n r : ℕ} (cap : ℕ)
    (e : Equiv.Perm (Fin (r + 1))) (M : Fin (r + 1) → Fin n → Bool) (i : Fin (r + 1)) :
    largeCoordinate cap (M ∘ e) i ↔ largeCoordinate cap M (e i) := by
  constructor
  · rintro ⟨a, ha, hl⟩
    refine ⟨a ∘ e.symm, ?_, by simpa using hl⟩
    simpa [Function.comp_def] using ha.reindex e.symm
  · rintro ⟨a, ha, hl⟩
    exact ⟨a ∘ e, ha.reindex e, hl⟩

private noncomputable def largeCoordinates {n r : ℕ} (cap : ℕ)
    (M : Fin (r + 1) → Fin n → Bool) : Finset (Fin (r + 1)) :=
  open Classical in
  Finset.univ.filter (largeCoordinate cap M)

@[simp] private theorem mem_largeCoordinates {n r cap : ℕ} {M : Fin (r + 1) → Fin n → Bool}
    {i : Fin (r + 1)} : i ∈ largeCoordinates cap M ↔ largeCoordinate cap M i := by
  classical
  simp [largeCoordinates]

private def spanWeightEligible {n r : ℕ} (cap : ℕ) (M : Fin (r + 2) → Fin n → Bool) : Prop :=
  open Classical in
  pairwiseSigns M ∧
    r + 2 ≤ 2 * (largeCoordinates cap M).card

private noncomputable def signSpanWeight {n r : ℕ} (cap : ℕ)
    (M : Fin (r + 2) → Fin n → Bool) : ℝ :=
  open Classical in
  if spanWeightEligible cap M then 1 / ((signVerticesInSpan M).card - 2 * (r + 1) : ℕ) else 0

private theorem signSpanWeight_nonneg {n r cap : ℕ} (M : Fin (r + 2) → Fin n → Bool) :
    0 ≤ signSpanWeight cap M := by
  unfold signSpanWeight
  split <;> positivity

private theorem signSpanWeight_reindex {n r cap : ℕ} (e : Equiv.Perm (Fin (r + 2)))
    (M : Fin (r + 2) → Fin n → Bool) :
    signSpanWeight cap (M ∘ e) = signSpanWeight cap M := by
  classical
  have hrange : range (realSigns ∘ (M ∘ e)) = range (realSigns ∘ M) := by
    change range ((realSigns ∘ M) ∘ e) = _
    rw [range_comp, e.surjective.range_eq, image_univ]
  have hp : pairwiseSigns (M ∘ e) ↔ pairwiseSigns M := by
    constructor
    · intro h i j hij
      simpa [Function.comp_def] using h (e.symm i) (e.symm j)
        (fun h' => hij (e.symm.injective h'))
    · intro h i j hij
      exact h (e i) (e j) (fun h' => hij (e.injective h'))
  have hc : (largeCoordinates cap (M ∘ e)).card = (largeCoordinates cap M).card := by
    refine Finset.card_bij (fun i _ => e i) ?_ (fun _ _ _ _ h => e.injective h) ?_
    · intro i hi
      simpa only [mem_largeCoordinates, largeCoordinate_reindex cap e M] using hi
    · intro i hi
      refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
      simpa only [mem_largeCoordinates, largeCoordinate_reindex cap e M, e.apply_symm_apply] using hi
  have he : spanWeightEligible cap (M ∘ e) ↔ spanWeightEligible cap M := by
    simp only [spanWeightEligible, hp, hc]
  have hd : signVerticesInSpan (M ∘ e) = signVerticesInSpan M := by
    ext x
    simp only [signVerticesInSpan, Finset.mem_filter, hrange]
  by_cases h : spanWeightEligible cap M
  · simp only [signSpanWeight, ite_eq_left h, ite_eq_left (he.mpr h), hd]
  · simp only [signSpanWeight, ite_eq_right h, ite_eq_right (fun h' => h (he.mp h'))]

private theorem signSpanWeight_cons_eq_of_eligible {n r cap : ℕ}
    {R : Fin (r + 1) → Fin (n + 1) → Bool} {x : Fin (n + 1) → Bool}
    (hx : realSigns x ∈ span ℝ (range (realSigns ∘ R)))
    (hp : pairwiseSigns R) (he : spanWeightEligible cap (Fin.cons x R)) :
    signSpanWeight cap (Fin.cons x R) = 1 / ((extraSigns R).card : ℝ) := by
  have hs : signVerticesInSpan (Fin.cons x R) = signVerticesInSpan R := by
    ext y
    simp only [signVerticesInSpan, Finset.mem_filter, Finset.mem_univ, true_and, signSpan_cons_eq R x hx]
  rw [signSpanWeight, ite_eq_left he, hs, ← card_extraSigns_eq _ hp]


private theorem signSpanWeight_cover {n r cap : ℕ} (R : Fin (r + 1) → Fin (n + 1) → Bool)
    (hbad : ¬ SignSpanGood R) (hindex : signCokernelIndex R ≠ 0)
    (hsmall : ¬ HasSmallSignRelation cap R) :
    1 ≤ ∑ x : Fin (n + 1) → Bool, signSpanWeight cap (Fin.cons x R) := by
  classical
  have hLI : LinearIndependent ℝ (realSigns ∘ R) := by
    have heq : (fun j i => (signedBit (R j i) : ℝ)) = realSigns ∘ R :=
      funext fun j => funext fun i => signedBit_cast (R j i)
    rw [← heq]
    exact linearIndependent_of_normalized_index_ne_zero (fun i j => R j i) hindex
  have hx : ∃ x, IsExtraSign R x := by
    by_contra hnone
    refine hbad ⟨hLI, fun x hx => ?_⟩
    by_contra he
    exact hnone ⟨x, hx, fun j => ⟨fun hj => he ⟨j, Or.inl hj⟩, fun hj => he ⟨j, Or.inr hj⟩⟩⟩
  obtain ⟨x, hExtra⟩ := hx
  have hpos : 0 < ((extraSigns R).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, mem_extraSigns.mpr hExtra⟩
  have hp := pairwiseSigns_of_linearIndependent hLI
  have hW (y : Fin (n + 1) → Bool) (hy : y ∈ extraSigns R) :
      signSpanWeight cap (Fin.cons y R) = 1 / ((extraSigns R).card : ℝ) := by
    have hy' := mem_extraSigns.mp hy
    refine signSpanWeight_cons_eq_of_eligible hy'.1 hp ⟨pairwiseSigns_cons_of_extra hp hy', ?_⟩
    obtain ⟨a, h0, ha⟩ := exists_primitive_extra_relation hLI hy'
    have hmaj : r + 2 ≤ 2 * (largeSignCoefficients cap a).card := by
      by_contra hm
      exact hsmall ⟨y, hy', a, h0, ha, by omega⟩
    refine hmaj.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact mem_largeCoordinates.mpr ⟨a, ha, hi'⟩
  calc
    1 = ((extraSigns R).card : ℝ) * (1 / ((extraSigns R).card : ℝ)) := by
      field_simp
    _ = ∑ y ∈ extraSigns R, 1 / ((extraSigns R).card : ℝ) := by simp [nsmul_eq_mul]
    _ = ∑ y ∈ extraSigns R, signSpanWeight cap (Fin.cons y R) :=
      Finset.sum_congr rfl (fun y hy => (hW y hy).symm)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => signSpanWeight_nonneg (Fin.cons y R))

private theorem signSpanWeight_marked_bound {n r cap : ℕ}
    (R : Fin (r + 1) → Fin (n + 1) → Bool) :
    open Classical in
    (∑ x : Fin (n + 1) → Bool,
      if largeCoordinate cap (Fin.cons x R) 0 then signSpanWeight cap (Fin.cons x R) else 0) ≤
      if signCokernelIndex R = 0 ∨ cap < signCokernelIndex R then 1 else 0 := by
  classical
  let f (x : Fin (n + 1) → Bool) :=
    if largeCoordinate cap (Fin.cons x R) 0 then signSpanWeight cap (Fin.cons x R) else 0
  have hMarked (x : Fin (n + 1) → Bool) (h : f x ≠ 0) :
      x ∈ extraSigns R ∧ (signCokernelIndex R = 0 ∨ cap < signCokernelIndex R) ∧
        f x = 1 / ((extraSigns R).card : ℝ) := by
    have hm : largeCoordinate cap (Fin.cons x R) 0 := by
      by_contra hm
      exact h (by simp [f, hm])
    have he : spanWeightEligible cap (Fin.cons x R) := by
      by_contra he
      exact h (by simp [f, hm, signSpanWeight, he])
    have hm' := hm
    obtain ⟨a, ha, hlarge⟩ := hm'
    have h0 : a 0 ≠ 0 := by
      intro h'
      simp [h'] at hlarge
    have hx := extra_mem_span_of_large_relation ha h0
    have hp : pairwiseSigns R := fun i j hij =>
      he.1 i.succ j.succ (fun h' => hij (Fin.succ_injective _ h'))
    refine ⟨mem_extraSigns.mpr ⟨hx, fun i => he.1 0 i.succ (Ne.symm (Fin.succ_ne_zero i))⟩,
      signCokernelIndex_zero_or_large ha hlarge, ?_⟩
    simpa only [f, ite_eq_left hm] using signSpanWeight_cons_eq_of_eligible hx hp he
  change (∑ x, f x) ≤ _
  by_cases hb : signCokernelIndex R = 0 ∨ cap < signCokernelIndex R
  · rw [ite_eq_left hb]
    calc
      _ ≤ ∑ x, if x ∈ extraSigns R then 1 / ((extraSigns R).card : ℝ) else 0 := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : f x = 0
        · rw [h]
          split <;> positivity
        · rw [ite_eq_left (hMarked x h).1]
          exact (hMarked x h).2.2.le
      _ = ((extraSigns R).card : ℝ) * (1 / ((extraSigns R).card : ℝ)) := by
        have hfilter : Finset.univ.filter (· ∈ extraSigns R) = extraSigns R := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 := by
        by_cases he : (extraSigns R).card = 0
        · simp [he]
        · have hp : 0 < ((extraSigns R).card : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero he
          field_simp
          exact le_rfl
  · rw [ite_eq_right hb]
    exact Finset.sum_nonpos fun x _ => (not_ne_iff.mp (fun hx => hb (hMarked x hx).2.1)).le


/-- The sign-span failure count is controlled by the bad cokernel and
small-coefficient exceptional counts. This is the finite weighted
reduction in Proposition 1. -/
theorem card_bad_signSpan_le_cokernel (n r cap : ℕ) :
    (Nat.card {R : Fin (r + 1) → Fin (n + 1) → Bool // ¬ SignSpanGood R} : ℝ) ≤
      3 * (Nat.card {R : Fin (r + 1) → Fin (n + 1) → Bool //
        signCokernelIndex R = 0 ∨ cap < signCokernelIndex R} : ℝ) +
      (Nat.card {R : Fin (r + 1) → Fin (n + 1) → Bool // HasSmallSignRelation cap R} : ℝ) := by
  classical
  let X := Fin (r + 1) → Fin (n + 1) → Bool
  let D : Set X := {R | ¬ SignSpanGood R}
  let L : Set X := {R | signCokernelIndex R = 0 ∨ cap < signCokernelIndex R}
  let S : Set X := {R | HasSmallSignRelation cap R}
  let E : Set X := {R | R ∈ D ∧ R ∉ L ∧ R ∉ S}
  have hE : (Nat.card E : ℝ) ≤ 2 * (Nat.card L : ℝ) := by
    refine card_le_twice_card_of_symmetric_weight (signSpanWeight cap) (largeCoordinate cap)
      (· ∈ E) (· ∈ L) signSpanWeight_nonneg (fun e M => signSpanWeight_reindex e M)
      (largeCoordinate_reindex cap) ?_ ?_ signSpanWeight_marked_bound
    · intro M h
      have he : spanWeightEligible cap M := by
        by_contra hm
        simp [signSpanWeight, hm] at h
      exact he.2
    · intro R h
      exact signSpanWeight_cover R h.1 (fun hz => h.2.1 (Or.inl hz)) h.2.2
  have hsub : D ⊆ (E ∪ L) ∪ S := by
    intro R hR
    by_cases hS : R ∈ S
    · exact Or.inr hS
    · by_cases hL : R ∈ L
      · exact Or.inl (Or.inr hL)
      · exact Or.inl (Or.inl ⟨hR, hL, hS⟩)
  have hcard : Nat.card D ≤ Nat.card E + Nat.card L + Nat.card S := by
    exact (ncard_le_ncard hsub).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_union_le _ _) _))
  have hcast : (Nat.card D : ℝ) ≤ (Nat.card E : ℝ) + (Nat.card L : ℝ) + (Nat.card S : ℝ) := by
    exact_mod_cast hcard
  change (Nat.card D : ℝ) ≤ 3 * (Nat.card L : ℝ) + (Nat.card S : ℝ)
  linarith

/-- The normalized binary interior of a uniform sign matrix is uniform. -/
theorem card_bad_signCokernelIndex (n r cap : ℕ) :
    Nat.card {R : Fin (r + 1) → Fin (n + 1) → Bool //
      signCokernelIndex R = 0 ∨ cap < signCokernelIndex R} =
      2 ^ (n + 1 + r) * Nat.card {B : Matrix (Fin r) (Fin n) Bool //
        let q := (LinearMap.range (B.map zeroOneBit).mulVecLin).toAddSubgroup.index
        q = 0 ∨ cap < q} := by
  let e (i j : ℕ) : Matrix (Fin i) (Fin j) Bool ≃ Matrix (Fin j) (Fin i) Bool :=
    ⟨Matrix.transpose, Matrix.transpose, Matrix.transpose_transpose, Matrix.transpose_transpose⟩
  let s : Set (Matrix (Fin n) (Fin r) Bool) := {B |
    let q := (LinearMap.range (B.transpose.map zeroOneBit).mulVecLin).toAddSubgroup.index
    q = 0 ∨ cap < q}
  let e' : {R : Fin (r + 1) → Fin (n + 1) → Bool //
        signCokernelIndex R = 0 ∨ cap < signCokernelIndex R} ≃
      {A : Matrix (Fin (n + 1)) (Fin (r + 1)) Bool // (signMatrixCoordinates n r A).2.2 ∈ s} :=
    Equiv.subtypeEquiv (e (r + 1) (n + 1)) (fun _ => Iff.rfl)
  rw [Nat.card_congr e', card_normalizedInterior_preimage n r s]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquiv (e n r) (fun _ => Iff.rfl))

end BooleanThreshold
