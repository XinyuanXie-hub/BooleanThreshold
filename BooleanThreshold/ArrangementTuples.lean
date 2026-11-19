module

public import BooleanThreshold.Arrangement
public import Mathlib.Data.Fintype.Perm

@[expose] public section

open Finset
open scoped Classical

namespace BooleanThreshold

noncomputable section

/-- The lifted vectors are independent, and their span contains only the listed lifted vertices. -/
def NormalizedGoodTuple {n : ℕ} (v : Fin n → Fin n → Bool) : Prop :=
  LinearIndependent ℝ (fun i => liftSignVertex (v i)) ∧
    ∀ x, liftSignVertex x ∈ Submodule.span ℝ (Set.range (fun i => liftSignVertex (v i))) →
      x ∈ Set.range v

/-- No entry is the distinguished base vertex. -/
def AvoidsBase {n : ℕ} (v : Fin n → Fin n → Bool) : Prop :=
  ∀ i, v i ≠ baseVertex n

private def tupleOfOrder {n : ℕ} (p : Σ s : ↥(arrangementGoodSets n), Fin n ≃ s.val) :
    {v : Fin n → Fin n → Bool // NormalizedGoodTuple v ∧ AvoidsBase v} := by
  let v (i : Fin n) := (p.2 i).val.val
  refine ⟨v, ⟨?_, ?_⟩, fun i => (p.2 i).val.prop⟩
  · exact ((mem_arrangementGoodSets.mp p.1.prop).2.1).comp p.2 p.2.injective
  · intro x hx
    have hrange : Set.range (fun i => liftSignVertex (v i)) =
        Set.range (fun j : p.1.val => liftSignVertex j.val.val) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨p.2 i, rfl⟩
      · rintro ⟨j, rfl⟩
        obtain ⟨i, rfl⟩ := p.2.surjective j
        exact ⟨i, rfl⟩
    rw [hrange] at hx
    obtain ⟨j, hj⟩ := (mem_arrangementGoodSets.mp p.1.prop).2.2 x hx
    obtain ⟨i, rfl⟩ := p.2.surjective j
    exact ⟨i, hj⟩

private theorem tupleOfOrder_bijective (n : ℕ) : Function.Bijective (@tupleOfOrder n) := by
  classical
  constructor
  · rintro ⟨⟨s, hs⟩, e⟩ ⟨⟨t, ht⟩, f⟩ h
    have heq (i : Fin n) : (e i).val = (f i).val := by
      apply Subtype.ext
      exact congrArg (fun v => v.val i) h
    have hst : s = t := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
        rw [← (show (e i).val = x from congrArg Subtype.val hi), heq i]
        exact (f i).prop
      · intro hx
        obtain ⟨i, hi⟩ := f.surjective ⟨x, hx⟩
        rw [← (show (f i).val = x from congrArg Subtype.val hi), ← heq i]
        exact (e i).prop
    subst t
    have hef : e = f := Equiv.ext fun i => Subtype.ext (heq i)
    cases hef
    rfl
  · intro v
    let f : Fin n ↪ {x : Fin n → Bool // x ≠ baseVertex n} :=
      ⟨fun i => ⟨v.val i, v.prop.2 i⟩,
        fun i j h => v.prop.1.1.injective (congrArg (fun x => liftSignVertex x.val) h)⟩
    let s := (univ : Finset (Fin n)).map f
    let e : Fin n ≃ ↥s :=
      Equiv.ofBijective (fun i => ⟨f i, mem_map_of_mem _ (mem_univ i)⟩)
        ⟨fun i j h => f.injective (congrArg Subtype.val h), fun j => by
          obtain ⟨i, _, hi⟩ := mem_map.mp j.prop
          exact ⟨i, Subtype.ext hi⟩⟩
    have hs : s ∈ arrangementGoodSets n := by
      refine mem_arrangementGoodSets.mpr ⟨by simp [s], ?_, ?_⟩
      · exact (linearIndependent_equiv e).mp v.prop.1.1
      · intro x hx
        have hrange : Set.range (fun j : s => liftSignVertex j.val.val) =
            Set.range (fun i => liftSignVertex (v.val i)) := by
          ext y
          constructor
          · rintro ⟨j, rfl⟩
            obtain ⟨i, rfl⟩ := e.surjective j
            exact ⟨i, rfl⟩
          · rintro ⟨i, rfl⟩
            exact ⟨e i, rfl⟩
        rw [hrange] at hx
        obtain ⟨i, hi⟩ := v.prop.1.2 x hx
        exact ⟨e i, hi⟩
    exact ⟨⟨⟨s, hs⟩, e⟩, Subtype.ext rfl⟩

/-- Each eligible subset has `n!` orderings, and these are exactly the eligible tuples. -/
theorem card_good_tuples_avoiding_base (n : ℕ) :
    Nat.card {v : Fin n → Fin n → Bool // NormalizedGoodTuple v ∧ AvoidsBase v} =
      (arrangementGoodSets n).card * n.factorial := by
  classical
  rw [Nat.card_congr (Equiv.ofBijective _ (tupleOfOrder_bijective n)).symm,
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hperm (s : ↥(arrangementGoodSets n)) : Fintype.card (Fin n ≃ s.val) = n.factorial := by
    have hs : s.val.card = n := (mem_arrangementGoodSets.mp s.prop).1
    have e : Fin n ≃ s.val := Fintype.equivOfCardEq (by simp [hs])
    simpa using Fintype.card_equiv e
  simp [hperm]

/-- At most `n * (2^n)^(n-1)` tuples meet the base vertex. -/
private theorem card_tuples_hitting_base (n : ℕ) :
    #{v ∈ (univ : Finset (Fin n → Fin n → Bool)) | ¬ AvoidsBase v} ≤
      n * (2 ^ n) ^ (n - 1) := by
  classical
  let A (i : Fin n) : Finset (Fin n → Fin n → Bool) := univ.filter (fun v => v i = baseVertex n)
  have hsub : {v ∈ (univ : Finset (Fin n → Fin n → Bool)) | ¬ AvoidsBase v} ⊆
      (univ : Finset (Fin n)).biUnion A := by
    intro v hv
    have h : ∃ i, v i = baseVertex n := by
      simpa only [AvoidsBase, mem_filter, mem_univ, true_and, not_forall, not_not] using hv
    obtain ⟨i, hi⟩ := h
    exact mem_biUnion.mpr ⟨i, mem_univ i, by simp [A, hi]⟩
  have hcard (i : Fin n) : (A i).card = (2 ^ n) ^ (n - 1) := by
    simpa [A] using Fintype.card_filter_piFinset_const_eq_of_mem
      (univ : Finset (Fin n → Bool)) i (x := baseVertex n) (mem_univ _)
  calc
    _ ≤ ((univ : Finset (Fin n)).biUnion A).card := card_le_card hsub
    _ ≤ ∑ i, (A i).card := card_biUnion_le
    _ = _ := by simp [hcard]

/-- Removing tuples that encounter the base vertex loses only the base-hit bound. -/
theorem card_good_tuples_le_good_sets (n : ℕ) :
    Nat.card {v : Fin n → Fin n → Bool // NormalizedGoodTuple v} ≤
      (arrangementGoodSets n).card * n.factorial + n * (2 ^ n) ^ (n - 1) := by
  classical
  let G := (univ : Finset (Fin n → Fin n → Bool)).filter NormalizedGoodTuple
  have hG : Nat.card {v : Fin n → Fin n → Bool // NormalizedGoodTuple v} = G.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hgood : (G.filter AvoidsBase).card = (arrangementGoodSets n).card * n.factorial := by
    rw [← card_good_tuples_avoiding_base, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext v
    simp [G]
  rw [hG, ← card_filter_add_card_filter_not (s := G) (p := AvoidsBase), hgood]
  apply Nat.add_le_add_left
  refine (card_le_card ?_).trans (card_tuples_hitting_base n)
  intro v hv
  exact mem_filter.mpr ⟨mem_univ v, (mem_filter.mp hv).2⟩

/-- Transfer a lower probability bound for the ordered uniform sample to the number of
eligible subsets of the non-base vertices. -/
theorem choose_mul_sub_le_card_good_sets (n : ℕ) (hn : 1 ≤ n) (δ : ℝ)
    (h : (1 - δ) * ((2 : ℝ) ^ n) ^ n ≤
      (Nat.card {v : Fin n → Fin n → Bool // NormalizedGoodTuple v} : ℝ)) :
    (1 - δ - n / (2 : ℝ) ^ n) * ((2 ^ n - 1).choose n : ℝ) ≤
      ((arrangementGoodSets n).card : ℝ) := by
  have hcard :
      (Nat.card {v : Fin n → Fin n → Bool // NormalizedGoodTuple v} : ℝ) ≤
        (arrangementGoodSets n).card * (n.factorial : ℝ) +
          (n : ℝ) * ((2 : ℝ) ^ n) ^ (n - 1) := by
    exact_mod_cast card_good_tuples_le_good_sets n
  have hpos : 0 < (2 : ℝ) ^ n := by positivity
  have hpow : ((2 : ℝ) ^ n) ^ n / (2 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ (n - 1) := by
    calc
      _ = ((2 : ℝ) ^ n) ^ (n - 1 + 1) / (2 : ℝ) ^ n :=
        congrArg (fun k : ℕ => ((2 : ℝ) ^ n) ^ k / (2 : ℝ) ^ n) (Nat.sub_add_cancel hn).symm
      _ = _ := by rw [pow_succ, mul_div_cancel_right₀ _ hpos.ne']
  have htransfer :
      (1 - δ - n / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ n ≤
        (arrangementGoodSets n).card * (n.factorial : ℝ) := by
    calc
      _ = (1 - δ) * ((2 : ℝ) ^ n) ^ n - (n : ℝ) * ((2 : ℝ) ^ n) ^ (n - 1) := by
        rw [sub_mul, ← hpow]
        ring
      _ ≤ _ := sub_le_iff_le_add.mpr (h.trans hcard)
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  by_cases hcoef : 0 ≤ 1 - δ - n / (2 : ℝ) ^ n
  · have hcompare :
        ((2 ^ n - 1).choose n : ℝ) * (n.factorial : ℝ) ≤ ((2 : ℝ) ^ n) ^ n := by
      have hnat : (2 ^ n - 1).choose n * n.factorial ≤ (2 ^ n) ^ n := by
        rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
        exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le ..) _)
      exact_mod_cast hnat
    refine (mul_le_mul_iff_of_pos_right hf).mp ?_
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hcompare hcoef).trans htransfer
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hcoef) (by positivity)).trans (by positivity)

end

end BooleanThreshold
