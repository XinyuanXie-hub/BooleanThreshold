module

public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

open Finset Filter
open scoped Topology

namespace BooleanThreshold

noncomputable section

variable {α V : Type*} [Fintype α] [DecidableEq α] [AddCommGroup V] [Module ℝ V]

/-- Strict linear sign patterns in which a specified form has positive sign. -/
def positivePatterns (base : α) (normal : α → V) : Finset (Finset {i // i ≠ base}) := by
  classical
  exact univ.filter fun u =>
    ∃ ℓ : V →ₗ[ℝ] ℝ, 0 < ℓ (normal base) ∧
      ∀ i : {i // i ≠ base},
        (i ∈ u → 0 < ℓ (normal i)) ∧ (i ∉ u → ℓ (normal i) < 0)

@[simp]
theorem mem_positivePatterns {base : α} {normal : α → V} {u : Finset {i // i ≠ base}} :
    u ∈ positivePatterns base normal ↔
      ∃ ℓ : V →ₗ[ℝ] ℝ, 0 < ℓ (normal base) ∧
        ∀ i : {i // i ≠ base},
          (i ∈ u → 0 < ℓ (normal i)) ∧ (i ∉ u → ℓ (normal i) < 0) := by
  simp [positivePatterns]

private theorem shatters_linearIndependent {base : α} {normal : α → V}
    {s : Finset {i // i ≠ base}} (h : (positivePatterns base normal).Shatters s) :
    LinearIndependent ℝ
      (fun i : Option s => Option.casesOn' i (normal base) (fun j : s => normal j.val)) := by
  classical
  let e : Option s → V :=
    fun i => Option.casesOn' i (normal base) (fun j : s => normal j.val)
  change LinearIndependent ℝ e
  rw [Fintype.linearIndependent_iff]
  have cancel (c : Option s → ℝ) (hc : ∑ i, c i • e i = 0) (hn : 0 ≤ c none) :
      ∀ i, c i = 0 := by
    let t := s.filter fun i => ∀ hi : i ∈ s, 0 ≤ c (some ⟨i, hi⟩)
    obtain ⟨u, hu, hu'⟩ := h (filter_subset _ _ : t ⊆ s)
    obtain ⟨ℓ, hbase, hsign⟩ := mem_positivePatterns.mp hu
    have hmem (i : s) : i.val ∈ u ↔ 0 ≤ c (some i) := by
      have h₁ : i.val ∈ s ∩ u ↔ i.val ∈ u := by simp [i.prop]
      rw [hu'] at h₁
      rw [← h₁]
      simp [i.prop]
    have hsum : ∑ i, c i * ℓ (e i) = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg (fun v => ℓ v) hc
    have hnonneg : ∀ i, 0 ≤ c i * ℓ (e i) := by
      intro i
      cases i with
      | none => exact mul_nonneg hn hbase.le
      | some i =>
          by_cases hi : i.val ∈ u
          · exact mul_nonneg ((hmem i).mp hi) ((hsign i.val).1 hi).le
          · exact mul_nonneg_of_nonpos_of_nonpos
              (le_of_lt (lt_of_not_ge (fun hn' => hi ((hmem i).mpr hn'))))
              ((hsign i.val).2 hi).le
    have hne : ∀ i, ℓ (e i) ≠ 0 := by
      intro i
      cases i with
      | none => exact hbase.ne'
      | some i =>
          by_cases hi : i.val ∈ u
          · exact ((hsign i.val).1 hi).ne'
          · exact ((hsign i.val).2 hi).ne
    intro i
    have hz : c i * ℓ (e i) = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (mem_univ i)
    exact (mul_eq_zero.mp hz).resolve_right (hne i)
  intro c hc i
  by_cases hn : 0 ≤ c none
  · exact cancel c hc hn i
  · have hneg : ∑ j, -c j • e j = 0 := by
      simp only [neg_smul, sum_neg_distrib, hc, neg_zero]
    exact neg_eq_zero.mp (cancel (fun j => -c j) hneg (neg_nonneg.mpr (le_of_not_ge hn)) i)

/-- The half of a central arrangement with one prescribed positive sign has VC dimension at most
one less than the dimension of the ambient vector space. -/
theorem card_positivePatterns_le [Module.Finite ℝ V]
    (base : α) (normal : α → V) {d : ℕ} (hd : Module.finrank ℝ V = d + 1) :
    (positivePatterns base normal).card ≤
      ∑ k ∈ Iic d, (Fintype.card {i // i ≠ base}).choose k := by
  have hv : (positivePatterns base normal).vcDim ≤ d := by
    refine Finset.sup_le_iff.mpr fun s hs => ?_
    have h := (shatters_linearIndependent (mem_shatterer.mp hs)).fintype_card_le_finrank
    have : s.card + 1 ≤ d + 1 := by simpa [hd] using h
    omega
  exact (card_le_card_shatterer _).trans <| card_shatterer_le_sum_vcDim.trans <|
    sum_le_sum_of_subset_of_nonneg (Iic_subset_Iic.mpr hv) fun _ _ _ => Nat.zero_le _

/-- Each set in `G` is strongly shattered by `A` if some fixed choice of signs outside it allows
every choice inside it. The complement form of Sauer–Shelah bounds the number of such sets. -/
theorem card_le_of_strong_patterns (G A : Finset (Finset α))
    (h : ∀ s ∈ G, ∃ u ⊆ sᶜ, ∀ t ⊆ s, u ∪ t ∈ A) :
    G.card ≤ A.card := by
  have hsub : G.image (fun s => sᶜ) ⊆ (Aᶜ).shattererᶜ := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
    obtain ⟨u, hu, hpatterns⟩ := h s hs
    rw [mem_compl, mem_shatterer]
    intro hs'
    obtain ⟨v, hv, hinter⟩ := hs' hu
    have hv' : v ∉ A := mem_compl.mp hv
    apply hv'
    have hsplit : u ∪ (s ∩ v) = v := by
      rw [← hinter]
      ext i
      by_cases hi : i ∈ s <;> simp [hi]
    rw [← hsplit]
    exact hpatterns _ inter_subset_left
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ compl_injective] at hcard
  exact hcard.trans <| by
    have hsh := card_le_card_shatterer Aᶜ
    simp only [card_compl] at hcard hsh ⊢
    omega

/-- A sufficiently small positive perturbation preserves every nonzero sign in a finite list. -/
theorem exists_positive_preserving_signs {ι : Type*} [Finite ι] (p q : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i,
      (0 < p i → 0 < p i + ε * q i) ∧ (p i < 0 → p i + ε * q i < 0) := by
  have hstable : ∀ᶠ ε : ℝ in 𝓝 0, ∀ i,
      (0 < p i → 0 < p i + ε * q i) ∧ (p i < 0 → p i + ε * q i < 0) := by
    refine eventually_all.mpr fun i => ?_
    have hc : ContinuousAt (fun ε : ℝ => p i + ε * q i) 0 :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
    have ht : Tendsto (fun ε : ℝ => p i + ε * q i) (𝓝 0) (𝓝 (p i)) := by
      simpa [ContinuousAt] using hc
    have hp : ∀ᶠ ε : ℝ in 𝓝 0, 0 < p i → 0 < p i + ε * q i := by
      by_cases h : 0 < p i
      · exact (ht.eventually_const_lt h).mono fun _ hε _ => hε
      · exact .of_forall fun _ h' => (h h').elim
    have hn : ∀ᶠ ε : ℝ in 𝓝 0, p i < 0 → p i + ε * q i < 0 := by
      by_cases h : p i < 0
      · exact (ht.eventually_lt_const h).mono fun _ hε _ => hε
      · exact .of_forall fun _ h' => (h h').elim
    exact hp.and hn
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  exact (hpos.and (hstable.filter_mono nhdsWithin_le_nhds)).exists

/-- A full set of independent normals with no other normals in its span is strongly shattered on
the positive side of the base normal. -/
theorem strong_patterns_of_span [Module.Finite ℝ V] {base : α} {normal : α → V}
    {s : Finset {i // i ≠ base}} (hd : Module.finrank ℝ V = s.card + 1)
    (hind : LinearIndependent ℝ (fun j : s => normal j.val))
    (hbase : normal base ∉ Submodule.span ℝ (Set.range (fun j : s => normal j.val)))
    (hspan : ∀ i : {i // i ≠ base},
      normal i ∈ Submodule.span ℝ (Set.range (fun j : s => normal j.val)) → i ∈ s) :
    ∃ u ⊆ sᶜ, ∀ t ⊆ s, u ∪ t ∈ positivePatterns base normal := by
  classical
  let e : Option s → V :=
    fun i => Option.casesOn' i (normal base) (fun j : s => normal j.val)
  let b : Module.Basis (Option s) ℝ V :=
    basisOfLinearIndependentOfCardEqFinrank' e (hind.option hbase) (by simp [hd])
  have hb (j : Option s) : b j = e j := by
    simp [b]
  have hb_base : b none = normal base := hb none
  have hb_mem (j : s) : b (some j) = normal j.val := hb (some j)
  let p := b.coord none
  have hp_base : p (normal base) = 1 := by
    rw [← hb_base]
    simp [p, Module.Basis.coord_apply]
  have hp_mem (j : s) : p (normal j.val) = 0 := by
    rw [← hb_mem j]
    simp [p, Module.Basis.coord_apply]
  have himage : b '' ({none}ᶜ : Set (Option s)) =
      Set.range (fun j : s => normal j.val) := by
    ext v
    constructor
    · rintro ⟨(_ | j), hj, rfl⟩
      · simp at hj
      · exact ⟨j, (hb_mem j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨some j, by simp, hb_mem j⟩
  have hp_out (i : {i // i ≠ base}) (hi : i ∉ s) : p (normal i) ≠ 0 := by
    intro hz
    apply hi (hspan i ?_)
    rw [← himage, b.mem_span_image]
    intro j hj
    cases j with
    | none => exact (Finsupp.mem_support_iff.mp hj hz).elim
    | some j => simp
  let u := sᶜ.filter (fun i : {i // i ≠ base} => 0 < p (normal i))
  have hu : u ⊆ sᶜ := filter_subset _ _
  refine ⟨u, hu, ?_⟩
  intro t ht
  let values : Option s → ℝ :=
    fun j => Option.casesOn' j 0 (fun i : s => if i.val ∈ t then 1 else -1)
  let q : V →ₗ[ℝ] ℝ := b.constr ℝ values
  have hq_base : q (normal base) = 0 := by
    rw [← hb_base]
    exact b.constr_basis ℝ values none
  have hq_mem (j : s) : q (normal j.val) = if j.val ∈ t then 1 else -1 := by
    rw [← hb_mem j]
    exact b.constr_basis ℝ values (some j)
  obtain ⟨ε, hε, hε_out⟩ :=
    exists_positive_preserving_signs (fun i : {i // i ≠ base} => p (normal i))
      (fun i => q (normal i))
  refine mem_positivePatterns.mpr ⟨p + ε • q, ?_, ?_⟩
  · change 0 < p (normal base) + ε * q (normal base)
    simp [hp_base, hq_base]
  intro i
  change (i ∈ u ∪ t → 0 < p (normal i) + ε * q (normal i)) ∧
    (i ∉ u ∪ t → p (normal i) + ε * q (normal i) < 0)
  by_cases hi : i ∈ s
  · have hiu : i ∉ u := fun hmem => (mem_compl.mp (hu hmem)) hi
    have hq := hq_mem ⟨i, hi⟩
    have hp := hp_mem ⟨i, hi⟩
    change q (normal i) = _ at hq
    change p (normal i) = _ at hp
    by_cases hit : i ∈ t <;> simp [hiu, hit, hp, hq, hε]
  · have hit : i ∉ t := fun hmem => hi (ht hmem)
    have hiu : i ∈ u ↔ 0 < p (normal i) := by simp [u, hi]
    constructor
    · intro hmem
      have hmem' : i ∈ u := by simpa [hit] using hmem
      exact (hε_out i).1 (hiu.mp hmem')
    · intro hmem
      have hmem' : i ∉ u := by simpa [hit] using hmem
      exact (hε_out i).2 (lt_of_le_of_ne (le_of_not_gt fun h => hmem' (hiu.mpr h))
        (hp_out i hi))

end

end BooleanThreshold
