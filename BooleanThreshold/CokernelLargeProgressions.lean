module

public import BooleanThreshold.CokernelLargeExposure
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Function Matrix Set MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace BooleanThreshold

/-- Volume of the integer box in a symmetric generalized arithmetic progression. -/
@[expose] def progressionVolume {d : ℕ} (L : Fin d → ℕ) : ℕ :=
  ∏ i, (2 * L i + 1)

/-- All linear combinations of the generators with coefficients in the box. -/
@[expose] noncomputable def symmetricProgression {d : ℕ} {K : Type*} [Ring K]
    (L : Fin d → ℕ) (g : Fin d → K) : Finset K :=
  open Classical in
  (Finset.univ : Finset (∀ i, (Finset.Icc (-(L i : ℤ)) (L i : ℤ) : Finset ℤ))).image
    (fun z => ∑ i, ((z i : ℤ) : K) * g i)

theorem mem_symmetricProgression_iff {d : ℕ} {K : Type*} [Ring K]
    (L : Fin d → ℕ) (g : Fin d → K) (x : K) :
    x ∈ symmetricProgression L g ↔
      ∃ z : ∀ i, (Finset.Icc (-(L i : ℤ)) (L i : ℤ) : Finset ℤ),
        (∑ i, ((z i : ℤ) : K) * g i) = x := by
  classical
  simp only [symmetricProgression, Finset.mem_image, Finset.mem_univ, true_and]

theorem card_symmetricProgression_le {d : ℕ} {K : Type*} [Ring K]
    (L : Fin d → ℕ) (g : Fin d → K) :
    (symmetricProgression L g).card ≤ progressionVolume L := by
  classical
  unfold symmetricProgression progressionVolume
  refine Finset.card_image_le.trans_eq ?_
  rw [Finset.card_univ, Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_coe, Int.card_Icc]
  omega

/-- The number of vectors restricted to a fixed finite set outside a fixed
exception set is bounded by the product of the corresponding coordinate counts. -/
theorem card_vectors_outside_exception_le {ι K : Type*} [Fintype ι] [Fintype K]
    (E : Finset ι) (Q : Finset K) {V : ℕ} (hV : Q.card ≤ V) :
    Nat.card {a : ι → K // ∀ i ∉ E, a i ∈ Q} ≤
      (Fintype.card K) ^ E.card * V ^ (Fintype.card ι - E.card) := by
  classical
  let D : Finset ι := Finset.univ \ E
  let f : {a : ι → K // ∀ i ∉ E, a i ∈ Q} → (E → K) × (D → Q) := fun a =>
    (fun i => a.val i, fun i => ⟨a.val i, a.prop i (Finset.mem_sdiff.mp i.prop).2⟩)
  have hf : Injective f := by
    intro a b h
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ E
    · exact congrArg (fun x : (E → K) × (D → Q) => x.1 ⟨i, hi⟩) h
    · have hd : i ∈ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      exact congrArg (fun x : (E → K) × (D → Q) => (x.2 ⟨i, hd⟩).val) h
  have hD : D.card = Fintype.card ι - E.card := by
    unfold D
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  calc
    _ ≤ Nat.card ((E → K) × (D → Q)) := Nat.card_le_card_of_injective f hf
    _ = (Fintype.card K) ^ E.card * Q.card ^ (Fintype.card ι - E.card) := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe, hD]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV _)

/-- All coordinates outside one set of `t` exceptions lie in a progression
of rank `d` whose integer box has volume at most `V`. -/
@[expose] def ProgressionStructured {N : ℕ} {K : Type*} [Ring K] (t d V : ℕ)
    (a : Fin N → K) : Prop :=
  ∃ E : Finset (Fin N), E.card = t ∧ ∃ (L : Fin d → ℕ) (g : Fin d → K),
    progressionVolume L ≤ V ∧ ∀ i ∉ E, a i ∈ symmetricProgression L g

/-- Counting exception sets, lengths, generators, and coordinates gives
the bound in (40), with `V+1` possible lengths before imposing the volume constraint. -/
theorem card_progressionStructured_le {K : Type*} [Ring K] [Fintype K]
    (N t d V : ℕ) :
    Nat.card {a : Fin N → K // ProgressionStructured t d V a} ≤
      N.choose t * (V + 1) ^ d * (Fintype.card K) ^ (t + d) * V ^ (N - t) := by
  classical
  let S := (Finset.univ : Finset (Fin N)).powersetCard t
  let J := S × (Fin d → Fin (V + 1)) × (Fin d → K)
  let lengths (j : J) : Fin d → ℕ := fun i => (j.2.1 i).val
  let Box (j : J) : Finset K := symmetricProgression (lengths j) j.2.2
  let Adm (j : J) (a : Fin N → K) :=
    progressionVolume (lengths j) ≤ V ∧ ∀ i ∉ j.1.val, a i ∈ Box j
  have hw (a : Fin N → K) (h : ProgressionStructured t d V a) : ∃ j : J, Adm j a := by
    obtain ⟨E, hE, L, g, hL, h⟩ := h
    have hs (i : Fin d) : L i < V + 1 := by
      have hp : 2 * L i + 1 ≤ progressionVolume L := by
        apply Finset.single_le_prod (fun k _ => ?_) (Finset.mem_univ i)
        omega
      omega
    exact ⟨⟨⟨E, Finset.mem_powersetCard_univ.mpr hE⟩, fun i => ⟨L i, hs i⟩, g⟩, hL, h⟩
  let f : {a : Fin N → K // ProgressionStructured t d V a} →
      Σ j : J, {a : Fin N → K // Adm j a} := fun a =>
    ⟨Classical.choose (hw a.val a.prop), a.val, Classical.choose_spec (hw a.val a.prop)⟩
  have hf : Injective f := fun a b h =>
    Subtype.ext (congrArg (fun z : Σ j : J, {a : Fin N → K // Adm j a} => z.2.val) h)
  have hcard (j : J) : Nat.card {a : Fin N → K // Adm j a} ≤ (Fintype.card K) ^ t * V ^ (N - t) := by
    by_cases hL : progressionVolume (lengths j) ≤ V
    · have hE : j.1.val.card = t := Finset.mem_powersetCard_univ.mp j.1.prop
      let g : {a : Fin N → K // Adm j a} → {a : Fin N → K // ∀ i ∉ j.1.val, a i ∈ Box j} :=
        fun a => ⟨a.val, a.prop.2⟩
      refine (Nat.card_le_card_of_injective g (fun a b h => Subtype.ext (congrArg
        (fun x : {a : Fin N → K // ∀ i ∉ j.1.val, a i ∈ Box j} => x.val) h))).trans ?_
      have hbound := card_vectors_outside_exception_le j.1.val (Box j)
        ((card_symmetricProgression_le (lengths j) j.2.2).trans hL)
      simpa only [hE, Fintype.card_fin] using hbound
    · have hEmpty : IsEmpty {a : Fin N → K // Adm j a} := ⟨fun a => hL a.prop.1⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hJ : Fintype.card J = N.choose t * ((V + 1) ^ d * (Fintype.card K) ^ d) := by
    simp only [J, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
      S, Finset.card_powersetCard, Finset.card_univ]
  calc
    _ ≤ Nat.card (Σ j : J, {a : Fin N → K // Adm j a}) := Nat.card_le_card_of_injective f hf
    _ = ∑ j : J, Nat.card {a : Fin N → K // Adm j a} := Nat.card_sigma
    _ ≤ ∑ _j : J, (Fintype.card K) ^ t * V ^ (N - t) := Finset.sum_le_sum fun j _ => hcard j
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hJ, pow_add, Nat.cast_id]
      ring

/-- The largest atom of a binary linear form on the finite field. -/
@[expose] noncomputable def binaryConcentration {p N : ℕ} [Fact p.Prime] (a : Fin N → ZMod p) : ℝ :=
  (Finset.univ : Finset (ZMod p)).sup' Finset.univ_nonempty fun z =>
    (uniformOn Set.univ).real {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z}

theorem binary_atom_le_concentration {p N : ℕ} [Fact p.Prime]
    (a : Fin N → ZMod p) (z : ZMod p) :
    (uniformOn Set.univ).real {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} ≤
      binaryConcentration a := by
  unfold binaryConcentration
  exact Finset.le_sup' (fun z =>
    (uniformOn Set.univ).real {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z}) (Finset.mem_univ z)

/-- With a fixed normal, annihilation by the independently sampled columns
is bounded by the largest atom to the number of columns. -/
theorem all_binary_columns_annihilate_mass_le {p N m : ℕ} [Fact p.Prime]
    (a : Fin N → ZMod p) {q : ℝ} (ha : binaryConcentration a ≤ q) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool |
      ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ≤ q ^ m := by
  let E : Set (Fin N → Bool) := {x | a ⬝ᵥ binaryColumn (ZMod p) x = 0}
  have hE : {R : Fin m → Fin N → Bool | ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} =
      Set.univ.pi (fun _ : Fin m => E) := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, E]
  rw [hE]
  rw [← pi_uniformOn_univ, measureReal_def, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow, ← measureReal_def]
  exact pow_le_pow_left₀ measureReal_nonneg ((binary_atom_le_concentration a 0).trans ha) _

/-- Union bound for a progression class whose atoms are uniformly small. -/
theorem structured_annihilation_mass_le {p N m : ℕ} [Fact p.Prime] (t d V : ℕ)
    {q : ℝ} (hq : 0 ≤ q) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool |
      ∃ a : Fin N → ZMod p, ProgressionStructured t d V a ∧ binaryConcentration a ≤ q ∧
        ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ≤
      (N.choose t : ℝ) * ((V + 1 : ℕ) : ℝ) ^ d * (p : ℝ) ^ (t + d) *
        (V : ℝ) ^ (N - t) * q ^ m := by
  classical
  let μ := uniformOn (Set.univ : Set (Fin m → Fin N → Bool))
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let s : Finset (Fin N → ZMod p) := Finset.univ.filter
    (fun a => ProgressionStructured t d V a ∧ binaryConcentration a ≤ q)
  let E (a : Fin N → ZMod p) : Set (Fin m → Fin N → Bool) :=
    {R | ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0}
  have he : {R : Fin m → Fin N → Bool |
      ∃ a : Fin N → ZMod p, ProgressionStructured t d V a ∧ binaryConcentration a ≤ q ∧
        ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} = ⋃ a ∈ s, E a := by
    ext R
    simp only [mem_ofPred_eq, mem_iUnion, s, E, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, hq, hkill⟩
      exact ⟨a, ⟨ha, hq⟩, hkill⟩
    · rintro ⟨a, ⟨ha, hq⟩, hkill⟩
      exact ⟨a, ha, hq, hkill⟩
  have hs : s.card ≤ Nat.card {a : Fin N → ZMod p // ProgressionStructured t d V a} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩
  have hcard : (s.card : ℝ) ≤ (N.choose t : ℝ) * ((V + 1 : ℕ) : ℝ) ^ d *
      (p : ℝ) ^ (t + d) * (V : ℝ) ^ (N - t) := by
    exact_mod_cast hs.trans (by simpa only [ZMod.card] using
      (card_progressionStructured_le (K := ZMod p) N t d V))
  rw [he]
  calc
    _ ≤ ∑ a ∈ s, μ.real (E a) := measureReal_biUnion_finset_le s E
    _ ≤ ∑ _a ∈ s, q ^ m := Finset.sum_le_sum fun a ha =>
      all_binary_columns_annihilate_mass_le a (Finset.mem_filter.mp ha).2.2
    _ = (s.card : ℝ) * q ^ m := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)


/-- Holding all but one nonzero coefficient fixed bounds every atom by one half. -/
theorem binaryConcentration_le_half {p N : ℕ} [Fact p.Prime]
    {a : Fin N → ZMod p} (ha : a ≠ 0) : binaryConcentration a ≤ 1 / 2 := by
  classical
  have hex : ∃ i, a i ≠ 0 := by
    by_contra h
    exact ha (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hex
  let f (x : Fin N → Bool) := Function.update x i (!(x i))
  have hf : Involutive f := by
    intro x
    funext j
    by_cases h : j = i
    · subst j
      simp [f]
    · simp [f, Function.update_of_ne h]
  have hF (x : Fin N → Bool) : a ⬝ᵥ binaryColumn (ZMod p) (f x) ≠
      a ⬝ᵥ binaryColumn (ZMod p) x := by
    intro h
    let r := ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, a j * binaryColumn (ZMod p) x j
    have h' : a ⬝ᵥ binaryColumn (ZMod p) x = r + a i * binaryColumn (ZMod p) x i :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    have h'' : a ⬝ᵥ binaryColumn (ZMod p) (f x) = r + a i * binaryColumn (ZMod p) (f x) i := by
      rw [dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := (Finset.mem_erase.mp hj).1
      simp [f, binaryColumn, Function.update_of_ne hj']
    rw [h', h'', add_right_inj] at h
    cases hx : x i <;> simp [f, binaryColumn, hx, hi, Ne.symm hi] at h
  unfold binaryConcentration
  apply Finset.sup'_le
  intro z _
  let E : Finset (Fin N → Bool) := Finset.univ.filter
    (fun x => a ⬝ᵥ binaryColumn (ZMod p) x = z)
  have hdis : Disjoint E (E.image f) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    exact hF w ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hw).2.symm)
  have hc : 2 * E.card ≤ 2 ^ N := by
    have hu := Finset.card_le_card (Finset.subset_univ (E ∪ E.image f))
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hf.injective,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hu
    omega
  have he : {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = z} = (E : Set _) := by
    ext x
    simp [E]
  rw [uniformOn_univ_real_eq_card, he, Set.ncard_coe_finset]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul, mul_comm (E.card : ℝ)] using
    (show (2 : ℝ) * E.card ≤ (2 : ℝ) ^ N by exact_mod_cast hc)

/-- A sparse nonzero normal is a rank-zero progression away from its support. -/
theorem sparse_binary_normal_annihilation_mass_le {p N m t : ℕ} [Fact p.Prime] (ht : t ≤ N) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool |
      ∃ a : Fin N → ZMod p, a ≠ 0 ∧ (Finset.univ.filter fun i => a i ≠ 0).card ≤ t ∧
        ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ≤
      (N.choose t : ℝ) * (p : ℝ) ^ t * (1 / 2 : ℝ) ^ m := by
  classical
  refine (measureReal_mono (s₂ := {R : Fin m → Fin N → Bool |
    ∃ a : Fin N → ZMod p, ProgressionStructured t 0 1 a ∧ binaryConcentration a ≤ 1 / 2 ∧
      ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0}) ?_).trans ?_
  · rintro R ⟨a, ha, hs, hnull⟩
    obtain ⟨E, hSE, _, hEt⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (Finset.univ.filter fun i => a i ≠ 0)) hs
      (by simpa only [Finset.card_univ, Fintype.card_fin] using ht)
    refine ⟨a, ⟨E, hEt, Fin.elim0, Fin.elim0, by simp [progressionVolume], ?_⟩,
      binaryConcentration_le_half ha, hnull⟩
    intro i hi
    have hzero : a i = 0 := by
      by_contra hn
      exact hi (hSE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    rw [hzero, mem_symmetricProgression_iff]
    exact ⟨fun i => i.elim0, by simp⟩
  · simpa using structured_annihilation_mass_le (p := p) (N := N) (m := m) t 0 1
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)

end BooleanThreshold
