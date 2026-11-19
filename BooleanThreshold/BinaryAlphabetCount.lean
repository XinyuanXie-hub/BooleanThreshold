module

public import BooleanThreshold.CokernelLargeExposure
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical

namespace BooleanThreshold

private theorem card_functions_of_alphabet {α : Type*} [Fintype α] {n : ℕ}
    (B : Finset α) (I : Finset (Fin n)) :
    (Fintype.piFinset (fun i : Fin n => if i ∈ I then univ else B)).card =
      (Fintype.card α) ^ I.card * B.card ^ (n - I.card) := by
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_univ]
  rw [← prod_filter_mul_prod_filter_not _ (fun i => i ∈ I)]
  have h₁ : (univ.filter fun i : Fin n => i ∈ I) = I := by ext i; simp
  have h₂ : (univ.filter fun i : Fin n => i ∉ I) = univ \ I := by ext i; simp
  rw [h₁, h₂]
  rw [prod_congr rfl (fun i hi => ite_eq_left hi),
    prod_congr rfl (fun i hi => ite_eq_right (mem_sdiff.mp hi).2)]
  rw [prod_const, prod_const, card_sdiff_of_subset (subset_univ I), card_univ, Fintype.card_fin]

/-- A finite family of coefficient alphabets gives a counting bound when at most
`t` coordinates may lie outside one of those alphabets. -/
theorem card_le_of_alphabet_exceptions {α J : Type*} [Fintype α] [Fintype J] {n t : ℕ}
    (A : Finset (Fin n → α)) (alphabet : J → Finset α) {V : ℝ} (_hV : 0 ≤ V)
    (hcard : ∀ j, ((alphabet j).card : ℝ) ≤ V)
    (hcover : ∀ a ∈ A, ∃ j, ∃ I : Finset (Fin n), I.card = t ∧
      ∀ i ∉ I, a i ∈ alphabet j) :
    (A.card : ℝ) ≤ (Fintype.card J : ℝ) * (n.choose t : ℝ) *
      (Fintype.card α : ℝ) ^ t * V ^ (n - t) := by
  let choices := (univ : Finset (Fin n)).powersetCard t
  let F (j : J) (I : Finset (Fin n)) := Fintype.piFinset (fun i => if i ∈ I then univ else alphabet j)
  let G (j : J) := choices.biUnion (F j)
  have hsub : A ⊆ univ.biUnion G := by
    intro a ha
    obtain ⟨j, I, hI, hF⟩ := hcover a ha
    refine mem_biUnion.mpr ⟨j, mem_univ _, mem_biUnion.mpr ⟨I, ?_, Fintype.mem_piFinset.mpr ?_⟩⟩
    · exact mem_powersetCard.mpr ⟨subset_univ _, hI⟩
    · intro i
      by_cases hi : i ∈ I
      · simp [hi]
      · simpa only [ite_eq_right hi] using hF i hi
  have hG (j : J) : ((G j).card : ℝ) ≤ (n.choose t : ℝ) * (Fintype.card α : ℝ) ^ t *
      V ^ (n - t) := by
    calc
      _ ≤ ∑ I ∈ choices, ((F j I).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _I ∈ choices, (Fintype.card α : ℝ) ^ t * V ^ (n - t) := by
        apply sum_le_sum
        intro I hI
        dsimp only [F]
        rw [card_functions_of_alphabet, (mem_powersetCard.mp hI).2]
        push_cast
        gcongr
        exact hcard j
      _ = _ := by simp [choices, card_powersetCard, nsmul_eq_mul, mul_assoc]
  calc
    _ ≤ ((univ.biUnion G).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ∑ j, ((G j).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _j : J, (n.choose t : ℝ) * (Fintype.card α : ℝ) ^ t * V ^ (n - t) := sum_le_sum fun j _ => hG j
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

/-- Probability that a binary vector annihilates the given coefficient vector. -/
@[expose] noncomputable def binaryZeroAtom {p n : ℕ} (a : Fin n → ZMod p) : ℝ :=
  (uniformOn Set.univ).real {x : Fin n → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = 0}

theorem all_binary_columns_zero_atom {p n m : ℕ} (a : Fin n → ZMod p) :
    (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
      ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} = binaryZeroAtom a ^ m := by
  let E : Set (Fin n → Bool) := {x | a ⬝ᵥ binaryColumn (ZMod p) x = 0}
  have hE : {R : Fin m → Fin n → Bool | ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} =
      Set.univ.pi (fun _ : Fin m => E) := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, E]
  rw [hE, ← pi_uniformOn_univ, measureReal_def, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow, ← measureReal_def]
  rfl

/-- The alphabet count times the probability of annihilating any one admissible vector. -/
theorem alphabet_annihilation_mass_le {p n m t : ℕ} [NeZero p]
    {J : Type*} [Fintype J] (alphabet : J → Finset (ZMod p))
    (P : (Fin n → ZMod p) → Prop) {V q : ℝ} (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hcard : ∀ j, ((alphabet j).card : ℝ) ≤ V)
    (hcover : ∀ a, P a → ∃ j, ∃ I : Finset (Fin n), I.card = t ∧
      ∀ i ∉ I, a i ∈ alphabet j)
    (hatom : ∀ a, P a → binaryZeroAtom a ≤ q) :
    (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
      ∃ a : Fin n → ZMod p, P a ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ≤
        (Fintype.card J : ℝ) * (n.choose t : ℝ) * (p : ℝ) ^ t * V ^ (n - t) * q ^ m := by
  let A := univ.filter P
  let E (a : Fin n → ZMod p) : Set (Fin m → Fin n → Bool) :=
    {R | ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0}
  have hE : {R : Fin m → Fin n → Bool |
      ∃ a : Fin n → ZMod p, P a ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} =
      ⋃ a ∈ A, E a := by
    ext R
    simp [A, E]
  have bound := card_le_of_alphabet_exceptions A alphabet hV hcard
    (fun a ha => hcover a (mem_filter.mp ha).2)
  rw [ZMod.card] at bound
  rw [hE]
  calc
    _ ≤ ∑ a ∈ A, (uniformOn Set.univ).real (E a) := measureReal_biUnion_finset_le A E
    _ ≤ ∑ _a ∈ A, q ^ m := by
      apply sum_le_sum
      intro a ha
      dsimp only [E]
      rw [all_binary_columns_zero_atom]
      exact pow_le_pow_left₀ measureReal_nonneg (hatom a (mem_filter.mp ha).2) _
    _ = (A.card : ℝ) * q ^ m := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right bound (pow_nonneg hq _)

end BooleanThreshold
