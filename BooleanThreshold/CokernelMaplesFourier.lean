module

public import BooleanThreshold.CokernelComparison
public import BooleanThreshold.CokernelLargeExposure
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.ToLin

public noncomputable section

open AddChar Matrix
open scoped BigOperators Classical Matrix

namespace BooleanThreshold

/-- The Fourier coefficient of a uniform bit on the cyclic group. -/
@[expose] def bitFourierCoefficient {q : ℕ} [NeZero q] (a : ZMod q) : ℂ :=
  (1 + ZMod.stdAddChar a) / 2

variable {q n : ℕ} [NeZero q]

private def vectorCharacter (a : Fin n → ZMod q) : AddChar (Fin n → ZMod q) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (dotProductBilin (ZMod q) (ZMod q) a).toAddMonoidHom

private theorem vectorCharacter_apply (a x : Fin n → ZMod q) :
    vectorCharacter a x = ZMod.stdAddChar (a ⬝ᵥ x) := rfl

private theorem vectorCharacter_injective : Function.Injective (vectorCharacter (q := q) (n := n)) := by
  intro a b hab
  funext i
  apply ZMod.injective_stdAddChar
  have h := DFunLike.congr_fun hab (Pi.single i 1)
  simpa only [vectorCharacter_apply, dotProduct_single_one] using h

private theorem vectorCharacter_surjective : Function.Surjective (vectorCharacter (q := q) (n := n)) :=
  ((Fintype.bijective_iff_injective_and_card _).2 ⟨vectorCharacter_injective, AddChar.card_eq.symm⟩).2

variable (V : Submodule (ZMod q) (Fin n → ZMod q))

local instance quotientFintype : Fintype ((Fin n → ZMod q) ⧸ V) :=
  Fintype.ofFinite _

/-- A character of the quotient has a unique vector of coefficients in the cyclic ring. -/
def quotientCharacterVector (ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ) : Fin n → ZMod q :=
  Classical.choose (vectorCharacter_surjective (ψ.compAddMonoidHom V.mkQ.toAddMonoidHom))

theorem quotientCharacterVector_apply (ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ)
    (x : Fin n → ZMod q) :
    ψ (V.mkQ x) = ZMod.stdAddChar (quotientCharacterVector V ψ ⬝ᵥ x) := by
  have h : vectorCharacter (quotientCharacterVector V ψ) = ψ.compAddMonoidHom V.mkQ.toAddMonoidHom :=
    Classical.choose_spec (vectorCharacter_surjective _)
  exact (DFunLike.congr_fun h x).symm

theorem quotientCharacterVector_orthogonal
    (ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ) {x : Fin n → ZMod q} (hx : x ∈ V) :
    quotientCharacterVector V ψ ⬝ᵥ x = 0 := by
  apply ZMod.injective_stdAddChar
  rw [← quotientCharacterVector_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero V).mpr hx,
    map_zero_eq_one, map_zero_eq_one]

theorem quotientCharacterVector_eq_zero_iff (ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ) :
    quotientCharacterVector V ψ = 0 ↔ ψ = 1 := by
  constructor
  · intro h
    rw [AddChar.eq_one_iff]
    intro y
    obtain ⟨x, rfl⟩ := V.mkQ_surjective y
    rw [quotientCharacterVector_apply, h, zero_dotProduct, map_zero_eq_one]
  · intro h
    apply vectorCharacter_injective
    ext x
    rw [vectorCharacter_apply, ← quotientCharacterVector_apply, h]
    simp [vectorCharacter_apply]

private theorem character_sum_eq_prod {A : Type*} [AddCommGroup A] {ι : Type*}
    (ψ : AddChar A ℂ) (s : Finset ι) (x : ι → A) : ψ (∑ i ∈ s, x i) = ∏ i ∈ s, ψ (x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi h => simp [hi, map_add_eq_mul, h]

/-- Fourier inversion for the probability of a prescribed coset of a
vector sampled coordinate by coordinate. -/
theorem sample_quotient_probability_fourier {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sample : Ω → ZMod q) (y : (Fin n → ZMod q) ⧸ V) :
    (finiteEventProbability (fun x : Fin n → Ω => V.mkQ (sample ∘ x) = y) : ℂ) =
      (∑ ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ,
        ψ (-y) * ∏ i, (∑ b, ZMod.stdAddChar (quotientCharacterVector V ψ i * sample b)) /
          (Fintype.card Ω : ℂ)) / (Fintype.card ((Fin n → ZMod q) ⧸ V) : ℂ) := by
  let Q := (Fin n → ZMod q) ⧸ V
  have hpow : ((Fintype.card (Fin n → Ω) : ℕ) : ℂ) = (Fintype.card Ω : ℂ) ^ n := by simp
  have hsum (ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ) :
      (∑ x : Fin n → Ω, ψ (V.mkQ (sample ∘ x) - y)) =
        ψ (-y) * ∏ i, ∑ b, ZMod.stdAddChar (quotientCharacterVector V ψ i * sample b) := by
    simp_rw [sub_eq_add_neg, map_add_eq_mul, ← Finset.sum_mul]
    rw [mul_comm, Fintype.prod_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [quotientCharacterVector_apply, dotProduct, character_sum_eq_prod]
    rfl
  have hind (x : Fin n → Ω) : (if V.mkQ (sample ∘ x) = y then (1 : ℂ) else 0) *
      (Fintype.card Q : ℂ) = ∑ ψ : AddChar Q ℂ, ψ (V.mkQ (sample ∘ x) - y) := by
    rw [AddChar.sum_apply_eq_ite, sub_eq_zero]
    split_ifs <;> simp
  have hcard : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbase : (Fintype.card Ω : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold finiteEventProbability finiteAverage
  push_cast [apply_ite]
  rw [hpow, div_eq_div_iff (pow_ne_zero _ hbase) hcard, Finset.sum_mul]
  simp_rw [hind]
  rw [Finset.sum_comm]
  simp only [hsum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ψ _
  rw [← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hbase)]

/-- Fourier inversion for membership in a submodule of a finite free module. -/
theorem sample_submodule_probability_fourier {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sample : Ω → ZMod q) :
    (finiteEventProbability (fun x : Fin n → Ω => (sample ∘ x) ∈ V) : ℂ) =
      (∑ ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ,
        ∏ i, (∑ b, ZMod.stdAddChar (quotientCharacterVector V ψ i * sample b)) /
          (Fintype.card Ω : ℂ)) / (Fintype.card ((Fin n → ZMod q) ⧸ V) : ℂ) := by
  simpa only [neg_zero, map_zero_eq_one, one_mul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] using sample_quotient_probability_fourier V sample 0

/-- Fourier inversion of the probability that a uniform binary column lies
in a submodule of a finite free module. -/
theorem binary_submodule_probability_fourier :
    (finiteEventProbability (fun x : Fin n → Bool => binaryColumn (ZMod q) x ∈ V) : ℂ) =
      (∑ ψ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ,
        ∏ i, bitFourierCoefficient (quotientCharacterVector V ψ i)) /
        (Fintype.card ((Fin n → ZMod q) ⧸ V) : ℂ) := by
  rw [show (fun x : Fin n → Bool => binaryColumn (ZMod q) x ∈ V) =
    (fun x => ((fun b : Bool => if b then (0 : ZMod q) else 1) ∘ x) ∈ V) from rfl,
    sample_submodule_probability_fourier]
  simp only [bitFourierCoefficient, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
    mul_one, mul_zero, map_zero_eq_one, Fintype.card_bool, Nat.cast_ofNat]

/-- A bound on every nonzero Fourier coefficient controls every binary
coset probability with the same absolute error. -/
theorem binary_quotient_probability_abs_sub_le
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcoeff : ∀ a : Fin n → ZMod q, a ≠ 0 → (∀ x ∈ V, a ⬝ᵥ x = 0) →
      (∏ i, ‖bitFourierCoefficient (a i)‖) ≤ ε)
    (y : (Fin n → ZMod q) ⧸ V) :
    |finiteEventProbability (fun x : Fin n → Bool => V.mkQ (binaryColumn (ZMod q) x) = y) -
        1 / (Nat.card ((Fin n → ZMod q) ⧸ V) : ℝ)| ≤ ε := by
  let Q := (Fin n → ZMod q) ⧸ V
  let P := finiteEventProbability (fun x : Fin n → Bool => V.mkQ (binaryColumn (ZMod q) x) = y)
  let f (ψ : AddChar Q ℂ) := ψ (-y) * ∏ i, bitFourierCoefficient (quotientCharacterVector V ψ i)
  let S := (Finset.univ : Finset (AddChar Q ℂ)).erase 0
  have hf0 : f 0 = 1 := by
    have hzero := (quotientCharacterVector_eq_zero_iff V 0).mpr rfl
    have hbit : bitFourierCoefficient (0 : ZMod q) = 1 := by norm_num [bitFourierCoefficient]
    simp [f, hzero, hbit]
  have hP : (P : ℂ) = (∑ ψ, f ψ) / (Fintype.card Q : ℂ) := by
    unfold P f
    rw [show (fun x : Fin n → Bool => V.mkQ (binaryColumn (ZMod q) x) = y) =
      (fun x => V.mkQ ((fun b : Bool => if b then (0 : ZMod q) else 1) ∘ x) = y) from rfl,
      sample_quotient_probability_fourier]
    simp only [bitFourierCoefficient, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
      mul_one, mul_zero, map_zero_eq_one, Fintype.card_bool, Nat.cast_ofNat]
    rfl
  have heq : ((P - 1 / (Fintype.card Q : ℝ) : ℝ) : ℂ) =
      (∑ ψ ∈ S, f ψ) / (Fintype.card Q : ℂ) := by
    push_cast
    rw [hP, ← Finset.sum_erase_add _ f (Finset.mem_univ 0), hf0, add_div, add_sub_cancel_right]
  have hnorm := congrArg norm heq
  rw [Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_natCast] at hnorm
  change |P - 1 / (Nat.card Q : ℝ)| ≤ ε
  rw [Nat.card_eq_fintype_card, hnorm]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Fintype.card_pos (α := Q)))).2
  calc
    _ ≤ ∑ ψ ∈ S, ‖f ψ‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ S, ε := by
      apply Finset.sum_le_sum
      intro ψ hψ
      have hne : quotientCharacterVector V ψ ≠ 0 := by
        intro hz
        exact (Finset.mem_erase.mp hψ).1 ((quotientCharacterVector_eq_zero_iff V ψ).mp hz)
      simp only [f, norm_mul, AddChar.norm_apply, one_mul, norm_prod]
      exact hcoeff _ hne (fun _ hx => quotientCharacterVector_orthogonal V ψ hx)
    _ = (S.card : ℝ) * ε := by simp
    _ ≤ ε * (Fintype.card Q : ℝ) := by
      rw [mul_comm ε]
      apply mul_le_mul_of_nonneg_right _ hε
      exact Nat.cast_le.mpr ((Finset.card_le_univ S).trans_eq AddChar.card_eq)

theorem quotientCharacterVector_add (ψ φ : AddChar ((Fin n → ZMod q) ⧸ V) ℂ) :
    quotientCharacterVector V (ψ + φ) = quotientCharacterVector V ψ + quotientCharacterVector V φ := by
  funext i
  apply ZMod.injective_stdAddChar
  simp only [Pi.add_apply, AddChar.map_add_eq_mul]
  rw [← dotProduct_single_one (quotientCharacterVector V (ψ + φ)) i, ← quotientCharacterVector_apply,
    AddChar.add_apply, quotientCharacterVector_apply, quotientCharacterVector_apply,
    dotProduct_single_one, dotProduct_single_one]

end BooleanThreshold
