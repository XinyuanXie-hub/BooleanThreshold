module

public import BooleanThreshold.CokernelComparison
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import BooleanThreshold.SpanNormalization

public noncomputable section

open scoped BigOperators Classical Function

namespace BooleanThreshold

theorem finiteEventProbability_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (e : Ω ≃ Γ)
    (P : Γ → Prop) :
    finiteEventProbability (fun x => P (e x)) = finiteEventProbability P := by
  unfold finiteEventProbability finiteAverage
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun x => rfl

/-- A simultaneous event under the uniform law on a finite product has
probability equal to the product of its coordinate probabilities. -/
theorem finiteEventProbability_pi {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] (P : ∀ i, Ω i → Prop) :
    finiteEventProbability (fun x : ∀ i, Ω i => ∀ i, P i (x i)) = ∏ i, finiteEventProbability (P i) := by
  unfold finiteEventProbability finiteAverage
  rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∀ i, P i (x i)
  · rw [ite_eq_left h]
    exact (Finset.prod_eq_one fun i _ => ite_eq_left (h i)).symm
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

/-- In the uniform reference matrix used in Lemma 8, determinant conditions
in distinct coprime factors of the modulus are independent. -/
theorem uniformCRT_det_zero_probability {I : Type*} [Fintype I] (q : I → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)] (hq : Pairwise (Nat.Coprime on q)) (n : ℕ) :
    finiteEventProbability (fun X : Fin n → Fin n → ZMod (∏ i, q i) =>
      ∀ i, ZMod.prodEquivPi q hq (Matrix.of X).det i = 0) =
      ∏ i, finiteEventProbability (fun X : Fin n → Fin n → ZMod (q i) => (Matrix.of X).det = 0) := by
  let crt := ZMod.prodEquivPi q hq
  let e : (Fin n → Fin n → ZMod (∏ i, q i)) ≃ (∀ i, Fin n → Fin n → ZMod (q i)) :=
    { toFun := fun X i j k => crt (X j k) i
      invFun := fun X j k => crt.symm (fun i => X i j k)
      left_inv := by intro X; funext j k; exact crt.symm_apply_apply _
      right_inv := by
        intro X
        funext i j k
        exact congrFun (crt.apply_symm_apply (fun i => X i j k)) i }
  have hdet (X : Fin n → Fin n → ZMod (∏ i, q i)) (i : I) :
      crt (Matrix.of X).det i = (Matrix.of (e X i)).det := by
    let h := (Pi.evalRingHom (fun j => ZMod (q j)) i).comp crt.toRingHom
    exact h.map_det (Matrix.of X)
  calc
    _ = finiteEventProbability (fun X => ∀ i, (Matrix.of (e X i)).det = 0) := by
      apply congrArg finiteEventProbability
      funext X
      apply propext
      constructor
      · intro h i
        exact (hdet X i).symm.trans (h i)
      · intro h i
        exact (hdet X i).trans (h i)
    _ = finiteEventProbability (fun X : ∀ i, Fin n → Fin n → ZMod (q i) =>
          ∀ i, (Matrix.of (X i)).det = 0) :=
      finiteEventProbability_equiv e (fun X => ∀ i, (Matrix.of (X i)).det = 0)
    _ = _ := finiteEventProbability_pi (fun i X => (Matrix.of X).det = 0)

/-- The binary determinant tail is bounded by the product of its uniform
prime-power reference tails plus the accumulated comparison error. -/
theorem binary_det_joint_le_uniform_reference {I : Type*} [Fintype I] (q : I → ℕ)
    [∀ i, NeZero (q i)] [NeZero (∏ i, q i)] (hq : Pairwise (Nat.Coprime on q)) (n : ℕ)
    {ε : ℝ}
    (hcompare : ∀ t : Finset I,
      |finiteEventProbability (fun X : Fin n → Fin n → Bool =>
        ∀ i ∈ t, ¬ q i ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) -
       finiteEventProbability (fun X : Fin n → Fin n → ZMod (∏ i, q i) =>
        ∀ i ∈ t, ZMod.prodEquivPi q hq (Matrix.of X).det i ≠ 0)| ≤ ε) :
    finiteEventProbability (fun X : Fin n → Fin n → Bool =>
      ∀ i, q i ∣ ((Matrix.of X).map zeroOneBit).det.natAbs) ≤
      (∏ i, finiteEventProbability (fun X : Fin n → Fin n → ZMod (q i) => (Matrix.of X).det = 0)) +
        (2 : ℝ) ^ Fintype.card I * ε := by
  let P (i : I) (X : Fin n → Fin n → Bool) :=
    q i ∣ ((Matrix.of X).map zeroOneBit).det.natAbs
  let Q (i : I) (X : Fin n → Fin n → ZMod (∏ i, q i)) :=
    ZMod.prodEquivPi q hq (Matrix.of X).det i = 0
  have h := finiteEventProbability_joint_abs_sub_le Finset.univ P Q (fun t _ => hcompare t)
  simp only [Finset.mem_univ, forall_const, Finset.card_univ] at h
  have hle : finiteEventProbability (fun X => ∀ i, P i X) -
      finiteEventProbability (fun X => ∀ i, Q i X) ≤ (2 : ℝ) ^ Fintype.card I * ε :=
    (le_abs_self _).trans h
  have hqprob : finiteEventProbability (fun X => ∀ i, Q i X) =
      ∏ i, finiteEventProbability (fun X : Fin n → Fin n → ZMod (q i) => (Matrix.of X).det = 0) :=
    uniformCRT_det_zero_probability q hq n
  rw [hqprob] at hle
  linarith only [hle]

end BooleanThreshold
