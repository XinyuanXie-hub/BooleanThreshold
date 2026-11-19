module

public import BooleanThreshold.KKSLargeCertificate
public import BooleanThreshold.KKSLargeProjection
public import BooleanThreshold.NonPairSign
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Nat.Choose.Bounds

public section

open Finset MeasureTheory ProbabilityTheory Module Submodule
open scoped ENNReal BigOperators

namespace BooleanThreshold

/-- Probability of annihilating `a` with a row whose independent coordinates have law `ν`. -/
@[expose] noncomputable def auxiliaryAtom {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (ν : Measure Ω) (z : Ω → ℝ) (a : Fin n → ℝ) : ℝ≥0∞ := by
  classical
  exact Measure.pi (fun _ : Fin n => ν) {x | ∑ i, a i * z (x i) = 0}

private theorem dotProductBilin_injective (n : ℕ) :
    Function.Injective (dotProductBilin ℝ ℝ : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin n → ℝ)) := by
  intro x y h
  exact dotProduct_eq _ _ fun u => congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) => f u) h

private theorem uniform_fixed_atom_null_le
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    {n d : ℕ} (hd : d < n) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (z : Ω ↪ ℝ) {b τ p : ℝ≥0∞} (hb : b ≤ 1) (hb' : ∀ x : Ω, ν {x} ≤ b)
    (hτ₀ : τ ≠ 0) (hτTop : τ ≠ ⊤) (hp₀ : p ≠ 0) (hpTop : p ≠ ⊤)
    (eval : Fin n → (Fin n → Bool) → Module.Dual ℝ (Fin n → ℝ))
    (S : Set (Fin n → ℝ)) (hS : ∀ a ∈ S, a ≠ 0)
    (hp : ∀ i a, a ∈ S → uniformOn Set.univ {x | eval i x a = 0} ≤ p)
    (hcompare : ∀ a ∈ S, p ≤ τ * auxiliaryAtom ν z a)
    (hproj : b ^ (n - d) ≤ p / (2 * τ)) :
    uniformOn Set.univ {r : Fin n → Fin n → Bool | ∃ a ∈ S, ∀ j, eval j (r j) a = 0} ≤
      (n.choose (n - d - 1) : ℝ≥0∞) * (2 * τ) ^ d * p := by
  classical
  let νn := Measure.pi (fun _ : Fin n => ν)
  let μ : Measure (Fin n → Bool) := uniformOn Set.univ
  let Z (x : Fin n → Ω) (i : Fin n) := z (x i)
  let aux (row : Fin n → Ω) : Module.Dual ℝ (Fin n → ℝ) :=
    dotProductBilin ℝ ℝ (Z row)
  let s := p / (2 * τ)
  have hsτ₀ : 2 * τ ≠ 0 := mul_ne_zero (by simp) hτ₀
  have hsτTop : 2 * τ ≠ ⊤ := ENNReal.mul_ne_top (by simp) hτTop
  have haux (r : Fin n → Ω) (a : Fin n → ℝ) :
      aux r a = ∑ i, a i * z (r i) := by simp [aux, Z, dotProduct, mul_comm]
  have hcert (a : Fin n → ℝ) (ha : a ∈ S) :
      s ^ d ≤ Measure.pi (fun _ : Fin d => νn)
        {w | LinearIndependent ℝ (aux ∘ w) ∧ ∀ j, aux (w j) a = 0} := by
    let A : Set (Fin n → Ω) := {r | ∑ i, a i * z (r i) = 0}
    have hA : p ≤ τ * νn A := hcompare a ha
    have hmass : s + s ≤ νn A := by
      rw [← two_mul, mul_comm, ← ENNReal.mul_div_right_comm]
      change p * 2 / (2 * τ) ≤ _
      rw [mul_comm (2 : ℝ≥0∞) τ, ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]
      exact (ENNReal.div_le_iff hτ₀ hτTop).mpr (by rwa [mul_comm])
    have hstep (W : Submodule ℝ (Fin n → ℝ)) (hW : finrank ℝ W < d) :
        s ≤ νn (A \ {x | Z x ∈ W}) := by
      have hμW : νn {x | Z x ∈ W} ≤ s :=
        (product_mass_submodule_le ν z b hb' W).trans <|
        (pow_le_pow_of_le_one zero_le hb (by omega)).trans hproj
      have hle : νn {x | Z x ∈ W} + s ≤ νn A := (add_le_add hμW le_rfl).trans hmass
      have hsub : s ≤ νn A - νn {x | Z x ∈ W} :=
        (ENNReal.le_sub_iff_add_le_left (measure_ne_top _ _) (le_self_add.trans hle)).mpr hle
      exact hsub.trans le_measure_sdiff
    refine (independent_samples_probability_lower νn Z A d s hstep).trans <| measure_mono ?_
    rintro w ⟨hli, ha⟩
    refine ⟨?_, fun j => ?_⟩
    · exact hli.map' _ (LinearMap.ker_eq_bot.mpr (dotProductBilin_injective n))
    · rw [haux]
      exact ha j
  have h := common_null_mul_certificate_rowwise_le μ νn eval aux S hS hp
    (m := n) (d := d) (p := p) (lower := s ^ d)
    (by simpa [Module.finrank_fintype_fun_eq_card] using
      (show n - d - 1 ≤ n from by omega)) hcert
  rw [show Measure.pi (fun _ : Fin n => μ) = uniformOn Set.univ from pi_uniformOn_univ] at h
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  have hpow : n - (n - d - 1) = d + 1 := by omega
  rw [hpow] at h
  have hs₀ : s ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hp₀, hsτTop⟩
  have hsTop : s ≠ ⊤ := ENNReal.div_ne_top hpTop hsτ₀
  apply (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ hs₀) (ENNReal.pow_ne_top hsTop)).mp
  calc
    _ ≤ (n.choose (n - d - 1) : ℝ≥0∞) * p ^ (d + 1) := h
    _ = s ^ d * ((n.choose (n - d - 1) : ℝ≥0∞) * (2 * τ) ^ d * p) := by
      symm
      calc
        _ = (s ^ d * (2 * τ) ^ d) * p * (n.choose (n - d - 1) : ℝ≥0∞) := by ac_rfl
        _ = _ := by rw [← mul_pow, ENNReal.div_mul_cancel hsτ₀ hsτTop, ← pow_succ, mul_comm]

private theorem zeroAtom_eq_card_ratio (n : ℕ) (a : Fin n → ℝ) :
    ∃ j : ℕ, j ≤ 2 ^ n ∧ zeroAtom a = (j : ℝ≥0∞) / 2 ^ n := by
  let E : Set (Fin n → Bool) := {row | ∑ i, a i * realSigns row i = 0}
  refine ⟨E.ncard, ?_, ?_⟩
  · have h : E.ncard ≤ (Set.univ : Set (Fin n → Bool)).ncard := Set.ncard_le_ncard (by simp)
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h
  · rw [zeroAtom, uniformOn_signCube_apply]
    change uniformOn Set.univ E = _
    rw [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite E), ← Set.ncard_eq_toFinset_card]
    simp

/-- Sum the random-certificate estimate over the possible values of the ordinary sign atom. -/
theorem uniform_null_set_le_of_auxiliary_atom_comparison
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    {n d : ℕ} (hd : d < n) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (z : Ω ↪ ℝ) {b τ cutoff : ℝ≥0∞} (hb : b ≤ 1) (hb' : ∀ x : Ω, ν {x} ≤ b)
    (hτ₀ : τ ≠ 0) (hτTop : τ ≠ ⊤)
    (eval : Fin n → (Fin n → Bool) → Module.Dual ℝ (Fin n → ℝ))
    (S : Set (Fin n → ℝ)) (hS : ∀ a ∈ S, a ≠ 0) (atom : (Fin n → ℝ) → ℝ≥0∞)
    (hatom : ∀ a ∈ S, ∃ j : ℕ, j ≤ 2 ^ n ∧ atom a = (j : ℝ≥0∞) / 2 ^ n)
    (heval : ∀ i a, a ∈ S → uniformOn Set.univ {x | eval i x a = 0} ≤ atom a)
    (hcut : ∀ a ∈ S, cutoff < atom a)
    (hcompare : ∀ a ∈ S, atom a ≤ τ * auxiliaryAtom ν z a)
    (hproj : b ^ (n - d) ≤ cutoff / (2 * τ)) :
    uniformOn Set.univ {r : Fin n → Fin n → Bool | ∃ a ∈ S, ∀ j, eval j (r j) a = 0} ≤
      (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ n * (2 * τ) ^ d := by
  classical
  let I : Finset ℕ := Icc 1 (2 ^ n)
  let p (j : ℕ) : ℝ≥0∞ := (j : ℝ≥0∞) / 2 ^ n
  let S' (j : ℕ) : Set (Fin n → ℝ) := {a ∈ S | atom a = p j}
  let E (j : ℕ) : Set (Fin n → Fin n → Bool) := {v | ∃ a ∈ S' j, ∀ k, eval k (v k) a = 0}
  have hsub : {v : Fin n → Fin n → Bool | ∃ a ∈ S, ∀ k, eval k (v k) a = 0} ⊆
      ⋃ j ∈ I, E j := by
    rintro v ⟨a, ha, hnull⟩
    obtain ⟨j, hj, hjp⟩ := hatom a ha
    have hj₀ : j ≠ 0 := by
      intro h
      have h' := hcut a ha
      rw [hjp, h] at h'
      simp at h'
    exact Set.mem_iUnion₂.mpr ⟨j, mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj₀, hj⟩,
      a, ⟨ha, hjp⟩, hnull⟩
  have hbound (j : ℕ) (hj : j ∈ I) :
      uniformOn Set.univ (E j) ≤ (2 : ℝ≥0∞) ^ n * (2 * τ) ^ d := by
    by_cases hS' : (S' j).Nonempty
    · obtain ⟨a, ha⟩ := hS'
      have hpc : cutoff ≤ p j := (hcut a ha.1).le.trans_eq ha.2
      have hp₀ : p j ≠ 0 := by
        rw [← ha.2]
        exact (zero_le.trans_lt (hcut a ha.1)).ne'
      have hpTop : p j ≠ ⊤ := ENNReal.div_ne_top (by simp) (by simp)
      have hp₁ : p j ≤ 1 := by
        apply (ENNReal.div_le_iff (by simp : (2 : ℝ≥0∞) ^ n ≠ 0)
          (by simp : (2 : ℝ≥0∞) ^ n ≠ ⊤)).mpr
        rw [one_mul]
        exact_mod_cast (mem_Icc.mp hj).2
      have hh := uniform_fixed_atom_null_le hd ν z hb hb' hτ₀ hτTop hp₀ hpTop eval (S' j)
        (fun a ha => hS a ha.1) (fun i a ha => (heval i a ha.1).trans_eq ha.2)
        (fun a ha => ha.2 ▸ hcompare a ha.1)
        (hproj.trans (ENNReal.div_le_div_right hpc _))
      refine hh.trans ?_
      have hc : (n.choose (n - d - 1) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
        exact_mod_cast Nat.choose_le_two_pow n (n - d - 1)
      calc
        _ ≤ ((2 : ℝ≥0∞) ^ n * (2 * τ) ^ d) * 1 :=
          mul_le_mul' (mul_le_mul' hc le_rfl) hp₁
        _ = _ := mul_one _
    · have hE : E j = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨a, ha, _⟩ => hS' ⟨a, ha⟩
      simp [hE]
  calc
    _ ≤ uniformOn Set.univ (⋃ j ∈ I, E j) := measure_mono hsub
    _ ≤ ∑ j ∈ I, uniformOn Set.univ (E j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ I, (2 : ℝ≥0∞) ^ n * (2 * τ) ^ d := sum_le_sum hbound
    _ = _ := by simp [I, Nat.card_Icc, mul_assoc]

/-- Apply the atom comparison to a square matrix of ordinary signs. -/
theorem signLaw_null_set_le_of_auxiliary_atom_comparison
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    {n d : ℕ} (hd : d < n) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (z : Ω ↪ ℝ) {b τ cutoff : ℝ≥0∞} (hb : b ≤ 1) (hb' : ∀ x : Ω, ν {x} ≤ b)
    (hτ₀ : τ ≠ 0) (hτTop : τ ≠ ⊤)
    (S : Set (Fin n → ℝ)) (hS : ∀ a ∈ S, a ≠ 0) (hcut : ∀ a ∈ S, cutoff < zeroAtom a)
    (hcompare : ∀ a ∈ S, zeroAtom a ≤ τ * auxiliaryAtom ν z a)
    (hproj : b ^ (n - d) ≤ cutoff / (2 * τ)) :
    signLaw n n {v | ∃ a ∈ S, ∀ j, ∑ i, a i * v i j = 0} ≤
      (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ n * (2 * τ) ^ d := by
  let eval (row : Fin n → Bool) : Module.Dual ℝ (Fin n → ℝ) :=
    dotProductBilin ℝ ℝ (realSigns row)
  have hev (r : Fin n → Bool) (a : Fin n → ℝ) :
      eval r a = ∑ i, a i * realSigns r i := by simp [eval, dotProduct, mul_comm]
  have hμ (a : Fin n → ℝ) : uniformOn Set.univ {r | eval r a = 0} ≤ zeroAtom a := by
    rw [zeroAtom, uniformOn_signCube_apply]
    simp [hev]
  let E : Set (Fin n → Fin n → ℝ) := {v | ∃ a ∈ S, ∀ j, ∑ i, a i * v j i = 0}
  change signLaw n n ((fun v j i => v i j) ⁻¹' E) ≤ _
  rw [signLaw_transpose, signLaw_apply]
  simp only [E, Set.preimage_ofPred_eq, ← hev]
  exact uniform_null_set_le_of_auxiliary_atom_comparison hd ν z hb hb' hτ₀ hτTop
    (fun _ => eval) S hS zeroAtom (fun a _ => zeroAtom_eq_card_ratio n a) (fun _ a _ => hμ a)
    hcut hcompare hproj

end BooleanThreshold
