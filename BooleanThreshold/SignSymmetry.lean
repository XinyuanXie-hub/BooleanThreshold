module

public import BooleanThreshold.SignMeasure
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- Flip the selected coordinates of every sign vector in a Boolean matrix. -/
def flipColumns {ι κ : Type*} (mask : κ → Bool) (v : ι → κ → Bool) : ι → κ → Bool :=
  fun i j => v i j ^^ mask j

theorem flipColumns_involutive {ι κ : Type*} (mask : κ → Bool) :
    Function.Involutive (flipColumns (ι := ι) mask) := by
  intro v
  funext i j
  simp [flipColumns]

/-- Flip the real coordinates selected by the mask. -/
def flipVector {κ : Type*} (mask : κ → Bool) (v : κ → ℝ) : κ → ℝ :=
  fun j => (if mask j then -1 else 1) * v j

theorem flipVector_involutive {κ : Type*} (mask : κ → Bool) :
    Function.Involutive (flipVector mask) := by
  intro v
  funext j
  cases hj : mask j <;> simp [flipVector, hj]

@[simp]
theorem flipVector_apply_ne_zero_iff {κ : Type*} (mask : κ → Bool) (v : κ → ℝ) (j : κ) :
    flipVector mask v j ≠ 0 ↔ v j ≠ 0 := by
  cases hj : mask j <;> simp [flipVector, hj]

theorem dot_flipVector_flipVector {κ : Type*} [Fintype κ] (mask : κ → Bool)
    (a v : κ → ℝ) :
    (∑ j, flipVector mask a j * flipVector mask v j) = ∑ j, a j * v j := by
  apply Finset.sum_congr rfl
  intro j _
  cases hj : mask j <;> simp [flipVector, hj]

theorem realSigns_flipColumns {n r : ℕ} (mask : Fin n → Bool) (v : Fin r → Fin n → Bool)
    (i : Fin r) (j : Fin n) :
    realSigns (flipColumns mask v i) j = (if mask j then -1 else 1) * realSigns (v i) j := by
  cases h₁ : v i j <;> cases h₂ : mask j <;> simp [realSigns, flipColumns, h₁, h₂]

theorem realSigns_flipColumns_eq {n r : ℕ} (mask : Fin n → Bool) (v : Fin r → Fin n → Bool)
    (i : Fin r) :
    realSigns (flipColumns mask v i) = flipVector mask (realSigns (v i)) :=
  funext <| realSigns_flipColumns mask v i

theorem dot_flipVector_realSigns_flipColumns {n r : ℕ} (mask : Fin n → Bool)
    (v : Fin r → Fin n → Bool) (a : Fin n → ℝ) (i : Fin r) :
    (∑ j, flipVector mask a j * realSigns (flipColumns mask v i) j) =
      ∑ j, a j * realSigns (v i) j := by
  rw [realSigns_flipColumns_eq, dot_flipVector_flipVector]

theorem linearIndependent_realSigns_flipColumns_iff {n r : ℕ} (mask : Fin n → Bool)
    (v : Fin r → Fin n → Bool) :
    LinearIndependent ℝ (fun i => realSigns (flipColumns mask v i)) ↔
      LinearIndependent ℝ (fun i => realSigns (v i)) := by
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := flipVector mask
      map_add' := fun a b => funext fun j => by simp [flipVector, mul_add]
      map_smul' := fun c a => funext fun j => by
        simp [flipVector, smul_eq_mul, mul_left_comm] }
  simp_rw [realSigns_flipColumns_eq]
  change LinearIndependent ℝ (f ∘ fun i => realSigns (v i)) ↔ _
  exact f.linearIndependent_iff_of_injOn (flipVector_involutive mask).injective.injOn

/-- Coordinated flips preserve uniform measure on the real sign cube. -/
theorem uniformOn_signCube_flipVector {n : ℕ} (mask : Fin n → Bool) (A : Set (Fin n → ℝ)) :
    uniformOn (signCube n) (flipVector mask ⁻¹' A) = uniformOn (signCube n) A := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun x j => x j ^^ mask j
      invFun := fun x j => x j ^^ mask j
      left_inv := fun x => funext fun j => by simp
      right_inv := fun x => funext fun j => by simp }
  have he (x : Fin n → Bool) : flipVector mask (realSigns x) = realSigns (e x) := by
    funext j
    exact (realSigns_flipColumns mask (fun _ : Fin 1 => x) 0 j).symm
  have hpre : realSigns ⁻¹' (flipVector mask ⁻¹' A) = e ⁻¹' (realSigns ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage, he]
  rw [uniformOn_signCube_apply, uniformOn_signCube_apply, hpre,
    ← Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    map_uniformOn_univ_of_equiv e]

theorem exists_null_row_flipColumns_iff {n r : ℕ} (mask : Fin n → Bool)
    (v : Fin r → Fin n → Bool) (A : Set (Fin n → ℝ))
    (hA : ∀ a, flipVector mask a ∈ A ↔ a ∈ A) :
    (∃ a ∈ A, ∀ i, ∑ j, a j * realSigns (flipColumns mask v i) j = 0) ↔
      (∃ a ∈ A, ∀ i, ∑ j, a j * realSigns (v i) j = 0) := by
  constructor
  · rintro ⟨a, ha, hnull⟩
    refine ⟨flipVector mask a, (hA a).2 ha, fun i => ?_⟩
    calc
      _ = ∑ j, a j * realSigns (flipColumns mask v i) j := by
        simpa only [flipVector_involutive mask a] using
          (dot_flipVector_realSigns_flipColumns mask v (flipVector mask a) i).symm
      _ = 0 := hnull i
  · rintro ⟨a, ha, hnull⟩
    refine ⟨flipVector mask a, (hA a).2 ha, fun i => ?_⟩
    rw [dot_flipVector_realSigns_flipColumns]
    exact hnull i

private def normalizeAt {ι κ : Type*} (i : ι) :
    (ι → κ → Bool) ≃ {v : ι → κ → Bool // v i = fun _ => false} × (κ → Bool) where
  toFun v := (⟨flipColumns (v i) v, funext fun j => by simp [flipColumns]⟩, v i)
  invFun p := flipColumns p.2 p.1.val
  left_inv v := flipColumns_involutive (v i) v
  right_inv p := by
    have hrow : flipColumns p.2 p.1.val i = p.2 := by
      funext j
      change (p.1.val i j ^^ p.2 j) = p.2 j
      rw [p.1.prop, Bool.false_xor]
    apply Prod.ext
    · apply Subtype.ext
      change flipColumns (flipColumns p.2 p.1.val i) (flipColumns p.2 p.1.val) = p.1.val
      rw [hrow, flipColumns_involutive]
    · exact hrow

/-- Under the uniform matrix law, an event invariant under coordinated sign
flips is independent of membership of a selected row in any set. -/
theorem uniformOn_real_inter_row_of_flipInvariant {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Set (ι → κ → Bool)) (hA : ∀ mask v, flipColumns mask v ∈ A ↔ v ∈ A)
    (i : ι) (W : Set (κ → Bool)) :
    (uniformOn Set.univ).real (A ∩ {v | v i ∈ W}) =
      (uniformOn Set.univ).real A * (uniformOn Set.univ).real W := by
  classical
  let e := normalizeAt (κ := κ) i
  let B : Set {v : ι → κ → Bool // v i = fun _ => false} := {v | v.val ∈ A}
  have hpre (U : Set (κ → Bool)) : e ⁻¹' (B ×ˢ U) = A ∩ {v | v i ∈ U} := by
    ext v
    exact and_congr (hA (v i) v) Iff.rfl
  have hApre : e ⁻¹' (B ×ˢ Set.univ) = A := by simpa using hpre Set.univ
  have hcard (U : Set (κ → Bool)) : (e ⁻¹' (B ×ˢ U)).ncard = B.ncard * U.ncard := by
    rw [Set.ncard_preimage_of_injective_subset_range e.injective, Set.ncard_prod]
    simp [e.surjective.range_eq]
  have hsize : Fintype.card (ι → κ → Bool) =
      Fintype.card {v : ι → κ → Bool // v i = fun _ => false} * Fintype.card (κ → Bool) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [← hpre W, ← hApre]
  simp only [uniformOn_univ_real_eq_card, hcard, hsize, Set.ncard_univ, Nat.card_eq_fintype_card,
    Nat.cast_mul, mul_div_mul_comm]
  have hrow : (Fintype.card (κ → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (κ → Bool) ≠ 0)
  rw [div_self hrow, mul_one]

end BooleanThreshold
