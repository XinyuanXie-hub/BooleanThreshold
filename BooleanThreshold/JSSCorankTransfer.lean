module

public import BooleanThreshold.SignSymmetry
public import BooleanThreshold.SignAtomSymmetry
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

private theorem uniformOn_univ_prod {X Y : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y] :
    (uniformOn (Set.univ : Set X)).prod (uniformOn (Set.univ : Set Y)) =
      uniformOn (Set.univ : Set (X × Y)) := by
  apply Measure.ext_of_singleton
  intro p
  calc
    _ = uniformOn Set.univ {p.1} * uniformOn Set.univ {p.2} := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    _ = _ := by
      simp only [uniformOn_univ, Measure.count_singleton, Fintype.card_prod, Nat.cast_mul, one_div]
      rw [ENNReal.mul_inv (by simp) (by simp)]

/-- A joint lower bound obtained by appending an independent row and then
applying independent column flips to the whole matrix. -/
theorem measure_append_and_flip_lower_bound {m d : ℕ}
    (E : Set (Fin m → Fin d → Bool)) (F : Set (Fin (m + 1) → Fin d → Bool))
    (rows masks : (Fin m → Fin d → Bool) → Set (Fin d → Bool))
    (q c : ℝ≥0∞)
    (hq : ∀ A ∈ E, q ≤ uniformOn Set.univ (rows A))
    (hc : ∀ A ∈ E, c ≤ uniformOn Set.univ (masks A))
    (hF : ∀ A ∈ E, ∀ b ∈ rows A, ∀ mask ∈ masks A,
      flipColumns mask (Fin.cons b A) ∈ F) :
    uniformOn Set.univ E * (q * c) ≤ uniformOn Set.univ F := by
  classical
  let B := Fin d → Bool
  let P := Fin m → B
  let Q := Fin (m + 1) → B
  let μ : Measure B := uniformOn Set.univ
  let ν : Measure P := uniformOn Set.univ
  let T : Set (P × (B × B)) := {x | x.1 ∈ E ∧ x.2.1 ∈ rows x.1 ∧ x.2.2 ∈ masks x.1}
  let e : (P × (B × B)) ≃ (B × Q) :=
    { toFun := fun x => (x.2.2, flipColumns x.2.2 (Fin.cons x.2.1 x.1))
      invFun := fun y =>
        let A := flipColumns y.1 y.2
        (Fin.tail A, (A 0, y.1))
      left_inv := fun x => by
        dsimp only
        rw [flipColumns_involutive x.2.2 (Fin.cons x.2.1 x.1)]
        simp
      right_inv := fun y => by
        dsimp only
        rw [Fin.cons_self_tail, flipColumns_involutive y.1 y.2] }
  have hT (x : P) (hx : x ∈ E) : Prod.mk x ⁻¹' T = rows x ×ˢ masks x := by
    ext y
    simp [T, hx]
  have hupper : uniformOn Set.univ (e ⁻¹' (Set.univ ×ˢ F)) = uniformOn Set.univ F := by
    rw [← Measure.map_apply (measurable_of_finite e) (Set.toFinite _).measurableSet,
      map_uniformOn_univ_of_equiv e, ← uniformOn_univ_prod, Measure.prod_prod,
      measure_univ, one_mul]
  calc
    uniformOn Set.univ E * (q * c) =
        ∫⁻ a, E.indicator (fun _ : P => q * c) a ∂ν := by
      rw [lintegral_indicator E.toFinite.measurableSet, lintegral_const,
        Measure.restrict_apply_univ, mul_comm]
    _ ≤ ∫⁻ a, (μ.prod μ) (Prod.mk a ⁻¹' T) ∂ν := by
      apply lintegral_mono
      intro a
      change E.indicator (fun _ : P => q * c) a ≤ (μ.prod μ) (Prod.mk a ⁻¹' T)
      by_cases ha : a ∈ E
      · rw [Set.indicator_of_mem ha, hT a ha, Measure.prod_prod]
        exact mul_le_mul' (hq a ha) (hc a ha)
      · rw [Set.indicator_of_notMem ha]
        exact zero_le
    _ = (ν.prod (μ.prod μ)) T := (Measure.prod_apply T.toFinite.measurableSet).symm
    _ = uniformOn Set.univ T := by rw [uniformOn_univ_prod, uniformOn_univ_prod]
    _ ≤ uniformOn Set.univ (e ⁻¹' (Set.univ ×ˢ F)) := by
      apply measure_mono
      rintro x ⟨hE, hb, hm⟩
      exact ⟨Set.mem_univ _, hF x.1 hE x.2.1 hb x.2.2 hm⟩
    _ = _ := hupper

/-- Unnormalized zero atom restricted to a prescribed set of sign rows. -/
noncomputable def windowAtom {d : ℕ} (a : Fin d → ℝ) (W : Set (Fin d → Bool)) : ℝ≥0∞ :=
  uniformOn Set.univ {b | (∑ i, a i * realSigns b i = 0) ∧ b ∈ W}

theorem windowAtom_le_zeroAtom {d : ℕ} (a : Fin d → ℝ) (W : Set (Fin d → Bool)) :
    windowAtom a W ≤ zeroAtom a := by
  rw [windowAtom, zeroAtom, uniformOn_signCube_apply]
  exact measure_mono fun _ h => h.1

private theorem integrate_windowAtom_flip {d : ℕ} (a : Fin d → ℝ) (W : Set (Fin d → Bool)) :
    (∫⁻ mask : Fin d → Bool, windowAtom (flipVector mask a) W ∂(uniformOn Set.univ)) =
      zeroAtom a * uniformOn Set.univ W := by
  classical
  let B := Fin d → Bool
  let μ : Measure B := uniformOn Set.univ
  let U : Set B := {x | ∑ i, a i * realSigns x i = 0}
  let T : Set (B × B) :=
    {p | (∑ i, flipVector p.1 a i * realSigns p.2 i = 0) ∧ p.2 ∈ W}
  have hsection (b : B) :
      μ ((fun mask : B => (mask, b)) ⁻¹' T) = W.indicator (fun _ : B => zeroAtom a) b := by
    by_cases hb : b ∈ W
    · let e : B ≃ B :=
        { toFun := fun mask i => b i ^^ mask i
          invFun := fun mask i => b i ^^ mask i
          left_inv := fun _ => funext fun i => by simp
          right_inv := fun _ => funext fun i => by simp }
      have hpre : (fun mask : B => (mask, b)) ⁻¹' T = e ⁻¹' U := by
        ext mask
        have hdot := dot_flipVector_realSigns_flipColumns mask
          (flipColumns mask (fun _ : Fin 1 => b)) a (0 : Fin 1)
        rw [flipColumns_involutive mask (fun _ : Fin 1 => b)] at hdot
        change ((∑ i, flipVector mask a i * realSigns b i = 0) ∧ b ∈ W) ↔
          (∑ i, a i * realSigns (e mask) i = 0)
        rw [hdot]
        simp [hb]
        rfl
      rw [hpre, ← Measure.map_apply (measurable_of_finite e) U.toFinite.measurableSet,
        map_uniformOn_univ_of_equiv e, Set.indicator_of_mem hb, zeroAtom, uniformOn_signCube_apply]
      rfl
    · have hempty : (fun mask : B => (mask, b)) ⁻¹' T = ∅ := by
        ext mask
        simp [T, hb]
      rw [hempty, measure_empty, Set.indicator_of_notMem hb]
  calc
    _ = (μ.prod μ) T := (Measure.prod_apply T.toFinite.measurableSet).symm
    _ = ∫⁻ b, μ ((fun mask : B => (mask, b)) ⁻¹' T) ∂μ :=
      Measure.prod_apply_symm T.toFinite.measurableSet
    _ = _ := by
      simp only [hsection]
      rw [lintegral_indicator_const W.toFinite.measurableSet]

/-- A fixed fraction of column orientations preserve a substantial restricted
atom and avoid the structured set, provided few orientations are structured. -/
theorem measure_good_atom_orientations {d : ℕ} (a : Fin d → ℝ) (S : Set (Fin d → ℝ))
    (W : Set (Fin d → Bool)) (hp : 0 < zeroAtom a)
    (hW : (1 / 2 : ℝ≥0∞) ≤ uniformOn Set.univ W)
    (hS : uniformOn Set.univ {mask : Fin d → Bool | flipVector mask a ∈ S} ≤ 1 / 8) :
    (1 / 8 : ℝ≥0∞) ≤ uniformOn Set.univ {mask : Fin d → Bool |
      flipVector mask a ∉ S ∧ zeroAtom a / 4 < windowAtom (flipVector mask a) W} := by
  classical
  let B := Fin d → Bool
  let μ : Measure B := uniformOn Set.univ
  let p := zeroAtom a
  let C : Set B := {mask | flipVector mask a ∈ S}
  let G : Set B := {mask | flipVector mask a ∉ S ∧ p / 4 < windowAtom (flipVector mask a) W}
  have hfin : p ≠ ∞ := measure_ne_top _ _
  have hbound (mask : B) : windowAtom (flipVector mask a) W ≤
      C.indicator (fun _ : B => p) mask + G.indicator (fun _ : B => p) mask + p / 4 := by
    have ha : windowAtom (flipVector mask a) W ≤ p :=
      (windowAtom_le_zeroAtom _ _).trans_eq (zeroAtom_flipVector mask a)
    by_cases hC : mask ∈ C
    · rw [Set.indicator_of_mem hC]
      exact ha.trans (le_self_add.trans le_self_add)
    · rw [Set.indicator_of_notMem hC, zero_add]
      by_cases hG : mask ∈ G
      · rw [Set.indicator_of_mem hG]
        exact ha.trans le_self_add
      · rw [Set.indicator_of_notMem hG, zero_add]
        exact le_of_not_gt fun h => hG ⟨hC, h⟩
  have hmean : p * (1 / 2) ≤ p * (1 / 8) + p * μ G + p / 4 := by
    calc
      _ ≤ p * μ W := mul_le_mul' (le_refl p) hW
      _ = ∫⁻ mask : B, windowAtom (flipVector mask a) W ∂μ := (integrate_windowAtom_flip a W).symm
      _ ≤ ∫⁻ mask, (C.indicator (fun _ : B => p) mask +
          G.indicator (fun _ : B => p) mask + p / 4) ∂μ := lintegral_mono hbound
      _ = p * μ C + p * μ G + p / 4 := by
        rw [lintegral_add_right _ measurable_const, lintegral_add_left (measurable_of_finite _),
          lintegral_indicator_const C.toFinite.measurableSet,
          lintegral_indicator_const G.toFinite.measurableSet, lintegral_const, measure_univ, mul_one]
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul' (le_refl p) hS) (le_refl _)) (le_refl _)
  have hdiv : p / 4 = p * (1 / 4 : ℝ≥0∞) := by rw [one_div, div_eq_mul_inv]
  rw [hdiv, ← mul_add, ← mul_add] at hmean
  have h' := (ENNReal.mul_le_mul_iff_right hp.ne' hfin).mp hmean
  change (1 / 8 : ℝ≥0∞) ≤ μ G
  apply ENNReal.le_of_add_le_add_left (a := 1 / 8 + 1 / 4) (by simp)
  have heq : (1 / 8 + 1 / 4 : ℝ≥0∞) + 1 / 8 = 1 / 2 := by
    apply le_antisymm
    · apply (ENNReal.toReal_le_toReal (by simp) (by simp)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_div]
    · apply (ENNReal.toReal_le_toReal (by simp) (by simp)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_div]
  rw [heq]
  simpa only [add_assoc, add_comm, add_left_comm] using h'

end BooleanThreshold
