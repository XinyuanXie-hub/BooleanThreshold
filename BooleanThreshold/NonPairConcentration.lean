module

public import BooleanThreshold.SignSymmetry
public import Mathlib.Tactic.Linarith

public section

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- Conditional anti-concentration on a window controls an invariant event.
The comparison only has to hold away from the exceptional and structured
parts of the sample determined by the first coordinate. -/
theorem probability_le_exceptional_structured
    {A B : Type*} [Finite A] [Finite B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (event : Set (A × B)) (exceptional structured : Set A) (window : Set B)
    {θ : ℝ≥0∞} (hθ : θ ≤ 1 / 2) (hW : 1 / 2 ≤ ν window)
    (hinv : (μ.prod ν) (event ∩ Prod.snd ⁻¹' window) = ν window * (μ.prod ν) event)
    (hcomp : ∀ a ∉ exceptional, a ∉ structured →
      ν ((Prod.mk a ⁻¹' event) ∩ window) ≤ θ * ν window * ν (Prod.mk a ⁻¹' event)) :
    (μ.prod ν).real event ≤
      2 * μ.real exceptional + 4 * (μ.prod ν).real (event ∩ Prod.fst ⁻¹' structured) := by
  let selected := event ∩ Prod.snd ⁻¹' window
  let structuredEvent := event ∩ Prod.fst ⁻¹' structured
  let remaining : Set (A × B) :=
    {x | x ∈ selected ∧ x.1 ∉ exceptional ∧ x.1 ∉ structured}
  have hcover : selected ⊆ ((exceptional ×ˢ window) ∪ structuredEvent) ∪ remaining := by
    intro x hx
    by_cases hs : x.1 ∈ structured
    · exact Or.inl (Or.inr ⟨hx.1, hs⟩)
    by_cases hb : x.1 ∈ exceptional
    · exact Or.inl (Or.inl ⟨hb, hx.2⟩)
    · exact Or.inr ⟨hx, hb, hs⟩
  have hremain : (μ.prod ν) remaining ≤ θ * ν window * (μ.prod ν) event := by
    rw [Measure.prod_apply remaining.toFinite.measurableSet,
      Measure.prod_apply event.toFinite.measurableSet,
      ← lintegral_const_mul _ (measurable_of_finite _)]
    apply lintegral_mono
    intro a
    by_cases hb : a ∈ exceptional
    · simp [remaining, hb]
    by_cases hs : a ∈ structured
    · simp [remaining, hs]
    exact (measure_mono (fun _ hx => hx.1)).trans (hcomp a hb hs)
  have hraw : ν window * (μ.prod ν) event ≤
      μ exceptional * ν window + (μ.prod ν) structuredEvent +
        θ * ν window * (μ.prod ν) event := by
    rw [← hinv]
    calc
      _ ≤ (μ.prod ν) (((exceptional ×ˢ window) ∪ structuredEvent) ∪ remaining) :=
        measure_mono hcover
      _ ≤ (μ.prod ν) ((exceptional ×ˢ window) ∪ structuredEvent) + (μ.prod ν) remaining :=
        measure_union_le _ _
      _ ≤ ((μ.prod ν) (exceptional ×ˢ window) + (μ.prod ν) structuredEvent) +
            θ * ν window * (μ.prod ν) event := add_le_add (measure_union_le _ _) hremain
      _ = _ := by rw [Measure.prod_prod]
  have hhalf : (1 / 2 : ℝ≥0∞) ≠ ∞ := by simp
  have hθfin := ne_top_of_le_ne_top hhalf hθ
  have hterm₁ : μ exceptional * ν window ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hterm₂ : θ * ν window * (μ.prod ν) event ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hθfin (measure_ne_top _ _)) (measure_ne_top _ _)
  have hsum : μ exceptional * ν window + (μ.prod ν) structuredEvent +
      θ * ν window * (μ.prod ν) event ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hterm₁, measure_ne_top _ _⟩, hterm₂⟩
  have hreal := ENNReal.toReal_mono hsum hraw
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hterm₁, measure_ne_top _ _⟩) hterm₂,
    ENNReal.toReal_add hterm₁ (measure_ne_top _ _)] at hreal
  simp only [ENNReal.toReal_mul, ← measureReal_def] at hreal
  have hθreal : θ.toReal ≤ 1 / 2 := by
    simpa [ENNReal.toReal_div] using ENNReal.toReal_mono hhalf hθ
  have hWreal : (1 / 2 : ℝ) ≤ ν.real window := by
    simpa [ENNReal.toReal_div, measureReal_def] using ENNReal.toReal_mono (measure_ne_top _ _) hW
  have hw_nonneg : 0 ≤ ν.real window := ENNReal.toReal_nonneg
  have hp_nonneg : 0 ≤ (μ.prod ν).real event := ENNReal.toReal_nonneg
  have hs_nonneg : 0 ≤ (μ.prod ν).real structuredEvent := ENNReal.toReal_nonneg
  have hcost := mul_le_mul_of_nonneg_right hθreal (mul_nonneg hw_nonneg hp_nonneg)
  have hstruct := mul_le_mul_of_nonneg_right hWreal hs_nonneg
  have hmul : ν.real window * (μ.prod ν).real event ≤
      ν.real window * (2 * μ.real exceptional + 4 * (μ.prod ν).real structuredEvent) := by
    nlinarith only [hreal, hcost, hstruct]
  exact le_of_mul_le_mul_left hmul (by linarith only [hWreal])

/-- Apply the conditional comparison to a finite sign matrix whose event is invariant
under changing the signs of entire columns. -/
theorem uniform_probability_le_exceptional_structured {n r : ℕ} (i : Fin (n + 1))
    (event : Set (Fin (n + 1) → Fin r → Bool))
    (exceptional structured : Set (Fin n → Fin r → Bool)) (window : Set (Fin r → Bool))
    {θ : ℝ≥0∞} (hθ : θ ≤ 1 / 2) (hW : 1 / 2 ≤ uniformOn Set.univ window)
    (hinv : ∀ mask v, flipColumns mask v ∈ event ↔ v ∈ event)
    (hcomp : ∀ a ∉ exceptional, a ∉ structured →
      uniformOn Set.univ {b | Fin.insertNth i b a ∈ event ∧ b ∈ window} ≤
        θ * uniformOn Set.univ window * uniformOn Set.univ {b | Fin.insertNth i b a ∈ event}) :
    (uniformOn Set.univ).real event ≤ 2 * (uniformOn Set.univ).real exceptional +
      4 * (uniformOn Set.univ).real (event ∩ {v | Fin.removeNth i v ∈ structured}) := by
  let μ : Measure (Fin n → Fin r → Bool) := uniformOn Set.univ
  let ν : Measure (Fin r → Bool) := uniformOn Set.univ
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin r → Bool) i).trans
    MeasurableEquiv.prodComm
  have hpres : MeasurePreserving e (uniformOn Set.univ) (μ.prod ν) := by
    have h := (Measure.measurePreserving_swap (μ := ν) (ν := Measure.pi (fun _ : Fin n => ν))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i)
    change MeasurePreserving (Prod.swap ∘ ⇑(MeasurableEquiv.piFinSuccAbove _ i)) _ _
    simpa only [pi_uniformOn_univ, μ, ν] using h
  have hmap (S : Set (Fin (n + 1) → Fin r → Bool)) :
      (μ.prod ν) (e.symm ⁻¹' S) = uniformOn Set.univ S :=
    (hpres.symm e).measure_preimage_equiv S
  have hassemble (a : (Fin n → Fin r → Bool) × (Fin r → Bool)) :
      e.symm a = Fin.insertNth i a.2 a.1 := rfl
  let pre := e.symm ⁻¹' event
  have hrow : pre ∩ Prod.snd ⁻¹' window = e.symm ⁻¹' (event ∩ {v | v i ∈ window}) := by
    ext a
    simp [pre, hassemble, Fin.insertNth_apply_same]
  have hstructured : pre ∩ Prod.fst ⁻¹' structured =
      e.symm ⁻¹' (event ∩ {v | Fin.removeNth i v ∈ structured}) := by
    ext a
    simp [pre, hassemble]
  have hindep : (μ.prod ν) (pre ∩ Prod.snd ⁻¹' window) = ν window * (μ.prod ν) pre := by
    rw [hrow, hmap, show (μ.prod ν) pre = _ from hmap event]
    have h := uniformOn_real_inter_row_of_flipInvariant event hinv i window
    simp only [measureReal_def, ← ENNReal.toReal_mul] at h
    have hfin : (uniformOn Set.univ event * ν window) ≠ ∞ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
    have hh := congrArg ENNReal.ofReal h
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal hfin] at hh
    exact hh.trans (mul_comm _ _)
  have h := probability_le_exceptional_structured μ ν pre exceptional structured window
    hθ hW hindep (fun a ha hs => hcomp a ha hs)
  simpa only [measureReal_def, hstructured, hmap, μ, pre] using h

end BooleanThreshold
