module

public import BooleanThreshold.JSSConditionalIntervalCover
public import BooleanThreshold.JSSConditionalSliceAverage
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace BooleanThreshold

/-- Apply a two-block smoothing count to one list of shifts whose coordinate
intervals have bounded width. -/
theorem card_filter_shift_smoothing_le_of_two_interval_grids {P d d₁ d₂ N W : ℕ}
    (hN : 0 < N) (hd : d₂ + d₁ = d) (B : Fin d → Finset ℤ)
    (hB : ∀ i, ∃ l u : ℤ, B i = Ico l u ∧ (B i).card ≤ W * N)
    (f : ZMod P → ℂ) (a : ℝ) {C : ℝ}
    (h : ∀ s₁ : Fin d₁ → ℤ, ∀ s₂ : Fin d₂ → ℤ,
      let A₁ := Fintype.piFinset (fun i => Ico (s₁ i) (s₁ i + (N : ℤ)))
      let A₂ := Fintype.piFinset (fun i => Ico (s₂ i) (s₂ i + (N : ℤ)))
      (((A₁.product A₂).filter (fun y => ∃ t, a ≤
        (cyclicShiftSmoothing (cyclicShiftSmoothing f y.1) y.2 t).re)).card : ℝ) ≤
          C * (N : ℝ) ^ (d₁ + d₂)) :
    (((Fintype.piFinset B).filter (fun y => ∃ t, a ≤ (cyclicShiftSmoothing f y t).re)).card : ℝ) ≤
      C * ((W : ℝ) * (N : ℝ)) ^ d := by
  subst d
  let B₁ (i : Fin d₁) := B (i.natAdd d₂)
  let B₂ (i : Fin d₂) := B (i.castAdd d₁)
  let A₁ := Fintype.piFinset B₁
  let A₂ := Fintype.piFinset B₂
  let e : ((Fin d₁ → ℤ) × (Fin d₂ → ℤ)) ≃ (Fin (d₂ + d₁) → ℤ) :=
    Equiv.prodComm _ _ |>.trans (Fin.appendEquiv _ _)
  have he (z : (Fin d₁ → ℤ) × (Fin d₂ → ℤ)) : e z = Fin.append z.2 z.1 := rfl
  let P₁ (z : (Fin d₁ → ℤ) × (Fin d₂ → ℤ)) :=
    ∃ t, a ≤ (cyclicShiftSmoothing (cyclicShiftSmoothing f z.1) z.2 t).re
  let P₂ (z : Fin (d₂ + d₁) → ℤ) := ∃ t, a ≤ (cyclicShiftSmoothing f z t).re
  have hGridPoint (z : (Fin d₁ → ℤ) × (Fin d₂ → ℤ)) :
      z ∈ A₁.product A₂ ↔ e z ∈ Fintype.piFinset B := by
    simp only [A₁, A₂, product_eq_sprod, mem_product, Fintype.mem_piFinset]
    refine ⟨fun hz i => ?_, fun hz => ⟨fun i => ?_, fun i => ?_⟩⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [he, Fin.append_left, B₂] using hz.2 j
      · simpa only [he, Fin.append_right, B₁] using hz.1 j
    · simpa only [he, Fin.append_right, B₁] using hz (i.natAdd d₂)
    · simpa only [he, Fin.append_left, B₂] using hz (i.castAdd d₁)
  have hGrid : (A₁.product A₂).map e.toEmbedding = Fintype.piFinset B := by
    ext z
    rw [mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hGridPoint x).mp hx
    · intro hz
      refine ⟨e.symm z, (hGridPoint _).mpr ?_, e.apply_symm_apply z⟩
      rwa [e.apply_symm_apply]
  have hP (z : (Fin d₁ → ℤ) × (Fin d₂ → ℤ)) : P₁ z ↔ P₂ (e z) := by
    simp only [P₁, P₂, he, cyclicShiftSmoothing_append]
  have hMap : ((A₁.product A₂).filter P₁).map e.toEmbedding = (Fintype.piFinset B).filter P₂ := by
    rw [Finset.map_filter, hGrid]
    congr 1
    funext z
    apply propext
    simpa only [Function.comp_apply, e.apply_symm_apply] using hP (e.symm z)
  have hh := card_filter_two_grids_le_of_interval_cover hN B₁ B₂
    (fun i => hB (i.natAdd d₂)) (fun i => hB (i.castAdd d₁)) P₁ h
  change (((Fintype.piFinset B).filter P₂).card : ℝ) ≤ _
  rw [← hMap, card_map, Nat.add_comm d₂ d₁]
  exact hh

/-- The real subset average has the same mixed-pair smoothing representation. -/
theorem sliceAverage_eq_integral_pair_smoothing_re {P n k : ℕ}
    (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)) (a : Fin n → ℤ)
    (g : ZMod P → ℝ) (t : ZMod P) :
    sliceAverage (fun i => if hi : i < n then (a ⟨i, hi⟩ : ZMod P) else 0) g n m.val t =
      ∫ b : Fin n → Bool,
        (cyclicShiftSmoothing (fun u => (g u : ℂ))
          (fun i => pairedSubsetShift e a b (mixedPairEmbedding e b i))
          (t + (selectedCoordinateSum a b : ℤ))).re ∂(uniformOn (signSlice n m)) := by
  let μ := uniformOn (signSlice n m)
  have hchoose (b : Fin n → Bool) :
      (∑ i ∈ univ.filter fun i => b i, (a i : ZMod P)) = (selectedCoordinateSum a b : ℤ) := by
    rw [selectedCoordinateSum, Int.cast_sum, sum_filter]
    apply sum_congr rfl
    intro i _
    cases b i <;> simp
  rw [← integral_signSlice_eq_sliceAverage]
  simp only [Fin.isLt, dite_eq_left, Fin.eta, hchoose]
  let F (b : Fin n → Bool) : ℂ := g (t + (selectedCoordinateSum a b : ℤ))
  let G (b : Fin n → Bool) : ℂ :=
    cyclicShiftSmoothing (fun u => (g u : ℂ)) (fun i => pairedSubsetShift e a b (mixedPairEmbedding e b i))
      (t + (selectedCoordinateSum a b : ℤ))
  have h₁ : Integrable F μ := integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  have h₂ : Integrable G μ := integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  have hEq : (∫ b, F b ∂μ) = ∫ b, G b ∂μ := integral_signSlice_subsetSum_eq_pair_smoothing e m a
    (fun u => (g u : ℂ)) t
  change (∫ b, RCLike.re (F b) ∂μ) = ∫ b, RCLike.re (G b) ∂μ
  rw [integral_re h₁, integral_re h₂, hEq]

end BooleanThreshold
