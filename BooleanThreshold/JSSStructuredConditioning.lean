module

public import BooleanThreshold.JSSStructuredShift
public import Mathlib.Data.Fin.Embedding
public import Mathlib.MeasureTheory.Measure.Real

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

private theorem uniformOn_subset_fiber_le {Ω Ξ Y : Type*}
    [Fintype Ω] [Fintype Ξ] [Fintype Y] [Nonempty Ω] [Nonempty Ξ]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ξ]
    (F : Set Ω) (H : Set Ξ) (e : F ≃ Y × H)
    (E : Set Ω) (hEF : E ⊆ F) (B : Y → Set Ξ) {q : ℝ}
    (hB : ∀ y, (uniformOn Set.univ).real (B y) ≤ q)
    (himage : ∀ x : E, (e ⟨x.val, hEF x.prop⟩).2.val ∈ B (e ⟨x.val, hEF x.prop⟩).1)
    (hH : 0 < (uniformOn Set.univ).real H) :
    (uniformOn Set.univ).real E ≤ q / (uniformOn Set.univ).real H *
      (uniformOn Set.univ).real F := by
  classical
  let T : Set (Y × Ξ) := {z | z.2 ∈ B z.1}
  let f (x : E) : T := ⟨((e ⟨x.val, hEF x.prop⟩).1, (e ⟨x.val, hEF x.prop⟩).2.val), himage x⟩
  have hf : Function.Injective f := by
    intro x x' h
    have hfirst := congrArg (fun z : T => z.val.1) h
    have hsecond := congrArg (fun z : T => z.val.2) h
    have he : e ⟨x.val, hEF x.prop⟩ = e ⟨x'.val, hEF x'.prop⟩ :=
      Prod.ext hfirst (Subtype.ext hsecond)
    exact Subtype.ext (congrArg (fun z : F => z.val) (e.injective he))
  have hΩ : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hΞ : 0 < (Fintype.card Ξ : ℝ) := by exact_mod_cast Fintype.card_pos
  let (y : Y) : Fintype (B y) := Fintype.ofFinite _
  let eT : T ≃ (y : Y) × B y := Equiv.subtypeProdEquivSigmaSubtype (fun y z => z ∈ B y)
  have hT : (Nat.card T : ℝ) ≤ (Fintype.card Y : ℝ) * (q * Fintype.card Ξ) := by
    rw [Nat.card_congr eT, Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ y : Y, q * Fintype.card Ξ := by
        apply Finset.sum_le_sum
        intro y _
        have h := hB y
        rw [uniformOn_univ_real_eq_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
        exact (div_le_iff₀ hΞ).mp h
      _ = _ := by simp
  have hE : (E.ncard : ℝ) ≤ (Fintype.card Y : ℝ) * (q * Fintype.card Ξ) := by
    apply le_trans _ hT
    exact_mod_cast Nat.card_le_card_of_injective f hf
  have hF : (F.ncard : ℝ) =
      (Fintype.card Y : ℝ) * ((uniformOn Set.univ).real H * (Fintype.card Ξ : ℝ)) := by
    change (Nat.card F : ℝ) = _
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := Y), Nat.cast_mul]
    congr 1
    rw [uniformOn_univ_real_eq_card, div_mul_cancel₀ _ hΞ.ne']
    rfl
  rw [uniformOn_univ_real_eq_card E, uniformOn_univ_real_eq_card F, hF]
  apply (div_le_iff₀ hΩ).mpr
  refine hE.trans_eq ?_
  field_simp [hH.ne']

private theorem fixedProjectionBits_probability {n : ℕ} (d : Fin (n + 2) → Option Bool)
    (p : Fin (n + 2)) :
    (uniformOn Set.univ).real {X : Fin (n + 1) → Fin (n + 1) → Bool |
      fixedProjectionBits d p X} =
      (1 / 2 : ℝ) ^ (Finset.univ.filter fun r => d (p.succAbove r) ≠ none).card := by
  classical
  let R : Set (Fin (n + 1) → Bool) := {x | x 0 = true}
  let ν : Measure Bool := uniformOn Set.univ
  have hR : uniformOn Set.univ R = 1 / 2 := by
    rw [← pi_uniformOn_univ]
    change (Measure.pi (fun _ : Fin (n + 1) => ν))
      ((Function.eval (0 : Fin (n + 1))) ⁻¹' {true}) = _
    calc
      _ = ν ({true} : Set Bool) :=
        (measurePreserving_eval (fun _ : Fin (n + 1) => ν) (0 : Fin (n + 1))).measure_preimage
          (measurableSet_singleton true).nullMeasurableSet
      _ = _ := by
        change uniformOn Set.univ ({true} : Set Bool) = _
        rw [uniformOn_univ, Measure.count_singleton, Fintype.card_bool]
        rfl
  have hH : {X : Fin (n + 1) → Fin (n + 1) → Bool | fixedProjectionBits d p X} =
      Set.univ.pi (fun r => if d (p.succAbove r) ≠ none then R else Set.univ) := by
    ext X
    simp [fixedProjectionBits, R]
  rw [measureReal_def, hH, ← pi_uniformOn_univ, Measure.pi_pi]
  have hr (r : Fin (n + 1)) : uniformOn Set.univ
      (if d (p.succAbove r) ≠ none then R else Set.univ) =
      if d (p.succAbove r) ≠ none then (1 / 2 : ℝ≥0∞) else 1 := by
    split <;> simp_all only [measure_univ]
  simp_rw [hr, ← Finset.prod_filter, Finset.prod_const,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]

/-- Conditional on a nonzero difference pattern, a shifted square estimate
controls the target-span event, at a cost of two per remaining fixed bit. -/
theorem uniformOn_difference_targetSpan_le_of_shifted {n : ℕ}
    (d : Fin (n + 2) → Option Bool) (p : Fin (n + 2)) (hp : d p ≠ none)
    {q : ℝ}
    (hshift : ∀ D : Fin (n + 1) → Fin (n + 1) → ℤ,
      (uniformOn Set.univ).real {X : Fin (n + 1) → Fin (n + 1) → Bool |
        ∃ a : Fin (n + 1) → ℝ, a ≠ 0 ∧
          ∀ r, ∑ j, a j * (realSigns (X r) j + (D r j : ℝ)) = 0} ≤ q) :
    (uniformOn Set.univ).real {M : Fin (n + 2) → Fin (n + 2) → Bool |
      firstDifferencePattern M = d ∧
      signMatrixMap M (Pi.single 0 1 - Pi.single (0 : Fin (n + 1)).succ 1) ∈
        (equalCoefficientSubspace 0 (0 : Fin (n + 1)).succ).map (signMatrixMap M)} ≤
      q * 2 ^ (Finset.univ.filter fun r => d (p.succAbove r) ≠ none).card *
        (uniformOn Set.univ).real {M | firstDifferencePattern M = d} := by
  let F : Set (Fin (n + 2) → Fin (n + 2) → Bool) := {M | firstDifferencePattern M = d}
  let H : Set (Fin (n + 1) → Fin (n + 1) → Bool) := {X | fixedProjectionBits d p X}
  let E : Set (Fin (n + 2) → Fin (n + 2) → Bool) := {M | firstDifferencePattern M = d ∧
    signMatrixMap M (Pi.single 0 1 - Pi.single (0 : Fin (n + 1)).succ 1) ∈
      (equalCoefficientSubspace 0 (0 : Fin (n + 1)).succ).map (signMatrixMap M)}
  let B (y : Fin n → Bool) : Set (Fin (n + 1) → Fin (n + 1) → Bool) := {X |
    ∃ a : Fin (n + 1) → ℝ, a ≠ 0 ∧
      ∀ r, ∑ j, a j * (realSigns (X r) j + (differenceProjectionShift d p y r j : ℝ)) = 0}
  have hH := fixedProjectionBits_probability d p
  have hH' : 0 < (uniformOn Set.univ).real H := by
    change 0 < (uniformOn Set.univ).real {X | fixedProjectionBits d p X}
    rw [hH]
    positivity
  have h := uniformOn_subset_fiber_le F H (differencePatternEquiv d p hp) E
    (fun _ h => h.1) B (fun y => hshift (differenceProjectionShift d p y))
    (fun M => shifted_projection_has_null hp ⟨M.val, M.prop.1⟩ M.prop.2) hH'
  change (uniformOn Set.univ).real E ≤
    q / (uniformOn Set.univ).real {X | fixedProjectionBits d p X} * (uniformOn Set.univ).real F at h
  rw [hH, one_div, inv_pow, div_inv_eq_mul] at h
  exact h

private theorem exists_reindex_pair {n : ℕ} (i j : Fin (n + 2)) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin (n + 2)), e 0 = i ∧ e (0 : Fin (n + 1)).succ = j := by
  let e₀ := Equiv.swap 0 i
  let f := (0 : Fin (n + 1)).succ
  let t := e₀ f
  have h₀ : e₀ 0 = i := Equiv.swap_apply_left _ _
  have ht : i ≠ t := fun h => Fin.succ_ne_zero _ (e₀.injective (h₀.trans h).symm)
  refine ⟨e₀.trans (Equiv.swap t j), ?_, ?_⟩
  · change Equiv.swap t j (e₀ 0) = i
    rw [h₀, Equiv.swap_apply_of_ne_of_ne ht hij]
  · exact Equiv.swap_apply_left t j

private def permuteColumns {m n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin m → Fin n → Bool) ≃ (Fin m → Fin n → Bool) where
  toFun M := fun r i => M r (e i)
  invFun M := fun r i => M r (e.symm i)
  left_inv M := by simp
  right_inv M := by simp

private theorem signMatrixMap_perm {m n : ℕ} (e : Equiv.Perm (Fin n))
    (M : Fin m → Fin n → Bool) (a : Fin n → ℝ) :
    signMatrixMap (permuteColumns e M) (a ∘ e) = signMatrixMap M a := by
  funext r
  rw [signMatrixMap_apply, signMatrixMap_apply]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The fixed-target estimate after reindexing any selected pair of columns. -/
theorem uniformOn_targetSpan_le_of_shifted {n k : ℕ}
    (i j : Fin (n + 2)) (hij : i ≠ j) (d : Fin (n + 2) → Option Bool)
    (hd : d ≠ fun _ => none) (hk : (Finset.univ.filter fun r => d r ≠ none).card ≤ k)
    {q : ℝ} (hq : 0 ≤ q)
    (hshift : ∀ D : Fin (n + 1) → Fin (n + 1) → ℤ,
      (uniformOn Set.univ).real {X : Fin (n + 1) → Fin (n + 1) → Bool |
        ∃ a : Fin (n + 1) → ℝ, a ≠ 0 ∧
          ∀ r, ∑ j, a j * (realSigns (X r) j + (D r j : ℝ)) = 0} ≤ q) :
    uniformOn Set.univ {M : Fin (n + 2) → Fin (n + 2) → Bool |
      (fun r => differenceCode (M r i) (M r j)) = d ∧
      signMatrixMap M (Pi.single i 1 - Pi.single j 1) ∈
        (equalCoefficientSubspace i j).map (signMatrixMap M)} ≤
      ENNReal.ofReal (q * 2 ^ k) * uniformOn Set.univ
        {M : Fin (n + 2) → Fin (n + 2) → Bool |
          (fun r => differenceCode (M r i) (M r j)) = d} := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, d p ≠ none := by
    by_contra! h
    exact hd (funext h)
  obtain ⟨e, he₀, he₁⟩ := exists_reindex_pair i j hij
  let eM := permuteColumns (m := n + 2) e
  let Ω := Fin (n + 2) → Fin (n + 2) → Bool
  let μ : Measure Ω := uniformOn Set.univ
  let f := (0 : Fin (n + 1)).succ
  let F : Set Ω := {M | (fun r => differenceCode (M r i) (M r j)) = d}
  let G : Set Ω := {M | firstDifferencePattern M = d}
  let E : Set Ω := {M | M ∈ F ∧ signMatrixMap M (Pi.single i 1 - Pi.single j 1) ∈
    (equalCoefficientSubspace i j).map (signMatrixMap M)}
  let H : Set Ω := {M | M ∈ G ∧ signMatrixMap M (Pi.single 0 1 - Pi.single f 1) ∈
    (equalCoefficientSubspace 0 f).map (signMatrixMap M)}
  have heM (M : Ω) (r s : Fin (n + 2)) : eM M r s = M r (e s) := rfl
  have hF : eM ⁻¹' G = F := by
    ext M
    have hh : firstDifferencePattern (eM M) = fun r => differenceCode (M r i) (M r j) := by
      funext r
      change differenceCode (eM M r 0) (eM M r (0 : Fin (n + 1)).succ) = _
      rw [heM, heM, he₀, he₁]
    exact iff_of_eq (congrArg (· = d) hh)
  have hE : E ⊆ eM ⁻¹' H := by
    rintro M ⟨hFM, b, hb, hEq⟩
    refine ⟨(hF ▸ hFM : M ∈ eM ⁻¹' G), b ∘ e, ?_, ?_⟩
    · change b i - b j = 0 at hb
      change b (e 0) - b (e f) = 0
      simpa only [f, he₀, he₁] using hb
    · rw [signMatrixMap_perm, hEq]
      funext r
      rw [map_sub, map_sub, Pi.sub_apply, Pi.sub_apply, signMatrixMap_basis, signMatrixMap_basis,
        signMatrixMap_basis, signMatrixMap_basis]
      simp only [realSigns, heM, f, he₀, he₁]
  have hpres (A : Set Ω) : μ (eM ⁻¹' A) = μ A := by
    change uniformOn Set.univ (eM ⁻¹' A) = uniformOn Set.univ A
    rw [← Measure.map_apply (measurable_of_finite _) A.toFinite.measurableSet,
      map_uniformOn_univ_of_equiv eM]
  have hcount : (Finset.univ.filter fun r => d (p.succAbove r) ≠ none).card ≤ k := by
    have hsub : ((Finset.univ.filter fun r => d (p.succAbove r) ≠ none).map p.succAboveEmb) ⊆
        Finset.univ.filter fun r => d r ≠ none := by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    rw [← Finset.card_map p.succAboveEmb]
    exact (Finset.card_le_card hsub).trans hk
  have hH := uniformOn_difference_targetSpan_le_of_shifted d p hp hshift
  have hreal : μ.real H ≤ q * 2 ^ k * μ.real G :=
    hH.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcount) hq)
      ENNReal.toReal_nonneg)
  have hfin : ENNReal.ofReal (q * 2 ^ k) * μ F ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  change μ E ≤ _
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfin).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hEF : μ.real E ≤ μ.real H := by
    have hm := (measure_mono hE : μ E ≤ μ (eM ⁻¹' H))
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hm.trans_eq (hpres H))
  have hFG : μ.real F = μ.real G := by
    exact congrArg ENNReal.toReal (hF ▸ hpres G)
  change μ.real E ≤ q * 2 ^ k * μ.real F
  rw [hFG]
  exact hEF.trans hreal

end BooleanThreshold
