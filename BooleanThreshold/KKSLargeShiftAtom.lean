module

public import BooleanThreshold.KKSLargeHalasz
public import BooleanThreshold.SignSymmetry

public section

open Filter Finset MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Classical

namespace BooleanThreshold

/-- Atom at an arbitrary real target under the sign-cube law. -/
@[expose] noncomputable def signAtomAt {n : ℕ} (a : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  uniformOn (signCube n) {x | ∑ i, a i * x i = t}

private noncomputable def auxiliaryAtomAt {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ν : Measure Ω) (z : Ω → ℝ) (a : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  Measure.pi (fun _ : Fin n => ν) {x | ∑ i, a i * z (x i) = t}

private theorem auxiliaryAtom_cons_integral
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (z : Ω → ℝ) {n : ℕ} (a : Fin n → ℝ)
    (u : ℝ) :
    auxiliaryAtom ν z (Fin.cons u a) = ∫⁻ x, auxiliaryAtomAt ν z a (-u * z x) ∂ν := by
  let νn := Measure.pi (fun _ : Fin n => ν)
  let E : Set (Ω × (Fin n → Ω)) := {p | u * z p.1 + ∑ i, a i * z (p.2 i) = 0}
  have hE : MeasurableSet E := E.toFinite.measurableSet
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0
  have hpres : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => ν)) (ν.prod νn) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
  have he : e ⁻¹' E = {r | ∑ i, (Fin.cons u a : Fin (n + 1) → ℝ) i * z (r i) = 0} := by
    ext r
    change u * z (r 0) + (∑ i : Fin n, a i * z (r (Fin.succAbove 0 i))) = 0 ↔ _
    simp [Fin.sum_univ_succ]
  rw [auxiliaryAtom, ← he, hpres.measure_preimage hE.nullMeasurableSet, Measure.prod_apply hE]
  apply lintegral_congr
  intro x
  congr 1
  ext r
  change u * z x + (∑ i, a i * z (r i)) = 0 ↔ (∑ i, a i * z (r i)) = -u * z x
  rw [neg_mul]
  exact add_eq_zero_iff_eq_neg'

theorem signAtomAt_neg {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    signAtomAt a (-t) = signAtomAt a t := by
  let mask : Fin n → Bool := fun _ => true
  have h := uniformOn_signCube_flipVector mask {x | ∑ i, a i * x i = t}
  have he : flipVector mask ⁻¹' {x | ∑ i, a i * x i = t} = {x | ∑ i, a i * x i = -t} := by
    ext x
    simp [flipVector, mask, mul_neg, sum_neg_distrib]
    constructor <;> intro h <;> linarith
  rw [he] at h
  exact h

private theorem signAtomAt_eq_auxiliary {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    signAtomAt a t =
      auxiliaryAtomAt (uniformOn Set.univ : Measure Bool) (fun b => if b then 1 else -1) a t := by
  rw [signAtomAt, auxiliaryAtomAt, uniformOn_signCube_apply, pi_uniformOn_univ]
  rfl

/-- A nonzero coefficient leaves at most one sign choice for the remaining coordinate. -/
theorem signAtomAt_le_half {n : ℕ} (a : Fin n → ℝ) (ha : a ≠ 0) (t : ℝ) :
    signAtomAt a t ≤ 1 / 2 := by
  cases n with
  | zero =>
      exact (ha (Subsingleton.elim _ _)).elim
  | succ n =>
      have hnonzero : ∃ i, a i ≠ 0 := by
        by_contra! h
        exact ha (funext h)
      obtain ⟨i, hi⟩ := hnonzero
      let ν : Measure Bool := uniformOn Set.univ
      let νn := Measure.pi (fun _ : Fin n => ν)
      let z (b : Bool) : ℝ := if b then 1 else -1
      let E : Set (Bool × (Fin n → Bool)) :=
        {p | a i * z p.1 + ∑ j, a (i.succAbove j) * z (p.2 j) = t}
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Bool) i
      have hE : MeasurableSet E := E.toFinite.measurableSet
      have hpres : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => ν)) (ν.prod νn) :=
        measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
      have he : e ⁻¹' E = {r | ∑ j, a j * z (r j) = t} := by
        ext r
        change a i * z (r i) + (∑ j : Fin n, a (i.succAbove j) * z (r (i.succAbove j))) = t ↔
          (∑ j : Fin (n + 1), a j * z (r j)) = t
        rw [Fin.sum_univ_succAbove (fun j => a j * z (r j)) i]
      have hbit (b : Bool) : ν {b} = 1 / 2 := by
        rw [show ν = uniformOn Set.univ from rfl, uniformOn_univ, Measure.count_singleton]
        norm_num
      rw [signAtomAt_eq_auxiliary, auxiliaryAtomAt]
      change (Measure.pi (fun _ : Fin (n + 1) => ν)) {r | ∑ j, a j * z (r j) = t} ≤ _
      rw [← he, hpres.measure_preimage hE.nullMeasurableSet, Measure.prod_apply_symm hE]
      calc
        _ ≤ ∫⁻ _ : Fin n → Bool, (1 / 2 : ℝ≥0∞) ∂νn := by
          apply lintegral_mono
          intro r
          let F : Set Bool := (fun b => (b, r)) ⁻¹' E
          change ν F ≤ _
          by_cases h : F.Nonempty
          · obtain ⟨b, hb⟩ := h
            rw [← hbit b]
            apply measure_mono
            intro c hc
            change a i * z b + (∑ j, a (i.succAbove j) * z (r j)) = t at hb
            change a i * z c + (∑ j, a (i.succAbove j) * z (r j)) = t at hc
            apply Set.mem_singleton_iff.mpr
            cases b <;> cases c <;> try rfl
            all_goals simp [z] at hb hc
            all_goals exact (hi (by linarith)).elim
          · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
            exact bot_le
        _ = _ := by rw [lintegral_const, measure_univ, mul_one]

private theorem signAtomAt_eq_cons {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    signAtomAt a t = zeroAtom (Fin.cons t a) := by
  have hZero : zeroAtom (Fin.cons t a) =
      auxiliaryAtom (uniformOn Set.univ : Measure Bool) (fun b => if b then 1 else -1)
        (Fin.cons t a) := by
    change zeroAtom (Fin.cons t a) =
      auxiliaryAtomAt (uniformOn Set.univ : Measure Bool) (fun b => if b then 1 else -1)
        (Fin.cons t a) 0
    rw [← signAtomAt_eq_auxiliary]
    rfl
  rw [hZero, auxiliaryAtom_cons_integral]
  have he (x : Bool) :
      auxiliaryAtomAt (uniformOn Set.univ : Measure Bool) (fun b => if b then 1 else -1)
        a (-t * (if x then 1 else -1)) = signAtomAt a t := by
    rw [← signAtomAt_eq_auxiliary]
    cases x <;> simp [signAtomAt_neg]
  simp_rw [he]
  rw [lintegral_const, measure_univ, mul_one]

private theorem standard_character_neg_shift {P : ℕ} [NeZero P] (t : ZMod P) :
    ZMod.stdAddChar (-t) = star (ZMod.stdAddChar t) := by
  have h : ZMod.stdAddChar t ≠ 0 := by
    intro h
    simpa [h] using norm_standard_character t
  apply mul_left_cancel₀ h
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  change 1 = ZMod.stdAddChar t * (starRingEnd ℂ) (ZMod.stdAddChar t)
  rw [Complex.mul_conj', norm_standard_character]
  norm_num

private theorem lazyAtomAt_le_zero {n : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (a : Fin n → ℤ) (t : ℤ) :
    auxiliaryAtomAt (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ)) (t : ℝ) ≤
      auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ)) := by
  let _ := lazyCoordinateLaw_probability hμ (by linarith : μ ≤ 1)
  let ν := lazyCoordinateLaw μ
  let P := (∑ i, (a i).natAbs) + t.natAbs + 1
  let _ : NeZero P := ⟨by dsimp [P]; omega⟩
  let φ (u : ZMod P) := 1 - μ + μ * (ZMod.stdAddChar u).re
  have hφ (u : ZMod P) :
      (∑ x : Fin 3, (ν.real {x} : ℂ) * ZMod.stdAddChar ((lazyBit x : ZMod P) * u)) =
        (φ u : ℂ) := by
    have hν (b : Fin 3) : ν.real {b} = lazyBitWeight μ b := by
      rw [measureReal_def, lazyCoordinateLaw_singleton,
        ENNReal.toReal_ofReal (lazyBitWeight_nonneg hμ (by linarith) b)]
    rw [Fin.sum_univ_three]
    simp [hν, lazyBitWeight, lazyBit, standard_character_neg_shift, φ]
    apply Complex.ext <;> simp <;> ring
  have hΦ (u : ZMod P) : 0 ≤ φ u := by
    have hz := Complex.abs_re_le_norm (ZMod.stdAddChar u)
    rw [norm_standard_character, abs_le] at hz
    have hh := mul_le_mul_of_nonneg_left hz.1 hμ
    dsimp [φ]
    linarith
  have ht := measureReal_sum_eq_cycle_product ν a lazyBit t (P := P) (by dsimp [P]; omega)
    (by decide) φ hφ
  have h0 := auxiliaryAtom_eq_cycle_product ν a lazyBit (P := P) (by dsimp [P]; omega)
    (by decide) φ hφ
  have h₁ : auxiliaryAtomAt ν lazyBitEmbedding (fun i => (a i : ℝ)) (t : ℝ) ≠ ⊤ := by
    unfold auxiliaryAtomAt
    exact measure_ne_top _ _
  have h₂ : auxiliaryAtom ν lazyBitEmbedding (fun i => (a i : ℝ)) ≠ ⊤ := by
    unfold auxiliaryAtom
    exact measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal h₁ h₂).mp
  change (Measure.pi (fun _ : Fin n => ν)).real {x | ∑ i, (a i : ℝ) * (lazyBit (x i) : ℝ) = t} ≤ _
  rw [ht]
  change _ ≤ (auxiliaryAtom ν (fun x => (lazyBit x : ℝ)) (fun i => (a i : ℝ))).toReal
  rw [h0]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro u _
  have hu := Complex.re_le_norm (ZMod.stdAddChar (-(t : ZMod P) * u))
  rw [norm_standard_character] at hu
  exact mul_le_of_le_one_left (prod_nonneg (fun _ _ => hΦ _)) hu

/-- The lazy-sign comparison holds uniformly over integer targets as well. -/
theorem exists_lazy_integer_target_comparison {τ : ℝ} (hτ : 0 < τ) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 / 2 ∧ ∃ K : ℕ, ∀ n (a : Fin n → ℤ),
      K < (univ.filter fun i => a i ≠ 0).card → ∀ t : ℤ,
      signAtomAt (fun i => (a i : ℝ)) (t : ℝ) ≤
        ENNReal.ofReal τ * auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding (fun i => (a i : ℝ)) := by
  obtain ⟨μ, hμ, hμhalf, K, hcompare⟩ := exists_lazy_atom_comparison_int hτ
  let _ := lazyCoordinateLaw_probability hμ.le (by linarith : μ ≤ 1)
  refine ⟨μ, hμ, hμhalf, K, fun n a ha t => ?_⟩
  have hsub : (univ.filter fun i : Fin n => a i ≠ 0).map
      ⟨Fin.succ, Fin.succ_injective _⟩ ⊆
        (univ.filter fun i : Fin (n + 1) => (Fin.cons t a : Fin (n + 1) → ℤ) i ≠ 0) := by
    rintro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    simpa using (mem_filter.mp hi).2
  have hcard : (univ.filter fun i : Fin n => a i ≠ 0).card ≤
      (univ.filter fun i : Fin (n + 1) => (Fin.cons t a : Fin (n + 1) → ℤ) i ≠ 0).card := by
    simpa using card_le_card hsub
  let ν := lazyCoordinateLaw μ
  have hcons : (fun i => ((Fin.cons t a : Fin (n + 1) → ℤ) i : ℝ)) =
      Fin.cons (t : ℝ) (fun i => (a i : ℝ)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hq : auxiliaryAtom ν lazyBitEmbedding (Fin.cons (t : ℝ) (fun i => (a i : ℝ))) ≤
      auxiliaryAtom ν lazyBitEmbedding (fun i => (a i : ℝ)) := by
    rw [auxiliaryAtom_cons_integral]
    calc
      _ ≤ ∫⁻ _ : Fin 3, auxiliaryAtom ν lazyBitEmbedding (fun i => (a i : ℝ)) ∂ν := by
        apply lintegral_mono
        intro x
        have he : (- (t : ℝ)) * lazyBitEmbedding x = (-(t * lazyBit x) : ℤ) := by
          change -(t : ℝ) * (lazyBit x : ℝ) = _
          push_cast
          ring
        dsimp only
        rw [he]
        exact lazyAtomAt_le_zero hμ.le hμhalf a (-(t * lazyBit x))
      _ = _ := by simp
  rw [signAtomAt_eq_cons]
  have hh := hcompare (n + 1) (Fin.cons t a) (ha.trans_le hcard)
  rw [hcons] at hh
  exact hh.trans (mul_le_mul' le_rfl hq)

end BooleanThreshold
