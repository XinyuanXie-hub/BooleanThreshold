module

public import BooleanThreshold.JSSCorank
public import BooleanThreshold.JSSCorankCompressible
public import BooleanThreshold.JSSCorankOrient
public import BooleanThreshold.JSSCorankTransfer

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Module
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanThreshold

/-- An excluded normal for the uniform conditional anti-concentration estimate. -/
def exceptionalConditionalNormalEvent (m d : ℕ) (S : Set (Fin d → ℝ))
    (W : Set (Fin d → Bool)) (θ : ℝ≥0∞) : Set (Fin m → Fin d → Bool) :=
  {A | ∃ a : Fin d → ℝ, (∑ i, a i ^ 2) = 1 ∧ a ∉ S ∧
    (∀ j : Fin m, ∑ i, a i * realSigns (A j) i = 0) ∧ θ < windowAtom a W}

/-- The uniform conditional atom estimate for all unit common normals to
an independent sign sample with one fewer row than columns. -/
def UniformConditionalAtomEstimate : Prop :=
  ∀ δ ρ : ℝ, 0 < δ → δ < 1 → 0 < ρ → ρ < 1 →
    ∃ γ > (0 : ℝ), ∃ L : ℝ≥0, ∀ᶠ m : ℕ in atTop,
      (uniformOn Set.univ).real
        (exceptionalConditionalNormalEvent (m + 1) (m + 2)
          (almostConstantUnitVectors (m + 2) δ ρ) (balancedSignWindow (m + 2) γ)
          ((L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ (m + 2) *
            uniformOn Set.univ (balancedSignWindow (m + 2) γ))) ≤ (1 / 4 : ℝ) ^ (m + 2)

/-- An incompressible null space with no small atom yields a bad conditional
normal after appending one row and applying a random column orientation. -/
theorem incompressible_no_small_atom_probability_le {m d s : ℕ} {ρ : ℝ}
    (S : Set (Fin d → ℝ)) (W : Set (Fin d → Bool)) {q θ : ℝ≥0∞}
    (hq : 0 < q) (hθ : θ ≤ q / 4) (hW : 1 / 2 ≤ uniformOn Set.univ W)
    (hOrient : ∀ a : Fin d → ℝ,
      ¬ nearSparse s ρ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin d)) →
      uniformOn Set.univ {mask | flipVector mask a ∈ S} ≤ 1 / 8) :
    uniformOn Set.univ ({A : Fin m → Fin d → Bool | ¬ hasSmallAtomNormal q A} \
      corankCompressibleEvent m d s ρ) * (q * (1 / 8)) ≤
      uniformOn Set.univ (exceptionalConditionalNormalEvent (m + 1) d S W θ) := by
  classical
  let P := Fin m → Fin d → Bool
  let E : Set P := {A | ¬ hasSmallAtomNormal q A} \ corankCompressibleEvent m d s ρ
  let F := exceptionalConditionalNormalEvent (m + 1) d S W θ
  have hex (A : P) (hA : A ∈ E) :
      ∃ a : Fin d → ℝ, (∑ i, a i ^ 2) = 1 ∧ (∀ j : Fin m, ∑ i, a i * realSigns (A j) i = 0) ∧
        ¬ nearSparse s ρ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin d)) := by
    have h := hA.2
    change ¬ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 →
      signMatrixMap A (WithLp.ofLp x) = 0 → nearSparse s ρ x at h
    push Not at h
    obtain ⟨x, hx, hnull, hs⟩ := h
    refine ⟨WithLp.ofLp x, ?_, ?_, ?_⟩
    · simpa only [hx, one_pow] using (EuclideanSpace.real_norm_sq_eq x).symm
    · intro j
      simpa only [signMatrixMap_apply, Pi.zero_apply] using congrFun hnull j
    · exact hs
  choose a ha using hex
  let normal (A : P) : Fin d → ℝ := if h : A ∈ E then a A h else 0
  have hNormal (A : P) (hA : A ∈ E) := ha A hA
  have hChoice (A : P) (hA : A ∈ E) : normal A = a A hA := by simp [normal, hA]
  have hHigh (A : P) (hA : A ∈ E) : q < zeroAtom (normal A) := by
    by_contra! hlow
    have hn := hNormal A hA
    rw [← hChoice A hA] at hn
    have hne : normal A ≠ 0 := by
      intro h
      rw [h] at hn
      simp at hn
    exact hA.1 ⟨normal A, hne, hlow, hn.2.1⟩
  let rows (A : P) : Set (Fin d → Bool) := {b | ∑ i, normal A i * realSigns b i = 0}
  let masks (A : P) : Set (Fin d → Bool) :=
    {mask | flipVector mask (normal A) ∉ S ∧
      zeroAtom (normal A) / 4 < windowAtom (flipVector mask (normal A)) W}
  refine measure_append_and_flip_lower_bound E F rows masks q (1 / 8) ?_ ?_ ?_
  · intro A hA
    have hz : uniformOn Set.univ (rows A) = zeroAtom (normal A) := by
      rw [zeroAtom, uniformOn_signCube_apply]
      rfl
    exact (hHigh A hA).le.trans_eq hz.symm
  · intro A hA
    have hn := hNormal A hA
    rw [← hChoice A hA] at hn
    exact measure_good_atom_orientations (normal A) S W (hq.trans (hHigh A hA))
      hW (hOrient _ hn.2.2)
  · intro A hA b hb mask hmask
    have hn := hNormal A hA
    rw [← hChoice A hA] at hn
    refine ⟨flipVector mask (normal A), ?_, hmask.1, ?_, ?_⟩
    · calc
        _ = ∑ i, normal A i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          cases h : mask i <;> simp [flipVector, h]
        _ = _ := hn.1
    · intro j
      rw [dot_flipVector_realSigns_flipColumns]
      refine Fin.cases ?_ (fun k => ?_) j
      · exact hb
      · exact hn.2.1 k
    · have hlt : q / (4 : ℝ≥0∞) < zeroAtom (normal A) / 4 :=
        (ENNReal.div_lt_div_iff_left (by simp) (by simp)).2 (hHigh A hA)
      exact hθ.trans_lt (hlt.trans hmask.2)

private theorem cutoff_product :
    (3 / 5 : ℝ≥0∞) = (9 / 10 : ℝ≥0∞) * (2 / 3 : ℝ≥0∞) := by
  have h : (3 / 5 : ℝ≥0) = (9 / 10 : ℝ≥0) * (2 / 3 : ℝ≥0) := by
    apply NNReal.eq
    norm_num
  simpa only [ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_mul, ENNReal.coe_ofNat] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h

private theorem atom_eventually (L : ℝ≥0) :
    ∀ᶠ d : ℕ in atTop, (L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ d ≤
      (2 / 3 : ℝ≥0∞) ^ d / 4 := by
  have hbase : (9 / 10 : ℝ≥0∞) < 1 := by
    have h : (9 / 10 : ℝ≥0) < 1 := by
      apply NNReal.coe_lt_coe.mp
      norm_num
    simpa only [ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_lt_one_iff.mpr h
  have ht := ENNReal.Tendsto.const_mul (a := (L : ℝ≥0∞))
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hbase) (Or.inr ENNReal.coe_ne_top)
  have ht' : ∀ᶠ d : ℕ in atTop, (L : ℝ≥0∞) * (9 / 10 : ℝ≥0∞) ^ d ≤ 1 / 4 :=
    (by simpa only [mul_zero] using ht : Tendsto
      (fun d : ℕ => (L : ℝ≥0∞) * (9 / 10 : ℝ≥0∞) ^ d) atTop (𝓝 0)).eventually_le_const
      (ENNReal.div_pos one_ne_zero (by simp))
  filter_upwards [ht'] with d hd
  rw [cutoff_product, mul_pow, ← mul_assoc]
  calc
    _ ≤ (1 / 4 : ℝ≥0∞) * (2 / 3 : ℝ≥0∞) ^ d := mul_le_mul' hd (le_refl _)
    _ = _ := by simp only [div_eq_mul_inv, one_mul, mul_comm]

private theorem window_mass_eventually {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ d : ℕ in atTop, 1 / 2 ≤ uniformOn Set.univ (balancedSignWindow d γ) := by
  obtain ⟨N, hN⟩ := balancedWindow_mass_ge_half hγ
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  apply (ENNReal.toReal_le_toReal (by simp) (measure_ne_top _ _)).mp
  simpa only [balancedSignWindow, measureReal_def, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat] using hN n hn

/-- The square corank-two estimate follows from the uniform conditional
anti-concentration estimate at the same rate used for the large-atom proof. -/
theorem square_corank_two_geometric_from_conditional
    (hCond : UniformConditionalAtomEstimate) :
    ∃ a : ℝ, 1 / 4 ≤ a ∧ a < 1 / 2 ∧ ∃ C ≥ (0 : ℝ), ∀ᶠ r : ℕ in atTop,
      (uniformOn Set.univ).real {v : Fin (r + 1) → Fin (r + 1) → Bool |
        finrank ℝ (Submodule.span ℝ (Set.range fun i => realSigns (v i))) < r} ≤ C * a ^ (r + 1) := by
  obtain ⟨ρ, hρ, hρ', J, hJ, D, hD, hcomp⟩ := corankCompressible_probability_geometric
  let δ : ℝ := 1 / (4 * (J : ℝ))
  have hJ1 : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast (show 1 ≤ J by omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ < 1 := by
    dsimp [δ]
    rw [div_lt_iff₀ (by positivity), one_mul]
    linarith
  obtain ⟨γ, hγ, L, hF⟩ := hCond δ ρ hδ hδ' hρ hρ'
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcomp.and hF)
  obtain ⟨N', hN'⟩ := eventually_atTop.mp ((atom_eventually L).and (window_mass_eventually hγ))
  refine square_corank_two_geometric_of_small_atom (b := 15 / 32) (D := D + 8)
    (by norm_num) (by norm_num) (by positivity) ?_
  refine eventually_atTop.mpr ⟨max N (max N' (40 * J)), fun m hm => ?_⟩
  have hmN : N ≤ m := (le_max_left _ _).trans hm
  have hmN' : max N' (40 * J) ≤ m := (le_max_right _ _).trans hm
  let d := m + 2
  let q := (2 / 3 : ℝ≥0∞) ^ d
  let W := balancedSignWindow d γ
  let S := almostConstantUnitVectors d δ ρ
  let θ := (L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ d * uniformOn Set.univ W
  let F := exceptionalConditionalNormalEvent (m + 1) d S W θ
  let C := corankCompressibleEvent m d (d / J) ρ
  let B : Set (Fin m → Fin d → Bool) := {A | ¬ hasSmallAtomNormal q A}
  let E := B \ C
  let μ : Measure (Fin m → Fin d → Bool) := uniformOn Set.univ
  let ν : Measure (Fin (m + 1) → Fin d → Bool) := uniformOn Set.univ
  have hq : 0 < q :=
    pos_iff_ne_zero.mpr (pow_ne_zero _ (ENNReal.div_pos (by simp) (by simp)).ne')
  have hθ : θ ≤ q / 4 := by
    calc
      _ ≤ (L : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ d * 1 := mul_le_mul' (le_refl _) prob_le_one
      _ ≤ _ := by
        rw [mul_one]
        exact (hN' d (by dsimp [d]; omega)).1
  have hW : 1 / 2 ≤ uniformOn Set.univ W := (hN' d (by dsimp [d]; omega)).2
  have hEN : μ E * (q * (1 / 8)) ≤ ν F :=
    incompressible_no_small_atom_probability_le S W hq hθ hW
      (almostConstant_orientation_probability_le hJ (by dsimp [d]; omega)
        hρ.le le_rfl le_rfl)
  have hEreal := ENNReal.toReal_mono (measure_ne_top ν F) hEN
  have hE : μ.real E * ((2 / 3 : ℝ) ^ d * (1 / 8)) ≤ (1 / 4 : ℝ) ^ d := by
    have hE' : μ.real E * ((2 / 3 : ℝ) ^ d * (1 / 8)) ≤ ν.real F := by
      simpa only [q, measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one] using hEreal
    exact hE'.trans (hN m hmN).2
  have hdiff : μ.real E ≤ 8 * (3 / 8 : ℝ) ^ d := by
    calc
      _ ≤ (1 / 4 : ℝ) ^ d / ((2 / 3 : ℝ) ^ d * (1 / 8)) := (le_div_iff₀ (by positivity)).2 hE
      _ = _ := by
        rw [div_mul_eq_div_div, ← div_pow]
        norm_num
        ring
  have hsub : B ⊆ E ∪ C := by
    intro x hx
    by_cases hy : x ∈ C
    · exact Or.inr hy
    · exact Or.inl ⟨hx, hy⟩
  calc
    μ.real B ≤ μ.real (E ∪ C) := measureReal_mono hsub
    _ ≤ μ.real E + μ.real C := measureReal_union_le _ _
    _ ≤ 8 * (3 / 8 : ℝ) ^ d + D * (15 / 32 : ℝ) ^ d := add_le_add hdiff (hN m hmN).1
    _ ≤ 8 * (15 / 32 : ℝ) ^ d + D * (15 / 32 : ℝ) ^ d := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by norm_num)) (le_refl _)
    _ = _ := by ring

end BooleanThreshold
