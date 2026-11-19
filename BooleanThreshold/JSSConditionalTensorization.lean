module

public import BooleanThreshold.JSSConditionalRoundingProfile
public import Mathlib.MeasureTheory.Integral.Pi

public section

open scoped ENNReal BigOperators Classical
open MeasureTheory
open ProbabilityTheory

namespace BooleanThreshold

private theorem exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  rw [Real.exp_neg]
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hn : (4 : ℝ) ≤ Real.exp 2 := by
    have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 2
    rw [← Real.exp_nat_mul] at h'
    norm_num at h' ⊢
    exact h'
  simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hn

/-- A linear upper small-ball profile bounds a Laplace moment. -/
theorem integral_exp_neg_abs_le_of_smallBall {B : Type*} [Finite B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (ν : Measure B) [IsProbabilityMeasure ν] (f : B → ℝ)
    {s L : ℝ} (hs : 0 < s) (hL : 0 ≤ L)
    (hprof : ∀ t ≥ s, ν.real {b | |f b| ≤ t} ≤ L * t) :
    ∫ b, Real.exp (-|f b| / s) ∂ν ≤ 10 * L * s := by
  classical
  let U : Set B := {b | |f b| ≤ 2 * s}
  let V (k : ℕ) : Set B := {b | 2 * (2 : ℝ) ^ k * s < |f b| ∧ |f b| ≤ 4 * (2 : ℝ) ^ k * s}
  let G₀ := U.indicator (fun _ : B => (1 : ℝ≥0∞))
  let G (k : ℕ) := (V k).indicator (fun _ : B => ENNReal.ofReal ((1 / 4 : ℝ) ^ k))
  have hpoint (b : B) : ENNReal.ofReal (Real.exp (-|f b| / s)) ≤ G₀ b + ∑' k, G k b := by
    by_cases hb : b ∈ U
    · have hl : Real.exp (-|f b| / s) ≤ 1 := Real.exp_le_one_iff.mpr <| by
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) hs.le
      have hle : ENNReal.ofReal (Real.exp (-|f b| / s)) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hl
      have heg : G₀ b = 1 := Set.indicator_of_mem hb _
      exact hle.trans (heg ▸ le_add_of_nonneg_right zero_le)
    · have hl : 2 * s < |f b| := lt_of_not_ge hb
      obtain ⟨k, hk⟩ := exists_dyadic_annulus hs hl
      have hmem : b ∈ V k := hk
      have hpow : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
      have hr : 2 * (2 : ℝ) ^ k ≤ |f b| / s := (le_div_iff₀ hs).mpr hk.1.le
      have hex : Real.exp (-|f b| / s) ≤ (1 / 4 : ℝ) ^ k := by
        calc
          _ ≤ Real.exp ((k : ℝ) * (-2)) := by
            apply Real.exp_monotone
            rw [neg_div]
            linarith only [hpow, hr]
          _ = Real.exp (-2) ^ k := Real.exp_nat_mul _ _
          _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_two_le _
      have hsum : G k b ≤ ∑' j, G j b := ENNReal.le_tsum (f := fun j => G j b) k
      refine le_trans ?_ (hsum.trans (le_add_of_nonneg_left zero_le))
      rw [show G k b = _ from Set.indicator_of_mem hmem _]
      exact ENNReal.ofReal_le_ofReal hex
  have h₀ : ∫⁻ b, G₀ b ∂ν ≤ ENNReal.ofReal (2 * L * s) := by
    rw [show G₀ = U.indicator (fun _ => 1) by rfl, lintegral_indicator_const U.toFinite.measurableSet,
      one_mul, ← ENNReal.ofReal_toReal (measure_ne_top ν U)]
    apply ENNReal.ofReal_le_ofReal
    have hl := hprof (2 * s) (by linarith)
    change (ν U).toReal ≤ L * (2 * s) at hl
    linarith only [hl]
  have hG (k : ℕ) : ∫⁻ b, G k b ∂ν ≤ ENNReal.ofReal (4 * L * s * (1 / 2 : ℝ) ^ k) := by
    rw [show G k = (V k).indicator _ by rfl, lintegral_indicator_const (V k).toFinite.measurableSet,
      ← ENNReal.ofReal_toReal (measure_ne_top ν (V k)), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hle : ν.real (V k) ≤ L * (4 * (2 : ℝ) ^ k * s) :=
      (measureReal_mono (fun _ hb => hb.2) (measure_ne_top _ _)).trans
        (hprof _ (by nlinarith only [mul_le_mul_of_nonneg_right hpow hs.le, hs]))
    calc
      _ ≤ (1 / 4 : ℝ) ^ k * (L * (4 * (2 : ℝ) ^ k * s)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by
        rw [show (1 / 2 : ℝ) ^ k = (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k by rw [← mul_pow]; norm_num]
        ring
  have hA : ∫⁻ b, ENNReal.ofReal (Real.exp (-|f b| / s)) ∂ν ≤ ENNReal.ofReal (10 * L * s) := by
    refine (lintegral_mono hpoint).trans ?_
    rw [lintegral_add_left (measurable_of_finite G₀),
      lintegral_tsum (fun k => (measurable_of_finite (G k)).aemeasurable)]
    have hsum : (∑' k, ∫⁻ b, G k b ∂ν) ≤ ENNReal.ofReal (8 * L * s) := by
      have h := ENNReal.tsum_le_tsum hG
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
          ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left (4 * L * s)),
        tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)] at h
      norm_num at h
      convert h using 2
      ring
    have h := add_le_add h₀ hsum
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h
    convert h using 2
    ring
  have hor := integral_eq_lintegral_of_nonneg_ae
    (ae_of_all ν fun b => Real.exp_nonneg (-|f b| / s))
    (measurable_of_finite (fun b => Real.exp (-|f b| / s))).aestronglyMeasurable
  rw [hor]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hA
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 10 * L * s)] using h

/-- Tensorization of the upper small-ball profile for independently sampled rows. -/
theorem probability_sum_sq_le_of_smallBall {B ι : Type*} [Finite B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (ν : Measure B) [IsProbabilityMeasure ν] (f : B → ℝ)
    {s L K : ℝ} (hs : 0 < s) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hprof : ∀ t ≥ s, ν.real {b | |f b| ≤ t} ≤ L * t) [Fintype ι] :
    (Measure.pi (fun _ : ι => ν)).real
      {r | ∑ i, (f (r i)) ^ 2 ≤ K ^ 2 * (Fintype.card ι : ℝ) * s ^ 2} ≤
      (10 * L * s * Real.exp K) ^ Fintype.card ι := by
  let m := Fintype.card ι
  let μ := Measure.pi (fun _ : ι => ν)
  let g (b : B) := Real.exp (-|f b| / s)
  let G (r : ι → B) := ∏ i, g (r i)
  let c := Real.exp (-K * (m : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hG₀ (r : ι → B) : 0 ≤ G r := by dsimp [G, g]; positivity
  have hG₁ (r : ι → B) : G r ≤ 1 := by
    apply Finset.prod_le_one₀ (fun _ _ => Real.exp_nonneg _)
    intro i _
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) hs.le)
  have hI : Integrable G μ :=
    (MemLp.of_bound (p := 1) (measurable_of_finite G).aestronglyMeasurable 1 (ae_of_all μ fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG₀ r)]
      exact hG₁ r)).integrable (by norm_num)
  have hsub : {r : ι → B | ∑ i, (f (r i)) ^ 2 ≤ K ^ 2 * (m : ℝ) * s ^ 2} ⊆ {r | c ≤ G r} := by
    intro r hr
    have hsumsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ => (1 : ℝ)) (fun i => |f (r i)|)
    simp only [one_mul, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hsumsq
    have hsum : ∑ i, |f (r i)| ≤ K * (m : ℝ) * s := by
      apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mp
      calc
        _ ≤ (m : ℝ) * ∑ i, (f (r i)) ^ 2 := hsumsq
        _ ≤ (m : ℝ) * (K ^ 2 * (m : ℝ) * s ^ 2) :=
          mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg m)
        _ = _ := by ring
    change c ≤ G r
    rw [show G r = Real.exp (∑ i, -|f (r i)| / s) by simp [G, g, Real.exp_sum]]
    apply Real.exp_monotone
    simp only [← Finset.sum_div, Finset.sum_neg_distrib, neg_div]
    have hh := (div_le_iff₀ hs).mpr hsum
    linarith only [hh]
  have hMark := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hG₀) hI c
  have hint : (∫ r, G r ∂μ) ≤ (10 * L * s) ^ m := by
    unfold G μ
    rw [integral_fintype_prod_eq_pow]
    apply pow_le_pow_left₀ (integral_nonneg (fun b => Real.exp_nonneg _)) _ _
    exact integral_exp_neg_abs_le_of_smallBall ν f hs hL hprof
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have hd : (10 * L * s * Real.exp K) ^ m * c = (10 * L * s) ^ m := by
    rw [mul_pow]
    change (10 * L * s) ^ m * Real.exp K ^ m * Real.exp (-K * (m : ℝ)) = _
    rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
    have hn : (m : ℝ) * K + -K * (m : ℝ) = 0 := by ring
    rw [hn, Real.exp_zero, mul_one]
  apply le_of_mul_le_mul_right _ hc
  rw [hd, mul_comm _ c]
  exact hMark.trans hint

/-- Only a fixed number of sampled rows need to fall inside the window. The
price of their possible locations is the binomial coefficient. -/
theorem uniformMatrix_sum_sq_le_of_smallBall_on_many_rows
    {B : Type*} [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : Set B) (hW : W.Nonempty) (f : B → ℝ) {s L K : ℝ}
    (hs : 0 < s) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hprof : ∀ t ≥ s, (uniformOn W).real {b | |f b| ≤ t} ≤ L * t) (m k : ℕ) :
    (uniformOn Set.univ).real {A : Fin m → B |
      (Finset.univ.filter fun i => A i ∈ W).card ≥ k ∧
      ∑ i, (f (A i)) ^ 2 ≤ K ^ 2 * (k : ℝ) * s ^ 2} ≤
      (m.choose k : ℝ) * (10 * L * s * Real.exp K) ^ k := by
  classical
  let choices := (Finset.univ : Finset (Fin m)).powersetCard k
  let E (I : Finset (Fin m)) : Set (Fin m → B) :=
    {A | (∀ i ∈ I, A i ∈ W) ∧ ∑ i ∈ I, (f (A i)) ^ 2 ≤ K ^ 2 * (k : ℝ) * s ^ 2}
  let S : Set (Fin m → B) := {A |
      (Finset.univ.filter fun i => A i ∈ W).card ≥ k ∧
        ∑ i, (f (A i)) ^ 2 ≤ K ^ 2 * (k : ℝ) * s ^ 2}
  have hsubset : S ⊆ ⋃ I ∈ choices, E I := by
    intro A hA
    obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq hA.1
    refine Set.mem_iUnion₂.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩,
      fun i hi => (Finset.mem_filter.mp (hI hi)).2, ?_⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg I.subset_univ (fun i _ _ => sq_nonneg _)).trans hA.2
  have hE (I : Finset (Fin m)) (hI : I ∈ choices) :
      (uniformOn Set.univ).real (E I) ≤ (10 * L * s * Real.exp K) ^ k := by
    let e : I ↪ Fin m := ⟨Subtype.val, Subtype.val_injective⟩
    let R : Set (I → B) := Set.univ.pi (fun _ : I => W)
    let F : Set (I → B) := {A | ∑ i, (f (A i)) ^ 2 ≤ K ^ 2 * (k : ℝ) * s ^ 2}
    have hpre : E I = (fun (A : Fin m → B) (i : I) => A (e i)) ⁻¹' (R ∩ F) := by
      ext A
      simp only [E, R, F, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_univ_pi]
      have hsum : (∑ i : I, (f (A (e i))) ^ 2) = ∑ i ∈ I, (f (A i)) ^ 2 :=
        Finset.sum_coe_sort I (fun i => (f (A i)) ^ 2)
      rw [hsum]
      exact and_congr_left' (by simp [e])
    have hrow : (uniformOn Set.univ : Measure (Fin m → B)).map
        (fun (x : Fin m → B) (i : I) => x (e i)) = uniformOn Set.univ := by
      rw [← pi_uniformOn_univ, pi_map_restrict_embedding _ e, pi_uniformOn_univ]
    let ν := uniformOn W
    let : IsProbabilityMeasure ν := isProbabilityMeasure_uniformOn W.toFinite hW
    have hcard : Fintype.card I = k := by
      rw [Fintype.card_coe, (Finset.mem_powersetCard.mp hI).2]
    rw [hpre, measureReal_def, ← Measure.map_apply (measurable_of_finite _) (R ∩ F).toFinite.measurableSet,
      hrow, uniformOn_inter Set.finite_univ, Set.univ_inter, ENNReal.toReal_mul, ← measureReal_def,
      ← measureReal_def, show R = Set.univ.pi (fun _ : I => W) by rfl, uniformOn_pi]
    refine (mul_le_of_le_one_right measureReal_nonneg measureReal_le_one).trans ?_
    have ht := probability_sum_sq_le_of_smallBall (ι := I) ν f hs hL hK hprof
    simpa only [ν, hcard, F] using ht
  change (uniformOn Set.univ).real S ≤ _
  calc
    _ ≤ (uniformOn Set.univ).real (⋃ I ∈ choices, E I) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ I ∈ choices, (uniformOn Set.univ).real (E I) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _I ∈ choices, (10 * L * s * Real.exp K) ^ k := Finset.sum_le_sum hE
    _ = _ := by simp [choices, Finset.card_powersetCard]

end BooleanThreshold
