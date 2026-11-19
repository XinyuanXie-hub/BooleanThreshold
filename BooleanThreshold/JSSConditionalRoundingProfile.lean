module

public import BooleanThreshold.JSSConditionalRounding

public section

open scoped BigOperators ENNReal Topology
open MeasureTheory

namespace BooleanThreshold

private theorem prod_real_measure_le_of_sections
    {A B : Type*} [Finite A] [Finite B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Set (A × B)) (U : Set A) {c : ℝ} (hc : 0 ≤ c)
    (hin : ∀ a ∈ U, ν.real (Prod.mk a ⁻¹' H) ≤ c)
    (hout : ∀ a ∉ U, Prod.mk a ⁻¹' H = ∅) :
    (μ.prod ν).real H ≤ μ.real U * c := by
  classical
  have h : (μ.prod ν) H ≤ μ U * ENNReal.ofReal c := by
    rw [Measure.prod_apply H.toFinite.measurableSet]
    calc
      _ ≤ ∫⁻ a, U.indicator (fun _ => ENNReal.ofReal c) a ∂μ := by
        apply lintegral_mono
        intro a
        by_cases ha : a ∈ U
        · change ν (Prod.mk a ⁻¹' H) ≤ _
          rw [Set.indicator_of_mem ha, ← ENNReal.ofReal_toReal (measure_ne_top ν _)]
          exact ENNReal.ofReal_le_ofReal (hin a ha)
        · simp [hout a ha, ha]
      _ = _ := by rw [lintegral_indicator_const U.toFinite.measurableSet, mul_comm]
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top μ _) ENNReal.ofReal_ne_top) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ← measureReal_def] using hr

private theorem real_measure_sections_ge_le
    {A B : Type*} [Finite A] [Finite B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Set (A × B)) {c : ℝ} (hc : 0 < c) :
    μ.real {a | c ≤ ν.real (Prod.mk a ⁻¹' H)} ≤ (μ.prod ν).real H / c := by
  let f (a : A) := ν (Prod.mk a ⁻¹' H)
  have hzero : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have h := meas_ge_le_lintegral_div (μ := μ) (measurable_of_finite f).aemeasurable
    (ε := ENNReal.ofReal c) hzero ENNReal.ofReal_ne_top
  have hset : {a | ENNReal.ofReal c ≤ f a} = {a | c ≤ ν.real (Prod.mk a ⁻¹' H)} := by
    ext a
    exact ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)
  rw [hset, ← Measure.prod_apply H.toFinite.measurableSet] at h
  have hfin : (μ.prod ν) H / ENNReal.ofReal c ≠ ∞ :=
    ENNReal.div_ne_top (measure_ne_top _ _) hzero
  have hr := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal hc.le, ← measureReal_def] using hr

private theorem measureReal_iUnion_le_geometric {A : Type*}
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (E : ℕ → Set A) {M q : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) (hq' : q < 1)
    (hE : ∀ k, μ.real (E k) ≤ M * q ^ k) :
    μ.real (⋃ k, E k) ≤ M / (1 - q) := by
  have hs : Summable (fun k : ℕ => M * q ^ k) :=
    (summable_geometric_of_lt_one hq hq').mul_left M
  have h : μ (⋃ k, E k) ≤ ∑' k, ENNReal.ofReal (M * q ^ k) := by
    apply (measure_iUnion_le E).trans
    apply ENNReal.tsum_le_tsum
    intro k
    exact (ENNReal.ofReal_toReal (measure_ne_top μ (E k))).symm.le.trans (ENNReal.ofReal_le_ofReal (hE k))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs,
    tsum_mul_left, tsum_geometric_of_lt_one hq hq', ← div_eq_mul_inv] at h
  simpa only [← measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ M / (1 - q))] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

private theorem exists_le_two_pow_mul {s x : ℝ} (hs : 0 < s) :
    ∃ k : ℕ, x ≤ (2 : ℝ) ^ k * s := by
  obtain ⟨k, hk⟩ := exists_nat_gt (x / s)
  refine ⟨k, (div_le_iff₀ hs).mp (hk.le.trans ?_)⟩
  exact_mod_cast Nat.lt_two_pow_self.le

theorem exists_dyadic_annulus {t x : ℝ} (ht : 0 < t) (hx : 2 * t < x) :
    ∃ k : ℕ, 2 * (2 : ℝ) ^ k * t < x ∧ x ≤ 4 * (2 : ℝ) ^ k * t := by
  let ex := exists_le_two_pow_mul (s := 2 * t) (x := x) (by positivity)
  have hk := Nat.find_spec ex
  have hn : Nat.find ex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hk
    exact (not_le_of_gt hx) hk
  obtain ⟨k, h⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hprev := lt_of_not_ge (Nat.find_min ex (show k < Nat.find ex by omega))
  refine ⟨k, ?_, ?_⟩
  · convert hprev using 1; ring
  · rw [h, pow_succ] at hk
    convert hk using 1; ring

private theorem exists_dyadic_ge_le_twice {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ∃ k : ℕ, t ≤ (2 : ℝ) ^ k * s ∧ (2 : ℝ) ^ k * s ≤ 2 * t := by
  let ex := exists_le_two_pow_mul (s := s) (x := t) hs
  refine ⟨Nat.find ex, Nat.find_spec ex, ?_⟩
  by_cases hz : Nat.find ex = 0
  · rw [hz, pow_zero, one_mul]
    linarith only [hst, hs]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have hprev := le_of_lt (lt_of_not_ge (Nat.find_min ex (show k < Nat.find ex by omega)))
  rw [hk, pow_succ]
  nlinarith only [hprev]

private def smallBall {B : Type*} (f : B → ℝ) (r : ℝ) : Set B := {b | |f b| ≤ r}

private theorem upper_rounding_leakage {A B : Type*} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : B → ℝ) (g : A → B → ℝ) {s L t : ℝ}
    (hs : 0 < s) (hL : 0 < L) (hst : s ≤ t)
    (hprof : ∀ u ≥ s, ν.real (smallBall f u) ≤ L * u)
    (hdev : ∀ b u, 0 < u → μ.real {a | u ≤ |g a b - f b|} ≤ s ^ 2 / (4 * u ^ 2)) :
    (μ.prod ν).real {p | |g p.1 p.2| ≤ t ∧ 2 * t < |f p.2|}
      ≤ 2 * (L * s ^ 2 / t) := by
  let H (k : ℕ) : Set (A × B) :=
    {p | |g p.1 p.2| ≤ t ∧ 2 * (2 : ℝ) ^ k * t < |f p.2| ∧ |f p.2| ≤ 4 * (2 : ℝ) ^ k * t}
  have ht := hs.trans_le hst
  have hsub : {p : A × B | |g p.1 p.2| ≤ t ∧ 2 * t < |f p.2|} ⊆ ⋃ k, H k := by
    rintro p ⟨hp, hlarge⟩
    obtain ⟨k, hk⟩ := exists_dyadic_annulus ht hlarge
    exact Set.mem_iUnion.mpr ⟨k, hp, hk⟩
  have hH (k : ℕ) : (μ.prod ν).real (H k) ≤ (L * s ^ 2 / t) * (1 / 2 : ℝ) ^ k := by
    let F : Set (B × A) := Prod.swap ⁻¹' H k
    let U := smallBall f (4 * (2 : ℝ) ^ k * t)
    have hSwap : (ν.prod μ).real F = (μ.prod ν).real (H k) := by
      have h := Measure.measurePreserving_swap (μ := ν) (ν := μ)
      exact congrArg ENNReal.toReal
        (h.measure_preimage (H k).toFinite.measurableSet.nullMeasurableSet)
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hscale : s ≤ 4 * (2 : ℝ) ^ k * t := by
      exact hst.trans (by nlinarith [mul_le_mul_of_nonneg_right hpow ht.le])
    have hslice (b : B) (_ : b ∈ U) :
        μ.real (Prod.mk b ⁻¹' F) ≤ s ^ 2 / (4 * ((2 : ℝ) ^ k * t) ^ 2) := by
      refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hdev b _ (by positivity))
      intro a ha
      obtain ⟨hball, hlo, _⟩ := ha
      change |g a b| ≤ t at hball
      change 2 * (2 : ℝ) ^ k * t < |f b| at hlo
      change (2 : ℝ) ^ k * t ≤ |g a b - f b|
      have hl := abs_sub_abs_le_abs_sub (f b) (g a b)
      rw [abs_sub_comm (f b) (g a b)] at hl
      nlinarith [mul_le_mul_of_nonneg_right hpow ht.le]
    have hout (b : B) (hb : b ∉ U) : Prod.mk b ⁻¹' F = ∅ := by
      ext a
      refine iff_false_intro fun ha => hb ?_
      exact ha.2.2
    rw [← hSwap]
    calc
      _ ≤ ν.real U * (s ^ 2 / (4 * ((2 : ℝ) ^ k * t) ^ 2)) :=
        prod_real_measure_le_of_sections ν μ F U (by positivity) hslice hout
      _ ≤ L * (4 * (2 : ℝ) ^ k * t) * (s ^ 2 / (4 * ((2 : ℝ) ^ k * t) ^ 2)) :=
        mul_le_mul_of_nonneg_right (hprof _ hscale) (by positivity)
      _ = _ := by
        rw [div_pow, one_pow]
        field_simp [ht.ne', pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have h := measureReal_iUnion_le_geometric (μ.prod ν) H (by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hH
  convert h using 1; ring

private theorem lower_rounding_loss_le {A B : Type*} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : B → ℝ) (g : A → B → ℝ) {s : ℝ} (hs : 0 < s)
    (hdev : ∀ b u, 0 < u → μ.real {a | u ≤ |g a b - f b|} ≤ s ^ 2 / (4 * u ^ 2)) :
    (μ.prod ν).real {p | |f p.2| ≤ s ∧ 2 * s < |g p.1 p.2|} ≤ ν.real (smallBall f s) / 4 := by
  let H : Set (A × B) := {p | |f p.2| ≤ s ∧ 2 * s < |g p.1 p.2|}
  let F : Set (B × A) := Prod.swap ⁻¹' H
  have hSwap : (ν.prod μ).real F = (μ.prod ν).real H := by
    have h := Measure.measurePreserving_swap (μ := ν) (ν := μ)
    exact congrArg ENNReal.toReal (h.measure_preimage H.toFinite.measurableSet.nullMeasurableSet)
  have hIn (b : B) (hb : b ∈ smallBall f s) : μ.real (Prod.mk b ⁻¹' F) ≤ 1 / 4 := by
    have h := hdev b s hs
    have hconst : s ^ 2 / (4 * s ^ 2) = 1 / 4 := by field_simp [hs.ne']
    rw [hconst] at h
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h
    intro a ha
    have ha' : 2 * s < |g a b| := ha.2
    change |f b| ≤ s at hb
    have hl := abs_sub_abs_le_abs_sub (g a b) (f b)
    change s ≤ |g a b - f b|
    linarith only [ha', hb, hl]
  have hOut (b : B) (hb : b ∉ smallBall f s) : Prod.mk b ⁻¹' F = ∅ := by
    ext a
    exact iff_false_intro fun ha => hb ha.1
  have h := prod_real_measure_le_of_sections ν μ F (smallBall f s) (by norm_num) hIn hOut
  simpa only [hSwap, H, div_eq_mul_inv, one_mul] using h

/-- A perturbation with uniformly controlled errors admits a realization that
preserves both an upper small-ball profile and one lower small-ball mass. -/
private theorem exists_profile_preserving_sample {A B : Type*} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : B → ℝ) (g : A → B → ℝ) {s L : ℝ} (hs : 0 < s) (hL : 0 < L)
    (center z : ℝ)
    (hprof : ∀ t ≥ s, ν.real (smallBall (fun b => f b - center) t) ≤ L * t)
    (hdev : ∀ b u, 0 < u → μ.real {a | u ≤ |g a b - f b|} ≤ s ^ 2 / (4 * u ^ 2)) :
    ∃ a, (∀ t ≥ s, ν.real (smallBall (fun b => g a b - center) t) ≤ 36 * L * t) ∧
      ν.real (smallBall (fun b => f b - z) s) / 2 ≤
        ν.real (smallBall (fun b => g a b - z) (2 * s)) := by
  let T (k : ℕ) := (2 : ℝ) ^ k * s
  let H (k : ℕ) : Set (A × B) := {p | |g p.1 p.2 - center| ≤ T k ∧ 2 * T k < |f p.2 - center|}
  let upperBad (k : ℕ) : Set A := {a | 16 * L * T k ≤ ν.real (Prod.mk a ⁻¹' H k)}
  let U := smallBall (fun b => f b - z) s
  let V (a : A) := smallBall (fun b => g a b - z) (2 * s)
  let G : Set (A × B) := {p | p.2 ∈ U ∧ p.2 ∉ V p.1}
  let lowerBad : Set A := {a | 0 < ν.real U ∧ ν.real U / 2 ≤ ν.real (Prod.mk a ⁻¹' G)}
  have hdev' (c : ℝ) (b : B) (t : ℝ) (ht : 0 < t) :
      μ.real {a | t ≤ |(g a b - c) - (f b - c)|} ≤ s ^ 2 / (4 * t ^ 2) := by
    simpa only [sub_sub_sub_cancel_right] using hdev b t ht
  have hT (k : ℕ) : s ≤ T k := by
    simpa only [T, one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)) hs.le
  have hUp (k : ℕ) : μ.real (upperBad k) ≤ (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ k := by
    have hJoint := upper_rounding_leakage μ ν (fun b => f b - center) (fun a b => g a b - center)
      hs hL (hT k) hprof (hdev' center)
    have hTk := hs.trans_le (hT k)
    apply (real_measure_sections_ge_le μ ν (H k) (show 0 < 16 * L * T k by positivity)).trans
    calc
      _ ≤ (2 * (L * s ^ 2 / T k)) / (16 * L * T k) :=
        div_le_div_of_nonneg_right hJoint (by positivity)
      _ = _ := by
        simp only [T, div_pow, one_pow]
        have hp : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
          norm_num
        rw [← hp]
        field_simp [hL.ne', hs.ne', pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
        ring
  have hUpAll : μ.real (⋃ k, upperBad k) ≤ 1 / 6 := by
    have h := measureReal_iUnion_le_geometric μ upperBad
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hUp
    norm_num at h ⊢
    exact h
  have hLow : μ.real lowerBad ≤ 1 / 2 := by
    by_cases hpos : 0 < ν.real U
    · have hG : (μ.prod ν).real G ≤ ν.real U / 4 := by
        simpa only [G, U, V, smallBall, Set.mem_ofPred_eq, not_le] using
          lower_rounding_loss_le μ ν (fun b => f b - z) (fun a b => g a b - z) hs (hdev' z)
      have heq : lowerBad = {a | ν.real U / 2 ≤ ν.real (Prod.mk a ⁻¹' G)} := by
        ext a
        simp [lowerBad, hpos]
      rw [heq]
      refine (real_measure_sections_ge_le μ ν G (by positivity : 0 < ν.real U / 2)).trans ?_
      calc
        _ ≤ (ν.real U / 4) / (ν.real U / 2) := div_le_div_of_nonneg_right hG (by positivity)
        _ = _ := by
          field_simp [hpos.ne']
          norm_num
    · have heq : lowerBad = ∅ := by ext a; simp [lowerBad, hpos]
      rw [heq, measureReal_empty]
      norm_num
  have hNotAll : (⋃ k, upperBad k) ∪ lowerBad ≠ Set.univ := by
    intro hall
    have h := measureReal_union_le (μ := μ) (⋃ k, upperBad k) lowerBad
    rw [hall, probReal_univ] at h
    linarith only [h, hUpAll, hLow]
  obtain ⟨a, ha⟩ := Set.nonempty_compl.mpr hNotAll
  have hupper (k : ℕ) : a ∉ upperBad k := fun h =>
    ha (Or.inl (Set.mem_iUnion.mpr ⟨k, h⟩))
  have hlower : a ∉ lowerBad := fun h => ha (Or.inr h)
  refine ⟨a, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, htk, hkt⟩ := exists_dyadic_ge_le_twice hs ht
    have hcover : smallBall (fun b => g a b - center) t ⊆
        smallBall (fun b => f b - center) (2 * T k) ∪ Prod.mk a ⁻¹' H k := by
      intro b hb
      by_cases h : b ∈ smallBall (fun b => f b - center) (2 * T k)
      · exact Or.inl h
      · exact Or.inr ⟨hb.trans htk, lt_of_not_ge h⟩
    have hlimit : ν.real (Prod.mk a ⁻¹' H k) ≤ 16 * L * T k :=
      le_of_lt (lt_of_not_ge (hupper k))
    have hscale : s ≤ 2 * T k := by linarith only [hT k, hs]
    calc
      _ ≤ ν.real (smallBall (fun b => f b - center) (2 * T k) ∪ Prod.mk a ⁻¹' H k) :=
        measureReal_mono hcover (measure_ne_top _ _)
      _ ≤ ν.real (smallBall (fun b => f b - center) (2 * T k)) + ν.real (Prod.mk a ⁻¹' H k) :=
        measureReal_union_le _ _
      _ ≤ 18 * L * T k := by nlinarith only [hprof _ hscale, hlimit]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hkt (show 0 ≤ 18 * L by positivity)
        linarith only [h]
  · by_cases hpos : 0 < ν.real U
    · have hmiss : ν.real (Prod.mk a ⁻¹' G) < ν.real U / 2 :=
        lt_of_not_ge fun h => hlower ⟨hpos, h⟩
      have hsub : U ⊆ V a ∪ Prod.mk a ⁻¹' G := by
        intro b hb
        by_cases h : b ∈ V a
        · exact Or.inl h
        · exact Or.inr ⟨hb, h⟩
      have h := (measureReal_mono hsub (measure_ne_top _ _)).trans
        (measureReal_union_le (μ := ν) (V a) (Prod.mk a ⁻¹' G))
      change ν.real U / 2 ≤ ν.real (V a)
      linarith only [h, hmiss]
    · have h := le_of_not_gt hpos
      linarith only [h, measureReal_nonneg (μ := ν) (s := V a)]

/-- Rounding preserves linear upper small-ball bounds and retains half of a
specified small-ball mass on doubling the radius. -/
theorem exists_roundedVector_preserving_small_balls {n : ℕ} (hn : 0 < n)
    (ν : Measure (Fin n → Bool)) [IsProbabilityMeasure ν]
    (v : Fin n → ℝ) (center z : ℝ) {L : ℝ} (hL : 0 < L)
    (hprof : ∀ t ≥ Real.sqrt (n : ℝ), ν.real {b | |signSum v b - center| ≤ t} ≤ L * t) :
    ∃ w : Fin n → ℤ, (∀ i, |(w i : ℝ) - v i| ≤ 1) ∧
      (∀ t ≥ Real.sqrt (n : ℝ), ν.real {b | |signSum (fun i => (w i : ℝ)) b - center| ≤ t}
        ≤ 36 * L * t) ∧
      ν.real {b | |signSum v b - z| ≤ Real.sqrt (n : ℝ)} / 2 ≤
        ν.real {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)} := by
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  let g (a b : Fin n → Bool) := signSum (fun i => (roundedVector v a i : ℝ)) b
  have hdev (b : Fin n → Bool) (t : ℝ) (ht : 0 < t) :
      (roundingLaw v).real {a | t ≤ |g a b - signSum v b|} ≤
        Real.sqrt (n : ℝ) ^ 2 / (4 * t ^ 2) := by
    have heq (u : Fin n → Bool) : g u b - signSum v b =
        ∑ i, realSigns b i * ((roundedVector v u i : ℝ) - v i) := by
      simp only [g, signSum, realSigns, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [heq, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact rounding_error_tail_le v (realSigns b) (fun i => by cases h : b i <;> simp [realSigns, h]) ht
  obtain ⟨b, hUp, hLo⟩ := exists_profile_preserving_sample (roundingLaw v) ν (signSum v) g
    hs hL center z hprof hdev
  exact ⟨roundedVector v b, roundedVector_coordinate_bound v b, hUp, hLo⟩

end BooleanThreshold
