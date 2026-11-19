module

public import BooleanThreshold.JSSConditionalInversion
public import BooleanThreshold.JSSConditionalStartingKernel
public import BooleanThreshold.JSSConditionalFejerFourier
public import BooleanThreshold.JSSConditionalSmallN
public import BooleanThreshold.JSSConditionalPermute

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

/-- Integer coefficient arrays whose cyclic slice average reaches the given
height at some translate. -/
@[expose] noncomputable def largeCyclicSliceBox {n P : ℕ} [NeZero P]
    (A : Fin n → Finset ℤ) (m : Fin (n + 1)) (g : ZMod P → ℝ) (h : ℝ) : Finset (Fin n → ℤ) :=
  open Classical in
  (Fintype.piFinset A).filter fun w => ∃ t : ZMod P,
    h ≤ sliceAverage (cyclicIntegerCoordinates (P := P) w) g n m.val t

/-- Simultaneously reindexing the selected signs and the coefficients leaves
each cyclic slice average unchanged. -/
theorem cyclicIntegerCoordinates_sliceAverage_comp {n P : ℕ}
    (e : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (w : Fin n → ℤ) (g : ZMod P → ℝ) (t : ZMod P) :
    sliceAverage (cyclicIntegerCoordinates (w ∘ e)) g n m.val t =
      sliceAverage (cyclicIntegerCoordinates w) g n m.val t := by
  classical
  let μ := uniformOn (signSlice n m)
  let E (b : Fin n → Bool) := b ∘ e
  let F (b : Fin n → Bool) := g (t + ∑ i ∈ Finset.univ.filter (fun i => b i), ((w ∘ e) i : ZMod P))
  have hE : Measurable E := measurable_of_finite _
  have hmap : μ.map E = μ := by
    ext S hS
    rw [Measure.map_apply hE hS]
    exact uniformOn_signSlice_comp_preimage e m S
  have hsum (b : Fin n → Bool) :
      (∑ i ∈ Finset.univ.filter (fun i => E b i), ((w ∘ e) i : ZMod P)) =
        ∑ i ∈ Finset.univ.filter (fun i => b i), (w i : ZMod P) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [← integral_signSlice_eq_sliceAverage m (cyclicIntegerCoordinates (w ∘ e)) g t,
    ← integral_signSlice_eq_sliceAverage m (cyclicIntegerCoordinates w) g t]
  simp only [cyclicIntegerCoordinates, Fin.isLt, dite_eq_left, Fin.eta]
  change (∫ b, F b ∂μ) = _
  calc
    _ = ∫ b, F b ∂(μ.map E) := by rw [hmap]
    _ = ∫ b, F (E b) ∂μ :=
      integral_map hE.aemeasurable (measurable_of_finite F).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun b => congrArg (fun u => g (t + u)) (hsum b))

private theorem mem_largeCyclicSliceBox_comp {n P : ℕ} [NeZero P]
    (e : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (A : Fin n → Finset ℤ)
    (w : Fin n → ℤ) (g : ZMod P → ℝ) (h : ℝ) :
    w ∘ e ∈ largeCyclicSliceBox (A ∘ e) m g h ↔ w ∈ largeCyclicSliceBox A m g h := by
  simp only [largeCyclicSliceBox, Finset.mem_filter, Fintype.mem_piFinset]
  apply and_congr
  · exact ⟨fun f i => by simpa using f (e.symm i), fun f i => f (e i)⟩
  · exact exists_congr fun t => Iff.of_eq
      (congrArg (fun r : ℝ => h ≤ r) (cyclicIntegerCoordinates_sliceAverage_comp e m w g t))

/-- Permuting the coordinate intervals preserves the count of large cyclic
slice averages exactly. -/
theorem largeCyclicSliceBox_card_comp {n P : ℕ} [NeZero P]
    (e : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (A : Fin n → Finset ℤ)
    (g : ZMod P → ℝ) (h : ℝ) :
    (largeCyclicSliceBox (A ∘ e) m g h).card = (largeCyclicSliceBox A m g h).card := by
  symm
  let E : (Fin n → ℤ) ≃ (Fin n → ℤ) := Equiv.arrowCongr e.symm (Equiv.refl ℤ)
  refine Finset.card_bij' (fun w _ => E w) (fun w _ => E.symm w) ?_ ?_
    (fun w _ => E.symm_apply_apply w) (fun w _ => E.apply_symm_apply w)
  · intro w hw
    exact (mem_largeCyclicSliceBox_comp e m A w g h).mpr hw
  · intro w hw
    apply (mem_largeCyclicSliceBox_comp e m A (E.symm w) g h).mp
    change E (E.symm w) ∈ largeCyclicSliceBox (A ∘ e) m g h
    rwa [E.apply_symm_apply]

/-- The cyclic kernel form of fixed-slice counting. The slice width and
threshold are independent of the requested exponential rate. -/
@[expose] def CyclicBandSliceCountEstimate : Prop :=
  ∀ (α : ℝ) (B : ℕ), 0 < α → α < 1 / 4 → 4 ≤ B →
    ∃ γ > (0 : ℝ), ∃ T > (0 : ℝ), ∀ M ≥ (0 : ℝ), ∃ b > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ (N P : ℕ) [NeZero P],
        Real.sqrt (n : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ (5 / 3 : ℝ) ^ n →
        4 * n ^ 2 * N < P → P ≤ 2 ^ n →
        ∀ g : ZMod P → ℝ, (∀ t, 0 ≤ g t) → (∑ t, g t) ≤ 1 →
          (∀ k : ZMod P, b * (P : ℝ) < (k.valMinAbs.natAbs : ℝ) →
            ZMod.dft (fun t => (g t : ℂ)) k = 0) →
        ∀ A : Fin n → Finset ℤ, oppositeBandBox n N B α A →
        ∀ m : Fin (n + 1), |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ) →
          ((largeCyclicSliceBox A m g (T / ((N : ℝ) * Real.sqrt (n : ℝ)))).card : ℝ) ≤
            Real.exp (-M * (n : ℝ)) * (((B : ℝ) + 1) * (N : ℝ)) ^ n

private theorem eventually_cyclic_modulus_le_two_pow :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, (N : ℝ) ≤ (5 / 3 : ℝ) ^ n →
      4 * n ^ 2 * N + 1 ≤ 2 ^ n := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1 : ℝ) < 6 / 5 by norm_num)
  filter_upwards [eventually_ge_atTop 1, hlim.eventually_le_const (show (0 : ℝ) < 1 / 5 by norm_num)]
    with n hn hdiv
  intro N hN
  have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly : (5 : ℝ) * (n : ℝ) ^ 2 ≤ (6 / 5 : ℝ) ^ n := by
    have h := (div_le_iff₀ (show 0 < (6 / 5 : ℝ) ^ n by positivity)).mp hdiv
    linarith only [h]
  have hpow : (1 : ℝ) ≤ (5 / 3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hs : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ h₁
  have h : (4 : ℝ) * (n : ℝ) ^ 2 * (N : ℝ) + 1 ≤ (2 : ℝ) ^ n := calc
    _ ≤ (4 : ℝ) * (n : ℝ) ^ 2 * (5 / 3 : ℝ) ^ n + (n : ℝ) ^ 2 * (5 / 3 : ℝ) ^ n :=
      add_le_add (mul_le_mul_of_nonneg_left hN (by positivity)) (one_le_mul_of_one_le_of_one_le hs hpow)
    _ = 5 * (n : ℝ) ^ 2 * (5 / 3 : ℝ) ^ n := by ring
    _ ≤ (6 / 5 : ℝ) ^ n * (5 / 3 : ℝ) ^ n := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num
  exact_mod_cast h

/-- Localizing a Fejér kernel on the cycle recovers the integer fixed-slice
estimate. At short scales the separated-pair estimate suffices directly. -/
theorem oppositeBandSliceEstimate_of_cyclic
    (hCyclic : CyclicBandSliceCountEstimate) : OppositeBandSliceEstimate := by
  classical
  intro α B hα hα' hB
  obtain ⟨γ₀, hγ₀, T, hT, hcyc⟩ := hCyclic α B hα hα' hB
  obtain ⟨C, hC, hsmall⟩ := oppositeBand_signSlice_smallBall_smallN_eventually
    (η := 1 / 4) (by norm_num) hα
  let H := 1 + C + 512 * T
  let γ := min γ₀ (1 / 4)
  have hγ : 0 < γ := lt_min hγ₀ (by norm_num)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH₁ : C < H := by dsimp [H]; linarith
  have hH₂ : 512 * T ≤ H := by dsimp [H]; linarith
  refine ⟨γ, hγ, H, hH, fun M hM => ?_⟩
  obtain ⟨b, hb, hlarge⟩ := hcyc M hM
  filter_upwards [hsmall, hlarge, eventually_exists_starting_fejer_bandwidth hb,
    eventually_cyclic_modulus_le_two_pow, eventually_ge_atTop 1]
    with n hsmalln hlargen hker hPbound hn
  intro N hN hNmax A hA m hm
  have hn' : 0 < n := by omega
  have hR : 0 < Real.sqrt (n : ℝ) := by positivity
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  by_cases hNs : (N : ℝ) ≤ Real.sqrt (n : ℝ)
  · have hm₀ : (1 / 4 : ℝ) * (n : ℝ) ≤ (m.val : ℝ) := by
      have h := mul_le_mul_of_nonneg_right
        (show γ ≤ 1 / 4 from min_le_right _ _) (Nat.cast_nonneg n)
      have hh := (abs_le.mp hm).1
      linarith only [h, hh]
    have hm₁ : (m.val : ℝ) ≤ (1 - 1 / 4) * (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_right
        (show γ ≤ 1 / 4 from min_le_right _ _) (Nat.cast_nonneg n)
      have hh := (abs_le.mp hm).2
      linarith only [h, hh]
    have he : largeSliceBox n m A (H / (N : ℝ)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hwA, z, hwz⟩ := Finset.mem_filter.mp hw
      have hw' := hsmalln N B A hN hNs hA m hm₀ hm₁ w (Fintype.mem_piFinset.mp hwA) z
      exact (not_le_of_gt (div_lt_div_of_pos_right hH₁ hN')) (hwz.trans hw')
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  · let P := 4 * n ^ 2 * N + 1
    let : NeZero P := ⟨by dsimp [P]; omega⟩
    have hP : 4 * n ^ 2 * N < P := Nat.lt_succ_self _
    have hPmin : 4 * n ^ 2 ≤ P :=
      (Nat.le_mul_of_pos_right _ hN).trans hP.le
    obtain ⟨W, hW, hWP, hbW, hWmin⟩ := hker P hPmin
    let g := fejerKernel W (P := P)
    let h := T / ((N : ℝ) * Real.sqrt (n : ℝ))
    have hband (k : ZMod P) (hk : b * (P : ℝ) < (k.valMinAbs.natAbs : ℝ)) :
        ZMod.dft (fun t => (g t : ℂ)) k = 0 :=
      dft_fejerKernel_eq_zero_of_band hW hWP k (by exact_mod_cast (hbW.trans_lt hk).le)
    have hm' : |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ₀ * (n : ℝ) :=
      hm.trans (by gcongr; exact min_le_left _ _)
    have hcount := hlargen N P (le_of_not_ge hNs) hNmax hP (hPbound N hNmax) g
      (fejerKernel_nonneg W) (fejerKernel_sum_eq_one hW hWP).le hband A hA m hm'
    refine (show (((largeSliceBox n m A (H / (N : ℝ))).card : ℝ)) ≤
      ((largeCyclicSliceBox A m g h).card : ℝ) from ?_).trans hcount
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwA, z, hz⟩ := Finset.mem_filter.mp hw
    obtain ⟨t, ht⟩ := exists_fejer_sliceAverage_ge_smallBall hn' hWmin m w z
    refine Finset.mem_filter.mpr ⟨hwA, t, ?_⟩
    have he : h = ((512 * T) / (N : ℝ)) / (512 * Real.sqrt (n : ℝ)) := by
      dsimp [h]
      field_simp
    rw [he]
    exact (div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right hH₂ hN'.le).trans hz)
      (by positivity)).trans ht

end BooleanThreshold
