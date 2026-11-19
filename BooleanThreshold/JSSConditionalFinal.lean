module

public import BooleanThreshold.JSSConditionalBlockWeights
public import BooleanThreshold.JSSConditionalCyclicAssemble
public import BooleanThreshold.JSSConditionalOrderedPreprocess
public import BooleanThreshold.JSSConditionalSuffixDecrement

public noncomputable section

open Filter Finset
open scoped BigOperators Classical Topology ZMod

namespace BooleanThreshold

private theorem cyclic_frequency_abs {P : ℕ} (k : ZMod P) :
    |(k.valMinAbs : ℝ) / (P : ℝ)| = (k.valMinAbs.natAbs : ℝ) / (P : ℝ) := by
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) P), ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]

private theorem eventually_const_mul_exp_neg_lt_one (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, A * Real.exp (-c * (n : ℝ)) < 1 := by
  have hx : Tendsto (fun n : ℕ => Real.exp (-(c * (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_natCast_atTop_atTop)
  have h := (tendsto_const_nhds (x := A)).mul hx
  rw [mul_zero] at h
  simpa only [neg_mul] using h.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)

private theorem absorb_slice_weight_union {n b : ℕ} (hn : 1 ≤ n) (hb : b ≤ n) (M : ℝ) :
    2 * ((b : ℝ) + 1) * Real.exp (-(M + 2) * (n : ℝ)) ≤ Real.exp (-M * (n : ℝ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb' : (b : ℝ) ≤ n := by exact_mod_cast hb
  have he := Real.add_one_le_exp (n : ℝ)
  calc
    _ ≤ Real.exp (n : ℝ) * Real.exp (n : ℝ) * Real.exp (-(M + 2) * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The fixed-slice counting estimate, obtained by preprocessing a nearly
full prefix and smoothing with the independent shifts of a fresh suffix. -/
theorem cyclicBandSliceCountEstimate : CyclicBandSliceCountEstimate := by
  intro α B hα _ _
  obtain ⟨η, hη, R, hR, hPre⟩ := eventual_prefix_preprocessing_on_opposite_band hα B
  obtain ⟨c, hc, σ, hσ, γ, hγ, hγmax, hgeom⟩ := eventually_small_suffix_pairs hη hη
  obtain ⟨cTail, hcTail, hTail⟩ :=
    sliceSplitWeight_bad_count_eventually (η := 1 / 4) (by norm_num) hσ
  let T := 24 * R + 4
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨γ, hγ, T, hT, fun M hM => ?_⟩
  have hRate : 0 ≤ M + 2 := by linarith
  obtain ⟨A, hA, hPreCount⟩ := hPre (M + 2) hRate
  obtain ⟨ω, hω, hSuffix⟩ := eventually_cyclic_slice_suffix_decrement
    (η := 1 / 16) (zero_le_one.trans hA) hR.le (by norm_num) hσ hRate (B + 1) (by omega)
  refine ⟨ω, hω, ?_⟩
  filter_upwards [hPreCount, hSuffix, hgeom, hTail, eventually_const_mul_exp_neg_lt_one A hcTail,
    eventually_ge_atTop 1] with n hnPre hnSuffix hnGeom hnTail hnSmall hn
  intro N P _ hN hNmax hP hPmax g hg hmass hband W hW m hm
  let k := ⌊c * (n : ℝ)⌋₊
  let b := 2 * k
  let a := n - b
  obtain ⟨hkn, hbn, hbη, _, ha, hFeas⟩ := hnGeom
  have hsum : a + b = n := Nat.sub_add_cancel hbn
  have haFull : (1 - η) * (n : ℝ) ≤ (a : ℝ) := by
    dsimp [a]
    rw [Nat.cast_sub hbn]
    linarith only [hbη]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hN' : 0 < (N : ℝ) := (Real.sqrt_pos.mpr hn').trans_le hN
  have hN₀ : 0 < N := by exact_mod_cast hN'
  have hNP : N ≤ P := by
    have hp : 0 < n ^ 2 := pow_pos (by omega) _
    have h := Nat.mul_le_mul_right N (show 1 ≤ 4 * n ^ 2 by omega)
    simpa only [one_mul] using h.trans hP.le
  have hFeasible (j : ℕ) (hj : j ≤ b) : j ≤ m.val ∧ m.val - j ≤ a :=
    ⟨(hFeas m.val hm j hj).1, (hFeas m.val hm j hj).2.1⟩
  have hpreWeight (j : ℕ) (hj : j ≤ b) :
      |2 * ((m.val - j : ℕ) : ℝ) - (a : ℝ)| ≤ 2 * η * (a : ℝ) :=
    (hFeas m.val hm j hj).2.2.trans (by linarith [mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) a)])
  obtain ⟨π, hPrefix⟩ :=
    hnPre a b hsum (by linarith only [ha]) haFull N P hN₀ hNmax hP hPmax W hW
  let W' := W ∘ π
  let scale := (N : ℝ) * Real.sqrt (n : ℝ)
  let U := A / scale
  let V := (24 * R + 2) / scale
  let Good (j : ℕ) := (1 / 16 : ℝ) * (b : ℝ) ≤ (j : ℝ) ∧
    (1 / 16 : ℝ) * (b : ℝ) ≤ ((b - j : ℕ) : ℝ)
  let ε := Real.exp (-(M + 2) * (n : ℝ))
  let D := (B + 1) * N
  have hScale : 0 < scale := by dsimp [scale]; positivity
  have hLow : (1 / 4 : ℝ) * (n : ℝ) ≤ (m.val : ℝ) := by
    have hc := mul_le_mul_of_nonneg_right hγmax hn'.le
    linarith only [hc, (abs_le.mp hm).1, hn']
  have hHigh : (m.val : ℝ) ≤ (1 - (1 / 4 : ℝ)) * (n : ℝ) := by
    have hc := mul_le_mul_of_nonneg_right hγmax hn'.le
    linarith only [hc, (abs_le.mp hm).2, hn']
  have hbLinear : σ * (n : ℝ) ≤ (b : ℝ) := hkn.trans (by
    dsimp [b]
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) k])
  have hweight : (∑ j ∈ range (m.val + 1),
      @ite ℝ (Good j) (Classical.propDecidable (Good j)) 0 (sliceSplitWeight a b m.val j)) ≤
      Real.exp (-cTail * (n : ℝ)) := by
    have h := hnTail a b m.val hsum hbLinear hLow hHigh
    norm_num at h
    have heq (j : ℕ) :
        @ite ℝ (Good j) (Classical.propDecidable (Good j)) 0 (sliceSplitWeight a b m.val j) =
          if (j : ℝ) < (1 / 16 : ℝ) * (b : ℝ) ∨
              ((b - j : ℕ) : ℝ) < (1 / 16 : ℝ) * (b : ℝ)
          then sliceSplitWeight a b m.val j else 0 := by
      have hbad : ((j : ℝ) < (1 / 16 : ℝ) * (b : ℝ) ∨
          ((b - j : ℕ) : ℝ) < (1 / 16 : ℝ) * (b : ℝ)) ↔ ¬ Good j := by
        simp only [Good, not_and_or, not_le]
      by_cases hg : Good j
      · rw [ite_eq_left hg, ite_eq_right (fun h => hbad.mp h hg)]
      · rw [ite_eq_right hg, ite_eq_left (hbad.mpr hg)]
    simp_rw [heq]
    simpa only [neg_mul] using h
  have hThreshold : V + U * Real.exp (-cTail * (n : ℝ)) < T / scale := by
    dsimp [V, U, T]
    rw [div_mul_eq_mul_div, ← add_div]
    apply div_lt_div_of_pos_right _ hScale
    linarith only [hnSmall]
  rw [← largeCyclicSliceBox_card_comp π m W g (T / scale)]
  refine (card_largeCyclicSliceBox_le_of_prefix_suffix (D := D) (U := U) (V := V)
    (T := T / scale) (ε := ε) (β := Real.exp (-cTail * (n : ℝ))) hsum W'
    (fun i => (hW.1 (π i)).2.2.1) g m (by dsimp [U]; positivity)
    (by dsimp [V]; positivity) (by dsimp [ε]; positivity)
    hThreshold Good hweight ?_ ?_).trans ?_
  · intro j hj
    have h := (hPrefix (m.val - j) (hFeasible j hj).2 (hpreWeight j hj) g hg hmass).1
    simp only [highSliceAverages, cyclicIntegerCoordinates_eq_sliceCoefficientArray, W', U, scale,
      ε, D, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h ⊢
    exact card_filter_le_redecide _ _ h
  · intro x hx j hj hjGood hCap
    let u := m.val - j
    let f := sliceAverage (cyclicIntegerCoordinates (P := P) x) g a u
    have hu : u ≤ a := (hFeasible j hj).2
    have hf : ∀ t, 0 ≤ f t := sliceAverage_nonneg _ _ hg _ _
    have hfMass : (∑ t, f t) ≤ 1 := by
      rw [show (∑ t, f t) = ∑ t, g t from sum_sliceAverage_eq_sum _ _ hu]
      exact hmass
    have hfBand (l : ZMod P) (hl : ω < |(l.valMinAbs : ℝ) / (P : ℝ)|) :
        𝓕 (fun t => (f t : ℂ)) l = 0 := by
      apply dft_sliceAverage_eq_zero _ _ _ _ _
      apply hband
      rw [cyclic_frequency_abs] at hl
      exact (lt_div_iff₀ (Nat.cast_pos.mpr (NeZero.pos P))).mp hl
    have hlocal := (hPrefix u hu (hpreWeight j hj) g hg hmass).2 x hx
    have hjLo : (1 / 16 : ℝ) * (2 * (k : ℝ)) ≤ (j : ℝ) := by
      simpa only [b, Nat.cast_mul, Nat.cast_ofNat] using hjGood.1
    have hjHi : (j : ℝ) ≤ (1 - (1 / 16 : ℝ)) * (2 * (k : ℝ)) := by
      have h := hjGood.2
      rw [Nat.cast_sub hj] at h
      dsimp [b] at h
      push_cast at h
      linarith only [h]
    have hsufBox (i : Fin b) :
        (∃ l u : ℤ, sliceTupleSuffix hsum W' i = Ico l u) ∧
          N ≤ (sliceTupleSuffix hsum W' i).card ∧ (sliceTupleSuffix hsum W' i).card ≤ D := by
      obtain ⟨hi, hLo, hHi, _⟩ := hW.1 (π (Fin.cast hsum (i.natAdd a)))
      have hLo' : 2 * N + 1 ≤ (sliceTupleSuffix hsum W' i).card := hLo
      exact ⟨hi, by omega, hHi⟩
    have hBound := hnSuffix N P hN hNP hPmax f hf hfMass hCap hlocal hfBand k hkn hbn
      ⟨j, Nat.lt_succ_of_le hj⟩ hjLo hjHi (sliceTupleSuffix hsum W') hsufBox
    simp only [D, Nat.cast_mul, cyclicIntegerCoordinates_eq_sliceCoefficientArray,
      sliceCoefficientArray, ε, V, scale, f, u, b] at hBound ⊢
    exact card_filter_le_redecide _ _ hBound
  · have hErr := absorb_slice_weight_union (b := b) hn hbn M
    simpa only [D, Nat.cast_mul, Nat.cast_add, Nat.cast_one, ε] using
      mul_le_mul_of_nonneg_right hErr (show 0 ≤ (D : ℝ) ^ n by positivity)

/-- The fixed-weight inverse estimate needed for the conditional normal bound. -/
theorem oppositeBandSliceEstimate : OppositeBandSliceEstimate :=
  oppositeBandSliceEstimate_of_cyclic cyclicBandSliceCountEstimate

end BooleanThreshold
