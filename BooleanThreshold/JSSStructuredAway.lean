module

public import BooleanThreshold.JSSStructuredSigns
public import BooleanThreshold.JSSStructuredAtoms
public import BooleanThreshold.JSSCorankSmallBall

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

private theorem sum_sq_complement {n : ℕ} (a : Fin n → ℝ) (I : Finset (Fin n)) :
    squaredNorm a = (∑ i ∈ I, a i ^ 2) + ∑ i ∈ Finset.univ \ I, a i ^ 2 := by
  rw [add_comm, Finset.sum_sdiff (Finset.subset_univ I)]
  rfl

private theorem exists_orientation (x : ℝ) :
    ∃ b : Bool, ∀ r : ℝ, ((if b then (-1 : ℝ) else 1) - r * x) ^ 2 = (1 - r * |x|) ^ 2 := by
  by_cases h : 0 ≤ x
  · exact ⟨false, fun r => by simp [abs_of_nonneg h]⟩
  · refine ⟨true, fun r => ?_⟩
    simp only [ite_true, abs_of_nonpos (le_of_not_ge h)]
    ring

private theorem dist_sq_to_signedBasis {n : ℕ} (a : Fin n → ℝ) (ha : squaredNorm a = 1)
    (i : Fin n) : ∃ b, squaredNorm (signedBasis b i - a) ≤
      2 * ∑ k ∈ Finset.univ \ {i}, a k ^ 2 := by
  let t := ∑ k ∈ Finset.univ \ ({i} : Finset (Fin n)), a k ^ 2
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmass : a i ^ 2 + t = 1 := by
    simpa [t, ha] using (sum_sq_complement a {i}).symm
  have hx : |a i| ≤ 1 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by
    rw [sq_abs]
    linarith only [hmass, ht])
  obtain ⟨b, hb⟩ := exists_orientation (a i)
  refine ⟨b, ?_⟩
  let v := signedBasis b i - a
  change squaredNorm v ≤ 2 * t
  rw [sum_sq_complement v {i}, Finset.sum_singleton]
  have hv : v i ^ 2 = (1 - |a i|) ^ 2 := by
    rw [show v i = (if b then -1 else 1) - a i by simp [v, signedBasis_apply]]
    simpa only [one_mul] using hb 1
  have hvt : (∑ k ∈ Finset.univ \ {i}, v k ^ 2) = t := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := by simpa using (Finset.mem_sdiff.mp hk).2
    simp [v, signedBasis_apply, hki]
  rw [hv, hvt]
  have hmass' : |a i| ^ 2 + t = 1 := by rwa [sq_abs]
  nlinarith only [hmass', mul_nonneg (abs_nonneg (a i)) (sub_nonneg.mpr hx)]

private theorem dist_sq_to_signedPair {n : ℕ} (a : Fin n → ℝ) (ha : squaredNorm a = 1)
    {i j : Fin n} (hij : i ≠ j) : ∃ b d,
      squaredNorm (signedBasis b i + signedBasis d j - Real.sqrt 2 • a) ≤
        4 * (∑ k ∈ Finset.univ \ {i, j}, a k ^ 2) + 2 * (|a i| - |a j|) ^ 2 := by
  let t := ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), a k ^ 2
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmass : |a i| ^ 2 + |a j| ^ 2 + t = 1 := by
    simpa only [Finset.sum_pair hij, sq_abs, ha] using (sum_sq_complement a {i, j}).symm
  obtain ⟨b, hb⟩ := exists_orientation (a i)
  obtain ⟨d, hd⟩ := exists_orientation (a j)
  refine ⟨b, d, ?_⟩
  let r := Real.sqrt 2
  have hr : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let v := signedBasis b i + signedBasis d j - r • a
  change squaredNorm v ≤ 4 * t + 2 * (|a i| - |a j|) ^ 2
  rw [sum_sq_complement v {i, j}, Finset.sum_pair hij]
  have hvi : v i ^ 2 = (1 - r * |a i|) ^ 2 := by
    simpa [v, signedBasis_apply, hij, Pi.smul_apply, smul_eq_mul] using hb r
  have hvj : v j ^ 2 = (1 - r * |a j|) ^ 2 := by
    simpa [v, signedBasis_apply, hij.symm, Pi.smul_apply, smul_eq_mul] using hd r
  have hvt : (∑ k ∈ Finset.univ \ {i, j}, v k ^ 2) = 2 * t := by
    simp only [t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≠ i ∧ k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
    simp [v, signedBasis_apply, hk'.1, hk'.2, Pi.smul_apply, smul_eq_mul, mul_pow, hr]
  rw [hvi, hvj, hvt]
  let z := r * (|a i| + |a j|)
  have hz : 0 ≤ z := by dsimp [z, r]; positivity
  have hzsq : z ^ 2 = 4 - 4 * t - 2 * (|a i| - |a j|) ^ 2 := by
    dsimp only [z]
    rw [mul_pow, hr]
    nlinarith only [hmass]
  have hz₂ : z ≤ 2 := (sq_le_sq₀ hz (by norm_num)).mp (by
    rw [hzsq]
    nlinarith only [ht, sq_nonneg (|a i| - |a j|)])
  have hEq : (1 - r * |a i|) ^ 2 + (1 - r * |a j|) ^ 2 + 2 * t = 4 - 2 * z := by
    calc
      _ = 2 - 2 * z + r ^ 2 * (|a i| ^ 2 + |a j| ^ 2) + 2 * t := by dsimp [z]; ring
      _ = _ := by rw [hr]; linarith only [hmass]
  rw [hEq]
  nlinarith only [hzsq, mul_nonneg hz (sub_nonneg.mpr hz₂)]

private theorem signSum_small_ball_le_of_scaled_diffuse {n : ℕ} (a : Fin n → ℝ)
    (I : Finset (Fin n)) {η : ℝ} (hη : 0 < η) (hmass : η ^ 2 ≤ ∑ i ∈ I, a i ^ 2)
    (hsmall : ∀ i ∈ I, |a i| ≤ η / 100) :
    (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ η / 100} ≤ 7 / 16 := by
  let b : Fin n → ℝ := fun i => a i / η
  have hb : 1 ≤ ∑ i ∈ I, b i ^ 2 := by
    simp only [b, div_pow, ← Finset.sum_div]
    rw [le_div_iff₀ (by positivity), one_mul]
    exact hmass
  have hbsmall (i : Fin n) (hi : i ∈ I) : |b i| ≤ 1 / 100 := by
    dsimp only [b]
    rw [abs_div, abs_of_pos hη, div_le_iff₀ hη]
    exact (hsmall i hi).trans_eq (by ring)
  refine (measureReal_mono (s₂ := {x | |signSum b x| ≤ 1 / 100}) ?_).trans
    (signSum_small_ball_le_of_diffuse_mass b I hb hbsmall)
  intro x hx
  have hs : signSum b x = signSum a x / η := by
    simp only [signSum, b, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change |signSum a x| ≤ η / 100 at hx
  change |signSum b x| ≤ 1 / 100
  rw [hs, abs_div, abs_of_pos hη, div_le_iff₀ hη]
  exact hx.trans_eq (by ring)

/-- A unit sign sum away from the signed coordinate vectors and signed
two-coordinate vectors has small-ball probability at most `7/16`. -/
theorem exists_signUnit_small_ball_away {ε : ℝ} (hε : 0 < ε) :
    ∃ θ > (0 : ℝ), ∀ (n : ℕ) (a : Fin n → ℝ), squaredNorm a = 1 →
      (∀ i b, ε ^ 2 < squaredNorm (signedBasis b i - a)) →
      (∀ i j : Fin n, i ≠ j → ∀ b d,
        ε ^ 2 < squaredNorm (signedBasis b i + signedBasis d j - Real.sqrt 2 • a)) →
      uniformOn Set.univ {x : Fin n → Bool | |signSum a x| ≤ θ} ≤ 7 / 16 := by
  classical
  let η := min (ε / 4) (1 / 4)
  let θ := η / 100
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hη₁ : η ≤ 1 / 4 := min_le_right _ _
  have hηε₂ := pow_le_pow_left₀ hη.le hηε 2
  have hη₁₂ := pow_le_pow_left₀ hη.le hη₁ 2
  refine ⟨θ, hθ, fun n a ha hbasis hpair => ?_⟩
  let I : Finset (Fin n) := Finset.univ.filter fun i => θ < |a i|
  let t := ∑ k ∈ Finset.univ \ I, a k ^ 2
  have hreal : (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ θ} ≤ 7 / 16 := by
    by_cases htail : η ^ 2 ≤ t
    · exact signSum_small_ball_le_of_scaled_diffuse a (Finset.univ \ I) hη htail (by
        intro k hk
        simpa [I] using (Finset.mem_sdiff.mp hk).2)
    have htail' : t < η ^ 2 := lt_of_not_ge htail
    by_cases h₃ : 3 ≤ I.card
    · have hr := ENNReal.toReal_mono (show (3 / 8 : ℝ≥0∞) ≠ ∞ from ENNReal.div_ne_top (by simp) (by simp))
        (uniformOn_signSum_smallBall_le_three_eighths a h₃ 0)
      simp only [sub_zero, ENNReal.toReal_div, ENNReal.toReal_ofNat] at hr
      exact hr.trans (by norm_num)
    have hcard : I.card = 0 ∨ I.card = 1 ∨ I.card = 2 := by omega
    rcases hcard with h0 | h1 | h2
    · have hI := Finset.card_eq_zero.mp h0
      have ht : t = 1 := by simpa [t, hI, squaredNorm] using ha
      linarith only [ht, htail', hη₁₂]
    · obtain ⟨i, hI⟩ := Finset.card_eq_one.mp h1
      obtain ⟨b, hz⟩ := dist_sq_to_signedBasis a ha i
      have ht : squaredNorm (signedBasis b i - a) ≤ 2 * t := by simpa only [t, hI] using hz
      nlinarith only [hbasis i b, ht, htail', hηε₂, sq_nonneg ε]
    · obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.mp h2
      by_cases hg : θ < |(|a i| - |a j|)|
      · have hi : θ < |a i| := (Finset.mem_filter.mp (show i ∈ I by simp [hI])).2
        have hj : θ < |a j| := (Finset.mem_filter.mp (show j ∈ I by simp [hI])).2
        exact (signSum_small_ball_le_of_unequal_pair a hij hi hj hg).trans (by norm_num)
      · obtain ⟨b, d, hz⟩ := dist_sq_to_signedPair a ha hij
        have ht : squaredNorm (signedBasis b i + signedBasis d j - Real.sqrt 2 • a) ≤
            4 * t + 2 * (|a i| - |a j|) ^ 2 := by simpa only [t, hI] using hz
        have hg₂ := pow_le_pow_left₀ (abs_nonneg _) (le_of_not_gt hg) 2
        rw [sq_abs] at hg₂
        dsimp [θ] at hg₂
        nlinarith only [hpair i j hij b d, ht, htail', hg₂, hηε₂, sq_nonneg ε]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (ENNReal.div_ne_top (by simp) (by simp))).mp (by
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ← measureReal_def] using hreal)

end BooleanThreshold
