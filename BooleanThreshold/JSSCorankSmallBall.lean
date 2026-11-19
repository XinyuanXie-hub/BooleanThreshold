module

public import BooleanThreshold.JSSConditionalTail
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Logic.Equiv.Bool

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanThreshold

private theorem signSum_cos_average {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    (∑ x : Fin n → Bool, Real.cos (t * signSum a x)) / Fintype.card (Fin n → Bool) =
      ∏ i, Real.cos (t * a i) := by
  classical
  let g (i : Fin n) (b : Bool) :=
    Complex.exp ((↑(t * (a i * (if b then 1 else -1))) : ℂ) * Complex.I)
  have hsum (x : Fin n → Bool) :
      Complex.exp ((↑(t * signSum a x) : ℂ) * Complex.I) = ∏ i, g i (x i) := by
    simp only [signSum, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    rfl
  have hprod : (∑ x : Fin n → Bool, Complex.exp ((↑(t * signSum a x) : ℂ) * Complex.I)) =
      ∏ i, ∑ b : Bool, g i b := by
    simp only [hsum, Fintype.prod_sum]
  have hg (i) : (∑ b : Bool, g i b) = (↑(2 * Real.cos (t * a i)) : ℂ) := by
    simp [g, Complex.exp_ofReal_mul_I, two_mul]
    ring
  have hreal := congrArg Complex.re hprod
  simp only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, hg, ← Complex.ofReal_prod,
    Complex.ofReal_re] at hreal
  rw [hreal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_pi_const, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_cancel_left₀ _ (by positivity)

private theorem cos_le_exp_neg_sq {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ Real.cos x ∧ Real.cos x ≤ Real.exp (-x ^ 2 / 8) := by
  have hsq := (sq_le_sq₀ (abs_nonneg x) zero_le_one).2 hx
  rw [sq_abs] at hsq
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπsq : Real.pi ^ 2 ≤ (4 : ℝ) ^ 2 :=
    (sq_le_sq₀ hπ.le (by norm_num)).2 Real.pi_lt_four.le
  have hcoeff : (1 / 8 : ℝ) ≤ 2 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (by positivity)).2
    linarith
  constructor
  · linarith only [Real.one_sub_sq_div_two_le_cos (x := x), hsq]
  · calc
      _ ≤ 1 - 2 / Real.pi ^ 2 * x ^ 2 :=
        Real.cos_le_one_sub_mul_cos_sq (hx.trans (by linarith [Real.pi_gt_three]))
      _ ≤ 1 - x ^ 2 / 8 := by
        linarith only [mul_le_mul_of_nonneg_right hcoeff (sq_nonneg x)]
      _ ≤ _ := by simpa [neg_div] using Real.one_sub_le_exp_neg (x ^ 2 / 8)

private theorem signSum_cos_product_le {n : ℕ} (a : Fin n → ℝ)
    (I : Finset (Fin n)) (ha : 1 ≤ ∑ i ∈ I, a i ^ 2) (t : ℝ)
    (ht : ∀ i ∈ I, |t * a i| ≤ 1) :
    (∏ i, Real.cos (t * a i)) ≤ Real.exp (-t ^ 2 / 8) := by
  have hI : 0 ≤ ∏ i ∈ I, Real.cos (t * a i) :=
    Finset.prod_nonneg (fun i hi => (cos_le_exp_neg_sq (ht i hi)).1)
  have hc : (∏ i ∈ Finset.univ \ I, Real.cos (t * a i)) ≤ 1 := by
    apply (le_abs_self _).trans
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
  calc
    _ ≤ ∏ i ∈ I, Real.cos (t * a i) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ I) (f := fun i => Real.cos (t * a i))]
      exact mul_le_of_le_one_left hI hc
    _ ≤ ∏ i ∈ I, Real.exp (-(t * a i) ^ 2 / 8) :=
      Finset.prod_le_prod₀ (fun i hi => (cos_le_exp_neg_sq (ht i hi)).1)
        (fun i hi => (cos_le_exp_neg_sq (ht i hi)).2)
    _ ≤ _ := by
      rw [← Real.exp_sum]
      apply Real.exp_monotone
      calc
        _ = ∑ i ∈ I, (-t ^ 2 / 8) * a i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (-t ^ 2 / 8) * (∑ i ∈ I, a i ^ 2) := (Finset.mul_sum _ _ _).symm
        _ ≤ (-t ^ 2 / 8) * 1 := mul_le_mul_of_nonpos_left ha
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
        _ = _ := mul_one _

private theorem cos_fourth_expand (x : ℝ) :
    Real.cos (4 * x) ^ 4 =
      3 / 8 + (1 / 2) * Real.cos (8 * x) + (1 / 8) * Real.cos (16 * x) := by
  rw [show 8 * x = 2 * (4 * x) by ring, show 16 * x = 2 * (2 * (4 * x)) by ring]
  simp only [Real.cos_two_mul]
  ring

/-- A weighted sign sum assigns at most `7/16` to `[-1/100, 1/100]`
if small coefficients carry at least one unit of squared mass. -/
theorem signSum_small_ball_le_of_diffuse_mass {n : ℕ} (a : Fin n → ℝ)
    (I : Finset (Fin n)) (ha : 1 ≤ ∑ i ∈ I, a i ^ 2)
    (hsmall : ∀ i ∈ I, |a i| ≤ 1 / 100) :
    (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ 1 / 100} ≤ 7 / 16 := by
  let W : Set (Fin n → Bool) := {x | |signSum a x| ≤ 1 / 100}
  let weight (x : Fin n → Bool) := Real.cos (4 * signSum a x) ^ 4
  have hlower (x : Fin n → Bool) (hx : x ∈ W) : (15 / 16 : ℝ) ≤ weight x := by
    have hx' : |4 * signSum a x| ≤ 4 / 100 := by
      change |signSum a x| ≤ 1 / 100 at hx
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      linarith only [hx]
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 100)).2 hx'
    rw [sq_abs] at hs
    have h99 : (99 / 100 : ℝ) ≤ Real.cos (4 * signSum a x) := by
      linarith only [hs, Real.one_sub_sq_div_two_le_cos (x := 4 * signSum a x)]
    exact (by norm_num : (15 / 16 : ℝ) ≤ (99 / 100) ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) h99 4)
  have hprob := uniformOn_univ_real_le_weighted_sum W weight
    (by norm_num : (0 : ℝ) < 15 / 16) (fun _ => by dsimp [weight]; positivity) hlower
  have hmean :
      (∑ x, weight x) / Fintype.card (Fin n → Bool) =
        3 / 8 + (1 / 2) * (∏ i, Real.cos (8 * a i)) + (1 / 8) * (∏ i, Real.cos (16 * a i)) := by
    let N : ℝ := Fintype.card (Fin n → Bool)
    have hN : N ≠ 0 := by
      dsimp [N]
      exact_mod_cast Fintype.card_ne_zero (α := Fin n → Bool)
    calc
      _ = 3 / 8 + (1 / 2) * ((∑ x : Fin n → Bool, Real.cos (8 * signSum a x)) / N) +
          (1 / 8) * ((∑ x : Fin n → Bool, Real.cos (16 * signSum a x)) / N) := by
        simp_rw [weight, cos_fourth_expand, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change (N * (3 / 8) + (1 / 2) * _ + (1 / 8) * _) / N = _
        field_simp
      _ = _ := by
        dsimp only [N]
        rw [signSum_cos_average, signSum_cos_average]
  have hfreq (t : ℝ) (ht : t = 8 ∨ t = 16) : (∏ i, Real.cos (t * a i)) ≤ 1 / 32 := by
    have ht' (i : Fin n) (hi : i ∈ I) : |t * a i| ≤ 1 := by
      rw [abs_mul]
      rcases ht with rfl | rfl <;> norm_num <;> linarith [hsmall i hi]
    refine (signSum_cos_product_le a I ha t ht').trans ?_
    have hexp : (32 : ℝ) ≤ Real.exp 8 := by
      have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num)
      linarith
    have ht8 : -t ^ 2 / 8 ≤ -8 := by rcases ht with rfl | rfl <;> norm_num
    refine (Real.exp_le_exp_of_le ht8).trans ?_
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp
  rw [hmean] at hprob
  have h8 := hfreq 8 (Or.inl rfl)
  have h16 := hfreq 16 (Or.inr rfl)
  change (uniformOn Set.univ).real W ≤ 7 / 16
  linarith only [hprob, h8, h16]

/-- A unit weighted sign sum with small coefficients assigns at most `7/16`
to the interval `[-1/100, 1/100]`. -/
theorem diffuse_signSum_small_ball_le {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hsmall : ∀ i, |a i| ≤ 1 / 100) :
    (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ 1 / 100} ≤ 7 / 16 :=
  signSum_small_ball_le_of_diffuse_mass a Finset.univ ha.ge (fun i _ => hsmall i)

private def flipAt {n : ℕ} (i : Fin n) : Equiv.Perm (Fin n → Bool) :=
  Equiv.piCongrRight fun j => if j = i then Equiv.boolNot else Equiv.refl Bool

private theorem signSum_sub_flipAt {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : Fin n → Bool) :
    signSum a x - signSum a (flipAt i x) = 2 * (a i * (if x i then 1 else -1)) := by
  rw [signSum, signSum, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · cases hx : x i <;> simp [flipAt, hx] <;> ring
  · intro j _ hj
    simp [flipAt, hj]
  · simp

/-- Two coefficients separated in magnitude give four disjoint translates
of an interval event when each coefficient also exceeds the interval radius. -/
theorem signSum_small_ball_le_of_unequal_pair {n : ℕ} (a : Fin n → ℝ)
    {i j : Fin n} (hij : i ≠ j) {θ : ℝ} (hi : θ < |a i|) (hj : θ < |a j|)
    (hd : θ < |(|a i| - |a j|)|) :
    (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ θ} ≤ 1 / 4 := by
  let A : Set (Fin n → Bool) := {x | |signSum a x| ≤ θ}
  let f := flipAt i
  let g := flipAt j
  have hs (x y : Fin n → Bool) (hx : x ∈ A) (hy : y ∈ A) :
      |signSum a x - signSum a y| ≤ 2 * θ := by
    change |signSum a x| ≤ θ at hx
    change |signSum a y| ≤ θ at hy
    calc
      _ ≤ |signSum a x| + |signSum a y| := by
        simpa only [← sub_eq_add_neg, abs_neg] using abs_add_le (signSum a x) (-signSum a y)
      _ ≤ _ := by linarith only [hx, hy]
  have hx_flip (k : Fin n) (hk : θ < |a k|) (x : Fin n → Bool) (hx : x ∈ A) :
      flipAt k x ∉ A := by
    intro hy
    have h := hs x (flipAt k x) hx hy
    rw [signSum_sub_flipAt, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    cases hb : x k <;> simp [hb] at h <;> linarith only [h, hk]
  have hx_both (x : Fin n → Bool) (hx : x ∈ A) : g (f x) ∉ A := by
    intro hy
    let u : ℝ := a i * (if x i then 1 else -1)
    let v : ℝ := a j * (if x j then 1 else -1)
    have huv : |u| = |a i| ∧ |v| = |a j| := by
      constructor
      · cases hbit : x i <;> simp [u, hbit]
      · cases hbit : x j <;> simp [v, hbit]
    have hf : f x j = x j := by simp [f, flipAt, hij.symm]
    have hd' : signSum a x - signSum a (g (f x)) = 2 * (u + v) := by
      have h₁ := signSum_sub_flipAt a i x
      have h₂ := signSum_sub_flipAt a j (f x)
      rw [show flipAt j (f x) = g (f x) by rfl, hf] at h₂
      change signSum a x - signSum a (f x) = 2 * u at h₁
      change signSum a (f x) - signSum a (g (f x)) = 2 * v at h₂
      linarith only [h₁, h₂]
    have h := hs x (g (f x)) hx hy
    rw [hd', abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    have habs := abs_abs_sub_abs_le_abs_sub u (-v)
    rw [abs_neg, sub_neg_eq_add, huv.1, huv.2] at habs
    linarith only [h, habs, hd]
  have hgg (x : Fin n → Bool) : g (g x) = x := by
    funext k
    by_cases hk : k = j <;> simp [g, flipAt, hk]
  have hcomm (x : Fin n → Bool) : f (g x) = g (f x) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [f, g, flipAt, hij]
    · by_cases hkj : k = j
      · subst k
        simp [f, g, flipAt, hij.symm]
      · simp [f, g, flipAt, hki, hkj]
  let μ : Measure (Fin n → Bool) := uniformOn Set.univ
  have hpres (e : Equiv.Perm (Fin n → Bool)) (B : Set (Fin n → Bool)) :
      μ.real (e ⁻¹' B) = μ.real B := by
    rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_of_finite e)
      B.toFinite.measurableSet]
    exact congrArg (fun ν : Measure (Fin n → Bool) => (ν B).toReal) (map_uniformOn_univ_of_equiv e)
  let B := A ∪ g ⁻¹' A
  have hB : μ.real B = 2 * μ.real A := by
    have hdisj : Disjoint A (g ⁻¹' A) := Set.disjoint_left.mpr fun x hx hy => hx_flip j hj x hx hy
    change μ.real (A ∪ g ⁻¹' A) = _
    rw [measureReal_union hdisj (Set.toFinite _).measurableSet, hpres g]
    ring
  have hBdisj : Disjoint B (f ⁻¹' B) := by
    rw [Set.disjoint_left]
    intro x hx hy
    change x ∈ A ∨ g x ∈ A at hx
    change f x ∈ A ∨ g (f x) ∈ A at hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hx_flip i hi x hx hy
    · exact hx_both x hx hy
    · apply hx_both (g x) hx
      rwa [hcomm, hgg]
    · apply hx_flip i hi (g x) hx
      change f (g x) ∈ A
      rwa [hcomm]
  have h := measureReal_mono (μ := μ) (Set.subset_univ (B ∪ f ⁻¹' B))
  rw [measureReal_union hBdisj (Set.toFinite _).measurableSet, hpres f, hB] at h
  have huniv : μ.real Set.univ = 1 := by simp [μ, measureReal_def]
  rw [huniv] at h
  change μ.real A ≤ 1 / 4
  linarith only [h]

private theorem small_ball_inter_le_of_pivot {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (hi : (1 / 100 : ℝ) < |a i|) (W : Set (Fin n → Bool))
    (hW : ∀ x, x ∈ W ↔ flipAt i x ∈ W) :
    (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ 1 / 100 ∧ x ∈ W} ≤
      (uniformOn Set.univ).real W / 2 := by
  let μ : Measure (Fin n → Bool) := uniformOn Set.univ
  let A : Set (Fin n → Bool) := {x | |signSum a x| ≤ 1 / 100 ∧ x ∈ W}
  let B := flipAt i ⁻¹' A
  have hmap : μ.map (flipAt i) = μ := map_uniformOn_univ_of_equiv (flipAt i)
  have hprob : μ.real B = μ.real A := by
    have h := congrArg (fun ν : Measure (Fin n → Bool) => ν A) hmap
    rw [Measure.map_apply (measurable_of_finite _) A.toFinite.measurableSet] at h
    exact congrArg ENNReal.toReal h
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : |signSum a x| ≤ 1 / 100 := hx.1
    have hy' : |signSum a (flipAt i x)| ≤ 1 / 100 := hy.1
    have hd : |signSum a x - signSum a (flipAt i x)| ≤
        |signSum a x| + |signSum a (flipAt i x)| := by
      simpa only [← sub_eq_add_neg, abs_neg] using abs_add_le (signSum a x) (-signSum a (flipAt i x))
    rw [signSum_sub_flipAt, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hd
    cases hbit : x i <;> simp [hbit] at hd <;> linarith only [hi, hx', hy', hd]
  have hsub : A ∪ B ⊆ W := by
    rintro x (hx | hx)
    · exact hx.2
    · exact (hW x).mpr hx.2
  have h := measureReal_mono (μ := μ) hsub
  rw [measureReal_union hdisj B.toFinite.measurableSet, hprob] at h
  change μ.real A ≤ μ.real W / 2
  linarith only [h]

/-- Every unit weighted sign sum assigns probability at most one half to a
fixed interval of radius `1/100` around zero. -/
theorem unit_signSum_small_ball_le {n : ℕ} (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    (uniformOn Set.univ).real {x : Fin n → Bool | |signSum a x| ≤ 1 / 100} ≤ 1 / 2 := by
  by_cases h : ∃ i, (1 / 100 : ℝ) < |a i|
  · obtain ⟨i, hi⟩ := h
    have hp := small_ball_inter_le_of_pivot a i hi Set.univ (fun x => by simp)
    simpa [measureReal_def] using hp
  · push Not at h
    exact (diffuse_signSum_small_ball_le a ha h).trans (by norm_num)

/-- The mass of a fixed small Euclidean ball under the projection of a sign
row on two orthonormal directions is bounded away from one half. -/
theorem orthonormal_signSum_small_ball_le {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1)
    (horth : ∑ i, u i * v i = 0) :
    (uniformOn Set.univ).real {x : Fin n → Bool |
      signSum u x ^ 2 + signSum v x ^ 2 ≤ (1 / 100 : ℝ) ^ 2} ≤ 7 / 16 := by
  let E : Set (Fin n → Bool) :=
    {x | signSum u x ^ 2 + signSum v x ^ 2 ≤ (1 / 100 : ℝ) ^ 2}
  have huE (x : Fin n → Bool) (hx : x ∈ E) : |signSum u x| ≤ 1 / 100 := by
    change signSum u x ^ 2 + signSum v x ^ 2 ≤ (1 / 100 : ℝ) ^ 2 at hx
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100), sq_abs]
    linarith only [hx, sq_nonneg (signSum v x)]
  by_cases h : ∃ i, (1 / 100 : ℝ) < |u i|
  · obtain ⟨i, hi⟩ := h
    let scale := Real.sqrt (u i ^ 2 + v i ^ 2)
    let w (j : Fin n) := (u i * v j - v i * u j) / scale
    have hune : u i ≠ 0 := by
      intro heq
      rw [heq, abs_zero] at hi
      linarith
    have hPos : 0 < u i ^ 2 + v i ^ 2 := by positivity
    have hscale : 0 < scale := Real.sqrt_pos_of_pos hPos
    have hscale₂ : scale ^ 2 = u i ^ 2 + v i ^ 2 := Real.sq_sqrt hPos.le
    have hwi : w i = 0 := by simp [w, mul_comm]
    have hw : ∑ j, w j ^ 2 = 1 := by
      have hn : (∑ j, (u i * v j - v i * u j) ^ 2) = u i ^ 2 + v i ^ 2 := by
        calc
          _ = ∑ j, (u i ^ 2 * v j ^ 2 + v i ^ 2 * u j ^ 2 -
              (2 * u i * v i) * (u j * v j)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = _ := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
              hu, hv, horth, mul_one, mul_zero, sub_zero]
      simp only [w, div_pow, ← Finset.sum_div, hn, ← hscale₂]
      exact div_self (by positivity)
    let W : Set (Fin n → Bool) := {x | |signSum w x| ≤ 1 / 100}
    have hwInv (x : Fin n → Bool) : x ∈ W ↔ flipAt i x ∈ W := by
      have hh := signSum_sub_flipAt w i x
      simp only [hwi, zero_mul, mul_zero] at hh
      change (|signSum w x| ≤ 1 / 100) ↔ (|signSum w (flipAt i x)| ≤ 1 / 100)
      rw [sub_eq_zero.mp hh]
    have hwE (x : Fin n → Bool) (hx : x ∈ E) : x ∈ W := by
      have hs : signSum w x = (u i * signSum v x - v i * signSum u x) / scale := by
        simp only [signSum, w, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      change |signSum w x| ≤ 1 / 100
      change signSum u x ^ 2 + signSum v x ^ 2 ≤ (1 / 100 : ℝ) ^ 2 at hx
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100),
        sq_abs, hs, div_pow, div_le_iff₀ (by positivity), hscale₂]
      have hmul := mul_le_mul_of_nonneg_right hx hPos.le
      nlinarith only [hmul, sq_nonneg (u i * signSum u x + v i * signSum v x)]
    have hp := small_ball_inter_le_of_pivot u i hi W hwInv
    calc
      _ ≤ (uniformOn Set.univ).real {x | |signSum u x| ≤ 1 / 100 ∧ x ∈ W} :=
        measureReal_mono fun x hx => ⟨huE x hx, hwE x hx⟩
      _ ≤ (uniformOn Set.univ).real W / 2 := hp
      _ ≤ _ := by
        have hhalf := unit_signSum_small_ball_le w hw
        change (uniformOn Set.univ).real W ≤ 1 / 2 at hhalf
        linarith only [hhalf]
  · push Not at h
    exact (measureReal_mono (μ := uniformOn Set.univ) huE).trans
      (diffuse_signSum_small_ball_le u hu h)

end BooleanThreshold
