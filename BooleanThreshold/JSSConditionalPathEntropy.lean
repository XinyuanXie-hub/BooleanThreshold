module

public import BooleanThreshold.JSSConditionalPathWeights
public import BooleanThreshold.Asymptotics

@[expose] public section

open Filter
open scoped BigOperators Topology Classical

namespace BooleanThreshold

/-- Steps at which both branch weights are substantial and the other branch
is above the drop threshold. -/
noncomputable def robustHighSiblingSteps (w : ℕ → Bool) (v : ℕ → ℝ) (ℓ : ℕ)
    (ε γ τ : ℝ) : Finset ℕ :=
  (Finset.range ℓ).filter fun i => ε ≤ slicePathWeight w i ∧ slicePathWeight w i ≤ 1 - ε ∧
    γ * τ < v i

private theorem step_height_le {h : ℕ → ℝ} {ℓ i j : ℕ}
    (hh : ∀ k < ℓ, h (k + 1) ≤ h k) (hij : i ≤ j) (hj : j ≤ ℓ) : h j ≤ h i := by
  induction j generalizing i with
  | zero =>
    have heq : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases hij' : i ≤ j
    · exact (hh j (by omega)).trans (ih hij' (by omega))
    · have heq : i = j + 1 := by omega
      subst i
      exact le_rfl

private theorem prod_step_height_ratio {h : ℕ → ℝ} {ℓ : ℕ} (hp : ∀ i ≤ ℓ, 0 < h i) :
    (∏ i ∈ Finset.range ℓ, h (i + 1) / h i) = h ℓ / h 0 := by
  induction ℓ with
  | zero => simp [div_self (hp 0 le_rfl).ne']
  | succ ℓ ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => hp i (hi.trans (Nat.le_succ _)))]
    field_simp [(hp ℓ (Nat.le_succ _)).ne', (hp 0 (Nat.zero_le _)).ne']

private theorem path_height_product_certificate {ℓ : ℕ} (hℓ : 0 < ℓ)
    (w : ℕ → Bool) (h v : ℕ → ℝ) {ε γ τ : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hγ : 0 < γ) (hτ : 0 < τ) (h₀ : h 0 ≤ 1) (hfinal : τ ≤ h ℓ)
    (hstep : ∀ i < ℓ, h (i + 1) ≤ h i)
    (hrec : ∀ i < ℓ, h (i + 1) = slicePathWeight w i * h i + (1 - slicePathWeight w i) * v i) :
    Real.exp (-6 * Real.sqrt ε * (ℓ : ℝ)) * ε ^ (robustHighSiblingSteps w v ℓ ε γ τ).card * τ ≤
      (1 + γ / ε) ^ ℓ / (ℓ.choose (prefixBitCount w true ℓ) : ℝ) := by
  let R (i : ℕ) := ε ≤ slicePathWeight w i ∧ slicePathWeight w i ≤ 1 - ε
  let T (i : ℕ) := ε ≤ slicePathWeight w i ∧ slicePathWeight w i ≤ 1 - ε ∧ γ * τ < v i
  let C := 1 + γ / ε
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  let q (i : ℕ) := h (i + 1) / h i
  let a (i : ℕ) := if ¬ R i then slicePathWeight w i else 1
  let b (i : ℕ) := if T i then ε else 1
  have hheight (i : ℕ) (hi : i ≤ ℓ) : τ ≤ h i := hfinal.trans (step_height_le hstep hi le_rfl)
  have hpos (i : ℕ) (hi : i ≤ ℓ) : 0 < h i := hτ.trans_le (hheight i hi)
  have hqi (i : ℕ) (hi : i < ℓ) : 0 ≤ q i ∧ q i ≤ 1 := by
    have h₁ := hpos i hi.le
    have h₂ := hpos (i + 1) (Nat.succ_le_of_lt hi)
    exact ⟨div_nonneg h₂.le h₁.le, (div_le_one₀ h₁).mpr (hstep i hi)⟩
  have hpoint (i : ℕ) (hi : i < ℓ) : a i * b i * q i ≤ C * slicePathWeight w i := by
    let p := slicePathWeight w i
    have hp₀ : 0 < p := slicePathWeight_pos w i
    have hp₁ : p ≤ 1 := slicePathWeight_le_one w i
    have hscale : p ≤ C * p := le_mul_of_one_le_left hp₀.le hC
    by_cases hR : R i
    · by_cases hT : T i
      · simp only [a, b, hR, not_true_eq_false, hT, ↓reduceIte, one_mul]
        exact ((mul_le_of_le_one_right hε.le (hqi i hi).2).trans hR.1).trans hscale
      · simp only [a, b, hR, not_true_eq_false, hT, ↓reduceIte, one_mul]
        have hv : v i ≤ γ * τ := by
          apply le_of_not_gt
          exact fun ht => hT ⟨hR.1, hR.2, ht⟩
        have hf : q i ≤ p + γ := by
          change h (i + 1) / h i ≤ p + γ
          apply (div_le_iff₀ (hpos i hi.le)).mpr
          rw [hrec i hi]
          have hmul : (1 - p) * v i ≤ γ * h i := by
            calc
              _ ≤ (1 - p) * (γ * τ) := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hp₁)
              _ ≤ γ * τ := mul_le_of_le_one_left (by positivity) (by linarith only [hp₀])
              _ ≤ γ * h i := mul_le_mul_of_nonneg_left (hheight i hi.le) hγ.le
          nlinarith only [hmul]
        refine hf.trans ?_
        change p + γ ≤ (1 + γ / ε) * p
        have hpp : ε ≤ p := hR.1
        have hmul := mul_le_mul_of_nonneg_left hpp (show 0 ≤ γ / ε by positivity)
        have he : γ / ε * ε = γ := by field_simp
        rw [he] at hmul
        nlinarith only [hmul]
    · have hT : ¬T i := fun ht => hR ⟨ht.1, ht.2.1⟩
      simp only [a, b, hR, hT, not_false_eq_true, ↓reduceIte, mul_one]
      exact (mul_le_of_le_one_right hp₀.le (hqi i hi).2).trans hscale
  have ha₀ (i : ℕ) : 0 ≤ a i := by
    dsimp [a]
    split
    · exact (slicePathWeight_pos w i).le
    · exact zero_le_one
  have hb₀ (i : ℕ) : 0 ≤ b i := by dsimp [b]; split <;> positivity
  have hprod := Finset.prod_le_prod₀ (s := Finset.range ℓ)
    (fun i hi => mul_nonneg (mul_nonneg (ha₀ i) (hb₀ i)) (hqi i (Finset.mem_range.mp hi)).1)
    (fun i hi => hpoint i (Finset.mem_range.mp hi))
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    slicePathWeight_prod_eq_inv_choose] at hprod
  have ha : (∏ i ∈ Finset.range ℓ, a i) = ∏ i ∈ (Finset.range ℓ).filter (fun i => ¬ R i),
      slicePathWeight w i := by
    change (∏ i ∈ Finset.range ℓ, if ¬ R i then slicePathWeight w i else 1) = _
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  have hb : (∏ i ∈ Finset.range ℓ, b i) = ε ^ (robustHighSiblingSteps w v ℓ ε γ τ).card := by
    simp [b, T, Finset.prod_ite, robustHighSiblingSteps]
  rw [ha, hb, show (∏ i ∈ Finset.range ℓ, q i) = h ℓ / h 0 from prod_step_height_ratio hpos] at hprod
  have ht : τ ≤ h ℓ / h 0 := by
    apply (le_div_iff₀ (hpos 0 (Nat.zero_le _))).mpr
    exact (mul_le_of_le_one_right hτ.le h₀).trans hfinal
  rw [div_eq_mul_inv]
  refine le_trans ?_ hprod
  have hlow := slicePathWeight_nonrobust_prod_lower w hℓ hε hε'
  have hprod₀ := Finset.prod_nonneg (s := (Finset.range ℓ).filter (fun i => ¬ R i))
    (fun i _ => (slicePathWeight_pos w i).le)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hlow (by positivity)) ht hτ.le (mul_nonneg hprod₀ (by positivity))

/-- The entropy of a nearly full, balanced fixed-weight slice forces a linear
number of high alternate branches along a greedy path. -/
theorem eventually_many_robustHighSiblingSteps {b : ℝ} (hb : (5 / 3 : ℝ) < b) :
    ∃ ε > (0 : ℝ), ε < 1 / 2 ∧ ∃ γ > (0 : ℝ), ∃ κ > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ ℓ ≤ n, 0 < ℓ → ∀ w : ℕ → Bool,
        b ^ n ≤ (ℓ.choose (prefixBitCount w true ℓ) : ℝ) →
        ∀ h v : ℕ → ℝ, ∀ τ : ℝ, 1 / ((5 / 3 : ℝ) ^ n * Real.sqrt (n : ℝ)) ≤ τ →
          h 0 ≤ 1 → τ ≤ h ℓ →
          (∀ i < ℓ, h (i + 1) ≤ h i) →
          (∀ i < ℓ, h (i + 1) = slicePathWeight w i * h i + (1 - slicePathWeight w i) * v i) →
          κ * (n : ℝ) ≤ ((robustHighSiblingSteps w v ℓ ε γ τ).card : ℝ) := by
  let D := Real.log (b / (5 / 3 : ℝ))
  have hb₀ : 0 < b := (by norm_num : (0 : ℝ) < 5 / 3).trans hb
  have hD : 0 < D := Real.log_pos ((one_lt_div (by norm_num)).mpr hb)
  let ε := min ((D / 48) ^ 2) (1 / 4 : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε' : ε < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  let γ := ε * (D / 8)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  let κ := D / (2 * (-Real.log ε))
  have hL : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε (hε'.trans (by norm_num)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hsmall : 6 * Real.sqrt ε ≤ D / 8 := by
    have hh : Real.sqrt ε ≤ D / 48 := (Real.sqrt_le_iff).mpr ⟨by positivity, min_le_left _ _⟩
    linarith only [hh]
  have hcoef : 1 + γ / ε ≤ Real.exp (D / 8) := by
    dsimp [γ]
    rw [show ε * (D / 8) / ε = D / 8 by field_simp, add_comm]
    exact Real.add_one_le_exp _
  have hEventually : ∀ᶠ n : ℕ in atTop, Real.sqrt (n : ℝ) ≤ Real.exp (D / 4 * (n : ℝ)) := by
    have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 (Real.one_lt_exp_iff.mpr (by positivity : 0 < D / 4))
    have hh := ht.eventually_le_const (show (0 : ℝ) < 1 from zero_lt_one)
    filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with n hn hn₀
    have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      apply (Real.sqrt_le_left (Nat.cast_nonneg _)).mpr
      have hh : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
      rw [pow_two]
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) hh
    refine hs.trans ?_
    have hh := (div_le_iff₀ (show 0 < Real.exp (D / 4) ^ n by positivity)).mp hn
    simpa only [pow_one, one_mul, ← Real.exp_nat_mul, mul_comm (n : ℝ) (D / 4)] using hh
  refine ⟨ε, hε, hε', γ, hγ, κ, hκ, ?_⟩
  filter_upwards [hEventually] with n hn ℓ hℓ hℓ₀ w hchoose h v τ hτ h₀ hfin hstep hrec
  let q := (5 / 3 : ℝ)
  let hN := Real.sqrt (n : ℝ)
  let C := 1 + γ / ε
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  let k := (robustHighSiblingSteps w v ℓ ε γ τ).card
  have hn₀ : 0 < n := hℓ₀.trans_le hℓ
  have hs : 0 < hN := by dsimp [hN]; positivity
  have hq : 0 < q := by dsimp [q]; norm_num
  have hτ₀ : 0 < τ := (by positivity : 0 < 1 / (q ^ n * hN)).trans_le hτ
  have hc : 0 < (ℓ.choose (prefixBitCount w true ℓ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (prefixBitCount_le w true ℓ)
  have hpath := path_height_product_certificate hℓ₀ w h v hε hε' hγ hτ₀ h₀ hfin hstep hrec
  have hpath' := (le_div_iff₀ hc).mp hpath
  have hcoal : Real.exp (-6 * Real.sqrt ε * (n : ℝ)) * ε ^ k * (1 / (q ^ n * hN)) * b ^ n ≤
      C ^ n := by
    refine (le_trans ?_ hpath').trans (pow_le_pow_right₀ hC hℓ)
    have he : Real.exp (-6 * Real.sqrt ε * (n : ℝ)) ≤ Real.exp (-6 * Real.sqrt ε * (ℓ : ℝ)) := by
      apply Real.exp_monotone
      have hi : (ℓ : ℝ) ≤ n := by exact_mod_cast hℓ
      linarith only [mul_le_mul_of_nonneg_left hi (show 0 ≤ 6 * Real.sqrt ε by positivity)]
    gcongr
  let A := Real.exp (6 * Real.sqrt ε * (n : ℝ))
  have hA : 0 < A := Real.exp_pos _
  have hneg : Real.exp (-6 * Real.sqrt ε * (n : ℝ)) * A = 1 := by
    dsimp [A]
    rw [← Real.exp_add, show -6 * Real.sqrt ε * (n : ℝ) + 6 * Real.sqrt ε * (n : ℝ) = 0 by ring,
      Real.exp_zero]
  have hbound : ε ^ k ≤ C ^ n * A * hN * (q / b) ^ n := by
    have hcpos : 0 < q ^ n * hN := by positivity
    have hBpos : 0 < b ^ n := by positivity
    have hh := mul_le_mul_of_nonneg_right hcoal (show 0 ≤ A * (q ^ n * hN) / b ^ n by positivity)
    have he : Real.exp (-6 * Real.sqrt ε * (n : ℝ)) * ε ^ k * (1 / (q ^ n * hN)) * b ^ n *
        (A * (q ^ n * hN) / b ^ n) = ε ^ k := by
      calc
        _ = (Real.exp (-6 * Real.sqrt ε * (n : ℝ)) * A) * ε ^ k := by
          field_simp [hcpos.ne', hBpos.ne']
        _ = _ := by rw [hneg, one_mul]
    rw [he] at hh
    refine hh.trans_eq ?_
    rw [div_pow q b]
    ring
  have heqb : (q / b) ^ n = Real.exp (-D * (n : ℝ)) := by
    have he : q / b = Real.exp (-D) := by
      rw [Real.exp_neg, show D = Real.log (b / q) by rfl, Real.exp_log (by positivity)]
      field_simp
    rw [he, ← Real.exp_nat_mul]
    congr 1
    ring
  have hbound' : ε ^ k ≤ Real.exp (-(D / 2) * (n : ℝ)) := by
    refine hbound.trans ?_
    rw [heqb]
    calc
      _ ≤ Real.exp (D / 8 * (n : ℝ)) * Real.exp (D / 8 * (n : ℝ)) *
          Real.exp (D / 4 * (n : ℝ)) * Real.exp (-D * (n : ℝ)) := by
        have hc : C ^ n ≤ Real.exp (D / 8 * (n : ℝ)) := by
          rw [mul_comm (D / 8), Real.exp_nat_mul]
          exact pow_le_pow_left₀ (zero_le_one.trans hC) hcoef _
        have ha : A ≤ Real.exp (D / 8 * (n : ℝ)) :=
          Real.exp_monotone (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n))
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hk : (k : ℝ) * Real.log ε ≤ -(D / 2) * (n : ℝ) := by
    apply Real.exp_le_exp.mp
    rwa [Real.exp_nat_mul, Real.exp_log hε]
  have hkk : D * (n : ℝ) ≤ (k : ℝ) * (2 * (-Real.log ε)) := by nlinarith only [hk]
  change κ * (n : ℝ) ≤ (k : ℝ)
  dsimp [κ]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity)).mpr hkk

end BooleanThreshold
