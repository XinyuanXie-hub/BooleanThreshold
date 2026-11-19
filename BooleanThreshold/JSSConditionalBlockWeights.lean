module

public import BooleanThreshold.JSSConditionalSliceBlocks
public import BooleanThreshold.JSSConditionalMixed

public noncomputable section

open Finset Filter
open scoped BigOperators Classical Topology

namespace BooleanThreshold

private theorem binomialWeight_nonneg (n j : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ binomialWeight n j p := by
  unfold binomialWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp') _)

private theorem binomialWeight_mul_pow_sum (n : ℕ) (p r : ℝ) :
    (∑ j ∈ range (n + 1), binomialWeight n j p * r ^ j) = (p * r + (1 - p)) ^ n := by
  rw [add_pow]
  apply sum_congr rfl
  intro j _
  simp only [binomialWeight, mul_pow]
  ring

private theorem binomialWeight_mul_pow_compl_sum (n : ℕ) (p r : ℝ) :
    (∑ j ∈ range (n + 1), binomialWeight n j p * r ^ (n - j)) =
      (p + (1 - p) * r) ^ n := by
  rw [add_pow]
  apply sum_congr rfl
  intro j _
  simp only [binomialWeight, mul_pow]
  ring

private theorem binomialWeight_le_one (n j : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    binomialWeight n j p ≤ 1 := by
  by_cases hj : j ≤ n
  · have hsum : (∑ i ∈ range (n + 1), binomialWeight n i p) = 1 := by
      simpa only [one_pow, mul_one, add_sub_cancel] using binomialWeight_mul_pow_sum n p 1
    rw [← hsum]
    exact single_le_sum (fun i _ => binomialWeight_nonneg n i hp hp')
      (mem_range.mpr (Nat.lt_succ_of_le hj))
  · simp [binomialWeight, Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]

private theorem sliceSplitWeight_eq_binomial_ratio {a b s j : ℕ} (hj : j ≤ s)
    {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    sliceSplitWeight a b s j =
      binomialWeight a (s - j) p * binomialWeight b j p / binomialWeight (a + b) s p := by
  by_cases h₁ : s - j ≤ a
  · by_cases h₂ : j ≤ b
    · let r := p ^ s * (1 - p) ^ (a + b - s)
      have hr : r ≠ 0 := by dsimp [r]; positivity
      have he₁ : p ^ (s - j) * p ^ j = p ^ s := by rw [← pow_add, Nat.sub_add_cancel hj]
      have he₂ : (1 - p) ^ (a - (s - j)) * (1 - p) ^ (b - j) =
          (1 - p) ^ (a + b - s) := by rw [← pow_add, show a - (s - j) + (b - j) = a + b - s by omega]
      have hn : binomialWeight a (s - j) p * binomialWeight b j p =
          ((a.choose (s - j) : ℝ) * (b.choose j : ℝ)) * r := by
        unfold binomialWeight
        rw [show r = (p ^ (s - j) * p ^ j) * ((1 - p) ^ (a - (s - j)) * (1 - p) ^ (b - j)) by
          rw [he₁, he₂]]
        ring
      have hd : binomialWeight (a + b) s p = ((a + b).choose s : ℝ) * r := by
        unfold binomialWeight r
        ring
      rw [hn, hd, mul_div_mul_right _ _ hr]
      rfl
    · simp [sliceSplitWeight, binomialWeight, Nat.choose_eq_zero_of_lt (lt_of_not_ge h₂)]
  · simp [sliceSplitWeight, binomialWeight, Nat.choose_eq_zero_of_lt (lt_of_not_ge h₁)]

private theorem sliceSplitWeight_le_tilted_binomial {a b s j : ℕ}
    (hs₀ : 0 < s) (hs₁ : s < a + b) (hj : j ≤ s) :
    sliceSplitWeight a b s j ≤
      ((a + b : ℕ) + (1 : ℝ)) * binomialWeight b j ((s : ℝ) / ((a + b : ℕ) : ℝ)) := by
  let n := a + b
  let p := (s : ℝ) / (n : ℝ)
  have hn : (0 : ℝ) < n := by exact_mod_cast (hs₀.trans hs₁)
  have hp : 0 < p := div_pos (by exact_mod_cast hs₀) hn
  have hp' : p < 1 := (div_lt_one hn).mpr (by exact_mod_cast hs₁)
  have hden : 1 / ((n : ℝ) + 1) ≤ binomialWeight n s p :=
    binomialWeight_at_mean_ge hs₀ hs₁
  have hden₀ : 0 < binomialWeight n s p := (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hden
  rw [sliceSplitWeight_eq_binomial_ratio hj hp hp']
  calc
    _ ≤ binomialWeight b j p / binomialWeight n s p :=
      div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (binomialWeight_nonneg b j hp.le hp'.le)
          (binomialWeight_le_one a (s - j) hp.le hp'.le)) hden₀.le
    _ ≤ binomialWeight b j p / (1 / ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (binomialWeight_nonneg b j hp.le hp'.le) (by positivity) hden
    _ = _ := by rw [one_div, div_inv_eq_mul, mul_comm]

private theorem sliceSplitWeight_nonneg_moment_le {a b s : ℕ}
    (hs₀ : 0 < s) (hs₁ : s < a + b) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ range (s + 1), sliceSplitWeight a b s j * f j) ≤
      (((a + b : ℕ) : ℝ) + 1) *
        ∑ j ∈ range (b + 1), binomialWeight b j ((s : ℝ) / ((a + b : ℕ) : ℝ)) * f j := by
  let n := a + b
  let p := (s : ℝ) / (n : ℝ)
  have hn : (0 : ℝ) < n := by exact_mod_cast (hs₀.trans hs₁)
  have hp : 0 ≤ p := by positivity
  have hp' : p ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hs₁.le)
  have hsum : (∑ j ∈ range (s + 1), binomialWeight b j p * f j) ≤
      ∑ j ∈ range (b + 1), binomialWeight b j p * f j := by
    by_cases h : s ≤ b
    · exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
        (fun j _ _ => mul_nonneg (binomialWeight_nonneg b j hp hp') (hf j))
    · apply le_of_eq
      symm
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      have hj' : b < j := by rw [mem_range] at hj; omega
      simp [binomialWeight, Nat.choose_eq_zero_of_lt hj']
  calc
    _ ≤ ∑ j ∈ range (s + 1), ((n : ℝ) + 1) * (binomialWeight b j p * f j) := by
      apply sum_le_sum
      intro j hj
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (sliceSplitWeight_le_tilted_binomial hs₀ hs₁
        (Nat.le_of_lt_succ (mem_range.mp hj))) (hf j)
    _ = ((n : ℝ) + 1) * ∑ j ∈ range (s + 1), binomialWeight b j p * f j := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- If the overall weight has both signs at density at least `η`, a block
with fewer than an `η/4` fraction of either sign has exponentially small weight. -/
theorem sliceSplitWeight_bad_count_le {a b s : ℕ} {η : ℝ}
    (hn : 0 < a + b) (hη : 0 < η)
    (hlo : η * ((a + b : ℕ) : ℝ) ≤ (s : ℝ))
    (hhi : (s : ℝ) ≤ (1 - η) * ((a + b : ℕ) : ℝ)) :
    (∑ j ∈ range (s + 1),
      if (j : ℝ) < (η / 4) * (b : ℝ) ∨ ((b - j : ℕ) : ℝ) < (η / 4) * (b : ℝ)
      then sliceSplitWeight a b s j else 0) ≤
        2 * (((a + b : ℕ) : ℝ) + 1) * Real.exp (-(η / 4) * (b : ℝ)) := by
  let n := a + b
  let p := (s : ℝ) / (n : ℝ)
  let u := (η / 4) * (b : ℝ)
  let r := Real.exp (-1)
  let g (j : ℕ) := Real.exp (-(j : ℝ)) + Real.exp (-((b - j : ℕ) : ℝ))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : η ≤ p := (le_div_iff₀ hn').mpr hlo
  have hp₁ : p ≤ 1 - η := (div_le_iff₀ hn').mpr hhi
  have hp' : η ≤ 1 - p := by linarith only [hp₁]
  have hs₀ : 0 < s := by exact_mod_cast ((mul_pos hη hn').trans_le hlo)
  have hs₁ : s < n := by
    have h := hhi.trans_lt (by nlinarith only [mul_pos hη hn'] : (1 - η) * (n : ℝ) < n)
    exact_mod_cast h
  have hr : 0 ≤ r := Real.exp_nonneg _
  have hr₂ : r ≤ 1 / 2 := by
    change Real.exp (-1) ≤ 1 / 2
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [Real.add_one_le_exp (1 : ℝ)])
  have hfactor (w : ℝ) (hw : η ≤ w) (hw₁ : w ≤ 1) :
      (1 - w * (1 - r)) ^ b ≤ Real.exp (-(η / 2) * (b : ℝ)) := by
    have hw₀ : 0 ≤ w := hη.le.trans hw
    have hbase : 0 ≤ 1 - w * (1 - r) := by
      rw [show 1 - w * (1 - r) = (1 - w) + w * r by ring]
      exact add_nonneg (sub_nonneg.mpr hw₁) (mul_nonneg hw₀ hr)
    have hm : η / 2 ≤ w * (1 - r) := by
      have h := mul_le_mul hw (show 1 / 2 ≤ 1 - r by linarith only [hr₂]) (by norm_num) hw₀
      nlinarith only [h]
    calc
      _ ≤ (Real.exp (-(η / 2))) ^ b :=
        pow_le_pow_left₀ hbase
          ((Real.one_sub_le_exp_neg _).trans (Real.exp_monotone (neg_le_neg hm))) _
      _ = _ := by rw [← Real.exp_nat_mul, mul_comm]
  have hexp (j : ℕ) : Real.exp (-(j : ℝ)) = r ^ j := by
    dsimp only [r]
    rw [← Real.exp_nat_mul, mul_neg, mul_one]
  have hg (j : ℕ) : 0 ≤ g j := by dsimp [g]; positivity
  have hmoment : (∑ j ∈ range (b + 1), binomialWeight b j p * g j) ≤
      2 * Real.exp (-(η / 2) * (b : ℝ)) := by
    simp only [g, hexp, mul_add, sum_add_distrib, binomialWeight_mul_pow_sum,
      binomialWeight_mul_pow_compl_sum]
    rw [show p * r + (1 - p) = 1 - p * (1 - r) by ring,
      show p + (1 - p) * r = 1 - (1 - p) * (1 - r) by ring, two_mul]
    exact add_le_add (hfactor p hp (by linarith only [hp₁, hη]))
      (hfactor (1 - p) hp' (by linarith only [hp, hη]))
  have hindicator (j : ℕ) :
      (if (j : ℝ) < u ∨ ((b - j : ℕ) : ℝ) < u then sliceSplitWeight a b s j else 0) ≤
        Real.exp u * (sliceSplitWeight a b s j * g j) := by
    have hw := sliceSplitWeight_nonneg a b s j
    by_cases h : (j : ℝ) < u ∨ ((b - j : ℕ) : ℝ) < u
    · rw [ite_eq_left h]
      have hb (t : ℝ) (ht : t < u) : 1 ≤ Real.exp u * Real.exp (-t) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_monotone (by linarith only [ht])
      have hi : 1 ≤ Real.exp u * g j := by
        rcases h with h | h
        · refine (hb _ h).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
          exact le_add_of_nonneg_right (Real.exp_nonneg _)
        · refine (hb _ h).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))
          exact le_add_of_nonneg_left (Real.exp_nonneg _)
      calc
        _ = sliceSplitWeight a b s j * 1 := (mul_one _).symm
        _ ≤ sliceSplitWeight a b s j * (Real.exp u * g j) := mul_le_mul_of_nonneg_left hi hw
        _ = _ := by ring
    · rw [ite_eq_right h]
      exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg hw (hg j))
  calc
    _ ≤ ∑ j ∈ range (s + 1), Real.exp u * (sliceSplitWeight a b s j * g j) :=
      sum_le_sum fun j _ => hindicator j
    _ = Real.exp u * ∑ j ∈ range (s + 1), sliceSplitWeight a b s j * g j := by rw [mul_sum]
    _ ≤ Real.exp u * (((n : ℝ) + 1) * ∑ j ∈ range (b + 1), binomialWeight b j p * g j) :=
      mul_le_mul_of_nonneg_left (sliceSplitWeight_nonneg_moment_le hs₀ hs₁ g hg) (Real.exp_nonneg _)
    _ ≤ Real.exp u * (((n : ℝ) + 1) * (2 * Real.exp (-(η / 2) * (b : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmoment (by positivity)) (Real.exp_nonneg _)
    _ = _ := by
      rw [show Real.exp u * (((n : ℝ) + 1) * (2 * Real.exp (-(η / 2) * (b : ℝ)))) =
        2 * ((n : ℝ) + 1) * (Real.exp u * Real.exp (-(η / 2) * (b : ℝ))) by ring, ← Real.exp_add]
      congr 2
      dsimp only [u]
      ring

/-- An extensive block of a balanced fixed-weight slice has extensive counts of
both signs, up to an exponentially small weight in the block decomposition. -/
theorem sliceSplitWeight_bad_count_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ a b s : ℕ, a + b = n → σ * (n : ℝ) ≤ (b : ℝ) →
      η * (n : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (1 - η) * (n : ℝ) →
        (∑ j ∈ range (s + 1),
          if (j : ℝ) < (η / 4) * (b : ℝ) ∨ ((b - j : ℕ) : ℝ) < (η / 4) * (b : ℝ)
          then sliceSplitWeight a b s j else 0) ≤ Real.exp (-c * (n : ℝ)) := by
  let c := η * σ / 8
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hl := tendsto_pow_const_div_const_pow_of_one_lt 1 (Real.one_lt_exp_iff.mpr hc)
  filter_upwards [hl.eventually_le_const (show (0 : ℝ) < 1 / 4 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlim hn a b s hsum hb hlo hhi
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC : 2 * ((n : ℝ) + 1) ≤ Real.exp (c * (n : ℝ)) := by
    have h := (div_le_iff₀ (show 0 < Real.exp c ^ n by positivity)).mp hlim
    rw [pow_one, ← Real.exp_nat_mul, mul_comm (n : ℝ)] at h
    linarith only [h, hn']
  have hB : -(η / 4) * (b : ℝ) ≤ -(2 * c) * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ η / 4 by positivity)
    dsimp only [c]
    nlinarith only [h]
  calc
    _ ≤ 2 * ((n : ℝ) + 1) * Real.exp (-(η / 4) * (b : ℝ)) := by
      rw [← hsum] at hn hlo hhi ⊢
      exact sliceSplitWeight_bad_count_le (by omega) hη hlo hhi
    _ ≤ Real.exp (c * (n : ℝ)) * Real.exp (-(2 * c) * (n : ℝ)) :=
      mul_le_mul hC (Real.exp_monotone hB) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem sliceSplitWeight_bad_first_count_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ a b s : ℕ, a + b = n → σ * (n : ℝ) ≤ (a : ℝ) →
      η * (n : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (1 - η) * (n : ℝ) →
        (∑ j ∈ range (s + 1),
          if ((s - j : ℕ) : ℝ) < (η / 4) * (a : ℝ) ∨
            ((a - (s - j) : ℕ) : ℝ) < (η / 4) * (a : ℝ)
          then sliceSplitWeight a b s j else 0) ≤ Real.exp (-c * (n : ℝ)) := by
  obtain ⟨c, hc, h⟩ := sliceSplitWeight_bad_count_eventually hη hσ
  refine ⟨c, hc, h.mono fun n hn a b s hab ha hlo hhi => ?_⟩
  let Q (j : ℕ) := (j : ℝ) < (η / 4) * (a : ℝ) ∨ ((a - j : ℕ) : ℝ) < (η / 4) * (a : ℝ)
  have hswap := sum_ite_sliceSplitWeight_swap a b s Q
  change (∑ j ∈ range (s + 1), if Q (s - j) then sliceSplitWeight a b s j else 0) ≤ _
  rw [hswap]
  exact hn b a s ((Nat.add_comm b a).trans hab) ha hlo hhi

/-- Removing a sufficiently small block preserves near-balanced weights
in the first block, regardless of the second block's count. -/
theorem firstBlock_doubled_count_near_middle {a b s j : ℕ} {η : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hsize : (b : ℝ) ≤ η * ((a + b : ℕ) : ℝ) / 4)
    (hbalanced : |2 * (s : ℝ) - ((a + b : ℕ) : ℝ)| ≤ η * ((a + b : ℕ) : ℝ) / 2)
    (hjs : j ≤ s) (hjb : j ≤ b) :
    |2 * ((s - j : ℕ) : ℝ) - (a : ℝ)| ≤ η * (a : ℝ) := by
  push_cast at hsize hbalanced
  have ht : (0 : ℝ) ≤ (a : ℝ) + (b : ℝ) := by positivity
  have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hj₁ : (j : ℝ) ≤ b := by exact_mod_cast hjb
  have hsmall : (b : ℝ) ≤ ((a : ℝ) + (b : ℝ)) / 8 := by
    have h := mul_le_mul_of_nonneg_right hη' ht
    linarith only [h, hsize]
  have hbig : (3 / 4 : ℝ) * ((a : ℝ) + (b : ℝ)) ≤ (a : ℝ) := by linarith only [hsmall, ht]
  have hB : |(b : ℝ) - 2 * (j : ℝ)| ≤ (b : ℝ) :=
    abs_le.mpr ⟨by linarith only [hj₁], by linarith only [hj₀]⟩
  calc
    _ = |(2 * (s : ℝ) - ((a : ℝ) + (b : ℝ))) + ((b : ℝ) - 2 * (j : ℝ))| := by
      rw [Nat.cast_sub hjs]
      congr 1
      ring
    _ ≤ |2 * (s : ℝ) - ((a : ℝ) + (b : ℝ))| + |(b : ℝ) - 2 * (j : ℝ)| :=
      abs_add_le _ _
    _ ≤ η * ((a : ℝ) + (b : ℝ)) / 2 + (b : ℝ) := add_le_add hbalanced hB
    _ ≤ η * ((3 / 4 : ℝ) * ((a : ℝ) + (b : ℝ))) := by linarith only [hsize]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbig hη

/-- One may reserve a linear number of pairs for the suffix while keeping
the prefix nearly full and making every suffix count compatible with a
near-balanced prefix count. -/
theorem eventually_small_suffix_pairs_uniform_gamma {γ : ℝ} (hγ : 0 < γ) :
    ∃ γtotal > (0 : ℝ), γtotal ≤ 1 / 8 ∧ ∀ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∃ σ > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop,
        let k := ⌊c * (n : ℝ)⌋₊
        let b := 2 * k
        let a := n - b
        σ * (n : ℝ) ≤ (k : ℝ) ∧ b ≤ n ∧ (b : ℝ) ≤ δ * (n : ℝ) ∧
          (b : ℝ) ≤ γ * (n : ℝ) / 4 ∧ 3 * (n : ℝ) / 4 ≤ (a : ℝ) ∧
          ∀ s : ℕ, |2 * (s : ℝ) - (n : ℝ)| ≤ 2 * γtotal * (n : ℝ) →
            ∀ j ≤ b, j ≤ s ∧ s - j ≤ a ∧ |2 * ((s - j : ℕ) : ℝ) - (a : ℝ)| ≤ γ * (a : ℝ) := by
  let η := min γ (1 / 2)
  let γtotal := η / 4
  have hη : 0 < η := lt_min hγ (by norm_num)
  have hηγ : η ≤ γ := min_le_left _ _
  have hη₂ : η ≤ 1 / 2 := min_le_right _ _
  have hγtotal : 0 < γtotal := by dsimp [γtotal]; positivity
  have hγtotal₈ : γtotal ≤ 1 / 8 := by dsimp [γtotal]; linarith only [hη₂]
  refine ⟨γtotal, hγtotal, hγtotal₈, fun δ hδ => ?_⟩
  let ρ := min δ (η / 4)
  let c := ρ / 4
  let σ := c / 2
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  have hc : 0 < c := by dsimp [c]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  refine ⟨c, hc, σ, hσ, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈2 / c⌉₊] with n hn
  let k := ⌊c * (n : ℝ)⌋₊
  let b := 2 * k
  let a := n - b
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn₂ : 2 ≤ c * (n : ℝ) := by
    have h := (Nat.le_ceil (2 / c)).trans (show (⌈2 / c⌉₊ : ℝ) ≤ n by exact_mod_cast hn)
    rw [div_le_iff₀ hc, mul_comm] at h
    exact h
  have hklo : σ * (n : ℝ) ≤ (k : ℝ) := by
    have h := Nat.lt_floor_add_one (c * (n : ℝ))
    change c * (n : ℝ) < (k : ℝ) + 1 at h
    dsimp [σ]
    linarith only [h, hn₂]
  have hkhi : (k : ℝ) ≤ c * (n : ℝ) := Nat.floor_le (by positivity)
  have hbρ : (b : ℝ) ≤ ρ * (n : ℝ) := by
    have h := mul_nonneg hρ.le hn₀
    dsimp [b, c] at *
    push_cast
    linarith only [hkhi, h]
  have hbδ : (b : ℝ) ≤ δ * (n : ℝ) :=
    hbρ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn₀)
  have hbη : (b : ℝ) ≤ η * (n : ℝ) / 4 := by
    have hh := hbρ.trans (mul_le_mul_of_nonneg_right (min_le_right δ (η / 4)) hn₀)
    linarith only [hh]
  have hbγ : (b : ℝ) ≤ γ * (n : ℝ) / 4 :=
    hbη.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hηγ hn₀) (by norm_num))
  have hbn₈ : (b : ℝ) ≤ (n : ℝ) / 8 := by
    have hh := mul_le_mul_of_nonneg_right hη₂ hn₀
    linarith only [hbη, hh]
  have hbn : b ≤ n := by exact_mod_cast (show (b : ℝ) ≤ (n : ℝ) by linarith only [hbn₈, hn₀])
  have hab : a + b = n := Nat.sub_add_cancel hbn
  have ha : 3 * (n : ℝ) / 4 ≤ (a : ℝ) := by
    dsimp only [a]
    rw [Nat.cast_sub hbn]
    linarith only [hbn₈, hn₀]
  refine ⟨hklo, hbn, hbδ, hbγ, ha, ?_⟩
  intro s hs j hj
  have hs' : |2 * (s : ℝ) - (n : ℝ)| ≤ η * (n : ℝ) / 2 := by
    dsimp [γtotal] at hs
    linarith only [hs]
  have hs₄ : |2 * (s : ℝ) - (n : ℝ)| ≤ (n : ℝ) / 4 := by
    have h := mul_le_mul_of_nonneg_right hη₂ hn₀
    linarith only [hs', h]
  have hsb : b ≤ s := by
    exact_mod_cast (show (b : ℝ) ≤ (s : ℝ) by linarith only [hbn₈, hn₀, (abs_le.mp hs₄).1])
  have hsa : s ≤ a := by
    exact_mod_cast (show (s : ℝ) ≤ (a : ℝ) by linarith only [ha, hn₀, (abs_le.mp hs₄).2])
  have hjs : j ≤ s := hj.trans hsb
  refine ⟨hjs, (Nat.sub_le _ _).trans hsa, ?_⟩
  have hpre := firstBlock_doubled_count_near_middle hη.le hη₂ (a := a) (b := b) (s := s) (j := j)
    (by rw [hab]; exact hbη) (by rw [hab]; exact hs') hjs hj
  exact hpre.trans (mul_le_mul_of_nonneg_right hηγ (Nat.cast_nonneg _))

theorem eventually_small_suffix_pairs {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ c > (0 : ℝ), ∃ σ > (0 : ℝ), ∃ γtotal > (0 : ℝ), γtotal ≤ 1 / 8 ∧
      ∀ᶠ n : ℕ in atTop,
        let k := ⌊c * (n : ℝ)⌋₊
        let b := 2 * k
        let a := n - b
        σ * (n : ℝ) ≤ (k : ℝ) ∧ b ≤ n ∧ (b : ℝ) ≤ δ * (n : ℝ) ∧
          (b : ℝ) ≤ γ * (n : ℝ) / 4 ∧ 3 * (n : ℝ) / 4 ≤ (a : ℝ) ∧
          ∀ s : ℕ, |2 * (s : ℝ) - (n : ℝ)| ≤ 2 * γtotal * (n : ℝ) →
            ∀ j ≤ b, j ≤ s ∧ s - j ≤ a ∧ |2 * ((s - j : ℕ) : ℝ) - (a : ℝ)| ≤ γ * (a : ℝ) := by
  obtain ⟨γtotal, hγtotal, hγtotal₈, h⟩ := eventually_small_suffix_pairs_uniform_gamma hγ
  obtain ⟨c, hc, σ, hσ, h⟩ := h δ hδ
  exact ⟨c, hc, σ, hσ, γtotal, hγtotal, hγtotal₈, h⟩

end BooleanThreshold
