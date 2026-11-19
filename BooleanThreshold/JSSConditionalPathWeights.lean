module

public import BooleanThreshold.JSSConditionalTail
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- The number of occurrences of one bit in a prefix. -/
def prefixBitCount (w : ℕ → Bool) (b : Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => w i = b).card

/-- The weight of the recorded branch in a backward fixed-weight averaging step. -/
noncomputable def slicePathWeight (w : ℕ → Bool) (i : ℕ) : ℝ :=
  (prefixBitCount w (w i) (i + 1) : ℝ) / ((i : ℝ) + 1)

theorem prefixBitCount_le (w : ℕ → Bool) (b : Bool) (n : ℕ) : prefixBitCount w b n ≤ n := by
  simpa only [prefixBitCount, Finset.card_range] using Finset.card_filter_le (Finset.range n) _

theorem prefixBitCount_mono (w : ℕ → Bool) (b : Bool) : Monotone (prefixBitCount w b) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem prefixBitCount_succ (w : ℕ → Bool) (b : Bool) (n : ℕ) :
    prefixBitCount w b (n + 1) = prefixBitCount w b n + if w n = b then 1 else 0 := by
  unfold prefixBitCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : w n = b
  · simp only [h, ↓reduceIte]
    apply Finset.card_insert_of_notMem
    exact fun hm => Finset.notMem_range_self (Finset.mem_filter.mp hm).1
  · simp [h]

theorem prefixBitCount_add (w : ℕ → Bool) (n : ℕ) :
    prefixBitCount w false n + prefixBitCount w true n = n := by
  induction n with
  | zero => simp [prefixBitCount]
  | succ n ih =>
    rw [prefixBitCount_succ, prefixBitCount_succ]
    cases w n <;> simp <;> omega

theorem slicePathWeight_pos (w : ℕ → Bool) (i : ℕ) : 0 < slicePathWeight w i := by
  unfold slicePathWeight
  rw [prefixBitCount_succ]
  simp only [↓reduceIte]
  positivity

theorem slicePathWeight_le_one (w : ℕ → Bool) (i : ℕ) : slicePathWeight w i ≤ 1 := by
  unfold slicePathWeight
  rw [div_le_one₀ (by positivity)]
  exact_mod_cast prefixBitCount_le w (w i) (i + 1)

private theorem slicePathWeight_prod_factorial (w : ℕ → Bool) (n : ℕ) :
    (∏ i ∈ Finset.range n, slicePathWeight w i) =
      ((prefixBitCount w false n).factorial : ℝ) * ((prefixBitCount w true n).factorial : ℝ) /
        (n.factorial : ℝ) := by
  induction n with
  | zero => simp [prefixBitCount]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, slicePathWeight, prefixBitCount_succ w false, prefixBitCount_succ w true,
      prefixBitCount_succ w (w n), Nat.factorial_succ]
    cases w n
    all_goals simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Nat.add_zero,
      Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    all_goals field_simp

/-- The product of the branch weights of a fixed record is the reciprocal of
the size of its complete fixed-weight slice. -/
theorem slicePathWeight_prod_eq_inv_choose (w : ℕ → Bool) (n : ℕ) :
    (∏ i ∈ Finset.range n, slicePathWeight w i) = (n.choose (prefixBitCount w true n) : ℝ)⁻¹ := by
  rw [slicePathWeight_prod_factorial]
  have hcount := prefixBitCount_add w n
  have hc : (n.choose (prefixBitCount w true n) : ℝ) *
        ((prefixBitCount w true n).factorial : ℝ) * ((prefixBitCount w false n).factorial : ℝ) =
      (n.factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (prefixBitCount_le w true n)
    rw [show n - prefixBitCount w true n = prefixBitCount w false n by omega] at h
    exact_mod_cast h
  rw [← hc]
  field_simp

private theorem factorial_div_pow_large {n k : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1) (hk : (k : ℝ) ≤ ε * (n : ℝ)) :
    Real.exp (-2 * Real.sqrt ε * (n : ℝ)) ≤ (k.factorial : ℝ) / (n : ℝ) ^ k := by
  let q := Real.sqrt ε
  have hq : 0 < q := Real.sqrt_pos.mpr hε
  have hq₁ : q ≤ 1 := Real.sqrt_le_one.mpr hε'
  have hq₂ : q ^ 2 = ε := Real.sq_sqrt hε.le
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : -Real.log q ≤ 1 / q := by
    rw [← Real.log_inv, one_div]
    exact (Real.log_le_sub_one_of_pos (inv_pos.mpr hq)).trans (sub_le_self _ zero_le_one)
  have hL : -(q * (n : ℝ)) ≤ (k : ℝ) * Real.log q := by
    have hL₀ : 0 ≤ -Real.log q := neg_nonneg.mpr (Real.log_nonpos hq.le hq₁)
    have h := (mul_le_mul_of_nonneg_right hk hL₀).trans
      (mul_le_mul_of_nonneg_left hlog (by positivity))
    rw [show ε * (n : ℝ) * (1 / q) = q * (n : ℝ) by rw [← hq₂]; field_simp] at h
    linarith only [h]
  have hpow : Real.exp (-(q * (n : ℝ))) ≤ q ^ k := by
    have h := Real.exp_monotone hL
    rwa [Real.exp_nat_mul, Real.exp_log hq] at h
  have hfac := (div_le_iff₀ (by positivity : (0 : ℝ) < (k.factorial : ℝ))).mp
    (Real.pow_div_factorial_le_exp (q * (n : ℝ)) (by positivity) k)
  have hfac' : q ^ k * Real.exp (-(q * (n : ℝ))) ≤ (k.factorial : ℝ) / (n : ℝ) ^ k := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [show q ^ k * Real.exp (-(q * (n : ℝ))) * (n : ℝ) ^ k =
        (Real.exp (q * (n : ℝ)))⁻¹ * (q * (n : ℝ)) ^ k by rw [Real.exp_neg, mul_pow]; ring]
    exact (mul_le_mul_of_nonneg_left hfac (by positivity)).trans_eq (by field_simp)
  calc
    _ = Real.exp (-(q * (n : ℝ))) * Real.exp (-(q * (n : ℝ))) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ q ^ k * Real.exp (-(q * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ ≤ _ := hfac'

private theorem low_pathWeight_prod (w : ℕ → Bool) (n : ℕ) (hn : 0 < n) (b : Bool)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) :
    Real.exp (-2 * Real.sqrt ε * (n : ℝ)) ≤
      ∏ i ∈ (Finset.range n).filter (fun i => w i = b ∧ slicePathWeight w i < ε), slicePathWeight w i := by
  let U := (Finset.range n).filter (fun i => w i = b ∧ slicePathWeight w i < ε)
  let K := ⌊ε * (n : ℝ)⌋₊
  let f (i : ℕ) := prefixBitCount w b (i + 1) - 1
  let g (j : ℕ) : ℝ := ((j : ℝ) + 1) / (n : ℝ)
  have hn₀ : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hK : (K : ℝ) ≤ ε * (n : ℝ) := Nat.floor_le (by positivity)
  have hmem (i : ℕ) (hi : i ∈ U) : i < n ∧ w i = b ∧ slicePathWeight w i < ε := by
    simpa only [U, Finset.mem_filter, Finset.mem_range] using hi
  have hpositive (i : ℕ) (hi : i ∈ U) : 0 < prefixBitCount w b (i + 1) := by
    rw [prefixBitCount_succ]
    simp only [(hmem i hi).2.1, ↓reduceIte]
    omega
  have hfsub : U.image f ⊆ Finset.range K := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hin, hib, hlo⟩ := hmem i hi
    have hilo : (prefixBitCount w b (i + 1) : ℝ) ≤ ε * (n : ℝ) := by
      unfold slicePathWeight at hlo
      rw [hib, div_lt_iff₀ (by positivity)] at hlo
      have hh : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hin
      exact hlo.le.trans (mul_le_mul_of_nonneg_left hh hε.le)
    have hcount : prefixBitCount w b (i + 1) ≤ K := (Nat.le_floor_iff (by positivity)).mpr hilo
    exact Finset.mem_range.mpr (by dsimp [f]; have := hpositive i hi; omega)
  have hfinj : Set.InjOn f U := by
    intro i hi j hj heq
    have hint (x y : ℕ) (hxy : x < y) (hy : y ∈ U) :
        prefixBitCount w b (x + 1) < prefixBitCount w b (y + 1) := by
      rw [prefixBitCount_succ w b y]
      simp only [(hmem y hy).2.1, ↓reduceIte]
      exact Nat.lt_succ_of_le (prefixBitCount_mono w b (Nat.succ_le_of_lt hxy))
    have hi' : i ∈ U := hi
    have hj' : j ∈ U := hj
    have hpi := hpositive i hi'
    have hpj := hpositive j hj'
    dsimp [f] at heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hh := hint i j hij hj'
      omega
    · rfl
    · have hh := hint j i hji hi'
      omega
  have hg (i : ℕ) (hi : i ∈ U) : g (f i) ≤ slicePathWeight w i := by
    obtain ⟨hin, hib, _⟩ := hmem i hi
    have hi₁ : 1 ≤ prefixBitCount w b (i + 1) := hpositive i hi
    have he : ((f i : ℕ) : ℝ) + 1 = (prefixBitCount w b (i + 1) : ℝ) := by
      dsimp [f]
      rw [Nat.cast_sub hi₁, Nat.cast_one, sub_add_cancel]
    unfold slicePathWeight
    rw [hib, show g (f i) = (prefixBitCount w b (i + 1) : ℝ) / (n : ℝ) by dsimp [g]; rw [he]]
    have hnI : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hin
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnI
  have he : (∏ j ∈ Finset.range K, g j) = (K.factorial : ℝ) / (n : ℝ) ^ K := by
    dsimp [g]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    exact_mod_cast Finset.prod_range_add_one_eq_factorial K
  have hKn : K ≤ n := by
    have hcast : (K : ℝ) ≤ (n : ℝ) := hK.trans (mul_le_of_le_one_left hn₀.le hε')
    exact_mod_cast hcast
  calc
    _ ≤ (K.factorial : ℝ) / (n : ℝ) ^ K := factorial_div_pow_large hn hε hε' hK
    _ = ∏ j ∈ Finset.range K, g j := he.symm
    _ ≤ ∏ j ∈ U.image f, g j := by
      apply Finset.prod_le_prod_of_subset_of_le_one₀ hfsub (fun _ _ => by dsimp [g]; positivity)
      intro j hj _
      apply (div_le_one₀ hn₀).mpr
      have hj' := (Finset.mem_range.mp hj).trans_le hKn
      exact_mod_cast Nat.succ_le_of_lt hj'
    _ = ∏ i ∈ U, g (f i) := Finset.prod_image hfinj
    _ ≤ _ := Finset.prod_le_prod₀ (fun j _ => by dsimp [g]; positivity) hg

private theorem high_pathWeight_prod (w : ℕ → Bool) (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 2) :
    Real.exp (-2 * ε * (n : ℝ)) ≤
      ∏ i ∈ (Finset.range n).filter (fun i => 1 - ε < slicePathWeight w i), slicePathWeight w i := by
  let V := (Finset.range n).filter (fun i => 1 - ε < slicePathWeight w i)
  have hp : 0 < 1 - ε := by linarith only [hε']
  have hlog : -Real.log (1 - ε) ≤ 2 * ε := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at h
    refine h.trans ?_
    rw [← one_div, sub_le_iff_le_add, div_le_iff₀ hp]
    nlinarith only [hε', hε, mul_nonneg hε.le (show 0 ≤ 1 - 2 * ε by linarith only [hε'])]
  have hV : V.card ≤ n := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range n)
  calc
    _ ≤ Real.exp ((n : ℝ) * Real.log (1 - ε)) := by
      apply Real.exp_monotone
      nlinarith only [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    _ = (1 - ε) ^ n := by rw [Real.exp_nat_mul, Real.exp_log hp]
    _ ≤ (1 - ε) ^ V.card := pow_le_pow_of_le_one hp.le (by linarith only [hε]) hV
    _ = ∏ _i ∈ V, (1 - ε) := (Finset.prod_const _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hp.le) (fun i hi => (Finset.mem_filter.mp hi).2.le)

/-- The branch-weight product over nonrobust steps loses at most a factor
exponential in `sqrt ε * n`, uniformly over all records. -/
theorem slicePathWeight_nonrobust_prod_lower (w : ℕ → Bool) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    Real.exp (-6 * Real.sqrt ε * (n : ℝ)) ≤
      ∏ i ∈ (Finset.range n).filter (fun i => ¬(ε ≤ slicePathWeight w i ∧
        slicePathWeight w i ≤ 1 - ε)), slicePathWeight w i := by
  let F (b : Bool) := (Finset.range n).filter (fun i => w i = b ∧ slicePathWeight w i < ε)
  let V := (Finset.range n).filter (fun i => 1 - ε < slicePathWeight w i)
  have hpart : (Finset.range n).filter (fun i => ¬(ε ≤ slicePathWeight w i ∧
      slicePathWeight w i ≤ 1 - ε)) = F false ∪ F true ∪ V := by
    ext i
    cases h : w i
    all_goals simp only [F, V, Finset.mem_filter, Finset.mem_union, h, and_false,
      Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, false_or, or_false, not_and_or, not_le]
    all_goals tauto
  have hF : Disjoint (F false) (F true) := by
    rw [Finset.disjoint_left]
    intro i hf ht
    have h := (Finset.mem_filter.mp hf).2.1.symm.trans (Finset.mem_filter.mp ht).2.1
    cases h
  have hFV : Disjoint (F false ∪ F true) V := by
    rw [Finset.disjoint_left]
    intro i hf hv
    have h₀ : slicePathWeight w i < ε := (Finset.mem_union.mp hf).elim
      (fun h => (Finset.mem_filter.mp h).2.2) (fun h => (Finset.mem_filter.mp h).2.2)
    have h₁ := (Finset.mem_filter.mp hv).2
    linarith only [hε', h₀, h₁]
  have hε₁ : ε ≤ 1 := by linarith only [hε']
  rw [hpart, Finset.prod_union hFV, Finset.prod_union hF]
  calc
    _ ≤ Real.exp (-2 * Real.sqrt ε * (n : ℝ)) * Real.exp (-2 * Real.sqrt ε * (n : ℝ)) *
        Real.exp (-2 * ε * (n : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_monotone
      have hs : ε ≤ Real.sqrt ε := by
        simpa only [← pow_two, Real.sq_sqrt hε.le] using
          mul_le_of_le_one_right (Real.sqrt_nonneg ε) (Real.sqrt_le_one.mpr hε₁)
      nlinarith only [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    _ ≤ _ := by
      have hf := low_pathWeight_prod w n hn false hε hε₁
      have ht := low_pathWeight_prod w n hn true hε hε₁
      have hv := high_pathWeight_prod w n hε hε'
      gcongr
      all_goals unfold slicePathWeight; positivity

end BooleanThreshold
