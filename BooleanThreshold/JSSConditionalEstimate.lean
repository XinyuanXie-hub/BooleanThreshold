module

public import BooleanThreshold.JSSConditionalCount
public import BooleanThreshold.JSSConditionalOperatorNorm
public import BooleanThreshold.JSSCorankConditional

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal Classical

namespace BooleanThreshold

/-- The integer small-ball counting input to the conditional normal estimate.
The window width and small-ball constant are uniform in the desired decay rate. -/
def ConditionalSmallBallCountEstimate : Prop :=
  ∀ δ ρ : ℝ, 0 < δ → δ < 1 → 0 < ρ → ρ < 1 →
    ∃ γ > (0 : ℝ), ∃ L ≥ (1 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ M ≥ (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, (3 / 5 : ℝ) ^ n ≤ u → u ≤ 1 / L →
        ((roundedConditionalCandidates n (uniformOn (balancedSignWindow n γ)) δ ρ L u).ncard : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * (C / u) ^ n

private theorem polynomial_eventually_le_exp (Q : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * (n : ℝ) ^ Q ≤ Real.exp (n : ℝ) := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt Q (Real.one_lt_exp_iff.mpr zero_lt_one)
  have h := ht.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h] with n hn
  have hh := (div_le_iff₀ (show 0 < Real.exp 1 ^ n by positivity)).mp hn
  rw [← Real.exp_nat_mul, mul_one] at hh
  linarith only [hh]

private theorem exceptional_conditional_prob_eventually
    {δ ρ γ L C : ℝ} (hγ : 0 < γ) (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hcount : ∀ M ≥ (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, (3 / 5 : ℝ) ^ n ≤ u → u ≤ 1 / L →
      ((roundedConditionalCandidates n (uniformOn (balancedSignWindow n γ)) δ ρ L u).ncard : ℝ) ≤
        Real.exp (-M * (n : ℝ)) * (C / u) ^ n) :
    ∀ᶠ n : ℕ in atTop, (uniformOn Set.univ).real
      (badConditionalNormal n (n - 1) (uniformOn (balancedSignWindow n γ)) δ ρ L ((3 / 5 : ℝ) ^ n)) ≤
        (1 / 4 : ℝ) ^ n := by
  obtain ⟨Q, _, hQ⟩ := few_unbalanced_rows_eventually hγ 4
  obtain ⟨K, hK, hKprob⟩ := signMatrix_norm_tail_exponential 4 (by norm_num)
  obtain ⟨N, hN⟩ := balancedWindow_mass_ge_half hγ
  let X := C * (1440 * L * Real.exp (2 * K)) * (5 / 3 : ℝ) ^ (Q + 1)
  have hX : 1 ≤ X := by
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ?_) (one_le_pow₀ (by norm_num))
    exact one_le_mul_of_one_le_of_one_le (by linarith only [hL]) (Real.one_le_exp (by positivity))
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  let M := 5 + Real.log X
  have hM : 0 ≤ M := add_nonneg (by norm_num) (Real.log_nonneg hX)
  have hMX : Real.exp (-M) * X = Real.exp (-5) := by
    rw [show -M = -5 + -Real.log X by dsimp [M]; ring, Real.exp_add,
      Real.exp_neg (Real.log X), Real.exp_log hX₀, mul_assoc, inv_mul_cancel₀ hX₀.ne', mul_one]
  filter_upwards [hcount M hM, hQ, polynomial_eventually_le_exp (Q + 1),
    eventually_ge_atTop (max N (2 * Q + 2))] with n hcountn hrows hpoly hn
  let m := n - 1
  let k := m - Q
  let W := balancedSignWindow n γ
  let β := (3 / 5 : ℝ) ^ n
  let μ : Measure (Fin m → Fin n → Bool) := uniformOn Set.univ
  have hn₀ : 0 < n := by omega
  have hn₂ : 2 ≤ n := (by omega : 2 ≤ max N (2 * Q + 2)).trans hn
  have hkn : k ≤ n := by dsimp [k, m]; omega
  have hhalf : n ≤ 2 * k := by
    have hnn := (le_max_right N (2 * Q + 2)).trans hn
    dsimp [k, m]
    omega
  have hW : W.Nonempty := by
    by_contra! h
    have hm : 1 / 2 ≤ (uniformOn Set.univ).real W := hN n ((le_max_left _ _).trans hn)
    rw [h, measureReal_empty] at hm
    norm_num at hm
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ₁ : β ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hJ : 1 ≤ β * (2 : ℝ) ^ n := by
    dsimp [β]
    rw [← mul_pow]
    exact one_le_pow₀ (by norm_num)
  have hu (j : ℕ) : β ≤ β * (2 : ℝ) ^ j :=
    le_mul_of_one_le_right hβ.le (one_le_pow₀ (by norm_num))
  have h := badConditionalNormal_prob_le_of_count (m := m) (J := n) hn₀ hkn hhalf W hW hL hβ hβ₁ hK.le hC
    (Real.exp_nonneg _) hJ (fun j _ hj => hcountn _ (hu j) hj)
  have hrow : μ.real {A : Fin m → Fin n → Bool | (Finset.univ.filter fun i => A i ∈ W).card < k} ≤
      Real.exp (-4 * (n : ℝ)) := by
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hrows m (Nat.sub_le _ _))
    intro A hA
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => A i ∈ W)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    change (Finset.univ.filter fun i => A i ∈ W).card < k at hA
    change Q ≤ (Finset.univ.filter fun i => A i ∉ W).card
    dsimp [k] at hA
    omega
  have hop : μ.real {A : Fin m → Fin n → Bool | ∃ a : Fin n → ℝ,
      K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) < ∑ j, (signSum a (A j)) ^ 2} ≤
        Real.exp (-4 * (n : ℝ)) := hKprob n m hn₀ (Nat.sub_le _ _)
  have hk₀ : k + Q = m := by dsimp [k, m]; omega
  have hchoose : (m.choose k : ℝ) ≤ (n : ℝ) ^ Q := by
    rw [Nat.choose_symm_of_eq_add hk₀.symm]
    exact_mod_cast (Nat.choose_le_pow m Q).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) Q)
  have hmul : (n + 1 : ℝ) * (m.choose k : ℝ) ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ (2 * (n : ℝ)) * (n : ℝ) ^ Q := by
        have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn₀
        gcongr
        linarith only [hn₁]
      _ = 2 * (n : ℝ) ^ (Q + 1) := by rw [pow_succ]; ring
      _ ≤ _ := hpoly
  have hexp : (n + 1 : ℝ) * (m.choose k : ℝ) * Real.exp (-M * (n : ℝ)) *
      (C * (1440 * L * Real.exp (2 * K))) ^ n / β ^ (n - k) ≤ Real.exp (-4 * (n : ℝ)) := by
    have hk₁ : n - k = Q + 1 := by dsimp [m] at hk₀; omega
    have hinv : (β ^ (n - k))⁻¹ = ((5 / 3 : ℝ) ^ (Q + 1)) ^ n := by
      rw [hk₁, ← inv_pow, show β⁻¹ = (5 / 3 : ℝ) ^ n by dsimp [β]; rw [← inv_pow]; norm_num,
        ← pow_mul, mul_comm n, pow_mul]
    rw [div_eq_mul_inv, hinv]
    calc
      _ ≤ Real.exp (n : ℝ) * Real.exp (-M * (n : ℝ)) *
          (C * (1440 * L * Real.exp (2 * K))) ^ n * ((5 / 3 : ℝ) ^ (Q + 1)) ^ n := by gcongr
      _ = Real.exp (n : ℝ) * ((Real.exp (-M)) ^ n * X ^ n) := by
        rw [show Real.exp (-M * (n : ℝ)) = Real.exp (-M) ^ n by rw [mul_comm, Real.exp_nat_mul]]
        dsimp only [X]
        rw [mul_pow (C * (1440 * L * Real.exp (2 * K)))]
        ring
      _ = _ := by
        rw [← mul_pow, hMX, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  refine h.trans ((add_le_add (add_le_add hrow hop) hexp).trans ?_)
  have hside : Real.exp (-4 * (n : ℝ)) ≤ (1 / 8 : ℝ) ^ n := by
    rw [mul_comm (-4 : ℝ), Real.exp_nat_mul]
    refine pow_le_pow_left₀ (Real.exp_nonneg _) ?_ _
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have h₄ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h₂ 4
    rw [← Real.exp_nat_mul] at h₄
    norm_num at h₄
    linarith only [h₄]
  calc
    _ ≤ 3 * (1 / 8 : ℝ) ^ n := by linarith only [hside]
    _ ≤ (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine (by norm_num : (3 : ℝ) ≤ 2 ^ 2).trans (pow_le_pow_right₀ (by norm_num) hn₂)
    _ = _ := by rw [← mul_pow]; norm_num

private theorem windowAtom_eq_conditional_mul {n : ℕ} (a : Fin n → ℝ) (W : Set (Fin n → Bool)) :
    windowAtom a W = uniformOn W {b | signSum a b = 0} * uniformOn Set.univ W := by
  unfold windowAtom
  change uniformOn Set.univ ({b | signSum a b = 0} ∩ W) = _
  rw [uniformOn_inter' Set.finite_univ, Set.univ_inter]

/-- The lattice-point counting input implies the uniform conditional estimate
for all unstructured unit normals simultaneously. -/
theorem uniformConditionalAtomEstimate_of_count
    (hCount : ConditionalSmallBallCountEstimate) : UniformConditionalAtomEstimate := by
  intro δ ρ hδ hd hρ hr
  obtain ⟨γ, hγ, L, hL, C, hC, hcount⟩ := hCount δ ρ hδ hd hρ hr
  let Lnn : ℝ≥0 := ⟨L, zero_le_one.trans hL⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (exceptional_conditional_prob_eventually hγ hL hC hcount)
  refine ⟨γ, hγ, Lnn, eventually_atTop.mpr ⟨N, fun m hm => ?_⟩⟩
  have hh := hN (m + 2) (by omega)
  let n := m + 2
  let W := balancedSignWindow n γ
  let β := (3 / 5 : ℝ) ^ n
  let ν := uniformOn W
  let θ := (Lnn : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ n * uniformOn Set.univ W
  have hsub : exceptionalConditionalNormalEvent (m + 1) n (almostConstantUnitVectors n δ ρ) W θ ⊆
      badConditionalNormal n (m + 1) ν δ ρ L β := by
    rintro A ⟨a, ha, hs, horth, hatom⟩
    refine ⟨a, ha, hs, horth, ?_⟩
    have hlt : (Lnn : ℝ≥0∞) * (3 / 5 : ℝ≥0∞) ^ n < ν {b | signSum a b = 0} := by
      rw [windowAtom_eq_conditional_mul] at hatom
      exact lt_of_not_ge (fun h => (not_le_of_gt hatom) (mul_le_mul_of_nonneg_right h zero_le))
    have hfin : ν {b | signSum a b = 0} ≠ ∞ := measure_ne_top _ _
    have hreal := (ENNReal.toReal_lt_toReal (by finiteness) hfin).mpr hlt
    have hLcoe : (Lnn : ℝ≥0∞).toReal = L := ENNReal.coe_toReal Lnn
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofNat, hLcoe, β] using hreal
  change (uniformOn Set.univ).real (exceptionalConditionalNormalEvent (m + 1) n
    (almostConstantUnitVectors n δ ρ) W θ) ≤ (1 / 4 : ℝ) ^ n
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [show (m + 2) - 1 = m + 1 by omega] at hh
  exact hh

end BooleanThreshold
