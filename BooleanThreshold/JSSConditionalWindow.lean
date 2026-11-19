module

public import BooleanThreshold.JSSConditionalTail
public import BooleanThreshold.SignWindow
public import BooleanThreshold.Asymptotics

public section

open scoped BigOperators Topology ENNReal Classical
open MeasureTheory ProbabilityTheory Filter

namespace BooleanThreshold

/-- Failure of the balanced-window condition has an exponential tail. -/
theorem balancedSignWindow_compl_prob_le {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} (hγ : 0 ≤ γ) :
    (uniformOn Set.univ).real (balancedSignWindow n γ)ᶜ ≤
      2 * Real.exp (-2 * γ ^ 2 * (n : ℝ)) := by
  let a : Fin n → ℝ := fun _ => (Real.sqrt (n : ℝ))⁻¹
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  have ha : ∑ i, a i ^ 2 = 1 := by
    simp [a, inv_pow, Real.sq_sqrt hn₀.le, mul_inv_cancel₀ hn₀.ne']
  let u := 2 * γ * Real.sqrt (n : ℝ)
  have hu : 0 ≤ u := by positivity
  have hsub : (balancedSignWindow n γ)ᶜ ⊆ {x | u ≤ |signSum a x|} := by
    intro x hx
    have hsum : signSum a x = (∑ i, realSigns x i) / Real.sqrt (n : ℝ) := by
      rw [div_eq_mul_inv, mul_comm, Finset.mul_sum]
      rfl
    change ¬ |∑ i, realSigns x i| ≤ 2 * γ * (n : ℝ) at hx
    change u ≤ |signSum a x|
    rw [hsum, abs_div, abs_of_pos hnS, le_div_iff₀ hnS]
    change 2 * γ * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ≤ _
    rw [mul_assoc (2 * γ), ← pow_two, Real.sq_sqrt hn₀.le]
    exact (lt_of_not_ge hx).le
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have ht := signSum_abs_tail_le a ha hu
  have heq : -u ^ 2 / 2 = -2 * γ ^ 2 * (n : ℝ) := by
    simp only [u, mul_pow, Real.sq_sqrt hn₀.le]
    ring
  simpa only [heq] using ht

/-- Union bound for a prescribed number of rows in a fixed event. -/
theorem uniformMatrix_many_rows_prob_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (U : Set Ω) (m k : ℕ) :
    (uniformOn Set.univ).real {A : Fin m → Ω | k ≤ (Finset.univ.filter (fun i => A i ∈ U)).card}
      ≤ (m.choose k : ℝ) * ((uniformOn Set.univ).real U) ^ k := by
  classical
  let μ : Measure (Fin m → Ω) := uniformOn Set.univ
  let ν : Measure Ω := uniformOn Set.univ
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let choices := (Finset.univ : Finset (Fin m)).powersetCard k
  let E (I : Finset (Fin m)) : Set (Fin m → Ω) := {A | ∀ i ∈ I, A i ∈ U}
  have hsub :
      {A : Fin m → Ω | k ≤ (Finset.univ.filter (fun i => A i ∈ U)).card} ⊆
        ⋃ I ∈ choices, E I := by
    intro A hA
    obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq hA
    exact Set.mem_iUnion₂.mpr
      ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩,
        fun i hi => (Finset.mem_filter.mp (hI hi)).2⟩
  have hrectangle (I : Finset (Fin m)) : μ.real (E I) = (ν.real U) ^ I.card := by
    let S (i : Fin m) := if i ∈ I then U else Set.univ
    have hE : E I = Set.pi Set.univ S := by
      ext A
      simp only [E, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h i
        by_cases hi : i ∈ I <;> simp [S, hi, h]
      · intro h i hi
        simpa [S, hi] using h i
    have hμ : μ = Measure.pi (fun _ : Fin m => ν) := pi_uniformOn_univ.symm
    rw [hE, hμ, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
    simp only [S, apply_ite ν, measure_univ, apply_ite ENNReal.toReal, ENNReal.toReal_one,
      ← measureReal_def, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    _ ≤ μ.real (⋃ I ∈ choices, E I) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ I ∈ choices, μ.real (E I) := measureReal_biUnion_finset_le _ _
    _ = ∑ _I ∈ choices, (ν.real U) ^ k := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [hrectangle, (Finset.mem_powersetCard.mp hI).2]
    _ = _ := by simp [choices, ν, Finset.card_powersetCard]

/-- For a fixed-width balancing window, there is a fixed count threshold above
which the probability of seeing unbalanced rows decays at any prescribed rate. -/
theorem few_unbalanced_rows_eventually {γ : ℝ} (hγ : 0 < γ) (B : ℝ) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ᶠ n : ℕ in atTop, ∀ m ≤ n,
      (uniformOn Set.univ).real {A : Fin m → Fin n → Bool |
        Q ≤ (Finset.univ.filter (fun i => A i ∉ balancedSignWindow n γ)).card} ≤
        Real.exp (-B * (n : ℝ)) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_nat_ge ((B + 1) / γ ^ 2)
  let Q := Q₀ + 1
  have hQ : 0 < Q := by omega
  have hQbound : B + 1 ≤ γ ^ 2 * (Q : ℝ) := by
    rw [mul_comm]
    apply (div_le_iff₀ (by positivity : 0 < γ ^ 2)).mp
    exact hQ₀.trans (by exact_mod_cast (show Q₀ ≤ Q by omega))
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / γ ^ 2)
  have hpolynomial : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ Q / Real.exp 1 ^ n ≤ 1 := by
    have ht := tendsto_pow_const_div_const_pow_of_one_lt Q (Real.one_lt_exp_iff.mpr zero_lt_one)
    exact ht.eventually_le_const (show (0 : ℝ) < 1 from zero_lt_one)
  refine ⟨Q, hQ, ((eventually_ge_atTop (max 1 N)).and hpolynomial).mono ?_⟩
  intro n hn m hm
  have hn₁ := (le_max_left 1 N).trans hn.1
  have hnN := (le_max_right 1 N).trans hn.1
  have h2 : (2 : ℝ) ≤ Real.exp (γ ^ 2 * (n : ℝ)) := by
    have hz : (1 : ℝ) ≤ γ ^ 2 * (n : ℝ) := by
      rw [mul_comm]
      apply (div_le_iff₀ (by positivity : 0 < γ ^ 2)).mp
      exact hN.trans (by exact_mod_cast hnN)
    have hz' : (2 : ℝ) ≤ γ ^ 2 * (n : ℝ) + 1 := by linarith only [hz]
    exact hz'.trans (Real.add_one_le_exp _)
  let U := (balancedSignWindow n γ)ᶜ
  have hrow : (uniformOn Set.univ).real U ≤ Real.exp (-γ ^ 2 * (n : ℝ)) := by
    calc
      _ ≤ 2 * Real.exp (-2 * γ ^ 2 * (n : ℝ)) := balancedSignWindow_compl_prob_le hn₁ hγ.le
      _ ≤ Real.exp (γ ^ 2 * (n : ℝ)) * Real.exp (-2 * γ ^ 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hc : (m.choose Q : ℝ) ≤ (n : ℝ) ^ Q := by
    exact_mod_cast (Nat.choose_le_pow m Q).trans (Nat.pow_le_pow_left hm Q)
  have hp : (n : ℝ) ^ Q ≤ Real.exp (n : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < Real.exp 1 ^ n)).1 hn.2
    simpa only [one_mul, ← Real.exp_nat_mul, mul_one] using h
  calc
    _ ≤ (m.choose Q : ℝ) * ((uniformOn Set.univ).real U) ^ Q := by
      simpa only [U, Set.mem_compl_iff] using uniformMatrix_many_rows_prob_le U m Q
    _ ≤ (n : ℝ) ^ Q * Real.exp (-γ ^ 2 * (n : ℝ)) ^ Q := by gcongr
    _ ≤ Real.exp (n : ℝ) * Real.exp (-γ ^ 2 * (n : ℝ)) ^ Q := by gcongr
    _ = Real.exp ((1 - (Q : ℝ) * γ ^ 2) * (n : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      have hlast : 1 - (Q : ℝ) * γ ^ 2 ≤ -B := by
        rw [mul_comm (Q : ℝ)]
        linarith only [hQbound]
      apply Real.exp_monotone
      simpa only [neg_mul] using mul_le_mul_of_nonneg_right hlast (Nat.cast_nonneg n)

end BooleanThreshold
