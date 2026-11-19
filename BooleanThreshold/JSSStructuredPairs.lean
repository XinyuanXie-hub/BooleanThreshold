module

public import BooleanThreshold.JSSStructuredGeometry
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BooleanThreshold

/-- Encode a zero difference by `none` and retain the sign of a nonzero
difference in the first entry. -/
def differenceCode (x y : Bool) : Option Bool := if x = y then none else some x

theorem differenceCode_ne_none_iff (x y : Bool) :
    differenceCode x y ≠ none ↔ x ≠ y := by
  cases x <;> cases y <;> decide

private theorem half_mul_half : (1 / 2 : ℝ≥0∞) * (1 / 2) = 1 / 4 := by
  have h : (1 / 2 : ℝ≥0) * (1 / 2) = 1 / 4 := by
    apply NNReal.eq
    norm_num
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h

private theorem quarter_add_quarter : (1 / 4 : ℝ≥0∞) + (1 / 4) = 1 / 2 := by
  have h : (1 / 4 : ℝ≥0) + (1 / 4) = 1 / 2 := by
    apply NNReal.eq
    norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h

private theorem uniformOn_two_bits {n : ℕ} (i j : Fin n) (hij : i ≠ j) (b c : Bool) :
    uniformOn Set.univ {x : Fin n → Bool | x i = b ∧ x j = c} = 1 / 4 := by
  classical
  let μ : Measure Bool := uniformOn Set.univ
  let A (k : Fin n) : Set Bool := if k = i then {b} else if k = j then {c} else Set.univ
  have hA : {x : Fin n → Bool | x i = b ∧ x j = c} = Set.univ.pi A := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor
    · rintro ⟨hi, hj⟩ k
      by_cases hki : k = i
      · subst k
        simpa [A] using hi
      · by_cases hkj : k = j
        · subst k
          simpa [A, hki] using hj
        · simp [A, hki, hkj]
    · intro h
      exact ⟨by simpa [A] using h i, by simpa [A, Ne.symm hij] using h j⟩
  rw [hA, ← pi_uniformOn_univ, Measure.pi_pi]
  change (∏ k : Fin n, μ (A k)) = _
  rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset (Fin n))) (by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp only [A, ite_eq_right hk.1, ite_eq_right hk.2]
    exact measure_univ)]
  rw [Finset.prod_pair hij]
  simp only [A, ite_eq_left rfl, ite_eq_right (Ne.symm hij), ite_true]
  have hμ (a : Bool) : μ {a} = (1 / 2 : ℝ≥0∞) := by
    change uniformOn Set.univ {a} = _
    rw [uniformOn_univ, Measure.count_singleton, Fintype.card_bool]
    rfl
  rw [hμ, hμ, half_mul_half]

private theorem uniformOn_xor {n : ℕ} (i j : Fin n) (hij : i ≠ j) (b : Bool) :
    uniformOn Set.univ {x : Fin n → Bool | (x i ^^ x j) = b} = 1 / 2 := by
  let F : Set (Fin n → Bool) := {x | x i = false ∧ x j = b}
  let T : Set (Fin n → Bool) := {x | x i = true ∧ x j = !b}
  have h : {x : Fin n → Bool | (x i ^^ x j) = b} = F ∪ T := by
    ext x
    cases hi : x i <;> cases hj : x j <;> cases b <;> simp [F, T, hi, hj]
  have hd : Disjoint F T := by
    refine Set.disjoint_left.mpr ?_
    intro x hf ht
    exact Bool.false_ne_true (hf.1.symm.trans ht.1)
  rw [h, measure_union hd (Set.toFinite T).measurableSet]
  change (uniformOn Set.univ) {x : Fin n → Bool | x i = false ∧ x j = b} +
    (uniformOn Set.univ) {x : Fin n → Bool | x i = true ∧ x j = !b} = _
  rw [uniformOn_two_bits i j hij, uniformOn_two_bits i j hij, quarter_add_quarter]

private theorem uniformOn_mismatch_set {m n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (I : Finset (Fin m)) :
    uniformOn Set.univ {M : Fin m → Fin n → Bool |
      (Finset.univ.filter fun k => M k i ≠ M k j) = I} = (1 / 2 : ℝ≥0∞) ^ m := by
  let A (k : Fin m) : Set (Fin n → Bool) := {x | x i ≠ x j ↔ k ∈ I}
  have h : {M : Fin m → Fin n → Bool | (Finset.univ.filter fun k => M k i ≠ M k j) = I} =
      Set.univ.pi A := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, A, Finset.ext_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hA (k : Fin m) : uniformOn Set.univ (A k) = 1 / 2 := by
    by_cases hk : k ∈ I
    · have he : A k = {x : Fin n → Bool | (x i ^^ x j) = true} := by
        ext x
        cases hi : x i <;> cases hj : x j <;> simp [A, hk, hi, hj]
      rw [he, uniformOn_xor i j hij]
    · have he : A k = {x : Fin n → Bool | (x i ^^ x j) = false} := by
        ext x
        cases hi : x i <;> cases hj : x j <;> simp [A, hk, hi, hj]
      rw [he, uniformOn_xor i j hij]
  rw [h, ← pi_uniformOn_univ, Measure.pi_pi]
  simp [hA]

/-- A uniformly sampled pair of columns disagrees on at most `k` rows with
probability at most the binomial lower tail with fair independent trials. -/
theorem uniformOn_sparse_columnDifference {m n k : ℕ} (i j : Fin n) (hij : i ≠ j) :
    uniformOn Set.univ {M : Fin m → Fin n → Bool |
      (Finset.univ.filter fun k => M k i ≠ M k j).card ≤ k} ≤
      (1 / 2 : ℝ≥0∞) ^ m * ∑ l ∈ Finset.range (k + 1), (m.choose l : ℝ≥0∞) := by
  let E (I : Finset (Fin m)) : Set (Fin m → Fin n → Bool) :=
    {M | (Finset.univ.filter fun k => M k i ≠ M k j) = I}
  let Isets (l : ℕ) := (Finset.univ : Finset (Fin m)).powersetCard l
  have hsub : {M : Fin m → Fin n → Bool | (Finset.univ.filter fun k => M k i ≠ M k j).card ≤ k} ⊆
      ⋃ l ∈ Finset.range (k + 1), ⋃ I ∈ Isets l, E I := by
    intro M hM
    let I := Finset.univ.filter fun k => M k i ≠ M k j
    have hc : I.card ≤ k := hM
    exact Set.mem_iUnion₂.mpr ⟨I.card, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hc),
      Set.mem_iUnion₂.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, rfl⟩⟩
  calc
    _ ≤ uniformOn Set.univ (⋃ l ∈ Finset.range (k + 1), ⋃ I ∈ Isets l, E I) := measure_mono hsub
    _ ≤ ∑ l ∈ Finset.range (k + 1), uniformOn Set.univ (⋃ I ∈ Isets l, E I) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ Finset.range (k + 1), ∑ I ∈ Isets l, uniformOn Set.univ (E I) :=
      Finset.sum_le_sum fun l _ => measure_biUnion_finset_le _ _
    _ = _ := by
      simp_rw [E, uniformOn_mismatch_set i j hij]
      rw [Finset.mul_sum]
      simp [Isets, mul_comm]

/-- Truncating the binomial sum counts sparse sign patterns. An exponential
weight turns the partial sum into a full binomial expansion. -/
theorem sum_choose_le_pow_div {m k : ℕ} (hk : k ≤ m) {s : ℝ}
    (hs : 0 < s) (hs₁ : s ≤ 1) :
    (∑ l ∈ Finset.range (k + 1), (m.choose l : ℝ)) ≤ (1 + s) ^ m / s ^ k := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ l ∈ Finset.range (k + 1), s ^ l * (m.choose l : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hl' : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs.le hs₁ hl') (Nat.cast_nonneg _)
    _ ≤ ∑ l ∈ Finset.range (m + 1), s ^ l * (m.choose l : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hk))
        (fun _ _ _ => by positivity)
    _ = _ := by simpa [add_comm] using (add_pow s (1 : ℝ) m).symm

/-- Weighted counts of sparse coordinate sets can have arbitrarily small
exponential growth as their allowed fraction decreases. -/
theorem exists_sparse_count_growth_bound {B R : ℝ} (hB : 1 ≤ B) (hR : 1 < R) :
    ∃ δ > (0 : ℝ), ∀ n k : ℕ, k ≤ n → (k : ℝ) ≤ δ * (n : ℝ) →
      (∑ l ∈ Finset.range (k + 1), (n.choose l : ℝ)) * B ^ k ≤ R ^ n := by
  let s : ℝ := min (1 / 2) ((R - 1) / 2)
  have hs : 0 < s := lt_min (by norm_num) (by linarith only [hR])
  have hs₁ : s < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsR : 1 + s < R := by linarith only [(min_le_right (1 / 2 : ℝ) ((R - 1) / 2)), hR]
  have hsB : s < B := hs₁.trans_le hB
  have hlogB : 0 < Real.log (B / s) := Real.log_pos ((lt_div_iff₀ hs).mpr (by simpa using hsB))
  have hspos : 0 < 1 + s := by positivity
  have hlogR : 0 < Real.log (R / (1 + s)) :=
    Real.log_pos ((lt_div_iff₀ hspos).mpr (by simpa using hsR))
  let δ := Real.log (R / (1 + s)) / Real.log (B / s)
  refine ⟨δ, div_pos hlogR hlogB, fun n k hkn hk => ?_⟩
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hlog : (k : ℝ) * Real.log (B / s) ≤ (n : ℝ) * Real.log (R / (1 + s)) := by
    calc
      _ ≤ δ * (n : ℝ) * Real.log (B / s) := mul_le_mul_of_nonneg_right hk hlogB.le
      _ = _ := by
        rw [mul_comm δ _, mul_assoc]
        congr 1
        exact div_mul_cancel₀ _ hlogB.ne'
  rw [Real.log_div hRpos.ne' hspos.ne'] at hlog
  calc
    _ ≤ ((1 + s) ^ n / s ^ k) * B ^ k :=
      mul_le_mul_of_nonneg_right (sum_choose_le_pow_div hkn hs hs₁.le) (by positivity)
    _ = (1 + s) ^ n * (B / s) ^ k := by rw [div_pow]; ring
    _ ≤ _ := by
      apply (Real.log_le_log_iff (by positivity) (pow_pos hRpos _)).mp
      rw [Real.log_mul (pow_pos hspos _).ne' (pow_pos (div_pos hBpos hs) _).ne',
        Real.log_pow, Real.log_pow, Real.log_pow]
      linarith only [hlog]

/-- The near-pair kernel event with a nonzero difference is controlled by
a fixed-target bound on the sparse difference patterns. -/
theorem uniformOn_nonzeroNearPair_le_of_conditional {m n k : ℕ} {K ε : ℝ}
    (hε : ε ^ 2 < 1) (hsparse : K ^ 2 * (m : ℝ) * ε ^ 2 ≤ 4 * (k : ℝ))
    (i j : Fin n) (hij : i ≠ j) {q : ℝ≥0∞}
    (hconditional : ∀ d : Fin m → Option Bool,
      d ≠ (fun _ => none) → (Finset.univ.filter fun l => d l ≠ none).card ≤ k →
      uniformOn Set.univ {M : Fin m → Fin n → Bool |
        (fun l => differenceCode (M l i) (M l j)) = d ∧
        signMatrixMap M (Pi.single i 1 - Pi.single j 1) ∈
          (equalCoefficientSubspace i j).map (signMatrixMap M)} ≤
      q * uniformOn Set.univ {M : Fin m → Fin n → Bool |
        (fun l => differenceCode (M l i) (M l j)) = d}) :
    uniformOn Set.univ {M : Fin m → Fin n → Bool |
      (fun r => differenceCode (M r i) (M r j)) ≠ (fun _ => none) ∧
      signOpBound K M ∧ ∃ a, signMatrixMap M a = 0 ∧
        squaredNorm (Pi.single i 1 - Pi.single j 1 - a) ≤ ε ^ 2} ≤
      q * ((1 / 2 : ℝ≥0∞) ^ m *
        ∑ l ∈ Finset.range (k + 1), (m.choose l : ℝ≥0∞)) := by
  classical
  let pattern (M : Fin m → Fin n → Bool) (l : Fin m) := differenceCode (M l i) (M l j)
  let zeroPattern : Fin m → Option Bool := fun _ => none
  let codes := Finset.univ.filter fun d : Fin m → Option Bool => d ≠ zeroPattern ∧
    (Finset.univ.filter fun l => d l ≠ none).card ≤ k
  let F (d : Fin m → Option Bool) : Set (Fin m → Fin n → Bool) := {M | pattern M = d}
  let P : Set (Fin m → Fin n → Bool) := {M |
    signMatrixMap M (Pi.single i 1 - Pi.single j 1) ∈
      (equalCoefficientSubspace i j).map (signMatrixMap M)}
  let sparse : Set (Fin m → Fin n → Bool) := {M |
    (Finset.univ.filter fun l => M l i ≠ M l j).card ≤ k}
  let E : Set (Fin m → Fin n → Bool) := {M | pattern M ≠ zeroPattern ∧ signOpBound K M ∧
    ∃ a, signMatrixMap M a = 0 ∧ squaredNorm (Pi.single i 1 - Pi.single j 1 - a) ≤ ε ^ 2}
  have hfilter (M : Fin m → Fin n → Bool) :
      (Finset.univ.filter fun l => pattern M l ≠ none) =
        Finset.univ.filter fun l => M l i ≠ M l j := by
    simp_rw [pattern, differenceCode_ne_none_iff]
  have hcover : E ⊆ ⋃ d ∈ codes, F d ∩ P := by
    rintro M ⟨hz, hM, a, ha, hclose⟩
    have hsmall := (column_diff_support_le_of_near_null hM i j ha hclose).trans hsparse
    have hcard : (Finset.univ.filter fun l => M l i ≠ M l j).card ≤ k := by
      exact_mod_cast (le_of_mul_le_mul_left hsmall (by norm_num : (0 : ℝ) < 4))
    have hcode : pattern M ∈ codes :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, by rw [hfilter]; exact hcard⟩
    exact Set.mem_iUnion₂.mpr ⟨pattern M, hcode, rfl,
      column_diff_mem_span_of_near_null hij hε ha hclose⟩
  have hdisj : (↑codes : Set (Fin m → Option Bool)).PairwiseDisjoint F := by
    intro d _ e _ hde
    refine Set.disjoint_left.mpr fun M hMd hMe => hde ?_
    exact (show pattern M = d from hMd).symm.trans hMe
  have hcodes : (⋃ d ∈ codes, F d) ⊆ sparse := by
    intro M hM
    obtain ⟨d, hd, hMd⟩ := Set.mem_iUnion₂.mp hM
    have hpat : pattern M = d := hMd
    change (Finset.univ.filter fun l => M l i ≠ M l j).card ≤ k
    rw [← hfilter, hpat]
    exact (Finset.mem_filter.mp hd).2.2
  have hsum : (∑ d ∈ codes, uniformOn Set.univ (F d)) ≤ uniformOn Set.univ sparse := by
    rw [← measure_biUnion_finset hdisj (fun _ _ => (Set.toFinite _).measurableSet)]
    exact measure_mono hcodes
  calc
    _ ≤ uniformOn Set.univ (⋃ d ∈ codes, F d ∩ P) := measure_mono hcover
    _ ≤ ∑ d ∈ codes, uniformOn Set.univ (F d ∩ P) := measure_biUnion_finset_le _ _
    _ ≤ ∑ d ∈ codes, q * uniformOn Set.univ (F d) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hne, hcard⟩ := (Finset.mem_filter.mp hd).2
      exact hconditional d hne hcard
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      gcongr
      exact hsum.trans (uniformOn_sparse_columnDifference i j hij)

end BooleanThreshold
