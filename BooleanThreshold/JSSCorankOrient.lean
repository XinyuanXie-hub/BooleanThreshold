module

public import BooleanThreshold.JSSCorankNet
public import BooleanThreshold.JSSConditionalTail
public import BooleanThreshold.SignSymmetry
public import BooleanThreshold.SignWindow
import Mathlib.Algebra.BigOperators.Field

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace BooleanThreshold

private theorem many_moderate_coordinates {n s : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (a : Fin n → ℝ) (ha : ¬ nearSparse s ρ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))) :
    s < (Finset.univ.filter (fun i => ρ / Real.sqrt (n : ℝ) < |a i|)).card := by
  classical
  let I := Finset.univ.filter (fun i => ρ / Real.sqrt (n : ℝ) < |a i|)
  change s < I.card
  by_contra h
  have hI : I.card ≤ s := le_of_not_gt h
  let z (i : Fin n) := if i ∈ I then a i else 0
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
  have hs : (Finset.univ.filter fun i => y i ≠ 0).card ≤ s := by
    refine (Finset.card_le_card ?_).trans hI
    intro i hi
    by_contra hnI
    exact (Finset.mem_filter.mp hi).2 (by simp [y, z, hnI])
  apply ha
  refine ⟨y, hs, ?_⟩
  rw [← sq_le_sq₀ (norm_nonneg _) hρ, EuclideanSpace.real_norm_sq_eq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hnR
  have hrad : 0 ≤ ρ / Real.sqrt (n : ℝ) := div_nonneg hρ hroot.le
  change (∑ i, (a i - z i) ^ 2) ≤ ρ ^ 2
  calc
    _ ≤ ∑ _i : Fin n, (ρ / Real.sqrt (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ I
      · simp [z, hi]
        exact sq_nonneg _
      · have habs : |a i| ≤ ρ / Real.sqrt (n : ℝ) := by
          by_contra hlt
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hlt⟩)
        rw [show z i = 0 by simp [z, hi], sub_zero, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow,
        Real.sq_sqrt hnR.le]
      field_simp [hnR.ne']

private theorem abs_flipVector {n : ℕ} (a : Fin n → ℝ) (mask : Fin n → Bool) (i : Fin n) :
    |flipVector mask a i| = |a i| := by
  cases h : mask i <;> simp [flipVector, h]

private noncomputable def positiveOn {n : ℕ} (I : Finset (Fin n)) (a : Fin n → ℝ)
    (mask : Fin n → Bool) : Finset (Fin n) :=
  I.filter fun i => 0 < flipVector mask a i

private noncomputable def negativeOn {n : ℕ} (I : Finset (Fin n)) (a : Fin n → ℝ)
    (mask : Fin n → Bool) : Finset (Fin n) :=
  I.filter fun i => flipVector mask a i < 0

private theorem side_counts_add {n : ℕ} (I : Finset (Fin n)) (a : Fin n → ℝ)
    (hI : ∀ i ∈ I, a i ≠ 0) (mask : Fin n → Bool) :
    (positiveOn I a mask).card + (negativeOn I a mask).card = I.card := by
  classical
  have hdis : Disjoint (positiveOn I a mask) (negativeOn I a mask) := by
    apply Finset.disjoint_left.mpr
    intro i hp hn
    exact (not_lt_of_gt (Finset.mem_filter.mp hp).2) (Finset.mem_filter.mp hn).2
  have hunion : positiveOn I a mask ∪ negativeOn I a mask = I := by
    ext i
    constructor
    · simp only [Finset.mem_union, positiveOn, negativeOn, Finset.mem_filter]
      rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · intro hi
      have hn : flipVector mask a i ≠ 0 := (flipVector_apply_ne_zero_iff _ _ _).2 (hI i hi)
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hneg⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hpos⟩)
  rw [← Finset.card_union_of_disjoint hdis, hunion]

private theorem small_side_probability_le {n : ℕ} (I : Finset (Fin n)) (a : Fin n → ℝ)
    (hI : ∀ i ∈ I, a i ≠ 0) (hk : 0 < I.card) :
    (uniformOn Set.univ).real {mask : Fin n → Bool |
      ((positiveOn I a mask).card : ℝ) ≤ I.card / 4 ∨
      ((negativeOn I a mask).card : ℝ) ≤ I.card / 4} ≤
      2 * Real.exp (-(I.card : ℝ) / 8) := by
  classical
  let k := I.card
  let scale := Real.sqrt (k : ℝ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hscale : 0 < scale := Real.sqrt_pos_of_pos hkR
  have hsq : scale ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  let w (i : Fin n) := if i ∈ I then ((if 0 < a i then (-1 : ℝ) else 1) / scale) else 0
  have hw : ∑ i, w i ^ 2 = 1 := by
    have hterm (i : Fin n) : w i ^ 2 = if i ∈ I then (1 : ℝ) / (k : ℝ) else 0 := by
      by_cases hi : i ∈ I <;> by_cases ha' : 0 < a i <;> simp [w, hi, ha', div_pow, hsq]
    simp only [hterm, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    change (k : ℝ) * (1 / (k : ℝ)) = 1
    simpa only [one_div] using mul_inv_cancel₀ hkR.ne'
  have hsum (mask : Fin n → Bool) :
      signSum w mask = (((positiveOn I a mask).card : ℝ) - (negativeOn I a mask).card) / scale := by
    have heq (i : Fin n) : w i * (if mask i then 1 else -1) =
        ((if i ∈ positiveOn I a mask then (1 : ℝ) else 0) -
          (if i ∈ negativeOn I a mask then 1 else 0)) / scale := by
      by_cases hi : i ∈ I
      · rcases lt_or_gt_of_ne (hI i hi) with hneg | hpos
        · cases hmask : mask i <;>
            simp [w, positiveOn, negativeOn, flipVector, hi, hmask, hneg,
              not_lt_of_ge hneg.le, div_eq_mul_inv]
        · cases hmask : mask i <;>
            simp [w, positiveOn, negativeOn, flipVector, hi, hmask, hpos,
              not_lt_of_ge hpos.le, div_eq_mul_inv]
      · simp [w, positiveOn, negativeOn, hi]
    unfold signSum
    simp only [heq, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hset : {mask : Fin n → Bool | ((positiveOn I a mask).card : ℝ) ≤ I.card / 4 ∨
      ((negativeOn I a mask).card : ℝ) ≤ I.card / 4} ⊆
      {mask | scale / 2 ≤ |signSum w mask|} := by
    intro mask hmask
    change scale / 2 ≤ |signSum w mask|
    rw [hsum, abs_div, abs_of_pos hscale, le_div_iff₀ hscale]
    have hs : ((positiveOn I a mask).card : ℝ) + (negativeOn I a mask).card = k := by
      exact_mod_cast side_counts_add I a hI mask
    have hprod : scale / 2 * scale = (k : ℝ) / 2 := by
      calc _ = scale ^ 2 / 2 := by ring
           _ = _ := by rw [hsq]
    rw [hprod, le_abs]
    rcases hmask with hpos | hneg
    · right
      linarith only [hs, hpos]
    · left
      linarith only [hs, hneg]
  refine (measureReal_mono hset).trans ?_
  have hle := signSum_abs_tail_le w hw (u := scale / 2) (by positivity)
  have hExp : -(scale / 2) ^ 2 / 2 = -(k : ℝ) / 8 := by
    rw [div_pow, hsq]
    ring
  simpa only [hExp] using hle

/-- For an incompressible vector, coordinated random signs make it almost
constant with probability at most one eighth, for sufficiently small
almost-constant parameters. -/
theorem almostConstant_orientation_probability_le {n J : ℕ} (hJ : 0 < J)
    (hn : 40 * J ≤ n) {ρ δ₀ ρ₀ : ℝ} (hρ : 0 ≤ ρ) (hρ₀ : ρ₀ ≤ ρ)
    (hδ₀ : δ₀ ≤ 1 / (4 * (J : ℝ))) (a : Fin n → ℝ)
    (ha : ¬ nearSparse (n / J) ρ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))) :
    uniformOn Set.univ {mask : Fin n → Bool | flipVector mask a ∈ almostConstantUnitVectors n δ₀ ρ₀}
      ≤ 1 / 8 := by
  classical
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  let I := Finset.univ.filter fun i => ρ / Real.sqrt (n : ℝ) < |a i|
  have hi (i : Fin n) (hiI : i ∈ I) : ρ / Real.sqrt (n : ℝ) < |a i| :=
    (Finset.mem_filter.mp hiI).2
  have hI : ∀ i ∈ I, a i ≠ 0 := by
    intro i hiI hz
    have hh := hi i hiI
    rw [hz, abs_zero] at hh
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / Real.sqrt (n : ℝ))) hh
  have hk : n / J < I.card := many_moderate_coordinates hnpos hρ a ha
  have hkpos : 0 < I.card := (Nat.zero_le _).trans_lt hk
  have hkProd : n < I.card * J := (Nat.div_lt_iff_lt_mul hJ).1 hk
  have hkR : (n : ℝ) < (I.card : ℝ) * (J : ℝ) := by exact_mod_cast hkProd
  have hδK : δ₀ * (n : ℝ) ≤ (I.card : ℝ) / 4 := by
    calc
      _ ≤ (1 / (4 * (J : ℝ))) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hδ₀ hnR.le
      _ = (n : ℝ) / (4 * (J : ℝ)) := by ring
      _ ≤ _ := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith only [hkR]
  let C : Set (Fin n → Bool) := {mask | flipVector mask a ∈ almostConstantUnitVectors n δ₀ ρ₀}
  have hsub : C ⊆ {mask | ((positiveOn I a mask).card : ℝ) ≤ I.card / 4 ∨
      ((negativeOn I a mask).card : ℝ) ≤ I.card / 4} := by
    intro mask hmask
    obtain ⟨_, center, hcenter⟩ := hmask
    let near := Finset.univ.filter fun i => |flipVector mask a i - center| ≤ ρ₀ / Real.sqrt (n : ℝ)
    have hnear : (1 - δ₀) * (n : ℝ) ≤ (near.card : ℝ) := hcenter
    have hsmall (P : Finset (Fin n)) (hd : Disjoint near P) :
        (P.card : ℝ) ≤ (I.card : ℝ) / 4 := by
      have hcard : near.card + P.card ≤ n := by
        rw [← Finset.card_union_of_disjoint hd]
        simpa using (Finset.card_le_univ (s := near ∪ P))
      have hcardR : (near.card : ℝ) + (P.card : ℝ) ≤ n := by exact_mod_cast hcard
      linarith only [hnear, hcardR, hδK]
    have hrad : ρ₀ / Real.sqrt (n : ℝ) ≤ ρ / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right hρ₀ (Real.sqrt_nonneg _)
    by_cases hc : 0 ≤ center
    · right
      apply hsmall
      apply Finset.disjoint_left.mpr
      intro i hni hPi
      obtain ⟨hIi, hneg⟩ := Finset.mem_filter.mp hPi
      have hdist := (Finset.mem_filter.mp hni).2
      have habs : |flipVector mask a i| ≤ |flipVector mask a i - center| := by
        rw [abs_of_neg hneg, abs_of_nonpos (by linarith)]
        linarith
      rw [abs_flipVector] at habs
      exact (not_lt_of_ge (habs.trans (hdist.trans hrad))) (hi i hIi)
    · left
      apply hsmall
      apply Finset.disjoint_left.mpr
      intro i hni hPi
      obtain ⟨hIi, hpos⟩ := Finset.mem_filter.mp hPi
      have hdist := (Finset.mem_filter.mp hni).2
      have habs : |flipVector mask a i| ≤ |flipVector mask a i - center| := by
        rw [abs_of_pos hpos, abs_of_nonneg (by linarith [lt_of_not_ge hc])]
        linarith [lt_of_not_ge hc]
      rw [abs_flipVector] at habs
      exact (not_lt_of_ge (habs.trans (hdist.trans hrad))) (hi i hIi)
  have h40 : (40 : ℝ) ≤ I.card := by
    have hnat : 40 ≤ n / J := (Nat.le_div_iff_mul_le hJ).2 hn
    exact_mod_cast hnat.trans hk.le
  have hExp : Real.exp (-(I.card : ℝ) / 8) ≤ 1 / 16 := by
    refine (Real.exp_le_exp_of_le (by linarith : -(I.card : ℝ) / 8 ≤ -5)).trans ?_
    rw [Real.exp_neg, ← one_div]
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num)
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  change uniformOn Set.univ C ≤ 1 / 8
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mp
  rw [← measureReal_def, ENNReal.toReal_div]
  norm_num
  have hprob := (measureReal_mono hsub).trans (small_side_probability_le I a hI hkpos)
  linarith only [hprob, hExp]

end BooleanThreshold
