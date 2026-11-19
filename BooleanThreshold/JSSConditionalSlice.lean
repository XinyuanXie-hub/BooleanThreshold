module

public import BooleanThreshold.JSSConditionalTail
public import BooleanThreshold.SignWindow

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical Function

namespace BooleanThreshold

/-- At least one nonempty fiber has conditional event probability at least
as large as the probability before specifying the fiber. -/
private theorem exists_uniformFiber_real_ge {B ι : Type*} [Finite B] [Fintype ι]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (W : Set B) (hW : W.Nonempty) (f : B → ι) (E : Set B) :
    ∃ i : ι, (W ∩ {b | f b = i}).Nonempty ∧
      (uniformOn W).real E ≤ (uniformOn (W ∩ {b | f b = i})).real E := by
  let R (i : ι) := W ∩ {b | f b = i}
  let μ := uniformOn W
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn W.toFinite hW
  have hdisj : Pairwise (Disjoint on R) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro b hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hcover : (⋃ i, R i) = W := by
    ext b
    simp only [Set.mem_iUnion, R, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, hb, _⟩ => hb, fun hb => ⟨f b, hb, rfl⟩⟩
  have hmass : (∑ i, μ.real (R i)) = 1 := by
    rw [← measureReal_iUnion_fintype hdisj (fun i => (R i).toFinite.measurableSet), hcover]
    change (uniformOn W).real W = 1
    rw [measureReal_def, uniformOn_self W.toFinite hW, ENNReal.toReal_one]
  have hsplit : μ.real E = ∑ i, (uniformOn (R i)).real E * μ.real (R i) := by
    have hdisj' : Pairwise (Disjoint on fun i => R i ∩ E) :=
      fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hsplit := measureReal_iUnion_fintype (μ := μ) hdisj'
      (fun i => (R i ∩ E).toFinite.measurableSet)
    rw [← Set.iUnion_inter, hcover] at hsplit
    rw [show μ.real (W ∩ E) = μ.real E by simp only [μ, measureReal_def, uniformOn_inter_self W.toFinite]] at hsplit
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro i _
    have hR : W ∩ R i = R i := Set.inter_eq_right.mpr Set.inter_subset_left
    simp only [μ, measureReal_def, uniformOn_inter W.toFinite, hR, ENNReal.toReal_mul]
  by_contra! h
  have hle (i : ι) : (uniformOn (R i)).real E * μ.real (R i) ≤ μ.real E * μ.real (R i) := by
    by_cases hi : (R i).Nonempty
    · exact mul_le_mul_of_nonneg_right (h i hi).le measureReal_nonneg
    · rw [Set.not_nonempty_iff_eq_empty.mp hi, measureReal_empty, mul_zero, mul_zero]
  obtain ⟨b, hb⟩ := hW
  have hi : (R (f b)).Nonempty := ⟨b, hb, rfl⟩
  have hpos : 0 < μ.real (R (f b)) := by
    apply ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    change uniformOn W (R (f b)) ≠ 0
    rw [Ne, uniformOn_eq_zero_iff W.toFinite, Set.inter_eq_right.mpr Set.inter_subset_left]
    exact hi.ne_empty
  have hlt : ∑ i, (uniformOn (R i)).real E * μ.real (R i) < ∑ i, μ.real E * μ.real (R i) :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨f b, Finset.mem_univ _, mul_lt_mul_of_pos_right (h (f b) hi) hpos⟩
  rw [← hsplit, ← Finset.mul_sum, hmass, mul_one] at hlt
  exact (not_lt_of_ge le_rfl) hlt

/-- The number of `true` coordinates of a sign vector. -/
def signWeight {n : ℕ} (b : Fin n → Bool) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => b i).card, by
    have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => b i)
    simpa using Nat.lt_succ_of_le (by simpa using h : (Finset.univ.filter fun i => b i).card ≤ n)⟩

/-- The sign vectors with one prescribed coordinate count. -/
def signSlice (n : ℕ) (m : Fin (n + 1)) : Set (Fin n → Bool) :=
  {b | signWeight b = m}

theorem sum_realSigns_eq_signWeight {n : ℕ} (b : Fin n → Bool) :
    ∑ i, realSigns b i = 2 * ((signWeight b).val : ℝ) - (n : ℝ) := by
  have hpoint (i : Fin n) : realSigns b i = (if b i then (1 : ℝ) else 0) * 2 - 1 := by
    cases h : b i <;> norm_num [realSigns, h]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsum : (∑ i : Fin n, if b i then (1 : ℝ) else 0) = ((signWeight b).val : ℝ) := by
    rw [← Finset.sum_filter]
    simp [signWeight]
  rw [hsum, mul_comm _ 2]
  simp

theorem signSlice_subset_balancedSignWindow {n : ℕ} {γ : ℝ} {m : Fin (n + 1)}
    (hm : |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ)) :
    signSlice n m ⊆ balancedSignWindow n γ := by
  intro b hb
  have hb' : signWeight b = m := hb
  change |∑ i, realSigns b i| ≤ _
  simpa only [sum_realSigns_eq_signWeight, hb'] using hm

/-- A large conditional small ball on the balancing window is already large
on one of its fixed-weight slices. -/
theorem exists_signSlice_real_ge {n : ℕ} {γ : ℝ} (hW : (balancedSignWindow n γ).Nonempty)
    (E : Set (Fin n → Bool)) :
    ∃ m : Fin (n + 1), |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ) ∧
      (signSlice n m).Nonempty ∧
      (uniformOn (balancedSignWindow n γ)).real E ≤ (uniformOn (signSlice n m)).real E := by
  obtain ⟨m, ⟨b, hb, hbm⟩, h⟩ := exists_uniformFiber_real_ge _ hW signWeight E
  have hm : |2 * (m.val : ℝ) - (n : ℝ)| ≤ 2 * γ * (n : ℝ) := by
    change |∑ i, realSigns b i| ≤ _ at hb
    change signWeight b = m at hbm
    simpa only [sum_realSigns_eq_signWeight, hbm] using hb
  have heq : balancedSignWindow n γ ∩ {x | signWeight x = m} = signSlice n m :=
    Set.inter_eq_right.mpr (signSlice_subset_balancedSignWindow hm)
  exact ⟨m, hm, ⟨b, hbm⟩, heq ▸ h⟩

/-- Translating every coefficient by the same integer only shifts the center
of a small ball on a fixed-weight slice. -/
theorem signSlice_real_smallBall_sub_const {n : ℕ} (m : Fin (n + 1))
    (w : Fin n → ℤ) (d : ℤ) (z r : ℝ) :
    (uniformOn (signSlice n m)).real {b |
      |signSum (fun i => ((w i - d : ℤ) : ℝ)) b - (z - (d : ℝ) * (2 * (m.val : ℝ) - n))| ≤ r} =
    (uniformOn (signSlice n m)).real {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ r} := by
  rw [measureReal_def, measureReal_def,
    ← uniformOn_inter_self (signSlice n m).toFinite, ← uniformOn_inter_self (t := {b |
        |signSum (fun i => (w i : ℝ)) b - z| ≤ r}) (signSlice n m).toFinite]
  congr 2
  ext b
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  apply and_congr_right
  intro hb
  have hbm : signWeight b = m := hb
  have hsum := sum_realSigns_eq_signWeight b
  rw [hbm] at hsum
  simp only [signSum, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ i, if b i then (1 : ℝ) else -1) = _ at hsum
  rw [hsum]
  ring_nf

end BooleanThreshold
