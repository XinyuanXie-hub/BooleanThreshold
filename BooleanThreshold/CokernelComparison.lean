module

public import BooleanThreshold.CokernelJointMoments

public noncomputable section

open scoped BigOperators Classical

namespace BooleanThreshold

/-- Probability on a finite uniform sample space, expressed using an indicator. -/
@[expose] def finiteEventProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ :=
  finiteAverage (fun x => if event x then 1 else 0)

theorem finiteEventProbability_classes {Ω T : Type*} [Fintype Ω] [DecidableEq T]
    (f : Ω → T) (s : Finset T) :
    finiteEventProbability (fun x => f x ∈ s) =
      ∑ t ∈ s, finiteEventProbability (fun x => f x = t) := by
  unfold finiteEventProbability
  rw [← finiteAverage_sum]
  apply congrArg finiteAverage
  funext x
  by_cases hx : f x ∈ s
  · rw [ite_eq_left hx]
    symm
    rw [Finset.sum_eq_single_of_mem (f x) hx]
    · simp
    · intro t _ ht
      simp [Ne.symm ht]
  · rw [ite_eq_right hx]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    have hne : f x ≠ t := fun heq => hx (heq.symm ▸ ht)
    simp [hne]

/-- Per-class comparison errors add when the event is a union of classes. -/
theorem finiteEventProbability_classes_abs_sub_le {Ω Γ T : Type*}
    [Fintype Ω] [Fintype Γ] [DecidableEq T] (f : Ω → T) (g : Γ → T) (s : Finset T)
    {ε : ℝ}
    (h : ∀ t ∈ s, |finiteEventProbability (fun x => f x = t) -
      finiteEventProbability (fun x => g x = t)| ≤ ε) :
    |finiteEventProbability (fun x => f x ∈ s) -
      finiteEventProbability (fun x => g x ∈ s)| ≤ (s.card : ℝ) * ε := by
  rw [finiteEventProbability_classes, finiteEventProbability_classes, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum h).trans_eq (by simp))

private theorem prod_indicator_eq_indicator_forall {I : Type*} (s : Finset I) (p : I → Prop) [DecidablePred p]
    [Decidable (∀ i ∈ s, p i)] :
    (∏ i ∈ s, if p i then (1 : ℝ) else 0) = if ∀ i ∈ s, p i then 1 else 0 := by
  by_cases h : ∀ i ∈ s, p i
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one (fun i hi => ite_eq_left (h i hi))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi, hpi⟩ := h
    exact Finset.prod_eq_zero hi (ite_eq_right hpi)

private theorem indicator_inter_eq_sum_complements {I : Type*} [DecidableEq I]
    (s : Finset I) (p : I → Prop) :
    (if ∀ i ∈ s, p i then (1 : ℝ) else 0) =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * (if ∀ i ∈ t, ¬p i then 1 else 0) := by
  rw [← prod_indicator_eq_indicator_forall]
  have hswap (i : I) : (if p i then (1 : ℝ) else 0) = 1 - (if ¬p i then 1 else 0) := by
    by_cases hi : p i <;> simp [hi]
  simp_rw [hswap]
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, prod_indicator_eq_indicator_forall]

/-- The finite inclusion–exclusion formula written in terms of simultaneous
complement events. -/
theorem finiteEventProbability_joint_eq_sum_complements {Ω I : Type*} [Fintype Ω] [DecidableEq I]
    (s : Finset I) (P : I → Ω → Prop) :
    finiteEventProbability (fun x => ∀ i ∈ s, P i x) =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * finiteEventProbability (fun x => ∀ i ∈ t, ¬P i x) := by
  unfold finiteEventProbability
  calc
    _ = finiteAverage (fun x => ∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card * (if ∀ i ∈ t, ¬P i x then 1 else 0)) :=
      congrArg finiteAverage (funext fun x => by
        have hexp := indicator_inter_eq_sum_complements s (fun i => P i x)
        by_cases hx : ∀ i ∈ s, P i x
        · simpa only [ite_eq_left hx] using hexp
        · simpa only [ite_eq_right hx] using hexp)
    _ = _ := by
      rw [finiteAverage_sum]
      simp only [finiteAverage_const_mul]
      apply Finset.sum_congr rfl
      intro t _
      apply congrArg (fun z => (-1 : ℝ) ^ t.card * z)
      apply congrArg finiteAverage
      funext x
      by_cases hx : ∀ i ∈ t, ¬P i x
      · simp only [ite_eq_left hx]
      · simp only [ite_eq_right hx]

/-- Comparison errors for intersections of complements carry over to the
simultaneous event, at the cost of a factor of two per index. -/
theorem finiteEventProbability_joint_abs_sub_le {Ω Γ I : Type*}
    [Fintype Ω] [Fintype Γ] [DecidableEq I] (s : Finset I)
    (P : I → Ω → Prop) (Q : I → Γ → Prop) {ε : ℝ}
    (h : ∀ t ⊆ s, |finiteEventProbability (fun x => ∀ i ∈ t, ¬P i x) -
      finiteEventProbability (fun x => ∀ i ∈ t, ¬Q i x)| ≤ ε) :
    |finiteEventProbability (fun x => ∀ i ∈ s, P i x) -
      finiteEventProbability (fun x => ∀ i ∈ s, Q i x)| ≤ (2 : ℝ) ^ s.card * ε := by
  rw [finiteEventProbability_joint_eq_sum_complements, finiteEventProbability_joint_eq_sum_complements,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hterm (t : Finset I) (ht : t ∈ s.powerset) :
      |(-1 : ℝ) ^ t.card * finiteEventProbability (fun x => ∀ i ∈ t, ¬P i x) -
       (-1 : ℝ) ^ t.card * finiteEventProbability (fun x => ∀ i ∈ t, ¬Q i x)| ≤ ε := by
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact h t (Finset.mem_powerset.mp ht)
  exact (Finset.sum_le_sum hterm).trans_eq (by simp)

end BooleanThreshold
