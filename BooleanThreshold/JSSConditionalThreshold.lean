module

public import BooleanThreshold.JSSConditionalRoundingProfile

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace BooleanThreshold

/-- The largest scale at which a sign sum's small-ball probability can exceed
`L` times the radius, with the scale restricted to the unit interval. -/
noncomputable def signSmallBallThreshold {n : ℕ} (ν : Measure (Fin n → Bool))
    (a : Fin n → ℝ) (L : ℝ) : ℝ :=
  sSup ({0} ∪ {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧
    ∃ z : ℝ, L * r < ν.real {b | |signSum a b - z| ≤ r}})

private theorem signSmallBallThreshold_le_inv {n : ℕ} (ν : Measure (Fin n → Bool))
    [IsProbabilityMeasure ν] (a : Fin n → ℝ) {L : ℝ} (hL : 0 < L) :
    signSmallBallThreshold ν a L ≤ 1 / L := by
  unfold signSmallBallThreshold
  apply csSup_le (Set.nonempty_of_mem (show (0 : ℝ) ∈ ({0} ∪ _) from Or.inl rfl))
  rintro r (hr | ⟨_, _, z, hz⟩)
  · simp at hr
    subst r
    positivity
  · have hp : ν.real {b | |signSum a b - z| ≤ r} ≤ 1 := measureReal_le_one
    rw [le_div_iff₀ hL, mul_comm]
    exact hz.le.trans hp

private theorem nonempty_and_bddAbove_threshold_set {n : ℕ} (ν : Measure (Fin n → Bool))
    (a : Fin n → ℝ) (L : ℝ) :
    let S : Set ℝ := {0} ∪ {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧
      ∃ z : ℝ, L * r < ν.real {b | |signSum a b - z| ≤ r}}
    S.Nonempty ∧ BddAbove S := by
  dsimp
  refine ⟨⟨0, Or.inl rfl⟩, ⟨1, ?_⟩⟩
  rintro r (hr | ⟨_, hr, _⟩)
  · simpa using (show r ≤ 1 by simpa only [Set.mem_singleton_iff.mp hr] using zero_le_one)
  · exact hr

theorem signSmallBallThreshold_ge_of_atom {n : ℕ} (ν : Measure (Fin n → Bool))
    [IsProbabilityMeasure ν] (a : Fin n → ℝ) (L : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hb : β ≤ 1)
    (hatom : L * β < ν.real {b | signSum a b = 0}) :
    β ≤ signSmallBallThreshold ν a L := by
  apply le_csSup (nonempty_and_bddAbove_threshold_set ν a L).2
  refine Or.inr ⟨hβ, hb, 0, hatom.trans_le (measureReal_mono ?_ (measure_ne_top _ _))⟩
  intro b h
  change signSum a b = 0 at h
  simp [h, hβ]

private theorem signSmallBall_le_of_gt_threshold {n : ℕ} (ν : Measure (Fin n → Bool))
    [IsProbabilityMeasure ν] (a : Fin n → ℝ) (z : ℝ) {L t : ℝ} (hL : 1 ≤ L) (ht : 0 ≤ t)
    (h : signSmallBallThreshold ν a L < t) :
    ν.real {b | |signSum a b - z| ≤ t} ≤ L * t := by
  by_cases h1 : t ≤ 1
  · by_contra! hfail
    have hle : t ≤ signSmallBallThreshold ν a L :=
      le_csSup (nonempty_and_bddAbove_threshold_set ν a L).2
        (Or.inr ⟨ht, h1, z, hfail⟩)
    exact (not_le_of_gt h) hle
  · have hp : ν.real {b | |signSum a b - z| ≤ t} ≤ 1 := measureReal_le_one
    exact hp.trans (one_le_mul_of_one_le_of_one_le hL (le_of_not_ge h1))

private theorem exists_large_smallBall_below_threshold {n : ℕ} (ν : Measure (Fin n → Bool))
    (a : Fin n → ℝ) (L : ℝ) (h : 0 < signSmallBallThreshold ν a L) :
    ∃ t z : ℝ, signSmallBallThreshold ν a L / 2 < t ∧ t ≤ signSmallBallThreshold ν a L ∧
      L * t < ν.real {b | |signSum a b - z| ≤ t} := by
  have hs := nonempty_and_bddAbove_threshold_set ν a L
  have hlt : signSmallBallThreshold ν a L / 2 < signSmallBallThreshold ν a L := by linarith
  obtain ⟨t, ht, htr⟩ := (lt_csSup_iff hs.2 hs.1).mp hlt
  rcases ht with ht | ⟨ht₀, ht₁, z, hz⟩
  · have hz : t = 0 := Set.mem_singleton_iff.mp ht
    linarith only [hz, htr, h]
  · exact ⟨t, z, htr, le_csSup hs.2 (Or.inr ⟨ht₀, ht₁, z, hz⟩), hz⟩

theorem signSum_const_mul {n : ℕ} (D : ℝ) (a : Fin n → ℝ) (b : Fin n → Bool) :
    signSum (D • a) b = D * signSum a b := by
  simp only [signSum, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- A vector with a large zero atom has a nearby scaled integer vector with
both an upper small-ball profile at zero and a retained large small ball. -/
theorem exists_integer_vector_of_large_zero_atom {n : ℕ} (hn : 0 < n)
    (ν : Measure (Fin n → Bool)) [IsProbabilityMeasure ν] (a : Fin n → ℝ)
    {L β : ℝ} (hL : 1 ≤ L) (hβ : 0 < β) (hb : β ≤ 1)
    (hatom : L * β < ν.real {b | signSum a b = 0}) :
    ∃ T : ℝ, β ≤ T ∧ T ≤ 1 / L ∧ ∃ w : Fin n → ℤ,
      (∀ i, |(w i : ℝ) - (Real.sqrt (n : ℝ) / (2 * T)) * a i| ≤ 1) ∧
      (∀ t ≥ Real.sqrt (n : ℝ),
        ν.real {b | |signSum (fun i => (w i : ℝ)) b| ≤ t} ≤
          72 * L * T / Real.sqrt (n : ℝ) * t) ∧
      ∃ z : ℝ, L * T / 4 ≤
        ν.real {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)} := by
  let T := signSmallBallThreshold ν a L
  have hTlo : β ≤ T := signSmallBallThreshold_ge_of_atom ν a L hβ.le hb hatom
  have hT : 0 < T := hβ.trans_le hTlo
  have hL' : 0 < L := zero_lt_one.trans_le hL
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  let D := Real.sqrt (n : ℝ) / (2 * T)
  have hD : 0 < D := by positivity
  let v := D • a
  have hprof (t : ℝ) (ht : Real.sqrt (n : ℝ) ≤ t) :
      ν.real {b | |signSum v b - 0| ≤ t} ≤ (L / D) * t := by
    have htD : 2 * T ≤ t / D := by
      apply (le_div_iff₀ hD).mpr
      have hDmul : 2 * T * D = Real.sqrt (n : ℝ) := by dsimp [D]; field_simp [hT.ne']
      simpa only [hDmul] using ht
    have hTT : T < t / D := (by linarith : T < 2 * T).trans_le htD
    have h := signSmallBall_le_of_gt_threshold ν a 0 hL (div_nonneg (hs.trans_le ht).le hD.le) hTT
    have heq : {b | |signSum v b - (0 : ℝ)| ≤ t} =
        {b | |signSum a b - (0 : ℝ)| ≤ t / D} := by
      ext b
      simp only [v, Set.mem_ofPred_eq, sub_zero, signSum_const_mul,
        abs_mul, abs_of_pos hD, le_div_iff₀ hD, mul_comm D]
    rw [heq]
    calc
      _ ≤ L * (t / D) := h
      _ = _ := by ring
  obtain ⟨t₀, z, hlt, hle, hlo⟩ := exists_large_smallBall_below_threshold ν a L hT
  obtain ⟨w, hclose, hup, hr⟩ := exists_roundedVector_preserving_small_balls hn ν v 0 (D * z)
    (show 0 < L / D by positivity) hprof
  have hbig : L * T / 2 ≤ ν.real {b | |signSum v b - D * z| ≤ Real.sqrt (n : ℝ)} := by
    have hleft : L * (T / 2) ≤ L * t₀ := mul_le_mul_of_nonneg_left hlt.le hL'.le
    rw [← mul_div_assoc] at hleft
    refine (hleft.trans hlo.le).trans (measureReal_mono ?_ (measure_ne_top _ _))
    intro b h
    change |signSum a b - z| ≤ t₀ at h
    change |signSum v b - D * z| ≤ _
    rw [show v = D • a by rfl, signSum_const_mul, ← mul_sub, abs_mul, abs_of_pos hD]
    have hd : D * t₀ ≤ Real.sqrt (n : ℝ) := by
      calc
        _ ≤ D * T := mul_le_mul_of_nonneg_left hle hD.le
        _ ≤ _ := by
          dsimp [D]
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ (by positivity : 0 < 2 * T)).mpr
          nlinarith only [mul_nonneg hs.le hT.le]
    exact (mul_le_mul_of_nonneg_left h hD.le).trans hd
  refine ⟨T, hTlo, signSmallBallThreshold_le_inv ν a hL', w, hclose, ?_, D * z, ?_⟩
  · intro t ht
    have h := hup t ht
    have heq : 36 * (L / D) = 72 * L * T / Real.sqrt (n : ℝ) := by dsimp [D]; field_simp; ring
    simpa only [sub_zero, heq] using h
  · have hthird := (div_le_div_of_nonneg_right hbig (by norm_num : (0 : ℝ) ≤ 2)).trans hr
    linarith only [hthird]

end BooleanThreshold
