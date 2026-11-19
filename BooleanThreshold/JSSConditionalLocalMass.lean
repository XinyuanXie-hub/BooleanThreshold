module

public import BooleanThreshold.JSSConditionalFejer
public import BooleanThreshold.JSSConditionalLocalBound
public import BooleanThreshold.JSSConditionalSliceAverage

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace BooleanThreshold

private theorem sum_translate_integrals_le_of_interval_mass {Ω G : Type*}
    [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype G] [AddCommGroup G] (μ : Measure Ω) [IsFiniteMeasure μ]
    (I : Finset G) (v : Ω → G) (f : G → ℝ) (hf : ∀ z, 0 ≤ f z) (hf₁ : ∑ z, f z ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (h : ∀ z, μ.real {b | z - v b ∈ I} ≤ R) :
    (∑ t ∈ I, ∫ b, f (t + v b) ∂μ) ≤ R := by
  classical
  let E (z : G) : Set Ω := {b | z - v b ∈ I}
  have hsum (x : Ω) : (∑ t ∈ I, f (t + v x)) =
      ∑ z : G, (E z).indicator (fun _ => f z) x := by
    let e := Equiv.addRight (v x)
    have hmap : I.map e.toEmbedding = Finset.univ.filter fun z => x ∈ E z := by
      ext z
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨t, ht, htz⟩
        change t + v x = z at htz
        change z - v x ∈ I
        rwa [← htz, add_sub_cancel_right]
      · intro hz
        exact ⟨z - v x, hz, sub_add_cancel _ _⟩
    calc
      _ = ∑ z ∈ I.map e.toEmbedding, f z := by simp [e]
      _ = _ := by rw [hmap, Finset.sum_filter]; simp only [Set.indicator_apply]
  rw [← integral_finsetSum I (fun _ _ => Integrable.of_finite)]
  simp_rw [hsum]
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_indicator_const _ (Set.toFinite _).measurableSet, smul_eq_mul]
  calc
    _ ≤ ∑ z : G, R * f z := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (h z) (hf z)
    _ = R * ∑ z, f z := (Finset.mul_sum _ _ _).symm
    _ ≤ R := mul_le_of_le_one_right hR hf₁

private theorem int_vector_sum_abs_le {n d N : ℕ} (a : Fin n → ℤ)
    (hab : ∀ i, |a i| ≤ (d : ℤ) * (N : ℤ)) :
    |∑ i, a i| ≤ (n : ℤ) * (d : ℤ) * (N : ℤ) := by
  calc
    _ ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (d : ℤ) * (N : ℤ) := Finset.sum_le_sum (fun i _ => hab i)
    _ = _ := by simp [mul_assoc]

private theorem cyclic_local_mass_le_of_smallBall {Ω : Type*}
    [Finite Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {P N A : ℕ} [NeZero P]
    (hP : 2 * (A + N) < P) (V : Ω → ℤ) (hV : ∀ b, |V b| ≤ (A : ℤ))
    (f : ZMod P → ℝ) (hf : ∀ z, 0 ≤ f z) (hf₁ : ∑ z, f z ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (h : ∀ z : ℤ, μ.real {b | |(V b : ℝ) - (z : ℝ)| ≤ (N : ℝ)} ≤ R)
    (u : ZMod P) :
    (∑ t ∈ cyclicInterval P N u, ∫ b, f (t + (V b : ZMod P)) ∂μ) ≤ R := by
  refine sum_translate_integrals_le_of_interval_mass μ (cyclicInterval P N u)
    (fun b => (V b : ZMod P)) f hf hf₁ hR (fun z => ?_)
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (h (z - u).valMinAbs)
  intro b hb
  obtain ⟨j, hj, hz⟩ := Finset.mem_image.mp (show z - (V b : ZMod P) ∈ cyclicInterval P N u from hb)
  have hz' : z - u = (V b + (j : ℤ) : ℤ) := by
    push_cast
    change u + (j : ZMod P) = z - (V b : ZMod P) at hz
    linear_combination -hz
  have hVb := abs_le.mp (hV b)
  have hMj : (j : ℤ) < (N : ℤ) := by exact_mod_cast Finset.mem_range.mp hj
  have hP' : (2 : ℤ) * ((A : ℤ) + (N : ℤ)) < (P : ℤ) := by exact_mod_cast hP
  have hRep : (V b + (j : ℤ)) * 2 ∈ Set.Ioc (-(P : ℤ)) (P : ℤ) := by
    have hj₀ : 0 ≤ (j : ℤ) := by positivity
    have hN₀ : 0 ≤ (N : ℤ) := by positivity
    constructor <;> linarith only [hVb.1, hVb.2, hMj, hP', hj₀, hN₀]
  have hMin := (ZMod.valMinAbs_spec (z - u) (V b + (j : ℤ))).mpr ⟨hz', hRep⟩
  change |(V b : ℝ) - ((z - u).valMinAbs : ℝ)| ≤ (N : ℝ)
  rw [hMin, Int.cast_add, Int.cast_natCast,
    show (V b : ℝ) - ((V b : ℝ) + (j : ℝ)) = -(j : ℝ) by ring,
    abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.mem_range.mp hj).le

private theorem interval_no_wrap {n P N : ℕ} (hn : 1 ≤ n) (hP : 4 * n ^ 2 * N < P) :
    2 * (n ^ 2 * N + N) < P := by
  have hn' : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hle : N ≤ n ^ 2 * N := by simpa using Nat.mul_le_mul_right N hn'
  nlinarith only [hP, hle]

/-- Random translated sign sums on a balanced slice spread the mass of any
nonnegative unit-mass function over each short cyclic interval. -/
theorem signSlice_cyclic_local_mass_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)),
        σ * (n : ℝ) ≤ (k : ℝ) → η * (n : ℝ) ≤ (m.val : ℝ) →
        (m.val : ℝ) ≤ (1 - η) * (n : ℝ) →
        ∀ (P N : ℕ) [NeZero P], 0 < N → 4 * n ^ 2 * N < P →
        ∀ a : Fin n → ℤ, (∀ i, |a i| ≤ (n : ℤ) * (N : ℤ)) →
          (∀ j, (N : ℝ) < |(a (e (j, false)) : ℝ) - (a (e (j, true)) : ℝ)|) →
        ∀ f : ZMod P → ℝ, (∀ z, 0 ≤ f z) → (∑ z, f z) ≤ 1 → ∀ u : ZMod P,
          (∑ t ∈ cyclicInterval P N u, ∫ b : Fin n → Bool,
            f (t + ∑ i, if b i then (a i : ZMod P) else -(a i : ZMod P))
              ∂(uniformOn (signSlice n m))) ≤ C / Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC, h⟩ := signSlice_smallBall_le_of_linear_pairs_eventually hη hσ
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn₁ k e m hk hml hmu P N instP _ hP a ha hgap f hf hf₁ u
  let μ := uniformOn (signSlice n m)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn (signSlice n m).toFinite (signSlice_nonempty m)
  let V (b : Fin n → Bool) : ℤ := ∑ i, if b i then a i else -a i
  have hv (b : Fin n → Bool) : (V b : ZMod P) = ∑ i, if b i then (a i : ZMod P) else -(a i : ZMod P) := by
    simp [V, Int.cast_sum, apply_ite]
  simp_rw [← hv]
  refine cyclic_local_mass_le_of_smallBall μ (interval_no_wrap hn₁ hP) V ?_ f hf hf₁ (by positivity) ?_ u
  · intro b
    simp only [Nat.cast_mul, pow_two]
    exact int_vector_sum_abs_le _ (fun i => by cases b i <;> simpa using ha i)
  · intro z
    have hSum (b : Fin n → Bool) : signSum (fun i => (a i : ℝ)) b = (V b : ℝ) := by
      simp only [signSum, V, Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> simp
    simp_rw [← hSum]
    exact hn k e m hk hml hmu (fun i => (a i : ℝ)) (z : ℝ) (N : ℝ) hgap

/-- The same local mass bound for the undoubled coefficients in fixed-weight
subset sums, with the averaging operator used in the slice recursion. -/
theorem sliceAverage_cyclic_local_mass_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)),
        σ * (n : ℝ) ≤ (k : ℝ) → η * (n : ℝ) ≤ (m.val : ℝ) →
        (m.val : ℝ) ≤ (1 - η) * (n : ℝ) →
        ∀ (d P N : ℕ) [NeZero P], n ≤ d → 0 < N → 4 * d ^ 2 * N < P →
        ∀ a : ℕ → ℤ, (∀ i : Fin n, |a i.val| ≤ (d : ℤ) * (N : ℤ)) →
          (∀ j, 2 * (N : ℝ) < |(a (e (j, false)).val : ℝ) - (a (e (j, true)).val : ℝ)|) →
        ∀ f : ZMod P → ℝ, (∀ z, 0 ≤ f z) → (∑ z, f z) ≤ 1 → ∀ u : ZMod P,
          (∑ t ∈ cyclicInterval P N u, sliceAverage (fun i => (a i : ZMod P)) f n m.val t) ≤
            C / Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC, h⟩ := signSlice_smallBall_le_of_linear_pairs_eventually hη hσ
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn₁ k e m hk hml hmu d P N instP hnd _ hP a ha hgap f hf hf₁ u
  let μ := uniformOn (signSlice n m)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOn (signSlice n m).toFinite (signSlice_nonempty m)
  let V (b : Fin n → Bool) : ℤ := ∑ i ∈ Finset.univ.filter (fun i => b i), a i.val
  have hv (b : Fin n → Bool) : (V b : ZMod P) =
      ∑ i ∈ Finset.univ.filter (fun i => b i), (a i.val : ZMod P) := Int.cast_sum _ _
  simp_rw [← integral_signSlice_eq_sliceAverage, ← hv]
  refine cyclic_local_mass_le_of_smallBall μ (interval_no_wrap (hn₁.trans hnd) hP) V ?_ f hf hf₁ (by positivity) ?_ u
  · intro b
    simp only [V, Finset.sum_filter, Nat.cast_mul, pow_two]
    refine (int_vector_sum_abs_le (d := d) (N := N) _ (fun i => ?_)).trans ?_
    · split
      · exact ha i
      · simp; positivity
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnd) (by positivity)
  · intro z
    let v : Fin n → ℝ := fun i => (a i.val : ℝ)
    let s : ℝ := ∑ i, v i
    have hSum (b : Fin n → Bool) : signSum v b = 2 * (V b : ℝ) - s := by
      simp only [signSum, V, Int.cast_sum, Finset.sum_filter, v, s]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> simp
      ring
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
      (hn k e m hk hml hmu v (2 * (z : ℝ) - s) (2 * (N : ℝ)) hgap)
    intro b hb
    change |(V b : ℝ) - (z : ℝ)| ≤ (N : ℝ) at hb
    change |signSum v b - (2 * (z : ℝ) - s)| ≤ 2 * (N : ℝ)
    rw [hSum, show 2 * (V b : ℝ) - s - (2 * (z : ℝ) - s) = 2 * ((V b : ℝ) - (z : ℝ)) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)

end BooleanThreshold
