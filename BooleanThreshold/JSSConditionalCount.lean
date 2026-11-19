module

public import BooleanThreshold.JSSConditionalThreshold
public import BooleanThreshold.JSSConditionalTensorization
public import BooleanThreshold.JSSConditionalWindow

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Classical

namespace BooleanThreshold

/-- Candidate lattice points at scale between `u` and `2*u` in the
conditional small-ball estimate for a unit normal. -/
def roundedConditionalCandidates (n : ℕ) (ν : Measure (Fin n → Bool))
    (δ ρ L u : ℝ) : Set (Fin n → ℤ) :=
  {w | (∃ a : Fin n → ℝ, (∑ i, a i ^ 2) = 1 ∧ a ∉ almostConstantUnitVectors n δ ρ ∧
      ∃ T : ℝ, u ≤ T ∧ T ≤ 2 * u ∧ T ≤ 1 / L ∧
        ∀ i, |(w i : ℝ) - (Real.sqrt (n : ℝ) / (2 * T)) * a i| ≤ 1) ∧
    (∀ t ≥ Real.sqrt (n : ℝ),
      ν.real {b | |signSum (fun i => (w i : ℝ)) b| ≤ t} ≤
        144 * L * u / Real.sqrt (n : ℝ) * t) ∧
    ∃ z : ℝ, L * u / 4 ≤
      ν.real {b | |signSum (fun i => (w i : ℝ)) b - z| ≤ 2 * Real.sqrt (n : ℝ)}}

/-- Samples admitting an unstructured unit normal with a large conditional zero atom. -/
def badConditionalNormal (n m : ℕ) (ν : Measure (Fin n → Bool))
    (δ ρ L β : ℝ) : Set (Fin m → Fin n → Bool) :=
  {A | ∃ a : Fin n → ℝ, (∑ i, a i ^ 2) = 1 ∧ a ∉ almostConstantUnitVectors n δ ρ ∧
    (∀ i, signSum a (A i) = 0) ∧ L * β < ν.real {b | signSum a b = 0}}

theorem roundedConditionalCandidates_finite (n : ℕ) (ν : Measure (Fin n → Bool))
    (δ ρ L : ℝ) {u : ℝ} (hu : 0 < u) :
    (roundedConditionalCandidates n ν δ ρ L u).Finite := by
  let R := Real.sqrt (n : ℝ) / (2 * u) + 1
  obtain ⟨N, hN⟩ := exists_nat_ge R
  refine (Set.Finite.pi' fun _ : Fin n => Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  rintro w ⟨⟨a, ha, _, T, hT, _, _, hclose⟩, _, _⟩
  intro i
  have hT₀ := hu.trans_le hT
  have ha' : |a i| ≤ 1 := by
    apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs, one_pow, ← ha]
    exact Finset.single_le_sum (f := fun j => a j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hD : Real.sqrt (n : ℝ) / (2 * T) ≤ Real.sqrt (n : ℝ) / (2 * u) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (by linarith)
  have hw : |(w i : ℝ)| ≤ R := by
    let d := (Real.sqrt (n : ℝ) / (2 * T)) * a i
    calc
      _ = |(w i : ℝ) - d + d| := by rw [sub_add_cancel]
      _ ≤ |(w i : ℝ) - d| + |d| := abs_add_le _ _
      _ ≤ 1 + (Real.sqrt (n : ℝ) / (2 * T)) * |a i| := by
        dsimp [d]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) / (2 * T))]
        exact add_le_add_left (hclose i) _
      _ ≤ 1 + Real.sqrt (n : ℝ) / (2 * T) :=
        add_le_add_right (mul_le_of_le_one_right (by positivity) ha') _
      _ ≤ R := by dsimp [R]; linarith only [hD]
  have hi := abs_le.mp (hw.trans hN)
  exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩

private theorem exists_dyadic_lower {β T : ℝ} (hβ : 0 < β) (hT : β ≤ T) :
    ∃ j : ℕ, β * 2 ^ j ≤ T ∧ T ≤ 2 * (β * 2 ^ j) := by
  by_cases h : T ≤ 2 * β
  · exact ⟨0, by simpa using hT, by simpa using h⟩
  · obtain ⟨j, hj, hj'⟩ := exists_dyadic_annulus hβ (lt_of_not_ge h)
    refine ⟨j + 1, ?_, ?_⟩ <;> rw [pow_succ]
    · convert hj.le using 1; ring
    · convert hj' using 1; ring

private theorem signSum_sub {n : ℕ} (a b : Fin n → ℝ) (x : Fin n → Bool) :
    signSum (a - b) x = signSum a x - signSum b x := by
  simp only [signSum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem rounded_candidate_norm_le {n m : ℕ} {K T : ℝ} {A : Fin m → Fin n → Bool}
    {a : Fin n → ℝ} {w : Fin n → ℤ}
    (horth : ∀ j, signSum a (A j) = 0)
    (hclose : ∀ i, |(w i : ℝ) - (Real.sqrt (n : ℝ) / (2 * T)) * a i| ≤ 1)
    (hnorm : ∀ a : Fin n → ℝ, ∑ j, (signSum a (A j)) ^ 2 ≤
      K ^ 2 * (n : ℝ) * ∑ i, a i ^ 2) :
    ∑ j, (signSum (fun i => (w i : ℝ)) (A j)) ^ 2 ≤ K ^ 2 * (n : ℝ) ^ 2 := by
  let D := Real.sqrt (n : ℝ) / (2 * T)
  let e : Fin n → ℝ := (fun i => (w i : ℝ)) - D • a
  have he (j : Fin m) : signSum e (A j) = signSum (fun i => (w i : ℝ)) (A j) := by
    rw [show e = (fun i => (w i : ℝ)) - D • a by rfl, signSum_sub, signSum_const_mul,
      horth, mul_zero, sub_zero]
  have hs : (∑ i, e i ^ 2) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |e i| ≤ 1 := hclose i
        simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (e i)) zero_le_one).mpr hi
      _ = _ := by simp
  rw [pow_two (n : ℝ), ← mul_assoc]
  simp_rw [← he]
  exact (hnorm e).trans (mul_le_mul_of_nonneg_left hs (by positivity))

/-- Once the integer witnesses are counted, the conditional exceptional probability
is controlled by a union bound over dyadic scales and the tensorized profile. -/
theorem badConditionalNormal_prob_le_of_count
    {n m k J : ℕ} (hn : 0 < n) (hkn : k ≤ n) (hhalf : n ≤ 2 * k)
    (W : Set (Fin n → Bool)) (hW : W.Nonempty) {δ ρ L β K C E : ℝ}
    (hL : 1 ≤ L) (hβ : 0 < β) (hb : β ≤ 1) (hK : 0 ≤ K) (hC : 1 ≤ C) (hE : 0 ≤ E)
    (hJ : 1 ≤ β * 2 ^ J)
    (hcount : ∀ j ≤ J, β * 2 ^ j ≤ 1 / L →
      ((roundedConditionalCandidates n (uniformOn W) δ ρ L (β * 2 ^ j)).ncard : ℝ) ≤
        E * (C / (β * 2 ^ j)) ^ n) :
    (uniformOn Set.univ).real (badConditionalNormal n m (uniformOn W) δ ρ L β) ≤
      (uniformOn Set.univ).real {A : Fin m → Fin n → Bool |
        (Finset.univ.filter fun i => A i ∈ W).card < k} +
      (uniformOn Set.univ).real {A : Fin m → Fin n → Bool |
        ∃ a : Fin n → ℝ, K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) <
          ∑ j, (signSum a (A j)) ^ 2} +
      (J + 1 : ℝ) * (m.choose k : ℝ) * E * (C * (1440 * L * Real.exp (2 * K))) ^ n /
        β ^ (n - k) := by
  let ν := uniformOn W
  let : IsProbabilityMeasure ν := isProbabilityMeasure_uniformOn W.toFinite hW
  let μ : Measure (Fin m → Fin n → Bool) := uniformOn Set.univ
  let u (j : ℕ) := β * (2 : ℝ) ^ j
  let P (j : ℕ) := roundedConditionalCandidates n ν δ ρ L (u j)
  have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
  have hfin (j : ℕ) : (P j).Finite := roundedConditionalCandidates_finite n ν δ ρ L (hu j)
  let B : Set (Fin m → Fin n → Bool) := {A | (Finset.univ.filter fun i => A i ∈ W).card < k}
  let O : Set (Fin m → Fin n → Bool) := {A | ∃ a, K ^ 2 * (n : ℝ) * (∑ i, a i ^ 2) <
    ∑ j, (signSum a (A j)) ^ 2}
  let Q (w : Fin n → ℤ) : Set (Fin m → Fin n → Bool) :=
    {A | k ≤ (Finset.univ.filter fun i => A i ∈ W).card ∧
      ∑ j, (signSum (fun i => (w i : ℝ)) (A j)) ^ 2 ≤ (2 * K) ^ 2 * (k : ℝ) * (Real.sqrt (n : ℝ)) ^ 2}
  let U : Set (Fin m → Fin n → Bool) := ⋃ j ∈ Finset.range (J + 1), ⋃ w ∈ (hfin j).toFinset, Q w
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  have hs' : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hL₀ := zero_lt_one.trans_le hL
  have hsubset : badConditionalNormal n m ν δ ρ L β ⊆ (B ∪ O) ∪ U := by
    rintro A ⟨a, ha, ha', horth, hatom⟩
    by_cases hB : A ∈ B
    · exact Or.inl (Or.inl hB)
    by_cases hO : A ∈ O
    · exact Or.inl (Or.inr hO)
    refine Or.inr ?_
    obtain ⟨T, hTlo, hThi, w, hw, hprof, z, hz⟩ :=
      exists_integer_vector_of_large_zero_atom hn ν a hL hβ hb hatom
    obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_lower hβ hTlo
    have hj : j ≤ J := by
      by_contra! hlt
      have h := mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hlt) hβ
      have hle : T ≤ 1 := hThi.trans (div_le_one₀ hL₀ |>.mpr hL)
      exact (not_lt_of_ge hJ) ((h.trans_le hjlo).trans_le hle)
    have hP : w ∈ P j := by
      refine ⟨⟨a, ha, ha', T, hjlo, hjhi, hThi, hw⟩, fun t ht => (hprof t ht).trans ?_, z, ?_⟩
      · have hh : 72 * L * T ≤ 144 * L * u j := by
          change T ≤ 2 * u j at hjhi
          nlinarith only [mul_le_mul_of_nonneg_left hjhi hL₀.le]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh hs.le) (hs.trans_le ht).le
      · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjlo hL₀.le) (by norm_num)).trans hz
    have hnorm (a : Fin n → ℝ) : ∑ j, (signSum a (A j)) ^ 2 ≤ K ^ 2 * (n : ℝ) * ∑ i, a i ^ 2 :=
      le_of_not_gt (fun h => hO ⟨a, h⟩)
    refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj),
      Set.mem_iUnion₂.mpr ⟨w, (hfin j).mem_toFinset.mpr hP, le_of_not_gt hB, ?_⟩⟩
    refine (rounded_candidate_norm_le horth hw hnorm).trans ?_
    rw [hs']
    have hk' : (n : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hhalf
    have hk₀ : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hkn' : (n : ℝ) ≤ 4 * (k : ℝ) := by linarith only [hk', hk₀]
    calc
      _ ≤ K ^ 2 * (n : ℝ) * (4 * (k : ℝ)) := by
        rw [pow_two (n : ℝ), ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hkn' (by positivity)
      _ = _ := by ring
  let A₀ := 1440 * L * Real.exp (2 * K)
  have hA₀ : 1 ≤ A₀ := by
    have h₁ : (1 : ℝ) ≤ 1440 * L := by linarith only [hL]
    exact one_le_mul_of_one_le_of_one_le h₁ (Real.one_le_exp (by positivity))
  have hbound (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      μ.real (⋃ w ∈ (hfin j).toFinset, Q w) ≤
        (m.choose k : ℝ) * E * (C * A₀) ^ n / β ^ (n - k) := by
    by_cases hule : u j ≤ 1 / L
    · have huz : 0 < u j := hu j
      have hQ (w : Fin n → ℤ) (hw : w ∈ (hfin j).toFinset) :
          μ.real (Q w) ≤ (m.choose k : ℝ) * (A₀ * u j) ^ k := by
        have hP : w ∈ P j := (hfin j).mem_toFinset.mp hw
        have hh := uniformMatrix_sum_sq_le_of_smallBall_on_many_rows W hW
          (signSum (fun i => (w i : ℝ))) hs (by positivity : 0 ≤ 144 * L * u j / Real.sqrt (n : ℝ))
          (by positivity : 0 ≤ 2 * K) hP.2.1 m k
        have heq : 10 * (144 * L * u j / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) *
            Real.exp (2 * K) = A₀ * u j := by dsimp [A₀]; field_simp [hs.ne']; ring
        simpa only [heq] using hh
      have hcard : (((hfin j).toFinset.card : ℕ) : ℝ) ≤ E * (C / u j) ^ n := by
        rw [← Set.ncard_eq_toFinset_card _ (hfin j)]
        exact hcount j (by simpa using hj) hule
      have hscale : β ≤ u j := by
        simpa [u] using (le_mul_of_one_le_right hβ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)))
      have hp₀ : A₀ ^ k ≤ A₀ ^ n := pow_le_pow_right₀ hA₀ hkn
      have hp₁ : β ^ (n - k) ≤ u j ^ (n - k) := pow_le_pow_left₀ hβ.le hscale _
      calc
        _ ≤ ∑ w ∈ (hfin j).toFinset, μ.real (Q w) := measureReal_biUnion_finset_le _ _
        _ ≤ ∑ _w ∈ (hfin j).toFinset, (m.choose k : ℝ) * (A₀ * u j) ^ k := Finset.sum_le_sum hQ
        _ = (((hfin j).toFinset.card : ℕ) : ℝ) * ((m.choose k : ℝ) * (A₀ * u j) ^ k) := by simp
        _ ≤ (E * (C / u j) ^ n) * ((m.choose k : ℝ) * (A₀ * u j) ^ k) := by gcongr
        _ = (m.choose k : ℝ) * E * (C ^ n * A₀ ^ k) / (u j) ^ (n - k) := by
          have heq : u j ^ n = u j ^ k * u j ^ (n - k) := by
            rw [← pow_add, Nat.add_sub_of_le hkn]
          rw [div_pow, mul_pow A₀, heq]
          field_simp [huz.ne']
        _ ≤ _ := by
          rw [mul_pow C A₀]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hp₁ |>.trans'
          gcongr
    · have hP : P j = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun w hw => by
        obtain ⟨⟨_, _, _, _, hlo, _, hhi, _⟩, _, _⟩ := hw
        exact hule (hlo.trans hhi)
      have hfin' : (hfin j).toFinset = ∅ := by
        ext w
        simp only [Set.Finite.mem_toFinset, hP, Set.mem_empty_iff_false, Finset.notMem_empty]
      have he : (⋃ w ∈ (hfin j).toFinset, Q w) = ∅ := by rw [hfin']; simp
      rw [he, measureReal_empty]
      positivity
  have hU : μ.real U ≤ (J + 1 : ℝ) * (m.choose k : ℝ) * E * (C * A₀) ^ n / β ^ (n - k) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (J + 1), μ.real (⋃ w ∈ (hfin j).toFinset, Q w) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (J + 1),
          ((m.choose k : ℝ) * E * (C * A₀) ^ n / β ^ (n - k)) := Finset.sum_le_sum hbound
      _ = _ := by simp [Nat.cast_add]; ring
  change μ.real (badConditionalNormal n m ν δ ρ L β) ≤ μ.real B + μ.real O + _
  calc
    _ ≤ μ.real ((B ∪ O) ∪ U) := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ μ.real (B ∪ O) + μ.real U := measureReal_union_le _ _
    _ ≤ μ.real B + μ.real O + μ.real U := add_le_add_left (measureReal_union_le _ _) _
    _ ≤ _ := add_le_add_right hU _

end BooleanThreshold
