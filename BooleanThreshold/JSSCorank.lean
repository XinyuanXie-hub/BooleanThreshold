module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.NonPairSign

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Module
open scoped ENNReal BigOperators

namespace BooleanThreshold

/-- A family of Boolean sign rows has a nonzero common normal with zero atom at most `q`. -/
def hasSmallAtomNormal {ι : Type*} {d : ℕ} (q : ℝ≥0∞) (rows : ι → Fin d → Bool) : Prop :=
  ∃ a : Fin d → ℝ, a ≠ 0 ∧ zeroAtom a ≤ q ∧
    ∀ j, ∑ i, a i * realSigns (rows j) i = 0

private theorem spans_subset_of_rank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m k : ℕ} (v : Fin m → V) (hk : k ≤ m)
    (hrank : finrank K (Submodule.span K (Set.range v)) ≤ k) :
    ∃ I : Finset (Fin m), I.card = k ∧
      Submodule.span K (v '' (I : Set (Fin m))) = Submodule.span K (Set.range v) := by
  classical
  obtain ⟨κ, e, he, hspan, hind⟩ := exists_linearIndependent' K v
  let : Fintype κ := Fintype.ofInjective e he
  let J := Finset.univ.map (⟨e, he⟩ : κ ↪ Fin m)
  have hJ : Set.range (v ∘ e) = v '' (J : Set (Fin m)) := by
    ext x
    simp [J, Function.comp_def, Set.mem_image]
  have hcard : J.card ≤ k := by
    rw [show J.card = Fintype.card κ by simp [J], ← finrank_span_eq_card hind, hspan]
    exact hrank
  obtain ⟨I, hJI, _, hI⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ J) hcard (by simpa using hk)
  refine ⟨I, hI, le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [← hspan, hJ]
  exact Submodule.span_mono (Set.image_mono hJI)

private theorem measure_rows_in_span_le {ι τ : Type*} [Fintype τ] {d : ℕ}
    (aRows : ι → Fin d → Bool) {q : ℝ≥0∞} (ha : hasSmallAtomNormal q aRows) :
    Measure.pi (fun _ : τ => uniformOn (Set.univ : Set (Fin d → Bool)))
        {rows | ∀ j, realSigns (rows j) ∈
          Submodule.span ℝ (Set.range fun i => realSigns (aRows i))} ≤
      q ^ Fintype.card τ := by
  obtain ⟨a, _, hq, hzero⟩ := ha
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ a
  have hL (v : Fin d → ℝ) : L v = ∑ i, a i * v i := rfl
  have hspan : Submodule.span ℝ (Set.range fun i => realSigns (aRows i)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr ((hL _).trans (hzero i))
  let rowEvent : Set (Fin d → Bool) := {x | ∑ i, a i * realSigns x i = 0}
  have hrow : uniformOn Set.univ rowEvent ≤ q := by
    rwa [zeroAtom, uniformOn_signCube_apply] at hq
  calc
    _ ≤ Measure.pi (fun _ : τ => uniformOn Set.univ) (Set.univ.pi (fun _ => rowEvent)) := by
      apply measure_mono
      intro rows hr j _
      exact (hL _).symm.trans (LinearMap.mem_ker.mp (hspan (hr j)))
    _ = uniformOn Set.univ rowEvent ^ Fintype.card τ := by
      rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ]
    _ ≤ _ := pow_le_pow_left' hrow _

private theorem selected_rows_bad_probability {n d m : ℕ} {I : Finset (Fin m)}
    (hI : I.card = n) (q : ℝ≥0∞) :
    Measure.pi (fun _ : I => uniformOn (Set.univ : Set (Fin d → Bool)))
        {aRows | ¬ hasSmallAtomNormal q aRows} =
      uniformOn Set.univ {aRows : Fin n → Fin d → Bool | ¬ hasSmallAtomNormal q aRows} := by
  classical
  let eI := Fintype.equivFinOfCardEq (show Fintype.card I = n by simpa using hI)
  let e := Equiv.arrowCongr eI (Equiv.refl (Fin d → Bool))
  let event : Set (Fin n → Fin d → Bool) := {aRows | ¬ hasSmallAtomNormal q aRows}
  have hset : {aRows | ¬ hasSmallAtomNormal q aRows} = e ⁻¹' event := by
    ext rows
    change ¬ hasSmallAtomNormal q rows ↔ ¬ hasSmallAtomNormal q (e rows)
    apply not_congr
    constructor
    · rintro ⟨a, ha, hq, hzero⟩
      exact ⟨a, ha, hq, fun j => hzero (eI.symm j)⟩
    · rintro ⟨a, ha, hq, hzero⟩
      refine ⟨a, ha, hq, fun j => ?_⟩
      simpa [e] using hzero (eI j)
  rw [pi_uniformOn_univ (ι := I) (Ω := Fin d → Bool), hset]
  have h := congrArg (fun μ : Measure (Fin n → Fin d → Bool) => μ event)
    (map_uniformOn_univ_of_equiv e)
  rwa [Measure.map_apply (measurable_of_finite e) event.toFinite.measurableSet] at h

private theorem square_selected_span_le {n : ℕ} (I : Finset (Fin (n + 2))) (hI : I.card = n)
    (q : ℝ≥0∞) :
    uniformOn Set.univ {v : Fin (n + 2) → Fin (n + 2) → Bool |
      Submodule.span ℝ (Set.range (fun i : I => realSigns (v i))) =
        Submodule.span ℝ (Set.range (fun i => realSigns (v i)))} ≤
      uniformOn Set.univ {aRows : Fin n → Fin (n + 2) → Bool |
        ¬ hasSmallAtomNormal q aRows} + q ^ 2 := by
  classical
  let ι := {i : Fin (n + 2) // i ∈ I}
  let τ := {i : Fin (n + 2) // i ∉ I}
  let rowLaw : Measure (Fin (n + 2) → Bool) := uniformOn Set.univ
  let ν₁ := Measure.pi fun _ : ι => rowLaw
  let ν₂ := Measure.pi fun _ : τ => rowLaw
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin (n + 2) => Fin (n + 2) → Bool) (· ∈ I)
  let t : Set ((ι → Fin (n + 2) → Bool) × (τ → Fin (n + 2) → Bool)) :=
    {p | ∀ j, realSigns (p.2 j) ∈ Submodule.span ℝ (Set.range fun i => realSigns (p.1 i))}
  let bad : Set (ι → Fin (n + 2) → Bool) := {aRows | ¬ hasSmallAtomNormal q aRows}
  have hcard : Fintype.card τ = 2 := by
    rw [show Fintype.card τ = (n + 2) - I.card by
      simp [τ, Fintype.card_subtype_compl, Fintype.card_coe]]
    omega
  have hpres : MeasurePreserving e (uniformOn Set.univ) (ν₁.prod ν₂) := by
    rw [← pi_uniformOn_univ (ι := Fin (n + 2)) (Ω := Fin (n + 2) → Bool)]
    dsimp [e, ν₁, ν₂, ι, τ]
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : Fin (n + 2) => rowLaw) (· ∈ I) using 1
    congr!
  have hsub :
      {v : Fin (n + 2) → Fin (n + 2) → Bool |
        Submodule.span ℝ (Set.range (fun i : I => realSigns (v i))) =
          Submodule.span ℝ (Set.range (fun i => realSigns (v i)))} ⊆ e ⁻¹' t := by
    intro v hv j
    change realSigns (v j) ∈ Submodule.span ℝ (Set.range (fun i : I => realSigns (v i)))
    rw [hv]
    exact Submodule.subset_span (Set.mem_range_self j.1)
  have hGood : (ν₁.prod ν₂) (t \ (bad ×ˢ Set.univ)) ≤ q ^ 2 := by
    rw [Measure.prod_apply (Set.toFinite _).measurableSet]
    calc
      _ ≤ ∫⁻ _ : ι → Fin (n + 2) → Bool, q ^ 2 ∂ν₁ := by
        apply lintegral_mono
        intro aRows
        by_cases ha : hasSmallAtomNormal q aRows
        · calc
            _ ≤ ν₂ {rows | ∀ j, realSigns (rows j) ∈
                Submodule.span ℝ (Set.range fun i : ι => realSigns (aRows i))} :=
              measure_mono fun _ h => h.1
            _ ≤ _ := by
              simpa only [hcard] using measure_rows_in_span_le (τ := τ) aRows ha
        · have hEmpty : Prod.mk aRows ⁻¹' (t \ (bad ×ˢ Set.univ)) = ∅ := by
            ext rows
            simp [bad, ha]
          simp [hEmpty]
      _ = _ := by simp
  calc
    _ ≤ uniformOn Set.univ (e ⁻¹' t) := measure_mono hsub
    _ = (ν₁.prod ν₂) t := hpres.measure_preimage t.toFinite.measurableSet.nullMeasurableSet
    _ ≤ (ν₁.prod ν₂) ((bad ×ˢ Set.univ) ∪ (t \ (bad ×ˢ Set.univ))) :=
      measure_mono (by rw [Set.union_sdiff_self]; exact Set.subset_union_right)
    _ ≤ (ν₁.prod ν₂) (bad ×ˢ Set.univ) + (ν₁.prod ν₂) (t \ (bad ×ˢ Set.univ)) :=
      measure_union_le _ _
    _ ≤ ν₁ bad + q ^ 2 := by
      rw [Measure.prod_prod, measure_univ, mul_one]
      exact add_le_add (le_refl _) hGood
    _ = _ := by rw [selected_rows_bad_probability hI q]

/-- Removing two redundant rows bounds the square corank event by a small-atom
failure probability and the squared concentration of a common normal. -/
theorem square_corank_two_probability_le_of_small_atom (n : ℕ) (q : ℝ≥0∞) :
    uniformOn Set.univ {v : Fin (n + 2) → Fin (n + 2) → Bool |
      finrank ℝ (Submodule.span ℝ (Set.range fun i => realSigns (v i))) ≤ n} ≤
      ((n + 2).choose 2 : ℝ≥0∞) *
        (uniformOn Set.univ {aRows : Fin n → Fin (n + 2) → Bool |
          ¬ hasSmallAtomNormal q aRows} + q ^ 2) := by
  classical
  let choices := (Finset.univ : Finset (Fin (n + 2))).powersetCard n
  let E (I : Finset (Fin (n + 2))) : Set (Fin (n + 2) → Fin (n + 2) → Bool) :=
    {v | Submodule.span ℝ (Set.range (fun i : I => realSigns (v i))) =
      Submodule.span ℝ (Set.range (fun i => realSigns (v i)))}
  let μ : Measure (Fin (n + 2) → Fin (n + 2) → Bool) := uniformOn Set.univ
  let b := uniformOn Set.univ {aRows : Fin n → Fin (n + 2) → Bool |
    ¬ hasSmallAtomNormal q aRows} + q ^ 2
  calc
    _ ≤ μ (⋃ I ∈ choices, E I) := by
      apply measure_mono
      intro v hv
      obtain ⟨I, hcard, hspan⟩ :=
        spans_subset_of_rank_le (fun i => realSigns (v i)) (by omega : n ≤ n + 2) hv
      refine Set.mem_iUnion₂.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
      change Submodule.span ℝ (Set.range (fun i : I => realSigns (v i))) = _
      rw [← hspan]
      congr 1
      ext x
      simp [Set.mem_image]
    _ ≤ ∑ I ∈ choices, μ (E I) := measure_biUnion_finset_le choices E
    _ ≤ ∑ _I ∈ choices, b :=
      Finset.sum_le_sum fun I hI => square_selected_span_le I (Finset.mem_powersetCard.mp hI).2 q
    _ = _ := by
      have hchoose : (n + 2).choose n = (n + 2).choose 2 := by
        rw [← Nat.choose_symm (by omega : 2 ≤ n + 2), Nat.add_sub_cancel]
      simp [choices, b, hchoose, mul_add]

/-- The corank bound with real-valued probabilities. -/
theorem square_corank_two_real_le_of_small_atom (n : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞) :
    (uniformOn Set.univ).real {v : Fin (n + 2) → Fin (n + 2) → Bool |
      finrank ℝ (Submodule.span ℝ (Set.range fun i => realSigns (v i))) ≤ n} ≤
      ((n + 2).choose 2 : ℝ) *
        ((uniformOn Set.univ).real {aRows : Fin n → Fin (n + 2) → Bool |
          ¬ hasSmallAtomNormal q aRows} + q.toReal ^ 2) := by
  let μ : Measure (Fin n → Fin (n + 2) → Bool) := uniformOn Set.univ
  let E : Set (Fin n → Fin (n + 2) → Bool) := {aRows | ¬ hasSmallAtomNormal q aRows}
  have hfinite : ((n + 2).choose 2 : ℝ≥0∞) * (μ E + q ^ 2) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.pow_ne_top hq⟩)
  have h := ENNReal.toReal_mono hfinite (square_corank_two_probability_le_of_small_atom n q)
  change _ ≤ (((n + 2).choose 2 : ℝ≥0∞) * (μ E + q ^ 2)).toReal at h
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_add (measure_ne_top μ E) (ENNReal.pow_ne_top hq), ENNReal.toReal_pow] using h

/-- An exponentially rare failure to find a small-atom normal gives a square
corank bound at some geometric rate strictly below one half. -/
theorem square_corank_two_geometric_of_small_atom {b D : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) (hD : 0 ≤ D)
    (hfail : ∀ᶠ n : ℕ in atTop, (uniformOn Set.univ).real
      {aRows : Fin n → Fin (n + 2) → Bool | ¬ hasSmallAtomNormal ((2 / 3 : ℝ≥0∞) ^ (n + 2)) aRows}
      ≤ D * b ^ (n + 2)) :
    ∃ a : ℝ, 1 / 4 ≤ a ∧ a < 1 / 2 ∧ ∃ C ≥ (0 : ℝ), ∀ᶠ r : ℕ in atTop,
      (uniformOn Set.univ).real {v : Fin (r + 1) → Fin (r + 1) → Bool |
        finrank ℝ (Submodule.span ℝ (Set.range fun i => realSigns (v i))) < r} ≤ C * a ^ (r + 1) := by
  let base := max b (4 / 9)
  have hbase : 0 < base := hb.trans_le (le_max_left _ _)
  have hbase' : base < 1 / 2 := max_lt hb' (by norm_num)
  let a := (base + 1 / 2) / 2
  have ha : base < a := by dsimp [a]; linarith
  have ha' : a < 1 / 2 := by dsimp [a]; linarith
  have hquarter : (1 / 4 : ℝ) ≤ a :=
    (by norm_num : (1 / 4 : ℝ) ≤ 4 / 9).trans ((le_max_right b (4 / 9)).trans ha.le)
  obtain ⟨C, hC, hpow⟩ := polynomial_div_pow_bounded 2 (show 1 < a / base by
    rw [lt_div_iff₀ hbase, one_mul]
    exact ha)
  refine ⟨a, hquarter, ha', (D + 1) * C, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfail
  refine eventually_atTop.mpr ⟨N + 1, fun r hr => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.lt_succ_iff]
  let q := (2 / 3 : ℝ≥0∞) ^ (n + 2)
  have hq : q ≠ ∞ := ENNReal.pow_ne_top (by simp [ENNReal.div_ne_top])
  have hq' : q.toReal ^ 2 = (4 / 9 : ℝ) ^ (n + 2) := by
    simp only [q, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    rw [← pow_mul, Nat.mul_comm (n + 2) 2, pow_mul]
    norm_num
  have hchoose : ((n + 2).choose 2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow (n + 2) 2
  have hmul : ((n + 2 : ℕ) : ℝ) ^ 2 * base ^ (n + 2) ≤ C * a ^ (n + 2) := by
    have hm := (div_le_iff₀ (pow_pos (div_pos (hbase.trans ha) hbase) (n + 2))).mp (hpow (n + 2))
    rw [div_pow, ← mul_div_assoc] at hm
    exact (le_div_iff₀ (pow_pos hbase _)).mp hm
  calc
    _ ≤ ((n + 2).choose 2 : ℝ) *
        ((uniformOn Set.univ).real {aRows : Fin n → Fin (n + 2) → Bool |
          ¬ hasSmallAtomNormal q aRows} + q.toReal ^ 2) :=
      square_corank_two_real_le_of_small_atom n hq
    _ ≤ ((n + 2).choose 2 : ℝ) * (D * b ^ (n + 2) + (4 / 9 : ℝ) ^ (n + 2)) := by
      rw [hq']
      gcongr
      exact hN n (by omega)
    _ ≤ ((n + 2 : ℕ) : ℝ) ^ 2 * (D * base ^ (n + 2) + base ^ (n + 2)) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = (D + 1) * (((n + 2 : ℕ) : ℝ) ^ 2 * base ^ (n + 2)) := by ring
    _ ≤ (D + 1) * C * a ^ (n + 1 + 1) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hmul (by positivity)

end BooleanThreshold
