module

public import BooleanThreshold.NonPairSign
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds

public section

open Finset Filter MeasureTheory ProbabilityTheory Module
open scoped ENNReal BigOperators

namespace BooleanThreshold

/-- The null-vector concentration bound restricted to the image of a linear parameterization. -/
theorem signLaw_exists_parameterized_null_le {n r : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] (Fin r → ℝ)) (S : Set V) {q : ℝ≥0∞}
    (hS : ∀ a ∈ S, f a ≠ 0) (hconc : ∀ a ∈ S, zeroAtom (f a) ≤ q)
    (hn : finrank ℝ V - 1 ≤ n) :
    signLaw n r {v | ∃ a ∈ S, ∀ j, ∑ i, f a i * v i j = 0} ≤
      (n.choose (finrank ℝ V - 1) : ℝ≥0∞) * q ^ (n - (finrank ℝ V - 1)) := by
  classical
  let μ : Measure (Fin r → Bool) := uniformOn Set.univ
  let eval (row : Fin r → Bool) : Module.Dual ℝ V :=
    (dotProductBilin ℝ ℝ (realSigns row)).comp f
  have heval (row : Fin r → Bool) (a : V) :
      eval row a = ∑ i, f a i * realSigns row i := by
    simp [eval, dotProduct, mul_comm]
  have hmap : μ.map (@realSigns r) = uniformOn (signCube r) := by
    rw [map_uniformOn_univ_eq_uniformOn_range (realSigns_injective r), range_realSigns]
  have hconc' (a : V) (ha : a ∈ S) : μ {row | eval row a = 0} ≤ q := by
    calc
      _ = μ {row | ∑ i, f a i * realSigns row i = 0} := by simp only [heval]
      _ = zeroAtom (f a) := by rw [zeroAtom, ← hmap, (realSigns_measurableEmbedding r).map_apply]; rfl
      _ ≤ q := hconc a ha
  let E : Set (Fin n → Fin r → ℝ) :=
    {rows | ∃ a ∈ S, ∀ j, ∑ i, f a i * rows j i = 0}
  change signLaw n r ((fun v j i => v i j) ⁻¹' E) ≤ _
  rw [signLaw_transpose, signLaw_apply, ← pi_uniformOn_univ]
  change Measure.pi (fun _ : Fin n => μ)
    {rows | ∃ a ∈ S, ∀ j, ∑ i, f a i * realSigns (rows j) i = 0} ≤ _
  have hS' (a : V) (ha : a ∈ S) : a ≠ 0 := fun h => hS a ha (h ▸ f.map_zero)
  simpa only [heval] using measure_exists_null_vector_le (μ := μ) eval S hS' hconc' hn

private noncomputable def parameterizeCoordinates {n : ℕ} (I : Finset (Fin n)) (b : I → ℝ) :
    (Option ↥(Iᶜ) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun a i := if h : i ∈ I then a none * b ⟨i, h⟩ else a (some ⟨i, mem_compl.mpr h⟩)
  map_add' a a' := by
    funext i
    by_cases hi : i ∈ I <;> simp [hi, add_mul]
  map_smul' c a := by
    funext i
    by_cases hi : i ∈ I <;> simp [hi, mul_assoc]

private def fixedCoordinatesNull {n : ℕ} (I : Finset (Fin n)) (b : I → ℝ) (q : ℝ≥0∞) :
    Set (Fin n → Fin n → ℝ) :=
  {v | ∃ a : Fin n → ℝ, a ≠ 0 ∧ zeroAtom a ≤ q ∧
    (∀ i : I, a i = b i) ∧ ∀ j, ∑ i, a i * v i j = 0}

private theorem signLaw_fixed_coords_null_le {n : ℕ}
    (I : Finset (Fin n)) (b : I → ℝ) (q : ℝ≥0∞) :
    signLaw n n (fixedCoordinatesNull I b q) ≤
      (n.choose (n - I.card) : ℝ≥0∞) * q ^ I.card := by
  classical
  let f := parameterizeCoordinates I b
  let S : Set (Option ↥(Iᶜ) → ℝ) := {a | f a ≠ 0 ∧ zeroAtom (f a) ≤ q}
  have ha (x : Fin n → ℝ) (hx : ∀ i : I, x i = b i) :
      ∃ a : Option ↥(Iᶜ) → ℝ, f a = x := by
    let a : Option ↥(Iᶜ) → ℝ := fun i => i.elim 1 (fun j => x j)
    refine ⟨a, funext fun i => ?_⟩
    by_cases hi : i ∈ I
    · simpa [f, parameterizeCoordinates, hi, a] using (hx ⟨i, hi⟩).symm
    · simp [f, parameterizeCoordinates, hi, a]
  have hsub : fixedCoordinatesNull I b q ⊆
      {v | ∃ a ∈ S, ∀ j, ∑ i, f a i * v i j = 0} := by
    rintro v ⟨x, hne, hconc, hcoords, hnull⟩
    obtain ⟨a, rfl⟩ := ha x hcoords
    exact ⟨a, ⟨hne, hconc⟩, hnull⟩
  have hI : I.card ≤ n := by simpa using card_le_univ I
  have hdim : finrank ℝ (Option ↥(Iᶜ) → ℝ) - 1 = n - I.card := by
    rw [finrank_fintype_fun_eq_card]
    simp
  refine (measure_mono hsub).trans ?_
  have h := signLaw_exists_parameterized_null_le (n := n) f S (fun a ha => ha.1) (fun a ha => ha.2)
    (by rw [hdim]; exact Nat.sub_le ..)
  rw [hdim, Nat.sub_sub_self hI] at h
  exact h

/-- Integer null vectors of small atom with at least `m` coefficients of absolute value at most
`B`. -/
@[expose] def smallCoefficientsNull (n m B : ℕ) (q : ℝ≥0∞) : Set (Fin n → Fin n → ℝ) := by
  classical
  exact {v | ∃ a : Fin n → ℤ, (fun i => (a i : ℝ)) ≠ 0 ∧
    zeroAtom (fun i => a i) ≤ q ∧ m ≤ (univ.filter fun i => (a i).natAbs ≤ B).card ∧
    ∀ j, ∑ i, (a i : ℝ) * v i j = 0}

/-- Enumerate the chosen small coordinates and their integer values, then use concentration on
the resulting families of coefficient vectors. -/
theorem signLaw_small_coords_null_le (n m B : ℕ) (q : ℝ≥0∞) :
    signLaw n n (smallCoefficientsNull n m B q) ≤
      (n.choose m : ℝ≥0∞) * (2 * (B : ℝ≥0∞) + 1) ^ m *
        (n.choose (n - m) : ℝ≥0∞) * q ^ m := by
  classical
  let selections := (univ : Finset (Fin n)).powersetCard m
  let interval := Icc (-(B : ℤ)) (B : ℤ)
  let E (I : Finset (Fin n)) (b : I → ↥interval) :=
    fixedCoordinatesNull I (fun i => ((b i).val : ℝ)) q
  let U (I : Finset (Fin n)) :=
    ⋃ b ∈ (univ : Finset (I → ↥interval)), E I b
  have hsub : smallCoefficientsNull n m B q ⊆ ⋃ I ∈ selections, U I := by
    rintro v ⟨a, hne, hconc, hcard, hnull⟩
    let small := (univ : Finset (Fin n)).filter fun i => (a i).natAbs ≤ B
    obtain ⟨I, hIsub, hIcard⟩ := exists_subset_card_eq hcard
    have hI : I ∈ selections := mem_powersetCard.mpr ⟨subset_univ _, hIcard⟩
    have hbounded (i : I) : a i ∈ interval := by
      have hi : (a i).natAbs ≤ B := (mem_filter.mp (hIsub i.prop)).2
      rw [mem_Icc]
      omega
    let b (i : I) : ↥interval := ⟨a i, hbounded i⟩
    refine Set.mem_iUnion₂.mpr ⟨I, hI, Set.mem_iUnion₂.mpr ⟨b, mem_univ _, ?_⟩⟩
    exact ⟨fun i => a i, hne, hconc, fun _ => rfl, hnull⟩
  have hinterval : interval.card = 2 * B + 1 := by
    rw [show interval = Icc (-(B : ℤ)) (B : ℤ) from rfl, Int.card_Icc]
    omega
  have hU (I : Finset (Fin n)) (hI : I ∈ selections) :
      signLaw n n (U I) ≤
        (2 * (B : ℝ≥0∞) + 1) ^ m * (n.choose (n - m) : ℝ≥0∞) * q ^ m := by
    have hIcard := (mem_powersetCard.mp hI).2
    calc
      _ ≤ ∑ b : I → ↥interval, signLaw n n (E I b) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _b : I → ↥interval, (n.choose (n - m) : ℝ≥0∞) * q ^ m := by
        exact sum_le_sum fun b _ => by simpa only [hIcard] using
          (signLaw_fixed_coords_null_le I (fun i => ((b i).val : ℝ)) q)
      _ = _ := by
        simp [hinterval, hIcard, mul_assoc]
  calc
    _ ≤ signLaw n n (⋃ I ∈ selections, U I) := measure_mono hsub
    _ ≤ ∑ I ∈ selections, signLaw n n (U I) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ selections, (2 * (B : ℝ≥0∞) + 1) ^ m *
        (n.choose (n - m) : ℝ≥0∞) * q ^ m := sum_le_sum hU
    _ = _ := by simp [selections, card_powersetCard, mul_assoc]

/-- Real-valued form of the finite bound for small coefficients. -/
theorem signLaw_small_coords_null_real_le (n m B : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    (signLaw n n).real (smallCoefficientsNull n m B (ENNReal.ofReal q)) ≤
      (n.choose m : ℝ) * (2 * (B : ℝ) + 1) ^ m * (n.choose (n - m) : ℝ) * q ^ m := by
  have hB : 2 * (B : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have htop : (n.choose m : ℝ≥0∞) * (2 * (B : ℝ≥0∞) + 1) ^ m *
        (n.choose (n - m) : ℝ≥0∞) * (ENNReal.ofReal q) ^ m ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.add_ne_top.mpr ⟨hB, by simp⟩)))
        (by simp))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h := ENNReal.toReal_mono htop (signLaw_small_coords_null_le n m B (ENNReal.ofReal q))
  have hadd : (2 * (B : ℝ≥0∞) + 1).toReal = 2 * (B : ℝ) + 1 := by
    rw [ENNReal.toReal_add hB (by simp)]
    simp [ENNReal.toReal_mul]
  simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hq,
    hadd] using h

/-- When the atom is at most `e^{-η n}` and at least half the coefficients have magnitude at most
`e^{η n/2}`, the probability remains exponentially small after multiplication by `2^n`. -/
theorem signLaw_small_coords_null_exponential {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ n *
        (signLaw n n).real
          (smallCoefficientsNull n ((n + 1) / 2) ⌊Real.exp (η / 2 * (n : ℝ))⌋₊
            (ENNReal.ofReal (Real.exp (-η * (n : ℝ))))) ≤
        Real.exp (-(n : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * (Real.log 24 + 1) / η)
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  let m := (n + 1) / 2
  let B := ⌊Real.exp (η / 2 * (n : ℝ))⌋₊
  let R := (signLaw n n).real
    (smallCoefficientsNull n m B (ENNReal.ofReal (Real.exp (-η * (n : ℝ)))))
  change (2 : ℝ) ^ n * R ≤ _
  have hkn : Real.log 24 + 1 ≤ η * (n : ℝ) / 4 := by
    have hN' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have := (div_le_iff₀ hη).mp (hN.trans hN')
    linarith
  have hm : m ≤ n := by dsimp [m]; omega
  have hhalf : (n : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show n ≤ 2 * m from by dsimp [m]; omega)
  have hquad : (Real.log 24 + 1) * (n : ℝ) ≤ η / 2 * (n : ℝ) * m := by
    calc
      _ ≤ (η * (n : ℝ) / 4) * n := mul_le_mul_of_nonneg_right hkn (by positivity)
      _ ≤ (η * (n : ℝ) / 4) * (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = _ := by ring
  have hchoose (s : ℕ) : (n.choose s : ℝ) ≤ 2 ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n s
  have hcap : 2 * (B : ℝ) + 1 ≤ 3 * Real.exp (η / 2 * (n : ℝ)) := by
    have hB : (B : ℝ) ≤ Real.exp (η / 2 * (n : ℝ)) :=
      Nat.floor_le (Real.exp_nonneg _)
    have he : 1 ≤ Real.exp (η / 2 * (n : ℝ)) := Real.one_le_exp (by positivity)
    linarith
  have hprob : R ≤ (2 : ℝ) ^ n * (3 * Real.exp (η / 2 * (n : ℝ))) ^ m *
        (2 : ℝ) ^ n * (Real.exp (-η * (n : ℝ))) ^ m := by
    apply (signLaw_small_coords_null_real_le n m B _ (Real.exp_nonneg _)).trans
    gcongr <;> exact hchoose _
  have hpow₂ : (2 : ℝ) ^ n * 2 ^ n * 2 ^ n = 8 ^ n := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hpow₃ : (3 * Real.exp (η / 2 * (n : ℝ))) ^ m * (Real.exp (-η * (n : ℝ))) ^ m =
      (3 : ℝ) ^ m * Real.exp (-(η / 2 * (n : ℝ) * m)) := by
    rw [← mul_pow, mul_assoc, ← Real.exp_add, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  calc
    _ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n * (3 * Real.exp (η / 2 * (n : ℝ))) ^ m *
          (2 : ℝ) ^ n * (Real.exp (-η * (n : ℝ))) ^ m) :=
      mul_le_mul_of_nonneg_left hprob (by positivity)
    _ = ((2 : ℝ) ^ n * 2 ^ n * 2 ^ n) *
        ((3 * Real.exp (η / 2 * (n : ℝ))) ^ m * (Real.exp (-η * (n : ℝ))) ^ m) := by ring
    _ = (8 : ℝ) ^ n * (3 ^ m * Real.exp (-(η / 2 * (n : ℝ) * m))) := by rw [hpow₂, hpow₃]
    _ ≤ (8 : ℝ) ^ n * (3 ^ n * Real.exp (-(η / 2 * (n : ℝ) * m))) := by
      gcongr
      norm_num
    _ = (24 : ℝ) ^ n * Real.exp (-(η / 2 * (n : ℝ) * m)) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ = Real.exp ((n : ℝ) * Real.log 24 - η / 2 * (n : ℝ) * m) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 24)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hquad])

end BooleanThreshold
