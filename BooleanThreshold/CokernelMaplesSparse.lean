module

public import BooleanThreshold.CokernelLargeProgressions
public import BooleanThreshold.NonPair
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.ToLin

public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix

namespace BooleanThreshold

/-- The rectangular matrix has a nonzero modular null vector with at most
the given number of nonzero coordinates. -/
@[expose] def hasSparseBinaryNormal (q N m s : ℕ) (R : Fin m → Fin N → Bool) : Prop :=
  ∃ a : Fin N → ZMod q, a ≠ 0 ∧
    (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ s ∧
    ∀ j, a ⬝ᵥ binaryColumn (ZMod q) (R j) = 0

private theorem exists_prime_sparse_normal {q N m s : ℕ} [NeZero q]
    {R : Fin m → Fin N → Bool} (h : hasSparseBinaryNormal q N m s R) :
    ∃ p ∈ q.primeFactors, hasSparseBinaryNormal p N m s R := by
  classical
  obtain ⟨a, ha, hs, hnull⟩ := h
  let d := Nat.gcd q (Finset.univ.gcd (fun i => (a i).val))
  have hdq : d ∣ q := Nat.gcd_dvd_left _ _
  have hda (i : Fin N) : d ∣ (a i).val :=
    (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd (Finset.mem_univ i))
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdq (NeZero.pos q)
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    contrapose! ha
    ext i
    exact ha i
  have hval : 0 < (a i).val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero _).not.mpr hi)
  have hdlt : d < q := (Nat.le_of_dvd hval (hda i)).trans_lt (ZMod.val_lt _)
  let v := q / d
  have hv : d * v = q := Nat.mul_div_cancel' hdq
  have hv' : v ≠ 1 := by
    intro h
    rw [h, mul_one] at hv
    omega
  obtain ⟨p, hp, hpv⟩ := Nat.exists_prime_and_dvd hv'
  let b (i : Fin N) := (a i).val / d
  have hab (i : Fin N) : d * b i = (a i).val := Nat.mul_div_cancel' (hda i)
  have hnz : (fun i => (b i : ZMod p)) ≠ 0 := by
    intro hb
    have hb' (i : Fin N) : p ∣ b i :=
      (ZMod.natCast_eq_zero_iff _ _).mp (congrFun hb i)
    have hbig : d * p ∣ d := Nat.dvd_gcd
      (hv ▸ Nat.mul_dvd_mul_left d hpv)
      (Finset.dvd_gcd fun i _ => hab i ▸ Nat.mul_dvd_mul_left d (hb' i))
    have hle := Nat.le_of_dvd hd hbig
    have htwo := Nat.mul_le_mul_left d hp.two_le
    omega
  have hpq : p ∣ q := hpv.trans (hv ▸ dvd_mul_left v d)
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩, fun i => (b i : ZMod p),
    hnz, ?_, fun j => ?_⟩
  · refine (Finset.card_le_card ?_).trans hs
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, fun ha0 => hi.2 ?_⟩
    simp [b, ha0]
  · let z : ℕ := ∑ i, b i * binaryColumn ℕ (R j) i
    have hcast (k : ℕ) (i : Fin N) :
        (binaryColumn ℕ (R j) i : ZMod k) = binaryColumn (ZMod k) (R j) i := by
      cases h : R j i <;> simp [binaryColumn, h]
    have hz : q ∣ d * z := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      have hdz : ((d * z : ℕ) : ZMod q) =
          a ⬝ᵥ binaryColumn (ZMod q) (R j) := by
        simp only [z, Finset.mul_sum, Nat.cast_sum, ← mul_assoc, hab, Nat.cast_mul,
          ZMod.natCast_zmod_val, hcast, dotProduct]
      rw [hdz, hnull j]
    have hvz : v ∣ z := Nat.dvd_of_mul_dvd_mul_left hd (hv.symm ▸ hz)
    have hzero : (z : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hpv.trans hvz)
    simpa only [z, Nat.cast_sum, Nat.cast_mul, hcast, dotProduct] using hzero

private theorem binary_null_probability_le {p s m : ℕ} [Fact p.Prime] (hm : s - 1 ≤ m) :
    (uniformOn Set.univ).real {R : Fin m → Fin s → Bool |
      ∃ a : Fin s → ZMod p, a ≠ 0 ∧ ∀ j, a ⬝ᵥ binaryColumn (ZMod p) (R j) = 0} ≤
      (m.choose (s - 1) : ℝ) * (1 / 2 : ℝ) ^ (m - (s - 1)) := by
  classical
  let eval (x : Fin s → Bool) : Module.Dual (ZMod p) (Fin s → ZMod p) :=
    dotProductBilin (ZMod p) (ZMod p) (binaryColumn (ZMod p) x)
  let μ := uniformOn (Set.univ : Set (Fin s → Bool))
  let S := {a : Fin s → ZMod p | a ≠ 0}
  have hAtom (a : Fin s → ZMod p) (ha : a ∈ S) :
      μ {x | eval x a = 0} ≤ (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (by finiteness)).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    simpa [μ, Measure.real, eval, dotProduct_comm a] using
      (binary_atom_le_concentration a 0).trans (binaryConcentration_le_half ha)
  have h := measure_exists_null_vector_le (μ := μ) (m := m) eval S (fun _ ha => ha)
    hAtom (by simpa using hm)
  rw [pi_uniformOn_univ] at h
  have hdim : Module.finrank (ZMod p) (Fin s → ZMod p) = s := by simp
  rw [hdim] at h
  convert ENNReal.toReal_mono (by finiteness) h using 1
  · simp [S, eval, Measure.real, dotProduct_comm]
  · simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

private theorem fixed_support_probability_le {p N m s : ℕ} [Fact p.Prime]
    (hm : s - 1 ≤ m) (I : Finset (Fin N)) (hI : I.card = s) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool |
      ∃ a : Fin N → ZMod p, a ≠ 0 ∧ (∀ i ∉ I, a i = 0) ∧
        ∀ j, a ⬝ᵥ binaryColumn (ZMod p) (R j) = 0} ≤
      (m.choose (s - 1) : ℝ) * (1 / 2 : ℝ) ^ (m - (s - 1)) := by
  classical
  let e : Fin s ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I ▸ hI)).symm
  let f : Fin s ↪ Fin N := e.toEmbedding.trans (Function.Embedding.subtype _)
  let E := {R : Fin m → Fin s → Bool | ∃ a : Fin s → ZMod p, a ≠ 0 ∧
    ∀ j, a ⬝ᵥ binaryColumn (ZMod p) (R j) = 0}
  let g : (Fin m → Fin N → Bool) → Fin m → Fin s → Bool := fun R j i => R j (f i)
  have hRange : Set.range f = (I : Set (Fin N)) := by
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      exact (e j).2
    · intro hi
      exact ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩
  have hsub : {R : Fin m → Fin N → Bool | ∃ a : Fin N → ZMod p, a ≠ 0 ∧
        (∀ i ∉ I, a i = 0) ∧ ∀ j, a ⬝ᵥ binaryColumn (ZMod p) (R j) = 0} ⊆ g ⁻¹' E := by
    rintro R ⟨a, ha, hs, hnull⟩
    refine ⟨a ∘ f, ?_, fun j => ?_⟩
    · intro hb
      apply ha
      ext i
      by_cases hi : i ∈ I
      · have hf : i ∈ Set.range f := hRange.symm ▸ hi
        obtain ⟨j, rfl⟩ := hf
        exact congrFun hb j
      · exact hs i hi
    · unfold dotProduct
      calc
        _ = ∑ i ∈ I, a i * binaryColumn (ZMod p) (R j) i := by
          refine Finset.sum_bij (fun i _ => f i) (fun i _ => (e i).2)
            (fun _ _ _ _ h => f.injective h) ?_ (fun _ _ => rfl)
          intro b hb
          have hb' : b ∈ Set.range f := hRange.symm ▸ hb
          obtain ⟨i, rfl⟩ := hb'
          exact ⟨i, Finset.mem_univ _, rfl⟩
        _ = ∑ i, a i * binaryColumn (ZMod p) (R j) i :=
          Finset.sum_subset (f := fun i => a i * binaryColumn (ZMod p) (R j) i)
            (Finset.subset_univ I) (fun i _ hi => by rw [hs i hi, zero_mul])
        _ = 0 := hnull j
  have hLaw : (uniformOn Set.univ).real (g ⁻¹' E) = (uniformOn Set.univ).real E := by
    let row (x : Fin N → Bool) (i : Fin s) := x (f i)
    have hrow : (uniformOn (Set.univ : Set (Fin N → Bool))).map row =
        uniformOn (Set.univ : Set (Fin s → Bool)) := by
      simpa only [pi_uniformOn_univ] using
        pi_map_restrict_embedding (uniformOn (Set.univ : Set Bool)) f
    have hg : (uniformOn (Set.univ : Set (Fin m → Fin N → Bool))).map g =
        uniformOn (Set.univ : Set (Fin m → Fin s → Bool)) := by
      rw [← pi_uniformOn_univ (ι := Fin m) (Ω := Fin N → Bool)]
      change (Measure.pi (fun _ : Fin m => uniformOn (Set.univ : Set (Fin N → Bool)))).map
        (fun R j => row (R j)) = _
      rw [Measure.pi_map_pi (fun _ => (measurable_of_finite row).aemeasurable)]
      simp only [hrow, pi_uniformOn_univ]
    simp only [measureReal_def]
    rw [← Measure.map_apply (measurable_of_finite g) (Set.toFinite E).measurableSet, hg]
  exact (measureReal_mono hsub).trans (hLaw.trans_le (binary_null_probability_le hm))

/-- A sparse null vector modulo a composite modulus can be detected at one of its
prime factors and on one support of the prescribed size. -/
theorem sparseBinaryNormal_probability_le {q N m s : ℕ} [NeZero q]
    (hs : s ≤ N) (hm : s - 1 ≤ m) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool | hasSparseBinaryNormal q N m s R} ≤
      (q.primeFactors.card : ℝ) * (N.choose s : ℝ) *
        ((m.choose (s - 1) : ℝ) * (1 / 2 : ℝ) ^ (m - (s - 1))) := by
  classical
  let μ := uniformOn (Set.univ : Set (Fin m → Fin N → Bool))
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let supports := (Finset.univ : Finset (Fin N)).powersetCard s
  let E (p : ℕ) (I : Finset (Fin N)) :=
    {R : Fin m → Fin N → Bool | ∃ a : Fin N → ZMod p, a ≠ 0 ∧
      (∀ i ∉ I, a i = 0) ∧ ∀ j, a ⬝ᵥ binaryColumn (ZMod p) (R j) = 0}
  have hcover : {R : Fin m → Fin N → Bool | hasSparseBinaryNormal q N m s R} ⊆
      ⋃ p ∈ q.primeFactors, ⋃ I ∈ supports, E p I := by
    intro R hR
    obtain ⟨p, hp, a, ha, hsize, hnull⟩ := exists_prime_sparse_normal hR
    let S := Finset.univ.filter (fun i => a i ≠ 0)
    obtain ⟨I, hSI, hI, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ S) hsize (by simpa using hs)
    refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, Set.mem_iUnion.mpr ⟨I,
      Set.mem_iUnion.mpr ⟨Finset.mem_powersetCard.mpr ⟨hI, hcard⟩, a, ha, ?_, hnull⟩⟩⟩⟩
    intro i hi
    have hn : i ∉ S := fun ht => hi (hSI ht)
    simpa [S] using hn
  have hprob (p : ℕ) (hp : p ∈ q.primeFactors) (I : Finset (Fin N)) (hI : I ∈ supports) :
      μ.real (E p I) ≤ (m.choose (s - 1) : ℝ) * (1 / 2 : ℝ) ^ (m - (s - 1)) := by
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact fixed_support_probability_le hm I (Finset.mem_powersetCard.mp hI).2
  have hcard : supports.card = N.choose s := by
    simp [supports, Finset.card_powersetCard]
  calc
    _ ≤ μ.real (⋃ p ∈ q.primeFactors, ⋃ I ∈ supports, E p I) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ p ∈ q.primeFactors, μ.real (⋃ I ∈ supports, E p I) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, ∑ I ∈ supports, μ.real (E p I) :=
      Finset.sum_le_sum fun p _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ q.primeFactors, ∑ _I ∈ supports,
        (m.choose (s - 1) : ℝ) * (1 / 2 : ℝ) ^ (m - (s - 1)) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun I hI => hprob p hp I hI
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard, mul_assoc]

private theorem choose_le_scaled_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (16 : ℝ) ^ k * (17 / 16 : ℝ) ^ n := by
  by_cases hk : k ≤ n
  · have hsum : (∑ i ∈ Finset.range (n + 1), (1 / 16 : ℝ) ^ i * (n.choose i : ℝ)) =
        (17 / 16 : ℝ) ^ n := by
      have h := add_pow (1 / 16 : ℝ) 1 n
      norm_num only [one_pow, mul_one] at h
      convert h.symm using 1
    have ht := Finset.single_le_sum (f := fun i => (1 / 16 : ℝ) ^ i * (n.choose i : ℝ))
      (fun i _ => mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    rw [hsum] at ht
    calc
      _ = (16 : ℝ) ^ k * ((1 / 16 : ℝ) ^ k * (n.choose k : ℝ)) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk), Nat.cast_zero]
    positivity

/-- With at least half the columns exposed, the probability of a nonzero null vector
on at most a 1/128 fraction of the coordinates is exponentially small. -/
theorem sparseBinaryNormal_probability_geometric {q N m : ℕ} [NeZero q]
    (hm : m ≤ N) (hNm : N ≤ 2 * m) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool |
      hasSparseBinaryNormal q N m (N / 128) R} ≤
      (q.primeFactors.card : ℝ) * (14739 / 16384 : ℝ) ^ N := by
  let s := N / 128
  have hs : s ≤ N := Nat.div_le_self _ _
  have hsm : s - 1 ≤ m := by dsimp [s]; omega
  apply (sparseBinaryNormal_probability_le hs hsm).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let b : ℝ := 17 / 16
  have hmPow : b ^ m ≤ b ^ N := pow_le_pow_right₀ (by norm_num [b]) hm
  have hsPow : (16 : ℝ) ^ (s - 1) ≤ (16 : ℝ) ^ s :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hchoose : (m.choose (s - 1) : ℝ) ≤ (16 : ℝ) ^ s * b ^ N :=
    (choose_le_scaled_pow _ _).trans
      (mul_le_mul hsPow hmPow (by positivity) (by positivity))
  have hhalf : (1 / 2 : ℝ) ^ m ≤ (3 / 4 : ℝ) ^ N := by
    calc
      _ ≤ ((3 / 4 : ℝ) ^ 2) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (3 / 4 : ℝ) ^ (2 * m) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hNm
  have hfail : (1 / 2 : ℝ) ^ (m - (s - 1)) ≤ (2 : ℝ) ^ s * (3 / 4 : ℝ) ^ N := by
    calc
      _ = (2 : ℝ) ^ (s - 1) * (1 / 2 : ℝ) ^ m := by
        conv_rhs => rw [← Nat.sub_add_cancel hsm, pow_add, mul_left_comm, ← mul_pow]
        norm_num
      _ ≤ _ := mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
        hhalf (by positivity) (by positivity)
  have hweight : (512 : ℝ) ^ s ≤ b ^ N := by
    calc
      _ ≤ (b ^ 128) ^ s := pow_le_pow_left₀ (by norm_num) (by norm_num [b]) _
      _ = b ^ (128 * s) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num [b]) (by dsimp [s]; omega)
  calc
    _ ≤ ((16 : ℝ) ^ s * b ^ N) * (((16 : ℝ) ^ s * b ^ N) *
        ((2 : ℝ) ^ s * (3 / 4 : ℝ) ^ N)) := by
      exact mul_le_mul (choose_le_scaled_pow N s)
        (mul_le_mul hchoose hfail (by positivity) (by positivity)) (by positivity) (by positivity)
    _ = (512 : ℝ) ^ s * (b ^ N * b ^ N * (3 / 4 : ℝ) ^ N) := by
      rw [show (512 : ℝ) = 16 * 16 * 2 by norm_num, mul_pow, mul_pow]
      ring
    _ ≤ b ^ N * (b ^ N * b ^ N * (3 / 4 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      norm_num [b]

end BooleanThreshold
