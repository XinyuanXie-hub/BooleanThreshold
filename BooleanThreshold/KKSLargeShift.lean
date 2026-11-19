module

public import BooleanThreshold.KKSLargeShiftBounds
public import BooleanThreshold.SpanRelations
public import BooleanThreshold.Asymptotics

public section

open Filter Finset MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix Classical

namespace BooleanThreshold

private theorem shiftedSignNull_largeSupport_le :
    ∃ η > (0 : ℝ), ∃ K : ℕ, ∀ n ≥ 6, ∀ D : Fin n → Fin n → ℤ,
      (uniformOn Set.univ).real
        {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℤ,
          K < (univ.filter fun j => a j ≠ 0).card ∧
          ENNReal.ofReal (Real.exp (-η * (n : ℝ))) < shiftedSignRowAtom D (fun j => (a j : ℝ)) ∧
          ∀ i, shiftedSignEval D i (X i) (fun j => (a j : ℝ)) = 0}
        ≤ (1 / 8 : ℝ) ^ n := by
  let τ : ℝ := 1 / 8192
  have hτ : 0 < τ := by norm_num [τ]
  obtain ⟨μ, hμ, hμhalf, K, hcompare⟩ := exists_lazy_integer_target_comparison hτ
  let _ := lazyCoordinateLaw_probability hμ.le (by linarith : μ ≤ 1)
  let b := 1 - μ
  have hb : 0 < b ∧ b < 1 := by dsimp [b]; constructor <;> linarith
  let η := -Real.log b / 4
  have hlog : Real.log b < 0 := Real.log_neg hb.1 hb.2
  have hη : 0 < η := by dsimp [η]; linarith
  refine ⟨η, hη, K, fun n hn D => ?_⟩
  let d := n / 2
  let q := ENNReal.ofReal (Real.exp (-η * (n : ℝ)))
  let S : Set (Fin n → ℝ) := {a | ∃ z : Fin n → ℤ, (fun j => (z j : ℝ)) = a ∧
    K < (univ.filter fun j => z j ≠ 0).card ∧ q < shiftedSignRowAtom D a}
  have hS (a : Fin n → ℝ) (ha : a ∈ S) : a ≠ 0 := by
    obtain ⟨z, rfl, hk, _⟩ := ha
    obtain ⟨j, hj⟩ := card_pos.mp ((Nat.zero_le K).trans_lt hk)
    intro hz
    have hc := congrFun hz j
    change (z j : ℝ) = 0 at hc
    exact (mem_filter.mp hj).2 (by exact_mod_cast hc)
  have hkeep (a : Fin n → ℝ) (ha : a ∈ S) :
      shiftedSignRowAtom D a ≤
        ENNReal.ofReal τ * auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding a := by
    obtain ⟨z, rfl, hk, _⟩ := ha
    exact shiftedSignRowAtom_le_auxiliary D z (hcompare n z hk)
  have hcut (a : Fin n → ℝ) (ha : a ∈ S) : q < shiftedSignRowAtom D a := by
    obtain ⟨_, _, _, h⟩ := ha
    exact h
  have hd : d < n := by dsimp [d]; omega
  have hquarter : (n : ℝ) / 4 ≤ ((n - d : ℕ) : ℝ) := by
    have hh : n ≤ 2 * (n - d) := by dsimp [d]; omega
    have hhR : (n : ℝ) ≤ 2 * ((n - d : ℕ) : ℝ) := by exact_mod_cast hh
    linarith
  have hprojR : b ^ (n - d) ≤ Real.exp (-η * (n : ℝ)) := by
    calc
      _ = Real.exp (((n - d : ℕ) : ℝ) * Real.log b) := by
        rw [Real.exp_nat_mul, Real.exp_log hb.1]
      _ ≤ Real.exp (((n : ℝ) / 4) * Real.log b) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hquarter hlog.le)
      _ = _ := by congr 1; dsimp [η]; ring
  have hT₀ : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.mpr hτ).ne'
  have h2T : (2 : ℝ≥0∞) * ENNReal.ofReal τ ≤ 1 := by
    calc
      _ = ENNReal.ofReal (2 * τ) := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by norm_num [τ])
      _ = _ := ENNReal.ofReal_one
  have hproj : (ENNReal.ofReal b) ^ (n - d) ≤ q / (2 * ENNReal.ofReal τ) := by
    refine ((ENNReal.ofReal_pow hb.1.le _).symm.le.trans (ENNReal.ofReal_le_ofReal hprojR)).trans ?_
    apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (by simp) hT₀))
      (Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))).mpr
    exact (mul_le_mul' le_rfl h2T).trans_eq (mul_one _)
  have hprob := uniform_null_set_le_of_auxiliary_atom_comparison hd
    (lazyCoordinateLaw μ) lazyBitEmbedding ((ENNReal.ofReal_le_ofReal hb.2.le).trans_eq ENNReal.ofReal_one)
    (lazyCoordinateLaw_atom_le hμhalf) hT₀ ENNReal.ofReal_ne_top (shiftedSignEval D) S hS
    (shiftedSignRowAtom D)
    (fun a _ => shiftedSignRowAtom_card_ratio (by omega) D a) (fun i a _ => shiftedSignRowAtom_ge D i a)
    hcut hkeep hproj
  have heq : {X : Fin n → Fin n → Bool | ∃ a ∈ S, ∀ i, shiftedSignEval D i (X i) a = 0} =
      {X | ∃ a : Fin n → ℤ, K < (univ.filter fun j => a j ≠ 0).card ∧
        q < shiftedSignRowAtom D (fun j => (a j : ℝ)) ∧
        ∀ i, shiftedSignEval D i (X i) (fun j => (a j : ℝ)) = 0} := by
    ext X
    constructor
    · rintro ⟨a, ⟨z, rfl, hk, ha⟩, hnull⟩
      exact ⟨z, hk, ha, hnull⟩
    · rintro ⟨z, hk, hz, hnull⟩
      exact ⟨_, ⟨z, rfl, hk, hz⟩, hnull⟩
  rw [heq] at hprob
  have hFin : (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal τ) ^ d ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
  have hprobR := ENNReal.toReal_mono hFin hprob
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hτ.le] at hprobR
  have hdecay : (2 * τ) ^ d ≤ 64 * (1 / 64 : ℝ) ^ n := by
    calc
      _ = (1 / 64 : ℝ) ^ (2 * d) := by rw [pow_mul]; norm_num [τ]
      _ = 64 * (1 / 64 : ℝ) ^ (2 * d + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by dsimp [d]; omega)) (by positivity)
  have h64 : (64 : ℝ) ≤ 2 ^ n := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num]
    exact pow_le_pow_right₀ (by norm_num) hn
  calc
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 * τ) ^ d := hprobR
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (64 * (1 / 64 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = 64 * (1 / 16 : ℝ) ^ n := by
      rw [mul_left_comm ((2 : ℝ) ^ n * 2 ^ n), ← mul_pow, ← mul_pow]
      norm_num
    _ ≤ (2 : ℝ) ^ n * (1 / 16 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right h64 (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

private theorem shiftedSignNull_integer_witness {n : ℕ} (D : Fin n → Fin n → ℤ)
    (X : Fin n → Fin n → Bool) (a : Fin n → ℝ) (ha : a ≠ 0)
    (hnull : ∀ i, ∑ j, a j * (realSigns (X i) j + (D i j : ℝ)) = 0) :
    ∃ z : Fin n → ℤ, z ≠ 0 ∧ ∀ i, shiftedSignEval D i (X i) (fun j => (z j : ℝ)) = 0 := by
  let A : Matrix (Fin n) (Fin n) ℤ := fun i j => signedBit (X i j) + D i j
  have hcast (i j : Fin n) : (A i j : ℝ) = realSigns (X i) j + (D i j : ℝ) := by
    dsimp [A]
    push_cast
    cases h : X i j <;> norm_num [realSigns, signedBit, h]
  have hA : ¬ LinearIndependent ℝ (fun j i => (A i j : ℝ)) := by
    intro h
    have hsum : (∑ j, a j • (fun i => (A i j : ℝ))) = 0 := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hcast]
      exact hnull i
    exact ha (funext (Fintype.linearIndependent_iff.mp h a hsum))
  obtain ⟨z, hz, c, hc⟩ := exists_primitive_int_relation A hA
  refine ⟨z, ?_, fun i => ?_⟩
  · intro h
    simp [h, dotProduct] at hc
  · have hi : (∑ j, A i j * z j) = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using congrFun hz i
    have hi' := congrArg (fun k : ℤ => (k : ℝ)) hi
    push_cast at hi'
    rw [shiftedSignEval_apply]
    simpa only [hcast, mul_comm] using hi'

private theorem polynomial_mul_exp_le (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ k * Real.exp (-η * (n : ℝ)) ≤
      C * Real.exp (-(η / 2) * (n : ℝ)) := by
  obtain ⟨C, hC, h⟩ := exp_neg_nat_mul_le_inv_pow k (half_pos hη)
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show n > 0 by omega)
  have hgain := (le_div_iff₀ (pow_pos hn₀ k)).mp (h n hn)
  rw [show Real.exp (-η * (n : ℝ)) =
    Real.exp (-(η / 2) * (n : ℝ)) * Real.exp (-(η / 2) * (n : ℝ)) by
      rw [← Real.exp_add]; congr 1; ring, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hgain) (Real.exp_nonneg _)

private theorem shiftedSignNull_smallSupport_real_le {n K : ℕ} (hK : K ≤ n)
    (D : Fin n → Fin n → ℤ) :
    (uniformOn Set.univ).real
        {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℝ,
          a ≠ 0 ∧ (univ.filter fun j => a j ≠ 0).card ≤ K ∧
          ∀ i, shiftedSignEval D i (X i) a = 0}
      ≤ (2 : ℝ) ^ (K - 1) * ((n : ℝ) ^ (K + (K - 1)) * Real.exp (-Real.log 2 * (n : ℝ))) := by
  have hFinite : (n.choose K : ℝ≥0∞) * (n.choose (K - 1) : ℝ≥0∞) *
      (1 / 2) ^ (n - (K - 1)) ≠ ⊤ := by finiteness
  have h := ENNReal.toReal_mono hFinite (shiftedSignNull_smallSupport_le hK D)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
  let m := K - 1
  have hm : m ≤ n := (Nat.sub_le _ _).trans hK
  have hpow : (1 / 2 : ℝ) ^ (n - m) = (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n := by
    calc
      _ = (1 / 2 : ℝ) ^ (n - m) * (2 * (1 / 2 : ℝ)) ^ m := by norm_num
      _ = (2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ (n - m) * (1 / 2 : ℝ) ^ m) := by rw [mul_pow]; ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hExp : (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2 * (n : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div]
  calc
    _ ≤ (n.choose K : ℝ) * (n.choose m : ℝ) * (1 / 2 : ℝ) ^ (n - m) := h
    _ ≤ (n : ℝ) ^ K * (n : ℝ) ^ m * (1 / 2 : ℝ) ^ (n - m) := by
      gcongr
      · exact_mod_cast Nat.choose_le_pow n K
      · exact_mod_cast Nat.choose_le_pow n m
    _ = _ := by rw [hpow, hExp, ← pow_add]; ring

/-- A square matrix of independent signs with arbitrary deterministic integer
shifts is singular with uniformly exponentially small probability. -/
theorem kks_shifted_sign_singularity :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ D : Fin n → Fin n → ℤ,
      (uniformOn Set.univ).real
        {X : Fin n → Fin n → Bool | ∃ a : Fin n → ℝ, a ≠ 0 ∧
          ∀ i, ∑ j, a j * (realSigns (X i) j + (D i j : ℝ)) = 0}
        ≤ C * Real.exp (-c * (n : ℝ)) := by
  obtain ⟨η, hη, K, hLarge⟩ := shiftedSignNull_largeSupport_le
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Cs, hCs, hSparse⟩ := polynomial_mul_exp_le (K + (K - 1)) hlog
  obtain ⟨Cl, hCl, hLow⟩ := polynomial_mul_exp_le 1 hη
  let c := min (Real.log 2 / 2) (η / 2)
  let Cs' := (2 : ℝ) ^ (K - 1) * Cs
  refine ⟨c, lt_min (half_pos hlog) (half_pos hη), Cs' + Cl + 1, by positivity,
    eventually_atTop.mpr ⟨max K 6, fun n hn D => ?_⟩⟩
  have hn₆ : 6 ≤ n := (le_max_right K 6).trans hn
  have hKn : K ≤ n := (le_max_left K 6).trans hn
  have hn₁ : 1 ≤ n := by omega
  let q := ENNReal.ofReal (Real.exp (-η * (n : ℝ)))
  let E : Set (Fin n → Fin n → Bool) := {X | ∃ a : Fin n → ℝ, a ≠ 0 ∧
    ∀ i, ∑ j, a j * (realSigns (X i) j + (D i j : ℝ)) = 0}
  let Sparse : Set (Fin n → Fin n → Bool) := {X | ∃ a : Fin n → ℝ,
    a ≠ 0 ∧ (univ.filter fun j => a j ≠ 0).card ≤ K ∧ ∀ i, shiftedSignEval D i (X i) a = 0}
  let Low : Set (Fin n → Fin n → Bool) := {X | ∃ a : Fin n → ℝ,
    a ≠ 0 ∧ shiftedSignRowAtom D a ≤ q ∧ ∀ i, shiftedSignEval D i (X i) a = 0}
  let Large : Set (Fin n → Fin n → Bool) := {X | ∃ a : Fin n → ℤ,
    K < (univ.filter fun j => a j ≠ 0).card ∧
    q < shiftedSignRowAtom D (fun j => (a j : ℝ)) ∧
    ∀ i, shiftedSignEval D i (X i) (fun j => (a j : ℝ)) = 0}
  let ν : Measure (Fin n → Fin n → Bool) := uniformOn Set.univ
  have hsubset : E ⊆ (Sparse ∪ Low) ∪ Large := by
    rintro X ⟨a, ha, hnull⟩
    obtain ⟨z, hz, hznull⟩ := shiftedSignNull_integer_witness D X a ha hnull
    let w (j : Fin n) : ℝ := z j
    have hw : w ≠ 0 := by
      intro h
      apply hz
      funext j
      have hj := congrFun h j
      change (z j : ℝ) = 0 at hj
      exact_mod_cast hj
    have hcard : (univ.filter fun j => w j ≠ 0) = univ.filter fun j => z j ≠ 0 := by
      ext j
      simp [w]
    by_cases hs : (univ.filter fun j => z j ≠ 0).card ≤ K
    · exact Or.inl (Or.inl ⟨w, hw, hcard.symm ▸ hs, hznull⟩)
    by_cases hq : shiftedSignRowAtom D w ≤ q
    · exact Or.inl (Or.inr ⟨w, hw, hq, hznull⟩)
    exact Or.inr ⟨z, lt_of_not_ge hs, lt_of_not_ge hq, hznull⟩
  have hs : ν.real Sparse ≤ Cs' * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
    refine (shiftedSignNull_smallSupport_real_le hKn D).trans ?_
    dsimp [Cs']
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hSparse n hn₁) (by positivity)
  have hl : ν.real Low ≤ Cl * Real.exp (-(η / 2) * (n : ℝ)) := by
    have h := ENNReal.toReal_mono (by dsimp [q]; finiteness : (n : ℝ≥0∞) * q ≠ ⊤)
      (shiftedSignNull_low_le (by omega) D q)
    have h' : ν.real Low ≤ (n : ℝ) * Real.exp (-η * (n : ℝ)) := by
      simpa only [ν, Low, measureReal_def, q, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
    simpa only [pow_one] using h'.trans (by simpa only [pow_one] using hLow n hn₁)
  have hh : ν.real Large ≤ Real.exp (-Real.log 2 * (n : ℝ)) := by
    calc
      _ ≤ (1 / 8 : ℝ) ^ n := hLarge n hn₆ D
      _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = _ := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div]
  have hexp {r : ℝ} (hr : c ≤ r) : Real.exp (-r * (n : ℝ)) ≤ Real.exp (-c * (n : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hr) (by positivity))
  have hcs : c ≤ Real.log 2 / 2 := min_le_left _ _
  have hcl : c ≤ η / 2 := min_le_right _ _
  change ν.real E ≤ _
  calc
    _ ≤ ν.real ((Sparse ∪ Low) ∪ Large) := measureReal_mono hsubset
    _ ≤ (ν.real Sparse + ν.real Low) + ν.real Large :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ (Cs' * Real.exp (-c * (n : ℝ)) + Cl * Real.exp (-c * (n : ℝ))) +
        Real.exp (-c * (n : ℝ)) :=
      add_le_add (add_le_add
        (hs.trans (mul_le_mul_of_nonneg_left (hexp hcs) (by positivity)))
        (hl.trans (mul_le_mul_of_nonneg_left (hexp hcl) hCl.le)))
        (hh.trans (hexp (hcs.trans (by linarith))))
    _ = _ := by ring

end BooleanThreshold
