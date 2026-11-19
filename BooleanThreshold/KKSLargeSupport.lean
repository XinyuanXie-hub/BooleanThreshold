module

public import BooleanThreshold.KKSLargeHalasz
public import BooleanThreshold.SpanSmallRelations

public section

open Filter Finset MeasureTheory
open scoped ENNReal BigOperators Classical

namespace BooleanThreshold

/-- The large-support case of Kahn–Komlós–Szemerédi, with the exponential
constant used in the small-relation estimate. -/
theorem kks_large_support_atom_bound :
    ∃ η > (0 : ℝ), ∃ s₀ : ℕ, ∀ᶠ n : ℕ in atTop,
      (signLaw n n).real
        (largeSupportAtomNull n s₀ (ENNReal.ofReal (Real.exp (-η * (n : ℝ))))) ≤
        (1 / 8 : ℝ) ^ n := by
  let τ : ℝ := 1 / 8192
  have hτ : 0 < τ := by norm_num [τ]
  obtain ⟨μ, hμ, hμhalf, K, hcompare⟩ := exists_lazy_atom_comparison_int hτ
  let _ := lazyCoordinateLaw_probability hμ.le (by linarith : μ ≤ 1)
  let b := 1 - μ
  have hb₀ : 0 < b := by dsimp [b]; linarith
  have hb₁ : b < 1 := by dsimp [b]; linarith
  let η := -Real.log b / 4
  have hη : 0 < η := by dsimp [η]; linarith [Real.log_neg hb₀ hb₁]
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log 2 / η)
  refine ⟨η, hη, K, eventually_atTop.mpr ⟨max N 6, fun n hn => ?_⟩⟩
  let d := n / 2
  let q := ENNReal.ofReal (Real.exp (-η * (n : ℝ)))
  let S : Set (Fin n → ℝ) := {a | ∃ z : Fin n → ℤ,
    (fun i => (z i : ℝ)) = a ∧
      K < (univ.filter fun i => z i ≠ 0).card ∧ q < zeroAtom a}
  have hS (a : Fin n → ℝ) (ha : a ∈ S) : a ≠ 0 := by
    obtain ⟨z, rfl, hk, _⟩ := ha
    obtain ⟨i, hi⟩ := card_pos.mp (Nat.zero_le K |>.trans_lt hk)
    intro hz
    have hc := congrFun hz i
    change (z i : ℝ) = 0 at hc
    exact (mem_filter.mp hi).2 (by exact_mod_cast hc)
  have hcut (a : Fin n → ℝ) (ha : a ∈ S) : q < zeroAtom a := by
    obtain ⟨_, _, _, h⟩ := ha
    exact h
  have hkeep (a : Fin n → ℝ) (ha : a ∈ S) :
      zeroAtom a ≤ ENNReal.ofReal τ * auxiliaryAtom (lazyCoordinateLaw μ) lazyBitEmbedding a := by
    obtain ⟨z, rfl, hk, _⟩ := ha
    exact hcompare n z hk
  have hn₆ : 6 ≤ n := (le_max_right _ _).trans hn
  have hd : d < n := by dsimp [d]; omega
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left N 6).trans hn
  have hqhalf : Real.exp (-η * (n : ℝ)) ≤ 1 / 2 := by
    have hh := (div_le_iff₀ hη).mp (hN.trans hnN)
    have he := Real.exp_le_exp.mpr (show -η * (n : ℝ) ≤ -Real.log 2 by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div] at he
  have hlog : ((n - d : ℕ) : ℝ) * Real.log b ≤ -2 * η * (n : ℝ) := by
    have h : (n : ℝ) / 2 ≤ ((n - d : ℕ) : ℝ) := by
      have hh : n ≤ 2 * (n - d) := by dsimp [d]; omega
      have hhR : (n : ℝ) ≤ 2 * ((n - d : ℕ) : ℝ) := by exact_mod_cast hh
      linarith
    calc
      _ ≤ ((n : ℝ) / 2) * Real.log b :=
        mul_le_mul_of_nonpos_right h (Real.log_neg hb₀ hb₁).le
      _ = _ := by dsimp [η]; ring
  have hprojR : b ^ (n - d) ≤ Real.exp (-η * (n : ℝ)) := by
    calc
      _ = Real.exp (((n - d : ℕ) : ℝ) * Real.log b) := by
        rw [Real.exp_nat_mul, Real.exp_log hb₀]
      _ ≤ Real.exp (-2 * η * (n : ℝ)) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (-η * (n : ℝ)) * Real.exp (-η * (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_of_le_one_right (Real.exp_nonneg _) (hqhalf.trans (by norm_num))
  have hT₀ : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.mpr hτ).ne'
  have h2T : (2 : ℝ≥0∞) * ENNReal.ofReal τ ≤ 1 := by
    calc
      _ = ENNReal.ofReal (2 * τ) := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by norm_num [τ])
      _ = _ := ENNReal.ofReal_one
  have hproj : (ENNReal.ofReal b) ^ (n - d) ≤ q / (2 * ENNReal.ofReal τ) := by
    refine ((ENNReal.ofReal_pow hb₀.le _).symm.le.trans (ENNReal.ofReal_le_ofReal hprojR)).trans ?_
    apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero (by simp) hT₀))
      (Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))).mpr
    exact (mul_le_mul' le_rfl h2T).trans_eq (mul_one _)
  have hν (x : Fin 3) : lazyCoordinateLaw μ {x} ≤ ENNReal.ofReal b :=
    lazyCoordinateLaw_atom_le hμhalf x
  have hprob := signLaw_null_set_le_of_auxiliary_atom_comparison hd
    (lazyCoordinateLaw μ) lazyBitEmbedding ((ENNReal.ofReal_le_ofReal hb₁.le).trans_eq ENNReal.ofReal_one)
    hν hT₀ ENNReal.ofReal_ne_top S hS hcut hkeep hproj
  have heq : {v : Fin n → Fin n → ℝ | ∃ a ∈ S, ∀ j, ∑ i, a i * v i j = 0} =
      largeSupportAtomNull n K q := by
    ext v
    constructor
    · rintro ⟨a, ⟨z, rfl, hk, ha⟩, hnull⟩
      exact ⟨z, hk, ha, hnull⟩
    · rintro ⟨z, hk, hz, hnull⟩
      exact ⟨_, ⟨z, rfl, hk, hz⟩, hnull⟩
  rw [heq] at hprob
  have hFin : (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal τ) ^ d ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
  have hprobR : (signLaw n n).real (largeSupportAtomNull n K q) ≤
      (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 * τ) ^ d := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hτ.le] using ENNReal.toReal_mono hFin hprob
  have hdecay : (2 * τ) ^ d ≤ 64 * (1 / 64 : ℝ) ^ n := by
    calc
      _ = (1 / 64 : ℝ) ^ (2 * d) := by rw [pow_mul]; norm_num [τ]
      _ = 64 * (1 / 64 : ℝ) ^ (2 * d + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by dsimp [d]; omega)) (by positivity)
  have h64 : (64 : ℝ) ≤ 2 ^ n := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num]
    exact pow_le_pow_right₀ (by norm_num) hn₆
  calc
    _ ≤ _ := hprobR
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (64 * (1 / 64 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = 64 * (1 / 16 : ℝ) ^ n := by
      rw [mul_left_comm ((2 : ℝ) ^ n * 2 ^ n), ← mul_pow, ← mul_pow]
      norm_num
    _ ≤ (2 : ℝ) ^ n * (1 / 16 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right h64 (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

end BooleanThreshold
