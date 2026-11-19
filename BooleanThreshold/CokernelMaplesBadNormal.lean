module

public import BooleanThreshold.BinaryAlphabetCount
public import BooleanThreshold.CokernelMaplesHighConcentration
public import BooleanThreshold.CokernelMaplesModulus
public import BooleanThreshold.CokernelMaplesPrefix

public noncomputable section

open Matrix MeasureTheory ProbabilityTheory Function
open scoped BigOperators Classical Matrix

namespace BooleanThreshold

/-- Failure of the Fourier bound for the span of the exposed columns. -/
@[expose] def HasLargeBinaryFourierNormal {q n m : ℕ} [NeZero q] (ε : ℝ)
    (R : Fin m → Fin n → Bool) : Prop :=
  ∃ a : Fin n → ZMod q, a ≠ 0 ∧ ε ≤ (∏ i, ‖bitFourierCoefficient (a i)‖) ∧
    ∀ j, a ⬝ᵥ binaryColumn (ZMod q) (R j) = 0

theorem bad_prefix_Fourier_probability_le {q n m : ℕ} [NeZero q] {ε β : ℝ} (hβ : 0 ≤ β)
    (hsmall : ∀ r ∈ q.divisors, ∀ [NeZero r],
      (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
        ∃ a : Fin n → ZMod r, n / 128 < (Finset.univ.filter fun i => a i ≠ 0).card ∧
          ε ≤ (∏ i, ‖bitFourierCoefficient (a i)‖) ∧ binaryZeroAtom a ≤ 16 / (r : ℝ) ∧
          ∀ j, a ⬝ᵥ binaryColumn (ZMod r) (R j) = 0} ≤ β)
    (hlarge : ∀ r ∈ q.divisors,
      (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
        ∃ a : Fin n → ZMod r, DenseCyclicNormal a ∧ 16 / (r : ℝ) < binaryZeroAtom a ∧
          ∀ j, a ⬝ᵥ binaryColumn (ZMod r) (R j) = 0} ≤ β) :
    (uniformOn Set.univ).real {R : Fin m → Fin n → Bool | HasLargeBinaryFourierNormal (q := q) ε R} ≤
      (uniformOn Set.univ).real {R : Fin m → Fin n → Bool | hasSparseBinaryNormal q n m (n / 128) R} +
        2 * (q : ℝ) * β := by
  let Ω := Fin m → Fin n → Bool
  let μ : Measure Ω := uniformOn Set.univ
  let S : Set Ω := {R | hasSparseBinaryNormal q n m (n / 128) R}
  let (r : q.divisors) : NeZero r.val := ⟨(Nat.pos_of_mem_divisors r.2).ne'⟩
  let A (r : q.divisors) : Set Ω := {R | ∃ a : Fin n → ZMod r.val,
    n / 128 < (Finset.univ.filter fun i => a i ≠ 0).card ∧
      ε ≤ (∏ i, ‖bitFourierCoefficient (a i)‖) ∧ binaryZeroAtom a ≤ 16 / (r.val : ℝ) ∧
      ∀ j, a ⬝ᵥ binaryColumn (ZMod r.val) (R j) = 0}
  let B (r : q.divisors) : Set Ω := {R | ∃ a : Fin n → ZMod r.val,
    DenseCyclicNormal a ∧ 16 / (r.val : ℝ) < binaryZeroAtom a ∧
      ∀ j, a ⬝ᵥ binaryColumn (ZMod r.val) (R j) = 0}
  have hsubset : {R : Ω | HasLargeBinaryFourierNormal (q := q) ε R} ⊆
      S ∪ (⋃ r : q.divisors, A r ∪ B r) := by
    intro R hR
    by_cases hS : R ∈ S
    · exact Or.inl hS
    obtain ⟨a, ha, haf, hzero⟩ := hR
    obtain ⟨r, d, h, hr, b, hab, hsurj⟩ := exists_surjective_divisor_normal ha
    have hdiv : r ∣ q := h ▸ dvd_mul_left r d
    have hrmem := Nat.mem_divisors.mpr ⟨hdiv, NeZero.ne q⟩
    let u : q.divisors := ⟨r, hrmem⟩
    let : NeZero r := ⟨by omega⟩
    have hzero' (j : Fin m) : b ⬝ᵥ binaryColumn (ZMod r) (R j) = 0 :=
      (divisorModulusEmbedding_binary_dotProduct_eq_zero_iff h b (R j)).mp (hab ▸ hzero j)
    refine Or.inr (Set.mem_iUnion.mpr ⟨u, ?_⟩)
    by_cases hbound : binaryZeroAtom b ≤ 16 / (r : ℝ)
    · apply Or.inl
      have hsupp : n / 128 < (Finset.univ.filter fun i => b i ≠ 0).card := by
        by_contra! hbad
        apply hS
        exact ⟨a, ha, by rwa [hab, divisorModulusEmbedding_support], hzero⟩
      have hf : ε ≤ (∏ i, ‖bitFourierCoefficient (b i)‖) := by
        rwa [hab, divisorModulusEmbedding_fourier_product] at haf
      exact ⟨b, hsupp, hf, hbound, hzero'⟩
    · apply Or.inr
      refine ⟨b, ?_, lt_of_not_ge hbound, hzero'⟩
      intro p hp hpdiv
      by_contra! hbad
      apply hS
      exact hasSparseBinaryNormal_of_dvd (hpdiv.trans hdiv)
        ⟨fun i => ZMod.castHom hpdiv (ZMod p) (b i),
          surjective_dotProduct_nonzero_mod_prime hp hpdiv hsurj, hbad,
          fun j => reduced_normal_dotProduct_eq_zero hpdiv (hzero' j)⟩
  calc
    _ ≤ μ.real (S ∪ (⋃ r : q.divisors, A r ∪ B r)) := measureReal_mono hsubset
    _ ≤ μ.real S + ∑ r : q.divisors, μ.real (A r ∪ B r) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_iUnion_fintype_le _))
    _ ≤ μ.real S + ∑ _r : q.divisors, 2 * β := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro r _
      rw [two_mul]
      exact (measureReal_union_le _ _).trans (add_le_add (hsmall r.val r.2) (hlarge r.val r.2))
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
      apply add_le_add le_rfl
      calc
        _ ≤ (q : ℝ) * (2 * β) := mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (Nat.card_divisors_le_self q)) (by positivity)
        _ = _ := by ring

/-- For a full-rank prefix, the Fourier bound gives uniform point probabilities
on the projected quotient up to the given error. -/
theorem projected_binary_probability_abs_sub_le {q n m k : ℕ} [NeZero q]
    {R : Fin m → Fin n → Bool} {ε : ℝ} (hε : 0 ≤ ε)
    (hR : ¬ HasLargeBinaryFourierNormal (q := q) ε R)
    (P : (Fin n → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q))
    (hP : Surjective P)
    (hker : LinearMap.ker P =
      LinearMap.range (((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))).mulVecLin))
    (y : Fin k → ZMod q) :
    |finiteEventProbability (fun x : Fin n → Bool => P (binaryColumn (ZMod q) x) = y) -
      1 / (q : ℝ) ^ k| ≤ ε := by
  let V := LinearMap.ker P
  let e := LinearMap.quotKerEquivOfSurjective P hP
  have hcard : (Nat.card ((Fin n → ZMod q) ⧸ V) : ℝ) = (q : ℝ) ^ k := by
    rw [Nat.card_congr e.toEquiv]
    simp [ZMod.card]
  have hcoeff (a : Fin n → ZMod q) (ha : a ≠ 0) (horth : ∀ x ∈ V, a ⬝ᵥ x = 0) :
      (∏ i, ‖bitFourierCoefficient (a i)‖) ≤ ε := by
    apply (lt_of_not_ge ?_).le
    intro h
    apply hR
    refine ⟨a, ha, h, fun j => horth _ ?_⟩
    change binaryColumn (ZMod q) (R j) ∈ LinearMap.ker P
    rw [hker]
    refine ⟨Pi.single j 1, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    ext i
    cases h : R j i <;> simp [binaryMatrixOfColumns, binaryColumn, zeroOneBit, h]
  have heq (x : Fin n → Bool) : P (binaryColumn (ZMod q) x) = y ↔
      V.mkQ (binaryColumn (ZMod q) x) = e.symm y := by
    have h := e.injective.eq_iff (a := V.mkQ (binaryColumn (ZMod q) x)) (b := e.symm y)
    rw [e.apply_symm_apply] at h
    exact h
  have hp := binary_quotient_probability_abs_sub_le V hε hcoeff (e.symm y)
  rw [hcard] at hp
  simpa only [← heq] using hp

end BooleanThreshold
