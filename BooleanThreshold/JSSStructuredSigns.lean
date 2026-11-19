module

public import BooleanThreshold.JSSStructuredNearPair

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

/-- A coordinate basis vector with an optional reversal of sign. -/
noncomputable def signedBasis {n : ℕ} (b : Bool) (i : Fin n) : Fin n → ℝ :=
  (if b then (-1 : ℝ) else 1) • Pi.single i 1

theorem signedBasis_apply {n : ℕ} (b : Bool) (i j : Fin n) :
    signedBasis b i j = if j = i then if b then -1 else 1 else 0 := by
  by_cases h : j = i <;> simp [signedBasis, h]

private theorem squaredNorm_flipVector {n : ℕ} (mask : Fin n → Bool) (a : Fin n → ℝ) :
    squaredNorm (flipVector mask a) = squaredNorm a := by
  unfold squaredNorm
  apply Finset.sum_congr rfl
  intro i _
  cases hi : mask i <;> simp [flipVector, hi]

private theorem flipVector_sub {n : ℕ} (mask : Fin n → Bool) (a b : Fin n → ℝ) :
    flipVector mask (a - b) = flipVector mask a - flipVector mask b := by
  funext i
  simp only [flipVector, Pi.sub_apply, mul_sub]

private theorem signMatrixMap_flip {m n : ℕ} (mask : Fin n → Bool)
    (M : Fin m → Fin n → Bool) (a : Fin n → ℝ) :
    signMatrixMap (flipColumns mask M) (flipVector mask a) = signMatrixMap M a := by
  funext r
  simp only [signMatrixMap_apply, dot_flipVector_realSigns_flipColumns]

private theorem signOpBound_flip {m n : ℕ} (mask : Fin n → Bool)
    {M : Fin m → Fin n → Bool} {K : ℝ} (hopper : signOpBound K M) :
    signOpBound K (flipColumns mask M) := by
  intro a
  have h := hopper (flipVector mask a)
  rw [← signMatrixMap_flip mask M, flipVector_involutive mask a, squaredNorm_flipVector] at h
  exact h

/-- A kernel vector also cannot be close to a negative coordinate vector in
the operator norm event. -/
theorem no_near_signedBasis_null_of_opBound {m n : ℕ} {K ε : ℝ}
    {M : Fin m → Fin n → Bool} (hm : 0 < m) (hM : signOpBound K M)
    (hε : K ^ 2 * ε ^ 2 < 1) (i : Fin n) (b : Bool) {a : Fin n → ℝ}
    (ha : signMatrixMap M a = 0) : ¬ squaredNorm (signedBasis b i - a) ≤ ε ^ 2 := by
  let mask : Fin n → Bool := fun _ => b
  have hbase : flipVector mask (signedBasis b i) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i <;> cases b <;> simp [mask, signedBasis_apply, flipVector, hj]
  intro hclose
  have h := no_near_basis_null_of_opBound hm (signOpBound_flip mask hM) hε i
    (show signMatrixMap (flipColumns mask M) (flipVector mask a) = 0 by
      rw [signMatrixMap_flip, ha])
  apply h
  rw [← hbase, ← flipVector_sub, squaredNorm_flipVector]
  exact hclose

/-- A kernel vector close to a signed sum of two columns, when the signed
sum of those columns is nonzero. -/
def nonzeroNearSignedPair {n : ℕ} (K ε : ℝ) (i j : Fin n) (b d : Bool) :
    Set (Fin n → Fin n → Bool) :=
  {M | signMatrixMap M (signedBasis b i + signedBasis d j) ≠ 0 ∧
    signOpBound K M ∧ ∃ a, signMatrixMap M a = 0 ∧
      squaredNorm (signedBasis b i + signedBasis d j - a) ≤ ε ^ 2}

private theorem signMatrixMap_diff_ne_zero_iff {m n : ℕ} (M : Fin m → Fin n → Bool)
    (i j : Fin n) :
    signMatrixMap M (Pi.single i 1 - Pi.single j 1) ≠ 0 ↔ ∃ r, M r i ≠ M r j := by
  have hr (r : Fin m) : signMatrixMap M (Pi.single i 1 - Pi.single j 1) r = 0 ↔
      M r i = M r j := by
    rw [map_sub, Pi.sub_apply, signMatrixMap_basis, signMatrixMap_basis, sub_eq_zero]
    cases hi : M r i <;> cases hj : M r j <;> norm_num [realSigns, hi, hj]
  rw [ne_eq, funext_iff, not_forall]
  exact exists_congr fun r => not_congr (hr r)

theorem uniformOn_nearSignedPair_le_nearDifference {n : ℕ} (K ε : ℝ)
    (i j : Fin n) (hij : i ≠ j) (b d : Bool) :
    (uniformOn Set.univ).real (nonzeroNearSignedPair K ε i j b d) ≤
      (uniformOn Set.univ).real (nonzeroNearColumnDifference K ε i j) := by
  let mask (k : Fin n) := if k = i then b else if k = j then !d else false
  let e : Equiv.Perm (Fin n → Fin n → Bool) :=
    ⟨flipColumns mask, flipColumns mask, flipColumns_involutive mask, flipColumns_involutive mask⟩
  let w : Fin n → ℝ := signedBasis b i + signedBasis d j
  let z : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
  have hw : flipVector mask w = z := by
    funext k
    by_cases hki : k = i
    · subst k
      cases b <;> simp [w, z, mask, flipVector, signedBasis_apply, hij]
    · by_cases hkj : k = j
      · subst k
        cases d <;> simp [w, z, mask, flipVector, signedBasis_apply, hki]
      · simp [w, z, mask, flipVector, signedBasis_apply, hki, hkj]
  have hsub : nonzeroNearSignedPair K ε i j b d ⊆ e ⁻¹' nonzeroNearColumnDifference K ε i j := by
    rintro M ⟨hM, hopper, a, ha, hclose⟩
    change flipColumns mask M ∈ nonzeroNearColumnDifference K ε i j
    refine ⟨(signMatrixMap_diff_ne_zero_iff _ _ _).mp ?_, signOpBound_flip mask hopper,
      flipVector mask a, ?_, ?_⟩
    · change signMatrixMap (flipColumns mask M) z ≠ 0
      rw [← hw, signMatrixMap_flip]
      exact hM
    · rw [signMatrixMap_flip, ha]
    · change squaredNorm (z - flipVector mask a) ≤ ε ^ 2
      rw [← hw, ← flipVector_sub, squaredNorm_flipVector]
      exact hclose
  refine (measureReal_mono hsub).trans_eq ?_
  rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_of_finite _)
    (Set.toFinite _).measurableSet, map_uniformOn_univ_of_equiv e]

end BooleanThreshold
