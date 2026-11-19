module

public import BooleanThreshold.CokernelLargeExposure
public import BooleanThreshold.CokernelUniformDeterminant
public import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units

public noncomputable section

open Function Matrix MeasureTheory ProbabilityTheory Submodule
open scoped BigOperators Classical Function

namespace BooleanThreshold

/-- Independence of the given residue-matrix columns at every residue field of the modulus. -/
@[expose] def modularPrefixIndependent {N m q : ℕ} (A : Matrix (Fin N) (Fin m) (ZMod q)) : Prop :=
  ∀ p (hp : p ∈ q.primeFactors),
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    LinearIndependent (ZMod p) (A.map
      (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p))).col

/-- Independence of a binary column family at every residue field of the modulus. -/
@[expose] def binaryPrefixIndependent {N m : ℕ} (q : ℕ) (R : Fin m → Fin N → Bool) : Prop :=
  ∀ p (hp : p ∈ q.primeFactors),
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    LinearIndependent (ZMod p) (binaryColumn (ZMod p) ∘ R)

theorem binaryPrefixIndependent_iff_modular {N m : ℕ} (q : ℕ) (R : Fin m → Fin N → Bool) :
    binaryPrefixIndependent q R ↔ modularPrefixIndependent
      ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))) := by
  unfold binaryPrefixIndependent modularPrefixIndependent
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have he : (((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))).map
      (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p))).col =
      binaryColumn (ZMod p) ∘ R := by
    funext i j
    change (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p))
      ((binaryMatrixOfColumns R j i : ℤ) : ZMod q) = binaryColumn (ZMod p) (R i) j
    rw [map_intCast]
    cases h : R i j <;> simp [binaryMatrixOfColumns, binaryColumn, zeroOneBit, h]
  change LinearIndependent (ZMod p) (binaryColumn (ZMod p) ∘ R) ↔
    LinearIndependent (ZMod p) (((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))).map
      (ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p))).col
  rw [he]

private theorem exists_prefix_dependence_step {m : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (X : Fin (m + 1) → V)
    (hX : ¬ LinearIndependent K X) :
    ∃ j, X j ∈ prefixSpan (K := K) X j.val := by
  by_contra! h
  have hr (k : ℕ) (hk : k ≤ m + 1) : Module.finrank K (prefixSpan (K := K) X k) = k := by
    induction k with
    | zero => rw [prefixSpan_zero]; simp
    | succ k ih =>
      let j : Fin (m + 1) := ⟨k, hk⟩
      change Module.finrank K (prefixSpan (K := K) X (j.val + 1)) = k + 1
      rw [prefixSpan_succ, finrank_sup_span_singleton (h j), ih (Nat.le_of_succ_le hk)]
  apply hX
  apply (linearIndependent_iff_card_eq_finrank_span).mpr
  calc
    _ = Module.finrank K (prefixSpan (K := K) X (m + 1)) :=
      (Fintype.card_fin (m + 1)).trans (hr (m + 1) le_rfl).symm
    _ = _ := by rw [prefixSpan_castLE X le_rfl]; congr

/-- Bounding the mass of every fixed subspace gives a rank estimate for
independent uniformly sampled columns. -/
theorem uniformColumn_dependence_probability_le {N m : ℕ} {K Ω : Type*} [Field K]
    [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (φ : Ω → Fin N → K) (hm : m ≤ N)
    (hφ : ∀ W : Submodule K (Fin N → K),
      (uniformOn Set.univ).real {x : Ω | φ x ∈ W} ≤ (1 / 2 : ℝ) ^ (N - Module.finrank K W)) :
    (uniformOn Set.univ).real {R : Fin m → Ω | ¬ LinearIndependent K (φ ∘ R)} ≤
      (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
  cases m with
  | zero =>
    have hzero : {R : Fin 0 → Ω | ¬ LinearIndependent K (φ ∘ R)} = ∅ := by
      ext R
      exact iff_false_intro (fun h => h linearIndependent_empty_type)
    rw [hzero, measureReal_empty]
    simp
  | succ m =>
    let μ := uniformOn (Set.univ : Set (Fin (m + 1) → Ω))
    let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    let E (j : Fin (m + 1)) := {R : Fin (m + 1) → Ω |
      φ (R j) ∈ prefixSpan (K := K) (φ ∘ R) j.val}
    have hcover : {R : Fin (m + 1) → Ω | ¬ LinearIndependent K (φ ∘ R)} ⊆ ⋃ j, E j := by
      intro R hR
      obtain ⟨j, hj⟩ := exists_prefix_dependence_step (φ ∘ R) hR
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have hE (j : Fin (m + 1)) : μ.real (E j) ≤ (1 / 2 : ℝ) ^ (N + 1 - (m + 1)) := by
      simp only [E, prefixSpan_castLE _ (Nat.le_of_lt j.isLt)]
      apply uniformOn_prefix_next_le j
        (fun R x => φ x ∈ Submodule.span K (Set.range (φ ∘ R)))
      intro R
      let W := Submodule.span K (Set.range (φ ∘ R))
      have hdim : Module.finrank K W ≤ j.val := by
        exact (finrank_range_le_card (R := K) (φ ∘ R)).trans_eq (Fintype.card_fin _)
      refine (hφ W).trans
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_)
      have hdim' := j.isLt
      omega
    calc
      _ ≤ μ.real (⋃ j, E j) := measureReal_mono hcover
      _ ≤ ∑ j, μ.real (E j) := measureReal_iUnion_fintype_le E
      _ ≤ ∑ _j : Fin (m + 1), (1 / 2 : ℝ) ^ (N + 1 - (m + 1)) :=
        Finset.sum_le_sum fun j _ => hE j
      _ = _ := by simp

/-- The early columns are independent at all prime factors, with a geometric error
in the number of columns that have yet to be exposed. -/
theorem binaryPrefixIndependent_failure_probability_le {q N m : ℕ} (hm : m ≤ N) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool | ¬ binaryPrefixIndependent q R} ≤
      (q.primeFactors.card : ℝ) * (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
  let μ := uniformOn (Set.univ : Set (Fin m → Fin N → Bool))
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let E (p : ℕ) : Set (Fin m → Fin N → Bool) :=
    {R | ∃ hp : p.Prime,
      let : Fact p.Prime := ⟨hp⟩
      ¬ LinearIndependent (ZMod p) (binaryColumn (ZMod p) ∘ R)}
  have hcover : {R : Fin m → Fin N → Bool | ¬ binaryPrefixIndependent q R} ⊆
      ⋃ p ∈ q.primeFactors, E p := by
    intro R hR
    by_contra h
    apply hR
    intro p hp
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    by_contra hdep
    exact h (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, Fact.out, hdep⟩⟩)
  calc
    _ ≤ μ.real (⋃ p ∈ q.primeFactors, E p) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ p ∈ q.primeFactors, μ.real (E p) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ q.primeFactors, (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
      apply Finset.sum_le_sum
      intro p hp
      let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      have hE : E p = {R | ¬ LinearIndependent (ZMod p) (binaryColumn (ZMod p) ∘ R)} := by
        ext R
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Fact.out, h⟩⟩
      rw [hE]
      exact uniformColumn_dependence_probability_le (binaryColumn (ZMod p)) hm
        binaryColumn_mass_in_subspace_le
    _ = _ := by simp [mul_assoc]

/-- The ordered split of the column indices into the exposed prefix and the suffix. -/
@[expose] def prefixSuffixIndex {N m k : ℕ} (h : m + k = N) : Fin m ⊕ Fin k ≃ Fin N :=
  finSumFinEquiv.trans (finCongr h)

/-- Form the square matrix by appending the given suffix columns to the fixed prefix. -/
@[expose] def appendMatrixColumns {N m k : ℕ} {R : Type*} (h : m + k = N)
    (A : Matrix (Fin N) (Fin m) R) (X : Fin k → Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => Sum.elim (A i) (fun l => X l i) ((prefixSuffixIndex h).symm j)

@[simp] theorem appendMatrixColumns_prefix {N m k : ℕ} {R : Type*} (h : m + k = N)
    (A : Matrix (Fin N) (Fin m) R) (X : Fin k → Fin N → R) (i : Fin N) (j : Fin m) :
    appendMatrixColumns h A X i (prefixSuffixIndex h (.inl j)) = A i j := by
  simp [appendMatrixColumns]

@[simp] theorem appendMatrixColumns_suffix {N m k : ℕ} {R : Type*} (h : m + k = N)
    (A : Matrix (Fin N) (Fin m) R) (X : Fin k → Fin N → R) (i : Fin N) (j : Fin k) :
    appendMatrixColumns h A X i (prefixSuffixIndex h (.inr j)) = X j i := by
  simp [appendMatrixColumns]

private theorem exists_sum_equiv_of_embedding {V : Type*} [Fintype V] {m k : ℕ}
    (h : m + k = Fintype.card V) (r : Fin m ↪ V) :
    ∃ e : Fin m ⊕ Fin k ≃ V, ∀ j, e (.inl j) = r j := by
  let E := Set.range r
  let er : Fin m ≃ E := Equiv.ofInjective r r.injective
  let ec := Equiv.Set.sumCompl E
  have hc := Fintype.card_congr ec
  rw [Fintype.card_sum, ← Fintype.card_congr er, Fintype.card_fin, ← h] at hc
  let ek : Fin k ≃ (Eᶜ : Set V) :=
    (Fintype.equivFinOfCardEq (show Fintype.card (Eᶜ : Set V) = k by omega)).symm
  exact ⟨(er.sumCongr ek).trans ec, fun _ => rfl⟩

private theorem exists_unit_completion_of_unit_minor {N m k : ℕ} {R : Type*} [CommRing R]
    (h : m + k = N) (A : Matrix (Fin N) (Fin m) R) (r : Fin m ↪ Fin N)
    (hminor : IsUnit (A.submatrix r id).det) :
    ∃ T : Matrix (Fin N) (Fin N) R, IsUnit T.det ∧
      ∀ i j, T i (prefixSuffixIndex h (.inl j)) = A i j := by
  obtain ⟨e, he⟩ := exists_sum_equiv_of_embedding (by simpa using h) r
  let f := prefixSuffixIndex h
  let B : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) R := Matrix.fromBlocks
    (A.submatrix r id) 0 (A.submatrix (fun i => e (.inr i)) id) 1
  let T := B.submatrix e.symm f.symm
  refine ⟨T, ?_, ?_⟩
  · have hB : IsUnit B.det := by
      dsimp [B]
      rwa [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    let U := B.submatrix f.symm f.symm
    have hU : IsUnit U.det := by simpa only [U, Matrix.det_submatrix_equiv_self] using hB
    let σ : Equiv.Perm (Fin N) := e.symm.trans f
    have hT : T = U.submatrix σ id := by
      ext i j
      change B (e.symm i) (f.symm j) = B (f.symm (f (e.symm i))) (f.symm j)
      rw [f.symm_apply_apply]
    rw [hT, Matrix.det_permute]
    let u := Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign σ)
    exact u.isUnit.mul hU
  · intro i j
    obtain ⟨l, rfl⟩ := e.surjective i
    change B (e.symm (e l)) (f.symm (f (.inl j))) = A (e l) j
    rw [e.symm_apply_apply, f.symm_apply_apply]
    cases l with
    | inl i => simp only [B, Matrix.fromBlocks_apply₁₁, Matrix.submatrix_apply, id_eq, he]
    | inr i => rfl

private theorem exists_unit_completion_prime_power {N m k p a : ℕ} (h : m + k = N)
    (hp : p.Prime) (ha : 0 < a) (A : Matrix (Fin N) (Fin m) (ZMod (p ^ a)))
    (hA : let : Fact p.Prime := ⟨hp⟩
      LinearIndependent (ZMod p) (A.map (ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p))).col) :
    ∃ T : Matrix (Fin N) (Fin N) (ZMod (p ^ a)), IsUnit T.det ∧
      ∀ i j, T i (prefixSuffixIndex h (.inl j)) = A i j := by
  let : Fact p.Prime := ⟨hp⟩
  let red := ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
  let B := A.map red
  have hrank : B.rank = m := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card (show LinearIndependent (ZMod p) B.col from hA),
      Fintype.card_fin]
  have hex := exists_rank_minor B
  rw [hrank] at hex
  obtain ⟨r, c, hc⟩ := hex
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp c.injective)
  have hminor : (B.submatrix r id).det ≠ 0 := by
    intro hz
    apply hc
    change ((B.submatrix r id).submatrix id σ).det = 0
    rw [Matrix.det_permute', hz, mul_zero]
  let d := (A.submatrix r id).det
  have hd : red d ≠ 0 := by
    rw [show red d = ((A.submatrix r id).map red).det from red.map_det _]
    exact hminor
  have hnot : ¬ p ∣ d.val := by
    intro hdiv
    apply hd
    conv_lhs => rw [← ZMod.natCast_zmod_val d, map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  apply exists_unit_completion_of_unit_minor h A r
  change IsUnit d
  rw [← ZMod.natCast_zmod_val d]
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).mpr hnot

/-- Independence at the prime factors of the modulus gives a unit-determinant
completion of the column family. -/
theorem modularPrefixIndependent_unit_completion {N m k q : ℕ} [NeZero q]
    (h : m + k = N) (A : Matrix (Fin N) (Fin m) (ZMod q))
    (hA : modularPrefixIndependent A) :
    ∃ T : Matrix (Fin N) (Fin N) (ZMod q), IsUnit T.det ∧
      ∀ i j, T i (prefixSuffixIndex h (.inl j)) = A i j := by
  let I := q.primeFactors
  let r (i : I) := i.val ^ q.factorization i.val
  have hp (i : I) : i.val.Prime := Nat.prime_of_mem_primeFactors i.property
  have ha (i : I) : 0 < q.factorization i.val := by
    apply Nat.pos_of_ne_zero
    exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using i.property)
  have hprod : q = ∏ i, r i :=
    (Nat.prod_primeFactors_pow_factorization (NeZero.ne q)).trans
      (Finset.prod_subtype I (fun _ => Iff.rfl) (fun p => p ^ q.factorization p))
  have hcoprime : Pairwise (Nat.Coprime on r) := fun i j hij =>
    Nat.coprime_pow_primes _ _ (hp i) (hp j) (fun he => hij (Subtype.ext he))
  let crt : ZMod q ≃+* ∀ i : I, ZMod (r i) :=
    (ZMod.ringEquivCongr hprod).trans (ZMod.prodEquivPi r hcoprime)
  let f (i : I) := (Pi.evalRingHom (fun i => ZMod (r i)) i).comp crt.toRingHom
  have himage (i : I) : let : Fact i.val.Prime := ⟨hp i⟩
      LinearIndependent (ZMod i.val) ((A.map (f i)).map
        (ZMod.castHom (dvd_pow_self i.val (ha i).ne') (ZMod i.val))).col := by
    let : Fact i.val.Prime := ⟨hp i⟩
    let g := ZMod.castHom (dvd_pow_self i.val (ha i).ne') (ZMod i.val)
    let g' := ZMod.castHom (Nat.dvd_of_mem_primeFactors i.property) (ZMod i.val)
    have he : (A.map (f i)).map g = A.map g' := by
      ext u v
      change g (f i (A u v)) = g' (A u v)
      obtain ⟨z, hz⟩ := ZMod.intCast_surjective (A u v)
      rw [← hz, map_intCast, map_intCast, map_intCast]
    change LinearIndependent (ZMod i.val) ((A.map (f i)).map g).col
    rw [he]
    exact hA i.val i.property
  choose T hdet hprefix using fun i => exists_unit_completion_prime_power h (hp i) (ha i)
    (A.map (f i)) (himage i)
  let U : Matrix (Fin N) (Fin N) (ZMod q) := Matrix.of fun i j => crt.symm (fun l => T l i j)
  have hU (i : I) : U.map (f i) = T i := by
    ext u v
    exact congrFun (crt.apply_symm_apply (fun l => T l u v)) i
  refine ⟨U, ?_, ?_⟩
  · have hunit : IsUnit (crt U.det) := Pi.isUnit_iff.mpr fun i => by
      change IsUnit (f i U.det)
      rw [(f i).map_det, RingHom.mapMatrix_apply, hU]
      exact hdet i
    simpa only [RingEquiv.symm_apply_apply] using hunit.map crt.symm
  · intro i j
    apply crt.injective
    funext l
    exact (congrArg (fun M => M i (prefixSuffixIndex h (.inl j))) (hU l)).trans (hprefix l i j)

/-- A full-rank prefix over all residue fields admits a surjective projection onto
its free cokernel. Appending suffix columns reduces the determinant-zero test
to their projected square matrix. -/
theorem matrixPrefixProjection {N m k q : ℕ} [NeZero q] (h : m + k = N)
    (A : Matrix (Fin N) (Fin m) (ZMod q)) (hA : modularPrefixIndependent A) :
    ∃ P : (Fin N → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q),
      Surjective P ∧ LinearMap.ker P = LinearMap.range A.mulVecLin ∧
      ∀ X : Fin k → Fin N → ZMod q,
        (appendMatrixColumns h A X).det = 0 ↔ (Matrix.of (fun i j => P (X j) i)).det = 0 := by
  obtain ⟨T, hTdet, hT⟩ := modularPrefixIndependent_unit_completion h A hA
  let R := ZMod q
  let e := prefixSuffixIndex h
  let P : (Fin N → R) →ₗ[R] (Fin k → R) := LinearMap.pi
    fun j => (LinearMap.proj (e (.inr j))).comp T⁻¹.mulVecLin
  let E (u : Fin m → R) (v : Fin k → R) : Fin N → R :=
    fun i => Sum.elim u v (e.symm i)
  have hE₁ (u : Fin m → R) (v : Fin k → R) (j : Fin m) :
      E u v (e (.inl j)) = u j := by simp [E]
  have hE₂ (u : Fin m → R) (v : Fin k → R) (j : Fin k) :
      E u v (e (.inr j)) = v j := by simp [E]
  have hP (x : Fin N → R) (j : Fin k) : P x j = (T⁻¹ *ᵥ x) (e (.inr j)) := rfl
  have hTA (u : Fin m → R) : T *ᵥ E u 0 = A *ᵥ u := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    calc
      _ = ∑ j : Fin m ⊕ Fin k, T i (e j) * E u 0 (e j) :=
        (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      _ = _ := by rw [Fintype.sum_sum_type]; simp [hT, hE₁, hE₂, e]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro s
    refine ⟨T *ᵥ E 0 s, funext fun j => ?_⟩
    rw [hP, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hTdet, Matrix.one_mulVec, hE₂]
  · ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      let y := T⁻¹ *ᵥ x
      let u (i : Fin m) := y (e (.inl i))
      have hy : y = E u 0 := by
        funext i
        obtain ⟨l, rfl⟩ := e.surjective i
        cases l with
        | inl j => rw [hE₁]
        | inr j =>
          rw [hE₂]
          exact congrFun hx j
      refine ⟨u, ?_⟩
      change A *ᵥ u = x
      rw [← hTA, ← hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hTdet, Matrix.one_mulVec]
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      funext j
      change P (A *ᵥ u) j = 0
      rw [← hTA, hP, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hTdet, Matrix.one_mulVec, hE₂]
      rfl
  · intro X
    let M := appendMatrixColumns h A X
    let B := (T⁻¹ * M).submatrix e e
    let D : Matrix (Fin k) (Fin k) R := Matrix.of fun i j => P (X j) i
    have hleft (i : Fin N) (j : Fin m) :
        (T⁻¹ * M) i (e (.inl j)) = (1 : Matrix (Fin N) (Fin N) R) i (e (.inl j)) := by
      rw [← Matrix.nonsing_inv_mul T hTdet]
      simp only [Matrix.mul_apply, M, e, appendMatrixColumns_prefix, hT]
    have hright (i j : Fin k) : (T⁻¹ * M) (e (.inr i)) (e (.inr j)) = D i j := by
      change _ = P (X j) i
      rw [hP]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, M, e, appendMatrixColumns_suffix]
    have hB : B = Matrix.fromBlocks 1 (B.submatrix Sum.inl Sum.inr) 0 D := by
      ext i j
      change (T⁻¹ * M) (e i) (e j) = _
      rcases i with i | i <;> rcases j with j | j
      · simp [hleft, Matrix.one_apply]
      · rfl
      · simp [hleft]
      · exact hright i j
    have hchange : (T⁻¹ * M).det = D.det := by
      rw [← Matrix.det_submatrix_equiv_self e (T⁻¹ * M)]
      change B.det = _
      rw [hB, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    have hmul : M.det = T.det * D.det := by
      rw [← hchange, ← Matrix.det_mul, Matrix.mul_nonsing_inv_cancel_left T M hTdet]
    change M.det = 0 ↔ D.det = 0
    rw [hmul]
    exact hTdet.isRegular.left.mul_left_eq_zero_iff

theorem binaryMatrixPrefixProjection {N m k q : ℕ} [NeZero q] (h : m + k = N)
    (R : Fin m → Fin N → Bool) (hR : binaryPrefixIndependent q R) :
    ∃ P : (Fin N → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q),
      Surjective P ∧ LinearMap.ker P =
        LinearMap.range ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))).mulVecLin ∧
      ∀ X : Fin k → Fin N → ZMod q,
        (appendMatrixColumns h ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))) X).det = 0 ↔
          (Matrix.of (fun i j => P (X j) i)).det = 0 :=
  matrixPrefixProjection h _ ((binaryPrefixIndependent_iff_modular q R).mp hR)

/-- A surjective additive map applied to uniform independent columns gives
uniform independent projected columns. -/
theorem finiteUniformFraction_projected_columns {I V W : Type*} [Finite I] [AddGroup V] [Finite V]
    [AddGroup W] (P : V →+ W) (hP : Surjective P) (E : (I → W) → Prop) :
    finiteUniformFraction (fun X : I → V => E (P ∘ X)) = finiteUniformFraction E := by
  let F : (I → V) →+ (I → W) := AddMonoidHom.pi fun i => P.comp (Pi.evalAddMonoidHom _ i)
  have hF : Surjective F := by
    intro y
    choose x hx using fun i => hP (y i)
    exact ⟨x, funext hx⟩
  exact finiteUniformFraction_addHom_preimage F hF E

end BooleanThreshold
