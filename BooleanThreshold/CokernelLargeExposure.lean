module

public import BooleanThreshold.CokernelModulo
public import BooleanThreshold.CokernelRankTransfer
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open scoped Matrix
open Function Matrix Set Submodule MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- A rank process with single-column increments has a second failed
increment before it ends at least two below the number of columns. -/
theorem exists_second_failed_increment (n : ℕ) (r : ℕ → ℕ)
    (hstep : ∀ j ≤ n, r j ≤ r (j + 1) ∧ r (j + 1) ≤ r j + 1)
    (hdef : r (n + 1) < n) :
    ∃ j : Fin (n + 1), r j.val + 1 = j.val ∧ r (j.val + 1) = r j.val := by
  let h : ∃ k, r k + 1 < k := ⟨n + 1, by omega⟩
  let k := Nat.find h
  have hk : r k + 1 < k := Nat.find_spec h
  have hkn : k ≤ n + 1 := Nat.find_min' h (by omega)
  have hkpos : 0 < k := by omega
  let j := k - 1
  have hj : j + 1 = k := Nat.sub_add_cancel hkpos
  have hjk : j < k := by omega
  have hfirst : j ≤ r j + 1 := Nat.le_of_not_gt (Nat.find_min h hjk)
  have hnext := (hstep j (by omega)).1
  rw [hj] at hnext
  refine ⟨⟨j, by omega⟩, ?_⟩
  change r j + 1 = j ∧ r (j + 1) = r j
  rw [hj]
  omega

/-- The span of the first `k` columns of a finite family. -/
@[expose] def prefixSpan {n : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (X : Fin (n + 1) → V) (k : ℕ) : Submodule K V :=
  span K (X '' {i | i.val < k})

theorem prefixSpan_zero {n : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (X : Fin (n + 1) → V) :
    prefixSpan (K := K) X 0 = ⊥ := by simp [prefixSpan]

theorem prefixSpan_succ {n : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (X : Fin (n + 1) → V) (j : Fin (n + 1)) :
    prefixSpan (K := K) X (j.val + 1) = prefixSpan X j.val ⊔ K ∙ X j := by
  have h : {i : Fin (n + 1) | i.val < j.val + 1} = insert j {i | i.val < j.val} := by
    ext i
    simp only [mem_ofPred_eq, mem_insert_iff]
    rw [← Fin.val_inj]
    omega
  rw [prefixSpan, h, image_insert_eq, span_insert, sup_comm]
  rfl

/-- In a deficient family of `n+1` columns, some extra column lies in the
span of a prefix of rank one below its length. -/
theorem exists_second_failed_column {n : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (X : Fin (n + 1) → V) (h : Module.finrank K (span K (range X)) < n) :
    ∃ j : Fin (n + 1),
      Module.finrank K (prefixSpan (K := K) X j.val) + 1 = j.val ∧
        X j ∈ prefixSpan (K := K) X j.val := by
  let r (k : ℕ) := Module.finrank K (prefixSpan (K := K) X k)
  have hstep (j : ℕ) (hj : j ≤ n) : r j ≤ r (j + 1) ∧ r (j + 1) ≤ r j + 1 := by
    let i : Fin (n + 1) := ⟨j, by omega⟩
    change r i.val ≤ r (i.val + 1) ∧ r (i.val + 1) ≤ r i.val + 1
    unfold r
    rw [prefixSpan_succ]
    by_cases hmem : X i ∈ prefixSpan (K := K) X i.val
    · rw [sup_eq_left.mpr ((span_singleton_le_iff_mem _ _).mpr hmem)]
      exact ⟨le_rfl, Nat.le_succ _⟩
    · rw [finrank_sup_span_singleton hmem]
      exact ⟨Nat.le_succ _, le_rfl⟩
  have hf : r (n + 1) < n := by
    have he : {i : Fin (n + 1) | i.val < n + 1} = univ := by
      ext i
      change i.val < n + 1 ↔ True
      exact iff_of_true i.isLt trivial
    change Module.finrank K (span K (X '' {i | i.val < n + 1})) < n
    rwa [he, image_univ]
  obtain ⟨j, hr, he⟩ := exists_second_failed_increment n r hstep hf
  refine ⟨j, hr, ?_⟩
  by_contra hmem
  have hstep' : r (j.val + 1) = r j.val + 1 := by
    unfold r
    rw [prefixSpan_succ, finrank_sup_span_singleton hmem]
  omega

/-- A choice of a full-rank minor of an integral prefix with full rational column rank. -/
theorem exists_nonzero_full_column_minor {N j : ℕ} (A : Matrix (Fin N) (Fin j) ℤ)
    (hfull : (A.map (fun x : ℤ => (x : ℚ))).rank = j) :
    ∃ (r : Fin j ↪ Fin N) (c : Fin j ↪ Fin j), (A.submatrix r c).det ≠ 0 := by
  have h := exists_rank_minor (A.map (fun x : ℤ => (x : ℚ)))
  rw [hfull] at h
  obtain ⟨r, c, hn⟩ := h
  refine ⟨r, c, fun hz => hn ?_⟩
  change ((A.submatrix r c).map (fun x : ℤ => (x : ℚ))).det = 0
  rw [← Int.cast_det, hz, Int.cast_zero]

/-- The chosen integer minor detects all primes at which its prefix loses rank. -/
noncomputable def fullColumnMinor {N j : ℕ} (A : Matrix (Fin N) (Fin j) ℤ)
    (hfull : (A.map (fun x : ℤ => (x : ℚ))).rank = j) : ℤ :=
  let h := exists_nonzero_full_column_minor A hfull
  let r : Fin j ↪ Fin N := Classical.choose h
  let c : Fin j ↪ Fin j := Classical.choose (Classical.choose_spec h)
  (A.submatrix r c).det

theorem fullColumnMinor_ne_zero {N j : ℕ} {A : Matrix (Fin N) (Fin j) ℤ}
    (hfull : (A.map (fun x : ℤ => (x : ℚ))).rank = j) : fullColumnMinor A hfull ≠ 0 :=
  Classical.choose_spec (Classical.choose_spec (exists_nonzero_full_column_minor A hfull))

theorem prime_dvd_fullColumnMinor_of_modular_rank_loss {N j p : ℕ}
    (hp : p.Prime) (A : Matrix (Fin N) (Fin j) ℤ)
    (hfull : (A.map (fun x : ℤ => (x : ℚ))).rank = j)
    (hdef : (A.map (fun x : ℤ => (x : ZMod p))).rank < j) :
    p ∣ (fullColumnMinor A hfull).natAbs := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let e := exists_nonzero_full_column_minor A hfull
  let r := Classical.choose e
  let c := Classical.choose (Classical.choose_spec e)
  have hz : ((A.map (fun x : ℤ => (x : ZMod p))).submatrix r c).det = 0 := by
    by_contra hz
    have hm := (A.map (fun x : ℤ => (x : ZMod p))).rank_submatrix_le r c
    rw [rank_of_det_ne_zero hz, Fintype.card_fin] at hm
    omega
  change ((A.submatrix r c).map (fun x : ℤ => (x : ZMod p))).det = 0 at hz
  rw [← Int.cast_det] at hz
  exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (ZMod.intCast_zmod_eq_zero_iff_dvd _ _ |>.mp hz))

theorem abs_fullColumnMinor_le_factorial {N j : ℕ} (A : Matrix (Fin N) (Fin j) ℤ)
    (hfull : (A.map (fun x : ℤ => (x : ℚ))).rank = j)
    (hA : ∀ i k, |A i k| ≤ 1) :
    |fullColumnMinor A hfull| ≤ (j.factorial : ℤ) := by
  unfold fullColumnMinor
  simpa only [one_pow, mul_one] using abs_minor_le_factorial_mul_pow A hA _ _


/-- Some set of coordinates of size equal to the dimension determines
every vector of a subspace. -/
theorem exists_coordinates_injective_on_subspace {N : ℕ} {K : Type*} [Field K]
    (W : Submodule K (Fin N → K)) :
    ∃ e : Fin (Module.finrank K W) ↪ Fin N, InjOn (fun x => x ∘ e) (W : Set (Fin N → K)) := by
  classical
  let d := Module.finrank K W
  let b := Module.finBasis K W
  let A : Matrix (Fin N) (Fin d) K := Matrix.of fun i j => (b j : Fin N → K) i
  have hLI : LinearIndependent K A.col :=
    b.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr W.subtype_injective)
  have hr : A.rank = d := by
    rw [A.rank_eq_finrank_span_cols, finrank_span_eq_card hLI, Fintype.card_fin]
  have hminor := exists_rank_minor A
  rw [hr] at hminor
  obtain ⟨r, c, hdet⟩ := hminor
  refine ⟨r, fun x hx y hy hxy => ?_⟩
  let z : W := ⟨x - y, W.sub_mem hx hy⟩
  let c' := Equiv.ofBijective c ⟨c.injective, Finite.injective_iff_surjective.mp c.injective⟩
  let a (j : Fin d) := b.repr z (c j)
  have hsum : (∑ j, a j • b (c j)) = z := by
    calc
      _ = ∑ j, b.repr z j • b j := Fintype.sum_equiv c' _ _ fun _ => rfl
      _ = _ := b.sum_repr z
  have hz : (A.submatrix r c) *ᵥ a = 0 := by
    funext i
    let ev : W →ₗ[K] K := (LinearMap.proj (r i)).comp W.subtype
    have he := congrArg ev hsum
    simp only [map_sum, map_smul, LinearMap.comp_apply, LinearMap.proj_apply, ev,
      Submodule.subtype_apply, z, Pi.sub_apply] at he
    rw [show x (r i) = y (r i) from congrFun hxy i, sub_self] at he
    simpa only [mulVec, dotProduct, Matrix.submatrix_apply, A, Matrix.of_apply, Pi.zero_apply,
      smul_eq_mul, mul_comm] using he
  have ha : a = 0 := mulVec_injective_of_det_ne_zero hdet (by rwa [mulVec_zero])
  have hzx : x - y = 0 := by
    have hz' : z = 0 := by
      rw [← hsum, ha]
      simp
    exact congrArg Subtype.val hz'
  exact sub_eq_zero.mp hzx

/-- Boolean encoding of a column with entries zero and one in a field. -/
@[expose] def binaryColumn (K : Type*) [Zero K] [One K] {N : ℕ} (x : Fin N → Bool) : Fin N → K :=
  fun i => if x i then 0 else 1

theorem binaryColumn_injective (K : Type*) [Field K] (N : ℕ) :
    Injective (@binaryColumn K _ _ N) := by
  intro x y h
  funext i
  have hi := congrFun h i
  cases hx : x i <;> cases hy : y i <;> simp [binaryColumn, hx, hy] at hi ⊢

/-- At most `2^d` binary columns can lie in a subspace of dimension `d`. -/
theorem binaryColumn_card_in_subspace_le {N : ℕ} {K : Type*} [Field K]
    (W : Submodule K (Fin N → K)) :
    Nat.card {x : Fin N → Bool // binaryColumn K x ∈ W} ≤ 2 ^ Module.finrank K W := by
  obtain ⟨p, hp⟩ := exists_coordinates_injective_on_subspace W
  let f : {x : Fin N → Bool // binaryColumn K x ∈ W} →
      Fin (Module.finrank K W) → Bool := fun x => x.val ∘ p
  have h : Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply binaryColumn_injective K N
    refine hp x.prop y.prop ?_
    funext i
    change (if x.val (p i) then (0 : K) else 1) = if y.val (p i) then 0 else 1
    rw [show x.val (p i) = y.val (p i) from congrFun hxy i]
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f h

/-- The chance that a uniform binary column lies in a prescribed subspace
is at most one half to the power of its codimension. -/
theorem binaryColumn_mass_in_subspace_le {N : ℕ} {K : Type*} [Field K]
    (W : Submodule K (Fin N → K)) :
    (uniformOn Set.univ).real {x : Fin N → Bool | binaryColumn K x ∈ W} ≤
      (1 / 2 : ℝ) ^ (N - Module.finrank K W) := by
  let d := Module.finrank K W
  have hd : d ≤ N := by simpa using W.finrank_le
  rw [uniformOn_univ_real_eq_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  have hcast : ({x : Fin N → Bool | binaryColumn K x ∈ W}.ncard : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast binaryColumn_card_in_subspace_le W
  calc
    _ ≤ (2 : ℝ) ^ d / (2 : ℝ) ^ N := div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := by
      have hpow := pow_add (2 : ℝ) d (N - d)
      rw [Nat.add_sub_cancel' hd] at hpow
      calc
        _ = (2 : ℝ) ^ d * 1 / ((2 : ℝ) ^ d * (2 : ℝ) ^ (N - d)) := by rw [hpow, mul_one]
        _ = _ := by
          rw [mul_div_mul_left, div_pow, one_pow]
          positivity


/-- A uniform finite product inherits a uniform bound on every conditional fiber. -/
theorem uniformOn_product_of_fiber_le {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (P : X → Y → Prop) (q : ℝ)
    (h : ∀ x, (uniformOn Set.univ).real {y : Y | P x y} ≤ q) :
    (uniformOn Set.univ).real {z : X × Y | P z.1 z.2} ≤ q := by
  let e : {z : X × Y // P z.1 z.2} ≃ (Σ x : X, {y : Y // P x y}) :=
    ⟨fun z => ⟨z.val.1, z.val.2, z.prop⟩,
      fun z => ⟨(z.1, z.2.val), z.2.prop⟩,
      fun z => by cases z; rfl, fun z => by cases z; rfl⟩
  have hcard : {z : X × Y | P z.1 z.2}.ncard = ∑ x, {y : Y | P x y}.ncard := by
    exact (Nat.card_congr e).trans Nat.card_sigma
  have hξ : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos (α := X)
  have hη : 0 < (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos (α := Y)
  rw [uniformOn_univ_real_eq_card, hcard, Nat.cast_sum, Fintype.card_prod, Nat.cast_mul]
  apply (div_le_iff₀ (mul_pos hξ hη)).2
  calc
    _ ≤ ∑ _x : X, q * (Fintype.card Y : ℝ) := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hx := h x
      rw [uniformOn_univ_real_eq_card] at hx
      exact (div_le_iff₀ hη).1 hx
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- Split a sample into the exposed columns, the next column, and the rest. -/
def splitAtColumn {N : ℕ} (X : Type*) (j : Fin (N + 1)) :
    (Fin (N + 1) → X) ≃ (Fin j.val → X) × (Fin (N - j.val) → X) × X :=
  let a := finCongr (show N + 1 = j.val + 1 + (N - j.val) by omega)
  ((Equiv.arrowCongr a (Equiv.refl X)).trans
    ((Fin.appendEquiv (j.val + 1) (N - j.val)).symm.trans
      ((Fin.succFunEquiv X j.val).prodCongr (Equiv.refl _)))).trans
    ((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))

theorem splitAtColumn_prefix {N : ℕ} {X : Type*} (j : Fin (N + 1)) (x : Fin (N + 1) → X) :
    (splitAtColumn X j x).1 = x ∘ Fin.castLE (Nat.le_of_lt j.isLt) := by
  funext i
  rfl

theorem splitAtColumn_next {N : ℕ} {X : Type*} (j : Fin (N + 1)) (x : Fin (N + 1) → X) :
    (splitAtColumn X j x).2.2 = x j := by
  rfl

/-- An event determined by a prefix and its next entry can be bounded by
uniform estimates for the next entry with the prefix fixed. -/
theorem uniformOn_prefix_next_le {N : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (j : Fin (N + 1))
    (P : (Fin j.val → X) → X → Prop) (q : ℝ)
    (h : ∀ x, (uniformOn Set.univ).real {y : X | P x y} ≤ q) :
    (uniformOn Set.univ).real
      {x : Fin (N + 1) → X | P (x ∘ Fin.castLE (Nat.le_of_lt j.isLt)) (x j)} ≤ q := by
  let e := splitAtColumn X j
  let s : Set ((Fin j.val → X) × (Fin (N - j.val) → X) × X) := {z | P z.1 z.2.2}
  have hmap : (uniformOn Set.univ).real (e ⁻¹' s) = (uniformOn Set.univ).real s := by
    simp only [measureReal_def]
    congr 1
    rw [← map_uniformOn_univ_of_equiv e, Measure.map_apply (measurable_of_finite _) (Set.toFinite s).measurableSet]
  have hs : e ⁻¹' s = {x : Fin (N + 1) → X | P (x ∘ Fin.castLE (Nat.le_of_lt j.isLt)) (x j)} := by
    ext x
    simp only [Set.mem_preimage, s, e, Set.mem_ofPred_eq, splitAtColumn_prefix, splitAtColumn_next]
  rw [← hs, hmap]
  exact uniformOn_product_of_fiber_le (fun x (z : (Fin (N - j.val) → X) × X) => P x z.2) q fun x =>
    uniformOn_product_of_fiber_le (fun (_ : Fin (N - j.val) → X) y => P x y) q fun _ => h x

/-- The prefix span can also be represented by the first entries indexed by a smaller `Fin`. -/
theorem prefixSpan_castLE {N j : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (X : Fin (N + 1) → V) (h : j ≤ N + 1) :
    prefixSpan (K := K) X j = span K (range (X ∘ Fin.castLE h)) := by
  unfold prefixSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.castLE h i, i.isLt, rfl⟩

/-- Associate the integer zero-one matrix to a list of binary columns. -/
@[expose] def binaryMatrixOfColumns {N j : ℕ} (X : Fin j → Fin N → Bool) :
    Matrix (Fin N) (Fin j) ℤ :=
  Matrix.of fun i j => zeroOneBit (X j i)

theorem rank_binaryMatrixOfColumns {N j : ℕ} (X : Fin j → Fin N → Bool) {K : Type*} [Field K] :
    ((binaryMatrixOfColumns X).map (fun x : ℤ => (x : K))).rank =
      Module.finrank K (span K (range (binaryColumn K ∘ X))) := by
  have hc : ((binaryMatrixOfColumns X).map (fun x : ℤ => (x : K))).col = binaryColumn K ∘ X := by
    funext k i
    cases h : X k i <;> simp [binaryMatrixOfColumns, binaryColumn, zeroOneBit, h, Matrix.col]
  rw [Matrix.rank_eq_finrank_span_cols, hc]


/-- Primes worth checking after a fixed prefix are divisors of one
nonzero integer minor determined by that prefix. -/
noncomputable def prefixPrimeCandidates {N j : ℕ} (a : ℕ) (R : Fin j → Fin N → Bool) : Finset ℕ :=
  open Classical in
  if h : ((binaryMatrixOfColumns R).map (fun x : ℤ => (x : ℚ))).rank = j then
    (fullColumnMinor (binaryMatrixOfColumns R) h).natAbs.primeFactors.filter (fun p => a < p)
  else ∅

theorem mem_prefixPrimeCandidates_of_modular_rank_loss {N j a p : ℕ}
    (R : Fin j → Fin N → Bool) (hp : p.Prime) (ha : a < p)
    (hQ : ((binaryMatrixOfColumns R).map (fun x : ℤ => (x : ℚ))).rank = j)
    (hp' : ((binaryMatrixOfColumns R).map (fun x : ℤ => (x : ZMod p))).rank < j) :
    p ∈ prefixPrimeCandidates a R := by
  have hdiv := prime_dvd_fullColumnMinor_of_modular_rank_loss hp _ hQ hp'
  have hn : (fullColumnMinor (binaryMatrixOfColumns R) hQ).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (fullColumnMinor_ne_zero hQ)
  simp [prefixPrimeCandidates, hQ, Nat.mem_primeFactors, hp, hdiv, hn, ha]

theorem prime_of_mem_prefixPrimeCandidates {N j a p : ℕ}
    {R : Fin j → Fin N → Bool} (hp : p ∈ prefixPrimeCandidates a R) : p.Prime ∧ a < p := by
  unfold prefixPrimeCandidates at hp
  split at hp
  · exact ⟨(Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩
  · exact False.elim (Finset.notMem_empty p hp)

/-- Their product bounds the count of distinct prime factors beyond an exponential cut. -/
theorem card_large_prime_factors_le_log (x : ℝ) (D : ℕ) (hD : D ≠ 0) :
    ((D.primeFactors.filter (fun p => ⌊Real.exp x⌋₊ < p)).card : ℝ) * x ≤ Real.log (D : ℝ) := by
  let s := D.primeFactors.filter (fun p => ⌊Real.exp x⌋₊ < p)
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
  have hdiv : ∏ p ∈ s, p ∣ D :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd _)
  have hle : ∏ p ∈ s, (p : ℝ) ≤ (D : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hdiv
  have hprod : 0 < ∏ p ∈ s, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hs p hp).pos
  calc
    _ = ∑ _p ∈ s, x := by simp [s]
    _ ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum fun p hp => ?_
      exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast (hs p hp).pos)).2
        (Nat.lt_of_floor_lt (Finset.mem_filter.mp hp).2)).le
    _ = Real.log (∏ p ∈ s, (p : ℝ)) := (Real.log_prod fun p hp =>
      ne_of_gt (by exact_mod_cast (hs p hp).pos)).symm
    _ ≤ _ := Real.log_le_log hprod hle

/-- A determinant bound controls the number of candidate primes beyond an exponential cutoff. -/
theorem prefixPrimeCandidates_card_le_log_cutoff {N j : ℕ} (hN : 0 < N) (hj : j ≤ N)
    {x : ℝ} (hx : 0 < x) (R : Fin j → Fin N → Bool) :
    ((prefixPrimeCandidates ⌊Real.exp x⌋₊ R).card : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) / x := by
  unfold prefixPrimeCandidates
  split
  · rename_i hQ
    let D := (fullColumnMinor (binaryMatrixOfColumns R) hQ).natAbs
    have hD : D ≠ 0 := Int.natAbs_ne_zero.mpr (fullColumnMinor_ne_zero hQ)
    have hm : |fullColumnMinor (binaryMatrixOfColumns R) hQ| ≤ (j.factorial : ℤ) := by
      apply abs_fullColumnMinor_le_factorial
      intro i k
      cases h : R k i <;> norm_num [binaryMatrixOfColumns, zeroOneBit, h]
    have hDfac : D ≤ j.factorial := by
      have hm' : (D : ℤ) ≤ (j.factorial : ℤ) := by simpa only [D, Int.natCast_natAbs] using hm
      exact_mod_cast hm'
    have hDN : D ≤ N ^ N := hDfac.trans
      ((Nat.factorial_le_pow j).trans
        ((Nat.pow_le_pow_left hj _).trans (Nat.pow_le_pow_right hN hj)))
    have hlog : Real.log (D : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD) (by exact_mod_cast hDN)
    exact (le_div_iff₀ hx).2 ((card_large_prime_factors_le_log x D hD).trans hlog)
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) hx.le



/-- The exponential cutoff leaves logarithmically many candidate primes. -/
theorem prefixPrimeCandidates_card_le {N j : ℕ} (hN : 0 < N) (hj : j ≤ N)
    {δ : ℝ} (hδ : 0 < δ) (R : Fin j → Fin N → Bool) :
    ((prefixPrimeCandidates ⌊Real.exp (δ * (N : ℝ))⌋₊ R).card : ℝ) ≤ Real.log (N : ℝ) / δ := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have h := prefixPrimeCandidates_card_le_log_cutoff hN hj (mul_pos hδ hn) R
  rw [mul_comm δ, mul_div_mul_left] at h
  · simpa only [mul_comm (N : ℝ) δ] using h
  · exact hn.ne'

/-- A lower cutoff of two still leaves no more than order `N log N` primes. -/
theorem prefixPrimeCandidates_card_le_all {N j a : ℕ} (hN : 0 < N) (hj : j ≤ N) (ha : 2 ≤ a)
    (R : Fin j → Fin N → Bool) :
    ((prefixPrimeCandidates a R).card : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) / Real.log 2 := by
  have hs : prefixPrimeCandidates a R ⊆ prefixPrimeCandidates 2 R := by
    unfold prefixPrimeCandidates
    split
    · intro p hp
      obtain ⟨hm, hp'⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hm, ha.trans_lt hp'⟩
    · exact Finset.empty_subset _
  have hcut : ⌊Real.exp (Real.log 2)⌋₊ = 2 := by rw [Real.exp_log (by norm_num)]; norm_num
  have h := prefixPrimeCandidates_card_le_log_cutoff hN hj (Real.log_pos (by norm_num : (1 : ℝ) < 2)) R
  rw [hcut] at h
  exact (show ((prefixPrimeCandidates a R).card : ℝ) ≤ (prefixPrimeCandidates 2 R).card by
    exact_mod_cast Finset.card_le_card hs).trans h

/-- No proper subspace containing the prefix captures too much binary
mass, simultaneously at all primes beyond the cutoff. -/
@[expose] def BinaryPrefixControl {N m : ℕ} (cutoff : ℕ) (q : ℝ)
    (R : Fin m → Fin N → Bool) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), cutoff < p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ V : Submodule (ZMod p) (Fin N → ZMod p), V ≠ ⊤ →
      (∀ i, binaryColumn (ZMod p) (R i) ∈ V) →
      (uniformOn Set.univ).real {x : Fin N → Bool | binaryColumn (ZMod p) x ∈ V} ≤ q

private def exposedColumnFails {N j : ℕ} (R : Fin j → Fin N → Bool) (p : ℕ)
    (x : Fin N → Bool) : Prop :=
  ∃ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    let V := span (ZMod p) (range (binaryColumn (ZMod p) ∘ R))
    V ≠ ⊤ ∧ binaryColumn (ZMod p) x ∈ V

private def exposureEvent {N j : ℕ} (cutoff m : ℕ) (q : ℝ) (C : Finset ℕ)
    (R : Fin j → Fin N → Bool) (x : Fin N → Bool) : Prop :=
  (∀ h : m ≤ j, BinaryPrefixControl cutoff q (R ∘ Fin.castLE h)) ∧
    ∃ p ∈ C, exposedColumnFails R p x

private theorem exposureEvent_mass_le {N j m cutoff : ℕ}
    (q : ℝ) (hq : 0 ≤ q) (C : Finset ℕ) (hpr : ∀ p ∈ C, p.Prime ∧ cutoff < p)
    (R : Fin j → Fin N → Bool) :
    (uniformOn Set.univ).real {x : Fin N → Bool | exposureEvent cutoff m q C R x} ≤
      (C.card : ℝ) * ((1 / 2 : ℝ) ^ (N - m) + q) := by
  classical
  let μ := uniformOn (Set.univ : Set (Fin N → Bool))
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let P : Prop := ∀ h : m ≤ j, BinaryPrefixControl cutoff q (R ∘ Fin.castLE h)
  let F (p : ℕ) : Set (Fin N → Bool) := {x | exposedColumnFails R p x}
  by_cases hP : P
  · have hcover : {x : Fin N → Bool | exposureEvent cutoff m q C R x} ⊆ ⋃ p ∈ C, F p := by
      intro x hx
      obtain ⟨_, p, hp, h⟩ := hx
      exact mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨hp, h⟩⟩
    have hf (p : ℕ) (hp : p ∈ C) : μ.real (F p) ≤ (1 / 2 : ℝ) ^ (N - m) + q := by
      obtain ⟨hprime, hcut⟩ := hpr p hp
      let : Fact p.Prime := ⟨hprime⟩
      let V := span (ZMod p) (range (binaryColumn (ZMod p) ∘ R))
      by_cases hV : V = ⊤
      · have hE : F p = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro x hx
          obtain ⟨hp', htop, _⟩ := hx
          exact htop hV
        rw [hE, measureReal_empty]
        positivity
      · have hF : F p ⊆ {x | binaryColumn (ZMod p) x ∈ V} := by
          intro x hx
          obtain ⟨hp', _, hx⟩ := hx
          exact hx
        apply (measureReal_mono hF).trans
        by_cases hjm : j ≤ m
        · have hd : Module.finrank (ZMod p) V ≤ j := by
            rw [show Module.finrank (ZMod p) V =
              ((binaryMatrixOfColumns R).map (fun x : ℤ => (x : ZMod p))).rank
              from (rank_binaryMatrixOfColumns R).symm]
            exact Matrix.rank_le_width _
          refine (binaryColumn_mass_in_subspace_le V).trans ?_
          have hpow : (1 / 2 : ℝ) ^ (N - Module.finrank (ZMod p) V) ≤ (1 / 2 : ℝ) ^ (N - m) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le_sub_left (hd.trans hjm) N)
          exact hpow.trans (le_add_of_nonneg_right hq)
        · have hml := Nat.le_of_not_ge hjm
          have hc := hP hml p hprime hcut V hV
            (fun i => subset_span (mem_range_self (Fin.castLE hml i)))
          exact hc.trans (le_add_of_nonneg_left (by positivity))
    calc
      _ ≤ μ.real (⋃ p ∈ C, F p) := measureReal_mono hcover (h₂ := measure_ne_top _ _)
      _ ≤ ∑ p ∈ C, μ.real (F p) := measureReal_biUnion_finset_le C F
      _ ≤ ∑ _p ∈ C, ((1 / 2 : ℝ) ^ (N - m) + q) := Finset.sum_le_sum hf
      _ = _ := by simp [mul_add]
  · have he : {x : Fin N → Bool | exposureEvent cutoff m q C R x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      exact fun x hx => hP hx.1
    rw [he, measureReal_empty]
    positivity


/-- The first square block of binary columns is singular over the rationals. -/
@[expose] def BinarySeedFailure {N : ℕ} (X : Fin N → Fin N → Bool) : Prop :=
  ¬ LinearIndependent ℚ (binaryColumn ℚ ∘ X)

private theorem deficient_columns_of_cokernel_prime {N p : ℕ} (hp : p.Prime)
    (X : Fin (N + 1) → Fin N → Bool)
    (hd : p ∣ binaryCokernelIndex (fun i j => X j i)) :
    letI : Fact p.Prime := ⟨hp⟩
    Module.finrank (ZMod p) (span (ZMod p) (range (binaryColumn (ZMod p) ∘ X))) < N := by
  let : Fact p.Prime := ⟨hp⟩
  have hd' : ¬ Surjective ((binaryMatrixOfColumns X).map (Int.castRingHom (ZMod p))).mulVecLin :=
    (prime_dvd_index_iff_not_surjective_mod hp (binaryMatrixOfColumns X)).1 hd
  have htop : LinearMap.range ((binaryMatrixOfColumns X).map (Int.castRingHom (ZMod p))).mulVecLin
      ≠ ⊤ := fun h => hd' (LinearMap.range_eq_top.mp h)
  change Module.finrank (ZMod p) (span (ZMod p) (range (binaryColumn (ZMod p) ∘ X))) < N
  rw [← rank_binaryMatrixOfColumns]
  exact (Submodule.finrank_lt htop).trans_eq (by simp)

private theorem prefix_full_rank_of_seed_independent {N : ℕ}
    (X : Fin (N + 1) → Fin N → Bool) (j : Fin (N + 1))
    (h : ¬ BinarySeedFailure (X ∘ Fin.castLE (Nat.le_succ N))) :
    ((binaryMatrixOfColumns (X ∘ Fin.castLE (Nat.le_of_lt j.isLt))).map
      (fun x : ℤ => (x : ℚ))).rank = j.val := by
  classical
  have hLI : LinearIndependent ℚ (binaryColumn ℚ ∘ X ∘ Fin.castLE (Nat.le_succ N)) :=
    not_not.mp h
  have hj : j.val ≤ N := Nat.le_of_lt_succ j.isLt
  have hL := hLI.comp (Fin.castLE hj) (Fin.castLE_injective hj)
  have hfun :
      (binaryColumn ℚ ∘ X ∘ Fin.castLE (Nat.le_succ N)) ∘ Fin.castLE hj =
      binaryColumn ℚ ∘ (X ∘ Fin.castLE (Nat.le_of_lt j.isLt)) := by
    funext i
    rfl
  rw [hfun] at hL
  rw [rank_binaryMatrixOfColumns, finrank_span_eq_card hL, Fintype.card_fin]

/-- The second failed column witnesses a prime in a finite list
determined by the exposed prefix. A union bound finishes the sieve. -/
theorem large_prime_probability_le_exposure_of_candidate_bound {N m cutoff : ℕ} (hm : m ≤ N)
    {L q : ℝ} (hq : 0 ≤ q)
    (hCandidates : ∀ j ≤ N, ∀ R : Fin j → Fin N → Bool,
      ((prefixPrimeCandidates cutoff R).card : ℝ) ≤ L) :
    (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
      hasLargePrimeDivisor cutoff (binaryCokernelIndex B)} ≤
        (uniformOn Set.univ).real {X : Fin (N + 1) → Fin N → Bool |
          BinarySeedFailure (X ∘ Fin.castLE (Nat.le_succ N))} +
        (uniformOn Set.univ).real {X : Fin (N + 1) → Fin N → Bool |
          ¬ BinaryPrefixControl cutoff q (X ∘ Fin.castLE (hm.trans (Nat.le_succ N)))} +
        ((N + 1 : ℕ) : ℝ) * (L * ((1 / 2 : ℝ) ^ (N - m) + q)) := by
  classical
  let Ω := Fin (N + 1) → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let : IsProbabilityMeasure μ := by dsimp [μ, Ω]; infer_instance
  let Large : Set (Fin N → Fin (N + 1) → Bool) :=
    {B | hasLargePrimeDivisor cutoff (binaryCokernelIndex B)}
  let e : Ω ≃ (Fin N → Fin (N + 1) → Bool) :=
    Equiv.piComm (fun (_ : Fin (N + 1)) (_ : Fin N) => Bool)
  let D := e ⁻¹' Large
  let S : Set Ω := {X | BinarySeedFailure (X ∘ Fin.castLE (Nat.le_succ N))}
  let P : Set Ω := {X | ¬ BinaryPrefixControl cutoff q (X ∘ Fin.castLE (hm.trans (Nat.le_succ N)))}
  let A (j : Fin (N + 1)) : Set Ω :=
    {X | let R := X ∘ Fin.castLE (Nat.le_of_lt j.isLt)
      exposureEvent cutoff m q (prefixPrimeCandidates cutoff R) R (X j)}
  let Q := L * ((1 / 2 : ℝ) ^ (N - m) + q)
  have hmass : (uniformOn Set.univ).real Large = μ.real D := by
    simp only [measureReal_def]
    congr 1
    rw [show μ = uniformOn (Set.univ : Set Ω) from rfl, ← map_uniformOn_univ_of_equiv e,
      Measure.map_apply (measurable_of_finite _) (Set.toFinite Large).measurableSet]
  have hcover : D ⊆ S ∪ P ∪ ⋃ j, A j := by
    intro X hX
    by_cases hS : X ∈ S
    · exact Or.inl (Or.inl hS)
    by_cases hP : X ∈ P
    · exact Or.inl (Or.inr hP)
    obtain ⟨p, hp, ha, hd⟩ := hX
    let : Fact p.Prime := ⟨hp⟩
    have hdim := deficient_columns_of_cokernel_prime hp X hd
    obtain ⟨j, hj, hx⟩ := exists_second_failed_column (binaryColumn (ZMod p) ∘ X) hdim
    let R := X ∘ Fin.castLE (Nat.le_of_lt j.isLt)
    let V := span (ZMod p) (range (binaryColumn (ZMod p) ∘ R))
    have hV : prefixSpan (K := ZMod p) (binaryColumn (ZMod p) ∘ X) j.val = V :=
      prefixSpan_castLE _ _
    have hQ := prefix_full_rank_of_seed_independent X j hS
    have hmod : ((binaryMatrixOfColumns R).map (fun x : ℤ => (x : ZMod p))).rank < j.val := by
      rw [rank_binaryMatrixOfColumns]
      change Module.finrank (ZMod p) V < j.val
      rw [hV] at hj
      omega
    have hc := mem_prefixPrimeCandidates_of_modular_rank_loss R hp ha hQ hmod
    have hVt : V ≠ ⊤ := by
      intro ht
      rw [hV, ht, finrank_top] at hj
      have hfin : Module.finrank (ZMod p) (Fin N → ZMod p) = N := by simp
      rw [hfin] at hj
      have := j.isLt
      omega
    refine Or.inr (mem_iUnion.2 ⟨j, ?_⟩)
    change (∀ h : m ≤ j.val, BinaryPrefixControl cutoff q (R ∘ Fin.castLE h)) ∧
      ∃ p ∈ prefixPrimeCandidates cutoff R, exposedColumnFails R p (X j)
    refine ⟨fun h => ?_, p, hc, hp, hVt, ?_⟩
    · exact not_not.mp hP
    · change binaryColumn (ZMod p) (X j) ∈ V
      rwa [← hV]
  have hA (j : Fin (N + 1)) : μ.real (A j) ≤ Q := by
    apply uniformOn_prefix_next_le j (fun R => exposureEvent cutoff m q (prefixPrimeCandidates cutoff R) R) Q
    intro R
    exact (exposureEvent_mass_le q hq _ (fun _ => prime_of_mem_prefixPrimeCandidates) R).trans
      (mul_le_mul_of_nonneg_right (hCandidates j.val (Nat.le_of_lt_succ j.isLt) R) (by positivity))
  change (uniformOn Set.univ).real Large ≤ μ.real S + μ.real P + ((N + 1 : ℕ) : ℝ) * Q
  calc
    _ = μ.real D := hmass
    _ ≤ μ.real (S ∪ P ∪ ⋃ j, A j) := measureReal_mono hcover (h₂ := measure_ne_top _ _)
    _ ≤ μ.real (S ∪ P) + μ.real (⋃ j, A j) := measureReal_union_le _ _
    _ ≤ μ.real S + μ.real P + ∑ j, μ.real (A j) :=
      add_le_add (measureReal_union_le _ _) (measureReal_iUnion_fintype_le A)
    _ ≤ μ.real S + μ.real P + ∑ _j : Fin (N + 1), Q :=
      add_le_add le_rfl (Finset.sum_le_sum fun j _ => hA j)
    _ = _ := by simp


/-- Coordinate restriction along an embedding preserves the uniform tuple law. -/
theorem uniformOn_restrict_real {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω] [Nonempty Ω]
    (e : κ ↪ ι) (E : Set (κ → Ω)) :
    (uniformOn Set.univ).real ((fun (x : ι → Ω) j => x (e j)) ⁻¹' E) =
      (uniformOn Set.univ).real E := by
  classical
  simp only [measureReal_def]
  congr 1
  rw [← Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet,
    ← pi_uniformOn_univ, pi_map_restrict_embedding (uniformOn (Set.univ : Set Ω)) e,
    pi_uniformOn_univ]

private theorem rank_zmod_le_rat {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) (p : ℕ) [Fact p.Prime] :
    (A.map (fun x : ℤ => (x : ZMod p))).rank ≤ (A.map (fun x : ℤ => (x : ℚ))).rank := by
  obtain ⟨r, c, h⟩ := exists_rank_minor (A.map (fun x : ℤ => (x : ZMod p)))
  have hn : (A.submatrix r c).det ≠ 0 := by
    intro hz
    apply h
    change ((A.submatrix r c).map (fun x : ℤ => (x : ZMod p))).det = 0
    rw [← Int.cast_det, hz, Int.cast_zero]
  have hQ : ((A.map (fun x : ℤ => (x : ℚ))).submatrix r c).det ≠ 0 := by
    change ((A.submatrix r c).map (fun x : ℤ => (x : ℚ))).det ≠ 0
    rwa [← Int.cast_det, ne_eq, Int.cast_eq_zero]
  simpa only [rank_of_det_ne_zero hQ, Fintype.card_fin] using
    (A.map (fun x : ℤ => (x : ℚ))).rank_submatrix_le r c

private theorem exists_first_failed_column {N : ℕ} {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (X : Fin (N + 1) → V) (h : Module.finrank K (prefixSpan (K := K) X N) < N) :
    ∃ j : Fin (N + 1), j.val < N ∧ X j ∈ prefixSpan (K := K) X j.val := by
  by_contra hnone
  have hr (k : ℕ) (hk : k ≤ N) : Module.finrank K (prefixSpan (K := K) X k) = k := by
    induction k with
    | zero => simp [prefixSpan_zero]
    | succ k ih =>
      let j : Fin (N + 1) := ⟨k, by omega⟩
      have hmem : X j ∉ prefixSpan (K := K) X k := fun hmem => hnone ⟨j, by change k < N; omega, hmem⟩
      change Module.finrank K (prefixSpan (K := K) X (j.val + 1)) = j.val + 1
      rw [prefixSpan_succ, finrank_sup_span_singleton hmem, ih (by omega)]
  rw [hr N le_rfl] at h
  exact (Nat.lt_irrefl N) h

/-- The same prefix condition also bounds a rationally singular square seed.
It suffices to expose columns at any one prime above the cutoff. -/
theorem binarySeedFailure_probability_le_exposure {N m cutoff : ℕ} (hm : m ≤ N)
    {q : ℝ} (hq : 0 ≤ q) :
    (uniformOn Set.univ).real {X : Fin (N + 1) → Fin N → Bool |
      BinarySeedFailure (X ∘ Fin.castLE (Nat.le_succ N))} ≤
      (uniformOn Set.univ).real {X : Fin (N + 1) → Fin N → Bool |
        ¬ BinaryPrefixControl cutoff q (X ∘ Fin.castLE (hm.trans (Nat.le_succ N)))} +
        ((N + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (N - m) + q) := by
  classical
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (cutoff + 1)
  have hcut : cutoff < p := by omega
  let : Fact p.Prime := ⟨hp⟩
  let Ω := Fin (N + 1) → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let : IsProbabilityMeasure μ := by dsimp [μ, Ω]; infer_instance
  let S : Set Ω := {X | BinarySeedFailure (X ∘ Fin.castLE (Nat.le_succ N))}
  let P : Set Ω := {X | ¬ BinaryPrefixControl cutoff q (X ∘ Fin.castLE (hm.trans (Nat.le_succ N)))}
  let A (j : Fin (N + 1)) : Set Ω :=
    {X | exposureEvent cutoff m q {p} (X ∘ Fin.castLE (Nat.le_of_lt j.isLt)) (X j)}
  let Q := (1 / 2 : ℝ) ^ (N - m) + q
  have hcover : S ⊆ P ∪ ⋃ j, A j := by
    intro X hX
    by_cases hP : X ∈ P
    · exact Or.inl hP
    let R := X ∘ Fin.castLE (Nat.le_succ N)
    let Y := binaryColumn (ZMod p) ∘ X
    have hQ : ((binaryMatrixOfColumns R).map (fun x : ℤ => (x : ℚ))).rank < N := by
      refine lt_of_le_of_ne (Matrix.rank_le_width _) (fun he => hX ?_)
      rw [rank_binaryMatrixOfColumns] at he
      apply (linearIndependent_iff_card_eq_finrank_span).2
      change Fintype.card (Fin N) = Module.finrank ℚ (span ℚ (range (binaryColumn ℚ ∘ R)))
      rw [Fintype.card_fin, he]
    have hdim : Module.finrank (ZMod p) (prefixSpan (K := ZMod p) Y N) < N := by
      rw [prefixSpan_castLE _ (Nat.le_succ N)]
      change Module.finrank (ZMod p) (span (ZMod p) (range (binaryColumn (ZMod p) ∘ R))) < N
      rw [← rank_binaryMatrixOfColumns]
      exact (rank_zmod_le_rat _ p).trans_lt hQ
    obtain ⟨j, hj, hmem⟩ := exists_first_failed_column Y hdim
    let R' := X ∘ Fin.castLE (Nat.le_of_lt j.isLt)
    let W := span (ZMod p) (range (binaryColumn (ZMod p) ∘ R'))
    have hW : prefixSpan (K := ZMod p) Y j.val = W := prefixSpan_castLE _ _
    have hW' : Module.finrank (ZMod p) W ≤ j.val := by
      change Module.finrank (ZMod p) (span (ZMod p) (range (binaryColumn (ZMod p) ∘ R'))) ≤ j.val
      rw [← rank_binaryMatrixOfColumns]
      exact Matrix.rank_le_width _
    have ht : W ≠ ⊤ := by
      intro ht
      rw [ht, finrank_top] at hW'
      simp only [Module.finrank_pi, Fintype.card_fin] at hW'
      omega
    refine Or.inr (mem_iUnion.2 ⟨j, fun h => not_not.mp hP, p, Finset.mem_singleton_self _, hp, ht, ?_⟩)
    change binaryColumn (ZMod p) (X j) ∈ W
    rwa [← hW]
  have hA (j : Fin (N + 1)) : μ.real (A j) ≤ Q := by
    apply uniformOn_prefix_next_le j (exposureEvent cutoff m q {p}) Q
    intro R
    have hp' (p' : ℕ) (h : p' ∈ ({p} : Finset ℕ)) : p'.Prime ∧ cutoff < p' := by
      rw [Finset.mem_singleton.mp h]
      exact ⟨hp, hcut⟩
    have hR := exposureEvent_mass_le (m := m) q hq {p} hp' R
    simpa only [Finset.card_singleton, Nat.cast_one, one_mul] using hR
  change μ.real S ≤ μ.real P + ((N + 1 : ℕ) : ℝ) * Q
  calc
    _ ≤ μ.real (P ∪ ⋃ j, A j) := measureReal_mono hcover (h₂ := measure_ne_top _ _)
    _ ≤ μ.real P + μ.real (⋃ j, A j) := measureReal_union_le _ _
    _ ≤ μ.real P + ∑ j, μ.real (A j) := add_le_add le_rfl (measureReal_iUnion_fintype_le A)
    _ ≤ μ.real P + ∑ _j : Fin (N + 1), Q := add_le_add le_rfl (Finset.sum_le_sum fun j _ => hA j)
    _ = _ := by simp

/-- Large prime divisibility is bounded by the bad prefix probability and
the sum of the two column exposure bounds. -/
theorem large_prime_probability_le_prefix_failure_of_candidate_bound {N m cutoff : ℕ} (hm : m ≤ N)
    {L q : ℝ} (hq : 0 ≤ q)
    (hCandidates : ∀ j ≤ N, ∀ R : Fin j → Fin N → Bool,
      ((prefixPrimeCandidates cutoff R).card : ℝ) ≤ L) :
    (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
      hasLargePrimeDivisor cutoff (binaryCokernelIndex B)} ≤
      2 * (uniformOn Set.univ).real {R : Fin m → Fin N → Bool | ¬ BinaryPrefixControl cutoff q R} +
        ((N + 1 : ℕ) : ℝ) * (L + 1) * ((1 / 2 : ℝ) ^ (N - m) + q) := by
  let Ω := Fin (N + 1) → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let S : Set Ω := {X | BinarySeedFailure (X ∘ Fin.castLE (Nat.le_succ N))}
  let P : Set Ω := {X | ¬ BinaryPrefixControl cutoff q (X ∘ Fin.castLE (hm.trans (Nat.le_succ N)))}
  let D : Set (Fin N → Fin (N + 1) → Bool) := {B | hasLargePrimeDivisor cutoff (binaryCokernelIndex B)}
  let Q := (1 / 2 : ℝ) ^ (N - m) + q
  let F : Set (Fin m → Fin N → Bool) := {R | ¬ BinaryPrefixControl cutoff q R}
  have hD : (uniformOn Set.univ).real D ≤ μ.real S + μ.real P +
      ((N + 1 : ℕ) : ℝ) * (L * Q) :=
    large_prime_probability_le_exposure_of_candidate_bound hm hq hCandidates
  have hS : μ.real S ≤ μ.real P + ((N + 1 : ℕ) : ℝ) * Q :=
    binarySeedFailure_probability_le_exposure hm hq
  have hP : μ.real P = (uniformOn Set.univ).real F :=
    uniformOn_restrict_real ⟨Fin.castLE (hm.trans (Nat.le_succ N)), Fin.castLE_injective _⟩ F
  change (uniformOn Set.univ).real D ≤ 2 * (uniformOn Set.univ).real F +
    ((N + 1 : ℕ) : ℝ) * (L + 1) * Q
  rw [← hP]
  calc
    _ ≤ (μ.real P + ((N + 1 : ℕ) : ℝ) * Q) + μ.real P +
        ((N + 1 : ℕ) : ℝ) * (L * Q) :=
      hD.trans (add_le_add (add_le_add hS le_rfl) le_rfl)
    _ = _ := by ring

/-- Large prime divisibility is bounded by the bad prefix probability and
the sum of the two column exposure bounds. -/
theorem large_prime_probability_le_prefix_failure {N m : ℕ} (hN : 0 < N) (hm : m ≤ N)
    {δ q : ℝ} (hδ : 0 < δ) (hq : 0 ≤ q) :
    let cutoff := ⌊Real.exp (δ * (N : ℝ))⌋₊
    (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
      hasLargePrimeDivisor cutoff (binaryCokernelIndex B)} ≤
      2 * (uniformOn Set.univ).real {R : Fin m → Fin N → Bool | ¬ BinaryPrefixControl cutoff q R} +
        ((N + 1 : ℕ) : ℝ) * (Real.log (N : ℝ) / δ + 1) * ((1 / 2 : ℝ) ^ (N - m) + q) :=
  large_prime_probability_le_prefix_failure_of_candidate_bound hm hq
    (fun _ hj => prefixPrimeCandidates_card_le hN hj hδ)

end BooleanThreshold
