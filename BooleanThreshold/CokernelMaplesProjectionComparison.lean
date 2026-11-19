module

public import BooleanThreshold.CokernelMaplesPrefix
public import BooleanThreshold.CokernelMaplesReduction

public noncomputable section

open Function Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace BooleanThreshold

private theorem finiteEventProbability_nonneg {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    0 ≤ finiteEventProbability P := by
  rw [finiteEventProbability_eq_fraction]
  unfold finiteUniformFraction
  positivity

private theorem finiteEventProbability_le_one {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    finiteEventProbability P ≤ 1 := by
  rw [finiteEventProbability_eq_fraction]
  unfold finiteUniformFraction
  have hcard : (Nat.card (Subtype P) : ℝ) ≤ Nat.card Ω := by
    exact_mod_cast Nat.card_le_card_of_injective (fun (x : Subtype P) => x.val) Subtype.val_injective
  exact (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)).trans (div_self_le_one _)

private theorem abs_prod_sub_prod_le {I : Type*} (s : Finset I) (f g : I → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - (∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    let F := ∏ j ∈ s, f j
    let G := ∏ j ∈ s, g j
    have hF₀ : 0 ≤ F := Finset.prod_nonneg fun j _ => (hf j).1
    have hF₁ : F ≤ 1 := Finset.prod_le_one₀ (fun j _ => (hf j).1) (fun j _ => (hf j).2)
    calc
      _ = |(f i - g i) * F + g i * (F - G)| := by
        change |f i * F - g i * G| = _
        congr 1
        ring
      _ ≤ |(f i - g i) * F| + |g i * (F - G)| := abs_add_le _ _
      _ = |f i - g i| * F + g i * |F - G| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hF₀, abs_of_nonneg (hg i).1]
      _ ≤ |f i - g i| * 1 + 1 * |F - G| :=
        add_le_add (mul_le_mul_of_nonneg_left hF₁ (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hg i).2 (abs_nonneg _))
      _ ≤ _ := by
        rw [mul_one, one_mul]
        exact add_le_add_right ih _

/-- Pointwise errors between two finite laws control every event in their
independent products. -/
theorem finiteEventProbability_iid_map_abs_sub_le {I Ω Γ V : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype Γ] [Fintype V] (f : Ω → V) (g : Γ → V)
    (P : (I → V) → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hAtom : ∀ y, |finiteEventProbability (fun x => f x = y) -
      finiteEventProbability (fun x => g x = y)| ≤ ε) :
    |finiteEventProbability (fun X : I → Ω => P (f ∘ X)) -
      finiteEventProbability (fun X : I → Γ => P (g ∘ X))| ≤
      (Fintype.card I : ℝ) * (Fintype.card V : ℝ) ^ Fintype.card I * ε := by
  let S : Finset (I → V) := Finset.univ.filter P
  let F (X : I → Ω) := f ∘ X
  let G (X : I → Γ) := g ∘ X
  have hp (y : I → V) : |finiteEventProbability (fun X => F X = y) -
      finiteEventProbability (fun X => G X = y)| ≤ (Fintype.card I : ℝ) * ε := by
    have hF : (fun X => F X = y) = (fun X : I → Ω => ∀ i, f (X i) = y i) :=
      funext fun _ => propext funext_iff
    have hG : (fun X => G X = y) = (fun X : I → Γ => ∀ i, g (X i) = y i) :=
      funext fun _ => propext funext_iff
    rw [hF, hG, finiteEventProbability_pi (fun (i : I) (x : Ω) => f x = y i),
      finiteEventProbability_pi (fun (i : I) (x : Γ) => g x = y i)]
    let u (i : I) := finiteEventProbability (fun x => f x = y i)
    let v (i : I) := finiteEventProbability (fun x => g x = y i)
    have h := abs_prod_sub_prod_le Finset.univ u v
      (fun _ => ⟨finiteEventProbability_nonneg _, finiteEventProbability_le_one _⟩)
      (fun _ => ⟨finiteEventProbability_nonneg _, finiteEventProbability_le_one _⟩)
    refine h.trans ?_
    calc
      _ ≤ ∑ _i : I, ε := Finset.sum_le_sum fun i _ => hAtom (y i)
      _ = _ := by simp
  have hcmp := finiteEventProbability_classes_abs_sub_le F G S (fun y _ => hp y)
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hcmp
  have hcard : (S.card : ℝ) ≤ (Fintype.card V : ℝ) ^ Fintype.card I := by
    have h : S.card ≤ Fintype.card (I → V) := Finset.card_le_univ S
    rw [Fintype.card_fun] at h
    exact_mod_cast h
  refine hcmp.trans ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq ?_)
  ring

theorem finiteEventProbability_uniform_zmod_column_eq {k q : ℕ} [NeZero q]
    (y : Fin k → ZMod q) :
    finiteEventProbability (fun x : Fin k → ZMod q => x = y) = 1 / (q : ℝ) ^ k := by
  let : Nonempty {x // x = y} := ⟨⟨y, rfl⟩⟩
  let : Subsingleton {x // x = y} :=
    ⟨fun x z => Subtype.ext (x.property.trans z.property.symm)⟩
  rw [finiteEventProbability_eq_fraction, finiteUniformFraction, Nat.card_unique, Nat.cast_one,
    Nat.card_fun, Nat.card_fin, Nat.card_zmod, Nat.cast_pow]

/-- An almost-uniform projection of each binary suffix column gives an additive
error bound for the determinant-zero probability of the completed matrix. -/
theorem binarySuffix_det_zero_comparison {N m k q : ℕ} [NeZero q] (h : m + k = N)
    (A : Matrix (Fin N) (Fin m) (ZMod q)) (P : (Fin N → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q))
    (hDet : ∀ X : Fin k → Fin N → ZMod q,
      (appendMatrixColumns h A X).det = 0 ↔ (Matrix.of (fun i j => P (X j) i)).det = 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hAtom : ∀ y, |finiteEventProbability (fun x : Fin N → Bool => P (binaryColumn (ZMod q) x) = y) -
      1 / (q : ℝ) ^ k| ≤ ε) :
    |finiteEventProbability (fun X : Fin k → Fin N → Bool =>
        (appendMatrixColumns h A (binaryColumn (ZMod q) ∘ X)).det = 0) -
      finiteEventProbability (fun Y : Fin k → Fin k → ZMod q => (Matrix.of Y).det = 0)| ≤
      (k : ℝ) * (q : ℝ) ^ (k * k) * ε := by
  let D (Y : Fin k → Fin k → ZMod q) := (Matrix.of (fun i j => Y j i)).det = 0
  have hD (Y : Fin k → Fin k → ZMod q) : D Y ↔ (Matrix.of Y).det = 0 := by
    change (Matrix.of Y)ᵀ.det = 0 ↔ _
    rw [Matrix.det_transpose]
  have hb : (fun X : Fin k → Fin N → Bool =>
        (appendMatrixColumns h A (binaryColumn (ZMod q) ∘ X)).det = 0) =
      (fun X => D ((P ∘ binaryColumn (ZMod q)) ∘ X)) :=
    funext fun X => propext (hDet (binaryColumn (ZMod q) ∘ X))
  have hAtom' (y : Fin k → ZMod q) :
      |finiteEventProbability (fun x : Fin N → Bool => (P ∘ binaryColumn (ZMod q)) x = y) -
        finiteEventProbability (fun x => id x = y)| ≤ ε := by
    rw [show (fun x => id x = y) = (fun x => x = y) from rfl,
      finiteEventProbability_uniform_zmod_column_eq]
    exact hAtom y
  have hcompare := finiteEventProbability_iid_map_abs_sub_le (P ∘ binaryColumn (ZMod q)) id D hε hAtom'
  rw [hb, ← show D = (fun Y : Fin k → Fin k → ZMod q => (Matrix.of Y).det = 0) from
    funext fun Y => propext (hD Y)]
  simpa only [id_comp, Fintype.card_fin, Fintype.card_fun, ZMod.card, Nat.cast_pow, ← pow_mul]
    using hcompare

/-- With a surjective projection the uniform suffix has exactly the uniform
determinant-zero law in the smaller dimension. -/
theorem uniformSuffix_det_zero_probability {N m k q : ℕ} [NeZero q] (h : m + k = N)
    (A : Matrix (Fin N) (Fin m) (ZMod q)) (P : (Fin N → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q))
    (hP : Surjective P)
    (hDet : ∀ X : Fin k → Fin N → ZMod q,
      (appendMatrixColumns h A X).det = 0 ↔ (Matrix.of (fun i j => P (X j) i)).det = 0) :
    finiteEventProbability (fun X : Fin k → Fin N → ZMod q => (appendMatrixColumns h A X).det = 0) =
      finiteEventProbability (fun Y : Fin k → Fin k → ZMod q => (Matrix.of Y).det = 0) := by
  let D (Y : Fin k → Fin k → ZMod q) := (Matrix.of (fun i j => Y j i)).det = 0
  have hD (Y : Fin k → Fin k → ZMod q) : D Y ↔ (Matrix.of Y).det = 0 := by
    change (Matrix.of Y)ᵀ.det = 0 ↔ _
    rw [Matrix.det_transpose]
  have he : (fun X : Fin k → Fin N → ZMod q => (appendMatrixColumns h A X).det = 0) =
      (fun X => D (P ∘ X)) := funext fun X => propext (hDet X)
  rw [he, ← show D = (fun Y : Fin k → Fin k → ZMod q => (Matrix.of Y).det = 0) from
    funext fun Y => propext (hD Y), finiteEventProbability_eq_fraction, finiteEventProbability_eq_fraction]
  exact finiteUniformFraction_projected_columns P.toAddMonoidHom hP D

private theorem finiteEventProbability_eq_real {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Ω → Prop) :
    finiteEventProbability P = (uniformOn Set.univ).real {x | P x} :=
  finiteAverage_indicator _

private theorem uniformResidueColumn_mass_in_subspace_le {N p q : ℕ} [NeZero q]
    [Fact p.Prime] [MeasurableSpace (ZMod q)] [MeasurableSingletonClass (ZMod q)]
    (hdiv : p ∣ q) (W : Submodule (ZMod p) (Fin N → ZMod p)) :
    (uniformOn Set.univ).real {x : Fin N → ZMod q |
      ZMod.castHom hdiv (ZMod p) ∘ x ∈ W} ≤ (1 / 2 : ℝ) ^ (N - Module.finrank (ZMod p) W) := by
  let red := ZMod.castHom hdiv (ZMod p)
  let F : (Fin N → ZMod q) →+ (Fin N → ZMod p) :=
    AddMonoidHom.pi fun i => red.toAddMonoidHom.comp (Pi.evalAddMonoidHom _ i)
  have hF : Surjective F := by
    intro y
    choose x hx using fun i => ZMod.castHom_surjective hdiv (y i)
    exact ⟨x, funext hx⟩
  rw [← finiteEventProbability_eq_real, finiteEventProbability_eq_fraction,
    show finiteUniformFraction (fun x : Fin N → ZMod q => red ∘ x ∈ W) =
      finiteUniformFraction (fun y : Fin N → ZMod p => y ∈ W) from
        finiteUniformFraction_addHom_preimage F hF _]
  let d := Module.finrank (ZMod p) W
  have hd : d ≤ N := by simpa [d] using W.finrank_le
  have hcard : Nat.card W = p ^ d := by
    have h := Nat.card_congr (Module.finBasis (ZMod p) W).equivFun.toEquiv
    rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
  have hp : p.Prime := Fact.out
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold finiteUniformFraction
  change ((Nat.card W : ℕ) : ℝ) / ((Nat.card (Fin N → ZMod p) : ℕ) : ℝ) ≤
    (1 / 2 : ℝ) ^ (N - d)
  rw [hcard, Nat.card_fun, Nat.card_fin, Nat.card_zmod, Nat.cast_pow, Nat.cast_pow]
  have hsplit : (p : ℝ) ^ N = (p : ℝ) ^ d * (p : ℝ) ^ (N - d) := by
    rw [← pow_add, Nat.add_sub_cancel' hd]
  rw [hsplit]
  calc
    _ = 1 / (p : ℝ) ^ (N - d) := by
      have h := mul_div_mul_left (1 : ℝ) ((p : ℝ) ^ (N - d)) (pow_ne_zero d hp₀.ne')
      simpa only [mul_one] using h
    _ ≤ _ := by
      rw [← one_div_pow]
      exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by norm_num) hp₂) _

/-- A uniform residue matrix has a full-rank early prefix at every prime
factor except with the stated geometric probability. -/
theorem uniformPrefixIndependent_failure_probability_le {N m q : ℕ} [NeZero q] (hm : m ≤ N) :
    finiteEventProbability (fun R : Fin m → Fin N → ZMod q =>
      ¬ modularPrefixIndependent (Matrix.of fun i j => R j i)) ≤
      (q.primeFactors.card : ℝ) * (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
  let : MeasurableSpace (ZMod q) := ⊤
  let : DiscreteMeasurableSpace (ZMod q) := ⟨fun _ => trivial⟩
  rw [finiteEventProbability_eq_real]
  let μ := uniformOn (Set.univ : Set (Fin m → Fin N → ZMod q))
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let E (p : ℕ) : Set (Fin m → Fin N → ZMod q) :=
    {R | ∃ hp : p ∈ q.primeFactors,
      let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      ¬ LinearIndependent (ZMod p) (fun j => ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) ∘ R j)}
  have hcover : {R : Fin m → Fin N → ZMod q |
      ¬ modularPrefixIndependent (Matrix.of (fun i j => R j i))} ⊆ ⋃ p ∈ q.primeFactors, E p := by
    intro R hR
    by_contra h
    apply hR
    intro p hp
    let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    by_contra hdep
    exact h (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hp, hdep⟩⟩)
  calc
    _ ≤ μ.real (⋃ p ∈ q.primeFactors, E p) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ p ∈ q.primeFactors, μ.real (E p) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ q.primeFactors, (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
      apply Finset.sum_le_sum
      intro p hp
      let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      let φ (x : Fin N → ZMod q) := ZMod.castHom (Nat.dvd_of_mem_primeFactors hp) (ZMod p) ∘ x
      have hE : E p = {R | ¬ LinearIndependent (ZMod p) (φ ∘ R)} := by
        ext R
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hp, h⟩⟩
      rw [hE]
      exact uniformColumn_dependence_probability_le φ hm
        (uniformResidueColumn_mass_in_subspace_le (Nat.dvd_of_mem_primeFactors hp))
    _ = _ := by simp [mul_assoc]

private theorem finiteEventProbability_product_eq_average {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : Ω → Γ → Prop) :
    finiteEventProbability (fun x : Ω × Γ => P x.1 x.2) =
      finiteAverage (fun x => finiteEventProbability (P x)) := by
  unfold finiteEventProbability finiteAverage
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, mul_assoc, _root_.mul_inv_rev]

private theorem finiteAverage_add_const {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (c : ℝ) :
    finiteAverage (fun x => f x + c) = finiteAverage f + c := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteAverage, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, add_div, mul_div_cancel_left₀ c hcard]

private theorem finiteEventProbability_product_abs_sub_le_of_good {Ω Γ : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Γ] (P : Ω → Γ → Prop) (Good : Ω → Prop)
    {c ε : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hε : 0 ≤ ε)
    (h : ∀ x, Good x → |finiteEventProbability (P x) - c| ≤ ε) :
    |finiteEventProbability (fun x : Ω × Γ => P x.1 x.2) - c| ≤
      ε + finiteEventProbability (fun x => ¬ Good x) := by
  let f (x : Ω) := finiteEventProbability (P x)
  rw [finiteEventProbability_product_eq_average]
  have hsub : finiteAverage (fun x => f x - c) = finiteAverage f - c := by
    simpa only [sub_eq_add_neg] using finiteAverage_add_const f (-c)
  rw [← hsub]
  calc
    _ ≤ finiteAverage (fun x => |f x - c|) := by
      have hcard : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
      simp only [finiteAverage, abs_div, abs_of_nonneg hcard]
      exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard
    _ ≤ finiteAverage (fun x => (if ¬ Good x then 1 else 0 : ℝ) + ε) := by
      apply finiteAverage_mono
      intro x
      by_cases hx : Good x
      · simpa only [hx, not_true, ite_false, zero_add] using h x hx
      · rw [ite_eq_left hx]
        have hf : |f x - c| ≤ 1 := by
          have hf₀ : 0 ≤ f x := finiteEventProbability_nonneg _
          have hf₁ : f x ≤ 1 := finiteEventProbability_le_one _
          exact abs_le.mpr ⟨by linarith only [hf₀, hc₁], by linarith only [hf₁, hc₀]⟩
        exact hf.trans (le_add_of_nonneg_right hε)
    _ = _ := by
      rw [finiteAverage_add_const, add_comm]
      unfold finiteEventProbability
      apply congrArg (fun g : Ω → ℝ => ε + finiteAverage g)
      funext x
      by_cases hx : Good x <;> simp [hx]

private def splitColumnEquiv {Ω : Type*} {N m k : ℕ} (h : m + k = N) :
    (Fin N → Ω) ≃ (Fin m → Ω) × (Fin k → Ω) :=
  (Equiv.arrowCongr (prefixSuffixIndex h).symm (Equiv.refl Ω)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) Ω)

private theorem splitColumnEquiv_symm_prefix {Ω : Type*} {N m k : ℕ} (h : m + k = N)
    (R : Fin m → Ω) (X : Fin k → Ω) (j : Fin m) :
    (splitColumnEquiv h).symm (R, X) (prefixSuffixIndex h (.inl j)) = R j := by
  change (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) Ω).symm (R, X)
    ((prefixSuffixIndex h).symm (prefixSuffixIndex h (.inl j))) = R j
  simp

private theorem splitColumnEquiv_symm_suffix {Ω : Type*} {N m k : ℕ} (h : m + k = N)
    (R : Fin m → Ω) (X : Fin k → Ω) (j : Fin k) :
    (splitColumnEquiv h).symm (R, X) (prefixSuffixIndex h (.inr j)) = X j := by
  change (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) Ω).symm (R, X)
    ((prefixSuffixIndex h).symm (prefixSuffixIndex h (.inr j))) = X j
  simp

private theorem uniform_det_eq_append {N m k q : ℕ} (h : m + k = N)
    (R : Fin m → Fin N → ZMod q) (X : Fin k → Fin N → ZMod q) :
    (Matrix.of ((splitColumnEquiv h).symm (R, X))).det =
      (appendMatrixColumns h (Matrix.of (fun i j => R j i)) X).det := by
  rw [← Matrix.det_transpose (Matrix.of ((splitColumnEquiv h).symm (R, X)))]
  congr 1
  ext i j
  obtain ⟨l, rfl⟩ := (prefixSuffixIndex h).surjective j
  cases l with
  | inl j => simp [Matrix.transpose_apply, splitColumnEquiv_symm_prefix]
  | inr j => simp [Matrix.transpose_apply, splitColumnEquiv_symm_suffix]

private theorem binary_det_eq_append {N m k q : ℕ} (h : m + k = N)
    (R : Fin m → Fin N → Bool) (X : Fin k → Fin N → Bool) :
    (((Matrix.of ((splitColumnEquiv h).symm (R, X))).map zeroOneBit).map (Int.castRingHom (ZMod q))).det =
      (appendMatrixColumns h ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q)))
        (binaryColumn (ZMod q) ∘ X)).det := by
  rw [← Matrix.det_transpose (((Matrix.of ((splitColumnEquiv h).symm (R, X))).map zeroOneBit).map
    (Int.castRingHom (ZMod q)))]
  congr 1
  ext i j
  obtain ⟨l, rfl⟩ := (prefixSuffixIndex h).surjective j
  cases l with
  | inl j =>
    simp [Matrix.transpose_apply, splitColumnEquiv_symm_prefix, binaryMatrixOfColumns]
  | inr j =>
    cases hx : X j i <;>
      simp [Matrix.transpose_apply, splitColumnEquiv_symm_suffix, binaryColumn, zeroOneBit, hx]

/-- Compare the determinant-zero events of full binary and uniform residue matrices
using an almost-uniform suffix projection on a good set of binary prefixes. -/
theorem binary_uniform_det_zero_comparison_of_projected_suffix {N m k q : ℕ} [NeZero q]
    (h : m + k = N) (Good : (Fin m → Fin N → Bool) → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hGood : ∀ R, Good R →
      ∃ P : (Fin N → ZMod q) →ₗ[ZMod q] (Fin k → ZMod q),
        (∀ X : Fin k → Fin N → ZMod q,
          (appendMatrixColumns h ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q))) X).det = 0 ↔
            (Matrix.of (fun i j => P (X j) i)).det = 0) ∧
        (∀ y, |finiteEventProbability (fun x : Fin N → Bool => P (binaryColumn (ZMod q) x) = y) -
          1 / (q : ℝ) ^ k| ≤ ε)) :
    |finiteEventProbability (fun X : Fin N → Fin N → Bool =>
        (((Matrix.of X).map zeroOneBit).map (Int.castRingHom (ZMod q))).det = 0) -
      finiteEventProbability (fun X : Fin N → Fin N → ZMod q => (Matrix.of X).det = 0)| ≤
      (k : ℝ) * (q : ℝ) ^ (k * k) * ε + finiteEventProbability (fun R => ¬ Good R) +
        (q.primeFactors.card : ℝ) * (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
  let B (R : Fin m → Fin N → Bool) (X : Fin k → Fin N → Bool) :=
    (appendMatrixColumns h ((binaryMatrixOfColumns R).map (Int.castRingHom (ZMod q)))
      (binaryColumn (ZMod q) ∘ X)).det = 0
  let U (R : Fin m → Fin N → ZMod q) (X : Fin k → Fin N → ZMod q) :=
    (appendMatrixColumns h (Matrix.of (fun i j => R j i)) X).det = 0
  let D (Y : Fin k → Fin k → ZMod q) := (Matrix.of Y).det = 0
  let c := finiteEventProbability D
  let δ := (k : ℝ) * (q : ℝ) ^ (k * k) * ε
  have hc₀ : 0 ≤ c := finiteEventProbability_nonneg _
  have hc₁ : c ≤ 1 := finiteEventProbability_le_one _
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hB : |finiteEventProbability (fun z : (Fin m → Fin N → Bool) × _ => B z.1 z.2) - c| ≤
      δ + finiteEventProbability (fun R => ¬ Good R) := by
    apply finiteEventProbability_product_abs_sub_le_of_good B Good hc₀ hc₁ hδ
    intro R hR
    obtain ⟨P, hDet, hAtom⟩ := hGood R hR
    exact binarySuffix_det_zero_comparison h _ P hDet hε hAtom
  have hU : |finiteEventProbability (fun z : (Fin m → Fin N → ZMod q) × _ => U z.1 z.2) - c| ≤
      (q.primeFactors.card : ℝ) * (m : ℝ) * (1 / 2 : ℝ) ^ (N + 1 - m) := by
    let Good' (R : Fin m → Fin N → ZMod q) :=
      modularPrefixIndependent (Matrix.of (fun i j => R j i))
    have hgood (R : Fin m → Fin N → ZMod q) (hR : Good' R) :
        |finiteEventProbability (U R) - c| ≤ 0 := by
      obtain ⟨P, hP, _, hDet⟩ := matrixPrefixProjection h _ hR
      rw [show finiteEventProbability (U R) = c from uniformSuffix_det_zero_probability h _ P hP hDet]
      simp
    have hu := finiteEventProbability_product_abs_sub_le_of_good U Good' hc₀ hc₁ le_rfl hgood
    rw [zero_add] at hu
    exact hu.trans (uniformPrefixIndependent_failure_probability_le (q := q) (by omega))
  have hBs : finiteEventProbability (fun X : Fin N → Fin N → Bool =>
      (((Matrix.of X).map zeroOneBit).map (Int.castRingHom (ZMod q))).det = 0) =
      finiteEventProbability (fun z : (Fin m → Fin N → Bool) × (Fin k → Fin N → Bool) => B z.1 z.2) := by
    rw [← finiteEventProbability_equiv (splitColumnEquiv h).symm]
    apply congrArg finiteEventProbability
    funext z
    exact propext (by rw [binary_det_eq_append h z.1 z.2])
  have hUs : finiteEventProbability (fun X : Fin N → Fin N → ZMod q => (Matrix.of X).det = 0) =
      finiteEventProbability (fun z : (Fin m → Fin N → ZMod q) × (Fin k → Fin N → ZMod q) => U z.1 z.2) := by
    rw [← finiteEventProbability_equiv (splitColumnEquiv h).symm]
    apply congrArg finiteEventProbability
    funext z
    exact propext (by rw [uniform_det_eq_append h z.1 z.2])
  rw [hBs, hUs]
  exact (abs_sub_le _ c _).trans (add_le_add hB (by rwa [abs_sub_comm]))

end BooleanThreshold
