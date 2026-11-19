module

public import BooleanThreshold.CokernelLargeTransfer
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity

public section

open Function Matrix Set MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace BooleanThreshold

/-- A nonzero normal to the prefix with atom above the prescribed threshold. -/
@[expose] def BinaryHighNormal {p N m : ℕ} [Fact p.Prime] (q : ℝ)
    (R : Fin m → Fin N → Bool) : Prop :=
  ∃ a : Fin N → ZMod p, a ≠ 0 ∧ q < binaryConcentration a ∧
    ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0

/-- A nonzero normal with a bounded-complexity progression representation. -/
@[expose] def BinaryStructuredNormal {p N m : ℕ} [Fact p.Prime] (t D V : ℕ)
    (R : Fin m → Fin N → Bool) : Prop :=
  ∃ a : Fin N → ZMod p, a ≠ 0 ∧ (∃ d ≤ D, ProgressionStructured t d V a) ∧
    ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0

/-- Failure of prefix control yields a high-atom normal at some prime. -/
theorem binaryPrefix_failure_gives_highNormal {N m cutoff : ℕ} {q : ℝ}
    {R : Fin m → Fin N → Bool} (h : ¬ BinaryPrefixControl cutoff q R) :
    ∃ (p : ℕ) (hp : p.Prime), cutoff < p ∧
      letI : Fact p.Prime := ⟨hp⟩
      BinaryHighNormal (p := p) q R := by
  by_contra hnone
  apply h
  intro p hp ha
  let : Fact p.Prime := ⟨hp⟩
  intro V hV hR
  apply le_of_not_gt
  intro hv
  obtain ⟨a, ha', hq, hk⟩ := exists_binary_normal_of_large_mass V hV hv
  exact hnone ⟨p, hp, ha, a, ha', hq, fun i => hk _ (hR i)⟩

private theorem binaryTranspose_mulVec_apply {N m : ℕ} {K : Type*} [Field K]
    (R : Fin m → Fin N → Bool) (a : Fin N → K) (i : Fin m) :
    (((binaryMatrixOfColumns R).transpose.map (fun x : ℤ => (x : K))) *ᵥ a) i =
      a ⬝ᵥ binaryColumn K (R i) := by
  unfold Matrix.mulVec dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  cases h : R i j <;> simp [binaryColumn, binaryMatrixOfColumns, zeroOneBit, h, mul_comm]

/-- Split the bad primes at an auxiliary prime. Below it the normal is
counted at its own prime. Above it the integer representation transfers
to a structured normal at the auxiliary prime. -/
theorem binaryPrefix_failure_cover_auxiliary_prime {N m t D V cutoff p₀ : ℕ}
    (hN : 1 ≤ N) (hp₀ : p₀.Prime) {q : ℝ}
    (hinverse : ∀ (p : ℕ) (hp : p.Prime), cutoff < p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ a : Fin N → ZMod p, a ≠ 0 → q < binaryConcentration a →
        ∃ d ≤ D, ProgressionStructured t d V a)
    (hminor : ∀ k ≤ D + t, (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (p₀ : ℤ))
    (R : Fin m → Fin N → Bool) (h : ¬ BinaryPrefixControl cutoff q R) :
    (∃ (p : ℕ) (hp : p.Prime), cutoff < p ∧ p ≤ p₀ ∧
      letI : Fact p.Prime := ⟨hp⟩
      BinaryHighNormal (p := p) q R) ∨
    (letI : Fact p₀.Prime := ⟨hp₀⟩; BinaryStructuredNormal (p := p₀) t D V R) := by
  obtain ⟨p, hp, hcut, hHigh⟩ := binaryPrefix_failure_gives_highNormal h
  let : Fact p.Prime := ⟨hp⟩
  by_cases hsmall : p ≤ p₀
  · exact Or.inl ⟨p, hp, hcut, hsmall, hHigh⟩
  · right
    let : Fact p₀.Prime := ⟨hp₀⟩
    obtain ⟨a, ha, hq, hnull⟩ := hHigh
    obtain ⟨d, hd, hs⟩ := hinverse p hp hcut a ha hq
    let U := (binaryMatrixOfColumns R).transpose
    have hU : ∀ i j, |U i j| ≤ 1 := by
      intro i j
      cases h : R i j <;> simp [U, binaryMatrixOfColumns, zeroOneBit, h]
    have ht : (p₀ : ℤ) ≤ (p : ℤ) := by exact_mod_cast Nat.le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨b, hb, hb', hkill⟩ := transfer_structured_binary_normal hN U hU
      (fun k hk => by
        have h := hminor k (hk.trans (Nat.add_le_add_right hd t))
        exact ⟨h.trans_le ht, h⟩) a ha hs (funext fun i => (binaryTranspose_mulVec_apply R a i).trans (hnull i))
    refine ⟨b, hb, ⟨d, hd, hb'⟩, fun i => ?_⟩
    exact (binaryTranspose_mulVec_apply R b i).symm.trans (congrFun hkill i)

/-- The direct branch costs at most the auxiliary prime times the largest
one-prime failure probability. The transferred branch costs one event. -/
theorem binaryPrefix_failure_mass_le_auxiliary_prime {N m t D V cutoff p₀ : ℕ}
    (hN : 1 ≤ N) (hp₀ : p₀.Prime) {q β γ : ℝ} (hβ : 0 ≤ β)
    (hinverse : ∀ (p : ℕ) (hp : p.Prime), cutoff < p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ a : Fin N → ZMod p, a ≠ 0 → q < binaryConcentration a →
        ∃ d ≤ D, ProgressionStructured t d V a)
    (hminor : ∀ k ≤ D + t, (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (p₀ : ℤ))
    (hDirect : ∀ (p : ℕ) (hp : p.Prime), cutoff < p → p ≤ p₀ →
      letI : Fact p.Prime := ⟨hp⟩
      (uniformOn Set.univ).real {R : Fin m → Fin N → Bool | BinaryHighNormal (p := p) q R} ≤ β)
    (hAux : letI : Fact p₀.Prime := ⟨hp₀⟩
      (uniformOn Set.univ).real
        {R : Fin m → Fin N → Bool | BinaryStructuredNormal (p := p₀) t D V R} ≤ γ) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool | ¬ BinaryPrefixControl cutoff q R} ≤
      (p₀ : ℝ) * β + γ := by
  classical
  let : Fact p₀.Prime := ⟨hp₀⟩
  let Ω := Fin m → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let : IsProbabilityMeasure μ := by dsimp [μ, Ω]; infer_instance
  let S := (Finset.Ioc cutoff p₀).filter Nat.Prime
  let F (p : ℕ) : Set Ω := {R | ∃ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    BinaryHighNormal (p := p) q R}
  let G : Set Ω := {R | BinaryStructuredNormal (p := p₀) t D V R}
  have hcover : {R : Ω | ¬ BinaryPrefixControl cutoff q R} ⊆ (⋃ p ∈ S, F p) ∪ G := by
    intro R hR
    obtain h | h := binaryPrefix_failure_cover_auxiliary_prime hN hp₀ hinverse hminor R hR
    · obtain ⟨p, hp, hlo, hhi, h⟩ := h
      exact Or.inl (mem_iUnion.2 ⟨p, mem_iUnion.2
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hlo, hhi⟩, hp⟩, hp, h⟩⟩)
    · exact Or.inr h
  have hF (p : ℕ) (hp : p ∈ S) : μ.real (F p) ≤ β := by
    obtain ⟨hIoc, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hIoc
    let : Fact p.Prime := ⟨hprime⟩
    have he : F p = {R | BinaryHighNormal (p := p) q R} := by
      ext R
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hprime, h⟩⟩
    rw [he]
    exact hDirect p hprime hlo hhi
  have hs : S.card ≤ p₀ := by
    exact (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc]; exact Nat.sub_le _ _)
  calc
    _ ≤ μ.real ((⋃ p ∈ S, F p) ∪ G) := measureReal_mono hcover (h₂ := measure_ne_top _ _)
    _ ≤ μ.real (⋃ p ∈ S, F p) + μ.real G := measureReal_union_le _ _
    _ ≤ (∑ p ∈ S, μ.real (F p)) + γ := add_le_add (measureReal_biUnion_finset_le _ _) hAux
    _ ≤ (∑ _p ∈ S, β) + γ := add_le_add (Finset.sum_le_sum hF) le_rfl
    _ = (S.card : ℝ) * β + γ := by simp
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hβ) le_rfl


/-- For each dense family of normals, a finite cover by progression and
concentration ranges turns into the sum of the corresponding atom bounds. -/
theorem binary_normal_event_mass_le_of_slices {p N m t D : ℕ} [Fact p.Prime]
    (ht : t ≤ N) {J : Type*} [Fintype J] (V : J → ℕ) (Q : J → ℝ) (hQ : ∀ j, 0 ≤ Q j)
    (P : (Fin N → ZMod p) → Prop)
    (hcover : ∀ a : Fin N → ZMod p, a ≠ 0 → P a →
      t < (Finset.univ.filter fun i => a i ≠ 0).card →
      ∃ j, ∃ d : Fin (D + 1), ProgressionStructured t d.val (V j) a ∧ binaryConcentration a ≤ Q j) :
    (uniformOn Set.univ).real {R : Fin m → Fin N → Bool |
      ∃ a : Fin N → ZMod p, a ≠ 0 ∧ P a ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ≤
      (N.choose t : ℝ) * (p : ℝ) ^ t * (1 / 2 : ℝ) ^ m +
      ∑ j : J, ∑ d : Fin (D + 1),
        (N.choose t : ℝ) * ((V j + 1 : ℕ) : ℝ) ^ d.val * (p : ℝ) ^ (t + d.val) *
          (V j : ℝ) ^ (N - t) * (Q j) ^ m := by
  classical
  let Ω := Fin m → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let : IsProbabilityMeasure μ := by dsimp [μ, Ω]; infer_instance
  let Sparse : Set Ω := {R | ∃ a : Fin N → ZMod p, a ≠ 0 ∧
    (Finset.univ.filter fun i => a i ≠ 0).card ≤ t ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0}
  let Slice (j : J) (d : Fin (D + 1)) : Set Ω := {R | ∃ a : Fin N → ZMod p,
    ProgressionStructured t d.val (V j) a ∧ binaryConcentration a ≤ Q j ∧
      ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0}
  have h : {R : Ω | ∃ a : Fin N → ZMod p, a ≠ 0 ∧ P a ∧
    ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ⊆ Sparse ∪ ⋃ j, ⋃ d, Slice j d := by
    rintro R ⟨a, ha, hp, hkill⟩
    by_cases hS : (Finset.univ.filter fun i => a i ≠ 0).card ≤ t
    · exact Or.inl ⟨a, ha, hS, hkill⟩
    · obtain ⟨j, d, hS', hqa⟩ := hcover a ha hp (lt_of_not_ge hS)
      exact Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨d, a, hS', hqa, hkill⟩⟩)
  have hSlice (j : J) (d : Fin (D + 1)) : μ.real (Slice j d) ≤
      (N.choose t : ℝ) * ((V j + 1 : ℕ) : ℝ) ^ d.val * (p : ℝ) ^ (t + d.val) *
        (V j : ℝ) ^ (N - t) * (Q j) ^ m :=
    structured_annihilation_mass_le t d.val (V j) (hQ j)
  calc
    _ ≤ μ.real (Sparse ∪ ⋃ j, ⋃ d, Slice j d) := measureReal_mono h (h₂ := measure_ne_top _ _)
    _ ≤ μ.real Sparse + μ.real (⋃ j, ⋃ d, Slice j d) := measureReal_union_le _ _
    _ ≤ μ.real Sparse + ∑ j, μ.real (⋃ d, Slice j d) :=
      add_le_add le_rfl (measureReal_iUnion_fintype_le _)
    _ ≤ μ.real Sparse + ∑ j, ∑ d, μ.real (Slice j d) :=
      add_le_add le_rfl (Finset.sum_le_sum fun j _ => measureReal_iUnion_fintype_le _)
    _ ≤ _ := add_le_add (sparse_binary_normal_annihilation_mass_le ht)
      (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun d _ => hSlice j d)

end BooleanThreshold
