module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

public section

open Module Submodule

namespace BooleanThreshold

/-- A family of `r` rows of length `r + 1` always has a nonzero common null vector. -/
theorem exists_nonzero_common_null {K : Type*} [Field K] {r : ℕ}
    (rows : Fin r → Fin (r + 1) → K) :
    ∃ a : Fin (r + 1) → K, a ≠ 0 ∧ ∀ j, ∑ i, a i * rows j i = 0 := by
  let cols (i : Fin (r + 1)) : Fin r → K := fun j => rows j i
  have hdep : ¬ LinearIndependent K cols := by
    intro hind
    have hdim := LinearIndependent.fintype_card_le_finrank hind
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  obtain ⟨a, ha, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨a, fun hz => hi (congrFun hz i), fun j => ?_⟩
  simpa only [cols, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun ha j

/-- An indexed family with one redundant vector has an independent subfamily
obtained by omitting a single index. -/
theorem exists_succAbove_linearIndependent_of_finrank_eq
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} (v : Fin (m + 1) → V)
    (h : finrank K (span K (Set.range v)) = m) :
    ∃ i : Fin (m + 1), LinearIndependent K (v ∘ i.succAbove) := by
  classical
  obtain ⟨κ, e, he, hspan, hind⟩ := exists_linearIndependent' K v
  let : Fintype κ := Fintype.ofInjective e he
  let I : Finset (Fin (m + 1)) := Finset.univ.map ⟨e, he⟩
  have hcard : I.card = m := by
    rw [show I.card = Fintype.card κ by simp [I], ← finrank_span_eq_card hind, hspan, h]
  have hcompl : (Finset.univ \ I).card = 1 := by
    rw [Finset.card_sdiff]
    simp [hcard]
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
  have hchoose (j : Fin m) : ∃ k, e k = i.succAbove j := by
    have hnot : i.succAbove j ∉ Finset.univ \ I := by
      rw [hi]
      simp
    have hmem : i.succAbove j ∈ I := by simpa using hnot
    simpa [I] using hmem
  choose f hf using hchoose
  have hf' : Function.Injective f := fun j k hfg =>
    i.succAbove_right_injective ((hf j).symm.trans ((congrArg e hfg).trans (hf k)))
  exact ⟨i, by simpa only [Function.comp_def, hf] using hind.comp f hf'⟩

end BooleanThreshold
