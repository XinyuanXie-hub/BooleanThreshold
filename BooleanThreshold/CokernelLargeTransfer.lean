module

public import BooleanThreshold.CokernelLargeProgressions
import Mathlib.Tactic.Positivity

public section

open Function Matrix Set Submodule MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace BooleanThreshold

private theorem rank_mul_lt_of_witness {l m n K : Type*}
    [Fintype l] [Fintype m] [Fintype n] [Field K] (U : Matrix l m K) (T : Matrix m n K)
    (a : n → K) (hT : T *ᵥ a ≠ 0) (hU : U *ᵥ (T *ᵥ a) = 0) :
    (U * T).rank < T.rank := by
  let f := T.mulVecLin
  let g := U.mulVecLin
  have hsub : f.ker ≤ (g.comp f).ker := fun x hx => by
    change g (f x) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero]
  have hlt : f.ker < (g.comp f).ker := by
    refine lt_of_le_of_ne hsub (fun h => hT ?_)
    have ha : a ∈ (g.comp f).ker := hU
    exact LinearMap.mem_ker.mp (h.symm ▸ ha)
  have hfin := Submodule.finrank_lt_finrank_of_lt hlt
  have hf := f.finrank_range_add_finrank_ker
  have hgf := (g.comp f).finrank_range_add_finrank_ker
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul]
  change Module.finrank K (LinearMap.range (g.comp f)) < Module.finrank K (LinearMap.range f)
  omega

/-- A low-column integer coefficient matrix preserves a nonzero annihilating
image when reduced at two primes above its minor bounds. -/
theorem transfer_bounded_integer_normal {p q N V : ℕ} [Fact p.Prime] [Fact q.Prime]
    {I J : Type*} [Fintype I] [Fintype J] (hN : 1 ≤ N)
    (U : Matrix I (Fin N) ℤ) (hU : ∀ i j, |U i j| ≤ 1)
    (T : Matrix (Fin N) J ℤ) (hT : ∀ i j, |T i j| ≤ (V : ℤ))
    (hminor : ∀ k ≤ Fintype.card J, (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (p : ℤ) ∧
      (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (q : ℤ))
    (y : J → ZMod p) (hy : (T.map (fun x : ℤ => (x : ZMod p))) *ᵥ y ≠ 0)
    (hnull : (U.map (fun x : ℤ => (x : ZMod p))) *ᵥ
      ((T.map (fun x : ℤ => (x : ZMod p))) *ᵥ y) = 0) :
    ∃ v : J → ZMod q, (T.map (fun x : ℤ => (x : ZMod q))) *ᵥ v ≠ 0 ∧
      (U.map (fun x : ℤ => (x : ZMod q))) *ᵥ
        ((T.map (fun x : ℤ => (x : ZMod q))) *ᵥ v) = 0 := by
  have hNT : 1 ≤ (N : ℤ) := by exact_mod_cast hN
  have hScale : (V : ℤ) ≤ (N : ℤ) * (V : ℤ) := le_mul_of_one_le_left (by positivity) hNT
  have hUT (i : I) (j : J) : |(U * T) i j| ≤ (N : ℤ) * (V : ℤ) := by
    simpa only [Fintype.card_fin] using abs_mul_entry_le U T hU hT i j
  have hCols (k : ℕ) (c : Fin k ↪ J) : k ≤ Fintype.card J := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective c c.injective
  have hminT (k : ℕ) (r : Fin k ↪ Fin N) (c : Fin k ↪ J) :
      |(T.submatrix r c).det| < (p : ℤ) ∧ |(T.submatrix r c).det| < (q : ℤ) :=
    let h := abs_minor_le_factorial_mul_pow T (fun i j => (hT i j).trans hScale) r c
    ⟨h.trans_lt (hminor k (hCols k c)).1, h.trans_lt (hminor k (hCols k c)).2⟩
  have hminUT (k : ℕ) (r : Fin k ↪ I) (c : Fin k ↪ J) :
      |((U * T).submatrix r c).det| < (p : ℤ) ∧ |((U * T).submatrix r c).det| < (q : ℤ) :=
    let h := abs_minor_le_factorial_mul_pow (U * T) hUT r c
    ⟨h.trans_lt (hminor k (hCols k c)).1, h.trans_lt (hminor k (hCols k c)).2⟩
  have hRank : ((U * T).map (fun x : ℤ => (x : ZMod p))).rank <
      (T.map (fun x : ℤ => (x : ZMod p))).rank := by
    change ((U * T).map (Int.castRingHom (ZMod p))).rank < _
    rw [Matrix.map_mul]
    exact rank_mul_lt_of_witness _ _ y hy hnull
  exact exists_mulVec_witness_at_second_prime U T
    (fun k r c => (hminT k r c).1) (fun k r c => (hminT k r c).2)
    (fun k r c => (hminUT k r c).1) (fun k r c => (hminUT k r c).2) hRank

/-- The small integer matrix describing a structured normal transfers its
nonzero annihilating image to any second prime larger than the minor bounds. -/
theorem transfer_structured_binary_normal {p q N m t d V : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hN : 1 ≤ N) (U : Matrix (Fin m) (Fin N) ℤ) (hU : ∀ i j, |U i j| ≤ 1)
    (hminor : ∀ k ≤ d + t, (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (p : ℤ) ∧
      (k.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ k < (q : ℤ))
    (a : Fin N → ZMod p) (ha : a ≠ 0) (hs : ProgressionStructured t d V a)
    (hnull : (U.map (fun x : ℤ => (x : ZMod p))) *ᵥ a = 0) :
    ∃ b : Fin N → ZMod q, b ≠ 0 ∧ ProgressionStructured t d V b ∧
      (U.map (fun x : ℤ => (x : ZMod q))) *ᵥ b = 0 := by
  classical
  obtain ⟨E, hE, L, g, hL, hstr⟩ := hs
  let I (k : Fin d) := (Finset.Icc (-(L k : ℤ)) (L k : ℤ) : Finset ℤ)
  have hrepr (i : Fin N) (hi : i ∉ E) :
      ∃ z : ∀ k, I k, (∑ k, ((z k : ℤ) : ZMod p) * g k) = a i := by
    exact (mem_symmetricProgression_iff L g (a i)).1 (hstr i hi)
  choose z hz using hrepr
  let K := Fin d ⊕ E
  let T : Matrix (Fin N) K ℤ := Matrix.of fun i j =>
    if hi : i ∈ E then Sum.elim (fun _ => 0) (fun e : E => if e.val = i then 1 else 0) j
    else Sum.elim (fun k => (z i hi k : ℤ)) (fun _ => 0) j
  have heval (r : ℕ) (y : K → ZMod r) (i : Fin N) (hi : i ∉ E) :
      ((T.map (fun x : ℤ => (x : ZMod r))) *ᵥ y) i =
        ∑ k, ((z i hi k : ℤ) : ZMod r) * y (Sum.inl k) := by
    change (∑ j : Fin d ⊕ E, ((T i j : ℤ) : ZMod r) * y j) = _
    rw [Fintype.sum_sum_type]
    simp [T, hi]
  let y : K → ZMod p := Sum.elim g (fun i => a i)
  have hy : (T.map (fun x : ℤ => (x : ZMod p))) *ᵥ y = a := by
    funext i
    by_cases hi : i ∈ E
    · have he (j : E) : j.val = i ↔ j = ⟨i, hi⟩ := by
        exact (Subtype.coe_inj : j.val = (⟨i, hi⟩ : E).val ↔ j = ⟨i, hi⟩)
      change (∑ j : Fin d ⊕ E, ((T i j : ℤ) : ZMod p) * y j) = _
      rw [Fintype.sum_sum_type]
      simp [T, hi, y, he, apply_ite]
    · rw [heval p y i hi]
      exact hz i hi
  have hV : 1 ≤ V :=
    (Finset.one_le_prod (s := Finset.univ) (f := fun k => 2 * L k + 1)
      (fun k _ => by omega)).trans hL
  have hLen (i : Fin d) : L i ≤ V := by
    have hi : 2 * L i + 1 ≤ progressionVolume L :=
      Finset.single_le_prod (f := fun k : Fin d => 2 * L k + 1) (fun k _ => by omega) (Finset.mem_univ i)
    omega
  have hT (i : Fin N) (j : K) : |T i j| ≤ (V : ℤ) := by
    by_cases hi : i ∈ E
    · cases j with
      | inl k => simp [T, hi]
      | inr k =>
        by_cases he : k.val = i
        · simpa [T, hi, he] using (show (1 : ℤ) ≤ V by exact_mod_cast hV)
        · simp [T, hi, he]
    · cases j with
      | inl k =>
        have hk : |(z i hi k : ℤ)| ≤ (L k : ℤ) :=
          abs_le.mpr (Finset.mem_Icc.mp (z i hi k).prop)
        simpa only [T, Matrix.of_apply, dite_eq_right hi, Sum.elim_inl] using
          hk.trans (by exact_mod_cast hLen k)
      | inr k => simp [T, hi]
  have hCols : Fintype.card K = d + t := by
    simp only [K, Fintype.card_fin, Fintype.card_sum, Fintype.card_coe, hE]
  obtain ⟨v, hv, hv'⟩ := transfer_bounded_integer_normal hN U hU T hT
    (by simpa only [hCols] using hminor) y (by rwa [hy]) (by rwa [hy])
  let b := (T.map (fun x : ℤ => (x : ZMod q))) *ᵥ v
  refine ⟨b, hv, ⟨E, hE, L, (fun k => v (Sum.inl k)), hL, ?_⟩, hv'⟩
  intro i hi
  exact (mem_symmetricProgression_iff _ _ _).2 ⟨z i hi, (heval q v i hi).symm⟩

/-- Every proper subspace is contained in the kernel of a nonzero linear form.
A high-mass proper subspace therefore supplies a high-concentration normal. -/
theorem exists_binary_normal_of_large_mass {N p : ℕ} [Fact p.Prime]
    (W : Submodule (ZMod p) (Fin N → ZMod p)) (hW : W ≠ ⊤) {q : ℝ}
    (hq : q < (uniformOn Set.univ).real {x : Fin N → Bool | binaryColumn (ZMod p) x ∈ W}) :
    ∃ a : Fin N → ZMod p, a ≠ 0 ∧ q < binaryConcentration a ∧
      ∀ x ∈ W, a ⬝ᵥ x = 0 := by
  classical
  obtain ⟨ψ, hψ, hbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hW) inferInstance
  let a : Fin N → ZMod p := fun i => ψ (Pi.single i 1)
  have he (x : Fin N → ZMod p) : ψ x = a ⬝ᵥ x := by
    have hs := (Pi.basisFun (ZMod p) (Fin N)).sum_repr x
    simp only [Pi.basisFun_repr, Pi.basisFun_apply] at hs
    conv_lhs => rw [← hs]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [a, mul_comm]
  have hkill (x : Fin N → ZMod p) (hx : x ∈ W) : a ⬝ᵥ x = 0 := by
    rw [← he]
    have hm : ψ x ∈ W.map ψ := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [hbot, Submodule.mem_bot] at hm
  have ha : a ≠ 0 := by
    intro hz
    apply hψ
    apply LinearMap.ext
    intro x
    simp [he, hz, zero_dotProduct]
  have hsub : {x : Fin N → Bool | binaryColumn (ZMod p) x ∈ W} ⊆
      {x : Fin N → Bool | a ⬝ᵥ binaryColumn (ZMod p) x = 0} :=
    fun x hx => hkill _ hx
  exact ⟨a, ha, hq.trans_le ((measureReal_mono hsub).trans (binary_atom_le_concentration a 0)), hkill⟩

end BooleanThreshold
