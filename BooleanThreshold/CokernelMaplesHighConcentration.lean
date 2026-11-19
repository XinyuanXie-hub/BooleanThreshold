module

public import BooleanThreshold.CokernelLargeFinitePrime
public import BooleanThreshold.CokernelMaplesWeights
public import BooleanThreshold.CyclicSumsetGrowth

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Pointwise Classical

namespace BooleanThreshold

/-- A cyclic normal is dense if all of its prime reductions are nonzero on
more than the allowed number of coordinates. -/
@[expose] def DenseCyclicNormal {r n : ℕ} (a : Fin n → ZMod r) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ h : p ∣ r,
    n / 128 < (univ.filter fun i => ZMod.castHom h (ZMod p) (a i) ≠ 0).card

private theorem denseCyclicNormal_alphabet_generates {r n : ℕ} [NeZero r]
    {a : Fin n → ZMod r} (ha : DenseCyclicNormal a)
    (A : Finset (ZMod r)) (I : Finset (Fin n)) (hI : I.card ≤ n / 128)
    (hgood : ∀ i ∉ I, a i ∈ A) :
    AddSubgroup.closure (A : Set (ZMod r)) = ⊤ := by
  let H := AddSubgroup.closure (A : Set (ZMod r))
  by_contra h
  have hOne : AddSubgroup.zmultiples (1 : ZMod r) = ⊤ := by
    apply (AddSubgroup.eq_top_iff' _).mpr
    intro x
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, by simp⟩
  obtain ⟨z, hz⟩ := AddSubgroup.exists_zmultiples_eq_of_zmultiples_eq_top hOne H
  have hd : z.gcd (r : ℤ) ≠ 1 := by
    intro h₁
    apply h
    change H = ⊤
    apply AddSubgroup.index_eq_one.mp
    rw [← hz, AddSubgroup.index_zmultiples_zsmul hOne, ZMod.addOrderOf_one, h₁]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have hpr : p ∣ r := hpd.trans (by exact_mod_cast Int.gcd_dvd_right z (r : ℤ))
  have hpz : (p : ℤ) ∣ z :=
    (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left z (r : ℤ))
  have hzCast : (z : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpz
  have hZero (i : Fin n) (hi : i ∉ I) : ZMod.castHom hpr (ZMod p) (a i) = 0 := by
    have hh : a i ∈ H := AddSubgroup.subset_closure (hgood i hi)
    rw [← hz] at hh
    obtain ⟨w, hw⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
    rw [← hw, map_zsmul, map_zsmul, map_one]
    simp [hzCast]
  have hsub : (univ.filter fun i => ZMod.castHom hpr (ZMod p) (a i) ≠ 0) ⊆ I := by
    intro i hi
    by_contra hnot
    exact (mem_filter.mp hi).2 (hZero i hnot)
  exact (ha p hp hpr).not_ge ((card_le_card hsub).trans hI)

private theorem zero_mem_sampledBinaryAlphabet {r L : ℕ} [NeZero r]
    {b : ℝ} (hb : 0 ≤ b) (s : Fin L → ZMod r) : 0 ∈ sampledBinaryAlphabet b s := by
  simp only [sampledBinaryAlphabet, mem_filter, mem_univ, true_and, zero_mul,
    AddChar.map_zero_eq_one, Complex.one_re, sub_self, zero_div, sum_const_zero]
  positivity

private theorem neg_mem_sampledBinaryAlphabet {r L : ℕ} [NeZero r]
    (b : ℝ) (s : Fin L → ZMod r) (x : ZMod r)
    (hx : x ∈ sampledBinaryAlphabet b s) : -x ∈ sampledBinaryAlphabet b s := by
  have hDeficit (u : ZMod r) : bitFourierDeficit (-u) = bitFourierDeficit u := by
    have h := congrArg (fun y : ℝ => y ^ 2) (bitFourierCoefficient_norm_neg u)
    change ‖bitFourierCoefficient (-u)‖ ^ 2 = ‖bitFourierCoefficient u‖ ^ 2 at h
    rw [bitFourierCoefficient_norm_sq, bitFourierCoefficient_norm_sq] at h
    linarith
  have hNeg (u : ZMod r) : (1 - (ZMod.stdAddChar (-u)).re) / 2 =
      (1 - (ZMod.stdAddChar u).re) / 2 := hDeficit u
  simp only [sampledBinaryAlphabet, mem_filter, mem_univ, true_and] at hx
  simpa only [sampledBinaryAlphabet, mem_filter, mem_univ, true_and, neg_mul, hNeg] using hx

private theorem exists_sampledBinaryAlphabet_of_dense_cyclic {r n t k L : ℕ} [NeZero r]
    {ρ M : ℝ} (hρ : 0 < ρ) (ht : t ≤ n / 128) (hk : 0 < k)
    (hM : 2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t) (heM : Real.exp (-M) ≤ ρ / 2)
    (hrρ : 8 < (r : ℝ) * ρ)
    (hL : 2 * (r : ℝ) * Real.exp (-(L : ℝ) / (128 * (k : ℝ) ^ 2)) < 1)
    (a : Fin n → ZMod r) (hdense : DenseCyclicNormal a) (ha : ρ ≤ binaryZeroAtom a) :
    ∃ s : Fin L → ZMod r,
      ((sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) s).card : ℝ) ≤ 24 / (ρ * k) ∧
      ∃ I : Finset (Fin n), I.card = t ∧
        ∀ i ∉ I, a i ∈ sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) s := by
  let S := univ.filter fun z : ZMod r => characterEnergy a z ≤ M
  have hρM : Real.exp (-M) ≤ binaryZeroAtom a / 2 :=
    heM.trans (div_le_div_of_nonneg_right ha (by norm_num))
  have hS : (r : ℝ) * ρ / 2 ≤ (S.card : ℝ) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _))
      (by norm_num)).trans (binaryEnergy_level_card_at_target 0 hρM)
  have hSb : 4 < S.card := by
    have : (4 : ℝ) < S.card := (show 4 < (r : ℝ) * ρ / 2 by linarith).trans_le hS
    exact_mod_cast this
  have hSn : S.Nonempty := card_pos.mp (by omega)
  have htn : t ≤ n := ht.trans (Nat.div_le_self _ _)
  obtain ⟨s, hs, I, hI, hgood⟩ := exists_sampledBinaryAlphabet_of_energy S hSn a htn hk
    (fun z hz => (mem_filter.mp hz).2) hM hL
  let b := 1 / (64 * (k : ℝ) ^ 2)
  let A := sampledBinaryAlphabet b s
  refine ⟨s, ?_, I, hI, hgood⟩
  change (A.card : ℝ) ≤ _
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hSn.card_pos
  have hkre := dualMeanDefect_sumset_card_le S A hSn hk hs
  have hproper : (k • A).card < Fintype.card (ZMod r) := by
    rw [ZMod.card]
    have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
    have h₄ : (4 : ℝ) < S.card := by exact_mod_cast hSb
    have hlt : ((k • A).card : ℝ) < r := hkre.trans_lt <|
      (div_lt_iff₀ hSpos).mpr (by nlinarith only [mul_lt_mul_of_pos_left h₄ hr])
    exact_mod_cast hlt
  have hgen := denseCyclicNormal_alphabet_generates hdense A I (hI ▸ ht) hgood
  have hsize := symmetric_generating_sumset_card_le A
    (zero_mem_sampledBinaryAlphabet (by dsimp [b]; positivity) s)
    (fun x hx => neg_mem_sampledBinaryAlphabet b s x hx) hgen hk hproper
  have hInv : 4 * (r : ℝ) / S.card ≤ 8 / ρ := by
    apply (div_le_div_iff₀ hSpos hρ).mpr
    linarith
  calc
    _ ≤ 3 * ((k • A).card : ℝ) / k := hsize
    _ ≤ 3 * (8 / ρ) / k := by gcongr; exact hkre.trans hInv
    _ = _ := by rw [mul_div_assoc, div_div]; ring

/-- A dense cyclic normal with intermediate annihilation probability has a
small sampled alphabet, uniformly over the modulus. -/
theorem sampled_dense_cyclic_annihilation_mass_le {r n m t k L : ℕ} [NeZero r]
    {ρ q M : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q) (ht : t ≤ n / 128) (hk : 0 < k)
    (hM : 2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t) (heM : Real.exp (-M) ≤ ρ / 2)
    (hrρ : 8 < (r : ℝ) * ρ)
    (hL : 2 * (r : ℝ) * Real.exp (-(L : ℝ) / (128 * (k : ℝ) ^ 2)) < 1) :
    (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
      ∃ a : Fin n → ZMod r, DenseCyclicNormal a ∧ ρ ≤ binaryZeroAtom a ∧ binaryZeroAtom a ≤ q ∧
        ∀ i, a ⬝ᵥ binaryColumn (ZMod r) (R i) = 0} ≤
      (r : ℝ) ^ L * (n.choose t : ℝ) * (r : ℝ) ^ t * (24 / (ρ * k)) ^ (n - t) * q ^ m := by
  let b := 1 / (64 * (k : ℝ) ^ 2)
  let V := 24 / (ρ * k)
  let alphabet (s : Fin L → ZMod r) :=
    if ((sampledBinaryAlphabet b s).card : ℝ) ≤ V then sampledBinaryAlphabet b s else ∅
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcard (s : Fin L → ZMod r) : ((alphabet s).card : ℝ) ≤ V := by
    by_cases h : ((sampledBinaryAlphabet b s).card : ℝ) ≤ V
    · simpa only [alphabet, ite_eq_left h] using h
    · simpa only [alphabet, ite_eq_right h, card_empty, Nat.cast_zero] using hV
  let P (a : Fin n → ZMod r) := DenseCyclicNormal a ∧ ρ ≤ binaryZeroAtom a ∧ binaryZeroAtom a ≤ q
  have hcover (a : Fin n → ZMod r) (ha : P a) :
      ∃ s, ∃ I : Finset (Fin n), I.card = t ∧ ∀ i ∉ I, a i ∈ alphabet s := by
    obtain ⟨s, hs, I, hI, hgood⟩ := exists_sampledBinaryAlphabet_of_dense_cyclic hρ ht hk hM heM hrρ hL
      a ha.1 ha.2.1
    refine ⟨s, I, hI, fun i hi => ?_⟩
    simpa only [alphabet, ite_eq_left (show ((sampledBinaryAlphabet b s).card : ℝ) ≤ V from hs)] using
      hgood i hi
  have h := alphabet_annihilation_mass_le (m := m) alphabet P hV hq hcard hcover (fun a ha => ha.2.2)
  simpa only [P, V, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, and_assoc] using h

end BooleanThreshold
