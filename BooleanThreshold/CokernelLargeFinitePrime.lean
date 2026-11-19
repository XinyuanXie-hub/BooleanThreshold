module

public import BooleanThreshold.BinaryAlphabetCount
public import BooleanThreshold.CokernelLargeDual
public import BooleanThreshold.CokernelLargeFourier
public import BooleanThreshold.CokernelLargeSampling

public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical

namespace BooleanThreshold

/-- The coefficient alphabet specified by finitely many character tests. -/
@[expose] noncomputable def sampledBinaryAlphabet {p L : ℕ} [NeZero p]
    (b : ℝ) (s : Fin L → ZMod p) : Finset (ZMod p) :=
  univ.filter fun c =>
    (∑ i, (1 - (ZMod.stdAddChar (c * s i)).re) / 2) ≤ (L : ℝ) * b

/-- A frequency sample covers all but a prescribed number of coefficients
and consists only of coefficients with small mean defect. -/
theorem exists_sampledBinaryAlphabet_of_energy {p n t k L : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hSn : S.Nonempty) (a : Fin n → ZMod p)
    {M : ℝ} (ht : t ≤ n) (hk : 0 < k)
    (hEnergy : ∀ z ∈ S, characterEnergy a z ≤ M)
    (hM : 2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t)
    (hL : 2 * (p : ℝ) * Real.exp (-(L : ℝ) / (128 * (k : ℝ) ^ 2)) < 1) :
    ∃ s : Fin L → ZMod p,
      (∀ c ∈ sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) s,
        dualMeanDefect S c ≤ 1 / (16 * (k : ℝ) ^ 2)) ∧
      ∃ I : Finset (Fin n), I.card = t ∧
        ∀ i ∉ I, a i ∈ sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) s := by
  let : Nonempty S := ⟨⟨hSn.choose, hSn.choose_spec⟩⟩
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let b := 1 / (64 * (k : ℝ) ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbL : 2 * (Fintype.card (ZMod p) : ℝ) * Real.exp (-(L : ℝ) * b / 2) < 1 := by
    rw [ZMod.card, show -(L : ℝ) * b / 2 = -(L : ℝ) / (128 * (k : ℝ) ^ 2) by dsimp [b]; ring]
    exact hL
  let f (c : ZMod p) (x : S) := (1 - (ZMod.stdAddChar (c * (x : ZMod p))).re) / 2
  have hf (c : ZMod p) (x : S) : f c x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨characterDefect_nonneg _, characterDefect_le_one _⟩
  obtain ⟨s, hs⟩ := exists_sample_distinguishes_means f hf hb hbL
  have hmean (c : ZMod p) : (∑ x : S, f c x) / Fintype.card S = dualMeanDefect S c := by
    rw [Fintype.card_coe]
    simp only [dualMeanDefect, f]
    rw [Finset.sum_coe_sort S (fun x => (1 - (ZMod.stdAddChar (c * x)).re) / 2)]
  simp only [hmean] at hs
  let y (i : Fin L) : ZMod p := s i
  let A := sampledBinaryAlphabet b y
  have hA (c : ZMod p) (hc : c ∈ A) : dualMeanDefect S c ≤ 1 / (16 * (k : ℝ) ^ 2) := by
    have h := (hs c).2 ((mem_filter.mp hc).2)
    rw [show 4 * b = 1 / (16 * (k : ℝ) ^ 2) by dsimp [b]; ring] at h
    exact h.le
  obtain ⟨I, hI, hgood⟩ := exists_dualMeanDefect_exceptions S hSn a hEnergy (div_pos hb (by norm_num))
    (show 2 * M ≤ (b / 4) * t by
      rw [show b / 4 = 1 / (256 * (k : ℝ) ^ 2) by dsimp [b]; ring]
      exact hM) ht
  exact ⟨y, hA, I, hI, fun i hi => mem_filter.mpr ⟨mem_univ _, (hs (a i)).1 (hgood i hi)⟩⟩

private theorem exists_sampledBinaryAlphabet {p n t k L : ℕ} [Fact p.Prime]
    {ρ M : ℝ} (hρ : 0 < ρ) (ht : t ≤ n) (hk : 0 < k)
    (hM : 2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t) (heM : Real.exp (-M) ≤ ρ / 2)
    (hpρ : 8 < (p : ℝ) * ρ)
    (hL : 2 * (p : ℝ) * Real.exp (-(L : ℝ) / (128 * (k : ℝ) ^ 2)) < 1)
    (a : Fin n → ZMod p) (ha : ρ ≤ binaryConcentration a) :
    ∃ s : Fin L → ZMod p,
      ((sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) s).card : ℝ) ≤ 8 / (ρ * k) + 1 ∧
      ∃ I : Finset (Fin n), I.card = t ∧
        ∀ i ∉ I, a i ∈ sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) s := by
  let S := univ.filter fun z : ZMod p => characterEnergy a z ≤ M
  have hS : (p : ℝ) * ρ / 2 ≤ (S.card : ℝ) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _))
      (by norm_num)).trans (binaryEnergy_level_card (heM.trans (by linarith)))
  have hSb : 4 < S.card := by
    have : (4 : ℝ) < S.card := (show 4 < (p : ℝ) * ρ / 2 by linarith).trans_le hS
    exact_mod_cast this
  have hSn : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨y, hA, I, hI, hgood⟩ := exists_sampledBinaryAlphabet_of_energy S hSn a ht hk
    (fun z hz => (mem_filter.mp hz).2) hM hL
  let A := sampledBinaryAlphabet (1 / (64 * (k : ℝ) ^ 2)) y
  refine ⟨y, ?_, I, hI, hgood⟩
  change (A.card : ℝ) ≤ _
  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hSn.card_pos
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hAcard := (dualMeanDefect_sumset_card_bounds S A hSb hk hA).2
  have hInv : 4 * (p : ℝ) / S.card ≤ 8 / ρ := by
    apply (div_le_div_iff₀ hSpos hρ).mpr
    linarith
  calc
    _ ≤ (4 * (p : ℝ) / S.card) / k + 1 := hAcard
    _ ≤ (8 / ρ) / k + 1 := add_le_add (div_le_div_of_nonneg_right hInv hkR.le) le_rfl
    _ = _ := by rw [div_div]

/-- The sampled-alphabet count for normals in one concentration interval over a prime field. -/
theorem sampled_binary_normal_annihilation_mass_le {p n m t k L : ℕ} [Fact p.Prime]
    {ρ q M : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ q) (ht : t ≤ n) (hk : 0 < k)
    (hM : 2 * M ≤ (1 / (256 * (k : ℝ) ^ 2)) * t) (heM : Real.exp (-M) ≤ ρ / 2)
    (hpρ : 8 < (p : ℝ) * ρ)
    (hL : 2 * (p : ℝ) * Real.exp (-(L : ℝ) / (128 * (k : ℝ) ^ 2)) < 1) :
    (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
      ∃ a : Fin n → ZMod p, ρ ≤ binaryConcentration a ∧ binaryConcentration a ≤ q ∧
        ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0} ≤
      (p : ℝ) ^ L * (n.choose t : ℝ) * (p : ℝ) ^ t * (8 / (ρ * k) + 1) ^ (n - t) * q ^ m := by
  let b := 1 / (64 * (k : ℝ) ^ 2)
  let V := 8 / (ρ * k) + 1
  let alphabet (s : Fin L → ZMod p) :=
    if ((sampledBinaryAlphabet b s).card : ℝ) ≤ V then sampledBinaryAlphabet b s else ∅
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcard (s : Fin L → ZMod p) : ((alphabet s).card : ℝ) ≤ V := by
    by_cases h : ((sampledBinaryAlphabet b s).card : ℝ) ≤ V
    · simpa only [alphabet, ite_eq_left h] using h
    · simpa only [alphabet, ite_eq_right h, card_empty, Nat.cast_zero] using hV
  let P (a : Fin n → ZMod p) := ρ ≤ binaryConcentration a ∧ binaryConcentration a ≤ q
  have hcover (a : Fin n → ZMod p) (ha : P a) :
      ∃ s, ∃ I : Finset (Fin n), I.card = t ∧ ∀ i ∉ I, a i ∈ alphabet s := by
    obtain ⟨s, hs, I, hI, hgood⟩ := exists_sampledBinaryAlphabet hρ ht hk hM heM hpρ hL a ha.1
    refine ⟨s, I, hI, fun i hi => ?_⟩
    simpa only [alphabet, ite_eq_left (show ((sampledBinaryAlphabet b s).card : ℝ) ≤ V from hs)] using
      hgood i hi
  have h := alphabet_annihilation_mass_le (m := m) alphabet P hV hq hcard hcover
    (fun a ha => (binary_atom_le_concentration a 0).trans ha.2)
  simpa only [P, V, Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, and_assoc] using h

end BooleanThreshold
