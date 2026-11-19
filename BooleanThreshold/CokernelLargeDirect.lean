module

public import BooleanThreshold.CokernelLargeAtomTransfer
public import BooleanThreshold.CokernelLargeControl
public import BooleanThreshold.CokernelLargeDirectParameters
public import BooleanThreshold.CokernelLargeFinitePrime
public import BooleanThreshold.CokernelLargeIntegerExpansion

/-!
# Large prime divisors of binary cokernels

For primes up to an auxiliary prime, sampled character defects give a small
alphabet for most coordinates of each high-concentration normal. At larger
primes, a bounded-height expansion gives the integer coefficient matrix used
to transfer the prefix relations and an entire maximal atom to the auxiliary
prime. The same finite-prime count then applies to the transferred normal.
-/

public section

open Filter Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Pointwise

namespace BooleanThreshold

private theorem minimum_atom_le_prefix_threshold {N : ℕ} (hN : 9 ≤ N) :
    1 / (N : ℝ) ^ 104 ≤ 1 / (N : ℝ) ^ 102 :=
  one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ N by omega)) (by decide))

private theorem eight_lt_prime_mul_minimum_atom {N K p : ℕ} (hN : 9 ≤ N) (hK : 105 ≤ K)
    (hp : N ^ K < p) {ρ : ℝ} (hρ : 1 / (N : ℝ) ^ 104 ≤ ρ) :
    8 < (p : ℝ) * ρ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h : 8 * (N : ℝ) ^ 104 < (p : ℝ) := calc
    _ < (N : ℝ) ^ 105 := by
      rw [show (105 : ℕ) = 104 + 1 by decide, pow_succ, mul_comm 8]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast (show 8 < N by omega)) (by positivity)
    _ ≤ (N : ℝ) ^ K := pow_le_pow_right₀ hN₁ hK
    _ < _ := by exact_mod_cast hp
  calc
    _ < (p : ℝ) * (1 / (N : ℝ) ^ 104) := by
      rw [mul_one_div]
      exact (lt_div_iff₀ (by positivity)).mpr h
    _ ≤ _ := mul_le_mul_of_nonneg_left hρ (Nat.cast_nonneg p)

set_option maxHeartbeats 700000 in
private theorem high_normal_transfer {N K p m : ℕ} {ε : ℝ} [Fact p.Prime]
    (P : BinaryDirectParameters N K ε) (hN : 9 ≤ N) (hK : 105 ≤ K) (hp : P.prime < p)
    (R : Fin m → Fin N → Bool)
    (hR : BinaryHighNormal (p := p) (1 / (N : ℝ) ^ 102) R) :
    letI : Fact P.prime.Prime := ⟨P.prime_prime⟩
    BinaryHighNormal (p := P.prime) (1 / (N : ℝ) ^ 102) R := by
  classical
  let : Fact P.prime.Prime := ⟨P.prime_prime⟩
  obtain ⟨a, ha, haq, haR⟩ := hR
  let k := P.sumLength
  let H := P.height
  let t := N - binaryInitialLength N
  let M := P.level
  let V := H.factorial * (H + 1)
  let b := 1 / (16 * (k : ℝ) ^ 2)
  let b₀ := 1 / (256 * (k : ℝ) ^ 2)
  let ρ := 1 / (N : ℝ) ^ 104
  have hρa : ρ ≤ binaryConcentration a := (minimum_atom_le_prefix_threshold hN).trans haq.le
  have hpCut := P.cutoff_lt_prime.trans hp
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hpp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast P.sumLength_pos
  let S : Finset (ZMod p) := univ.filter (fun s => characterEnergy a s ≤ M)
  have hScard : (p : ℝ) * binaryConcentration a / 2 ≤ (S.card : ℝ) :=
    binaryEnergy_level_card (P.exp_neg_level_le.trans (div_le_div_of_nonneg_right hρa (by norm_num)))
  have hSbig : 4 < S.card := by
    have h := eight_lt_prime_mul_minimum_atom hN hK hpCut hρa
    exact_mod_cast (show (4 : ℝ) < (S.card : ℝ) by linarith)
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSener (s : ZMod p) (hs : s ∈ S) : characterEnergy a s ≤ M := (mem_filter.mp hs).2
  obtain ⟨E, hEcard, hE⟩ := exists_dualMeanDefect_exceptions S hS a hSener
    (show 0 < b₀ by dsimp [b₀]; positivity) P.energy_budget (Nat.sub_le N (binaryInitialLength N))
  let A : Finset (ZMod p) := univ.filter (fun c => dualMeanDefect S c ≤ b)
  have hA (c : ZMod p) (hc : c ∈ A) : dualMeanDefect S c ≤ b := (mem_filter.mp hc).2
  have hzero : 0 ∈ A := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [dualMeanDefect]
    simp only [zero_mul, AddChar.map_zero_eq_one, Complex.one_re, sub_self, zero_div, sum_const_zero]
    dsimp [b]
    positivity
  have hAE (i : Fin N) (hi : i ∉ E) : a i ∈ A := by
    refine mem_filter.mpr ⟨mem_univ _, (hE i hi).trans ?_⟩
    dsimp [b₀, b]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
    norm_num
  have hsumset := (dualMeanDefect_sumset_card_bounds S A hSbig P.sumLength_pos hA).1
  have hSρ : (p : ℝ) * ρ / 2 ≤ (S.card : ℝ) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρa (Nat.cast_nonneg p))
      (by norm_num)).trans hScard
  have hsmall : ((k • A).card : ℝ) < ((H : ℝ) + 1) ^ binaryExpansionRank := calc
    _ ≤ 4 * (p : ℝ) / S.card := hsumset
    _ ≤ 4 * (p : ℝ) / ((p : ℝ) * ρ / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hSρ
    _ = 8 * (N : ℝ) ^ 104 := by
      have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      dsimp [ρ]
      field_simp
      ring
    _ < _ := P.sumset_size_lt
  obtain ⟨G, _, hGcard, hG⟩ := exists_integer_expansion_of_small_sumset
    (p := p) (D := binaryExpansionRank) (L := H) (k := k)
    hzero P.rank_mul_height_le (by exact_mod_cast hsmall)
  have hHp : H < p := by
    refine P.height_le_size.trans_lt ?_
    exact (Nat.le_self_pow (by omega : K ≠ 0) N).trans_lt hpCut
  obtain ⟨T, hT, y, hy⟩ := exists_integer_normal_matrix hHp hAE hG
  have hV (i : Fin N) (j : G ⊕ E) : |T i j| ≤ (V : ℤ) := by
    simpa only [V, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hT i j
  have hCols : Fintype.card (G ⊕ E) ≤ binaryExpansionRank + t := by
    simp only [Fintype.card_sum, Fintype.card_coe, hEcard]
    omega
  have hminor (r : ℕ) (hr : r ≤ Fintype.card (G ⊕ E)) :
      (r.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ r < (p : ℤ) ∧
        (r.factorial : ℤ) * ((N : ℤ) * (V : ℤ)) ^ r < (P.prime : ℤ) :=
    let h := P.minor_lt r (hr.trans hCols)
    ⟨h.trans (by exact_mod_cast hp), h⟩
  obtain ⟨a', ha', hrho, hk'⟩ := transfer_binary_annihilation_and_concentration (q := P.prime)
    (by omega : 1 ≤ N) R T hV hminor y hy ha (hρpos.trans_le hρa) haR
  exact ⟨a', ha', haq.trans_le hrho, hk'⟩

set_option maxHeartbeats 700000 in
private theorem finite_prime_high_normal_mass_le {N K p : ℕ} {ε : ℝ} [Fact p.Prime]
    (P : BinaryDirectParameters N K ε) (hN : 9 ≤ N) (hK : 105 ≤ K)
    (hpLo : N ^ K < p) (hpHi : p ≤ P.prime) :
    (uniformOn Set.univ).real {R : Fin (binaryInitialLength N) → Fin N → Bool |
      BinaryHighNormal (p := p) (1 / (N : ℝ) ^ 102) R} ≤
      (16 * 104 : ℝ) * Real.exp (ε * (N : ℝ)) * (3 / 4 : ℝ) ^ binaryInitialLength N := by
  classical
  let m := binaryInitialLength N
  let t := N - m
  let k := P.sumLength
  let L := P.sampleLength
  let u := binaryAtomRatio N
  let Bucket := Fin (16 * 104)
  let ρ (j : Bucket) := u ^ (j.val + 1)
  let q (j : Bucket) := min (1 / 2) (u ^ j.val)
  have hu : 0 < u := binaryAtomRatio_pos (by omega)
  have hu₁ : u ≤ 1 := binaryAtomRatio_le_one (by omega)
  have hk : 0 < (k : ℝ) := by exact_mod_cast P.sumLength_pos
  have ht : t ≤ N := Nat.sub_le _ _
  have htm : N - t = m := Nat.sub_sub_self (binaryInitialLength_le N)
  let Ω := Fin m → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let : IsProbabilityMeasure μ := by dsimp [μ, Ω]; infer_instance
  let F (j : Bucket) : Set Ω := {R | ∃ a : Fin N → ZMod p, ρ j ≤ binaryConcentration a ∧
    binaryConcentration a ≤ q j ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod p) (R i) = 0}
  have hCover : {R : Ω | BinaryHighNormal (p := p) (1 / (N : ℝ) ^ 102) R} ⊆ ⋃ j, F j := by
    rintro R ⟨a, ha, hqa, hR⟩
    have hlow : u ^ (16 * 104) < binaryConcentration a := by
      dsimp [u]
      rw [binaryAtomRatio_pow_eq_lowest]
      exact (minimum_atom_le_prefix_threshold hN).trans_lt hqa
    have hup := binaryConcentration_le_half ha
    obtain ⟨j, hj₀, hj₁⟩ := exists_geometric_bucket (16 * 104) hlow
      (hup.trans (by norm_num))
    exact Set.mem_iUnion.mpr ⟨j, a, hj₀.le, le_min hup hj₁, hR⟩
  have hF (j : Bucket) : μ.real (F j) ≤ Real.exp (ε * (N : ℝ)) * (3 / 4 : ℝ) ^ m := by
    have hρ : 0 < ρ j := pow_pos hu _
    have hq : 0 ≤ q j := le_min (by norm_num) (pow_nonneg hu.le _)
    have hminρ : 1 / (N : ℝ) ^ 104 ≤ ρ j := by
      rw [← binaryAtomRatio_pow_eq_lowest]
      exact pow_le_pow_of_le_one hu.le hu₁ j.isLt
    have hpρ := eight_lt_prime_mul_minimum_atom hN hK hpLo hminρ
    have heM : Real.exp (-P.level) ≤ ρ j / 2 := P.exp_neg_level_le.trans
      (div_le_div_of_nonneg_right hminρ (by norm_num))
    have hBound := sampled_binary_normal_annihilation_mass_le (p := p) (m := m) (L := L)
      hρ hq ht P.sumLength_pos P.energy_budget heM hpρ (P.sample_weight_lt p hpHi)
    have hratio : q j / ρ j ≤ (N : ℝ) ^ (1 / 16 : ℝ) := by
      apply (div_le_iff₀ hρ).mpr
      refine (min_le_right _ _).trans_eq ?_
      dsimp [ρ]
      rw [pow_succ]
      have hh : (N : ℝ) ^ (1 / 16 : ℝ) * u = 1 := by
        dsimp [u, binaryAtomRatio]
        have hroot : 0 < (N : ℝ) ^ (1 / 16 : ℝ) := by positivity
        field_simp
      calc
        _ = u ^ j.val * ((N : ℝ) ^ (1 / 16 : ℝ) * u) := by rw [hh, mul_one]
        _ = _ := by ring
    have hSmall : (8 / (ρ j * (k : ℝ)) + 1) * q j ≤ (3 / 4 : ℝ) := calc
      _ = (8 / (k : ℝ)) * (q j / ρ j) + q j := by field_simp
      _ ≤ (8 / (k : ℝ)) * (N : ℝ) ^ (1 / 16 : ℝ) + 1 / 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hratio (by positivity)) (min_le_left _ _)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        have h : 8 * (N : ℝ) ^ (1 / 16 : ℝ) / (k : ℝ) ≤ (1 / 4 : ℝ) :=
          (div_le_iff₀ hk).mpr (P.alphabet_ratio.trans_eq (by ring))
        linarith
    refine hBound.trans ?_
    calc
      _ = (N.choose t : ℝ) * (p : ℝ) ^ (t + L) *
          (((8 / (ρ j * (k : ℝ)) + 1) * q j) ^ m) := by rw [htm, pow_add, mul_pow]; ring
      _ ≤ _ := by
        refine mul_le_mul (P.sample_count_le p hpHi) (pow_le_pow_left₀ ?_ hSmall m) ?_ (by positivity)
        · positivity
        · positivity
  calc
    _ ≤ μ.real (⋃ j, F j) := measureReal_mono hCover (h₂ := measure_ne_top _ _)
    _ ≤ ∑ j, μ.real (F j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Bucket, Real.exp (ε * (N : ℝ)) * (3 / 4 : ℝ) ^ m :=
      Finset.sum_le_sum fun j _ => hF j
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Bucket, Fintype.card_fin]; ring

set_option maxHeartbeats 700000 in
private theorem binary_prefix_failure_mass_le_direct {N K : ℕ} {ε : ℝ}
    (P : BinaryDirectParameters N K ε) (hN : 9 ≤ N) (hK : 105 ≤ K) :
    (uniformOn Set.univ).real
      {R : Fin (binaryInitialLength N) → Fin N → Bool |
        ¬ BinaryPrefixControl (N ^ K) (1 / (N : ℝ) ^ 102) R} ≤
      Real.exp (ε * (N : ℝ)) * ((16 * 104 : ℝ) * Real.exp (ε * (N : ℝ)) *
        (3 / 4 : ℝ) ^ binaryInitialLength N) := by
  classical
  let m := binaryInitialLength N
  let r := 1 / (N : ℝ) ^ 102
  let Ω := Fin m → Fin N → Bool
  let μ := uniformOn (Set.univ : Set Ω)
  let : IsProbabilityMeasure μ := by dsimp [μ, Ω]; infer_instance
  let S := (Finset.Ioc (N ^ K) P.prime).filter Nat.Prime
  let F (p : ℕ) : Set Ω := {R | ∃ hp : p.Prime,
    letI : Fact p.Prime := ⟨hp⟩
    BinaryHighNormal (p := p) r R}
  let B := (16 * 104 : ℝ) * Real.exp (ε * (N : ℝ)) * (3 / 4 : ℝ) ^ m
  have hCover : {R : Ω | ¬ BinaryPrefixControl (N ^ K) r R} ⊆ ⋃ p ∈ S, F p := by
    intro R hR
    obtain ⟨p, hp, hcut, h⟩ := binaryPrefix_failure_gives_highNormal hR
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp₀ : p ≤ P.prime
    · exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hcut, hp₀⟩, hp⟩, hp, h⟩⟩
    · exact Set.mem_iUnion.mpr ⟨P.prime, Set.mem_iUnion.mpr ⟨mem_filter.mpr
        ⟨mem_Ioc.mpr ⟨P.cutoff_lt_prime, le_rfl⟩, P.prime_prime⟩,
        P.prime_prime, high_normal_transfer P hN hK (lt_of_not_ge hp₀) R h⟩⟩
  have hF (p : ℕ) (hp : p ∈ S) : μ.real (F p) ≤ B := by
    obtain ⟨hIoc, hprime⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hIoc
    let : Fact p.Prime := ⟨hprime⟩
    have he : F p = {R | BinaryHighNormal (p := p) r R} := by
      ext R
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hprime, h⟩⟩
    rw [he]
    exact finite_prime_high_normal_mass_le P hN hK hlo hhi
  have hS : S.card ≤ P.prime :=
    (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc]; exact Nat.sub_le _ _)
  calc
    _ ≤ μ.real (⋃ p ∈ S, F p) := measureReal_mono hCover (h₂ := measure_ne_top _ _)
    _ ≤ ∑ p ∈ S, μ.real (F p) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ S, B := Finset.sum_le_sum hF
    _ = (S.card : ℝ) * B := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((show (S.card : ℝ) ≤ (P.prime : ℝ) by exact_mod_cast hS).trans P.prime_count_le) (by positivity)

/-- The large-prime prefix estimate obtained through finite Fourier sampling
and preservation of a maximal atom under bounded integer rank transfer. -/
theorem binary_prefix_bound_direct {K : ℕ} (hK : 105 ≤ K) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real
        {R : Fin (binaryInitialLength N) → Fin N → Bool |
          ¬ BinaryPrefixControl (N ^ K) (1 / (N : ℝ) ^ 102) R} ≤
        C / (N : ℝ) ^ 99 := by
  have hlog : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  let ε := Real.log (4 / 3) / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hExp⟩ := exp_neg_nat_mul_le_inv_pow 99 (show 0 < Real.log (4 / 3) / 4 by positivity)
  refine ⟨(16 * 104 : ℝ) * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 9, eventually_binaryInitialLength_half,
    eventually_binaryDirectParameters K hε] with N hN hhalf hP
  obtain ⟨P⟩ := hP
  let m := binaryInitialLength N
  have hm : (N : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hhalf
  have hDecay : (3 / 4 : ℝ) ^ m ≤ Real.exp (-(Real.log (4 / 3) / 2) * (N : ℝ)) := by
    have he : (3 / 4 : ℝ) ^ m = Real.exp (-(Real.log (4 / 3)) * (m : ℝ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [he]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hm hlog.le])
  refine (binary_prefix_failure_mass_le_direct P hN hK).trans ?_
  calc
    _ ≤ Real.exp (ε * (N : ℝ)) * ((16 * 104 : ℝ) * Real.exp (ε * (N : ℝ)) *
        Real.exp (-(Real.log (4 / 3) / 2) * (N : ℝ))) := by gcongr
    _ = (16 * 104 : ℝ) * Real.exp (-(Real.log (4 / 3) / 4) * (N : ℝ)) := by
      calc
        _ = (16 * 104 : ℝ) * (Real.exp (ε * (N : ℝ)) *
            (Real.exp (ε * (N : ℝ)) * Real.exp (-(Real.log (4 / 3) / 2) * (N : ℝ)))) := by ring
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; dsimp [ε]; ring
    _ ≤ (16 * 104 : ℝ) * (C / (N : ℝ) ^ 99) :=
      mul_le_mul_of_nonneg_left (hExp N (by omega)) (by norm_num)
    _ = _ := by ring

/-- An unconditional polynomial-prime tail for the index of the binary cokernel. -/
theorem polynomial_prime_bound_direct {K : ℕ} (hK : 105 ≤ K) :
    ∃ A > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (uniformOn Set.univ).real {B : Fin N → Fin (N + 1) → Bool |
        hasLargePrimeDivisor (N ^ K) (binaryCokernelIndex B)} ≤ A / (N : ℝ) ^ 99 :=
  polynomial_prime_bound_of_prefix_control (by omega) (binary_prefix_bound_direct hK)

end BooleanThreshold
