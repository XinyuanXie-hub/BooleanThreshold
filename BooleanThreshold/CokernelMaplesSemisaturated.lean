module

public import BooleanThreshold.BinaryAlphabetCount
public import BooleanThreshold.CokernelMaplesWeights
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds

public section

open Filter Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical

namespace BooleanThreshold

private noncomputable def nearZeroArc (q : ℕ) [NeZero q] (ε : ℝ) : Finset (ZMod q) :=
  univ.filter fun x =>
    (x.val : ℝ) < ε * (q : ℝ) ∨ ((q - x.val : ℕ) : ℝ) < ε * (q : ℝ)

private theorem nearZeroArc_card_le {q : ℕ} [NeZero q] {ε : ℝ} (hε : 0 ≤ ε) :
    ((nearZeroArc q ε).card : ℝ) ≤ 2 * ε * (q : ℝ) + 2 := by
  let C (f : ZMod q → ℕ) := univ.filter fun x => (f x : ℝ) < ε * (q : ℝ)
  have hC (f : ZMod q → ℕ) (hf : Function.Injective f) : ((C f).card : ℝ) ≤ ε * (q : ℝ) + 1 := by
    have hcard : (C f).card ≤ ⌈ε * (q : ℝ)⌉₊ := by
      rw [← card_range ⌈ε * (q : ℝ)⌉₊]
      apply card_le_card_of_injOn f _ hf.injOn
      intro x hx
      exact mem_range.mpr (Nat.lt_ceil.mpr (mem_filter.mp hx).2)
    have hcardR : ((C f).card : ℝ) ≤ (⌈ε * (q : ℝ)⌉₊ : ℝ) := by exact_mod_cast hcard
    exact hcardR.trans (Nat.ceil_lt_add_one (by positivity : 0 ≤ ε * (q : ℝ))).le
  let f (x : ZMod q) := q - x.val
  have hf : Function.Injective f := by
    intro x y h
    have hx := x.val_lt
    have hy := y.val_lt
    apply ZMod.val_injective q
    dsimp only [f] at h
    omega
  have hset : nearZeroArc q ε = C ZMod.val ∪ C f := by
    ext x
    simp [nearZeroArc, C, f]
  have hs : ((nearZeroArc q ε).card : ℝ) ≤ ((C ZMod.val).card : ℝ) + ((C f).card : ℝ) := by
    rw [hset]
    exact_mod_cast card_union_le (C ZMod.val) (C f)
  linarith only [hs, hC ZMod.val (ZMod.val_injective q), hC f hf]

private theorem zero_of_mem_nearZeroArc {q : ℕ} [NeZero q] {ε : ℝ}
    (hε : ε * (q : ℝ) ≤ 1) {x : ZMod q} (hx : x ∈ nearZeroArc q ε) : x = 0 := by
  have h := (mem_filter.mp hx).2
  rcases h with h | h
  · have hval : x.val < 1 := by exact_mod_cast h.trans_le hε
    apply ZMod.val_injective q
    simpa using Nat.lt_one_iff.mp hval
  · have hval : q - x.val < 1 := by exact_mod_cast h.trans_le hε
    have hp := x.val_lt
    omega

private theorem stdAddChar_re_val {q : ℕ} [NeZero q] (x : ZMod q) :
    (ZMod.stdAddChar x).re = Real.cos (2 * Real.pi * ((x.val : ℝ) / (q : ℝ))) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

private theorem bitFourierCoefficient_norm_le_arc {q : ℕ} [NeZero q] {ε : ℝ}
    (hε : 0 < ε) {x : ZMod q} (hx : x ∉ nearZeroArc q ε) :
    ‖bitFourierCoefficient x‖ ≤ Real.exp (-(1 - Real.cos (2 * Real.pi * ε)) / 4) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hl : ε * (q : ℝ) ≤ (x.val : ℝ) :=
    le_of_not_gt fun h => hx (mem_filter.mpr ⟨mem_univ _, Or.inl h⟩)
  have hh : ε * (q : ℝ) ≤ ((q - x.val : ℕ) : ℝ) :=
    le_of_not_gt fun h => hx (mem_filter.mpr ⟨mem_univ _, Or.inr h⟩)
  rw [Nat.cast_sub x.val_lt.le] at hh
  let u := (x.val : ℝ) / (q : ℝ)
  have hu₁ : ε ≤ u := (le_div_iff₀ hq).mpr hl
  have hu₂ : u ≤ 1 - ε := (div_le_iff₀ hq).mpr (by linarith)
  have hcos : Real.cos (2 * Real.pi * u) ≤ Real.cos (2 * Real.pi * ε) := by
    have hp : 0 ≤ 2 * Real.pi := by positivity
    by_cases hu : u ≤ 1 / 2
    · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
        (by nlinarith only [mul_le_mul_of_nonneg_left hu hp])
        (mul_le_mul_of_nonneg_left hu₁ hp)
    · have hu' : 1 - u ≤ 1 / 2 := by linarith
      rw [show 2 * Real.pi * u = 2 * Real.pi - 2 * Real.pi * (1 - u) by ring, Real.cos_two_pi_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
        (by nlinarith only [mul_le_mul_of_nonneg_left hu' hp])
        (mul_le_mul_of_nonneg_left (by linarith) hp)
  refine (bitFourierCoefficient_norm_le_exp x).trans (Real.exp_le_exp.mpr ?_)
  rw [bitFourierDeficit, stdAddChar_re_val]
  exact (by dsimp only [u] at hcos; linarith)

private theorem bad_arc_coordinates_card_le {q n : ℕ} [NeZero q] {ε : ℝ}
    (hε : 0 < ε) (hεh : ε ≤ 1 / 2) (a : Fin n → ZMod q)
    (ha : Real.exp (-((1 - Real.cos (2 * Real.pi * ε)) / (4 * 128)) * (n : ℝ)) ≤
      ∏ j, ‖bitFourierCoefficient (a j)‖) :
    (univ.filter fun j => a j ∉ nearZeroArc q ε).card ≤ n / 128 := by
  let γ := (1 - Real.cos (2 * Real.pi * ε)) / 4
  have hγ : 0 < γ := by
    have hc : Real.cos (2 * Real.pi * ε) < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
        (by nlinarith only [mul_le_mul_of_nonneg_left hεh (show 0 ≤ 2 * Real.pi by positivity)])
        (by positivity)
    dsimp [γ]
    linarith
  let I := univ.filter fun j => a j ∉ nearZeroArc q ε
  have hprod : (∏ j, ‖bitFourierCoefficient (a j)‖) ≤ Real.exp (-γ * (I.card : ℝ)) := by
    calc
      _ ≤ ∏ j, if a j ∉ nearZeroArc q ε then Real.exp (-γ) else 1 := by
        apply prod_le_prod₀ (fun j _ => norm_nonneg _)
        intro j _
        by_cases hj : a j ∉ nearZeroArc q ε
        · rw [ite_eq_left hj]
          simpa only [γ, neg_div] using bitFourierCoefficient_norm_le_arc hε hj
        · rw [ite_eq_right hj]
          exact bitFourierCoefficient_norm_le_one _
      _ = Real.exp (-γ) ^ I.card := by rw [prod_ite, prod_const, prod_const, one_pow, mul_one]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h := Real.exp_le_exp.mp (ha.trans hprod)
  have hh : γ * (I.card : ℝ) ≤ γ * ((n : ℝ) / 128) := by
    have he : (1 - Real.cos (2 * Real.pi * ε)) / (4 * 128) = γ / 128 := by dsimp [γ]; ring
    rw [he] at h
    linarith
  have hc := (mul_le_mul_iff_of_pos_left hγ).mp hh
  exact (Nat.le_div_iff_mul_le (by decide)).mpr
    (by exact_mod_cast ((le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).mp hc))

private theorem eventually_polynomial_modulus_remaining_pow_le (B : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, 0 < q → q ≤ n ^ B →
      (q : ℝ) ^ (n - (n - ⌈L * Real.log (n : ℝ)⌉₊)) ≤ 2 ^ n := by
  let A := (B : ℝ) * (L + 1)
  let η := Real.log 2 / (A + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hη
  filter_upwards [eventually_ge_atTop 3, tendsto_natCast_atTop_atTop.eventually hsmall]
    with n hn hsmalln
  intro q hq hqn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hln : 1 ≤ Real.log (n : ℝ) :=
    (Real.le_log_iff_exp_le hnpos).mpr (Real.exp_one_lt_three.le.trans hnR)
  let s := n - (n - ⌈L * Real.log (n : ℝ)⌉₊)
  have hs : s ≤ ⌈L * Real.log (n : ℝ)⌉₊ := by dsimp [s]; omega
  have hsR : (s : ℝ) ≤ (L + 1) * Real.log (n : ℝ) := by
    have hcast : (s : ℝ) ≤ (⌈L * Real.log (n : ℝ)⌉₊ : ℝ) := by exact_mod_cast hs
    have hceil := (Nat.ceil_lt_add_one (mul_nonneg hL (zero_le_one.trans hln))).le
    linarith only [hcast, hceil, hln]
  have hsq : Real.log (n : ℝ) ^ 2 ≤ η * (n : ℝ) := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using hsmalln
  have hsBound : (s : ℝ) * ((B : ℝ) * Real.log (n : ℝ)) ≤ Real.log 2 * (n : ℝ) := by
    calc
      _ ≤ ((L + 1) * Real.log (n : ℝ)) * ((B : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hsR (by positivity)
      _ = A * Real.log (n : ℝ) ^ 2 := by dsimp [A]; ring
      _ ≤ (A + 1) * Real.log (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ (A + 1) * (η * (n : ℝ)) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by rw [← mul_assoc, mul_comm (A + 1)]; simp [η, ne_of_gt (show 0 < A + 1 by positivity)]
  calc
    _ ≤ ((n : ℝ) ^ B) ^ s := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hqn) _
    _ = (Real.exp (Real.log (n : ℝ)) ^ B) ^ s := by rw [Real.exp_log hnpos]
    _ = Real.exp ((s : ℝ) * ((B : ℝ) * Real.log (n : ℝ))) := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log 2 * (n : ℝ)) := Real.exp_le_exp.mpr hsBound
    _ = _ := by rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Dense Fourier normals of small row mass are exponentially unlikely at
polynomial moduli, even for a logarithmically shortened prefix. -/
theorem maples_semisaturated_exclusion {D L : ℝ} (hD : 1 ≤ D) (hL : 0 ≤ L) (B : ℕ) :
    ∃ d > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (q : ℕ) [NeZero q], q ≤ n ^ B →
      (uniformOn Set.univ).real {R : Fin (n - ⌈L * Real.log (n : ℝ)⌉₊) → Fin n → Bool |
        ∃ a : Fin n → ZMod q,
          n / 128 < (univ.filter fun j => a j ≠ 0).card ∧
          Real.exp (-d * (n : ℝ)) ≤ (∏ j, ‖bitFourierCoefficient (a j)‖) ∧
          binaryZeroAtom a ≤ D / (q : ℝ) ∧
          ∀ i, a ⬝ᵥ binaryColumn (ZMod q) (R i) = 0} ≤ (1 / 2 : ℝ) ^ n := by
  let b := 1 / (8 * D)
  let ε := b ^ 2 / 8
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hb : 0 < b := by dsimp [b]; positivity
  have hb₁ : b ≤ 1 := by dsimp [b]; apply div_le_one_of_le₀ <;> linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεh : ε ≤ 1 / 2 := by
    dsimp [ε]
    have hh : b ^ 2 ≤ 1 := (pow_le_pow_left₀ hb.le hb₁ 2).trans_eq (one_pow _)
    linarith
  let d := (1 - Real.cos (2 * Real.pi * ε)) / (4 * 128)
  have hd : 0 < d := by
    have hc : Real.cos (2 * Real.pi * ε) < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
        (by nlinarith only [mul_le_mul_of_nonneg_left hεh (show 0 ≤ 2 * Real.pi by positivity)])
        (by positivity)
    dsimp [d]
    linarith
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_polynomial_modulus_remaining_pow_le B hL] with n hRest
  intro q _ hqn
  let m := n - ⌈L * Real.log (n : ℝ)⌉₊
  let t := n / 128
  let A := nearZeroArc q ε
  let P (a : Fin n → ZMod q) :=
    t < (univ.filter fun j => a j ≠ 0).card ∧
      Real.exp (-d * (n : ℝ)) ≤ (∏ j, ‖bitFourierCoefficient (a j)‖) ∧
      binaryZeroAtom a ≤ D / (q : ℝ)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : t ≤ n := Nat.div_le_self _ _
  have hm : m ≤ n := Nat.sub_le _ _
  have hbad (a : Fin n → ZMod q) (ha : P a) :
      (univ.filter fun j => a j ∉ A).card ≤ t := bad_arc_coordinates_card_le hε hεh a ha.2.1
  suffices h : (uniformOn Set.univ).real {R : Fin m → Fin n → Bool |
      ∃ a : Fin n → ZMod q, P a ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod q) (R i) = 0} ≤ (1 / 2 : ℝ) ^ n by
    simpa only [P, t, m, and_assoc] using h
  by_cases hsmall : b ^ 2 * (q : ℝ) < 4
  · have hzer : ε * (q : ℝ) ≤ 1 := by dsimp [ε]; linarith
    have hempty : {R : Fin m → Fin n → Bool |
        ∃ a : Fin n → ZMod q, P a ∧ ∀ i, a ⬝ᵥ binaryColumn (ZMod q) (R i) = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨a, ha, _⟩
      have hsub : (univ.filter fun j => a j ≠ 0) ⊆ univ.filter fun j => a j ∉ A := by
        intro j hj
        exact mem_filter.mpr ⟨mem_univ _, fun hz =>
          (mem_filter.mp hj).2 (zero_of_mem_nearZeroArc hzer hz)⟩
      exact ha.1.not_ge ((card_le_card hsub).trans (hbad a ha))
    rw [hempty, measureReal_empty]
    positivity
  have hA : (A.card : ℝ) ≤ b ^ 2 * (q : ℝ) := by
    refine nearZeroArc_card_le hε.le |>.trans ?_
    dsimp [ε]
    linarith only [le_of_not_gt hsmall]
  have hcover (a : Fin n → ZMod q) (ha : P a) :
      ∃ _j : Unit, ∃ I : Finset (Fin n), I.card = t ∧ ∀ i ∉ I, a i ∈ A := by
    obtain ⟨I, hI, _, hc⟩ := exists_subsuperset_card_eq (subset_univ _) (hbad a ha)
      (by simpa using ht)
    exact ⟨(), I, hc, fun i hi => by
      by_contra h
      exact hi (hI (mem_filter.mpr ⟨mem_univ _, h⟩))⟩
  have hprob := alphabet_annihilation_mass_le (m := m) (fun _ : Unit => A) P
    (by positivity : 0 ≤ b ^ 2 * (q : ℝ)) (by positivity : 0 ≤ D / (q : ℝ))
    (fun _ => hA) hcover (fun a ha => ha.2.2)
  simp only [Fintype.card_unit, Nat.cast_one, one_mul] at hprob
  have hchoose : (n.choose t : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n t
  have hpowD : D ^ m ≤ D ^ n := pow_le_pow_right₀ hD hm
  have hpowb : b ^ (2 * (n - t)) ≤ b ^ n := by
    apply pow_le_pow_of_le_one hb.le hb₁
    dsimp [t]
    omega
  have hfactor :
      (q : ℝ) ^ t * (b ^ 2 * (q : ℝ)) ^ (n - t) * (D / (q : ℝ)) ^ m =
        (q : ℝ) ^ (n - m) * (D ^ m * b ^ (2 * (n - t))) := by
    rw [mul_pow (b ^ 2) (q : ℝ), div_pow D (q : ℝ), ← pow_mul b 2 (n - t)]
    have hsum : (q : ℝ) ^ t * (q : ℝ) ^ (n - t) = (q : ℝ) ^ n := by
      rw [← pow_add, Nat.add_sub_of_le ht]
    have hdiv : (q : ℝ) ^ n / (q : ℝ) ^ m = (q : ℝ) ^ (n - m) := by
      apply (div_eq_iff (pow_ne_zero _ hqR.ne')).mpr
      rw [← pow_add, Nat.sub_add_cancel hm]
    rw [← hdiv, ← hsum]
    ring
  have hbD : 2 * D * b = (1 / 4 : ℝ) := by dsimp [b]; field_simp; ring
  calc
    _ ≤ (n.choose t : ℝ) * ((q : ℝ) ^ t * (b ^ 2 * (q : ℝ)) ^ (n - t) *
        (D / (q : ℝ)) ^ m) := by simpa only [mul_assoc] using hprob
    _ = (n.choose t : ℝ) * ((q : ℝ) ^ (n - m) * (D ^ m * b ^ (2 * (n - t)))) := by rw [hfactor]
    _ ≤ (2 : ℝ) ^ n * ((q : ℝ) ^ (n - m) * (D ^ n * b ^ n)) := by gcongr
    _ = (q : ℝ) ^ (n - m) * (1 / 4 : ℝ) ^ n := by rw [← hbD, mul_pow, mul_pow]; ring
    _ ≤ (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := mul_le_mul_of_nonneg_right (hRest q hq hqn) (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

end BooleanThreshold
