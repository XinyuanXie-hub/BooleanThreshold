module

public import BooleanThreshold.CokernelMaplesFourier
public import BooleanThreshold.CokernelMaplesSparse
import Mathlib.GroupTheory.SpecificGroups.Cyclic

public noncomputable section

open AddChar Matrix
open scoped BigOperators Classical Matrix

namespace BooleanThreshold

/-- The additive embedding of a divisor modulus, obtained by multiplying
integer representatives by the complementary factor. -/
def divisorModulusEmbedding {q r d : ℕ} [NeZero q] (h : d * r = q) : ZMod r →+ ZMod q :=
  ZMod.lift r
    ⟨(AddMonoidHom.mulLeft (d : ZMod q)).comp (Int.castAddHom (ZMod q)), by
      change (d : ZMod q) * ((r : ℤ) : ZMod q) = 0
      rw [Int.cast_natCast, ← Nat.cast_mul, h, ZMod.natCast_self]⟩

theorem divisorModulusEmbedding_intCast {q r d : ℕ} [NeZero q] (h : d * r = q) (x : ℤ) :
    divisorModulusEmbedding h (x : ZMod r) = (((d : ℤ) * x : ℤ) : ZMod q) := by
  rw [divisorModulusEmbedding, ZMod.lift_coe, Int.cast_mul]
  rw [Int.cast_natCast]
  rfl

theorem divisorModulusEmbedding_injective {q r d : ℕ} [NeZero q] (h : d * r = q) :
    Function.Injective (divisorModulusEmbedding h) := by
  have hd : d ≠ 0 := fun hz => NeZero.ne q (by simpa [hz] using h.symm)
  intro x y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  intro hab
  simp only [divisorModulusEmbedding_intCast] at hab
  have hz : (((d : ℤ) * (a - b) : ℤ) : ZMod q) = 0 := by
    rw [mul_sub, Int.cast_sub, sub_eq_zero]
    exact hab
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← h, Nat.cast_mul,
    mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hd)] at hz
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hz

theorem divisorModulusEmbedding_character {q r d : ℕ} [NeZero q] [NeZero r]
    (h : d * r = q) (x : ZMod r) :
    ZMod.stdAddChar (divisorModulusEmbedding h x) = ZMod.stdAddChar x := by
  have hd : d ≠ 0 := fun hz => NeZero.ne q (by simpa [hz] using h.symm)
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  simp only [divisorModulusEmbedding_intCast, ZMod.stdAddChar_coe]
  congr 1
  rw [← h]
  push_cast
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  field_simp

theorem divisorModulusEmbedding_dotProduct {q r d n : ℕ} [NeZero q] (h : d * r = q)
    (a : Fin n → ZMod r) (x : Fin n → ZMod q) :
    divisorModulusEmbedding h (a ⬝ᵥ fun i => ZMod.castHom (h ▸ dvd_mul_left r d) (ZMod r) (x i)) =
      (divisorModulusEmbedding h ∘ a) ⬝ᵥ x := by
  conv_lhs => rw [dotProduct, map_sum]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective (a i)
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (x i)
  simp only [Function.comp_apply, ← hu, ← hv, map_intCast, ← Int.cast_mul,
    divisorModulusEmbedding_intCast, mul_assoc]

/-- Every nonzero modular normal is an embedded normal at a divisor of
the modulus. Its reduced linear functional is surjective. -/
theorem exists_surjective_divisor_normal {q n : ℕ} [NeZero q]
    {a : Fin n → ZMod q} (ha : a ≠ 0) :
    ∃ (r d : ℕ) (h : d * r = q), 1 < r ∧
      ∃ b : Fin n → ZMod r, a = divisorModulusEmbedding h ∘ b ∧
        Function.Surjective (fun x : Fin n → ZMod r => b ⬝ᵥ x) := by
  let L : (Fin n → ZMod q) →ₗ[ZMod q] ZMod q := dotProductBilin (ZMod q) (ZMod q) a
  have hL (x : Fin n → ZMod q) : L x = a ⬝ᵥ x := rfl
  let J := L.toAddMonoidHom.range.comap (Int.castAddHom (ZMod q))
  obtain ⟨e, he⟩ := AddSubgroup.exists_zmultiples_eq_of_zmultiples_eq_top Int.zmultiples_one J
  let d := e.natAbs
  have hJ : J = AddSubgroup.zmultiples (d : ℤ) := by
    rw [Int.zmultiples_natAbs, ← he]
    simp
  have hqJ : (q : ℤ) ∈ J := by
    change ∃ x, L x = ((q : ℤ) : ZMod q)
    exact ⟨0, by rw [map_zero, Int.cast_natCast, ZMod.natCast_self]⟩
  have hdq : d ∣ q := by
    rw [hJ, Int.mem_zmultiples_iff, Int.natCast_dvd_natCast] at hqJ
    exact hqJ
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdq (NeZero.pos q)
  let r := q / d
  have hr : d * r = q := Nat.mul_div_cancel' hdq
  have hdr (i : Fin n) : d ∣ (a i).val := by
    have hh : ((a i).val : ℤ) ∈ J := by
      change ∃ x, L x = (((a i).val : ℤ) : ZMod q)
      refine ⟨Pi.single i 1, ?_⟩
      rw [hL, dotProduct_single_one, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hJ, Int.mem_zmultiples_iff, Int.natCast_dvd_natCast] at hh
    exact hh
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    contrapose! ha
    ext i
    exact ha i
  have hanonzero := Nat.pos_of_ne_zero ((ZMod.val_eq_zero (a i)).not.mpr hi)
  have hdlt : d < q := (Nat.le_of_dvd hanonzero (hdr i)).trans_lt (ZMod.val_lt _)
  have hrpos : 1 < r := by
    by_contra! h
    have hh := Nat.mul_le_mul_left d h
    rw [hr, mul_one] at hh
    omega
  let b (i : Fin n) : ZMod r := ((a i).val / d : ℕ)
  have hab : a = divisorModulusEmbedding hr ∘ b := by
    funext i
    simp only [Function.comp_apply]
    change a i = divisorModulusEmbedding hr (((a i).val / d : ℕ) : ZMod r)
    calc
      _ = ((a i).val : ZMod q) := (ZMod.natCast_zmod_val _).symm
      _ = ((d * ((a i).val / d) : ℕ) : ZMod q) := by rw [Nat.mul_div_cancel' (hdr i)]
      _ = _ := by
        rw [show (((a i).val / d : ℕ) : ZMod r) = ((((a i).val / d : ℕ) : ℤ) : ZMod r)
          from (Int.cast_natCast _).symm, divisorModulusEmbedding_intCast, ← Int.natCast_mul,
          Int.cast_natCast]
  have hD : (d : ℤ) ∈ J := by
    rw [hJ]
    exact AddSubgroup.mem_zmultiples _
  change ∃ x, L x = ((d : ℤ) : ZMod q) at hD
  obtain ⟨x, hx⟩ := hD
  let y (i : Fin n) := ZMod.castHom (hr ▸ dvd_mul_left r d) (ZMod r) (x i)
  have hy : b ⬝ᵥ y = 1 := by
    apply divisorModulusEmbedding_injective hr
    have h1 : divisorModulusEmbedding hr 1 = (d : ZMod q) := by
      simpa only [Int.cast_one, mul_one, Int.cast_natCast] using
        divisorModulusEmbedding_intCast hr 1
    rw [divisorModulusEmbedding_dotProduct, ← hab, ← hL, hx, h1, Int.cast_natCast]
  refine ⟨r, d, hr, hrpos, b, hab, fun t => ⟨t • y, ?_⟩⟩
  change b ⬝ᵥ (t • y) = t
  rw [dotProduct_smul, hy, smul_eq_mul, mul_one]

private theorem binaryColumn_castHom {q r n : ℕ} (h : r ∣ q) (x : Fin n → Bool) :
    (fun i => ZMod.castHom h (ZMod r) (binaryColumn (ZMod q) x i)) = binaryColumn (ZMod r) x := by
  funext i
  cases hx : x i
  · exact (ZMod.castHom h (ZMod r)).map_one
      |> (by simpa only [binaryColumn, hx, Bool.false_eq_true, ite_false] using ·)
  · exact (ZMod.castHom h (ZMod r)).map_zero
      |> (by simpa only [binaryColumn, hx, ite_true] using ·)

theorem divisorModulusEmbedding_binary_dotProduct_eq_zero_iff {q r d n : ℕ} [NeZero q]
    (h : d * r = q) (a : Fin n → ZMod r) (x : Fin n → Bool) :
    (divisorModulusEmbedding h ∘ a) ⬝ᵥ binaryColumn (ZMod q) x = 0 ↔
      a ⬝ᵥ binaryColumn (ZMod r) x = 0 := by
  rw [← divisorModulusEmbedding_dotProduct, binaryColumn_castHom, ← map_zero (divisorModulusEmbedding h),
    (divisorModulusEmbedding_injective h).eq_iff]

theorem divisorModulusEmbedding_support {q r d n : ℕ} [NeZero q] (h : d * r = q)
    (a : Fin n → ZMod r) :
    (Finset.univ.filter (fun i => (divisorModulusEmbedding h ∘ a) i ≠ 0)) =
      Finset.univ.filter (fun i => a i ≠ 0) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  simpa only [map_zero] using (not_congr
    ((divisorModulusEmbedding_injective h).eq_iff (a := a i) (b := 0)))

theorem divisorModulusEmbedding_fourier_product {q r d n : ℕ} [NeZero q] [NeZero r]
    (h : d * r = q) (a : Fin n → ZMod r) :
    (∏ i, ‖bitFourierCoefficient ((divisorModulusEmbedding h ∘ a) i)‖) =
      ∏ i, ‖bitFourierCoefficient (a i)‖ := by
  simp only [Function.comp_apply, bitFourierCoefficient, divisorModulusEmbedding_character]

/-- An annihilating vector over a divisor lifts with exactly the same support. -/
theorem hasSparseBinaryNormal_of_dvd {q r n m s : ℕ} [NeZero q] (hr : r ∣ q)
    {R : Fin m → Fin n → Bool} (h : hasSparseBinaryNormal r n m s R) :
    hasSparseBinaryNormal q n m s R := by
  obtain ⟨d, hd⟩ := hr
  have he : d * r = q := (mul_comm _ _).trans hd.symm
  unfold hasSparseBinaryNormal at h ⊢
  obtain ⟨a, ha, hs, hz⟩ := h
  refine ⟨divisorModulusEmbedding he ∘ a, ?_, ?_, fun j => ?_⟩
  · intro hzero
    apply ha
    funext i
    apply divisorModulusEmbedding_injective he
    have hi := congrFun hzero i
    simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using hi
  · rw [divisorModulusEmbedding_support]
    exact hs
  · exact (divisorModulusEmbedding_binary_dotProduct_eq_zero_iff he a (R j)).mpr (hz j)

theorem surjective_dotProduct_nonzero_mod_prime {q p n : ℕ} (hp : p.Prime) (hdiv : p ∣ q)
    {a : Fin n → ZMod q} (ha : Function.Surjective (fun x : Fin n → ZMod q => a ⬝ᵥ x)) :
    (fun i => ZMod.castHom hdiv (ZMod p) (a i)) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  intro hzero
  obtain ⟨x, hx⟩ := ha 1
  replace hx : a ⬝ᵥ x = 1 := hx
  have h := congrArg (ZMod.castHom hdiv (ZMod p)) hx
  simp only [dotProduct, map_sum, map_mul, map_one] at h
  have hzero' (i : Fin n) : ZMod.castHom hdiv (ZMod p) (a i) = 0 := congrFun hzero i
  simp [hzero'] at h

theorem reduced_normal_dotProduct_eq_zero {q r n : ℕ} (h : r ∣ q) {a : Fin n → ZMod q}
    {x : Fin n → Bool} (hz : a ⬝ᵥ binaryColumn (ZMod q) x = 0) :
    (fun i => ZMod.castHom h (ZMod r) (a i)) ⬝ᵥ binaryColumn (ZMod r) x = 0 := by
  have hmap := congrArg (ZMod.castHom h (ZMod r)) hz
  have hbin (i : Fin n) : ZMod.castHom h (ZMod r) (binaryColumn (ZMod q) x i) =
      binaryColumn (ZMod r) x i := congrFun (binaryColumn_castHom h x) i
  simpa only [dotProduct, map_sum, map_mul, hbin, map_zero] using hmap

end BooleanThreshold
