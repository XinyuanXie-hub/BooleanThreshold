module

public import BooleanThreshold.Asymptotics
public import BooleanThreshold.JSSConditionalSlice
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.SuccPred.Archimedean

public section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanThreshold

/-- A fixed-weight sign slice has the corresponding binomial cardinality. -/
theorem signSlice_ncard {n : ℕ} (m : Fin (n + 1)) :
    (signSlice n m).ncard = n.choose m.val := by
  classical
  let e : (signSlice n m) ≃ {I : Finset (Fin n) // I.card = m.val} :=
    { toFun := fun x => ⟨Finset.univ.filter fun i => x.val i,
        congrArg Fin.val (show signWeight x.val = m from x.prop)⟩
      invFun := fun I => ⟨fun i => decide (i ∈ I.val), by
        change signWeight _ = m
        apply Fin.ext
        simpa [signWeight] using I.prop⟩
      left_inv := fun x => Subtype.ext (funext fun i => by cases h : x.val i <;> simp [h])
      right_inv := fun I => Subtype.ext (by ext i; simp) }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len,
    Fintype.card_fin]

theorem signSlice_nonempty {n : ℕ} (m : Fin (n + 1)) : (signSlice n m).Nonempty := by
  apply (Set.ncard_pos (signSlice n m).toFinite).mp
  exact (signSlice_ncard m).symm ▸ Nat.choose_pos (Nat.le_of_lt_succ m.isLt)

/-- The probability of exactly `z` successes in `n` independent trials of bias `p`. -/
@[expose] noncomputable def binomialWeight (n z : ℕ) (p : ℝ) : ℝ :=
  (n.choose z : ℝ) * p ^ z * (1 - p) ^ (n - z)

private theorem binomialWeight_step {n z : ℕ} (hz : z < n) (p : ℝ) :
    binomialWeight n (z + 1) p * (((z + 1 : ℕ) : ℝ) * (1 - p)) =
      binomialWeight n z p * (((n - z : ℕ) : ℝ) * p) := by
  have h : (n.choose (z + 1) : ℝ) * ((z + 1 : ℕ) : ℝ) =
      (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) := by exact_mod_cast Nat.choose_succ_right_eq n z
  have hp : (1 - p) ^ (n - z) = (1 - p) ^ (n - (z + 1)) * (1 - p) := by
    rw [← pow_succ, show n - (z + 1) + 1 = n - z by omega]
  simp only [binomialWeight, hp, pow_succ p z]
  calc
    _ = ((n.choose (z + 1) : ℝ) * ((z + 1 : ℕ) : ℝ)) *
      (p ^ z * (1 - p) ^ (n - (z + 1)) * p * (1 - p)) := by ring
    _ = _ := by rw [h]; ring

/-- The biased binomial distribution with mean `m` has mass at least
`1 / (n + 1)` at its mode `m`. -/
theorem binomialWeight_at_mean_ge {n m : ℕ} (hm : 0 < m) (hmn : m < n) :
    1 / ((n : ℝ) + 1) ≤ binomialWeight n m ((m : ℝ) / (n : ℝ)) := by
  let p : ℝ := (m : ℝ) / (n : ℝ)
  let W (z : ℕ) := binomialWeight n z p
  have hn : 0 < (n : ℝ) := by exact_mod_cast (hm.trans hmn)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmn' : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hp : 0 < p := div_pos hm' hn
  have hp₁ : p < 1 := (div_lt_one hn).mpr hmn'
  have hpN : p * (n : ℝ) = m := div_mul_cancel₀ _ hn.ne'
  have hpcN : (1 - p) * (n : ℝ) = (n : ℝ) - (m : ℝ) := by rw [sub_mul, one_mul, hpN]
  let A (z : ℕ) : ℝ := ((z + 1 : ℕ) : ℝ) * (1 - p)
  let B (z : ℕ) : ℝ := ((n - z : ℕ) : ℝ) * p
  have ha (z : ℕ) : 0 < A z := mul_pos (by positivity) (sub_pos.mpr hp₁)
  have hW (z : ℕ) : 0 ≤ W z := by dsimp [W, binomialWeight]; positivity
  have hcmp (z : ℕ) (hz : z < n) : (B z - A z) * (n : ℝ) =
      (n : ℝ) * ((m : ℝ) - ((z : ℝ) + 1)) + (m : ℝ) := by
    rw [sub_mul]
    simp only [B, A, mul_assoc, hpN, hpcN, Nat.cast_sub hz.le, Nat.cast_add, Nat.cast_one]
    ring
  have hup : MonotoneOn W (Set.Iic m) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Iic
    intro z _ _ hz
    have hz' : z + 1 ≤ m := hz
    have hzn : z < n := by omega
    have hh : 0 ≤ (m : ℝ) - ((z : ℝ) + 1) := by exact sub_nonneg.mpr (by exact_mod_cast hz')
    have hAB : A z ≤ B z := by
      apply le_of_mul_le_mul_right _ hn
      linarith only [hcmp z hzn, mul_nonneg hn.le hh, hm']
    apply le_of_mul_le_mul_right _ (ha z)
    rw [show W (z + 1) * A z = W z * B z from binomialWeight_step hzn p]
    exact mul_le_mul_of_nonneg_left hAB (hW z)
  have hdown : AntitoneOn W (Set.Icc m n) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Icc
    intro z _ hz hz'
    obtain ⟨hzm, _⟩ : m ≤ z ∧ z ≤ n := hz
    have hzn : z < n := Nat.lt_of_succ_le hz'.2
    have hh : (m : ℝ) - ((z : ℝ) + 1) ≤ -1 := by
      have hh' : (m : ℝ) ≤ z := by exact_mod_cast hzm
      linarith only [hh']
    have hBA : B z ≤ A z := by
      apply le_of_mul_le_mul_right _ hn
      linarith only [hcmp z hzn, mul_le_mul_of_nonneg_left hh hn.le, hmn']
    apply le_of_mul_le_mul_right _ (ha z)
    rw [show W (z + 1) * A z = W z * B z from binomialWeight_step hzn p]
    exact mul_le_mul_of_nonneg_left hBA (hW z)
  have hmode (z : ℕ) (hz : z ≤ n) : W z ≤ W m := by
    by_cases hzm : z ≤ m
    · exact hup hzm (Set.mem_Iic.mpr (le_refl m)) hzm
    · have h := le_of_not_ge hzm
      exact hdown ⟨le_rfl, hmn.le⟩ ⟨h, hz⟩ h
  have hsum : (∑ z ∈ Finset.range (n + 1), W z) = 1 := by
    calc
      _ = (p + (1 - p)) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro _ _
        unfold W binomialWeight
        ring
      _ = _ := by rw [show p + (1 - p) = 1 by ring, one_pow]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  calc
    _ = ∑ z ∈ Finset.range (n + 1), W z := hsum.symm
    _ ≤ ∑ _z ∈ Finset.range (n + 1), W m :=
      Finset.sum_le_sum fun z hz => hmode z (Nat.le_of_lt_succ (Finset.mem_range.mp hz))
    _ = W m * ((n : ℝ) + 1) := by simp [mul_comm]

private def mixedCount {k : ℕ} (y : Fin k × Bool → Bool) : ℕ :=
  (Finset.univ.filter fun i => y (i, false) ≠ y (i, true)).card

private noncomputable def bitWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

private noncomputable def cubeWeight {n : ℕ} (p : ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, bitWeight p (x i)

private theorem cubeWeight_on_slice {n : ℕ} (m : Fin (n + 1)) (p : ℝ)
    {x : Fin n → Bool} (hx : x ∈ signSlice n m) :
    cubeWeight p x = p ^ m.val * (1 - p) ^ (n - m.val) := by
  classical
  let t := Finset.univ.filter fun i => x i
  have ht : t.card = m.val := congrArg Fin.val (show signWeight x = m from hx)
  have hf : (Finset.univ.filter fun i => ¬ (x i : Prop)).card = n - m.val := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => (x i : Prop))
    rw [Finset.card_univ, Fintype.card_fin] at h
    change t.card + _ = n at h
    omega
  simp only [cubeWeight, bitWeight, Finset.prod_ite, Finset.prod_const, hf]
  rw [show (Finset.univ.filter fun i => (x i : Prop)).card = m.val from ht]

private theorem product_bitWeights_sum_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    (∑ x : ι → Bool, ∏ i, bitWeight p (x i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun _ : ι => bitWeight p)]
  have h : (∑ b : Bool, bitWeight p b) = 1 := by simp [bitWeight]
  simp only [h, Finset.prod_const_one]

private theorem cubeWeight_factor {n k : ℕ} (p : ℝ) (e : Fin k × Bool ↪ Fin n)
    (x : Fin n → Bool) :
    cubeWeight p x = (∏ j : Fin k × Bool, bitWeight p (x (e j))) *
      ∏ j : {i : Fin n // i ∉ Set.range e}, bitWeight p (x j.val) := by
  classical
  let I := Finset.univ.filter (fun i : Fin n => i ∈ Set.range e)
  have hI (i : Fin n) : i ∈ I ↔ i ∈ Set.range e := by simp [I]
  have hJ (i : Fin n) : i ∈ Finset.univ \ I ↔ i ∉ Set.range e := by simp [hI]
  unfold cubeWeight
  rw [← Finset.prod_sdiff (Finset.subset_univ I) (f := fun i => bitWeight p (x i)), mul_comm,
    Finset.prod_subtype I hI, Finset.prod_subtype _ hJ]
  congr 1
  exact (Fintype.prod_equiv (Equiv.ofInjective e e.injective) _ _ (fun _ => rfl)).symm

private noncomputable def mixedPairWeight (p : ℝ) (b : Bool → Bool) : ℝ :=
  (∏ i : Bool, bitWeight p (b i)) * Real.exp (-(if b false ≠ b true then 1 else 0))

private theorem sum_mixedPairWeight (p : ℝ) :
    (∑ b : Bool → Bool, mixedPairWeight p b) = 1 - 2 * p * (1 - p) * (1 - Real.exp (-1)) := by
  let φ := Equiv.boolArrowEquivProd Bool
  rw [Fintype.sum_equiv φ _ (fun s => mixedPairWeight p (φ.symm s)) (fun x => by simp)]
  rw [Fintype.sum_prod_type]
  simp [φ, Equiv.boolArrowEquivProd, mixedPairWeight, bitWeight]
  ring

private theorem sum_weighted_exp_mixed {n k : ℕ} (p : ℝ) (e : Fin k × Bool ↪ Fin n) :
    (∑ x : Fin n → Bool, cubeWeight p x * Real.exp (-(mixedCount (x ∘ e) : ℝ))) =
      (1 - 2 * p * (1 - p) * (1 - Real.exp (-1))) ^ k := by
  classical
  let R := fun i : Fin n => i ∈ Set.range e
  let φ : (Fin n → Bool) ≃ ((Fin k × Bool → Bool) × ({i : Fin n // ¬ R i} → Bool)) :=
    (Equiv.piEquivPiSubtypeProd R (fun _ => Bool)).trans
      (Equiv.prodCongr (Equiv.piCongrLeft (fun _ : Subtype R => Bool)
        (Equiv.ofInjective e e.injective)).symm (Equiv.refl _))
  let f (y : Fin k × Bool → Bool) := (∏ j, bitWeight p (y j)) * Real.exp (-(mixedCount y : ℝ))
  let g (z : {i : Fin n // ¬ R i} → Bool) := ∏ j, bitWeight p (z j)
  have hφ₁ (x : Fin n → Bool) : (φ x).1 = x ∘ e := by
    funext j
    simp only [φ, Equiv.trans_apply, Equiv.prodCongr_apply]
    rfl
  have hφ₂ (x : Fin n → Bool) : (φ x).2 = fun j => x j.val := rfl
  have hsum : (∑ x : Fin n → Bool, cubeWeight p x * Real.exp (-(mixedCount (x ∘ e) : ℝ))) =
      ∑ y : Fin k × Bool → Bool, f y := by
    rw [Fintype.sum_equiv φ _ (fun s => f s.1 * g s.2) (fun x => by
      rw [hφ₁, hφ₂, cubeWeight_factor p e x]
      simp only [f, g, Function.comp_apply]
      ring)]
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, g, product_bitWeights_sum_one, mul_one]
  rw [hsum]
  let ψ := Equiv.curry (Fin k) Bool Bool
  have hprod (y : Fin k × Bool → Bool) : f y = ∏ i, mixedPairWeight p (ψ y i) := by
    have hc : (mixedCount y : ℝ) = ∑ i, if y (i, false) ≠ y (i, true) then (1 : ℝ) else 0 := by
      exact (Finset.sum_boole (fun i : Fin k => y (i, false) ≠ y (i, true)) Finset.univ).symm
    simp only [f, ψ, mixedPairWeight, Equiv.curry_apply, Finset.prod_mul_distrib,
      hc, ← Finset.sum_neg_distrib, Real.exp_sum, Fintype.prod_prod_type]
    rfl
  rw [Fintype.sum_equiv ψ _ (fun z => ∏ i, mixedPairWeight p (z i)) hprod,
    ← Fintype.prod_sum (fun _ : Fin k => mixedPairWeight p), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, sum_mixedPairWeight]

private theorem slice_pairs_mixed_aux {n k : ℕ} {η σ : ℝ} (hη : 0 < η)
    (hn : 0 < n) (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1))
    (hk : σ * (n : ℝ) ≤ (k : ℝ)) (hml : η * (n : ℝ) ≤ (m.val : ℝ))
    (hmu : (m.val : ℝ) ≤ (1 - η) * (n : ℝ)) :
    (uniformOn (signSlice n m)).real {x | (mixedCount (x ∘ e) : ℝ) < (σ * η ^ 2 / 2) * (n : ℝ)} ≤
      ((n : ℝ) + 1) * Real.exp (-(σ * η ^ 2 / 2) * (n : ℝ)) := by
  classical
  let p : ℝ := (m.val : ℝ) / (n : ℝ)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : η ≤ p := (le_div_iff₀ hn').mpr hml
  have hp' : p ≤ 1 - η := (div_le_iff₀ hn').mpr hmu
  have hpc : η ≤ 1 - p := by linarith only [hp']
  have hp₀ : 0 < p := hη.trans_le hp
  have hpc₀ : 0 < 1 - p := hη.trans_le hpc
  have hm : 0 < m.val := by exact_mod_cast ((mul_pos hη hn').trans_le hml)
  have hmn : m.val < n := by
    have h := mul_lt_mul_of_pos_right (show 1 - η < 1 by linarith only [hη]) hn'
    have hh : (m.val : ℝ) < (n : ℝ) := hmu.trans_lt (by simpa only [one_mul] using h)
    exact_mod_cast hh
  let τ := σ * η ^ 2 / 2
  let y := τ * (n : ℝ)
  let W := p ^ m.val * (1 - p) ^ (n - m.val)
  let α := Real.exp (-y)
  let E : Set (Fin n → Bool) := {x | (mixedCount (x ∘ e) : ℝ) < y}
  let S := signSlice n m
  let F := (S ∩ E).toFinite.toFinset
  let μ := uniformOn S
  let G (x : Fin n → Bool) := cubeWeight p x * Real.exp (-(mixedCount (x ∘ e) : ℝ))
  have hG (x : Fin n → Bool) : 0 ≤ G x := by
    apply mul_nonneg _ (Real.exp_nonneg _)
    apply Finset.prod_nonneg
    intro i _
    cases x i <;> simp [bitWeight, hp₀.le, hpc₀.le]
  have hweighted : (F.card : ℝ) * (W * α) ≤ ∑ x : Fin n → Bool, G x := by
    calc
      _ = ∑ _x ∈ F, W * α := by simp
      _ ≤ ∑ x ∈ F, G x := by
        apply Finset.sum_le_sum
        intro x hx
        have hx' : x ∈ S ∩ E := (Set.Finite.mem_toFinset (S ∩ E).toFinite).mp hx
        change W * α ≤ cubeWeight p x * Real.exp (-(mixedCount (x ∘ e) : ℝ))
        rw [cubeWeight_on_slice m p hx'.1]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_monotone
        exact neg_le_neg (show _ ≤ y from (show _ < y from hx'.2).le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F) (fun x _ _ => hG x)
  have hchoose : (n.choose m.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn.le).ne'
  have hcard : μ.real E * (n.choose m.val : ℝ) = (F.card : ℝ) := by
    change (uniformOn S).real E * _ = _
    rw [uniformOn_finite_real_eq_card S.toFinite, show S.ncard = n.choose m.val from signSlice_ncard m,
      div_mul_cancel₀ _ hchoose]
    norm_cast
    exact Set.ncard_eq_toFinset_card _
  have hmass : μ.real E / ((n : ℝ) + 1) * α ≤ ∑ x : Fin n → Bool, G x := by
    calc
      _ = μ.real E * (1 / ((n : ℝ) + 1)) * α := by rw [div_eq_mul_inv, one_div]
      _ ≤ μ.real E * binomialWeight n m.val p * α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (binomialWeight_at_mean_ge hm hmn) measureReal_nonneg)
          (Real.exp_nonneg _)
      _ = (F.card : ℝ) * (W * α) := by
        change μ.real E * ((n.choose m.val : ℝ) * p ^ m.val * (1 - p) ^ (n - m.val)) * α = _
        calc
          _ = (μ.real E * (n.choose m.val : ℝ)) * (W * α) := by dsimp [W]; ring
          _ = _ := by rw [hcard]
      _ ≤ _ := hweighted
  let q := 2 * p * (1 - p) * (1 - Real.exp (-1))
  have hexpHalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith only [Real.add_one_le_exp (1 : ℝ)])
  have hq₁ : q ≤ 1 := by
    have hpair : 2 * p * (1 - p) ≤ 1 := by nlinarith only [sq_nonneg (p - 1 / 2)]
    dsimp [q]
    exact mul_le_of_le_one_right (by positivity) (by linarith only [Real.exp_pos (-1)]) |>.trans hpair
  have hq₀ : η ^ 2 ≤ q := by
    have hp₂ : η ^ 2 ≤ p * (1 - p) := by
      rw [sq]
      exact mul_le_mul hp hpc hη.le hp₀.le
    calc
      _ = 2 * (η ^ 2) * (1 / 2) := by ring
      _ ≤ 2 * (p * (1 - p)) * (1 - Real.exp (-1)) := by gcongr; linarith only [hexpHalf]
      _ = _ := by dsimp [q]; ring
  have htail : ∑ x : Fin n → Bool, G x ≤ Real.exp (-(2 * y)) := by
    change (∑ x : Fin n → Bool, cubeWeight p x * Real.exp (-(mixedCount (x ∘ e) : ℝ))) ≤ _
    rw [sum_weighted_exp_mixed p e]
    change (1 - q) ^ k ≤ _
    have hb := (Real.one_sub_le_exp_neg q).trans (Real.exp_monotone (neg_le_neg hq₀))
    calc
      _ ≤ Real.exp (-(η ^ 2)) ^ k := pow_le_pow_left₀ (sub_nonneg.mpr hq₁) hb _
      _ = Real.exp (-(η ^ 2) * (k : ℝ)) := by rw [mul_comm, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_monotone (by
        have h := mul_le_mul_of_nonneg_left hk (sq_nonneg η)
        dsimp [y, τ]
        nlinarith only [h])
  change μ.real E ≤ ((n : ℝ) + 1) * Real.exp (-τ * (n : ℝ))
  rw [neg_mul]
  change μ.real E ≤ ((n : ℝ) + 1) * Real.exp (-y)
  calc
    _ = (μ.real E / ((n : ℝ) + 1) * α) * (((n : ℝ) + 1) / α) := by
      field_simp [show α ≠ 0 from (Real.exp_pos _).ne', show (n : ℝ) + 1 ≠ 0 by positivity]
    _ ≤ Real.exp (-(2 * y)) * (((n : ℝ) + 1) / α) :=
      mul_le_mul_of_nonneg_right (hmass.trans htail) (by dsimp [α]; positivity)
    _ = _ := by
      dsimp only [α]
      rw [div_eq_mul_inv, ← Real.exp_neg, mul_left_comm, ← Real.exp_add]
      congr 2
      ring

/-- A fixed-weight sign vector with both signs present at linear density
has linearly many discordant pairs among any linearly many disjoint pairs,
except on an event of exponentially small probability. -/
theorem slice_pairs_many_mixed_eventually {η σ : ℝ} (hη : 0 < η) (hσ : 0 < σ) :
    ∃ τ > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (k : ℕ) (e : Fin k × Bool ↪ Fin n) (m : Fin (n + 1)),
        σ * (n : ℝ) ≤ (k : ℝ) → η * (n : ℝ) ≤ (m.val : ℝ) →
        (m.val : ℝ) ≤ (1 - η) * (n : ℝ) →
        (uniformOn (signSlice n m)).real {x |
          ((Finset.univ.filter fun i => x (e (i, false)) ≠ x (e (i, true))).card : ℝ) < τ * (n : ℝ)} ≤
            Real.exp (-c * (n : ℝ)) := by
  let τ := σ * η ^ 2 / 2
  let c := τ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨τ, hτ, c, hc, ?_⟩
  have hlimit := tendsto_pow_const_div_const_pow_of_one_lt 1 (Real.one_lt_exp_iff.mpr hc)
  filter_upwards [hlimit.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hn hn₁ k e m hk hl hu
  have hbase : (n : ℝ) + 1 ≤ Real.exp (c * (n : ℝ)) := by
    have h := (div_le_iff₀ (show 0 < Real.exp c ^ n by positivity)).mp hn
    rw [pow_one, ← Real.exp_nat_mul, mul_comm (n : ℝ)] at h
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
    linarith only [h, hn']
  refine (slice_pairs_mixed_aux hη (by omega) e m hk hl hu).trans ?_
  calc
    _ ≤ Real.exp (c * (n : ℝ)) * Real.exp (-τ * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [c]; ring

end BooleanThreshold
