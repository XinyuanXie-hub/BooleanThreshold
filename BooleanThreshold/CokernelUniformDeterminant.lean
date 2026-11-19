module

public import BooleanThreshold.CokernelValuationCap

@[expose] public section

open Matrix
open scoped BigOperators

namespace BooleanThreshold

/-- Form a square matrix from its first column and the sequence of remaining columns. -/
def matrixWithFirstColumn {n : ℕ} {R : Type*} (x : Fin (n + 1) → R)
    (y : Fin n → Fin (n + 1) → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i => Fin.cons (x i) (fun j => y j i)

private theorem det_matrixWithFirstColumn {n : ℕ} {R : Type*} [CommRing R]
    (x : Fin (n + 1) → R) (y : Fin n → Fin (n + 1) → R)
    (q : Fin n → R) (hq : ∀ i, x i.succ = q i * x 0) :
    (matrixWithFirstColumn x y).det =
      x 0 * (Matrix.of fun i j => y j i.succ - q i * y j 0).det := by
  classical
  let A := matrixWithFirstColumn x y
  let E := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).updateCol 0
    (Fin.cons 1 fun i => -q i)
  have hE00 : E 0 0 = 1 := by
    simp [E]
  have hE0s (j : Fin n) : E 0 j.succ = 0 := by
    simp [E, Ne.symm j.succ_ne_zero]
  have hEss (i j : Fin n) : E i.succ j.succ = (1 : Matrix (Fin n) (Fin n) R) i j := by
    simp [E, Matrix.one_apply]
  have hE : E.det = 1 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hEsub : E.submatrix Fin.succ Fin.succ = 1 := by
      ext i j
      exact hEss i j
    simp [hE00, hE0s, hEsub, Fin.succAbove_zero]
  have htop (j : Fin (n + 1)) : (E * A) 0 j = A 0 j := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hE00, hE0s]
  have hbot (i : Fin n) (j : Fin (n + 1)) :
      (E * A) i.succ j = A i.succ j - q i * A 0 j := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [E, Matrix.updateCol_self, Fin.cons_succ, hEss, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, neg_mul, sub_eq_add_neg]
    exact add_comm _ _
  have hzero (i : Fin n) : (E * A) i.succ 0 = 0 := by
    rw [hbot]
    simp [A, matrixWithFirstColumn, hq]
  have hsub : (E * A).submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j => y j i.succ - q i * y j 0) := by
    ext i j
    rw [Matrix.submatrix_apply, hbot]
    rfl
  calc
    A.det = (E * A).det := by rw [Matrix.det_mul, hE, one_mul]
    _ = x 0 * (Matrix.of fun i j => y j i.succ - q i * y j 0).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, htop, Fin.succAbove_zero, hsub, hzero,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rfl

/-- If a first-column entry divides all the entries below it, elimination
reduces the determinant count to a smaller square matrix. -/
theorem matrixWithFirstColumn_det_zero_card {n : ℕ} {R : Type*} [CommRing R] [Finite R]
    (x : Fin (n + 1) → R) (h : ∀ i : Fin n, x 0 ∣ x i.succ) :
    Nat.card { y : Fin n → Fin (n + 1) → R // (matrixWithFirstColumn x y).det = 0 } =
      Nat.card R ^ n * Nat.card
        { L : Matrix (Fin n) (Fin n) R // x 0 * L.det = 0 } := by
  classical
  choose q hq using h
  have hq' (i : Fin n) : x i.succ = q i * x 0 := by rw [hq i, mul_comm]
  let e : (Fin n → Fin (n + 1) → R) ≃
      (Fin n → R) × Matrix (Fin n) (Fin n) R :=
    { toFun := fun y => (fun j => y j 0, Matrix.of fun i j => y j i.succ - q i * y j 0)
      invFun := fun p j => Fin.cons (p.1 j) (fun i => p.2 i j + q i * p.1 j)
      left_inv := by
        intro y
        funext j i
        refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · simp
      right_inv := by
        intro p
        apply Prod.ext
        · rfl
        · ext i j
          simp }
  have hdet (y : Fin n → Fin (n + 1) → R) :
      (matrixWithFirstColumn x y).det = 0 ↔ x 0 * (e y).2.det = 0 := by
    rw [det_matrixWithFirstColumn x y q hq']
    rfl
  let swap := Equiv.prodComm (Fin n → R) (Matrix (Fin n) (Fin n) R)
  let eswap := swap.subtypeEquiv
    (p := fun z => x 0 * z.2.det = 0) (q := fun z => x 0 * z.1.det = 0)
    (fun _ => Iff.rfl)
  rw [Nat.card_congr (e.subtypeEquiv (q := fun z => x 0 * z.2.det = 0) hdet),
    Nat.card_congr eswap, Nat.card_congr
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun L : Matrix (Fin n) (Fin n) R =>
        x 0 * L.det = 0)),
    Nat.card_prod, Nat.card_fun, Nat.card_fin, mul_comm]

/-- Elimination at any row containing a first-column divisor of the other
entries gives the same conditional determinant count. -/
theorem matrixWithFirstColumn_det_zero_card_of_pivot {n : ℕ} {R : Type*} [CommRing R]
    [Finite R] (x : Fin (n + 1) → R) (i : Fin (n + 1)) (h : ∀ j, x i ∣ x j) :
    Nat.card { y : Fin n → Fin (n + 1) → R // (matrixWithFirstColumn x y).det = 0 } =
      Nat.card R ^ n * Nat.card { L : Matrix (Fin n) (Fin n) R // x i * L.det = 0 } := by
  classical
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i
  let z := x ∘ σ
  have hz : z 0 = x i := by simp [z, σ]
  let e : (Fin n → Fin (n + 1) → R) ≃ (Fin n → Fin (n + 1) → R) :=
    { toFun := fun y j k => y j (σ k)
      invFun := fun y j k => y j (σ.symm k)
      left_inv := by intro y; funext j k; simp
      right_inv := by intro y; funext j k; simp }
  have he (y : Fin n → Fin (n + 1) → R) :
      (matrixWithFirstColumn x y).det = 0 ↔ (matrixWithFirstColumn z (e y)).det = 0 := by
    have heq : matrixWithFirstColumn z (e y) =
        (matrixWithFirstColumn x y).submatrix σ id := by
      ext r c
      rfl
    rw [heq, Matrix.det_permute]
    let u := Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign σ)
    change (matrixWithFirstColumn x y).det = 0 ↔
      (u : R) * (matrixWithFirstColumn x y).det = 0
    simp
  rw [Nat.card_congr (e.subtypeEquiv
    (q := fun y => (matrixWithFirstColumn z y).det = 0) he),
    matrixWithFirstColumn_det_zero_card z (fun j => hz ▸ h (σ j.succ)), hz]

/-- The valuation of a residue modulo a prime power, truncated at the
exponent for the zero residue. -/
def zmodPrimeOrder (p a : ℕ) (x : ZMod (p ^ a)) : ℕ :=
  if x = 0 then a else x.val.factorization p

private theorem zmodPrimeOrder_lt {p a : ℕ} [Fact p.Prime] {x : ZMod (p ^ a)}
    (hx : x ≠ 0) : zmodPrimeOrder p a x < a := by
  have hp : p.Prime := Fact.out
  have hx' : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  simpa only [zmodPrimeOrder, ite_eq_right hx] using
    (Nat.pow_lt_pow_iff_right hp.one_lt).1 ((Nat.ordProj_le p hx').trans_lt x.val_lt)

private theorem le_zmodPrimeOrder_iff {p a t : ℕ} [Fact p.Prime]
    (x : ZMod (p ^ a)) (ht : t ≤ a) :
    t ≤ zmodPrimeOrder p a x ↔ p ^ t ∣ x.val := by
  have hp : p.Prime := Fact.out
  by_cases hx : x = 0
  · subst x
    simp [zmodPrimeOrder, ht]
  · have hx' : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
    simpa only [zmodPrimeOrder, ite_eq_right hx] using
      (hp.pow_dvd_iff_le_factorization hx' : p ^ t ∣ x.val ↔ t ≤ x.val.factorization p).symm

private theorem zmod_eq_pow_mul_unit {p a : ℕ} [Fact p.Prime]
    {x : ZMod (p ^ a)} (hx : x ≠ 0) :
    ∃ u : (ZMod (p ^ a))ˣ, x = (p : ZMod (p ^ a)) ^ zmodPrimeOrder p a x * u := by
  have hp : p.Prime := Fact.out
  have hx' : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  have ha : 0 < a := Nat.zero_lt_of_lt (zmodPrimeOrder_lt hx)
  have hu : IsUnit ((ordCompl[p] x.val : ℕ) : ZMod (p ^ a)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).mpr (Nat.not_dvd_ordCompl hp hx')
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec, zmodPrimeOrder, ite_eq_right hx, ← Nat.cast_pow, ← Nat.cast_mul,
    Nat.ordProj_mul_ordCompl_eq_self, ZMod.natCast_zmod_val]

private theorem zmod_dvd_of_order_le {p a : ℕ} [Fact p.Prime]
    {x : ZMod (p ^ a)} (hx : x ≠ 0) {y : ZMod (p ^ a)}
    (h : zmodPrimeOrder p a x ≤ zmodPrimeOrder p a y) : x ∣ y := by
  obtain ⟨u, hu⟩ := zmod_eq_pow_mul_unit hx
  rw [hu, u.isUnit.mul_right_dvd]
  have hd := (le_zmodPrimeOrder_iff y (zmodPrimeOrder_lt hx).le).mp h
  obtain ⟨z, hz⟩ := hd
  refine ⟨(z : ZMod (p ^ a)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val y, hz, Nat.cast_mul, Nat.cast_pow]

private theorem zmod_pow_mul_eq_zero_iff {p a t : ℕ} [Fact p.Prime]
    (d : ZMod (p ^ a)) (ht : t ≤ a) :
    (p : ZMod (p ^ a)) ^ t * d = 0 ↔
      ZMod.castHom (pow_dvd_pow p (Nat.sub_le a t)) (ZMod (p ^ (a - t))) d = 0 := by
  have hp : p.Prime := Fact.out
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  conv_lhs =>
    rw [← ZMod.natCast_zmod_val d, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  have hpow : p ^ a = p ^ t * p ^ (a - t) := by
    rw [← pow_add, Nat.add_sub_of_le ht]
  exact (Iff.of_eq (congrArg (fun m => m ∣ p ^ t * d.val) hpow)).trans
    (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos t))

/-- The fraction of points of a finite type satisfying a predicate. -/
noncomputable def finiteUniformFraction {Ω : Type*} (event : Ω → Prop) : ℝ :=
  (Nat.card (Subtype event) : ℝ) / Nat.card Ω

private theorem card_addHom_preimage {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (s : H → Prop) :
    Nat.card {x : G // s (f x)} = Nat.card f.ker * Nat.card (Subtype s) := by
  classical
  let g (y : H) := Classical.choose (hf y)
  have hg (y : H) : f (g y) = y := Classical.choose_spec (hf y)
  let e : {x : G // s (f x)} ≃ f.ker × Subtype s :=
    { toFun := fun x =>
        (⟨(x : G) - g (f x), by simp [hg]⟩, ⟨f x, x.property⟩)
      invFun := fun y => ⟨(y.1 : G) + g y.2, by
        simpa [hg, AddMonoidHom.mem_ker.mp y.1.property] using y.2.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (x : G) - g (f x) + g (f x) = x
        exact sub_add_cancel _ _
      right_inv := by
        intro y
        have h : f ((y.1 : G) + g y.2) = y.2 := by
          simp [hg, AddMonoidHom.mem_ker.mp y.1.property]
        apply Prod.ext
        · apply Subtype.ext
          change (y.1 : G) + g y.2 - g (f ((y.1 : G) + g y.2)) = y.1
          rw [h, add_sub_cancel_right]
        · apply Subtype.ext
          exact h }
  rw [Nat.card_congr e, Nat.card_prod]

/-- A surjective additive homomorphism sends the uniform law on its finite domain
to the uniform law on its codomain. -/
theorem finiteUniformFraction_addHom_preimage {G H : Type*} [AddGroup G] [AddGroup H]
    [Finite G] (f : G →+ H) (hf : Function.Surjective f) (s : H → Prop) :
    finiteUniformFraction (fun x : G => s (f x)) = finiteUniformFraction s := by
  have hker : (Nat.card f.ker : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have htotal : Nat.card G = Nat.card f.ker * Nat.card H := by
    simpa only [Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun _ : G => True) (by simp)),
      Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun _ : H => True) (by simp))]
      using card_addHom_preimage f hf (fun _ => True)
  unfold finiteUniformFraction
  rw [card_addHom_preimage f hf s, htotal, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left _ _ hker

private theorem finiteUniformFraction_det_reduce {n p a t : ℕ} [Fact p.Prime] (ht : t ≤ a) :
    finiteUniformFraction (fun L : Matrix (Fin n) (Fin n) (ZMod (p ^ a)) =>
      (p : ZMod (p ^ a)) ^ t * L.det = 0) =
      finiteUniformFraction (fun L : Matrix (Fin n) (Fin n) (ZMod (p ^ (a - t))) =>
        L.det = 0) := by
  let f := ZMod.castHom (pow_dvd_pow p (Nat.sub_le a t)) (ZMod (p ^ (a - t)))
  let F : Matrix (Fin n) (Fin n) (ZMod (p ^ a)) →+
      Matrix (Fin n) (Fin n) (ZMod (p ^ (a - t))) := f.mapMatrix.toAddMonoidHom
  have hF : Function.Surjective F := by
    intro L
    choose A hA using fun i j => ZMod.castHom_surjective (pow_dvd_pow p (Nat.sub_le a t)) (L i j)
    refine ⟨Matrix.of A, ?_⟩
    ext i j
    exact hA i j
  have hiff (L : Matrix (Fin n) (Fin n) (ZMod (p ^ a))) :
      (p : ZMod (p ^ a)) ^ t * L.det = 0 ↔ (F L).det = 0 := by
    rw [zmod_pow_mul_eq_zero_iff L.det ht]
    change f L.det = 0 ↔ (f.mapMatrix L).det = 0
    rw [f.map_det]
  have hfun := funext fun L => propext (hiff L)
  rw [hfun]
  exact finiteUniformFraction_addHom_preimage F hF (fun L => L.det = 0)

/-- The least truncated valuation of the entries in a nonempty column. -/
def zmodColumnPrimeOrder {n : ℕ} (p a : ℕ) (x : Fin (n + 1) → ZMod (p ^ a)) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => zmodPrimeOrder p a (x i))

private theorem zmodColumnPrimeOrder_le {n p a : ℕ} (x : Fin (n + 1) → ZMod (p ^ a))
    (i : Fin (n + 1)) : zmodColumnPrimeOrder p a x ≤ zmodPrimeOrder p a (x i) :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem zmodColumnPrimeOrder_lt {n p a : ℕ} [Fact p.Prime]
    {x : Fin (n + 1) → ZMod (p ^ a)} (hx : x ≠ 0) :
    zmodColumnPrimeOrder p a x < a := by
  have h : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := h
  exact (zmodColumnPrimeOrder_le x i).trans_lt (zmodPrimeOrder_lt hi)

private theorem finiteUniformFraction_matrixWithFirstColumn {n : ℕ} {R : Type*}
    [CommRing R] [Finite R] (x : Fin (n + 1) → R) (i : Fin (n + 1))
    (hi : ∀ j, x i ∣ x j) :
    finiteUniformFraction (fun y : Fin n → Fin (n + 1) → R =>
      (matrixWithFirstColumn x y).det = 0) =
      finiteUniformFraction (fun L : Matrix (Fin n) (Fin n) R => x i * L.det = 0) := by
  have hcard : Nat.card (Fin n → Fin (n + 1) → R) =
      Nat.card R ^ n * Nat.card (Matrix (Fin n) (Fin n) R) := by
    change Nat.card (Fin n → Fin (n + 1) → R) =
      Nat.card R ^ n * Nat.card (Fin n → Fin n → R)
    simp only [Nat.card_fun, Nat.card_fin]
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hR : (Nat.card R : ℝ) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  unfold finiteUniformFraction
  rw [matrixWithFirstColumn_det_zero_card_of_pivot x i hi, hcard]
  simp only [Nat.cast_mul, Nat.cast_pow]
  exact mul_div_mul_left _ _ hR

/-- For a fixed nonzero first column, the determinant tail in the prime-power
ring is the smaller determinant tail with exponent reduced by the column's order. -/
theorem finiteUniformFraction_matrixWithFirstColumn_prime_power {n p a : ℕ} [Fact p.Prime]
    (x : Fin (n + 1) → ZMod (p ^ a)) (hx : x ≠ 0) :
    finiteUniformFraction (fun y : Fin n → Fin (n + 1) → ZMod (p ^ a) =>
      (matrixWithFirstColumn x y).det = 0) =
      finiteUniformFraction (fun L : Matrix (Fin n) (Fin n)
        (ZMod (p ^ (a - zmodColumnPrimeOrder p a x))) => L.det = 0) := by
  let t := zmodColumnPrimeOrder p a x
  have ht : t < a := zmodColumnPrimeOrder_lt hx
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    (fun i => zmodPrimeOrder p a (x i))
  change t = zmodPrimeOrder p a (x i) at hi
  have hix : x i ≠ 0 := by
    intro heq
    have h : t = a := by simpa [heq, zmodPrimeOrder] using hi
    omega
  have hd (j : Fin (n + 1)) : x i ∣ x j :=
    zmod_dvd_of_order_le hix (hi ▸ zmodColumnPrimeOrder_le x j)
  rw [finiteUniformFraction_matrixWithFirstColumn x i hd]
  obtain ⟨u, hu⟩ := zmod_eq_pow_mul_unit hix
  have heq : (fun L : Matrix (Fin n) (Fin n) (ZMod (p ^ a)) => x i * L.det = 0) =
      (fun L => (p : ZMod (p ^ a)) ^ t * L.det = 0) := by
    funext L
    rw [hu, ← hi, mul_comm ((p : ZMod (p ^ a)) ^ t) _, mul_assoc]
    exact propext u.mul_right_eq_zero
  rw [heq, finiteUniformFraction_det_reduce ht.le]

private theorem zmodColumnPrimeOrder_eq_max_iff {n p a : ℕ} [Fact p.Prime]
    (x : Fin (n + 1) → ZMod (p ^ a)) : zmodColumnPrimeOrder p a x = a ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (zmodColumnPrimeOrder_lt hx).ne h
  · rintro rfl
    simp [zmodColumnPrimeOrder, zmodPrimeOrder]

private theorem zmodColumnPrimeOrder_le_max {n p a : ℕ} [Fact p.Prime]
    (x : Fin (n + 1) → ZMod (p ^ a)) : zmodColumnPrimeOrder p a x ≤ a := by
  by_cases hx : x = 0
  · exact (zmodColumnPrimeOrder_eq_max_iff x).mpr hx |>.le
  · exact (zmodColumnPrimeOrder_lt hx).le

private theorem finiteUniformFraction_eq_zero {X : Type*} [Zero X] :
    finiteUniformFraction (fun x : X => x = 0) = 1 / (Nat.card X : ℝ) := by
  let : Nonempty {x : X // x = 0} := ⟨⟨0, rfl⟩⟩
  let : Subsingleton {x : X // x = 0} :=
    ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩
  rw [finiteUniformFraction, Nat.card_unique, Nat.cast_one]

/-- The fraction of columns whose entries are all multiples of a fixed prime power. -/
theorem finiteUniformFraction_zmodColumnPrimeOrder_ge {n p a t : ℕ} [Fact p.Prime]
    (ht : t ≤ a) :
    finiteUniformFraction (fun x : Fin (n + 1) → ZMod (p ^ a) =>
      t ≤ zmodColumnPrimeOrder p a x) = ((p : ℝ)⁻¹) ^ ((n + 1) * t) := by
  let f := ZMod.castHom (pow_dvd_pow p ht) (ZMod (p ^ t))
  let F : (Fin (n + 1) → ZMod (p ^ a)) →+ (Fin (n + 1) → ZMod (p ^ t)) :=
    { toFun := fun x i => f (x i)
      map_zero' := by
        funext i
        exact map_zero f
      map_add' := by
        intro x y
        funext i
        exact map_add f (x i) (y i) }
  have hF : Function.Surjective F := by
    intro x
    choose y hy using fun i => ZMod.castHom_surjective (pow_dvd_pow p ht) (x i)
    exact ⟨y, funext hy⟩
  have hiff (x : Fin (n + 1) → ZMod (p ^ a)) :
      t ≤ zmodColumnPrimeOrder p a x ↔ F x = 0 := by
    have hdiv (i : Fin (n + 1)) : t ≤ zmodPrimeOrder p a (x i) ↔ f (x i) = 0 := by
      rw [le_zmodPrimeOrder_iff (x i) ht]
      change p ^ t ∣ (x i).val ↔ ZMod.castHom (pow_dvd_pow p ht) (ZMod (p ^ t)) (x i) = 0
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    constructor
    · intro h
      funext i
      exact (hdiv i).mp (h.trans (zmodColumnPrimeOrder_le x i))
    · intro h
      apply Finset.le_inf' Finset.univ_nonempty
      intro i _
      exact (hdiv i).mpr (congrFun h i)
  rw [funext (fun x => propext (hiff x)), finiteUniformFraction_addHom_preimage F hF (fun x => x = 0),
    finiteUniformFraction_eq_zero, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  simp only [Nat.cast_pow, one_div, inv_pow, ← pow_mul, Nat.mul_comm t]

private theorem finiteUniformFraction_level {X : Type*} [Finite X] (f : X → ℕ) (t : ℕ) :
    finiteUniformFraction (fun x => f x = t) =
      finiteUniformFraction (fun x => t ≤ f x) -
        finiteUniformFraction (fun x => t + 1 ≤ f x) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let s := Finset.univ.filter fun x : X => f x = t
  let r := Finset.univ.filter fun x : X => t + 1 ≤ f x
  have hd : Disjoint s r := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hs := (Finset.mem_filter.mp hx).2
    have hr := (Finset.mem_filter.mp hy).2
    omega
  have h : (Finset.univ.filter fun x : X => t ≤ f x) = s ∪ r := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, s, r]
    omega
  unfold finiteUniformFraction
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, h, Finset.card_union_of_disjoint hd,
    Nat.cast_add, s, r]
  ring

/-- The exact probability that the least column valuation equals a value below the cutoff. -/
theorem finiteUniformFraction_zmodColumnPrimeOrder_eq {n p a t : ℕ} [Fact p.Prime]
    (ht : t < a) :
    finiteUniformFraction (fun x : Fin (n + 1) → ZMod (p ^ a) =>
      zmodColumnPrimeOrder p a x = t) = ((p : ℝ)⁻¹) ^ ((n + 1) * t) -
        ((p : ℝ)⁻¹) ^ ((n + 1) * (t + 1)) := by
  rw [finiteUniformFraction_level, finiteUniformFraction_zmodColumnPrimeOrder_ge ht.le,
    finiteUniformFraction_zmodColumnPrimeOrder_ge ht]

private theorem finiteUniformFraction_average {X Y Ω : Type*} [Fintype X] [Finite Y]
    (e : X × Y ≃ Ω) (event : Ω → Prop) :
    finiteUniformFraction event =
      (∑ x : X, finiteUniformFraction (fun y : Y => event (e (x, y)))) / Nat.card X := by
  have htot := Nat.card_congr e.symm
  rw [Nat.card_prod] at htot
  have hcard : Nat.card (Subtype event) =
      ∑ x : X, Nat.card {y : Y // event (e (x, y))} := by
    let ee := e.subtypeEquiv (p := fun z => event (e z)) (q := event) (fun _ => Iff.rfl)
    rw [← Nat.card_congr ee, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y => event (e (x, y)))), Nat.card_sigma]
  unfold finiteUniformFraction
  rw [hcard, htot, Nat.cast_sum, Nat.cast_mul, mul_comm (Nat.card X : ℝ), div_mul_eq_div_div]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem finiteUniformAverage_fibers {X : Type*} [Fintype X]
    (g : X → ℕ) (a : ℕ) (h : ∀ x, g x ≤ a) (f : ℕ → ℝ) :
    (∑ x : X, f (g x)) / Nat.card X =
      ∑ t ∈ Finset.range (a + 1), finiteUniformFraction (fun x => g x = t) * f t := by
  classical
  have hm : ∀ x ∈ (Finset.univ : Finset X), g x ∈ Finset.range (a + 1) :=
    fun x _ => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (h x))
  rw [← Finset.sum_fiberwise_of_maps_to' hm f]
  simp only [finiteUniformFraction, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem finiteUniformFraction_univ {X : Type*} [Finite X] [Nonempty X] (p : X → Prop)
    (hp : ∀ x, p x) : finiteUniformFraction p = 1 := by
  rw [finiteUniformFraction, Nat.card_congr (Equiv.subtypeUnivEquiv hp),
    div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/-- Probability that a uniform matrix over `ZMod (p^a)` has determinant zero. -/
noncomputable def uniformDeterminantTail (n p a : ℕ) : ℝ :=
  finiteUniformFraction (fun A : Matrix (Fin n) (Fin n) (ZMod (p ^ a)) => A.det = 0)

private theorem uniformDeterminantTail_succ_eq (n p a : ℕ) [Fact p.Prime] :
    uniformDeterminantTail (n + 1) p a =
      (∑ t ∈ Finset.range a,
        (((p : ℝ)⁻¹) ^ ((n + 1) * t) - ((p : ℝ)⁻¹) ^ ((n + 1) * (t + 1))) *
          uniformDeterminantTail n p (a - t)) + ((p : ℝ)⁻¹) ^ ((n + 1) * a) := by
  let R := ZMod (p ^ a)
  let e : ((Fin (n + 1) → R) × (Fin n → Fin (n + 1) → R)) ≃
      Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    { toFun := fun xy => matrixWithFirstColumn xy.1 xy.2
      invFun := fun A => (fun i => A i 0, fun j i => A i j.succ)
      left_inv := by intro xy; rfl
      right_inv := by
        intro A
        ext i j
        exact Fin.cases rfl (fun _ => rfl) j }
  let g := @zmodColumnPrimeOrder n p a
  let f (t : ℕ) := if t = a then (1 : ℝ) else uniformDeterminantTail n p (a - t)
  have hf (x : Fin (n + 1) → R) :
      finiteUniformFraction (fun y => (e (x, y)).det = 0) = f (g x) := by
    change finiteUniformFraction (fun y => (matrixWithFirstColumn x y).det = 0) = f (g x)
    by_cases hx : x = 0
    · have hga : g x = a := (zmodColumnPrimeOrder_eq_max_iff x).mpr hx
      rw [hga, show f a = 1 by simp [f]]
      refine finiteUniformFraction_univ _ fun y => ?_
      rw [Matrix.det_succ_column_zero]
      simp [matrixWithFirstColumn, hx]
    · have hga : g x < a := zmodColumnPrimeOrder_lt hx
      exact (finiteUniformFraction_matrixWithFirstColumn_prime_power x hx).trans
        (by simp [f, hga.ne, uniformDeterminantTail, g])
  have hmax : finiteUniformFraction (fun x => g x = a) = ((p : ℝ)⁻¹) ^ ((n + 1) * a) := by
    rw [show (fun x => g x = a) = (fun x => a ≤ g x) from
      funext fun x => propext ⟨fun h => h.ge, fun h => (zmodColumnPrimeOrder_le_max x).antisymm h⟩]
    exact finiteUniformFraction_zmodColumnPrimeOrder_ge le_rfl
  change finiteUniformFraction (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) R =>
    A.det = 0) = _
  rw [finiteUniformFraction_average e (fun A => A.det = 0)]
  simp_rw [hf]
  rw [finiteUniformAverage_fibers g a zmodColumnPrimeOrder_le_max f,
    Finset.sum_range_succ, hmax, show f a = 1 by simp [f], mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [finiteUniformFraction_zmodColumnPrimeOrder_eq ht']
  simp [f, ht'.ne]

private noncomputable def determinantTailConstant (q : ℝ) (n : ℕ) : ℝ :=
  (1 - q ^ n) / (1 - q)

private theorem determinantTailConstant_one_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    {n : ℕ} (hn : 1 ≤ n) : 1 ≤ determinantTailConstant q n := by
  unfold determinantTailConstant
  rw [le_div_iff₀ (sub_pos.mpr hq₁), one_mul]
  have h := pow_le_pow_of_le_one hq₀ hq₁.le hn
  rw [pow_one] at h
  linarith

private theorem det_tail_recurrence_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (n a : ℕ) :
    (∑ t ∈ Finset.range a,
      (q ^ ((n + 1) * t) - q ^ ((n + 1) * (t + 1))) *
        (determinantTailConstant q n * q ^ (a - t))) + q ^ ((n + 1) * a) ≤
      determinantTailConstant q (n + 1) * q ^ a := by
  have hco : (1 - q ^ (n + 1)) * determinantTailConstant q n =
      determinantTailConstant q (n + 1) * (1 - q ^ n) := by
    unfold determinantTailConstant
    ring
  have hterm (t : ℕ) (ht : t ≤ a) :
      (q ^ ((n + 1) * t) - q ^ ((n + 1) * (t + 1))) *
        (determinantTailConstant q n * q ^ (a - t)) =
        (determinantTailConstant q (n + 1) * q ^ a) *
          (q ^ (n * t) - q ^ (n * (t + 1))) := by
    have hsplit : q ^ ((n + 1) * t) = q ^ (n * t) * q ^ t := by
      rw [Nat.add_mul, one_mul, pow_add]
    rw [Nat.mul_add (n + 1), Nat.mul_one, pow_add,
      Nat.mul_add n, Nat.mul_one, pow_add, hsplit,
      show q ^ a = q ^ t * q ^ (a - t) by rw [← pow_add, Nat.add_sub_of_le ht]]
    calc
      _ = (1 - q ^ (n + 1)) * determinantTailConstant q n *
          (q ^ (n * t) * q ^ t * q ^ (a - t)) := by ring
      _ = _ := by rw [hco]; ring
  have hsum : (∑ t ∈ Finset.range a,
      (q ^ ((n + 1) * t) - q ^ ((n + 1) * (t + 1))) *
        (determinantTailConstant q n * q ^ (a - t))) =
      (determinantTailConstant q (n + 1) * q ^ a) * (1 - q ^ (n * a)) := by
    calc
      _ = ∑ t ∈ Finset.range a,
          (determinantTailConstant q (n + 1) * q ^ a) *
            (q ^ (n * t) - q ^ (n * (t + 1))) :=
        Finset.sum_congr rfl fun t ht => hterm t (Finset.mem_range.mp ht).le
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' (fun t => q ^ (n * t))]
        simp
  rw [hsum, Nat.add_mul, one_mul, pow_add]
  have hC := determinantTailConstant_one_le hq₀ hq₁ (Nat.succ_pos n)
  have h := mul_le_mul_of_nonneg_right hC
    (mul_nonneg (pow_nonneg hq₀ (n * a)) (pow_nonneg hq₀ a))
  simp only [one_mul] at h
  calc
    _ ≤ (determinantTailConstant q (n + 1) * q ^ a) * (1 - q ^ (n * a)) +
        determinantTailConstant q (n + 1) * (q ^ (n * a) * q ^ a) := by
      gcongr
    _ = _ := by ring

private theorem uniformDeterminantTail_one (p a : ℕ) [Fact p.Prime] :
    uniformDeterminantTail 1 p a = ((p : ℝ)⁻¹) ^ a := by
  let R := ZMod (p ^ a)
  have heq : (fun A : Matrix (Fin 1) (Fin 1) R => A.det = 0) = fun A => A = 0 := by
    funext A
    apply propext
    constructor
    · intro h
      rw [Matrix.det_unique, Fin.default_eq_zero] at h
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      simpa [hi, hj] using h
    · rintro rfl
      simp
  change finiteUniformFraction (fun A : Matrix (Fin 1) (Fin 1) R => A.det = 0) = _
  rw [heq, finiteUniformFraction_eq_zero]
  change 1 / (Nat.card (Fin 1 → Fin 1 → ZMod (p ^ a)) : ℝ) = _
  simp only [Nat.card_fun, Nat.card_fin, pow_one, Nat.card_zmod, Nat.cast_pow, one_div, inv_pow]

private theorem uniformDeterminantTail_le_constant (n p : ℕ) [Fact p.Prime] (hn : 0 < n)
    (a : ℕ) : uniformDeterminantTail n p a ≤
      determinantTailConstant ((p : ℝ)⁻¹) n * ((p : ℝ)⁻¹) ^ a := by
  let q := ((p : ℝ)⁻¹)
  have hp : p.Prime := Fact.out
  have hp₁ : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq₀ : 0 ≤ q := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hq₁ : q < 1 := inv_lt_one_of_one_lt₀ hp₁
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · subst n
      rw [uniformDeterminantTail_one]
      change q ^ a ≤ determinantTailConstant q 1 * q ^ a
      rw [determinantTailConstant, pow_one, div_self (sub_ne_zero.mpr hq₁.ne'), one_mul]
    · have hn' : 0 < n := Nat.pos_of_ne_zero h
      rw [uniformDeterminantTail_succ_eq]
      change (∑ t ∈ Finset.range a,
        (q ^ ((n + 1) * t) - q ^ ((n + 1) * (t + 1))) *
          uniformDeterminantTail n p (a - t)) + q ^ ((n + 1) * a) ≤ _
      refine le_trans (add_le_add (Finset.sum_le_sum ?_) le_rfl)
        (det_tail_recurrence_le hq₀ hq₁ n a)
      intro t _
      exact mul_le_mul_of_nonneg_left (ih hn' (a - t))
        (sub_nonneg.mpr (pow_le_pow_of_le_one hq₀ hq₁.le
          (Nat.mul_le_mul_left (n + 1) t.le_succ)))

/-- The uniform reference bound for divisibility of the determinant by a
prime power, on matrices with independently uniform residue entries. -/
theorem uniformDeterminantTail_le (n p a : ℕ) [Fact p.Prime] (hn : 0 < n) :
    uniformDeterminantTail n p a ≤ 2 / (p : ℝ) ^ a := by
  have hp : p.Prime := Fact.out
  have hp₂ : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hq : ((p : ℝ)⁻¹) ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp₂
  have hq₀ : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hconst : determinantTailConstant ((p : ℝ)⁻¹) n ≤ 2 := by
    unfold determinantTailConstant
    apply (div_le_iff₀ (by linarith)).mpr
    have hpow := pow_nonneg hq₀ n
    linarith
  calc
    _ ≤ determinantTailConstant ((p : ℝ)⁻¹) n * ((p : ℝ)⁻¹) ^ a :=
      uniformDeterminantTail_le_constant n p hn a
    _ ≤ 2 * ((p : ℝ)⁻¹) ^ a := mul_le_mul_of_nonneg_right hconst (pow_nonneg hq₀ a)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

end BooleanThreshold
