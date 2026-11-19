module

public import BooleanThreshold.CokernelMomentWeights
public import BooleanThreshold.SignMeasure
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public noncomputable section

open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace BooleanThreshold

/-- The expectation of a real-valued function on a finite uniform sample space. -/
def finiteAverage {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card Ω

theorem finiteAverage_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    finiteAverage f ≤ finiteAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

theorem finiteAverage_sum {Ω I : Type*} [Fintype Ω] (s : Finset I) (f : I → Ω → ℝ) :
    finiteAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem finiteAverage_const_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    finiteAverage (fun x => c * f x) = c * finiteAverage f := by
  unfold finiteAverage
  rw [← Finset.mul_sum, mul_div_assoc]

theorem finiteAverage_indicator {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (s : Set Ω) :
    finiteAverage (fun x => if x ∈ s then 1 else 0) = (uniformOn Set.univ).real s := by
  rw [finiteAverage, uniformOn_univ_real_eq_card, Finset.sum_boole]
  congr 1
  have hset : (↑(Finset.univ.filter (fun x => x ∈ s)) : Set Ω) = s := by ext x; simp
  have hc := Set.ncard_coe_finset (Finset.univ.filter (fun x => x ∈ s))
  rw [hset] at hc
  exact_mod_cast hc.symm

theorem finiteAverage_event {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : Ω → Prop) [DecidablePred p] :
    finiteAverage (fun x => if p x then 1 else 0) = (uniformOn Set.univ).real {x | p x} := by
  have heq : (fun x => if p x then (1 : ℝ) else 0) =
      (fun x => @ite ℝ (x ∈ {y | p y}) (Classical.propDecidable (x ∈ {y | p y})) 1 0) := by
    funext x
    by_cases hx : p x
    · rw [ite_eq_left hx, ite_eq_left (show x ∈ {y | p y} from hx)]
    · rw [ite_eq_right hx, ite_eq_right (show x ∉ {y | p y} from hx)]
  exact (congrArg finiteAverage heq).trans (finiteAverage_indicator _)

/-- The successive increments in the nonnegative integer power function. -/
def powerIncrement (m j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) ^ m - (j : ℝ) ^ m

theorem powerIncrement_nonneg (m j : ℕ) : 0 ≤ powerIncrement m j := by
  unfold powerIncrement
  exact sub_nonneg.mpr (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast j.le_succ) _)

private theorem sum_powerIncrement_range (m D : ℕ) (hm : 0 < m) :
    ∑ j ∈ Finset.range D, powerIncrement m j = (D : ℝ) ^ m := by
  simpa only [powerIncrement, Nat.cast_zero, zero_pow hm.ne', sub_zero] using
    (Finset.sum_range_sub (fun j : ℕ => (j : ℝ) ^ m) D)

theorem sum_powerIncrement (m D : ℕ) (hm : 0 < m) :
    ∑ j : Fin D, powerIncrement m j = (D : ℝ) ^ m := by
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_powerIncrement_range m D hm

private theorem pow_eq_sum_powerIncrement {u D m : ℕ} (hu : u ≤ D) (hm : 0 < m) :
    (u : ℝ) ^ m = ∑ j : Fin D, powerIncrement m j * (if (j : ℕ) < u then 1 else 0) := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    powerIncrement m j * (if j < u then (1 : ℝ) else 0))]
  have hfilter : (Finset.range D).filter (fun j => j < u) = Finset.range u := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter, sum_powerIncrement_range m u hm]

private theorem prod_if_forall {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] [Decidable (∀ i, p i)] :
    (∏ i, if p i then (1 : ℝ) else 0) = if ∀ i, p i then 1 else 0 := by
  by_cases h : ∀ i, p i
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hn : ¬ ∀ j, p j := fun hall => hi (hall i)
    rw [ite_eq_right hn]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Joint upper-tail bounds give bounds on mixed positive moments by a finite
expansion of each power into successive increments. -/
theorem joint_power_moment_le {Ω I : Type*} [Fintype Ω] [Fintype I] (D : ℕ)
    (ν : Ω → I → ℕ) (hν : ∀ x i, ν x i ≤ D) (m : I → ℕ) (hm : ∀ i, 0 < m i)
    (u : I → Fin D → ℝ) (A E : ℝ)
    (hTail : ∀ j : I → Fin D,
      finiteAverage (fun x => if ∀ i, (j i : ℕ) < ν x i then 1 else 0) ≤
        A * (∏ i, u i (j i)) + E) :
    finiteAverage (fun x => ∏ i, (ν x i : ℝ) ^ m i) ≤
      A * (∏ i, ∑ j : Fin D, powerIncrement (m i) j * u i j) +
        E * (∏ i, (D : ℝ) ^ m i) := by
  let w (j : I → Fin D) := ∏ i, powerIncrement (m i) (j i)
  let p (j : I → Fin D) (x : Ω) : ℝ := if ∀ i, (j i : ℕ) < ν x i then 1 else 0
  have hprod (x : Ω) :
      (∏ i, (ν x i : ℝ) ^ m i) = ∑ j : I → Fin D, w j * p j x := by
    simp_rw [pow_eq_sum_powerIncrement (hν x _) (hm _)]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, w, p]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact prod_if_forall (fun i => (j i : ℕ) < ν x i)
  simp_rw [hprod]
  rw [finiteAverage_sum]
  simp only [finiteAverage_const_mul]
  calc
    _ ≤ ∑ j : I → Fin D, w j * (A * (∏ i, u i (j i)) + E) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hTail j)
        (Finset.prod_nonneg fun i _ => powerIncrement_nonneg (m i) (j i))
    _ = A * (∑ j : I → Fin D, ∏ i, powerIncrement (m i) (j i) * u i (j i)) +
        E * (∑ j : I → Fin D, w j) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.prod_mul_distrib, w]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by
      simp_rw [show ∀ i, (D : ℝ) ^ m i = ∑ j : Fin D, powerIncrement (m i) j from
        fun i => (sum_powerIncrement (m i) D (hm i)).symm]
      rw [Finset.prod_univ_sum, Finset.prod_univ_sum]
      simp only [Fintype.piFinset_univ, w]

/-- For primes at least two, the geometric tail weighted by the increments
of a bounded-degree power is at most a degree-dependent constant divided by the prime. -/
theorem powerIncrement_geometric_bound (k : ℕ) :
    ∃ M > (0 : ℝ), ∀ (m D p : ℕ), m ≤ k → 2 ≤ p →
      ∑ j : Fin D, powerIncrement m j * (1 / (p : ℝ) ^ ((j : ℕ) + 1)) ≤ M / (p : ℝ) := by
  obtain ⟨A, hA, hpoly⟩ := polynomial_div_pow_bounded k (show (1 : ℝ) < 3 / 2 by norm_num)
  refine ⟨6 * A, by positivity, fun m D p hm hp => ?_⟩
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : 0 < (p : ℝ) := by positivity
  have hterm (j : ℕ) :
      powerIncrement m j * (1 / (p : ℝ) ^ (j + 1)) ≤
        ((3 / 2) * A / (p : ℝ)) * (3 / 4 : ℝ) ^ j := by
    have hinc : powerIncrement m j ≤ A * (3 / 2 : ℝ) ^ (j + 1) := by
      have hmono : ((j + 1 : ℕ) : ℝ) ^ m ≤ ((j + 1 : ℕ) : ℝ) ^ k :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ j + 1 by omega)) hm
      have hle := (div_le_iff₀ (show 0 < (3 / 2 : ℝ) ^ (j + 1) by positivity)).mp (hpoly (j + 1))
      exact (sub_le_self _ (by positivity)).trans (hmono.trans hle)
    have hden : (2 : ℝ) ^ j * (p : ℝ) ≤ (p : ℝ) ^ (j + 1) := by
      rw [pow_succ]
      gcongr
    calc
      _ = powerIncrement m j / (p : ℝ) ^ (j + 1) := by ring
      _ ≤ (A * (3 / 2 : ℝ) ^ (j + 1)) / ((2 : ℝ) ^ j * (p : ℝ)) :=
        div_le_div₀ (by positivity) hinc (by positivity) hden
      _ = (A * (3 / 2) * ((3 / 2 : ℝ) ^ j / 2 ^ j)) / (p : ℝ) := by
        rw [pow_succ', div_mul_eq_div_div]
        ring
      _ = _ := by rw [← div_pow, show (3 / 2 : ℝ) / 2 = 3 / 4 by norm_num]; ring
  have hgeom : ∑ j : Fin D, (3 / 4 : ℝ) ^ (j : ℕ) ≤ 4 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (3 / 4 : ℝ) ^ j),
      geom_sum_eq (by norm_num : (3 / 4 : ℝ) ≠ 1)]
    have hh : 0 ≤ (3 / 4 : ℝ) ^ D := by positivity
    norm_num
    linarith
  calc
    _ ≤ ∑ j : Fin D, ((3 / 2) * A / (p : ℝ)) * (3 / 4 : ℝ) ^ (j : ℕ) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = ((3 / 2) * A / (p : ℝ)) * ∑ j : Fin D, (3 / 4 : ℝ) ^ (j : ℕ) := by rw [Finset.mul_sum]
    _ ≤ ((3 / 2) * A / (p : ℝ)) * 4 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

end BooleanThreshold
