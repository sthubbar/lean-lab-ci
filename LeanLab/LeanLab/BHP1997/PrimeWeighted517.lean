/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17.
A reusable weighted form of the prime number theorem on integer intervals, by partial summation
against the unweighted interval estimate, together with the bookkeeping for weights that are a
function of bounded variation times the indicator of a set with finitely many jumps.
No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prime514
import LeanLab.BHP1997.Abel514

namespace LeanLab.BHP1997.LowerShortC165
open Decomp132
open scoped BigOperators

/-- P0069 page 51, display 5.17, the partial summation step. If every initial segment of the
interval from L to U carries an unweighted sum of size at most R, then a weight bounded by M with
total variation at most V along the interval changes the sum by at most M plus V times R. -/
theorem weighted_interval_abs_le (a F : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) {M V R : ℝ}
    (hM0 : 0 ≤ M) (hF : ∀ n ∈ Finset.Ioc L U, |F n| ≤ M)
    (hV : ∑ i ∈ Finset.Ico (L + 1) U, |F (i + 1) - F i| ≤ V)
    (hR : ∀ i : ℕ, L ≤ i → i ≤ U → |∑ m ∈ Finset.Ioc L i, a m| ≤ R) :
    |∑ n ∈ Finset.Ioc L U, a n * F n| ≤ (M + V) * R := by
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hV
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR L le_rfl hLU)
  rcases hLU.eq_or_lt with rfl | hlt
  · rw [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    positivity
  have hs : ∀ m ∈ Finset.Ioc L U, L + 1 ≤ m ∧ m ≤ U := fun m hm => by
    have := Finset.mem_Ioc.mp hm
    omega
  have h1 : ‖∑ m ∈ Finset.Ioc L U, ((a m : ℝ) : ℂ)‖ ≤ R := by
    have h := hR U hlt.le le_rfl
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sum] at h
    exact h
  have h2 : ∀ i ∈ Finset.Ico (L + 1) U,
      ‖∑ m ∈ (Finset.Ioc L U).filter (fun m => m ≤ i), ((a m : ℝ) : ℂ)‖ ≤ R := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hf : (Finset.Ioc L U).filter (fun m => m ≤ i) = Finset.Ioc L i := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    have h := hR i (by omega) (by omega)
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sum] at h
    rw [hf]
    exact h
  have key := Decomp514Abel.weighted_sum_norm_le (Finset.Ioc L U) hs
    (fun m => ((F m : ℝ) : ℂ)) (fun m => ((a m : ℝ) : ℂ)) h1 h2
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_eq_abs] at key
  have he : ∑ n ∈ Finset.Ioc L U, a n * F n = ∑ n ∈ Finset.Ioc L U, F n * a n :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [he]
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hR0)
  exact add_le_add (hF U (Finset.mem_Ioc.mpr ⟨hlt, le_rfl⟩)) hV

/-- P0069 page 51, display 5.17, the prime number theorem input on integer intervals, with a
threshold constant that is at least one. -/
theorem pnt_interval_nat (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, C ≤ X → ∀ L i : ℕ, L ≤ i → (i : ℝ) ≤ X →
      |∑ m ∈ Finset.Ioc L i, (primeWeight m - 1 / Real.log (m : ℝ))| ≤
        C * X * Real.log X ^ (-A) := by
  obtain ⟨C1, h1⟩ := Prime514.pnt_short_interval A hA
  refine ⟨max C1 1, le_max_right _ _, fun X hX L i hLi hiX => ?_⟩
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have h := h1 X ((le_max_left _ _).trans hX) (L : ℝ) (i : ℝ) (Nat.cast_nonneg L)
    (Nat.cast_le.mpr hLi) hiX
  simp only [Nat.floor_natCast] at h
  have hlog : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hX1) _
  calc _ ≤ C1 * X * Real.log X ^ (-A) := h
    _ ≤ max C1 1 * X * Real.log X ^ (-A) := by
      gcongr
      exact le_max_left _ _

/-- P0069 page 51, display 5.17, the weighted prime number theorem. For every positive A there
is C such that for X at least C and every integer interval from L to U below X, a weight F
bounded by M on the interval with total variation at most V satisfies: the sum of F over the
primes of the interval differs from the sum of F over all integers with density one over log by
at most C times M plus V times X over the power A of log X. -/
theorem pnt_weighted (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ X : ℝ, C ≤ X → ∀ L U : ℕ, L ≤ U → (U : ℝ) ≤ X →
      ∀ (F : ℕ → ℝ) (M V : ℝ), 0 ≤ M → (∀ n ∈ Finset.Ioc L U, |F n| ≤ M) →
        ∑ i ∈ Finset.Ico (L + 1) U, |F (i + 1) - F i| ≤ V →
        |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ)) * F n| ≤
          C * (M + V) * X * Real.log X ^ (-A) := by
  obtain ⟨C, -, hC⟩ := pnt_interval_nat A hA
  refine ⟨C, fun X hX L U hLU hUX F M V hM0 hF hV => ?_⟩
  have h := weighted_interval_abs_le (fun m => primeWeight m - 1 / Real.log (m : ℝ)) F hLU hM0
    hF hV (R := C * X * Real.log X ^ (-A))
    (fun i hLi hiU => hC X hX L i hLi ((Nat.cast_le.mpr hiU).trans hUX))
  calc _ ≤ (M + V) * (C * X * Real.log X ^ (-A)) := h
    _ = _ := by ring

/-- P0069 page 51, display 5.17, the weighted prime number theorem with the error measured by
the upper endpoint. When the upper endpoint U is at least the power c of X, the error is at most
C times M plus V times U over the power A of log X. -/
theorem pnt_weighted_power (A : ℝ) (hA : 0 < A) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ X : ℝ, C ≤ X → ∀ L U : ℕ, L ≤ U → X ^ c ≤ (U : ℝ) →
      ∀ (F : ℕ → ℝ) (M V : ℝ), 0 ≤ M → (∀ n ∈ Finset.Ioc L U, |F n| ≤ M) →
        ∑ i ∈ Finset.Ico (L + 1) U, |F (i + 1) - F i| ≤ V →
        |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ)) * F n| ≤
          C * (M + V) * (U : ℝ) * Real.log X ^ (-A) := by
  obtain ⟨C1, hC1⟩ := pnt_weighted A hA
  let K : ℝ := max C1 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 ≤ K := by linarith
  let C : ℝ := max (max (K ^ (1 / c)) (K * c ^ (-A))) 2
  have hCa : K ^ (1 / c) ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCb : K * c ^ (-A) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC2 : 2 ≤ C := le_max_right _ _
  refine ⟨C, fun X hX L U hLU hXU F M V hM0 hF hV => ?_⟩
  have hX2 : 2 ≤ X := hC2.trans hX
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hV
  have hKU : K ≤ (U : ℝ) := by
    have h1 : (K ^ (1 / c)) ^ c ≤ X ^ c :=
      Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) (hCa.trans hX) hc.le
    rw [← Real.rpow_mul hK0, one_div_mul_cancel hc.ne', Real.rpow_one] at h1
    exact h1.trans hXU
  have hU0 : 0 < (U : ℝ) := by linarith
  have hlogU : c * Real.log X ≤ Real.log (U : ℝ) := by
    rw [← Real.log_rpow hX0]
    exact Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hXU
  have hcl : 0 < c * Real.log X := mul_pos hc hlogX
  have hpow : Real.log (U : ℝ) ^ (-A) ≤ c ^ (-A) * Real.log X ^ (-A) := by
    rw [← Real.mul_rpow hc.le hlogX.le, Real.rpow_neg (hcl.le.trans hlogU),
      Real.rpow_neg hcl.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hcl _) (Real.rpow_le_rpow hcl.le hlogU hA.le)
  have hlogUn : 0 ≤ Real.log (U : ℝ) ^ (-A) := Real.rpow_nonneg (hcl.le.trans hlogU) _
  have hlogXn : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlogX.le _
  have h := hC1 (U : ℝ) ((le_max_left _ _).trans hKU) L U hLU le_rfl F M V hM0 hF hV
  calc _ ≤ C1 * (M + V) * (U : ℝ) * Real.log (U : ℝ) ^ (-A) := h
    _ ≤ K * (M + V) * (U : ℝ) * Real.log (U : ℝ) ^ (-A) := by
      gcongr
      exact le_max_left _ _
    _ ≤ K * (M + V) * (U : ℝ) * (c ^ (-A) * Real.log X ^ (-A)) := by
      gcongr
    _ = K * c ^ (-A) * ((M + V) * (U : ℝ) * Real.log X ^ (-A)) := by ring
    _ ≤ C * ((M + V) * (U : ℝ) * Real.log X ^ (-A)) := by
      gcongr
    _ = _ := by ring

/-- P0069 page 51, display 5.17, weight bookkeeping. The total variation of a product G times S,
with G bounded by M of variation at most V and S bounded by one of variation at most J, is at
most V plus M times J. -/
theorem variation_mul_le (G S : ℕ → ℝ) {a b : ℕ} {M V J : ℝ} (hM0 : 0 ≤ M)
    (hG : ∀ n ∈ Finset.Icc a b, |G n| ≤ M) (hS : ∀ n ∈ Finset.Icc a b, |S n| ≤ 1)
    (hV : ∑ i ∈ Finset.Ico a b, |G (i + 1) - G i| ≤ V)
    (hJ : ∑ i ∈ Finset.Ico a b, |S (i + 1) - S i| ≤ J) :
    ∑ i ∈ Finset.Ico a b, |G (i + 1) * S (i + 1) - G i * S i| ≤ V + M * J := by
  have hpt : ∀ i ∈ Finset.Ico a b, |G (i + 1) * S (i + 1) - G i * S i| ≤
      |G (i + 1) - G i| + M * |S (i + 1) - S i| := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hS1 := hS (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hGi := hG i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have he : G (i + 1) * S (i + 1) - G i * S i =
        (G (i + 1) - G i) * S (i + 1) + G i * (S (i + 1) - S i) := by ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hS1)
      (mul_le_mul_of_nonneg_right hGi (abs_nonneg _))
  calc _ ≤ ∑ i ∈ Finset.Ico a b, (|G (i + 1) - G i| + M * |S (i + 1) - S i|) :=
        Finset.sum_le_sum hpt
    _ = ∑ i ∈ Finset.Ico a b, |G (i + 1) - G i| +
        M * ∑ i ∈ Finset.Ico a b, |S (i + 1) - S i| := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ V + M * J := add_le_add hV (mul_le_mul_of_nonneg_left hJ hM0)

/-- P0069 page 51, display 5.17, weight bookkeeping. The jump of an indicator between two
truth values is zero when they agree and one when they differ. -/
theorem indicator_delta_abs (p q : Prop) [Decidable p] [Decidable q] :
    |(if p then (1 : ℝ) else 0) - (if q then (1 : ℝ) else 0)| = if (p ↔ q) then 0 else 1 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- P0069 page 51, display 5.17, weight bookkeeping. The total variation of the indicator of a
set along a finite set of steps is the number of steps at which the indicator changes value. -/
theorem indicator_variation_eq_card (P : ℕ → Prop) [DecidablePred P] (T : Finset ℕ) :
    ∑ i ∈ T, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| =
      ((T.filter (fun i => ¬ (P (i + 1) ↔ P i))).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [indicator_delta_abs]
  by_cases h : (P (i + 1) ↔ P i) <;> simp [h]

/-- P0069 page 51, display 5.17, weight bookkeeping for a weight with finitely many jumps.
If G is bounded by M with variation at most V and the indicator of the set P changes value at
most J times along the interval, then G times the indicator has variation at most V plus M J. -/
theorem variation_mul_indicator_le (G : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] {a b : ℕ}
    {M V : ℝ} {J : ℕ} (hM0 : 0 ≤ M) (hG : ∀ n ∈ Finset.Icc a b, |G n| ≤ M)
    (hV : ∑ i ∈ Finset.Ico a b, |G (i + 1) - G i| ≤ V)
    (hJ : ((Finset.Ico a b).filter (fun i => ¬ (P (i + 1) ↔ P i))).card ≤ J) :
    ∑ i ∈ Finset.Ico a b, |G (i + 1) * (if P (i + 1) then (1 : ℝ) else 0) -
      G i * (if P i then (1 : ℝ) else 0)| ≤ V + M * J := by
  refine variation_mul_le G (fun n => if P n then (1 : ℝ) else 0) hM0 hG ?_ hV ?_
  · intro n _
    by_cases h : P n <;> simp [h]
  · rw [indicator_variation_eq_card]
    exact_mod_cast hJ

/-- P0069 page 51, display 5.17, weight bookkeeping. The indicator of a boolean combination R
of finitely many sets changes value only at a step where one of the atoms changes value, so its
total variation is at most the sum of the total variations of the atoms. -/
theorem indicator_variation_le_atoms {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (R : ℕ → Prop) [∀ k, DecidablePred (P k)] [DecidablePred R] (T : Finset ℕ)
    (h : ∀ i ∈ T, (∀ k ∈ s, (P k (i + 1) ↔ P k i)) → (R (i + 1) ↔ R i)) :
    ∑ i ∈ T, |(if R (i + 1) then (1 : ℝ) else 0) - (if R i then (1 : ℝ) else 0)| ≤
      ∑ k ∈ s, ∑ i ∈ T,
        |(if P k (i + 1) then (1 : ℝ) else 0) - (if P k i then (1 : ℝ) else 0)| := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i hi => ?_
  have hnn : ∀ k ∈ s, (0 : ℝ) ≤
      |(if P k (i + 1) then (1 : ℝ) else 0) - (if P k i then (1 : ℝ) else 0)| :=
    fun k _ => abs_nonneg _
  by_cases hR : (R (i + 1) ↔ R i)
  · rw [indicator_delta_abs]
    simp only [hR, ite_true]
    exact Finset.sum_nonneg hnn
  · have hex : ∃ k ∈ s, ¬ (P k (i + 1) ↔ P k i) := by
      by_contra hno
      exact hR (h i hi fun k hk => by_contra fun hk' => hno ⟨k, hk, hk'⟩)
    obtain ⟨k, hk, hPk⟩ := hex
    rw [indicator_delta_abs]
    simp only [hR, ite_false]
    have hone : (1 : ℝ) =
        |(if P k (i + 1) then (1 : ℝ) else 0) - (if P k i then (1 : ℝ) else 0)| := by
      rw [indicator_delta_abs]
      simp only [hPk, ite_false]
    exact hone.le.trans (Finset.single_le_sum hnn hk)

/-- P0069 page 51, display 5.17, weight bookkeeping, counting form. The number of steps at which
a boolean combination R of finitely many sets changes value is at most the total number of
steps at which the atoms change value. -/
theorem indicator_changes_le_atoms {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (R : ℕ → Prop) [∀ k, DecidablePred (P k)] [DecidablePred R] (T : Finset ℕ)
    (h : ∀ i ∈ T, (∀ k ∈ s, (P k (i + 1) ↔ P k i)) → (R (i + 1) ↔ R i)) :
    (T.filter (fun i => ¬ (R (i + 1) ↔ R i))).card ≤
      ∑ k ∈ s, (T.filter (fun i => ¬ (P k (i + 1) ↔ P k i))).card := by
  have hv := indicator_variation_le_atoms s P R T h
  simp only [indicator_variation_eq_card] at hv
  exact_mod_cast hv

/-- P0069 page 51, display 5.17, weight bookkeeping. The indicator of an intersection changes
value only where one of the two sets changes value. -/
theorem indicator_variation_and_le (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (T : Finset ℕ) :
    ∑ i ∈ T, |(if P (i + 1) ∧ Q (i + 1) then (1 : ℝ) else 0) -
        (if P i ∧ Q i then (1 : ℝ) else 0)| ≤
      ∑ i ∈ T, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| +
      ∑ i ∈ T, |(if Q (i + 1) then (1 : ℝ) else 0) - (if Q i then (1 : ℝ) else 0)| := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h1 : P (i + 1) <;> by_cases h2 : P i <;> by_cases h3 : Q (i + 1) <;>
    by_cases h4 : Q i <;> simp [h1, h2, h3, h4]

/-- P0069 page 51, display 5.17, weight bookkeeping. The indicator of a union changes value
only where one of the two sets changes value. -/
theorem indicator_variation_or_le (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (T : Finset ℕ) :
    ∑ i ∈ T, |(if P (i + 1) ∨ Q (i + 1) then (1 : ℝ) else 0) -
        (if P i ∨ Q i then (1 : ℝ) else 0)| ≤
      ∑ i ∈ T, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| +
      ∑ i ∈ T, |(if Q (i + 1) then (1 : ℝ) else 0) - (if Q i then (1 : ℝ) else 0)| := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h1 : P (i + 1) <;> by_cases h2 : P i <;> by_cases h3 : Q (i + 1) <;>
    by_cases h4 : Q i <;> simp [h1, h2, h3, h4]

/-- P0069 page 51, display 5.17, weight bookkeeping. The indicator of a complement changes
value exactly where the set changes value. -/
theorem indicator_variation_not_eq (P : ℕ → Prop) [DecidablePred P] (T : Finset ℕ) :
    ∑ i ∈ T, |(if ¬ P (i + 1) then (1 : ℝ) else 0) - (if ¬ P i then (1 : ℝ) else 0)| =
      ∑ i ∈ T, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : P (i + 1) <;> by_cases h2 : P i <;> simp [h1, h2]

/-- P0069 page 51, display 5.17, weight bookkeeping. A lower cutoff, a condition that once true
stays true, is an indicator with at most one jump along any interval. -/
theorem indicator_variation_mono_le_one (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i, P i → P (i + 1)) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)|
      ≤ 1 := by
  have hpt : ∀ i ∈ Finset.Ico a b,
      |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| =
        (fun n => if P n then (1 : ℝ) else 0) (i + 1) -
          (fun n => if P n then (1 : ℝ) else 0) i := by
    intro i _
    by_cases h2 : P i
    · simp [h2, hP i h2]
    · by_cases h1 : P (i + 1) <;> simp [h1, h2]
  rw [Finset.sum_congr rfl hpt]
  rcases le_or_gt a b with hab | hab
  · rw [Finset.sum_Ico_sub (f := fun n => if P n then (1 : ℝ) else 0) hab]
    by_cases h1 : P b <;> by_cases h2 : P a <;> simp [h1, h2]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact zero_le_one

/-- P0069 page 51, display 5.17, weight bookkeeping. An upper cutoff, a condition that once
false stays false, is an indicator with at most one jump along any interval. -/
theorem indicator_variation_anti_le_one (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i, P (i + 1) → P i) (a b : ℕ) :
    ∑ i ∈ Finset.Ico a b, |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)|
      ≤ 1 := by
  have h := indicator_variation_mono_le_one (fun n => ¬ P n)
    (fun i hi h1 => hi (hP i h1)) a b
  rwa [indicator_variation_not_eq] at h

end LeanLab.BHP1997.LowerShortC165

