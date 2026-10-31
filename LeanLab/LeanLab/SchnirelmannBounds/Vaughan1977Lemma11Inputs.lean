/-
P0066, pages 96 and 103, Lemma 2 and the two error budgets in the proof of Lemma 11.
Source: https://doi.org/10.1515/crll.1977.290.93
The analytic estimates are explicit unproved Props. No target statement is weakened.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Euler

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs

open Vaughan1977Eq55 Vaughan1977Lemma12 Vaughan1977Moments Vaughan1977Euler

def piR (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

/-- The logarithmic integral normalized as in 2.16. -/
def li2 (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The full cited theta bound 2.15, not the one sided shared input. -/
def Eq215 : Prop := ∀ x : ℝ, 678407 ≤ x →
  |Chebyshev.theta x - x| < x / (40 * Real.log x)

/-- Equation 2.16 on page 96, with the exact threshold and constant. -/
def Eq216 : Prop := ∀ x : ℝ, 10 ^ 35 ≤ x →
  |piR x - li2 x| < x / (38 * Real.log x ^ 2)

/-- The pair of ordinary integrals on page 103. -/
def mainIntegral (x : ℝ) : ℝ :=
  (∫ u in (3 : ℝ)..x, u / Real.log u) + ∫ u in x..(2 * x), (2 * x - u) / Real.log u

def asymptotic (x : ℝ) : ℝ :=
  x ^ 2 / Real.log x * (1 + (3 - 4 * Real.log 2) / (2 * Real.log x))

/-- The second error estimate in the proof on page 103. Still unproved. -/
def DistributionError : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x →
  |Psi x - mainIntegral x| < x ^ 2 / (5 * Real.log x ^ 2)

/-- The final quadrature estimate on page 103. Still unproved. -/
def QuadratureError : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x →
  |mainIntegral x - asymptotic x| < x ^ 2 / (10 * Real.log x ^ 2)

theorem thetaUpper_of_eq215 (h : Eq215) : ThetaUpper := by
  intro x hx
  have he := (abs_lt.mp (h x hx)).2
  linarith

/-- Prime counts on a real interval, with the natural floors made explicit. -/
theorem interval_card {a b : ℝ} (hab : a ≤ b) :
    (((Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime).card : ℝ) = piR b - piR a := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsub : (⌊a⌋₊).primesLE ⊆ (⌊b⌋₊).primesLE := by
    intro p hp
    obtain ⟨hpa, hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpa.trans hfl, hpr⟩
  have hset : (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpb, hpr⟩, hnot⟩
      have hpa : ⌊a⌋₊ < p := by
        by_contra h
        exact hnot ⟨le_of_not_gt h, hpr⟩
      exact ⟨⟨hpa, hpb⟩, hpr⟩
    · rintro ⟨⟨hpa, hpb⟩, hpr⟩
      refine ⟨⟨hpb, hpr⟩, ?_⟩
      rintro ⟨hpa', _⟩
      omega
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [hset] at hc
  simp only [Nat.primesLE_card_eq_primeCounting] at hc
  have hr : (((Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime).card : ℝ) + piR a = piR b := by
    unfold piR
    exact_mod_cast hc
  linarith

/-- Regroup 5.1 as the weighted difference of two prime counts. -/
theorem psi_eq_pi (x : ℝ) (hx : 6 ≤ x) :
    Psi x = ∑ p ∈ P1 x, Real.log p * (piR (2 * x - p) - piR (x - p)) := by
  unfold Psi
  change (∑ p ∈ P1 x,
    ∑ q ∈ (Icc 1 ⌊2 * x - p⌋₊).filter (fun q : ℕ => q.Prime ∧ x - p < (q : ℝ)), Real.log p) = _
  apply Finset.sum_congr rfl
  intro p hp
  have hpI := (Finset.mem_filter.mp hp).1
  have hpx : (p : ℝ) ≤ x - 3 := by
    have hc : (p : ℝ) ≤ ⌊x - 3⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hpI).2
    have hf := Nat.floor_le (by linarith : 0 ≤ x - 3)
    linarith
  have hxp : 0 ≤ x - p := by linarith
  have hset : (Icc 1 ⌊2 * x - p⌋₊).filter (fun q : ℕ => q.Prime ∧ x - p < (q : ℝ)) =
      (Ioc ⌊x - p⌋₊ ⌊2 * x - p⌋₊).filter Nat.Prime := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, hhi⟩, hpr, hlo⟩
      exact ⟨⟨(Nat.floor_lt hxp).mpr hlo, hhi⟩, hpr⟩
    · rintro ⟨⟨hlo, hhi⟩, hpr⟩
      exact ⟨⟨hpr.one_le, hhi⟩, hpr, (Nat.floor_lt hxp).mp hlo⟩
  rw [hset, Finset.sum_const, nsmul_eq_mul, interval_card (by linarith)]
  ring

/-- The prime interval error from the two endpoint instances of 2.16. -/
theorem interval_error (h : Eq216) {a b : ℝ} (ha : 10 ^ 35 ≤ a) (hb : 10 ^ 35 ≤ b) :
    |(piR b - piR a) - (li2 b - li2 a)| <
      b / (38 * Real.log b ^ 2) + a / (38 * Real.log a ^ 2) := by
  have he : (piR b - piR a) - (li2 b - li2 a) = (piR b - li2 b) - (piR a - li2 a) := by ring
  rw [he]
  have ht := abs_sub_le (piR b - li2 b) 0 (piR a - li2 a)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  exact lt_of_le_of_lt ht (add_lt_add (h b hb) (h a ha))

/-- The weighted endpoint error used for the long interval part of the page 103 split. -/
theorem weighted_interval_error (h : Eq216) (s : Finset ℕ) (w a b : ℕ → ℝ)
    (hw : ∀ p ∈ s, 0 ≤ w p) (ha : ∀ p ∈ s, 10 ^ 35 ≤ a p)
    (hb : ∀ p ∈ s, 10 ^ 35 ≤ b p) :
    |∑ p ∈ s, w p * ((piR (b p) - piR (a p)) - (li2 (b p) - li2 (a p)))| ≤
      ∑ p ∈ s, w p * (b p / (38 * Real.log (b p) ^ 2) + a p / (38 * Real.log (a p) ^ 2)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro p hp
  rw [abs_mul, abs_of_nonneg (hw p hp)]
  exact mul_le_mul_of_nonneg_left (interval_error h (ha p hp) (hb p hp)).le (hw p hp)

/-- The two printed budgets imply the unchanged Lemma 11, CONDITIONAL on both errors. -/
theorem lemma11_of_errors (hD : DistributionError) (hQ : QuadratureError) : Lemma11 := by
  intro x hx
  have h := add_lt_add (hD x hx) (hQ x hx)
  have he : x ^ 2 / (5 * Real.log x ^ 2) + x ^ 2 / (10 * Real.log x ^ 2) =
      0.3 * x ^ 2 / Real.log x ^ 2 := by ring
  rw [he] at h
  have ht := abs_sub_le (Psi x) (mainIntegral x) (asymptotic x)
  exact lt_of_le_of_lt ht h

theorem eq510tail_of_eq215_euler {C : ℝ} (hC : C ≤ 6.2130)
    (hBT : Vaughan1977Lemma3.Lemma3Coprime) (h215 : Eq215)
    (hMass : EulerMassBound C) (hMoment : EulerMomentBound) : Eq510tail C :=
  eq510tail_of_euler hC hBT (thetaUpper_of_eq215 h215) hMass hMoment

/-- A paper level assembly. The two page 103 error estimates remain explicit inputs. -/
theorem statement27_of_paper_errors {C : ℝ} (hClow : 6.2022 ≤ C) (hCup : C ≤ 6.2130)
    (hRS : LeanLab.RieselVaughan1983.RS33)
    (h8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC)
    (hBT : Vaughan1977Lemma3.Lemma3Coprime) (h215 : Eq215)
    (hMass : EulerMassBound C) (hMoment : EulerMomentBound)
    (hD : DistributionError) (hQ : QuadratureError) : Vaughan1977.Statement27 :=
  statement27_of_euler hClow hCup hRS h8 (lemma11_of_errors hD hQ) hBT
    (thetaUpper_of_eq215 h215) hMass hMoment

example : piR 6 = 3 := by
  have h : Nat.primeCounting 6 = 3 := by decide
  norm_num [piR, h]

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.thetaUpper_of_eq215
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.interval_card
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.psi_eq_pi
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.interval_error
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.weighted_interval_error
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.lemma11_of_errors
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.eq510tail_of_eq215_euler
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma11Inputs.statement27_of_paper_errors
