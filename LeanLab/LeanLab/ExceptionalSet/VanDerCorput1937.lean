/-
P0063 J. G. van der Corput, Sur l'hypothèse de Goldbach pour presque tous les nombres pairs,
Acta Arith. 2 (1937) 266-290. Read from the page images of Lean Lab/copies/P0063.pdf, a scan
saved by Steve 2026-10-19, page 267, by the live session after run 20261018T2303Z-8776.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Page 267: "à tout nombre naturel m correspond une constante c₁, ne dépendant que de m, telle que
pour toute valeur ≥ 3 de N, le nombre des nombres naturels pairs ≤ N qui ne sont pas égaux à la
somme de deux nombres premiers impairs, est inférieur à c₁ N (log N)^{-m}." The same page also
announces that almost every even number is a difference of two odd primes, with exceptions
below c₂ N (log N)^{-m}.
-/
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet
open Real

attribute [local instance] Classical.propDecidable

/-- Sum of two odd primes. -/
def IsOddGoldbachSum (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = n

/-- The paper's count: even naturals `1 ≤ n ≤ N` that are not a sum of two odd primes. -/
noncomputable def Eodd (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => Even n ∧ ¬ IsOddGoldbachSum n)).card

/-- The main theorem of page 267, as printed. Cited. -/
def VdCTheorem : Prop :=
  ∀ m : ℕ, ∃ c₁ : ℝ, ∀ N : ℕ, 3 ≤ N → (Eodd N : ℝ) < c₁ * N * Real.log N ^ (-(m : ℝ))

/-- Even `n` that is a difference of two odd primes. -/
def IsOddPrimeDiff (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p = q + n

/-- The second theorem announced on page 267: exceptions to "even = difference of two odd
primes" up to `N` number below `c₂ N (log N)^{-m}`. Cited. -/
def VdCDifference : Prop :=
  ∀ m : ℕ, ∃ c₂ : ℝ, ∀ N : ℕ, 3 ≤ N →
    ((((Finset.Icc 1 N).filter (fun n => Even n ∧ ¬ IsOddPrimeDiff n)).card : ℕ) : ℝ)
      < c₂ * N * Real.log N ^ (-(m : ℝ))

lemma E_le_Eodd (N : ℕ) : E N ≤ Eodd N := by
  unfold E Eodd
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  refine ⟨⟨by omega, hn.1.2⟩, hn.2.1, ?_⟩
  rintro ⟨p, q, hp, hq, -, -, h⟩
  exact hn.2.2 ⟨p, q, hp, hq, h⟩

/-- van der Corput's theorem gives the lab's `LogPowerSaving`, the strength credited to him. -/
theorem logPowerSaving_of_vdc (h : VdCTheorem) : LogPowerSaving := by
  intro A hA
  obtain ⟨c, hc⟩ := h ⌈A⌉₊
  refine ⟨max c 0 + 1, fun X hX => ?_⟩
  rcases (show X = 2 ∨ 3 ≤ X by omega) with rfl | hX3
  · have : E 2 = 0 := by
      unfold E; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro n hn; simp at hn <;> omega
    rw [this]; simp only [Nat.cast_zero]
    have : 0 < Real.log (2 : ℕ) := Real.log_pos (by norm_num)
    positivity
  · have hXr : (3 : ℝ) ≤ X := by exact_mod_cast hX3
    have hL1 : 1 ≤ Real.log X := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
    have hLpos : 0 < Real.log X := by linarith
    have h1 := hc X hX3
    have hE : (E X : ℝ) ≤ Eodd X := by exact_mod_cast E_le_Eodd X
    have hpow : Real.log X ^ (-((⌈A⌉₊ : ℕ) : ℝ)) ≤ Real.log X ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by have := Nat.le_ceil A; linarith)
    have hdiv : (X : ℝ) / Real.log X ^ A = X * Real.log X ^ (-A) := by
      rw [Real.rpow_neg hLpos.le, div_eq_mul_inv]
    rw [mul_div_assoc, hdiv]
    have hX0 : (0 : ℝ) ≤ X := by positivity
    have hp0 : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hLpos.le _
    have hp1 : 0 ≤ Real.log X ^ (-((⌈A⌉₊ : ℕ) : ℝ)) := Real.rpow_nonneg hLpos.le _
    calc (E X : ℝ) ≤ Eodd X := hE
      _ ≤ c * X * Real.log X ^ (-((⌈A⌉₊ : ℕ) : ℝ)) := h1.le
      _ ≤ (max c 0 + 1) * X * Real.log X ^ (-((⌈A⌉₊ : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hp1
          apply mul_le_mul_of_nonneg_right _ hX0
          linarith [le_max_left c 0]
      _ ≤ (max c 0 + 1) * (X * Real.log X ^ (-A)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpow hX0

/-- Hence the title form, almost all even numbers are Goldbach sums. -/
theorem densityZero_of_vdc (h : VdCTheorem) : DensityZero :=
  vanDerCorput_of_strong (logPowerSaving_of_vdc h)

end LeanLab.ExceptionalSet
