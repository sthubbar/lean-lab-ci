/-
AI wrote this Lean code for CODEX task51.
P0074 pages 7 and 8, finite expansion for Lemma 3.1.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.ComplexRamanujan
import LeanLab.Grimmelt2019.NearestFraction
import LeanLab.PNTPort.LargeSieve.Farey

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- Negative frequencies give the same real Ramanujan sum. -/
theorem ram_sum_neg_eq (q : ℕ) (m : ℤ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      LeanLab.PNTPort.LargeSieve.e (-((m : ℝ) * a / q))) = (ram q m : ℂ) := by
  simp_rw [e_neg]
  rw [← map_sum, ram_sum_eq, Complex.conj_ofReal]

/-- A Farey sum groups exactly into its reduced residues at each denominator. -/
theorem sum_farey_by_denominator {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (f : ℕ × ℕ → A) :
    ∑ p ∈ farey Q, f p = ∑ q ∈ Finset.Icc 1 Q,
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), f (q, a) := by
  classical
  unfold farey
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  have hqQ := (Finset.mem_Icc.mp hq).2
  rw [← Finset.sum_filter]
  have he : (Finset.range Q).filter (fun a => a < q ∧ Nat.Coprime a q) =
      (Finset.range q).filter (fun a => Nat.Coprime a q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  exact congrArg (fun S : Finset ℕ => ∑ a ∈ S, f (q, a)) he

/-- The real model has the paper's negative-frequency Farey expansion. -/
theorem LamQ_eq_farey (Q : ℕ) (n : ℤ) :
    (LamQ Q n : ℂ) = ∑ p ∈ farey Q,
      ((ArithmeticFunction.moebius p.1 : ℂ) / p.1.totient) *
        LeanLab.PNTPort.LargeSieve.e (-((n : ℝ) * fareyPt p)) := by
  rw [sum_farey_by_denominator]
  unfold LamQ
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_natCast, ← ram_sum_neg_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  unfold fareyPt
  ring

/-- Expanding the model and exchanging the finite sums isolates each frequency. -/
theorem shortInterval_LamQ_expansion (Q : ℕ) (t H α : ℝ) :
    (∑ n ∈ shortInterval t H, (LamQ Q n : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) =
      ∑ p ∈ farey Q, ((ArithmeticFunction.moebius p.1 : ℂ) / p.1.totient) *
        ∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * (α - fareyPt p)) := by
  simp_rw [LamQ_eq_farey, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, ← e_add]
  congr 2
  ring

#print axioms ram_sum_neg_eq
#print axioms sum_farey_by_denominator
#print axioms LamQ_eq_farey
#print axioms shortInterval_LamQ_expansion
end LeanLab.Grimmelt2019.MainTerm
