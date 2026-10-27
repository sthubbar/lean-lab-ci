/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0002 Chen 1973, p. 171, the lambda convolution before display 24.
The finite upper-divisor Moebius inversion is stated separately from the quadratic form.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973Weights

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973LambdaConvolution

open Chen1973Display24 Chen1973Weights

/-- Upper-divisor Moebius inversion on a finite divisor-closed set. -/
lemma upper_moebius_inversion (s : Finset ℕ) (h0 : ∀ m ∈ s, m ≠ 0)
    (hdc : ∀ m ∈ s, ∀ d, d ∣ m → d ∈ s) (Y : ℕ → ℝ) {k : ℕ} (hk : k ∈ s) :
    (∑ d ∈ s.filter (k ∣ ·), ∑ m ∈ s.filter (d ∣ ·), ((μ (m / d) : ℤ) : ℝ) * Y m) = Y k := by
  classical
  rw [sum_comm' (t' := s) (s' := fun m => m.divisors.filter (k ∣ ·))]
  · simp_rw [← sum_mul]
    rw [sum_eq_single_of_mem k hk]
    · rw [sum_moebius_interval (h0 k hk) (dvd_refl k), ite_eq_left rfl, one_mul]
    · intro m hm hmk
      by_cases hkm : k ∣ m
      · rw [sum_moebius_interval (h0 m hm) hkm, ite_eq_right hmk, zero_mul]
      · have he : m.divisors.filter (k ∣ ·) = ∅ := by
          apply eq_empty_of_forall_notMem
          intro d hd
          simp only [mem_filter, Nat.mem_divisors] at hd
          exact hkm (hd.2.trans hd.1.1)
        rw [he, sum_empty, zero_mul]
  · intro d m
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, hkd⟩, hm, hdm⟩
      exact ⟨⟨⟨hdm, h0 m hm⟩, hkd⟩, hm⟩
    · rintro ⟨⟨⟨hdm, _⟩, hkd⟩, hm⟩
      exact ⟨⟨hdc m hm d hdm, hkd⟩, hm, hdm⟩

/-- Chen p. 171: the lambda convolution immediately before display 24. -/
theorem lamC_convolution {x D k : ℕ} (hk : k ∈ sv x D) :
    ∑ d ∈ (sv x D).filter (k ∣ ·), lamC x D d / (d.totient : ℝ) =
      ((μ k : ℤ) : ℝ) / (Sv x D * ψ k) := by
  have he : ∀ d ∈ sv x D, lamC x D d / (d.totient : ℝ) =
      ∑ m ∈ (sv x D).filter (d ∣ ·),
        ((μ (m / d) : ℤ) : ℝ) * (((μ m : ℤ) : ℝ) / (Sv x D * ψ m)) := by
    intro d hd
    have hdpos : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hphi : (d.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hdpos).ne'
    unfold lamC
    rw [mul_div_cancel_left₀ _ hphi]
  rw [sum_congr rfl (fun d hd => he d (mem_filter.mp hd).1)]
  apply upper_moebius_inversion (sv x D) ?_ ?_ _ hk
  · intro m hm
    exact (Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hm).1).1)
  · intro m hm d hdm
    exact sv_mem_of_dvd hm hdm

example : ∑ d ∈ (sv 2 1).filter (1 ∣ ·), lamC 2 1 d / (d.totient : ℝ) =
    ((μ 1 : ℤ) : ℝ) / (Sv 2 1 * ψ 1) := lamC_convolution (by simp [sv])

end LeanLab.AlmostPrimeSums.Chen1973LambdaConvolution

#print axioms LeanLab.AlmostPrimeSums.Chen1973LambdaConvolution.upper_moebius_inversion

#print axioms LeanLab.AlmostPrimeSums.Chen1973LambdaConvolution.lamC_convolution
