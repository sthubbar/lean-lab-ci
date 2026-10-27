/-
P0069, Lemma 9, pages 22 and 23. The analytic leaf retains Perron's
formula, contour estimates and the Dirichlet L fourth moment.
The finite fourth-power assembly is explicit and reuses Lemma9.lean.
The final theorem is CONDITIONAL on the analytic leaf.
AI wrote the Lean code. CODEX task132, 2026-10-26. Goldbach is open.
-/
import LeanLab.BHP1997.MeanValue132
import LeanLab.BHP1997.Lemma9

namespace LeanLab.BHP1997.Decomp132b
open Classical Complex MeanValue132

/-- LEAF. Pages 22 and 23, formula 3.36 and the following fourth moment
estimate for J. Sources outside P0069: Perron's formula from Titchmarsh,
reference 30, Theorem 3.19; the Dirichlet L fourth moment from Ramachandra,
reference 26, as cited in Lemma 7; Rademacher, reference 28, via Lemma 8.
The extra log x on the first contour error costs only an absolute constant
since x is at least 2. Retain this named analytic input as CONDITIONAL. -/
theorem perron_input :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x N T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        ∃ J : ℝ × DirichletCharacter ℂ q → ℂ,
          (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C * ((q : ℝ) * T * Real.log x ^ B) ∧
          ∀ p ∈ S, ‖partialSum N p.2 p.1‖ ≤ ‖J p‖ +
            C * Real.log x * (Real.sqrt q / Real.sqrt T) +
            C * Real.log x * (Real.sqrt N / T) +
            C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) := by
  sorry

/-- LEAF. Page 23, taking fourth powers in 3.36 and summing.
The factor 64 is the existing Lemma9.pow4_sum. -/
theorem fourth_moment_sum {α : Type*} (S : Finset α) (F J : α → ℂ)
    (a b c : α → ℝ)
    (h : ∀ p ∈ S, ‖F p‖ ≤ ‖J p‖ + a p + b p + c p) :
    (∑ p ∈ S, ‖F p‖ ^ 4) ≤ 64 * ((∑ p ∈ S, ‖J p‖ ^ 4) +
      ∑ p ∈ S, ((a p) ^ 4 + (b p) ^ 4 + (c p) ^ 4)) := by
  calc
    (∑ p ∈ S, ‖F p‖ ^ 4) ≤ ∑ p ∈ S,
        64 * (‖J p‖ ^ 4 + (a p) ^ 4 + (b p) ^ 4 + (c p) ^ 4) := by
      apply Finset.sum_le_sum
      intro p hp
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (h p hp) 4)
        (LeanLab.BHP1997.Lemma9.pow4_sum _ _ _ _)
    _ = 64 * ((∑ p ∈ S, ‖J p‖ ^ 4) +
        ∑ p ∈ S, ((a p) ^ 4 + (b p) ^ 4 + (c p) ^ 4)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- LEAF. Page 22, the error fourth powers in the displayed bound.
Reuse Lemma9.fourth_powers for the three square-root quotients. -/
theorem error_sum {q : ℕ} (x N T C : ℝ) (hN : 0 ≤ N) (hT : 0 ≤ T)
    (S : Finset (ℝ × DirichletCharacter ℂ q)) :
    (∑ p ∈ S, ((C * Real.log x * (Real.sqrt q / Real.sqrt T)) ^ 4 +
      (C * Real.log x * (Real.sqrt N / T)) ^ 4 +
      (C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0)) ^ 4)) =
        C ^ 4 * remainder x N T S := by
  have hp (t : ℝ) := LeanLab.BHP1997.Lemma9.fourth_powers
    (q := (q : ℝ)) (T := T) (N := N) (t := t) (Nat.cast_nonneg _) hT hN
  have hfirst : (C * Real.log x * (Real.sqrt q / Real.sqrt T)) ^ 4 =
      C ^ 4 * Real.log x ^ 4 * ((q : ℝ) ^ 2 / T ^ 2) := by
    rw [mul_pow, mul_pow, (hp 0).1]
  have hsecond : (C * Real.log x * (Real.sqrt N / T)) ^ 4 =
      C ^ 4 * Real.log x ^ 4 * (N ^ 2 / T ^ 4) := by
    rw [mul_pow, mul_pow, (hp 0).2.1]
  have hthird (p : ℝ × DirichletCharacter ℂ q) :
      (C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0)) ^ 4 =
        C ^ 4 * N ^ 2 * (if p.2 = 1 then 1 / (1 + |p.1|) ^ 4 else 0) := by
    by_cases hc : p.2 = 1
    · simp only [hc, ite_true, mul_pow, (hp p.1).2.2]
      ring
    · simp [hc]
  simp_rw [hfirst, hsecond, hthird]
  unfold remainder
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

/-- Lemma 9, page 22, with the exact cited Prop as conclusion.
CONDITIONAL on perron_input. The assembly has no direct sorry. -/
theorem lemma9 : MeanValue132.Lemma9 := by
  obtain ⟨B, C, hB, hC, hinput⟩ := perron_input
  refine ⟨B, 64 * max C (C ^ 4), hB, by positivity, ?_⟩
  intro x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  obtain ⟨J, hJ, hpoint⟩ := hinput x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  have hs := fourth_moment_sum S (fun p => partialSum N p.2 p.1) J
    (fun _ => C * Real.log x * (Real.sqrt q / Real.sqrt T))
    (fun _ => C * Real.log x * (Real.sqrt N / T))
    (fun p => C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0)) hpoint
  rw [error_sum x N T C (by linarith) (by linarith) S] at hs
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hmain : 0 ≤ (q : ℝ) * T * Real.log x ^ B := by positivity
  have hrem : 0 ≤ remainder x N T S := by
    unfold remainder
    apply add_nonneg
    · positivity
    · apply mul_nonneg (sq_nonneg _)
      apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
  have h1 := mul_le_mul_of_nonneg_right (le_max_left C (C ^ 4)) hmain
  have h2 := mul_le_mul_of_nonneg_right (le_max_right C (C ^ 4)) hrem
  nlinarith

end LeanLab.BHP1997.Decomp132b
