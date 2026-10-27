import LeanLab.PNTPort.Vinogradov.TernaryCircle

/-!
# Route R-5020: the ternary asymptotic is blind to one binary exception

T3 MOONSHOT map entry, unit U-5258. AI wrote this file. KNOWN mathematics; not progress on
Goldbach, which is open.

* `r3_eq_sum_r2`: `r₃(n) = ∑_{a ≤ N} Λ(a) r₂(n - a)` with `r₂(m) = ∑_{b + c = m, b, c ≤ N} Λ(b)Λ(c)`.
* `one_exception_change`: replacing `r₂` by a function that differs from it only at one `m₀`,
  for instance a world where `m₀` has no Goldbach representation, changes the sum by at most
  `log N · |r₂(m₀) - r₂'(m₀)|`; with `r₂(m₀) ≪ N log N` this is `N log² N`, against
  `r₃(n) ≍ N²`, so an error term `N²/(log N)^A` cannot see a single exception.
-/

namespace LeanLab.Routes.R5020

open Finset Real
open LeanLab.PNTPort.Vinogradov

/-- The binary count with both summands in `[1, N]`. -/
noncomputable def r2 (N m : ℕ) : ℝ :=
  ∑ b ∈ Icc 1 N, ∑ c ∈ Icc 1 N, if b + c = m then Λ b * Λ c else 0
  where Λ := ArithmeticFunction.vonMangoldt

theorem r3_eq_sum_r2 (N n : ℕ) :
    r3 N n = ∑ a ∈ Icc 1 N, ArithmeticFunction.vonMangoldt a * r2 N (n - a) := by
  unfold r3 r2
  refine sum_congr rfl fun a ha => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [mem_Icc] at ha hb hc
  by_cases h : a + b + c = n
  · rw [if_pos h, if_pos (by omega)]; simp [r2.Λ]; ring
  · rw [if_neg h, if_neg (by omega), mul_zero]

/-- One changed value of `r₂` moves the ternary sum by at most `log N` times the change. -/
theorem one_exception_change (N n m₀ : ℕ) (hm₀ : 1 ≤ m₀) (r2' : ℕ → ℝ) (h : ∀ m, m ≠ m₀ → r2' m = r2 N m) :
    |r3 N n - ∑ a ∈ Icc 1 N, ArithmeticFunction.vonMangoldt a * r2' (n - a)| ≤
      Real.log N * |r2 N m₀ - r2' m₀| := by
  rw [r3_eq_sum_r2, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  have hz : ∀ a ∈ Icc 1 N, n - a ≠ m₀ →
      ArithmeticFunction.vonMangoldt a * (r2 N (n - a) - r2' (n - a)) = 0 := by
    intro a _ ha; rw [h _ ha, sub_self, mul_zero]
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun a => n - a = m₀),
    sum_eq_zero (s := (Icc 1 N).filter (fun a => ¬ (n - a = m₀)))
      (fun a ha => by rw [mem_filter] at ha; exact hz a ha.1 ha.2), add_zero]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hl : ∀ a ∈ (Icc 1 N).filter (fun a => n - a = m₀),
      |ArithmeticFunction.vonMangoldt a * (r2 N (n - a) - r2' (n - a))| =
        ArithmeticFunction.vonMangoldt a * |r2 N m₀ - r2' m₀| := by
    intro a ha
    rw [mem_filter] at ha
    rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ha.2]
  rw [sum_congr rfl hl, ← sum_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  -- the fibre is at most the single point `n - m₀`
  have hsub : (Icc 1 N).filter (fun a => n - a = m₀) ⊆ {n - m₀} := by
    intro a ha; rw [mem_filter] at ha; rw [mem_singleton]; omega
  have hcard : ((Icc 1 N).filter (fun a => n - a = m₀)).card ≤ 1 :=
    (card_le_card hsub).trans (card_singleton _).le
  have hlN := Real.log_natCast_nonneg N
  calc ∑ a ∈ (Icc 1 N).filter (fun a => n - a = m₀), ArithmeticFunction.vonMangoldt a
      ≤ ∑ a ∈ (Icc 1 N).filter (fun a => n - a = m₀), Real.log N := by
        refine sum_le_sum fun a ha => ?_
        rw [mem_filter, mem_Icc] at ha
        exact ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log (by exact_mod_cast ha.1.1) (by exact_mod_cast ha.1.2))
    _ = ((Icc 1 N).filter (fun a => n - a = m₀)).card * Real.log N := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * Real.log N := by
        apply mul_le_mul_of_nonneg_right _ hlN; exact_mod_cast hcard
    _ = Real.log N := one_mul _

end LeanLab.Routes.R5020
