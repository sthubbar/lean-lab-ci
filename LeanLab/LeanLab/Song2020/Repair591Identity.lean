/-
AI wrote the Lean code. CODEX task591.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, page 3, Lemma 2.
The statement is written in Dirichlet convolution notation.
Binary Goldbach is open.
-/
import LeanLab.Akeno2026.Vaughan86

namespace LeanLab.Song2020.Repair591Identity

open ArithmeticFunction LeanLab.Akeno2026.Vaughan86
open scoped Classical

noncomputable section

/-- Song 2020, page 3, Lemma 2. In convolution notation the three terms equal
Lambda minus its part below u. At n above u this is exactly Lambda of n. -/
theorem song_lemma2_convolution591 (u v : ℝ) (n : ℕ) (hn : u < (n : ℝ)) :
    vonMangoldt n =
      (shortPart (moebius : ArithmeticFunction ℝ) v * log) n -
      (shortPart (moebius : ArithmeticFunction ℝ) v * shortPart vonMangoldt u *
        (zeta : ArithmeticFunction ℝ)) n -
      ((vonMangoldt - shortPart vonMangoldt u) *
        (shortPart (moebius : ArithmeticFunction ℝ) v * (zeta : ArithmeticFunction ℝ) - 1)) n := by
  have h : shortPart (moebius : ArithmeticFunction ℝ) v * log -
      shortPart (moebius : ArithmeticFunction ℝ) v * shortPart vonMangoldt u *
        (zeta : ArithmeticFunction ℝ) -
      (vonMangoldt - shortPart vonMangoldt u) *
        (shortPart (moebius : ArithmeticFunction ℝ) v * (zeta : ArithmeticFunction ℝ) - 1) =
      vonMangoldt - shortPart vonMangoldt u := by
    rw [← vonMangoldt_mul_zeta]
    ring
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  have hs : shortPart vonMangoldt u n = 0 := by
    change (if (n : ℝ) ≤ u then vonMangoldt n else 0) = 0
    simp [not_le.mpr hn]
  simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, hs, neg_zero, add_zero] using he.symm

/-- Song 2020, page 3, Lemma 2. The factor mu cut at v convolved with one,
minus the convolution unit, is the divisor sum b of k restricted to k above one. -/
theorem cut_mobius_divisor_tail591 (v : ℝ) (hv : 1 ≤ v) (k : ℕ) :
    (shortPart (moebius : ArithmeticFunction ℝ) v * (zeta : ArithmeticFunction ℝ) - 1) k =
      if 1 < k then ∑ d ∈ k.divisors,
        (if (d : ℝ) ≤ v then (moebius : ArithmeticFunction ℝ) d else 0) else 0 := by
  rcases k with _ | k
  · simp
  rcases k with _ | k
  · rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
      ArithmeticFunction.coe_mul_zeta_apply]
    simp [shortPart, hv]
  · rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.one_apply_ne (by omega), neg_zero, add_zero, if_pos (by omega)]
    rfl

end

end LeanLab.Song2020.Repair591Identity

#print axioms LeanLab.Song2020.Repair591Identity.song_lemma2_convolution591
#print axioms LeanLab.Song2020.Repair591Identity.cut_mobius_divisor_tail591
