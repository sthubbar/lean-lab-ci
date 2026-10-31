/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261019T2314Z-cloud29, unit U-5794, paper P0011.

# DERZ 1997 with Zinoviev's theorem replaced by its GRH arc input

`zinoviev_of_arcInput`: the cited `zinoviev`, GRH ⇒ every odd `n > 10^20` is a sum of three primes,
follows from GRH ⇒ `Zinoviev1997.ArcInput n` for those `n`, by `Zinoviev1997.zinoviev_of_arcs`.
`derz_main_of_arcs`: the P0011 main theorem, CONDITIONAL ON that arc input, `derz_lemma` and the
`10^13` even range, so DERZ's use of P0097 now rests only on the GRH content of Zinoviev's
Lemmas 2.1, 3.2 and 3.3. Binary Goldbach is OPEN.
-/
import LeanLab.DERZ1997.Statements
import LeanLab.Zinoviev1997.Theorem34

namespace LeanLab.DERZ1997

theorem zinoviev_of_arcInput
    (h : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → LeanLab.Zinoviev1997.ArcInput n) :
    GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n := by
  intro hG n ho hn
  have hnR : (10 : ℝ) ^ 20 ≤ n := by exact_mod_cast hn.le
  exact LeanLab.Zinoviev1997.zinoviev_of_arcs n hnR (h hG n ho hn)

theorem derz_main_of_arcs
    (hA : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → LeanLab.Zinoviev1997.ArcInput n)
    (hL : GRH → ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 →
      ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9)
    (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of (zinoviev_of_arcInput hA) hL hD

end LeanLab.DERZ1997
