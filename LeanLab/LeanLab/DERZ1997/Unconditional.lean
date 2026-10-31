/-
The P0011 intermediate lemma without GRH, from two explicit short interval theorems.
Inputs, cited, not proved here:
  P0099 Ramaré-Saouter 2003: for every y > 10 726 905 041 the interval (y (1 - 1/Δ), y]
    holds a prime, Δ = 28 314 000; the lab's form is `LeanLab.Tao2012.RSShortIntervals`.
  P0059 Kadiri-Lumley 2014, arXiv 1407.7902, Theorem 1.1 with the Table 2 row log x0 = 45,
    Δ = 95 381 241: for every x > e^45 there is a prime p with (1 - 1/Δ) x < p < x.
    VERIFY 2026-10-16: Table 2 headers are log x0, m, δ, T1, σ0, a, Δ, so Δ = 95 381 241;
    797 398 875 is T1. Theorem 1.1 needs x > x0 ≥ 4e18 and gives a strict interval.
Not new: Ramaré-Saouter 2003 Corollary 1 already reach odd Goldbach to 1.132e22 by this ladder.
The exact DERZ constant 1.615e12 up to 10^20 needs Kadiri-Lumley at the top; no print source
for that combination was found, but it is an immediate corollary, a re-derivation.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.DERZ1997.Statements
import LeanLab.Tao2012.SmallRange

namespace LeanLab.DERZ1997
open LeanLab.Tao2012

/-- Kadiri-Lumley Table 2, row `log x0 = 45`, natural number form. -/
def KL45 : Prop :=
  ∀ y : ℕ, Real.exp 45 < y → ∃ p : ℕ, p.Prime ∧ p < y ∧ 95381241 * (y - p) < y

theorem exp45_lt : Real.exp 45 < 45 * 10 ^ 18 := by
  have h1 : Real.exp 45 = Real.exp 1 ^ 45 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1]
  calc Real.exp 1 ^ 45 < (2.7182818286 : ℝ) ^ 45 := by
        gcongr; exact Real.exp_one_lt_d9
    _ < 45 * 10 ^ 18 := by norm_num

/-- The P0011 intermediate lemma, unconditionally, from Ramaré-Saouter and Kadiri-Lumley.
Small `n` take `p = 2`. Up to `4.5 · 10^19` Ramaré-Saouter's gap `y / 28314000` is below
`1.59 · 10^12`; above, Kadiri-Lumley's gap `y / 95381241` is below `1.05 · 10^12`. -/
theorem derz_lemma_of_intervals (hRS : RSShortIntervals) (hKL : KL45) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9 := by
  intro n h6 hn
  rcases Nat.lt_or_ge (1615 * 10 ^ 9 + 2) n with hbig | hsmall
  · set y := n - 4 with hy
    rcases Nat.lt_or_ge (45 * 10 ^ 18) y with hhi | hlo
    · have hexp : Real.exp 45 < (y : ℝ) := by
        calc Real.exp 45 < 45 * 10 ^ 18 := exp45_lt
          _ < (y : ℝ) := by exact_mod_cast hhi
      obtain ⟨p, hp, hpy, hgap⟩ := hKL y hexp
      refine ⟨p, hp, by omega, ?_⟩
      norm_num at hn hgap ⊢
      omega
    · have hy0 : 10726905041 < y := by norm_num at hbig ⊢; omega
      obtain ⟨p, hp, hpy, hgap⟩ := hRS y hy0
      simp only [Δ] at hgap
      refine ⟨p, hp, by omega, ?_⟩
      norm_num at hlo hgap ⊢
      omega
  · exact ⟨2, Nat.prime_two, by omega, by omega⟩

/-- P0011's main theorem with GRH used only through Zinoviev's large range. -/
theorem derz_main_of_intervals
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hRS : RSShortIntervals) (hKL : KL45) (hD : EvenGoldbachUpTo (10 ^ 13)) :
    GRH → TernaryGoldbach :=
  derz_main_of hZ (fun _ => derz_lemma_of_intervals hRS hKL) hD

/-- Without GRH: odd Goldbach up to `10^20` from the lemma's conclusion and the even range,
the same ladder Saouter 1998 used with other inputs. -/
theorem ternary_upTo_of_lemma
    (hL : ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 1615 * 10 ^ 9)
    (hD : EvenGoldbachUpTo (10 ^ 13)) : TernaryGoldbachUpTo (10 ^ 20) := by
  intro n ho h7 hn
  rcases Nat.lt_or_ge n (10 ^ 13 + 4) with hlow | hmid
  · have hev : Even (n - 3) := Nat.Odd.sub_odd ho (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩
  · obtain ⟨p, hp, h4, hle⟩ := hL n (by omega) hn
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (1615 : ℕ) * 10 ^ 9 < n - 2 := by norm_num at hmid ⊢; omega
      omega
    have hev : Even (n - p) := Nat.Odd.sub_odd ho (hp.eq_two_or_odd'.resolve_left hp2)
    obtain ⟨q, r, hq, hr, hqr⟩ := hD (n - p) hev h4 (by norm_num at hle ⊢; omega)
    exact ⟨p, q, r, hp, hq, hr, by omega⟩

/-- Odd Goldbach to `10^20` unconditionally from Ramaré-Saouter, Kadiri-Lumley and the
`10^13` even range: Saouter's 1998 theorem, P0018, re-derived from later inputs. -/
theorem saouter_of_intervals (hRS : RSShortIntervals) (hKL : KL45)
    (hD : EvenGoldbachUpTo (10 ^ 13)) : TernaryGoldbachUpTo (10 ^ 20) :=
  ternary_upTo_of_lemma (derz_lemma_of_intervals hRS hKL) hD

end LeanLab.DERZ1997
