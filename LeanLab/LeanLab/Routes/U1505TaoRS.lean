/-
Unit U-1505, T3 CONNECTION SWEEP, run 20261023T1343Z-19109. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics. Binary Goldbach is OPEN.

P0007 Tao 2012 cites Ramaré-Saouter 2003 Theorem 3 as its Theorem 8.1, `Tao2012.Theorem8_1`, a
cited input of `theorem1_4_of_section8`. The lab's P0099 folder already proves Ramaré-Saouter
Theorem 3 CONDITIONAL ON Table 1 row one at 10^20, `Theorem2At1e20`, and the Section 7 prime chain
`ChainCert`, RamareSaouter2003/Theorem3Smooth.lean `theorem3_of_chain`.

* `theorem8_1_of_rs3`: Tao's Theorem 8.1 from Ramaré-Saouter Theorem 3 in the lab's real form,
  since 2.8·10^7 < 28 314 000 and 1.1·10^10 > 10 726 905 041. PROVED.
* `theorem8_1_of_chain`: Tao's Theorem 8.1 CONDITIONAL ON `Theorem2At1e20` and `ChainCert`.
* `theorem1_4_of_rs`, `every_at_most_six_of_rs`: Tao's Theorem 1.4 and the six primes bound with
  Theorem 8.1 replaced by those two inputs; the other inputs, Theorem 1.6, Theorem 8.2 as printed
  and Liu-Wang, are unchanged.
-/
import Mathlib
import LeanLab.Tao2012.Section8
import LeanLab.RamareSaouter2003.Theorem3Smooth

namespace LeanLab.Routes.U1505
open LeanLab.Tao2012 LeanLab.SchnirelmannConstant

/-- Ramaré-Saouter Theorem 3, real form, implies Tao's Theorem 8.1. -/
theorem theorem8_1_of_rs3
    (h : ∀ x : ℝ, 10726905041 < x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x) :
    Theorem8_1 := by
  intro y hy
  have hy' : (10726905041 : ℝ) < y := by
    have : (11 * 10 ^ 9 : ℝ) ≤ y := by exact_mod_cast hy
    linarith
  obtain ⟨p, hp, hl, hu⟩ := h y hy'
  have hpy : p ≤ y := by exact_mod_cast hu
  refine ⟨p, hp, hpy, ?_⟩
  have hc : ((y - p : ℕ) : ℝ) = (y : ℝ) - p := Nat.cast_sub hpy
  have h1 : (28314000 : ℝ) * ((y : ℝ) - p) < y := by
    have e : (y : ℝ) * (1 - 1 / 28314000) = y - y / 28314000 := by ring
    rw [e] at hl
    have : (y : ℝ) - p < y / 28314000 := by linarith
    rw [lt_div_iff₀ (by norm_num)] at this
    linarith
  have h0 : (0 : ℝ) ≤ (y : ℝ) - p := by linarith
  have h2 : (28 * 10 ^ 6 : ℝ) * ((y : ℝ) - p) ≤ y := by nlinarith
  rw [← hc] at h2
  exact_mod_cast h2

/-- Tao's Theorem 8.1 CONDITIONAL ON Ramaré-Saouter Table 1 row one and the Section 7 chain. -/
theorem theorem8_1_of_chain (h2 : LeanLab.RamareSaouter2003.Smooth.Theorem2At1e20)
    (hc : LeanLab.RamareSaouter2003.Smooth.ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000) :
    Theorem8_1 :=
  theorem8_1_of_rs3 (LeanLab.RamareSaouter2003.Smooth.theorem3_of_chain h2 hc)

/-- Tao's Theorem 1.4 with Theorem 8.1 replaced by Ramaré-Saouter's own inputs. -/
theorem theorem1_4_of_rs (h2 : LeanLab.RamareSaouter2003.Smooth.Theorem2At1e20)
    (hc : LeanLab.RamareSaouter2003.Smooth.ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000)
    (h16 : EvenGoldbachUpTo N0) (h82 : Theorem8_2_printed) (hLW : LiuWang) :
    ∀ x : ℕ, Odd x → 1 < x → AtMostPrimes 5 x :=
  theorem1_4_of_section8 (theorem8_1_of_chain h2 hc) h16 h82 hLW

/-- The six primes bound with the same inputs. -/
theorem every_at_most_six_of_rs (h2 : LeanLab.RamareSaouter2003.Smooth.Theorem2At1e20)
    (hc : LeanLab.RamareSaouter2003.Smooth.ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000)
    (h16 : EvenGoldbachUpTo N0) (h82 : Theorem8_2_printed) (hLW : LiuWang) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 6 n :=
  every_at_most_six_of_section8 (theorem8_1_of_chain h2 hc) h16 h82 hLW

/-- Vacuity of the arithmetic step: at y = 11·10^9 the hypothesis range of Theorem 8.1 is met. -/
example : (10726905041 : ℝ) < (11 * 10 ^ 9 : ℕ) := by norm_num

end LeanLab.Routes.U1505

#print axioms LeanLab.Routes.U1505.theorem8_1_of_rs3
#print axioms LeanLab.Routes.U1505.theorem8_1_of_chain
#print axioms LeanLab.Routes.U1505.theorem1_4_of_rs
#print axioms LeanLab.Routes.U1505.every_at_most_six_of_rs
