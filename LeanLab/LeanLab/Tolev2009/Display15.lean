/-
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/
import LeanLab.Tolev2009.Displays14to16

open Finset Real

namespace LeanLab.Tolev2009.Display15

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16

/-- Prime pairs in the coefficient w of display 15.
The printed condition on the second prime follows from k dividing n when it is needed. -/
def pairs (k l N : ℕ) (n : ℤ) : Finset (ℕ × ℕ) :=
  (primeSet k l N ×ˢ primeSet 1 0 N).filter (fun pp => (pp.1 : ℤ) - pp.2 = n)

/-- The nonnegative correlation coefficient printed in display 15. -/
noncomputable def w (k l N : ℕ) (n : ℤ) : ℝ :=
  ∑ pp ∈ pairs k l N n, Real.log pp.1 * Real.log pp.2

/-- The first prime and the frequency determine the second prime. -/
theorem pairs_card_le (k l N : ℕ) (n : ℤ) (hk : 1 ≤ k) :
    (pairs k l N n).card ≤ N / k + 1 := by
  refine le_trans ?_ (card_primeSet_le k l N hk)
  apply card_le_card_of_injOn Prod.fst
  · intro pp hpp
    exact (mem_product.mp (mem_filter.mp hpp).1).1
  · intro p hp q hq he
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    exact Prod.ext he (by omega)

theorem w_nonneg (k l N : ℕ) (n : ℤ) : 0 ≤ w k l N n := by
  apply sum_nonneg
  intro pp _
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

/-- Display 15 before replacing the modulus by its dyadic scale. -/
theorem w_le (k l N : ℕ) (n : ℤ) (hk : 1 ≤ k) :
    w k l N n ≤ Real.log N ^ 2 * ((N : ℝ) / k + 1) := by
  have ht : ∀ pp ∈ pairs k l N n, Real.log pp.1 * Real.log pp.2 ≤ Real.log N ^ 2 := by
    intro pp hpp
    rcases mem_product.mp (mem_filter.mp hpp).1 with ⟨hp, hq⟩
    have h1 := log_mem_primeSet hp
    have h2 := log_mem_primeSet hq
    simpa only [pow_two] using mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)
  have hc : ((pairs k l N n).card : ℝ) ≤ (N : ℝ) / k + 1 := by
    have h := pairs_card_le k l N n hk
    have hd : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
    calc
      ((pairs k l N n).card : ℝ) ≤ ((N / k + 1 : ℕ) : ℝ) := by exact_mod_cast h
      _ ≤ _ := by push_cast; linarith
  calc
    _ ≤ ∑ pp ∈ pairs k l N n, Real.log N ^ 2 := sum_le_sum ht
    _ = ((pairs k l N n).card : ℝ) * Real.log N ^ 2 := by simp [sum_const]
    _ ≤ ((N : ℝ) / k + 1) * Real.log N ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by ring

/-- Display 15, with an explicit constant and the paper's natural dyadic scale. -/
theorem display15 (K k l N : ℕ) (n : ℤ) (hK : 1 ≤ K) (hKk : K < k) (hKN : K ≤ N) :
    |w k l N n| ≤ 2 * Real.log N ^ 2 * N / K := by
  rw [abs_of_nonneg (w_nonneg _ _ _ _)]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hd : (N : ℝ) / k ≤ N / K :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hK0 (by exact_mod_cast hKk.le)
  have hone : (1 : ℝ) ≤ (N : ℝ) / K := (one_le_div hK0).mpr (by exact_mod_cast hKN)
  refine (w_le k l N n (by omega)).trans ?_
  have h := mul_le_mul_of_nonneg_left (show (N : ℝ) / k + 1 ≤ 2 * ((N : ℝ) / K) by linarith)
    (sq_nonneg (Real.log N))
  convert h using 1 <;> ring

/-- Modulus divisibility supplies the second prime's missing progression condition. -/
theorem second_congruence (k l N : ℕ) (n : ℤ) (hn : (k : ℤ) ∣ n)
    (pp : ℕ × ℕ) (hpp : pp ∈ pairs k l N n) : pp.2 % k = l % k := by
  rcases mem_filter.mp hpp with ⟨hpp, hdiff⟩
  have hp := (mem_product.mp hpp).1
  have hpmod := (mem_filter.mp hp).2.2
  have hd : (k : ℤ) ∣ (pp.1 : ℤ) - pp.2 := hdiff ▸ hn
  have he : pp.2 ≡ pp.1 [MOD k] := Nat.modEq_of_dvd hd
  exact he.trans hpmod

end LeanLab.Tolev2009.Display15
