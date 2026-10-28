/-
P0022 L. Kaniecki 1995, Acta Arith. 72, page 371.
Decomposition of the proof of Lemma 6.
AI wrote this Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.KanieckiGap.Lemma6

namespace LeanLab.KanieckiGap

/-- LEAF. Page 371, (6.1). Upper bound for gapAt p in the large p case. -/
theorem large_p_gap_bound (hS : LeanLab.DERZ1997.Schoenfeld61) {p x : ℕ} (hp : p.Prime)
    (hsmall : ¬ nextPrime p ≤ 7263 * 10 ^ 10) (hpR : (23 * 10 ^ 8 : ℝ) ≤ p)
    (hpx : p ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * Real.pi) := by
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  obtain ⟨hq1, hq2⟩ := nextPrime_spec p
  have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
  set q := nextPrime p with hq
  have hθ := theta_before_next p
  rw [← hq] at hθ
  have hcast : ((q - 1 : ℕ) : ℝ) = (p : ℝ) + (gapAt p : ℝ) - 1 := by
    unfold gapAt; rw [← hq]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hg1 : (1 : ℝ) ≤ gapAt p := by unfold gapAt; exact_mod_cast (by omega : 1 ≤ q - p)
  have hS1 := hS ((q - 1 : ℕ) : ℝ) (by rw [hcast]; linarith)
  have hS2 := hS (p : ℝ) hpR
  have hgp : (gapAt p : ℝ) ≤ p := by unfold gapAt; exact_mod_cast (by omega : q - p ≤ p)
  have hkey : (gapAt p : ℝ) - 1 < B p + B (p + gapAt p - 1) := by
    rw [hθ, hcast] at hS1
    have a1 := (abs_lt.mp hS1).1
    have a2 := (abs_lt.mp hS2).2
    unfold B; linarith
  refine (core hpR hg1 hgp hkey).trans_le ?_
  have hpx' : (p : ℝ) ≤ x := by exact_mod_cast hpx
  have hLp := log_ge_21_5 hpR
  gcongr

/-- LEAF. Page 371, (6.1). Upper bound for gapAt p in the small p case. -/
theorem small_p_gap_bound (hY : YoungPotler) {p x : ℕ} (hp : p.Prime)
    (hsmall : nextPrime p ≤ 7263 * 10 ^ 10) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * Real.pi) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by linarith)
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hLx := log_ge_21_5 hxR
  have h778 := hY p hp hsmall
  have : (gapAt p : ℝ) ≤ 778 := by exact_mod_cast h778
  have hsx : (47958 : ℝ) ≤ √(x : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul hsx (pow_le_pow_left₀ (by norm_num) hLx 2) (by norm_num)
    (Real.sqrt_nonneg _)]

/-- LEAF. Page 371, paragraph 4. Combining large p and small p cases.
 CONDITIONAL ON Schoenfeld61 and YoungPotler. -/
theorem gap_bound_combined (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : YoungPotler) {p x : ℕ}
    (hp : p.Prime) (hpx : p ≤ x) (hx : 23 * 10 ^ 8 ≤ x) :
    (gapAt p : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * Real.pi) := by
  have hxR : (23 * 10 ^ 8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx := log_ge_21_5 hxR
  rcases Nat.lt_or_ge (7263 * 10 ^ 10) (nextPrime p) with hbig | hsmall
  · have h2p := nextPrime_le_two_mul (p := p) hp.one_lt.le
    have hp13 : 23 * 10 ^ 8 ≤ p := by omega
    have hpR : (23 * 10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp13
    exact large_p_gap_bound hS hp (by linarith) hpR hpx
  · exact small_p_gap_bound hY hp hsmall hx

/-- LEAF. Page 371, (6.1). Upper bound for lam x using the gap bound.
 CONDITIONAL ON Schoenfeld61 and YoungPotler. -/
theorem lam_bound (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : YoungPotler) (x : ℕ)
    (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < √(x : ℝ) * Real.log x ^ 2 / (4 * Real.pi) := by
  have hx7 : ¬ x ≤ 7 := by omega
  have hne : ((Finset.range (x + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩⟩
  obtain ⟨p, hpmem, hpeq⟩ := Finset.exists_mem_eq_sup _ hne gapAt
  rw [Finset.mem_filter, Finset.mem_range] at hpmem
  have hlam : lam x = gapAt p := by unfold lam; rw [ite_eq_right (fun h => False.elim (hx7 h)), hpeq]
  rw [hlam]
  exact gap_bound_combined hS hY hpmem.2 (by omega) hx

/-- **Kaniecki Lemma 6**, integer `x`, CONDITIONAL ON `Schoenfeld61` and `YoungPotler`:
`λ(x) < (1/4π) √((1 + 1/16597) x) log² x` for `x ≥ 2.3 · 10^9`. -/
theorem lemma6_assembly (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : YoungPotler) (x : ℕ)
    (hx : 23 * 10 ^ 8 ≤ x) :
    (lam x : ℝ) < 1 / (4 * Real.pi) * √((1 + 1 / 16597) * x) * Real.log x ^ 2 := by
  have h_lam := lam_bound hS hY x hx
  have hsq : √(x : ℝ) ≤ √((1 + 1 / 16597) * x) :=
    Real.sqrt_le_sqrt (by
      have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast (by linarith)
      nlinarith)
  calc (lam x : ℝ) < √(x : ℝ) * Real.log (x : ℝ) ^ 2 / (4 * Real.pi) := h_lam
    _ ≤ √((1 + 1 / 16597) * (x : ℝ)) * Real.log (x : ℝ) ^ 2 / (4 * Real.pi) := by
      gcongr
    _ = 1 / (4 * Real.pi) * √((1 + 1 / 16597) * (x : ℝ)) * Real.log (x : ℝ) ^ 2 := by ring

end LeanLab.KanieckiGap
