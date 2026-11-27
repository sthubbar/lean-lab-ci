import LeanLab.HelfgottMajor.SPLIT_vonMangoldt_tsum_eleven_tenths_le

/-!
# Split of `psi_le_rosser_schoenfeld` (`HelfgottMajor/SPLIT_vonMangoldt_tsum_eleven_tenths_le`)

The target is Rosser and Schoenfeld 1962, Theorem 12, display 3.35 on page 71:
`ψ(x) ≤ 1.03883 x` for `x > 0`.  Its proof, page 77 of the paper, has two ranges:

* `x ≤ 2000`: "By comparison with Gram's Table of `ψ(x)`, Theorem 12 was verified for
  `x ≤ 2000`", the maximum of `ψ(x)/x` there being taken at `x = 113`; since `ψ` is constant
  between integers this is a finite check on `N ≤ 2000`, `psi_le_of_le_two_thousand`, proved
  here by a kernel check of `lcm(1, ..., N) · 100000^N ≤ 282590^N` and `2.82590 ≤ e^{1.03883}`;
* `2000 ≤ x`: "one can complete the proof of Theorem 12 by proving that `ψ(x) ≤ 1.03882 x`
  for `2000 ≤ x`", from Theorem 18, Table III and display 4.12, leaf
  `psi_le_of_two_thousand_le`.

The reduction from real `x` to `⌊x⌋` and the assembly are proved here.

AI wrote this Lean code.  Binary Goldbach is OPEN.
-/

namespace LeanLab.HelfgottMajor.SplitPsiRosserSchoenfeld

open Real

/-- `lcmRec n = lcm(1, ..., n)` by the recursion `lcmRec (n + 1) = lcm (lcmRec n) (n + 1)`, a computable form of
Mathlib's `Nat.lcmUpto` for the kernel check below; equal to it by `lcmRec_eq_lcmUpto`.  Helper for
the finite range of Rosser and Schoenfeld 1962 Theorem 12, page 77. -/
def lcmRec : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmRec n) (n + 1)

/-- The kernel checker for `lcm(1, ..., n) · 100000^n ≤ 282590^n`, run with accumulators for
`lcmRec n`, `100000^n` and `282590^n` from `n` on for `k` steps; sound by `chkAux_sound`.  Helper for
the finite range of Rosser and Schoenfeld 1962 Theorem 12, page 77. -/
def chkAux : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, n, l, a, b => decide (l * a ≤ b) &&
      chkAux k (n + 1) (Nat.lcm l (n + 1)) (a * 100000) (b * 282590)

/-- Soundness of the checker `chkAux`, by induction on the number of steps. -/
theorem chkAux_sound : ∀ k n, chkAux k n (lcmRec n) (100000 ^ n) (282590 ^ n) = true →
    ∀ j < k, lcmRec (n + j) * 100000 ^ (n + j) ≤ 282590 ^ (n + j) := by
  intro k
  induction k with
  | zero => intro n _ j hj; omega
  | succ k ih =>
    intro n h j hj
    simp only [chkAux, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases j with _ | j
    · simpa using h.1
    · have h2 : chkAux k (n + 1) (lcmRec (n + 1)) (100000 ^ (n + 1)) (282590 ^ (n + 1)) = true := by
        simpa [lcmRec, pow_succ] using h.2
      have := ih (n + 1) h2 j (by omega)
      rwa [show n + 1 + j = n + (j + 1) by omega] at this

/-- The kernel check up to `n = 2000`, by `decide +kernel`. -/
theorem chk : chkAux 2001 0 1 1 1 = true := by decide +kernel

/-- `lcm(1, ..., N) · 100000^N ≤ 282590^N` for `N ≤ 2000`, tightest at `N = 113`. -/
theorem lcmRec_le (N : ℕ) (hN : N ≤ 2000) : lcmRec N * 100000 ^ N ≤ 282590 ^ N := by
  have := chkAux_sound 2001 0 (by simpa [lcmRec] using chk) N (by omega)
  simpa using this

/-- The recursion `lcmRec` computes Mathlib's `Nat.lcmUpto`. -/
theorem lcmRec_eq_lcmUpto (n : ℕ) : lcmRec n = Nat.lcmUpto n := by
  induction n with
  | zero => simp [lcmRec, Nat.lcmUpto]
  | succ n ih =>
    rw [lcmRec, ih, Nat.lcmUpto, Nat.lcmUpto,
      ← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n + 1), Finset.lcm_insert]
    exact Nat.lcm_comm _ _

/-- `2.82590 ≤ e^{1.03883}`, from `e > 2.7182818283` and the cubic Taylor lower bound for
`e^{0.03883}`; the true value is `2.8259088`. -/
theorem exp_ge : (2.82590 : ℝ) ≤ Real.exp 1.03883 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.sum_le_exp_of_nonneg (x := (0.03883 : ℝ)) (by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h3 : Real.exp 1.03883 = Real.exp 1 * Real.exp 0.03883 := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.03883]

/-- Rosser and Schoenfeld 1962, page 77, the range `x ≤ 2000` of Theorem 12, verified there
against Gram's table, proved here; on integers `N ≤ 2000`, `ψ(N) = log lcm(1, ..., N) ≤ 1.03883 N`, tight at
`N = 113` where `ψ(113)/113 = 1.038826...`.  Proof: Mathlib's `psi_eq_log_lcmUpto`, the kernel
check `lcmRec_le` and `exp_ge`. -/
theorem psi_le_of_le_two_thousand (N : ℕ) (hN : N ≤ 2000) :
    Chebyshev.psi N ≤ 1.03883 * N := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hpos : (0 : ℝ) < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  rw [Real.log_le_iff_le_exp hpos]
  have key : (Nat.lcmUpto N : ℝ) ≤ (2.82590 : ℝ) ^ N := by
    have h := lcmRec_le N hN
    rw [lcmRec_eq_lcmUpto] at h
    have h' : (Nat.lcmUpto N : ℝ) * 100000 ^ N ≤ 282590 ^ N := by exact_mod_cast h
    have hp : (0 : ℝ) < 100000 ^ N := by positivity
    rw [show (2.82590 : ℝ) = 282590 / 100000 by norm_num, div_pow, le_div_iff₀ hp]
    exact h'
  refine key.trans ?_
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) exp_ge N

/-- LEAF: Rosser and Schoenfeld 1962, page 77, the range `2000 ≤ x` of Theorem 12,
`ψ(x) ≤ 1.03882 x`, from their Theorem 18, Table III and display 4.12, resting on the explicit
zeros of `ζ` below height 21 and an explicit zero free region.  HARD. -/
theorem psi_le_of_two_thousand_le (x : ℝ) (hx : 2000 ≤ x) :
    Chebyshev.psi x ≤ 1.03882 * x := by
  sorry

/-- `ψ` is constant between integers: `ψ(x) = ψ(⌊x⌋)`, since Mathlib's `Chebyshev.psi x` is the sum
of `Λ(n)` over `0 < n ≤ ⌊x⌋`. -/
theorem psi_eq_psi_floor (x : ℝ) : Chebyshev.psi x = Chebyshev.psi (⌊x⌋₊ : ℝ) := by
  rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast]

/-- The parent leaf `psi_le_rosser_schoenfeld`, verbatim, from the two range leaves. -/
theorem psi_le_rosser_schoenfeld_split (x : ℝ) (hx : 0 < x) :
    Chebyshev.psi x ≤ 1.03883 * x := by
  by_cases h : 2000 ≤ x
  · have := psi_le_of_two_thousand_le x h
    linarith
  · have h' : x ≤ 2000 := (not_le.mp h).le
    have hfl : ⌊x⌋₊ ≤ 2000 := by
      have := Nat.floor_le_floor h'
      simpa using this
    rw [psi_eq_psi_floor]
    refine (psi_le_of_le_two_thousand _ hfl).trans ?_
    have := Nat.floor_le hx.le
    linarith

end LeanLab.HelfgottMajor.SplitPsiRosserSchoenfeld
