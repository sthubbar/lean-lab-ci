/-
Saouter 1998, P0018, unit U-0915, run 20261018T0602Z-9546.
Y. Saouter, Checking the odd Goldbach conjecture up to 10^20, Math. Comp. 67 (1998), 863 to 866.
Read in full in Claude in Chrome on 2026-10-18, from the AMS PDF content streams.
The paper's own ladder: primes N = 2^22 * R + 1 with R odd and N ≡ 3 mod 10, certified by a
Brillhart-Lehmer-Selfridge criterion with base 5, steps of 95360 * 2^22 below Sinisalo's 4 * 10^11.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.Saouter1998.Paper

/-! ## Section 4: the shape of the ladder primes -/

/-- The ladder primes as the paper intends them: `N k = 5 * 2^23 * k + 12582913`. -/
def N (k : ℕ) : ℕ := 5 * 2 ^ 23 * k + 12582913

/-- The formula as printed on page 865, `N = 5 * 2^23 * k + 1258213`, one digit 9 missing. -/
def Nprinted (k : ℕ) : ℕ := 5 * 2 ^ 23 * k + 1258213

/-- The intended formula has the shape of Theorem 2: `2^22 * R + 1` with `R = 10 k + 3`. -/
theorem N_form (k : ℕ) : N k = 2 ^ 22 * (10 * k + 3) + 1 := by
  unfold N; ring

theorem N_R_odd (k : ℕ) : (10 * k + 3) % 2 = 1 := by omega

theorem N_mod_ten (k : ℕ) : N k % 10 = 3 := by
  unfold N; omega

/-- Table 1 starts at `k = 3`, which gives the paper's first prime 138412033 = 33 * 2^22 + 1. -/
theorem N_three : N 3 = 138412033 ∧ 138412033 = 33 * 2 ^ 22 + 1 := by
  norm_num [N]

/-- FINDING F-0018 candidate: the printed formula misses the first prime of the paper. -/
theorem printed_three_ne : Nprinted 3 = 127087333 ∧ Nprinted 3 ≠ 138412033 := by
  norm_num [Nprinted]

/-- The printed formula never has the shape `2^22 * R + 1` that Theorem 2 needs. -/
theorem printed_not_form (k : ℕ) : Nprinted k % 2 ^ 22 ≠ 1 := by
  unfold Nprinted; omega

/-- The printed and intended formulas differ by a constant, for every `k`. -/
theorem printed_gap (k : ℕ) : N k = Nprinted k + 11324700 := by
  unfold N Nprinted; omega

/-- The last prime of the sequence, page 865, is the intended formula at `k = 2384185796007`,
so it has the shape of Theorem 2, and it passes `10^20` while staying below `2 * (2^22)^3`. -/
theorem last_prime_form :
    N 2384185796007 = 100000000209366024193 ∧
      100000000209366024193 = 2 ^ 22 * 23841857960073 + 1 ∧ 23841857960073 % 2 = 1 ∧
      10 ^ 20 < 100000000209366024193 ∧ 100000000209366024193 < 2 * (2 ^ 22) ^ 3 := by
  norm_num [N]

/-! ## Sections 2 and 4: the arithmetic of the step -/

/-- Page 865: `95360 * 2^22` is the largest multiple of `10 * 2^22` below `4 * 10^11`. -/
theorem nominal_step :
    95360 * 2 ^ 22 < 4 * 10 ^ 11 ∧ 4 * 10 ^ 11 ≤ (95360 + 10) * 2 ^ 22 ∧ 95360 % 10 = 0 := by
  norm_num

theorem nominal_step_largest (m : ℕ) (h : 10 * 2 ^ 22 * m < 4 * 10 ^ 11) :
    10 * 2 ^ 22 * m ≤ 95360 * 2 ^ 22 := by
  omega

/-- Page 863: at least `250 * 10^6` primes are needed. -/
theorem rung_count : 10 ^ 20 / (4 * 10 ^ 11) = 250 * 10 ^ 6 := by norm_num

/-- Proof of Theorem 1: `2 * (2^22)^3 > 10^20`, the size condition of Lemma 1. -/
theorem cube_bound : (10 : ℕ) ^ 20 < 2 * (2 ^ 22) ^ 3 := by norm_num

/-! ## Section 3, Lemma 2: base 5 is a quadratic non-residue -/

/-- Lemma 2, page 864: for a prime `N ≡ 3 mod 10`, `5^((N-1)/2) ≡ -1 mod N`.
Proved here from Euler's criterion and quadratic reciprocity, as the paper says. -/
theorem lemma2 (p : ℕ) [hp : Fact p.Prime] (h : p % 10 = 3) :
    (5 : ZMod p) ^ ((p - 1) / 2) = -1 := by
  have hp2 : p ≠ 2 := by intro h2; subst h2; norm_num at h
  have h5 : (5 : ℕ) ≠ p := by intro h5; subst h5; norm_num at h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdiv : (p - 1) / 2 = p / 2 := by omega
  have hne : ((5 : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have : (p : ℤ) ∣ 5 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd 5 p).mp h0
      exact this
    have h' : p ∣ 5 := by exact_mod_cast this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h' with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact h5 h1.symm
  have hrec : legendreSym p 5 = legendreSym 5 p := by
    have := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hp2
    exact_mod_cast this
  have hmod : legendreSym 5 (p : ℤ) = legendreSym 5 3 := by
    rw [legendreSym.mod 5 (p : ℤ)]
    congr 1
    omega
  have h53 : legendreSym 5 3 = -1 := by
    norm_num
  have heul := legendreSym.eq_pow p (5 : ℤ)
  rw [hrec, hmod, h53] at heul
  rw [hdiv]
  have : ((5 : ℤ) : ZMod p) = (5 : ZMod p) := by push_cast; rfl
  rw [this] at heul
  rw [← heul]
  push_cast
  rfl

/-! ## The paper's criterion and result, as cited statements, not proved here -/

/-- Theorem 2, page 864, the Brillhart-Lehmer-Selfridge criterion specialised: for
`N = 2^22 R + 1 < 10^20`, `N ≡ 3 mod 10`, `R` odd and `5^((N-1)/2) ≡ -1 mod N`, with
`R = 2 F s + r`, `0 ≤ r < 2 F`, `F = 2^22`, `N` is prime iff `s = 0` or `r^2 - 8 s` is not a
square. Stated as a Prop; the lab has not proved Lemma 1, Theorem 5 of Brillhart, Lehmer and
Selfridge 1975. -/
def Theorem2 : Prop :=
  ∀ R : ℕ, R % 2 = 1 → 2 ^ 22 * R + 1 < 10 ^ 20 → (2 ^ 22 * R + 1) % 10 = 3 →
    (5 : ZMod (2 ^ 22 * R + 1)) ^ ((2 ^ 22 * R) / 2) = -1 →
      ((2 ^ 22 * R + 1).Prime ↔
        (R / (2 * 2 ^ 22) = 0 ∨
          ¬ IsSquare ((R % (2 * 2 ^ 22) : ℤ) ^ 2 - 8 * (R / (2 * 2 ^ 22) : ℤ))))

/-- The main result, abstract: every odd `n` with `7 ≤ n ≤ 10^20` is a sum of three primes.
Cited; the lab's kernel-checked range stops at `10^14`, `ternaryGoldbachUpTo_1e14`. -/
def MainResult : Prop :=
  ∀ n : ℕ, 7 ≤ n → n ≤ 10 ^ 20 → n % 2 = 1 →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r

end LeanLab.Saouter1998.Paper

#print axioms LeanLab.Saouter1998.Paper.lemma2
#print axioms LeanLab.Saouter1998.Paper.printed_three_ne
#print axioms LeanLab.Saouter1998.Paper.printed_not_form
#print axioms LeanLab.Saouter1998.Paper.printed_gap
#print axioms LeanLab.Saouter1998.Paper.N_form
#print axioms LeanLab.Saouter1998.Paper.N_mod_ten
#print axioms LeanLab.Saouter1998.Paper.N_three
#print axioms LeanLab.Saouter1998.Paper.last_prime_form
#print axioms LeanLab.Saouter1998.Paper.nominal_step
#print axioms LeanLab.Saouter1998.Paper.nominal_step_largest
#print axioms LeanLab.Saouter1998.Paper.rung_count
#print axioms LeanLab.Saouter1998.Paper.cube_bound
