/-
Split of the two OPEN leaves `lower_stopping_even_band` and `lower_stopping_even_high` of
SPLIT_lower_stopping_error.lean, the summed signed lower stopping error of BJS arXiv 2207.09452v6,
Lemma 11 display 33 over positive even n as in Proposition 13 p. 14, with C2 of Lemma 14 at most
114 for epsilon one over 8349, journal Table 1 p. 1218.

The paper proof has two separate parts. First, Lemma 11 bounds each T_n separately by
V of z times f_n of s plus epsilon tau_n e^2 h of s, with tau_n of display 31. Second,
Proposition 13 sums these bounds over even n, and Lemma 14 with Table 1 bounds the sum of the
tau_{2n} by 114. This file separates exactly those parts. It names tau_n, so it adds the
coefficients of display 31 as a definition, parametric in the numbers c_n of display 18, and the
Table 2 values of c_n with the Lemma 8 value 0.9607 beyond n equal to 500.

Leaves, each a cited piece of the paper:
- `lower_stopping_even_step`, Lemma 11 at one even n, for any c satisfying display 18.
- `bjsTable2C_display18`, Lemma 7 with Table 2 and Lemma 8: display 18 holds with those c_n.
- `bjsTau_even_sum_le`, Lemma 14 with Table 1: the partial sums of tau_{2n} are at most 114.
The summation of Proposition 13 is PROVED here as `lower_stopping_even_sum_of_step`. From the
three leaves follow `lower_stopping_even_band_split` verbatim, `lower_stopping_even_high` under the
extra hypothesis 0 < D, and the parent target `lower_stopping_error` verbatim.

No existing statement is changed, no sorry is added to an existing file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_lower_stopping_error

namespace LeanLab.BS2022GRH.Decomp327c
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d Decomp327a
noncomputable section

/-- The numbers c_n of BJS display 18: c_1 equal to 1 p. 6, c_n from Table 2 of Lemma 7 p. 7 for
2 at most n at most 500, and the Lemma 8 value 0.9607 of Nathanson Lemma 9.7 for n above 500.
The value at n equal to 0 is never used. Needed to name tau_n of display 31. -/
def bjsTable2C (n : ℕ) : ℝ :=
  if n ≤ 1 then 1 else if n = 2 then 33 / 100 else if n = 3 then 39 / 100
  else if n = 4 then 45 / 100 else if n = 5 then 51 / 100 else if n = 6 then 54 / 100
  else if n = 7 then 57 / 100 else if n = 8 then 58 / 100 else if n ≤ 10 then 61 / 100
  else if n ≤ 12 then 63 / 100 else if n = 13 then 64 / 100 else if n = 14 then 65 / 100
  else if n ≤ 18 then 66 / 100 else if n ≤ 20 then 67 / 100 else if n ≤ 26 then 68 / 100
  else if n ≤ 34 then 69 / 100 else if n ≤ 46 then 7 / 10 else if n ≤ 82 then 71 / 100
  else if n ≤ 345 then 72 / 100 else if n ≤ 500 then 73 / 100 else 9607 / 10000

/-- The factor xi_{s0} of BJS display 31 p. 10, written with kappa equal to kappa_{s0} of
Lemma 10, gamma equal to gamma_{s0} of Lemma 9, a equal to c_{n-1}^{n-2}, b equal to
c_n^{n-1} and t equal to tau_{n-1}. -/
def bjsXi (ε κ γ a b t : ℝ) : ℝ :=
  κ + (γ + κ) * ε + 2 * γ * (a / t) + 2 * (b / t)

/-- The coefficients tau_n of BJS display 31 p. 10, for a choice c of the numbers c_n of
display 18: tau_1 equal to 3; for even n, tau_{n-1} times the maximum of xi_{s0} over s0 in 2,
2.2, 2.4, 2.6, 2.8, 3, with gamma_{s0} equal to e^{s0-2} and gamma_3 equal to 4e/3 by Lemma 9 and
kappa_{s0} by Lemma 10; for odd n, tau_{n-1} times the maximum of xi_3 and xi tilde, with
kappa tilde equal to 0.9214 by Lemma 10 display 26. Index n plus 2 below is the paper's n, so
c_{n-1}^{n-2} is `c (n + 1) ^ n` and c_n^{n-1} is `c (n + 2) ^ (n + 1)`. -/
def bjsTau (ε : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 3
  | n + 2 =>
    let t := bjsTau ε c (n + 1)
    let a := c (n + 1) ^ n
    let b := c (n + 2) ^ (n + 1)
    if (n + 2) % 2 = 0 then
      t * max (bjsXi ε (9607 / 10000) 1 a b t)
        (max (bjsXi ε (9557 / 10000) (exp (1 / 5)) a b t)
          (max (bjsXi ε (9457 / 10000) (exp (2 / 5)) a b t)
            (max (bjsXi ε (9261 / 10000) (exp (3 / 5)) a b t)
              (max (bjsXi ε (8914 / 10000) (exp (4 / 5)) a b t)
                (bjsXi ε (8349 / 10000) (4 * exp 1 / 3) a b t)))))
    else
      t * max (bjsXi ε (8349 / 10000) (4 * exp 1 / 3) a b t)
        ((9214 / 10000) + (5 + 4 * ε) * ε + 6 * (1 + ε) * (a / t) + 2 * (2 + ε) * (b / t))

/-- LEAF: BJS Lemma 11 p. 10 at a single even n at least 2, display 33 with h_n of display 32:
T_n of display 28 is at most V of z times f_n of s plus epsilon tau_n e^2 h of s, for every
choice of c_n satisfying display 18, here with K equal to 1 plus epsilon in display 29 and s from
2 to 4. The proof is the induction of Lemma 11 on n, odd and even, via Nathanson Lemmas 9.3 and
9.8, displays 34 to 38 for s at least 3, the bands s0 to s0 plus 0.2 for s0 in 2, 2.2, 2.4, 2.6,
2.8, display 39 for odd n, and Lemmas 9 and 10. Class HARD, a real analytic induction for Codex.
Strictly smaller than the input leaves: one n, no summation, no numerics on tau_n. -/
theorem lower_stopping_even_step (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (c : ℕ → ℝ)
    (hc : ∀ m : ℕ, 1 ≤ m → ∀ s : ℝ, (m % 2 = 1 ∧ 1 ≤ s) ∨ (m % 2 = 0 ∧ 2 ≤ s) →
      delayTerm m s ≤ 2 * exp 2 * c m ^ (m - 1) * hS s)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4)
    (n : ℕ) (hn : 0 < n) (hne : n % 2 = 0) :
    stoppingTerm (siftingPrimes P z \ Q) D g n -
        (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * bjsTau (1 / 8349) c n * exp 2 * hS (log D / log z)) := by
  sorry

/-- LEAF: BJS Lemma 7 p. 7 with Table 2 for 2 at most n at most 500, c_1 equal to 1 p. 6, and
Lemma 8, Nathanson Lemma 9.7, for n above 500: display 18 holds with `bjsTable2C`. Class HARD:
the Riemann sum computation of Section 2.2 display 21 for n up to 500, and Nathanson's analytic
Lemma 9.7. -/
theorem bjsTable2C_display18 :
    ∀ m : ℕ, 1 ≤ m → ∀ s : ℝ, (m % 2 = 1 ∧ 1 ≤ s) ∨ (m % 2 = 0 ∧ 2 ≤ s) →
      delayTerm m s ≤ 2 * exp 2 * bjsTable2C m ^ (m - 1) * hS s := by
  sorry

/-- LEAF: BJS Lemma 14 p. 15 display 44 with journal Table 1 p. 1218 at epsilon one over 8349:
every partial sum of tau_{2n} over positive even indices is at most C2 of epsilon, at most 114,
with tau_n from display 31 and c_n from Table 2 and Lemma 8. Class MEDIUM: an exact rational
iteration of display 31 over the first 500 terms plus the geometric tail bound of Lemma 12
display 40 and Lemma 14. -/
theorem bjsTau_even_sum_le (N : ℕ) :
    (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then bjsTau (1 / 8349) bjsTable2C n else 0) ≤ 114 := by
  sorry

/-- The summation of BJS Proposition 13 p. 14 for the even n: the per n bound of Lemma 11 at
every positive even n, with coefficients whose partial sums are at most 114, gives the summed
lower stopping error. PROVED, no LEAF. -/
theorem lower_stopping_even_sum_of_step (S : Finset ℕ) (D : ℝ) (g : ℕ → ℝ) (s V : ℝ)
    (τ : ℕ → ℝ) (N : ℕ) (hV : 0 ≤ V)
    (hstep : ∀ n, 0 < n → n % 2 = 0 →
      stoppingTerm S D g n - V * delayTerm n s ≤ V * ((1 / 8349 : ℝ) * τ n * exp 2 * hS s))
    (hsum : (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then τ n else 0) ≤ 114) :
    (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then stoppingTerm S D g n - V * delayTerm n s
      else 0) ≤ V * ((1 / 8349 : ℝ) * 114 * exp 2 * hS s) := by
  have hh : 0 ≤ hS s := by
    unfold hS
    split_ifs with h1 h2
    · positivity
    · positivity
    · have : 0 < s := by linarith
      positivity
  have hk : 0 ≤ V * ((1 / 8349 : ℝ) * exp 2 * hS s) :=
    mul_nonneg hV (mul_nonneg (by positivity) hh)
  calc (∑ n ∈ range N, if 0 < n ∧ n % 2 = 0 then stoppingTerm S D g n - V * delayTerm n s
          else 0)
      ≤ ∑ n ∈ range N, (V * ((1 / 8349 : ℝ) * exp 2 * hS s)) *
          (if 0 < n ∧ n % 2 = 0 then τ n else 0) := by
        apply sum_le_sum
        intro n _
        split_ifs with h
        · have := hstep n h.1 h.2
          linarith [show V * ((1 / 8349 : ℝ) * τ n * exp 2 * hS s) =
            V * ((1 / 8349 : ℝ) * exp 2 * hS s) * τ n by ring]
        · simp
    _ = (V * ((1 / 8349 : ℝ) * exp 2 * hS s)) *
          ∑ n ∈ range N, (if 0 < n ∧ n % 2 = 0 then τ n else 0) := by
        rw [mul_sum]
    _ ≤ (V * ((1 / 8349 : ℝ) * exp 2 * hS s)) * 114 := mul_le_mul_of_nonneg_left hsum hk
    _ = V * ((1 / 8349 : ℝ) * 114 * exp 2 * hS s) := by ring

/-- The summed bound for s from 2 to 4, from the three LEAFs of this file.
CONDITIONAL ON lower_stopping_even_step, bjsTable2C_display18 and bjsTau_even_sum_le. -/
theorem lower_stopping_even_summed (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 0 < n ∧ n % 2 = 0 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) := by
  have hV : 0 ≤ ∏ p ∈ siftingPrimes P z \ Q, (1 - g p) := by
    apply prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hg p (mem_filter.mp (mem_sdiff.mp hp).1).2.1).2.le
  exact lower_stopping_even_sum_of_step _ D g _ _ (bjsTau (1 / 8349) bjsTable2C) _ hV
    (fun n hn hne => lower_stopping_even_step P Q g z D bjsTable2C bjsTable2C_display18
      hP hg hz hprod hzD hs n hn hne)
    (bjsTau_even_sum_le _)

/-- `lower_stopping_even_band` verbatim from the LEAFs of this file.
CONDITIONAL ON lower_stopping_even_step, bjsTable2C_display18 and bjsTau_even_sum_le. -/
theorem lower_stopping_even_band_split (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D s0 : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D)
    (hs0 : s0 = 2 ∨ s0 = 11 / 5 ∨ s0 = 12 / 5 ∨ s0 = 13 / 5 ∨ s0 = 14 / 5)
    (hlo : s0 ≤ log D / log z) (hhi : log D / log z ≤ s0 + 1 / 5) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 0 < n ∧ n % 2 = 0 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) := by
  have h4 : log D / log z ≤ 4 := by
    rcases hs0 with h | h | h | h | h <;> rw [h] at hhi <;> linarith
  exact lower_stopping_even_summed P Q g z D hP hg hz hprod hzD h4

/-- `lower_stopping_even_high` with the extra hypothesis 0 < D of BJS Lemma 11, from the LEAFs of
this file. The leaf itself drops the hypothesis z^2 at most D of its parent, and since Real.log is
even it then also covers D at most minus z^3, outside Lemma 11; see the QUESTION in the notes.
CONDITIONAL ON lower_stopping_even_step, bjsTable2C_display18 and bjsTau_even_sum_le. -/
theorem lower_stopping_even_high_pos_split (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hDpos : 0 < D) (hs3 : 3 ≤ log D / log z) (hs : log D / log z ≤ 4) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 0 < n ∧ n % 2 = 0 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) := by
  have hzpos : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hlD : 3 * log z ≤ log D := (le_div_iff₀ hlz).1 hs3
  have hzD : z ^ 2 ≤ D := by
    have hle : log (z ^ 2) ≤ log D := by rw [log_pow]; push_cast; linarith
    exact (log_le_log_iff (by positivity) hDpos).1 hle
  exact lower_stopping_even_summed P Q g z D hP hg hz hprod hzD hs

/-- The OPEN target `lower_stopping_error` of Decomp327c verbatim, directly from the three LEAFs
of this file, bypassing the band and high leaves.
CONDITIONAL ON lower_stopping_even_step, bjsTable2C_display18 and bjsTau_even_sum_le. -/
theorem lower_stopping_error_split2 (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 0 < n ∧ n % 2 = 0 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) :=
  lower_stopping_even_summed P Q g z D hP hg hz hprod hzD hs

end

end LeanLab.BS2022GRH.Decomp327c

#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_even_sum_of_step
#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_even_summed
#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_even_band_split
#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_even_high_pos_split
#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_error_split2
