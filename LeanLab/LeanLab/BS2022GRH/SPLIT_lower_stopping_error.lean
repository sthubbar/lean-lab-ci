/-
Split of the OPEN target `lower_stopping_error` of Decomp327c, the signed lower stopping error
of BJS arXiv 2207.09452v6, Lemma 11 display 33 summed over positive even n as in Proposition 13
p. 14, with the constant C2 of Lemma 14 read from journal Table 1 p. 1218.

The target sums, over positive even n, the stopping term T_n of display 28 minus V times the
delay term f_n. The hypotheses z^2 at most D and s at most 4 confine s to the interval from 2
to 4. The proof of Lemma 11 on p. 12 treats even n in two cases: s at least 3, displays 34 to 38
with the factor xi_3, and 2 at most s at most 3, where for each s0 in 2, 2.2, 2.4, 2.6, 2.8 the
same argument gives the factor xi_{s0} on the band from s0 to s0 plus 0.2. This file splits the
target along exactly those cases: one leaf per band, stated once with s0 as a parameter, and one
leaf for s from 3 to 4. Each leaf keeps the full sum over even n and the constant 114, since the
paper bounds tau_n by the maximum over all bands at once, display 31.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp327c

namespace LeanLab.BS2022GRH.Decomp327c
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d Decomp327a
noncomputable section

lemma hS_pos_ge_one {s : ℝ} (hs : 1 ≤ s) : 0 < hS s := by
  have h₁ : 0 < s := by linarith
  unfold hS
  split_ifs <;>
    (try positivity) <;>
    (try {
      constructor <;> positivity
    })

lemma V_pos (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z) :
    0 < ∏ p ∈ (siftingPrimes P z \ Q), (1 - g p) := by
  have h₁ : ∀ p ∈ siftingPrimes P z, p ∈ P := by
    intro p hp
    have h₂ : p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z) := hp
    exact h₂.2.1
  have h₂ : ∀ p ∈ siftingPrimes P z \ Q, 0 < 1 - g p := by
    intro p hp
    have h₃ : p ∈ siftingPrimes P z := hp.1
    have h₄ : p ∉ Q := hp.2
    have h₅ : p ∈ P := h₁ p h₃
    have h₆ : 0 ≤ g p ∧ g p < 1 := hg p h₅
    linarith
  have h₃ : 0 < ∏ p ∈ (siftingPrimes P z \ Q), (1 - g p) := by
    apply Finset.prod_pos
    intro p hp
    exact h₂ p hp
  exact h₃

/-- LEAF: BJS Lemma 11, the case n even and 2 at most s at most 3, p. 12: for s0 in 2, 2.2,
2.4, 2.6, 2.8 and s0 at most s at most s0 plus 0.2, the argument of displays 34 to 38 with
gamma_{s0} of Lemma 9 and kappa_{s0} of Lemma 10 gives the factor xi_{s0}, then summed over
positive even n as in Proposition 13 with C2 of Lemma 14 bounded by 114 in journal Table 1
p. 1218. Class HARD, a real analytic induction step for Codex: the induction of Lemma 11 together
with the numerical bound on the sum of tau_{2n}. Strictly easier than the target: s is confined to
one band of width 0.2. Non-vacuity: z equal to 2 and D equal to 4 gives s equal to 2 in the band
s0 equal to 2, and P empty satisfies every hypothesis. -/
theorem lower_stopping_even_band (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D s0 : ℝ)
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
  have hs_ge_two : (2 : ℝ) ≤ log D / log z := by
    have h₁ : 0 < z := by linarith
    have h₂ : 0 < log z := log_pos (by linarith)
    have h₃ : log (z ^ 2) ≤ log D := log_le_log (pow_pos h₁ 2) hzD
    have h₄ : log (z ^ 2) = 2 * log z := by rw [log_pow] <;> norm_num
    have h₅ : 2 * log z ≤ log D := by linarith
    have h₆ : 2 ≤ log D / log z := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hs_le_four : log D / log z ≤ 4 := by
    have h₁ : s0 ≤ 14 / 5 := by
      rcases hs0 with (rfl | rfl | rfl | rfl | rfl) <;> norm_num
    have h₂ : log D / log z ≤ s0 + 1 / 5 := hhi
    have h₃ : s0 + 1 / 5 ≤ (4 : ℝ) := by linarith
    linarith
  have hS_pos' : 0 < hS (log D / log z) := by
    have h₁ : 1 ≤ log D / log z := by linarith
    exact hS_pos_ge_one h₁
  have hlogz : 0 < log z := by
    have h₁ : 0 < z := by linarith
    exact log_pos h₁
  have hV_pos : 0 < ∏ p ∈ (siftingPrimes P z \ Q), (1 - g p) := by
    exact V_pos P Q g z hP hg hz
  sorry

/-- LEAF: BJS Lemma 11, the case n at least 2 and s at least 3, p. 11 displays 34 to 38 with
gamma_3 of Lemma 9 and kappa_3 of Lemma 10, giving the factor xi_3, here for even n and s from 3
to 4 where h of s equals 3 s^{-1} e^{-s} by display 7, summed over positive even n as in
Proposition 13 with C2 of Lemma 14 bounded by 114 in journal Table 1 p. 1218. Class HARD, a real
analytic induction step for Codex: displays 34 to 38, Lemma 10 for the integral of h, and the
numerical bound on the sum of tau_{2n}. Strictly easier than the target: s is confined to the
interval from 3 to 4. Non-vacuity: z equal to 2 and D equal to 8 gives s equal to 3, and P empty
satisfies every hypothesis. -/
theorem lower_stopping_even_high (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hs3 : 3 ≤ log D / log z) (hs : log D / log z ≤ 4) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 0 < n ∧ n % 2 = 0 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) := by
  have hs_ge_two : (2 : ℝ) ≤ log D / log z := by linarith
  have hs_le_four : log D / log z ≤ 4 := hs
  have hS_pos' : 0 < hS (log D / log z) := by
    have h₁ : 1 ≤ log D / log z := by linarith
    exact hS_pos_ge_one h₁
  have hlogz : 0 < log z := by
    have h₁ : 0 < z := by linarith
    exact log_pos h₁
  have hV_pos : 0 < ∏ p ∈ (siftingPrimes P z \ Q), (1 - g p) := by
    exact V_pos P Q g z hP hg hz
  sorry

/-- The target statement verbatim, from the band LEAF on each of the five bands of width 0.2
covering s from 2 to 3, and the LEAF for s from 3 to 4.
CONDITIONAL ON lower_stopping_even_band and lower_stopping_even_high. -/
theorem lower_stopping_error_split (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
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
  have hzpos : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hslo : (2 : ℝ) ≤ log D / log z := by
    apply (le_div_iff₀ hlz).2
    have hh := log_le_log ((pow_pos hzpos 2)) hzD
    rw [log_pow] at hh
    norm_num at hh
    linarith
  rcases le_total 3 (log D / log z) with h3 | h3
  · exact lower_stopping_even_high P Q g z D hP hg hz hprod h3 hs
  · rcases le_total (log D / log z) (11 / 5) with b1 | b1
    · exact lower_stopping_even_band P Q g z D 2 hP hg hz hprod hzD (Or.inl rfl) hslo
        (by linarith)
    rcases le_total (log D / log z) (12 / 5) with b2 | b2
    · exact lower_stopping_even_band P Q g z D (11 / 5) hP hg hz hprod hzD
        (Or.inr (Or.inl rfl)) b1 (by linarith)
    rcases le_total (log D / log z) (13 / 5) with b3 | b3
    · exact lower_stopping_even_band P Q g z D (12 / 5) hP hg hz hprod hzD
        (Or.inr (Or.inr (Or.inl rfl))) b2 (by linarith)
    rcases le_total (log D / log z) (14 / 5) with b4 | b4
    · exact lower_stopping_even_band P Q g z D (13 / 5) hP hg hz hprod hzD
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) b3 (by linarith)
    · exact lower_stopping_even_band P Q g z D (14 / 5) hP hg hz hprod hzD
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) b4 (by linarith)

end

end LeanLab.BS2022GRH.Decomp327c

#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_even_band
#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_even_high
#print axioms LeanLab.BS2022GRH.Decomp327c.lower_stopping_error_split
