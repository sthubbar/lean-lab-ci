/-
Vaughan 1977 page 101 and Montgomery and Vaughan 1974 page 73 display 1.3.
https://doi.org/10.1515/crll.1977.290.93
https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf
Arithmetic spacing for the individual denominators in the weighted large sieve.
The determinant argument adapts the lab theorem PNTPort.LargeSieve.farey_spaced.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.PNTPort.LargeSieve.Farey

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Decomp1525b2
open LeanLab.PNTPort.LargeSieve

/-- Distinct reduced fractions in the interval from zero exclusive to one inclusive
have circular distance at least the reciprocal product of their denominators. -/
theorem reduced_fraction_spacing {q s a b : ℕ} (hq : 0 < q) (hs : 0 < s)
    (ha : 0 < a) (haq : a ≤ q) (hb : 0 < b) (hbs : b ≤ s)
    (hcop : a.Coprime q) (hcop' : b.Coprime s) (hne : (q, a) ≠ (s, b)) :
    1 / ((q : ℝ) * s) ≤ dist0 ((a : ℝ) / q - (b : ℝ) / s) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let m : ℤ := round ((a : ℝ) / q - (b : ℝ) / s)
  let j : ℤ := (a : ℤ) * s - b * q - m * q * s
  have hx : (a : ℝ) / q - (b : ℝ) / s - m = j / ((q : ℝ) * s) := by
    dsimp [j]
    push_cast
    field_simp
  have hj : j ≠ 0 := by
    intro hj
    rw [hj, Int.cast_zero, zero_div, sub_eq_zero] at hx
    have hlt : |(a : ℝ) / q - (b : ℝ) / s| < 1 := by
      have ha0 : (0 : ℝ) < (a : ℝ) / q := by positivity
      have hb0 : (0 : ℝ) < (b : ℝ) / s := by positivity
      have ha1 : (a : ℝ) / q ≤ 1 := by
        rw [div_le_one hqR]
        exact_mod_cast haq
      have hb1 : (b : ℝ) / s ≤ 1 := by
        rw [div_le_one hsR]
        exact_mod_cast hbs
      rw [abs_lt]
      constructor <;> linarith
    rw [hx] at hlt
    have hm : m = 0 := by
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at hlt
      have h := abs_lt.mp hlt
      omega
    rw [hm, Int.cast_zero, sub_eq_zero, div_eq_div_iff hqR.ne' hsR.ne'] at hx
    have hab : a * s = b * q := by exact_mod_cast hx
    have hqs : q ∣ s := hcop.symm.dvd_of_dvd_mul_left
      (show q ∣ a * s from ⟨b, by rw [hab, mul_comm]⟩)
    have hsq : s ∣ q := hcop'.symm.dvd_of_dvd_mul_left
      (show s ∣ b * q from ⟨a, by rw [← hab, mul_comm]⟩)
    have hqs' := Nat.dvd_antisymm hqs hsq
    subst s
    have hab' : a = b := Nat.eq_of_mul_eq_mul_right hq hab
    exact hne (Prod.ext rfl hab')
  have hd : dist0 ((a : ℝ) / q - (b : ℝ) / s) = |(j : ℝ)| / ((q : ℝ) * s) := by
    unfold dist0
    change |(a : ℝ) / q - (b : ℝ) / s - (m : ℝ)| = _
    rw [hx, abs_div, abs_of_pos (mul_pos hqR hsR)]
  rw [hd]
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    exact_mod_cast Int.one_le_abs hj
  exact div_le_div_of_nonneg_right hj1 (by positivity)

/-- Each Farey row has the individual spacing required for the weighted Hilbert input. -/
theorem farey_individual_spacing (Q : ℝ) (r t : Σ _ : ℕ, ℕ)
    (hr : r ∈ (Icc 1 ⌊Q⌋₊).sigma (fun q => (Icc 1 q).filter (fun a => a.Coprime q)))
    (ht : t ∈ (Icc 1 ⌊Q⌋₊).sigma (fun q => (Icc 1 q).filter (fun a => a.Coprime q)))
    (hne : r ≠ t) :
    1 / ((r.1 : ℝ) * Q) ≤ dist0 ((r.2 : ℝ) / r.1 - (t.2 : ℝ) / t.1) := by
  obtain ⟨hrq, hra⟩ := mem_sigma.mp hr
  obtain ⟨htq, hta⟩ := mem_sigma.mp ht
  obtain ⟨hrange, hrcop⟩ := mem_filter.mp hra
  obtain ⟨htrange, htcop⟩ := mem_filter.mp hta
  have hr0 : 0 < r.1 := by have := (mem_Icc.mp hrq).1; omega
  have ht0 : 0 < t.1 := by have := (mem_Icc.mp htq).1; omega
  have ha0 : 0 < r.2 := by have := (mem_Icc.mp hrange).1; omega
  have hb0 : 0 < t.2 := by have := (mem_Icc.mp htrange).1; omega
  have hfpos : 0 < ⌊Q⌋₊ := lt_of_lt_of_le ht0 (mem_Icc.mp htq).2
  have hQ0 : 0 ≤ Q := le_trans zero_le_one (Nat.floor_pos.mp hfpos)
  have htF : (t.1 : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast (mem_Icc.mp htq).2
  have htQ : (t.1 : ℝ) ≤ Q := htF.trans (Nat.floor_le hQ0)
  have hpair := reduced_fraction_spacing hr0 ht0 ha0 (mem_Icc.mp hrange).2
    hb0 (mem_Icc.mp htrange).2 hrcop htcop
    (show (r.1, r.2) ≠ (t.1, t.2) from fun h => hne (Sigma.ext (congrArg Prod.fst h)
      (heq_of_eq (congrArg Prod.snd h))))
  apply le_trans _ hpair
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left htQ (Nat.cast_nonneg _)

example : 1 / ((1 : ℝ) * 2) ≤ dist0 ((1 : ℝ) / 1 - (1 : ℝ) / 2) := by
  simpa using reduced_fraction_spacing (q := 1) (s := 2) (a := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)

example : 1 / ((1 : ℝ) * 2) ≤ dist0 ((1 : ℝ) / 1 - (1 : ℝ) / 2) := by
  simpa using farey_individual_spacing 2 ⟨1, 1⟩ ⟨2, 1⟩
    (by norm_num [mem_sigma]) (by norm_num [mem_sigma]) (by decide)

end LeanLab.SchnirelmannBounds.Decomp1525b2

#print axioms LeanLab.SchnirelmannBounds.Decomp1525b2.reduced_fraction_spacing

#print axioms LeanLab.SchnirelmannBounds.Decomp1525b2.farey_individual_spacing
