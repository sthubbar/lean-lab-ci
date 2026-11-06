import LeanLab.AlmostPrimes.CampbellCount
import LeanLab.AlmostPrimes.CampbellLemma43

/-!
AI wrote the Lean code. Goldbach is open.
Campbell 2026 v1, https://arxiv.org/abs/2608.09488v1.
Printed page 4, equations 3.2 and 3.3, and printed page 10, Lemma 4.3.
The existing residue count proof supplies the auxiliary remainder bound.
This file recovers the printed factor 19/6 for the pre-sieved remainder.
-/

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp416a
open Campbell2026 CampbellCase2X CampbellLemma43

/-- LEAF. Campbell page 4, equation 3.2 and the following three-case display.
The auxiliary remainder at three is minus two thirds when three divides N,
zero when N has residue one, and minus two thirds when N has residue two. -/
theorem rho_three_exact (N : ℕ) (hN : 2 ≤ N) :
    DDMain.rd N {3} = if N % 3 = 0 then -(2 / 3 : ℝ)
      else if N % 3 = 1 then 0 else -(2 / 3 : ℝ) := by
  have hX := Xcount_eq N
  have hc := CampbellCount.Xcount_exact_real N hN
  have hY : DDMain.Xc N = (N : ℝ) - 1 := by
    simp [DDMain.Xc, Nat.cast_sub (by omega : 1 ≤ N)]
  have hg : DDMain.gd N {3} = if N % 3 = 0 then (1 / 3 : ℝ) else 2 / 3 := by
    simp [DDMain.gd, DDLemma21.g, Nat.dvd_iff_mod_eq_zero]
  rw [hY] at hX
  unfold DDMain.rd
  rw [hg, hY]
  split_ifs at * <;> linarith

/-- LEAF. Campbell page 10, Lemma 4.3, the display bounding rho three. -/
theorem rho_three_bound (N : ℕ) (hN : 2 ≤ N) :
    |DDMain.rd N {3}| ≤ (2 / 3 : ℝ) := by
  rw [rho_three_exact N hN]
  split_ifs <;> norm_num

/-- LEAF. Campbell page 10, local factors in the proof that g of d is at most one half.
Every sifting prime other than three has density at most one half. -/
theorem g_le_half (N : ℕ) {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    CampbellCase2.g N p ≤ (1 / 2 : ℝ) := by
  rw [g_eq]
  unfold DDLemma21.g
  split_ifs with h2 hd
  · norm_num
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p)).2
    linarith
  · have hp5 : 5 ≤ p := by
      have hp2 := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    have hp5r : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p)).2
    linarith

/-- LEAF. Campbell page 10, Lemma 4.3.
A nonempty square-free modulus without the prime three has density at most one half. -/
theorem gS_le_half (N : ℕ) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (h3 : 3 ∉ s) (hne : s.Nonempty) : gS N s ≤ (1 / 2 : ℝ) := by
  obtain ⟨p, hp⟩ := hne
  have hsub : ∀ q ∈ s.erase p, q.Prime := fun q hq => hs q (mem_of_mem_erase hq)
  have he := (gS_bounds N hsub).2
  have hp0 := (g_bounds N (hs p hp)).1
  have hp1 := g_le_half N (hs p hp) (by intro h; subst p; exact h3 hp)
  have heq : gS N s = CampbellCase2.g N p * gS N (s.erase p) := by
    unfold gS
    exact (mul_prod_erase s _ hp).symm
  rw [heq]
  exact (mul_le_mul_of_nonneg_left he hp0).trans (by simpa using hp1)

/-- LEAF. Campbell page 10, Lemma 4.3, r one equals zero. -/
theorem rA_empty (N : ℕ) : rA N ∅ = 0 := by
  simp [rA, Ad3, Xcount, gS]

/-- LEAF. Campbell page 10, Lemma 4.3, the displayed remainder estimate.
For every square-free modulus made of sifting primes, absolute r is at most
nineteen sixths times two to the number of its prime divisors. -/
theorem rA_bound_sharp (N : ℕ) (hN : 2 ≤ N) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (h3 : 3 ∉ s) :
    |rA N s| ≤ (19 / 6 : ℝ) * (2 : ℝ) ^ s.card := by
  by_cases he : s = ∅
  · subst s
    rw [rA_empty]
    norm_num
  have hne : s.Nonempty := nonempty_iff_ne_empty.mpr he
  have h1 := DDNathanson.nathansonRd N s hs
  have h2 := DDNathanson.nathansonRd N (insert 3 s) (by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_three
    · exact hs p hp)
  rw [card_insert_of_notMem h3, pow_succ] at h2
  have h3b := rho_three_bound N hN
  have hg0 := (gS_bounds N hs).1
  have hg := gS_le_half N hs h3 hne
  have hprod : |gS N s * DDMain.rd N {3}| ≤ (1 / 3 : ℝ) := by
    rw [abs_mul, abs_of_nonneg hg0]
    have hm := mul_le_mul hg h3b (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at hm ⊢
    linarith
  have hk : (2 : ℝ) ≤ 2 ^ s.card := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s.card := pow_le_pow_right₀ (by norm_num) hne.card_pos
  rw [rA_eq N hs h3]
  have ha := abs_add_le (DDMain.rd N s - DDMain.rd N (insert 3 s))
    (gS N s * DDMain.rd N {3})
  have hb := abs_sub (DDMain.rd N s) (DDMain.rd N (insert 3 s))
  linarith

example : DDMain.rd 3 {3} = -(2 / 3 : ℝ) := by
  rw [rho_three_exact 3 (by decide)]
  norm_num

example : |rA 3 {2}| ≤ (19 / 6 : ℝ) * 2 ^ ({2} : Finset ℕ).card :=
  rA_bound_sharp 3 (by decide) (by simp [Nat.prime_two]) (by simp)

end LeanLab.AlmostPrimes.Decomp416a

#print axioms LeanLab.AlmostPrimes.Decomp416a.rho_three_exact
#print axioms LeanLab.AlmostPrimes.Decomp416a.rho_three_bound
#print axioms LeanLab.AlmostPrimes.Decomp416a.g_le_half
#print axioms LeanLab.AlmostPrimes.Decomp416a.gS_le_half
#print axioms LeanLab.AlmostPrimes.Decomp416a.rA_empty
#print axioms LeanLab.AlmostPrimes.Decomp416a.rA_bound_sharp
