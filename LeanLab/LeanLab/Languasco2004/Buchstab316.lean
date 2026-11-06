/-
Finite pieces for Jia page 263 display 47 and strict cutoff corrections.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These do not close the OPEN Buchstab input.
-/
import LeanLab.Languasco2004.Decomp316d

namespace LeanLab.Languasco2004.Buchstab316
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 263 display 47: a finite directed star with no loop has at most
one fewer edge than its vertex set. This is the per integer recovery count. -/
theorem star_card_bound (s : Finset ℕ) (r : Finset (ℕ × ℕ)) (hr : r.Nonempty)
    (hmem : ∀ e ∈ r, e.1 ∈ s ∧ e.2 ∈ s ∧ e.1 ≠ e.2)
    (hcenter : ∀ e ∈ r, ∀ f ∈ r, e.2 = f.2) : r.card + 1 ≤ s.card := by
  obtain ⟨e, he⟩ := hr
  have hroot : e.2 ∈ s := (hmem e he).2.1
  have hc : r.card ≤ (s.erase e.2).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro f hf
      obtain ⟨hf1, _, hfne⟩ := hmem f hf
      apply mem_erase.mpr
      refine ⟨?_, hf1⟩
      intro h
      exact hfne (h.trans (hcenter e he f hf))
    · intro f hf g hg hfg
      exact Prod.ext hfg (hcenter f hf g hg)
  have hcard := card_erase_add_one hroot
  omega

/-- Page 263: two surviving prime divisors not dividing n cannot both
serve as the least prime in the recovery term. -/
theorem least_divisor_unique (a n q r : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) (hqa : q ∣ a) (hra : r ∣ a)
    (hsq : ∀ p : ℕ, p.Prime → p < q → ¬ p ∣ n → ¬ p ∣ a)
    (hsr : ∀ p : ℕ, p.Prime → p < r → ¬ p ∣ n → ¬ p ∣ a) : q = r := by
  rcases lt_trichotomy q r with h | h | h
  · exact False.elim (hsr q hq h hqn hqa)
  · exact h
  · exact False.elim (hsq r hr h hrn hra)

/-- Page 263 strict cutoff correction: a finite set of positive multiples
below a real bound M has size at most M divided by the modulus. -/
theorem multiples_count_le (s : Finset ℕ) (d : ℕ) (M : ℝ)
    (hd : 0 < d) (hM : 0 ≤ M)
    (hs : ∀ a ∈ s, 0 < a ∧ (a : ℝ) ≤ M ∧ d ∣ a) : (s.card : ℝ) ≤ M / d := by
  have hsub : s ⊆ (Ioc 0 ⌊M⌋₊).filter (fun a => d ∣ a) := by
    intro a ha
    obtain ⟨ha0, haM, hda⟩ := hs a ha
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨ha0, Nat.le_floor haM⟩, hda⟩
  have hc : s.card ≤ ⌊M⌋₊ / d := by
    simpa only [Nat.Ioc_filter_dvd_card_eq_div] using card_le_card hsub
  calc (s.card : ℝ) ≤ ((⌊M⌋₊ / d : ℕ) : ℝ) := by exact_mod_cast hc
       _ ≤ (⌊M⌋₊ : ℝ) / d := Nat.cast_div_le
       _ ≤ M / d := div_le_div_of_nonneg_right (Nat.floor_le hM) (by positivity)

/-- Pages 263 to 269: a divisor beyond n contributes no sifted integer.
This justifies the finite caps in the supplied source sums. -/
theorem sifted_zero_of_large_divisor (N Y : ℝ) (n d : ℕ) (z : ℝ) (hd : n < d) :
    Decomp279a.sifted N Y n d z = 0 := by
  unfold Decomp279a.sifted
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro a ha h
  obtain ⟨ha0, han⟩ := mem_Icc.mp ha
  have hda := Nat.le_of_dvd (by omega : 0 < a) h.1
  omega

/-- Page 267 display 52: a recovery summand beyond either finite prime cap
is zero. This is independent of all analytic estimates. -/
theorem recovery_summand_zero_of_large_index (N Y : ℝ) (n p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hlarge : n < p ∨ n < q) :
    Decomp279a.sifted N Y n (p * q) q = 0 := by
  apply sifted_zero_of_large_divisor
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  rcases hlarge with h | h <;> nlinarith

#print axioms star_card_bound
#print axioms least_divisor_unique
#print axioms multiples_count_le
#print axioms sifted_zero_of_large_divisor
#print axioms recovery_summand_zero_of_large_index
end
end LeanLab.Languasco2004.Buchstab316
