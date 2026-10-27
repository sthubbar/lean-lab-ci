/-
P0066 Vaughan 1977, On the estimation of Schnirelman's constant, J. reine angew. Math. 290,
93-108, doi 10.1515/crll.1977.290.93. The paper itself was NOT read: the doi fetch failed and
there is no copy in copies/; a UCI line is in NEEDS_COPY.md. Statements are taken from:
* Vaughan, Astérisque 61 (1979) 213-222, p. 217: "C_0 = 27, Vaughan [58]", where C_0 is
  such that every n > 1 is the sum of at most C_0 primes, [58] being this paper.
* Vaughan, Bull. LMS 8 (1976) 245-250, footnote: "This can be reduced further to 27. The
  proof is to appear in J. Reine Angew. Math."
* Riesel-Vaughan 1983, Ark. Mat. 21, p. 45: a lower bound N(x) > x/18 for the count of even
  n ≤ x that are sums of at most two primes gives the theorem "in the usual manner (for
  example as in §6 of [7])", [7] being this paper.
So Section 6 of Vaughan 1977 is the step from a density bound N(x) > x/c to a constant. This
file proves that step for every even c = 2k by Mann's theorem, reusing the lab's
`Schnirelmann.Mann.mann_sum` and Riesel-Vaughan's `NCount` and set `B` by import. The density
bound behind Vaughan's 27 is NOT read from the paper: the bound x/26 is the weakest density of
the form x/(2k) that this step turns into 27, a reconstruction, named `VaughanDensity26`.
UPDATE 2026-10-21, U-6848 CLOUD MANUAL-M1: papers/P0066.pdf, the version of record, has been read;
`VaughanDensity26` is the paper's own statement p. 106, see Vaughan1977Sec6.lean, so the word
reconstruction above is superseded.
AI-written Lean code, Claude, 2026-10-20, run 20261020T2004Z-7678, unit U-1273. Checked only
by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.RieselVaughan1983.Reduction

open Finset
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977
open LeanLab.SchnirelmannConstant LeanLab.Schnirelmann.Mann LeanLab.RieselVaughan1983
open LeanLab.Ramare1995.Section9

/-- The density hypothesis with constant `c`: `N(x) > x / c` for every real `x ≥ 2`, `N` the
count of even `n ≤ x` that are sums of at most two primes, Riesel-Vaughan p. 45. -/
def DensityC (c : ℝ) : Prop := ∀ x : ℝ, 2 ≤ x → x / c < (NCount x : ℝ)

/-- Riesel-Vaughan's (1.1) is `DensityC 18`. -/
theorem density11_iff : Density11 ↔ DensityC 18 := Iff.rfl

/-- The statement credited to Vaughan 1977, Astérisque 61 p. 217: every `n > 1` is a sum of
at most 27 primes. -/
def Statement27 : Prop := ∀ n : ℕ, 1 < n → AtMostPrimes 27 n

/-- The reconstructed analytic input, NOT read from the paper: `N(x) > x/26` for `x ≥ 2`. -/
def VaughanDensity26 : Prop := DensityC 26

/-- A density bound with a smaller constant implies one with a larger constant. -/
theorem DensityC.mono {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') (h : DensityC c) :
    DensityC c' := by
  intro x hx
  have h1 := h x hx
  have hx0 : 0 ≤ x := by linarith
  have : x / c' ≤ x / c := div_le_div_of_nonneg_left hx0 hc hcc
  linarith

/-- `DensityC (2k)` gives `σ(B) ≥ 1/k`, `B = {m : 2m is at most two primes}`. -/
lemma density_B_of (k : ℕ) (hk : 0 < k) (h : DensityC (2 * k)) :
    (1 / k : ℝ) ≤ schnirelmannDensity B := by
  apply le_density_of
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (2 : ℝ) ≤ 2 * n := by linarith
  have h1 := h _ hx
  have h2 : (NCount (2 * n : ℝ) : ℝ) ≤ cnt B n := by exact_mod_cast ncount_le_cnt n
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have e : (2 * n : ℝ) / (2 * k) = 1 / k * n := by field_simp
  rw [e] at h1
  linarith

/-- **Section 6 step, even form.** If `N(x) > x/(2k)` for all `x ≥ 2`, every even natural
number is a sum of at most `2k` primes: `k` copies of `B` have density sum at least 1, so by
Mann's theorem they cover ℕ. -/
theorem even_of_densityC (k : ℕ) (hk : 0 < k) (h : DensityC (2 * k)) :
    ∀ n : ℕ, Even n → AtMostPrimes (2 * k) n := by
  intro n hn
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact AtMostPrimes.zero.mono (by omega)
  have hM := mann_sum (fun _ => B) j
  have hd := density_B_of (j + 1) hk h
  have hsum : (1 : ℝ) ≤ ∑ i ∈ range (j + 1), schnirelmannDensity ((fun _ => B) i) := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hd hj.le
    rw [mul_one_div_cancel hj.ne'] at this
    exact this
  rw [min_eq_left hsum] at hM
  have h1 : schnirelmannDensity (SumSet (fun _ => B) (j + 1)) = 1 :=
    le_antisymm schnirelmannDensity_le_one hM
  rw [schnirelmannDensity_eq_one_iff] at h1
  have hmem : m ∈ SumSet (fun _ => B) (j + 1) := h1 (by simp; omega)
  obtain ⟨f, hf, hs⟩ := hmem
  have := atMost_of_sum f (j + 1) hf
  rw [hs] at this
  simpa [two_mul] using this

/-- **Section 6 step, general form.** If `N(x) > x/(2k)` for all `x ≥ 2`, every `n > 1` is a
sum of at most `2k + 1` primes: an odd `n` is `3 + (n - 3)`. -/
theorem atMost_of_densityC (k : ℕ) (hk : 0 < k) (h : DensityC (2 * k)) :
    ∀ n : ℕ, 1 < n → AtMostPrimes (2 * k + 1) n := by
  intro n hn
  have hE := even_of_densityC k hk h
  rcases Nat.even_or_odd n with he | ho
  · exact (hE n he).mono (by omega)
  · have h3 : 3 ≤ n := by obtain ⟨t, rfl⟩ := ho; omega
    have he : Even (n - 3) := by obtain ⟨t, rfl⟩ := ho; exact ⟨t - 1, by omega⟩
    have := (AtMostPrimes.prime Nat.prime_three).add (hE (n - 3) he)
    rw [show 3 + (n - 3) = n by omega] at this
    exact this.mono (by omega)

/-- Explicit arithmetic: any real density constant `c > 0` gives the constant
`2 ⌈c/2⌉ + 1`. -/
theorem atMost_of_density_real (c : ℝ) (hc : 0 < c) (h : DensityC c) :
    ∀ n : ℕ, 1 < n → AtMostPrimes (2 * ⌈c / 2⌉₊ + 1) n := by
  have hk : 0 < ⌈c / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
  apply atMost_of_densityC _ hk
  apply DensityC.mono hc _ h
  have := Nat.le_ceil (c / 2)
  linarith

/-- **Vaughan's 27, CONDITIONAL ON `VaughanDensity26`**, the reconstructed input
`N(x) > x/26`. -/
theorem statement27_of_density26 (h : VaughanDensity26) : Statement27 := by
  have := atMost_of_densityC 13 (by norm_num) (by unfold VaughanDensity26 at h; norm_num; exact h)
  unfold Statement27; simpa using this

/-- Even form under the same input: every even number is at most 26 primes. -/
theorem even26_of_density26 (h : VaughanDensity26) :
    ∀ n : ℕ, Even n → AtMostPrimes 26 n := by
  have := even_of_densityC 13 (by norm_num) (by unfold VaughanDensity26 at h; norm_num; exact h)
  simpa using this

/-- Riesel-Vaughan's (1.1), `x/18`, implies the reconstructed Vaughan input `x/26`. -/
theorem density26_of_density11 (h : Density11) : VaughanDensity26 :=
  DensityC.mono (c := 18) (by norm_num) (by norm_num) h

/-- Consistency: the general step at `k = 9` recovers Riesel-Vaughan's Corollary 19 from
(1.1), the lab's `corollary19_of_density11`, independently. -/
theorem corollary19_of_density11' (h : Density11) : Corollary19 := by
  have := atMost_of_densityC 9 (by norm_num) (by norm_num; exact h)
  unfold Corollary19; simpa using this

/-! ### Vacuity tests -/

/-- `N(2) ≥ 1`: the prime 2 counts, so `x = 2` does not falsify `DensityC 26`. -/
lemma ncount_two_pos : 1 ≤ NCount 2 := by
  unfold NCount
  have hf : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hf, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨2, by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨by norm_num, even_two, (AtMostPrimes.prime Nat.prime_two).mono (by norm_num)⟩⟩

/-- `N(2) ≤ 1`: only `n = 2` is even in `[1, 2]`. -/
lemma ncount_two_le : NCount 2 ≤ 1 := by
  unfold NCount
  have hf : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hf]
  calc #{n ∈ Icc 1 2 | Even n ∧ AtMostPrimes 2 n} ≤ #({2} : Finset ℕ) := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨h1, h2⟩, ⟨t, ht⟩, _⟩ := hn
        rw [Finset.mem_singleton]; omega
    _ = 1 := by simp

/-- The hypothesis is not trivially true: `DensityC c` forces `c > 2`. -/
theorem densityC_gt_two {c : ℝ} (hc : 0 < c) (h : DensityC c) : 2 < c := by
  have h1 := h 2 le_rfl
  have h2 : (NCount 2 : ℝ) ≤ 1 := by exact_mod_cast ncount_two_le
  have : 2 / c < 1 := lt_of_lt_of_le h1 h2
  rwa [div_lt_one hc] at this

/-- The hypothesis is not refuted at its first point: `2/26 < N(2)`. -/
example : (2 : ℝ) / 26 < NCount 2 := by
  have : (1 : ℝ) ≤ NCount 2 := by exact_mod_cast ncount_two_pos
  linarith

end LeanLab.SchnirelmannBounds.Vaughan1977
