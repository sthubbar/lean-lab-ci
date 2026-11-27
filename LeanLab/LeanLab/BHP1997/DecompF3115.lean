/-
Split of `leaf_upper_sifted_tapered` for FREE-nv-glm2 task3115.

The file isolates the sifted coefficient supply, the reference density, the
character mean value, and the two exact taper identities.  The assembly has
no sorry.  AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312bFeed1122UpperSupply
import LeanLab.BHP1997.Decomp528a

namespace LeanLab.BHP1997.Decomp312bFeed1122
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132 Decomp528a
open scoped BigOperators
open Filter

/-- LEAF: The sifted coefficient step.  It supplies one coefficient family with a
uniform divisor-count bound and eventual domination of the prime weight on the
short window.  This omits the density, mean value, and taper identities. -/
theorem leaf_F3115_c1_supply (h4 : Thm4.Theorem4Paper) (B0 : ℝ) (hB0 : 1 ≤ B0)
    (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ c1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        primeWeight k ≤ section4SiftedFamily c1 x k) := by
  refine ⟨fun _ k => primeWeight k, ⟨1, ?_⟩, ?_⟩
  · intro x k
    by_cases hk : k.Prime
    · have ht : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne_zero⟩
      have hp : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B0 :=
        Real.one_le_rpow ht (by linarith)
      simp only [section4SiftedFamily, primeWeight, if_pos hk, one_mul]
      unfold siftedWeight
      split_ifs
      · simpa using hp
      · simpa using (le_trans zero_le_one hp)
    · simp only [section4SiftedFamily, primeWeight, if_neg hk, zero_mul, abs_zero, one_mul]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · filter_upwards [prime_sifted_eventually_on_left (ε := ε) (by linarith)] with x hx
    intro k hk
    exact le_of_eq (hx k hk).symm

/-- LEAF: The reference-density step for the sifted coefficient family.  It supplies
one density constant in the prescribed narrow interval and the logarithmic
reference-average estimate.  It does not supply the character mean value or any
agreement with a tapered family. -/
theorem leaf_F3115_c1_density (c1 : ℝ → ℕ → ℝ) :
    ∃ u1 : ℝ, 1 ≤ u1 ∧ u1 < 1.0001 ∧
      ReferenceDensity u1 (section4SiftedFamily c1) := by
  sorry

/-- LEAF: The character mean-value step for the tapered sifted coefficient family.
This is the estimate on the wide interval used by the upper construction.  It does
not include the divisor bound, the reference density, or prime domination. -/
theorem leaf_F3115_taper_mean_value (c1 : ℝ → ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    MeanValue41 ε (Decomp528a.tapered (section4SiftedFamily c1)) := by
  sorry

/-- LEAF: The first exact taper identity.  On the short window I the taper equals
one for all sufficiently large x, so the tapered family agrees there with the
sifted family.  This is an identity and supplies no analytic estimate. -/
theorem leaf_F3115_taper_agreement_left (c1 : ℝ → ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
      Decomp528a.tapered (section4SiftedFamily c1) x k = section4SiftedFamily c1 x k := by
  have hε' : ε < 9 / 20 := by linarith
  filter_upwards [Decomp528a.taper_one_left hε'] with x hx k hk
  rw [Decomp528a.tapered, hx x hx k hk, one_mul]

/-- LEAF: The second exact taper identity.  On the reference interval I1 the taper
equals one for all sufficiently large x, so the tapered family agrees there with
the sifted family.  This is an identity and supplies no analytic estimate. -/
theorem leaf_F3115_taper_agreement_reference (c1 : ℝ → ℕ → ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
      Decomp528a.tapered (section4SiftedFamily c1) x k = section4SiftedFamily c1 x k := by
  filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with x hx k hk
  rw [Decomp528a.tapered, Decomp528a.taper_one_reference hx hk, one_mul]

/-- Assembly of the sifted and tapered upper construction.  The statement is copied
from `leaf_upper_sifted_tapered`.  Its proof is the exact conjunction of the five
leaves above and contains no sorry. -/
theorem leaf_upper_sifted_tapered_F3115 (h4 : Thm4.Theorem4Paper) (B0 : ℝ) (hB0 : 1 ≤ B0)
    (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
      1 ≤ u1 ∧ u1 < 1.0001 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u1 (section4SiftedFamily c1) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        primeWeight k ≤ section4SiftedFamily c1 x k) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        b x k = section4SiftedFamily c1 x k) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        b x k = section4SiftedFamily c1 x k) := by
  obtain ⟨c1, hc, hdom⟩ := leaf_F3115_c1_supply h4 B0 hB0 ε hε hε10
  obtain ⟨u1, hu1, hu1', hd⟩ := leaf_F3115_c1_density c1
  have hm := leaf_F3115_taper_mean_value c1 ε hε hε10
  have hI := leaf_F3115_taper_agreement_left c1 ε hε hε10
  have hI1 := leaf_F3115_taper_agreement_reference c1
  obtain ⟨C, hC⟩ := hc
  refine ⟨u1, c1, Decomp528a.tapered (section4SiftedFamily c1), hu1, hu1', hc, ?_, hm, hd, hdom, hI, hI1⟩
  exact ⟨C, fun x k => Decomp528a.tapered_divisor_bound hC x k⟩

end LeanLab.BHP1997.Decomp312bFeed1122
