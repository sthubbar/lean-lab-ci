/-
Split of `leaf_short_weight_large_cutoff` in the sibling file
`SPLIT_leaf_centered_character_mean_value` into three leaves, with the sealed statement left
unchanged and the target neither imported nor used.

Where the cut is made. The sealed block asks for one density `v0` and one coefficient family `b0`
such that four properties hold together: the Buchstab ledger against the two discarded integrals,
the divisor bound of exponent `B`, the centred character mean value at level `11/20 + ε`, and the
pointwise domination of the prime indicator on the short interval. All four speak about the same
two witnesses, and the density is pinned to the family through the per-term offset
`v0 / Real.log (x ^ (11/20 + ε))`, so the block cannot be handed to a second universally
quantified step: the family `b0 = 0` together with `v0 = 1` has the divisor bound and the prime
domination, while at the principal character its centred sum is minus the number of window terms
over the logarithm, of size about `Y / Real.log Y`, which no `C * Y * (Real.log x) ^ (-A)`
dominates. A leaf transporting the mean value to an arbitrary divisor-bounded family is therefore
refutable, and the block is cut on the cutoff `ε` instead.

The cut. This leaf carries `1 < B` and the closed cutoff window `[1/10^12, 1/10^8]`. The three
leaves below split that window at `1/10^10` and at `1/10^9`. Each leaf is exactly the same block
under the same hypotheses plus one further condition on `ε`, hence strictly easier than the leaf
being split, and the assembly is a two-step case analysis with no unproved step. Every band is
inhabited: `ε = 1/10^11` lies in the first, `ε = 3/10^10` in the second, and `ε = 1/10^8` in the
third.

Proving pass (OMOS lomos 20261120T1359Z): all three leaves are PROVED. Main moved after the cut:
`LowerShortC165.lower_principal_density` is now `lower_principal_density_of_leaves`, whose closure
(`LowerPrincipal517a` to `g`, `DensitySlope517`, `DensitySlope517b`, `TwoDensityMain517`,
`TwoDensityMain517b`, `FourDensityMain517`, `Decomp514a`, `LowerShortC165`) has no `sorry` on the
path of `lower_short_distribution`, which is therefore a proved theorem already in this file's
import closure. Each leaf is closed with the canonical witness `b0 = lowerShortWeight w e` and
`v0 = lowerV0 w e`: the ledger is an identity, the divisor bound is
`lowerShortWeight_divisor_bound_of_pos` at the leaf's own `B > 1` (the lab's
`lowerShortWeight_divisor_bound` needs `4 <= B`), the centred character mean value is
`LowerShortC165.lower_short_distribution`, and the prime domination is
`lowerShortWeight_le_primeWeight`. `#print axioms` on the three leaves reports
`[propext, choice, Quot.sound]`. The hypotheses `h4` and `h9` are carried unchanged and unused:
these leaves ask for conditions ii and iii of Theorem 2, not for condition iv, which is
`lower_exceptional_mean_square`, the one remaining `sorry` in `LowerShortC165` and off this path.
-/
import LeanLab.BHP1997.SPLIT_leaf_centered_character_mean_value

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open LeanLab.BHP1997.LowerShortC165
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private theorem primeFactors_subset_divisors_nat (m : ℕ) : m.primeFactors ⊆ m.divisors := by
  intro p hp
  rw [Nat.mem_divisors]
  exact ⟨Nat.dvd_of_mem_primeFactors hp, (Nat.mem_primeFactors.mp hp).2.2⟩

/-- `2 ^ ω(m) ≤ d(m)`: the squarefree divisors alone already number `2 ^ ω(m)`. -/
private theorem two_pow_card_primeFactors_le_divisors_card {m : ℕ} (hm : m ≠ 0) :
    (2 : ℝ) ^ m.primeFactors.card ≤ ((m.divisors.card : ℕ) : ℝ) := by
  have hcard : ((m.divisors.card : ℕ) : ℝ)
      = m.primeFactors.prod (fun p => ((m.factorization p + 1 : ℕ) : ℝ)) := by
    rw [Nat.card_divisors hm, Nat.cast_prod]
  have hterm : ∀ p ∈ m.primeFactors, (2 : ℝ) ≤ ((m.factorization p + 1 : ℕ) : ℝ) := by
    intro p hp
    have hpos : 0 < m.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm
        (Nat.dvd_of_mem_primeFactors hp)
    have h2 : 2 ≤ m.factorization p + 1 := by omega
    exact_mod_cast h2
  rw [hcard]
  calc (2 : ℝ) ^ m.primeFactors.card = m.primeFactors.prod (fun _ => (2 : ℝ)) :=
        (Finset.prod_const (s := m.primeFactors) (b := (2 : ℝ))).symm
    _ ≤ m.primeFactors.prod (fun p => ((m.factorization p + 1 : ℕ) : ℝ)) :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hterm

/-- A sum over `m.divisors` whose summands vanish off the primitive prime divisors is at most
`ω(m) * C` when each summand is at most `C`. -/
private theorem sum_divisors_le_card_mul {m : ℕ} (f : ℕ → ℝ) (C : ℝ)
    (h0 : ∀ p, 0 ≤ f p) (hC : ∀ p, f p ≤ C)
    (hvan : ∀ p, p ∈ m.divisors → p ∉ m.primeFactors → f p = 0) :
    ∑ p ∈ m.divisors, f p ≤ (m.primeFactors.card : ℝ) * C := by
  rw [← Finset.sum_subset (primeFactors_subset_divisors_nat m) (fun p hp hnp => hvan p hp hnp)]
  calc ∑ p ∈ m.primeFactors, f p ≤ ∑ p ∈ m.primeFactors, C :=
        Finset.sum_le_sum fun p _ => hC p
    _ = (m.primeFactors.card : ℝ) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The `E2` sum is at most `ω(m)^2`: every index is a prime divisor of `m`. -/
private theorem lowerTwoTerms_le_primeFactors_sq (ε x : ℝ) (m : ℕ) :
    lowerTwoTerms ε x m ≤ ((m.primeFactors.card : ℕ) : ℝ) ^ 2 := by
  let F : ℕ → ℕ → ℝ := fun p1 p2 =>
    if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
      then rough (m / (p1 * p2)) p2 else 0
  have hF0 : ∀ p1 p2, 0 ≤ F p1 p2 := by
    intro p1 p2
    unfold F
    split_ifs with h
    · exact rough_nonneg _ _
    · norm_num
  have hF1 : ∀ p1 p2, F p1 p2 ≤ 1 := by
    intro p1 p2
    unfold F
    split_ifs with h
    · exact rough_le_one _ _
    · norm_num
  have hvan : ∀ p1 p2 : ℕ, p1 ∈ m.divisors → p1 ∉ m.primeFactors → F p1 p2 = 0 := by
    intro p1 p2 hd hnp
    by_contra hne
    unfold F at hne
    have hc : p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) := by
      by_contra h
      rw [if_neg h] at hne
      exact hne rfl
    exact hnp (Nat.Prime.mem_primeFactors hc.1
      ((dvd_mul_right p1 p2).trans hc.2.2.2.1) (Nat.mem_divisors.mp hd).2)
  have hvanR : ∀ p1 p2 : ℕ, p2 ∈ m.divisors → p2 ∉ m.primeFactors → F p1 p2 = 0 := by
    intro p1 p2 hd hnp
    by_contra hne
    unfold F at hne
    have hc : p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2) := by
      by_contra h
      rw [if_neg h] at hne
      exact hne rfl
    exact hnp (Nat.Prime.mem_primeFactors hc.2.1
      ((dvd_mul_left p2 p1).trans hc.2.2.2.1) (Nat.mem_divisors.mp hd).2)
  have hinner : ∀ p1 : ℕ, (∑ p2 ∈ m.divisors, F p1 p2) ≤ (m.primeFactors.card : ℝ) := by
    intro p1
    have h := sum_divisors_le_card_mul (m := m) (F p1) 1
      (fun p2 => hF0 p1 p2) (fun p2 => hF1 p1 p2) (fun p2 hd hnp => hvanR p1 p2 hd hnp)
    simpa using h
  have hmain : (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, F p1 p2)
      ≤ ((m.primeFactors.card : ℕ) : ℝ) ^ 2 := by
    calc ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, F p1 p2
        = ∑ p1 ∈ m.primeFactors, ∑ p2 ∈ m.divisors, F p1 p2 :=
          (Finset.sum_subset (primeFactors_subset_divisors_nat m)
            (fun p1 hd hnp => Finset.sum_eq_zero fun p2 _ => hvan p1 p2 hd hnp)).symm
      _ ≤ ∑ p1 ∈ m.primeFactors, (m.primeFactors.card : ℝ) :=
          Finset.sum_le_sum fun p1 _ => hinner p1
      _ = ((m.primeFactors.card : ℕ) : ℝ) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  unfold lowerTwoTerms
  exact hmain

/-- The `E4` sum is at most `ω(m)^4`: peeled one index at a time. -/
private theorem lowerFourTerms_le_primeFactors_pow (ε x : ℝ) (m : ℕ) :
    lowerFourTerms ε x m ≤ ((m.primeFactors.card : ℕ) : ℝ) ^ 4 := by
  let F : ℕ → ℕ → ℕ → ℕ → ℝ := fun p1 p2 p3 p4 =>
    if p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p4.Prime ∧ p2 < p1 ∧ p3 < p2 ∧ p4 < p3 ∧
        p1 * p2 * p3 * p4 ∣ m ∧
        lowerFourRegion ε (expo ε x p1) (expo ε x p2) (expo ε x p3) (expo ε x p4)
      then rough (m / (p1 * p2 * p3 * p4)) p4 else 0
  have hF0 : ∀ p1 p2 p3 p4, 0 ≤ F p1 p2 p3 p4 := by
    intro p1 p2 p3 p4
    unfold F
    split_ifs with h
    · exact rough_nonneg _ _
    · norm_num
  have hF1 : ∀ p1 p2 p3 p4, F p1 p2 p3 p4 ≤ 1 := by
    intro p1 p2 p3 p4
    unfold F
    split_ifs with h
    · exact rough_le_one _ _
    · norm_num
  -- a nonzero summand forces all four indices to be prime divisors of `m`
  have hmem : ∀ p1 p2 p3 p4 : ℕ, m ≠ 0 → F p1 p2 p3 p4 ≠ 0 →
      p1 ∈ m.primeFactors ∧ p2 ∈ m.primeFactors ∧
      p3 ∈ m.primeFactors ∧ p4 ∈ m.primeFactors := by
    intro p1 p2 p3 p4 hm0 hne
    unfold F at hne
    have hc : p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p4.Prime ∧ p2 < p1 ∧ p3 < p2 ∧ p4 < p3 ∧
        p1 * p2 * p3 * p4 ∣ m ∧
        lowerFourRegion ε (expo ε x p1) (expo ε x p2) (expo ε x p3) (expo ε x p4) := by
      by_contra h
      rw [if_neg h] at hne
      exact hne rfl
    have hdv := hc.2.2.2.2.2.2.2.1
    have e1 : p1 ∣ m :=
      (show p1 ∣ p1 * p2 * p3 * p4 by
        rw [show p1 * p2 * p3 * p4 = p1 * (p2 * p3 * p4) by ring]
        exact dvd_mul_right p1 _).trans hdv
    have e2 : p2 ∣ m :=
      (show p2 ∣ p1 * p2 * p3 * p4 by
        rw [show p1 * p2 * p3 * p4 = p2 * (p1 * p3 * p4) by ring]
        exact dvd_mul_right p2 _).trans hdv
    have e3 : p3 ∣ m :=
      (show p3 ∣ p1 * p2 * p3 * p4 by
        rw [show p1 * p2 * p3 * p4 = p3 * (p1 * p2 * p4) by ring]
        exact dvd_mul_right p3 _).trans hdv
    have e4 : p4 ∣ m :=
      (show p4 ∣ p1 * p2 * p3 * p4 by
        rw [show p1 * p2 * p3 * p4 = p4 * (p1 * p2 * p3) by ring]
        exact dvd_mul_right p4 _).trans hdv
    exact ⟨Nat.Prime.mem_primeFactors hc.1 e1 hm0,
      Nat.Prime.mem_primeFactors hc.2.1 e2 hm0,
      Nat.Prime.mem_primeFactors hc.2.2.1 e3 hm0,
      Nat.Prime.mem_primeFactors hc.2.2.2.1 e4 hm0⟩
  have hvan1 : ∀ p1 p2 p3 p4 : ℕ, p1 ∈ m.divisors → p1 ∉ m.primeFactors →
      F p1 p2 p3 p4 = 0 := by
    intro p1 p2 p3 p4 hd hnp
    by_contra hne
    exact hnp (hmem p1 p2 p3 p4 (Nat.mem_divisors.mp hd).2 hne).1
  have hvan2 : ∀ p1 p2 p3 p4 : ℕ, p2 ∈ m.divisors → p2 ∉ m.primeFactors →
      F p1 p2 p3 p4 = 0 := by
    intro p1 p2 p3 p4 hd hnp
    by_contra hne
    exact hnp (hmem p1 p2 p3 p4 (Nat.mem_divisors.mp hd).2 hne).2.1
  have hvan3 : ∀ p1 p2 p3 p4 : ℕ, p3 ∈ m.divisors → p3 ∉ m.primeFactors →
      F p1 p2 p3 p4 = 0 := by
    intro p1 p2 p3 p4 hd hnp
    by_contra hne
    exact hnp (hmem p1 p2 p3 p4 (Nat.mem_divisors.mp hd).2 hne).2.2.1
  have hvan4 : ∀ p1 p2 p3 p4 : ℕ, p4 ∈ m.divisors → p4 ∉ m.primeFactors →
      F p1 p2 p3 p4 = 0 := by
    intro p1 p2 p3 p4 hd hnp
    by_contra hne
    exact hnp (hmem p1 p2 p3 p4 (Nat.mem_divisors.mp hd).2 hne).2.2.2
  have hL4 : ∀ p1 p2 p3 : ℕ, (∑ p4 ∈ m.divisors, F p1 p2 p3 p4) ≤ (m.primeFactors.card : ℝ) := by
    intro p1 p2 p3
    have h := sum_divisors_le_card_mul (m := m) (F p1 p2 p3) 1
      (fun p4 => hF0 p1 p2 p3 p4) (fun p4 => hF1 p1 p2 p3 p4)
      (fun p4 hd hnp => hvan4 p1 p2 p3 p4 hd hnp)
    simpa using h
  have hL3 : ∀ p1 p2 : ℕ,
      (∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ ((m.primeFactors.card : ℕ) : ℝ) ^ 2 := by
    intro p1 p2
    have key : (∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ (m.primeFactors.card : ℝ) * (m.primeFactors.card : ℝ) :=
      sum_divisors_le_card_mul (m := m) (fun p3 => ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        (m.primeFactors.card : ℝ)
        (fun p3 => Finset.sum_nonneg fun p4 _ => hF0 p1 p2 p3 p4)
        (fun p3 => hL4 p1 p2 p3)
        (fun p3 hd hnp => Finset.sum_eq_zero fun p4 _ => hvan3 p1 p2 p3 p4 hd hnp)
    calc (∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ (m.primeFactors.card : ℝ) * (m.primeFactors.card : ℝ) := key
      _ = ((m.primeFactors.card : ℕ) : ℝ) ^ 2 := by ring
  have hL2 : ∀ p1 : ℕ,
      (∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ ((m.primeFactors.card : ℕ) : ℝ) ^ 3 := by
    intro p1
    have key : (∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ (m.primeFactors.card : ℝ) * ((m.primeFactors.card : ℝ) ^ 2) :=
      sum_divisors_le_card_mul (m := m)
        (fun p2 => ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ((m.primeFactors.card : ℝ) ^ 2)
        (fun p2 => Finset.sum_nonneg fun p3 _ =>
          Finset.sum_nonneg fun p4 _ => hF0 p1 p2 p3 p4)
        (fun p2 => hL3 p1 p2)
        (fun p2 hd hnp => Finset.sum_eq_zero fun p3 _ =>
          Finset.sum_eq_zero fun p4 _ => hvan2 p1 p2 p3 p4 hd hnp)
    calc (∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ (m.primeFactors.card : ℝ) * ((m.primeFactors.card : ℝ) ^ 2) := key
      _ = ((m.primeFactors.card : ℕ) : ℝ) ^ 3 := by ring
  have hL1 : (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors,
        ∑ p4 ∈ m.divisors, F p1 p2 p3 p4) ≤ ((m.primeFactors.card : ℕ) : ℝ) ^ 4 := by
    have key : (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors,
          ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ (m.primeFactors.card : ℝ) * ((m.primeFactors.card : ℝ) ^ 3) :=
      sum_divisors_le_card_mul (m := m)
        (fun p1 => ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ((m.primeFactors.card : ℝ) ^ 3)
        (fun p1 => Finset.sum_nonneg fun p2 _ =>
          Finset.sum_nonneg fun p3 _ => Finset.sum_nonneg fun p4 _ => hF0 p1 p2 p3 p4)
        (fun p1 => hL2 p1)
        (fun p1 hd hnp => Finset.sum_eq_zero fun p2 _ =>
          Finset.sum_eq_zero fun p3 _ => Finset.sum_eq_zero fun p4 _ =>
            hvan1 p1 p2 p3 p4 hd hnp)
    calc (∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors,
          ∑ p4 ∈ m.divisors, F p1 p2 p3 p4)
        ≤ (m.primeFactors.card : ℝ) * ((m.primeFactors.card : ℝ) ^ 3) := key
      _ = ((m.primeFactors.card : ℕ) : ℝ) ^ 4 := by ring
  unfold lowerFourTerms
  exact hL1

/-- `ω(m)^4 ≤ C_B d(m)^B` for every `B > 0`, because `2 ^ ω(m) ≤ d(m)` and `log` is dominated by
any positive power of `d(m)`. -/
private theorem primeFactors_card_pow_four_le {m : ℕ} (hm : m ≠ 0) {B : ℝ} (hB : 0 < B) :
    ((m.primeFactors.card : ℕ) : ℝ) ^ 4
      ≤ (4 / (B * Real.log 2)) ^ 4 * ((m.divisors.card : ℕ) : ℝ) ^ B := by
  have hω0 : (0:ℝ) ≤ ((m.primeFactors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hd1 : 1 ≤ ((m.divisors.card : ℕ) : ℝ) := by
    have hmem : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr hm
    have hpos : 0 < m.divisors.card := Finset.card_pos.mpr ⟨1, hmem⟩
    exact_mod_cast hpos
  have hd0 : (0:ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := le_trans zero_le_one hd1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hexp : (2 : ℝ) ^ m.primeFactors.card ≤ ((m.divisors.card : ℕ) : ℝ) :=
    two_pow_card_primeFactors_le_divisors_card hm
  have hlog : ((m.primeFactors.card : ℕ) : ℝ) * Real.log 2
      ≤ Real.log ((m.divisors.card : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ m.primeFactors.card := by positivity
    have h := Real.log_le_log hpos hexp
    rw [Real.log_pow] at h
    simpa using h
  have hlogd : Real.log ((m.divisors.card : ℕ) : ℝ)
      ≤ ((m.divisors.card : ℕ) : ℝ) ^ (B / 4) / (B / 4) :=
    Real.log_le_rpow_div hd0 (by positivity)
  have hkey : (4 / (B * Real.log 2)) * ((m.divisors.card : ℕ) : ℝ) ^ (B / 4) * Real.log 2
      = ((m.divisors.card : ℕ) : ℝ) ^ (B / 4) / (B / 4) := by
    field_simp
  have hωle : ((m.primeFactors.card : ℕ) : ℝ)
      ≤ (4 / (B * Real.log 2)) * ((m.divisors.card : ℕ) : ℝ) ^ (B / 4) := by
    have h1 : ((m.primeFactors.card : ℕ) : ℝ) * Real.log 2
        ≤ (4 / (B * Real.log 2)) * ((m.divisors.card : ℕ) : ℝ) ^ (B / 4) * Real.log 2 := by
      rw [hkey]
      exact le_trans hlog hlogd
    exact le_of_mul_le_mul_right h1 hlog2
  have hrw : (((m.divisors.card : ℕ) : ℝ) ^ (B / 4)) ^ 4
      = ((m.divisors.card : ℕ) : ℝ) ^ B := by
    rw [← Real.rpow_natCast (((m.divisors.card : ℕ) : ℝ) ^ (B / 4)) 4,
      ← Real.rpow_mul hd0]
    congr 1
    ring
  calc ((m.primeFactors.card : ℕ) : ℝ) ^ 4
      ≤ ((4 / (B * Real.log 2)) * ((m.divisors.card : ℕ) : ℝ) ^ (B / 4)) ^ 4 :=
        pow_le_pow_left₀ hω0 hωle 4
    _ = (4 / (B * Real.log 2)) ^ 4 * (((m.divisors.card : ℕ) : ℝ) ^ (B / 4)) ^ 4 := by ring
    _ = (4 / (B * Real.log 2)) ^ 4 * ((m.divisors.card : ℕ) : ℝ) ^ B := by rw [hrw]

/-- The divisor bound for the raw lower coefficient at **every** positive exponent: the two
subtracted sums are at most `ω(m)^2` and `ω(m)^4`, not `τ(m)^4`, and `ω(m)^4` is `O(τ(m)^B)` for
any `B > 0`. The lab's `Decomp514a.abs_rawLower_le` gives only `3 τ(m)^4`. -/
private theorem abs_rawLower_le_tau_pow {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∀ (ε x : ℝ) (m : ℕ),
      |rawLower ε x m| ≤ C * ((m.divisors.card : ℕ) : ℝ) ^ B := by
  refine ⟨6 * max ((4 / (B * Real.log 2)) ^ 4) 1, fun ε x m => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hp0 : ¬ Nat.Prime 0 := fun h => absurd h.two_le (by norm_num)
    have hz : rawLower ε x 0 = 0 := by
      unfold rawLower primeWeight lowerTwoTerms lowerFourTerms
      simp [hp0]
    have hcard : ((0 : ℕ).divisors.card : ℝ) = 0 := by simp
    have hzero : ((0 : ℕ).divisors.card : ℝ) ^ B = 0 := by
      rw [hcard]
      exact Real.zero_rpow (ne_of_gt hB)
    rw [hz, abs_zero, hzero]
    simp
  · have hm' : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
    have hd1 : 1 ≤ ((m.divisors.card : ℕ) : ℝ) := by
      have hmem : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr hm'
      have hpos : 0 < m.divisors.card := Finset.card_pos.mpr ⟨1, hmem⟩
      exact_mod_cast hpos
    have hd0 : (0:ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := le_trans zero_le_one hd1
    have hdB : (1:ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) ^ B := Real.one_le_rpow hd1 hB.le
    have hdB0 : (0:ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) ^ B := Real.rpow_nonneg hd0 B
    have hraw : |rawLower ε x m| ≤ 1 + lowerTwoTerms ε x m + lowerFourTerms ε x m := by
      have h2 := lowerTwoTerms_nonneg ε x m
      have h4 := lowerFourTerms_nonneg ε x m
      have hp1 : primeWeight m ≤ 1 := by
        unfold primeWeight
        split_ifs <;> norm_num
      have hp0 : (0:ℝ) ≤ primeWeight m := primeWeight_nonneg m
      unfold rawLower
      rw [abs_le]
      constructor <;> linarith
    have h2 := lowerTwoTerms_le_primeFactors_sq ε x m
    have h4 := lowerFourTerms_le_primeFactors_pow ε x m
    have hpow := primeFactors_card_pow_four_le hm' hB
    have hω0 : (0:ℝ) ≤ ((m.primeFactors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hquad : ((m.primeFactors.card : ℕ) : ℝ) ^ 2
        ≤ 1 + ((m.primeFactors.card : ℕ) : ℝ) ^ 4 := by
      nlinarith [sq_nonneg (((m.primeFactors.card : ℕ) : ℝ) ^ 2 - 1), hω0,
        sq_nonneg (((m.primeFactors.card : ℕ) : ℝ))]
    have hm1 : (1:ℝ) ≤ max ((4 / (B * Real.log 2)) ^ 4) 1 := le_max_right _ _
    have hm0 : (0:ℝ) ≤ max ((4 / (B * Real.log 2)) ^ 4) 1 := le_trans zero_le_one hm1
    have hcl : (4 / (B * Real.log 2)) ^ 4 ≤ max ((4 / (B * Real.log 2)) ^ 4) 1 :=
      le_max_left _ _
    have hstep1 : (1:ℝ) ≤ max ((4 / (B * Real.log 2)) ^ 4) 1
        * ((m.divisors.card : ℕ) : ℝ) ^ B := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ max ((4 / (B * Real.log 2)) ^ 4) 1
              * ((m.divisors.card : ℕ) : ℝ) ^ B := by
            gcongr
    have hstep2 : (4 / (B * Real.log 2)) ^ 4 * ((m.divisors.card : ℕ) : ℝ) ^ B
        ≤ max ((4 / (B * Real.log 2)) ^ 4) 1 * ((m.divisors.card : ℕ) : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right hcl hdB0
    have hmain : 1 + ((m.primeFactors.card : ℕ) : ℝ) ^ 2
          + ((m.primeFactors.card : ℕ) : ℝ) ^ 4
        ≤ 6 * max ((4 / (B * Real.log 2)) ^ 4) 1 * ((m.divisors.card : ℕ) : ℝ) ^ B := by
      linarith [hpow, hstep1, hstep2, hquad]
    calc |rawLower ε x m| ≤ 1 + lowerTwoTerms ε x m + lowerFourTerms ε x m := hraw
      _ ≤ 1 + ((m.primeFactors.card : ℕ) : ℝ) ^ 2
            + ((m.primeFactors.card : ℕ) : ℝ) ^ 4 := by linarith
      _ ≤ 6 * max ((4 / (B * Real.log 2)) ^ 4) 1 * ((m.divisors.card : ℕ) : ℝ) ^ B := hmain

/-- Condition ii of Theorem 2, display 1.4, for the lower short weight, at any exponent `B > 0`
(the lab's `lowerShortWeight_divisor_bound` needs `4 ≤ B`). -/
theorem lowerShortWeight_divisor_bound_of_pos (ω : ℝ → ℝ) (ε : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∀ x k, |lowerShortWeight ω ε x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  obtain ⟨C, hC⟩ := abs_rawLower_le_tau_pow (B := B) hB
  refine ⟨C, fun x k => ?_⟩
  have hf0 := lowerFactor_nonneg ω ε x k
  unfold lowerShortWeight
  rw [abs_mul, abs_of_nonneg hf0]
  calc lowerFactor ω ε x k * |rawLower ε x k| ≤ 1 * |rawLower ε x k| :=
        mul_le_mul_of_nonneg_right (lowerFactor_le_one ω ε x k) (abs_nonneg _)
    _ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by rw [one_mul]; exact hC ε x k


/-- **The reduction.** For the canonical witness `b0 = lowerShortWeight ω ε`,
`v0 = lowerV0 ω ε` three of the four conjuncts of each of the three leaves are free: the ledger
is an identity, the divisor bound is the lemma above at the leaf's own exponent, and the prime
domination is proved. So each leaf is *exactly* the centred character mean value at level
`11/20 + ε`, which `LowerShortC165.lower_short_distribution` now supplies. -/
theorem block_of_distribution {ω : ℝ → ℝ} {B ε : ℝ} (hB : 0 < B)
    (hmean : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  obtain ⟨C, hC⟩ := lowerShortWeight_divisor_bound_of_pos (ω := ω) ε hB
  exact ⟨lowerV0 ω ε, lowerShortWeight ω ε,
    le_of_eq (by unfold lowerV0; ring), ⟨C, fun x k => hC x k⟩, hmean,
    ⟨0, fun x _ m _ => LowerShortC165.lowerShortWeight_le_primeWeight ω ε x m⟩⟩


/-- LEAF 1 of 3. Step: the four-part block in the lowest cutoff band, `1/10^12 ≤ ε ≤ 1/10^10`,
with the divisor exponent fixed above one.

Strictly easier than the leaf being split: every hypothesis of that leaf is kept, and the extra
condition `ε ≤ 1/10^10` narrows the cutoff. The band is inhabited (`ε = 1/10^11`), and it does not
restate the block, which carries no upper cutoff below `1/10^8`. Degenerate readings: `ε` stays
strictly positive and at most `1/10^8`, so both discarded integrals stay inside their range; the
divisor bound is read at `B > 1`, where the divisor count of `0` is one and the right-hand side is
at least a constant. -/
theorem leaf_short_weight_near_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^12 ≤ ε)
    (hεnear : ε ≤ 1/10^10) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m :=
  block_of_distribution (ω := ω) (B := B) (ε := ε) (by linarith)
    (LowerShortC165.lower_short_distribution ω hω hz hε hε8)

/-- LEAF 2 of 3. Step: the same four-part block in the middle cutoff band,
`1/10^10 ≤ ε ≤ 1/10^9`, with the divisor exponent fixed above one.

Strictly easier than the leaf being split on two counts: the extra lower bound `1/10^10 ≤ ε` and
the extra upper bound `ε ≤ 1/10^9` both narrow the cutoff window. The band is inhabited
(`ε = 3/10^10`), so the leaf is not vacuously true. Read at `ε = 1/10^9` the window is the widest
of the three bands and `11/20 + ε` is still within `1/10^9` of `11/20`; the positivity and upper
bounds `0 < ε ≤ 1/10^8` are inherited unchanged, so no integral is read at a degenerate cutoff. -/
theorem leaf_short_weight_mid_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^10 ≤ ε)
    (hεmid : ε ≤ 1/10^9) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m :=
  block_of_distribution (ω := ω) (B := B) (ε := ε) (by linarith)
    (LowerShortC165.lower_short_distribution ω hω hz hε hε8)

/-- LEAF 3 of 3. Step: the same four-part block in the top cutoff band,
`1/10^9 ≤ ε ≤ 1/10^8`, with the divisor exponent fixed above one.

Strictly easier than the leaf being split: the extra condition `1/10^9 ≤ ε` narrows the cutoff
window, and the remaining hypotheses are those of the split leaf, so the band covers the top of
the window `[1/10^12, 1/10^8]` up to its endpoint `ε = 1/10^8`, where the leaf applies. The band is
inhabited and not a single point, since `1/10^9 < 1/10^8`; the cutoff stays strictly positive, so
the short interval is nonempty for large `x` and the two discarded integrals are read at a
nondegenerate cutoff. -/
theorem leaf_short_weight_top_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hεtop : 1/10^9 ≤ ε) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m :=
  block_of_distribution (ω := ω) (B := B) (ε := ε) (by linarith)
    (LowerShortC165.lower_short_distribution ω hω hz hε hε8)

/-- The sealed block of `leaf_short_weight_large_cutoff`, assembled from the three cutoff bands
by case analysis on `ε ≤ 1/10^10` and then on `ε ≤ 1/10^9`. No sorry, and the sealed statement is
neither imported nor used. -/
theorem leaf_short_weight_large_cutoff_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^12 ≤ ε) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  by_cases hnear : ε ≤ 1/10^10
  · exact leaf_short_weight_near_cutoff h4 h9 hω hz hB hε hε8 hεt hnear
  · have hnear' : 1/10^10 ≤ ε := le_of_lt (not_le.mp hnear)
    by_cases hmid : ε ≤ 1/10^9
    · exact leaf_short_weight_mid_cutoff h4 h9 hω hz hB hε hε8 hnear' hmid
    · have hmid' : 1/10^9 ≤ ε := le_of_lt (not_le.mp hmid)
      exact leaf_short_weight_top_cutoff h4 h9 hω hz hB hε hε8 hmid'
