/-
P0069 Baker, Harman and Pintz 1997, Section 5, pages 50 to 52. The lower short weight b0.

This file builds the paper's coefficient b0 explicitly and splits
`DecompC165d.lower_short_weight_analytic` along the paper's own proof.

* Display 5.15 on page 50 and the text after 5.16 on page 51: b0 is the prime indicator minus
  the sum over p1 p2 n3 with exponent pair in E2, minus the sum over p1 p2 p3 p4 n5 with
  exponent quadruple in E4. The regions are the lab's `lowerTwoDiscarded` and the support of
  `lowerFourDeletedIntegrand`, the conservative E4, so the subtracted sums and the two integrals
  in v0 use one and the same region.
* Pages 51 and 52 and the U-1624 audit in `Audit1624`: the raw coefficient has density
  `V(s) / log Z` at `m = Z ^ s`, not a constant density. Displays 1.8 and 5.17 at a constant
  center hold only up to a fixed log power for the raw weight. Following the U-1624 NEXT line,
  the weight is multiplied by the slowly varying factor `v0 log Z / (log Y * V(s))`, clipped to
  `[0, 1]`, with `Z = 4 Y`. Then the main term is `v0 / log Y`, exactly the center of 1.8.
  The scale `4 Y` in place of U-1624's `2.1 Y` widens the margin for the factor to stay below 1.

PROVED here: the divisor bound, condition ii, for every `B ≥ 4`, the sandwich 1.4 against the
prime indicator, and the identity of the density formula at `s = 1` with the page 51 `v0`.
Burst 7: the principal case of 5.17 is reduced to the cited character free 5.17,
`lower_principal_density`, by the support of b0 on integers with no prime factor below `Z ^ c1`.
The non-principal case is reduced by linearity of 5.15 to the cited Siegel-Walfisz input for
each of its three terms, `lower_nonprincipal_terms`. Both inputs are CITED-LEFT leaves.
OPEN here: display 1.9 through Lemma 29 and 5.18 to 5.23.
These three leaves are about this one explicit family, not about an arbitrary family, so the
CODEX refutation `sealed_exceptional_leaf_type_false` of the old general transfer does not apply.

Burst 20261115: the two rough Siegel Walfisz inputs and the factor increment are proved in this
file, the rough inputs from `Rough514.rough_family_character_sum` in `RoughFamily514`, the
increment from Lipschitz bounds near one for the E2 and E4 densities.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Abel514
import LeanLab.BHP1997.Prime514
import LeanLab.BHP1997.Rough308
import LeanLab.BHP1997.Decomp308a
import LeanLab.BHP1997.DecompC165dBase312
import LeanLab.BHP1997.RoughFamily514

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-! ### The coefficient -/

/-- Page 3, the parameter Y of J. -/
noncomputable def shortY (ε x : ℝ) : ℝ := x ^ (11 / 20 + ε)

/-- Pages 51 and 52 with the U-1624 normalization: the exponent scale `Z = 4 Y`. -/
noncomputable def scaleZ (ε x : ℝ) : ℝ := 4 * shortY ε x

/-- Pages 50 and 51: the exponent `β` of a prime `p = Z ^ β`. -/
noncomputable def expo (ε x : ℝ) (p : ℕ) : ℝ := Real.log p / Real.log (scaleZ ε x)

/-- Page 50, display 5.15: `ψ(n, p)`, one when `n` has no prime factor below `p`. -/
noncomputable def rough (n p : ℕ) : ℝ :=
  if ∀ r : ℕ, r.Prime → r ∣ n → p ≤ r then 1 else 0

/-- Page 51, the conservative region E4: exactly the support condition of
`lowerFourDeletedIntegrand`. -/
def lowerFourRegion (ε a b c d : ℝ) : Prop :=
  (1+7*(2*(1/16-1/10^5)))/15-ε ≤ d ∧ d ≤ c ∧ c ≤ b ∧ b ≤ a ∧
    a+2*b ≤ 1/2+(1+22*(2*(1/16-1/10^5)))/60-2*ε ∧
    a+b+c ≤ 1/2+(2*(1/16-1/10^5))/4-2*ε ∧ ¬lowerFourCovered ε a b c d

/-- Page 51: the sum over `p1 p2 n3 = m` with `p2 < p1` and `(β1, β2)` in E2, display 5.15,
third sum, restricted to E2. -/
noncomputable def lowerTwoTerms (ε x : ℝ) (m : ℕ) : ℝ :=
  ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors,
    if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
    then rough (m / (p1 * p2)) p2 else 0

/-- Page 51: the sum over `p1 p2 p3 p4 n5 = m` with `p4 < p3 < p2 < p1` and exponents in E4,
reached by decomposing the D part of 5.15 twice. -/
noncomputable def lowerFourTerms (ε x : ℝ) (m : ℕ) : ℝ :=
  ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors,
    if p1.Prime ∧ p2.Prime ∧ p3.Prime ∧ p4.Prime ∧ p2 < p1 ∧ p3 < p2 ∧ p4 < p3 ∧
        p1 * p2 * p3 * p4 ∣ m ∧
        lowerFourRegion ε (expo ε x p1) (expo ε x p2) (expo ε x p3) (expo ε x p4)
    then rough (m / (p1 * p2 * p3 * p4)) p4 else 0

/-- Page 51, "We now obtain b0 from ρ by subtracting": the raw lower coefficient. -/
noncomputable def rawLower (ε x : ℝ) (m : ℕ) : ℝ :=
  primeWeight m - lowerTwoTerms ε x m - lowerFourTerms ε x m

/-! ### The density and the normalizing factor -/

/-- Page 51, the E2 integral with the `1` of `1 - β1 - β2` replaced by `s`: the density of the
E2 sum at `m = Z ^ s`, times `log Z`. -/
noncomputable def lowerTwoDensityAt (ω : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
    if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0

/-- Page 51, the E4 integral with `1` replaced by `s`. -/
noncomputable def lowerFourDensityAt (ω : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ∫ a in lowerFourGridReal 0..lowerFourGridReal 128,
    ∫ b in lowerFourGridReal 0..lowerFourGridReal 128,
      ∫ c in lowerFourGridReal 0..lowerFourGridReal 128,
        ∫ d in lowerFourGridReal 0..lowerFourGridReal 128,
          if lowerFourRegion ε a b c d then
            (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2))
          else 0

/-- Pages 51 and 52, U-1624: the density `V(s)` of the raw coefficient at `m = Z ^ s`, times
`log Z`. The prime term contributes `1 / s`. -/
noncomputable def lowerDensityAt (ω : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  1 / s - lowerTwoDensityAt ω ε s - lowerFourDensityAt ω ε s

/-- Page 51: `v0`, one minus the E2 and E4 integrals. -/
noncomputable def lowerV0 (ω : ℝ → ℝ) (ε : ℝ) : ℝ :=
  1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε

/-- U-1624 normalization of pages 51 and 52: the factor `v0 log Z / (log Y * V(s))`, clipped
to `[0, 1]`. It turns the variable density into the constant center `v0 / log Y` of 1.8. -/
noncomputable def lowerFactor (ω : ℝ → ℝ) (ε x : ℝ) (m : ℕ) : ℝ :=
  max 0 (min 1 (lowerV0 ω ε * Real.log (scaleZ ε x) /
    (Real.log (x ^ (11 / 20 + ε)) * lowerDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)))))

/-- Pages 51 and 52: the lower short weight b0, normalized. -/
noncomputable def lowerShortWeight (ω : ℝ → ℝ) (ε x : ℝ) (m : ℕ) : ℝ :=
  lowerFactor ω ε x m * rawLower ε x m

/-! ### Proved elementary pieces -/

/-- P0069 Baker Harman Pintz 1997, Section 5, page 50, display 5.15: `ψ(n, p) ≥ 0`. -/
theorem rough_nonneg (n p : ℕ) : 0 ≤ rough n p := by
  unfold rough; split_ifs <;> norm_num

/-- P0069 Baker Harman Pintz 1997, Section 5, page 50, display 5.15: `ψ(n, p) ≤ 1`. -/
theorem rough_le_one (n p : ℕ) : rough n p ≤ 1 := by
  unfold rough; split_ifs <;> norm_num

/-- P0069 Baker Harman Pintz 1997, Section 5, page 51: the E2 sum is a sum of values of `ψ`, so it is nonnegative. -/
theorem lowerTwoTerms_nonneg (ε x : ℝ) (m : ℕ) : 0 ≤ lowerTwoTerms ε x m := by
  unfold lowerTwoTerms
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs
  · exact rough_nonneg _ _
  · exact le_rfl

/-- P0069 Baker Harman Pintz 1997, Section 5, page 51: the E4 sum is nonnegative. -/
theorem lowerFourTerms_nonneg (ε x : ℝ) (m : ℕ) : 0 ≤ lowerFourTerms ε x m := by
  unfold lowerFourTerms
  refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
  split_ifs
  · exact rough_nonneg _ _
  · exact le_rfl

/-- P0069 Baker Harman Pintz 1997, page 3, condition ii for the E2 sum: at most `τ(m)^2`. -/
theorem lowerTwoTerms_le (ε x : ℝ) (m : ℕ) :
    lowerTwoTerms ε x m ≤ ((m.divisors.card : ℕ) : ℝ) ^ 2 := by
  unfold lowerTwoTerms
  have h : ∀ p1 ∈ m.divisors, ∀ p2 ∈ m.divisors,
      (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
      then rough (m / (p1 * p2)) p2 else 0) ≤ 1 := by
    intro _ _ _ _
    split_ifs
    · exact rough_le_one _ _
    · norm_num
  calc _ ≤ ∑ _p1 ∈ m.divisors, ∑ _p2 ∈ m.divisors, (1 : ℝ) :=
        Finset.sum_le_sum fun p1 hp1 => Finset.sum_le_sum fun p2 hp2 => h p1 hp1 p2 hp2
    _ = _ := by simp [sq]

/-- P0069 Baker Harman Pintz 1997, page 3, condition ii for the E4 sum: at most `τ(m)^4`. -/
theorem lowerFourTerms_le (ε x : ℝ) (m : ℕ) :
    lowerFourTerms ε x m ≤ ((m.divisors.card : ℕ) : ℝ) ^ 4 := by
  unfold lowerFourTerms
  calc _ ≤ ∑ _p1 ∈ m.divisors, ∑ _p2 ∈ m.divisors, ∑ _p3 ∈ m.divisors,
          ∑ _p4 ∈ m.divisors, (1 : ℝ) := by
        refine Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
          Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => ?_
        split_ifs
        · exact rough_le_one _ _
        · norm_num
    _ = _ := by simp; ring

/-- P0069 Baker Harman Pintz 1997, Section 5, page 51, display 1.4 for the raw weight: b0 is at most the prime indicator, since the two
subtracted sums are nonnegative. -/
theorem rawLower_le_primeWeight (ε x : ℝ) (m : ℕ) : rawLower ε x m ≤ primeWeight m := by
  unfold rawLower
  linarith [lowerTwoTerms_nonneg ε x m, lowerFourTerms_nonneg ε x m]

/-- P0069 Baker Harman Pintz 1997, page 2, display 1.4: `ρ(m) ≥ 0`. -/
theorem primeWeight_nonneg (m : ℕ) : 0 ≤ primeWeight m := by
  unfold primeWeight; split_ifs <;> norm_num

/-- P0069 Baker Harman Pintz 1997, page 3, condition ii: `ρ(m) ≤ τ(m)^4`. -/
theorem primeWeight_le_tau_pow (m : ℕ) :
    primeWeight m ≤ ((m.divisors.card : ℕ) : ℝ) ^ 4 := by
  unfold primeWeight
  split_ifs with hp
  · rw [Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne]
    norm_num
  · positivity

/-- P0069 Baker Harman Pintz 1997, page 3, condition ii for the raw weight: `|b0(m)| ≤ 3 τ(m)^4`. -/
theorem abs_rawLower_le (ε x : ℝ) (m : ℕ) :
    |rawLower ε x m| ≤ 3 * ((m.divisors.card : ℕ) : ℝ) ^ 4 := by
  have h2 := lowerTwoTerms_le ε x m
  have h4 := lowerFourTerms_le ε x m
  have h2n := lowerTwoTerms_nonneg ε x m
  have h4n := lowerFourTerms_nonneg ε x m
  have hp := primeWeight_le_tau_pow m
  have hp0 := primeWeight_nonneg m
  have hsq : ((m.divisors.card : ℕ) : ℝ) ^ 2 ≤ ((m.divisors.card : ℕ) : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos m.divisors.card with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by exact_mod_cast h
      exact pow_le_pow_right₀ h1 (by norm_num)
  unfold rawLower
  rw [abs_le]
  constructor <;> nlinarith

/-- P0069 Baker Harman Pintz 1997, Section 5, pages 51 and 52, U-1624 factor: nonnegative. -/
theorem lowerFactor_nonneg (ω : ℝ → ℝ) (ε x : ℝ) (m : ℕ) : 0 ≤ lowerFactor ω ε x m :=
  le_max_left _ _

/-- P0069 Baker Harman Pintz 1997, Section 5, pages 51 and 52, U-1624 factor: at most one. -/
theorem lowerFactor_le_one (ω : ℝ → ℝ) (ε x : ℝ) (m : ℕ) : lowerFactor ω ε x m ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

/-- P0069 Baker Harman Pintz 1997, page 3, condition ii for b0, for every divisor exponent `B ≥ 4`. -/
theorem lowerShortWeight_divisor_bound (ω : ℝ → ℝ) (ε : ℝ) {B : ℝ} (hB : 4 ≤ B) :
    ∃ C : ℝ, ∀ x k, |lowerShortWeight ω ε x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  refine ⟨3, fun x k => ?_⟩
  set t : ℝ := ((k.divisors.card : ℕ) : ℝ) with ht
  have hraw := abs_rawLower_le ε x k
  have hf0 := lowerFactor_nonneg ω ε x k
  have hf1 := lowerFactor_le_one ω ε x k
  have hpow : t ^ 4 ≤ t ^ B := by
    rcases Nat.eq_zero_or_pos k.divisors.card with h | h
    · have : t = 0 := by rw [ht, h]; simp
      rw [this, Real.zero_rpow (by linarith)]
      norm_num
    · have h1 : (1 : ℝ) ≤ t := by rw [ht]; exact_mod_cast h
      have := Real.rpow_le_rpow_of_exponent_le h1 hB
      simpa [Real.rpow_natCast] using this
  unfold lowerShortWeight
  rw [abs_mul, abs_of_nonneg hf0]
  calc lowerFactor ω ε x k * |rawLower ε x k| ≤ 1 * |rawLower ε x k| :=
        mul_le_mul_of_nonneg_right hf1 (abs_nonneg _)
    _ ≤ 3 * t ^ 4 := by rw [one_mul]; exact hraw
    _ ≤ 3 * t ^ B := by linarith

/-- P0069 Baker Harman Pintz 1997, page 2, display 1.4: `b0(m) ≤ ρ(m)` on J, for every `x`. -/
theorem lowerShortWeight_le_primeWeight (ω : ℝ → ℝ) (ε x : ℝ) (m : ℕ) :
    lowerShortWeight ω ε x m ≤ primeWeight m := by
  have hf0 := lowerFactor_nonneg ω ε x m
  have hf1 := lowerFactor_le_one ω ε x m
  have hr := rawLower_le_primeWeight ε x m
  have hp := primeWeight_nonneg m
  unfold lowerShortWeight
  rcases le_or_gt 0 (rawLower ε x m) with h | h
  · nlinarith
  · nlinarith

/-- P0069 Baker Harman Pintz 1997, Section 5, page 51: at `s = 1` the density formula is the printed `v0`, one minus the E2 and E4
integrals. -/
theorem lowerDensityAt_one (ω : ℝ → ℝ) (ε : ℝ) : lowerDensityAt ω ε 1 = lowerV0 ω ε := by
  have h2 : lowerTwoDensityAt ω ε 1 = lowerTwoDeletedIntegral ω ε := rfl
  have hi : ∀ a b c d : ℝ, (if lowerFourRegion ε a b c d then
      (if (1-a-b-c-d)/d < 1 then 0 else ω ((1-a-b-c-d)/d)/(a*b*c*d^2)) else 0) =
      lowerFourDeletedIntegrand ω ε a b c d := by
    intro a b c d
    unfold lowerFourDeletedIntegrand lowerFourRegion
    split_ifs <;> rfl
  have h4 : lowerFourDensityAt ω ε 1 = lowerFourDeletedIntegral ω ε := by
    unfold lowerFourDensityAt lowerFourDeletedIntegral
    simp only [hi]
  unfold lowerDensityAt lowerV0
  rw [h2, h4, div_one]

/-! ### Support of b0: every prime factor exceeds `Z ^ c1` -/

/-- P0069 Baker Harman Pintz 1997, Section 5, page 50, display 5.15, and page 51: `m` has a
prime factor `p` with `p = Z ^ β`, `β ≥ c1`, below or equal to every prime factor of `m`. In
5.15 the retained sums all run over primes at least `Y ^ c1` and rough factors `ψ(n, p)`. -/
def RoughAbove (ε x : ℝ) (m : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (1+7*(2*(1/16-1/10^5)))/15-ε ≤ expo ε x p ∧
    ∀ r : ℕ, r.Prime → r ∣ m → p ≤ r

/-- Page 50, display 5.15: if `ψ(n, p) ≠ 0`, every prime factor of `n` is at least `p`. -/
theorem rough_ne_zero {n p : ℕ} (h : rough n p ≠ 0) :
    ∀ r : ℕ, r.Prime → r ∣ n → p ≤ r := by
  unfold rough at h
  split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

/-- Page 51: a nonzero term of the E2 sum over `p1 p2 n3 = m` has every prime factor at least
`p2 ≥ Z ^ c1`, since `p2 < p1` and `ψ(n3, p2) ≠ 0`. -/
theorem lowerTwoTerms_support {ε x : ℝ} {m : ℕ} (h : lowerTwoTerms ε x m ≠ 0) :
    RoughAbove ε x m := by
  by_contra hR
  apply h
  unfold lowerTwoTerms
  refine Finset.sum_eq_zero fun p1 _ => Finset.sum_eq_zero fun p2 _ => ?_
  split_ifs with hc
  · obtain ⟨hp1, hp2, h21, hdvd, hdisc⟩ := hc
    by_contra hne
    apply hR
    refine ⟨p2, hp2, hdisc.1, fun r hr hrm => ?_⟩
    have hm : m = p1 * p2 * (m / (p1 * p2)) := (Nat.mul_div_cancel' hdvd).symm
    rw [hm] at hrm
    rcases (Nat.Prime.dvd_mul hr).mp hrm with h12 | hn
    · rcases (Nat.Prime.dvd_mul hr).mp h12 with h1 | h2
      · rw [(Nat.prime_dvd_prime_iff_eq hr hp1).mp h1]; exact h21.le
      · rw [(Nat.prime_dvd_prime_iff_eq hr hp2).mp h2]
    · exact rough_ne_zero hne r hr hn
  · rfl

/-- Page 51: a nonzero term of the E4 sum over `p1 p2 p3 p4 n5 = m` has every prime factor at
least `p4 ≥ Z ^ c1`, since `p4 < p3 < p2 < p1` and `ψ(n5, p4) ≠ 0`. -/
theorem lowerFourTerms_support {ε x : ℝ} {m : ℕ} (h : lowerFourTerms ε x m ≠ 0) :
    RoughAbove ε x m := by
  by_contra hR
  apply h
  unfold lowerFourTerms
  refine Finset.sum_eq_zero fun p1 _ => Finset.sum_eq_zero fun p2 _ =>
    Finset.sum_eq_zero fun p3 _ => Finset.sum_eq_zero fun p4 _ => ?_
  split_ifs with hc
  · obtain ⟨hp1, hp2, hp3, hp4, h21, h32, h43, hdvd, hreg⟩ := hc
    by_contra hne
    apply hR
    refine ⟨p4, hp4, hreg.1, fun r hr hrm => ?_⟩
    have hm : m = p1 * p2 * p3 * p4 * (m / (p1 * p2 * p3 * p4)) :=
      (Nat.mul_div_cancel' hdvd).symm
    rw [hm] at hrm
    rcases (Nat.Prime.dvd_mul hr).mp hrm with h1234 | hn
    · rcases (Nat.Prime.dvd_mul hr).mp h1234 with h123 | h4
      · rcases (Nat.Prime.dvd_mul hr).mp h123 with h12 | h3
        · rcases (Nat.Prime.dvd_mul hr).mp h12 with h1 | h2
          · rw [(Nat.prime_dvd_prime_iff_eq hr hp1).mp h1]; omega
          · rw [(Nat.prime_dvd_prime_iff_eq hr hp2).mp h2]; omega
        · rw [(Nat.prime_dvd_prime_iff_eq hr hp3).mp h3]; omega
      · rw [(Nat.prime_dvd_prime_iff_eq hr hp4).mp h4]
    · exact rough_ne_zero hne r hr hn
  · rfl

/-- Page 51: b0 is supported on primes and on integers all of whose prime factors are at least
`Z ^ c1`, by 5.15 and the two subtracted sums. -/
theorem rawLower_support {ε x : ℝ} {m : ℕ} (h : rawLower ε x m ≠ 0) :
    m.Prime ∨ RoughAbove ε x m := by
  by_cases hp : m.Prime
  · exact Or.inl hp
  by_cases h2 : lowerTwoTerms ε x m = 0
  · by_cases h4 : lowerFourTerms ε x m = 0
    · exfalso; apply h
      unfold rawLower primeWeight
      rw [if_neg hp, h2, h4]; norm_num
    · exact Or.inr (lowerFourTerms_support h4)
  · exact Or.inr (lowerTwoTerms_support h2)

/-- Page 51, the remark after 5.15 used for 5.17: if `q < m` and `q < Z ^ c1`, a nonzero `b0(m)`
forces `m` coprime to `q`. -/
theorem rawLower_coprime {ε x : ℝ} {m q : ℕ} (hZ1 : 1 < scaleZ ε x)
    (hq : 1 ≤ q) (hqm : q < m)
    (hqZ : (q : ℝ) < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε))
    (h : rawLower ε x m ≠ 0) : Nat.Coprime m q := by
  by_contra hc
  set r := (Nat.gcd m q).minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hc
  have hrg : r ∣ Nat.gcd m q := Nat.minFac_dvd _
  have hrm : r ∣ m := hrg.trans (Nat.gcd_dvd_left m q)
  have hrq : r ≤ q := Nat.le_of_dvd hq (hrg.trans (Nat.gcd_dvd_right m q))
  rcases rawLower_support h with hp | ⟨p, hp, hc1, hpr⟩
  · have := (Nat.prime_dvd_prime_iff_eq hrp hp).mp hrm
    omega
  · have hpr' := hpr r hrp hrm
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hZpos : 0 < scaleZ ε x := by linarith
    have hZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
    have hlog : ((1+7*(2*(1/16-1/10^5)))/15-ε) * Real.log (scaleZ ε x) ≤ Real.log p := by
      unfold expo at hc1
      rwa [le_div_iff₀ hZ] at hc1
    have hZp : scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε) ≤ (p : ℝ) := by
      rw [Real.rpow_def_of_pos hZpos, ← Real.exp_log hp0]
      apply Real.exp_le_exp.mpr
      linarith
    have : (p : ℝ) ≤ q := by exact_mod_cast hpr'.trans hrq
    linarith

/-- P0069 Baker Harman Pintz 1997, page 51, display 5.17 with page 3, display 1.8: the growth fact
that `q ≤ (log x) ^ A` lies below `x ^ (11/200)` for large `x`. -/
theorem log_rpow_lt_rpow (A : ℝ) : ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
    Real.log x ^ A < x ^ (11 / 200 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0:ℝ) < 11/200)).bound
    (by norm_num : (0:ℝ) < 1/2)
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.mp (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hC x hx
  have hp : 0 < x ^ (11/200:ℝ) := Real.rpow_pos_of_pos h2 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at h1
  calc Real.log x ^ A ≤ |Real.log x ^ A| := le_abs_self _
    _ ≤ 1/2 * x ^ (11/200:ℝ) := h1
    _ < _ := by linarith

/-- Pages 3 and 51: for `x ≥ 1` the scale `Z = 4 Y` has `Z ^ c1 ≥ x ^ (11/200)`. -/
theorem scaleZ_rpow_ge {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x) :
    x ^ (11 / 200 : ℝ) ≤ scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε) ∧
      1 < scaleZ ε x := by
  have hY : x ^ (11/20 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hx1 : 1 ≤ x ^ (11/20 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hZ : x ^ (11/20 : ℝ) ≤ scaleZ ε x := by
    unfold scaleZ shortY; linarith
  have hZ1 : 1 < scaleZ ε x := by unfold scaleZ shortY; linarith
  refine ⟨?_, hZ1⟩
  have hc : (1/10 : ℝ) ≤ (1+7*(2*(1/16-1/10^5)))/15-ε := by
    have : (1/10 : ℝ) + 1/10^8 ≤ (1+7*(2*(1/16-1/10^5)))/15 := by norm_num
    linarith
  calc x ^ (11 / 200 : ℝ) = (x ^ (11/20 : ℝ)) ^ (1/10 : ℝ) := by
        rw [← Real.rpow_mul (by linarith)]; norm_num
    _ ≤ scaleZ ε x ^ (1/10 : ℝ) := Real.rpow_le_rpow (by linarith) hZ (by norm_num)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1.le hc


end LeanLab.BHP1997.LowerShortC165

namespace LeanLab.BHP1997.Decomp514a
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165
open scoped BigOperators

/-- P0069 page 50 display 5.15 and page 27 display 4.14. The explicit lower
coefficient uses the same rough indicator as the existing finite Buchstab API. -/
theorem rough_eq_roughIndicator (n p : ℕ) :
    rough n p = Task308.roughIndicator n p := by
  simp only [rough, Task308.roughIndicator, Nat.le_minFac]

/-- P0069 page 27 display 4.14, used in the decomposition on page 50 display 5.15.
The exact finite Buchstab identity holds for the sealed lower coefficient rough function.
This is a finite identity and supplies no rough number distribution estimate. -/
theorem rough_buchstab_finite (n w z : ℕ) (hwz : w ≤ z) :
    rough n z = rough n w -
      ∑ p ∈ z.primesBelow.filter (fun p => w ≤ p ∧ p ∣ n), rough (n / p) p := by
  simp_rw [rough_eq_roughIndicator]
  exact Task308.rough_buchstab_finite n w z hwz

/-- P0069 page 51 display 5.17. Two prefix cutoffs combine by taking their minimum. -/
theorem prefix_filter_min (S : Finset ℕ) (t u : ℝ) :
    (S.filter (fun m : ℕ => (m : ℝ) ≤ t)).filter (fun m : ℕ => (m : ℝ) ≤ u) =
      S.filter (fun m : ℕ => (m : ℝ) ≤ min t u) := by
  ext m
  simp [le_min_iff, and_assoc]

/-- P0069 page 51 display 5.17 and page 3 display 1.8. Partial summation
against the explicit normalization factor costs at most two when its discrete variation is at most one.
CONDITIONAL on the stated prefix and variation bounds. -/
theorem normalized_term_bound (ω : ℝ → ℝ) (ε x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (a : ℕ → ℝ) {R t : ℝ} (hR : 0 ≤ R)
    (ht : t ≤ 2 * x ^ (11 / 20 + ε))
    (hp : ∀ u : ℝ, u ≤ 2 * x ^ (11 / 20 + ε) →
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (a m : ℂ) * χ (m : ZMod q)‖ ≤ R)
    (hv : ∑ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
      |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤ 1) :
    ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((lowerFactor ω ε x m * a m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤ 2 * R := by
  let S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)
  have hs : ∀ m ∈ S, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ m ∧
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := by
    intro m hm
    have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1
    exact ⟨Nat.le_of_lt h.1, h.2⟩
  have hprefix : ∀ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
      ‖∑ m ∈ S.filter (fun m => m ≤ i), (a m : ℂ) * χ (m : ZMod q)‖ ≤ R := by
    intro i _
    have hi : S.filter (fun m => m ≤ i) =
        (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ min t (i : ℝ)) := by
      simp only [S, ← Nat.cast_le (α := ℝ)]
      exact prefix_filter_min _ _ _
    rw [hi]
    exact hp _ ((min_le_left _ _).trans ht)
  have hb := Decomp514Abel.weighted_sum_norm_le S hs
    (fun m => (lowerFactor ω ε x m : ℂ))
    (fun m => (a m : ℂ) * χ (m : ZMod q)) (hp t ht) hprefix
  have hnorm : ‖(lowerFactor ω ε x ⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lowerFactor_nonneg _ _ _ _)]
    exact lowerFactor_le_one _ _ _ _
  have hvar : ∑ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
      ‖(lowerFactor ω ε x (i + 1) : ℂ) - (lowerFactor ω ε x i : ℂ)‖ ≤ 1 := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hv
  have hid : (∑ m ∈ S, (lowerFactor ω ε x m : ℂ) *
      ((a m : ℂ) * χ (m : ZMod q))) =
      ∑ m ∈ S, ((lowerFactor ω ε x m * a m : ℝ) : ℂ) * χ (m : ZMod q) := by
    push_cast
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hid] at hb
  exact hb.trans (by nlinarith)

/-- LEAF. P0069 page 51 display 5.17 and page 3 display 1.8.
The nonprincipal prime number theorem input for this one unnormalized term of 5.15.
For a rough term this requires the ordered prime expansion of its rough variable.
The prime input and the two rough inputs are separate. This prime estimate follows from Prime514.nonprincipal_prime_short. -/
theorem leaf_prime_siegel_walfisz {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((primeWeight m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact Prime514.nonprincipal_prime_short hε hε8

/-- P0069 page 51 display 5.17 with page 50 display 5.15. For an exponent pair in E2 the outer
product `p1 p2 = Z ^ (β1 + β2)` has `β1 + β2 ≤ 9 / 10`, so it is at most `Y`, and the level
`p2 = Z ^ β2` has `β2 ≥ c1 - ε ≥ 1 / 10`, so it is at least `(2 Y) ^ (1 / 10)`. -/
theorem lowerTwo_outer_bounds {ε x : ℝ} (hε8 : ε ≤ 1/10^8)
    (hY : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε)) {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (h : lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)) :
    p1 * p2 ≤ ⌊x ^ (11 / 20 + ε)⌋₊ ∧
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (p2 : ℝ) := by
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY
  have hZ : scaleZ ε x = 4 * x ^ (11 / 20 + ε) := rfl
  have hZpos : 0 < scaleZ ε x := by rw [hZ]; linarith
  have hlZ : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
    rw [hZ, Real.log_mul (by norm_num) hYpos.ne']
  have hlY : 9 * Real.log 4 ≤ Real.log (x ^ (11 / 20 + ε)) := by
    have h9 := Real.log_le_log (by norm_num) hY
    rw [Real.log_pow] at h9
    exact_mod_cast h9
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlZpos : 0 < Real.log (scaleZ ε x) := by linarith
  obtain ⟨hb, -, -, hab, -⟩ := h
  unfold expo at hb hab
  have hp1' : (0 : ℝ) < p1 := by exact_mod_cast hp1.pos
  have hp2' : (0 : ℝ) < p2 := by exact_mod_cast hp2.pos
  have hc : (1 / 10 : ℝ) ≤ (1+7*(2*(1/16-1/10^5)))/15-ε := by
    have : (1/10 : ℝ) + 1/10^8 ≤ (1+7*(2*(1/16-1/10^5)))/15 := by norm_num
    linarith
  have h2 : 1 / 10 * Real.log (scaleZ ε x) ≤ Real.log p2 := by
    have h3 := (le_div_iff₀ hlZpos).mp hb
    have h4 := mul_le_mul_of_nonneg_right hc hlZpos.le
    linarith
  have h12 : Real.log p1 + 2 * Real.log p2 ≤ Real.log (scaleZ ε x) := by
    have h3 : Real.log p1 / Real.log (scaleZ ε x) + 2 * (Real.log p2 / Real.log (scaleZ ε x)) =
        (Real.log p1 + 2 * Real.log p2) / Real.log (scaleZ ε x) := by ring
    rw [h3] at hab
    rwa [div_le_one hlZpos] at hab
  constructor
  · apply Nat.le_floor
    push_cast
    have h3 : Real.log ((p1 : ℝ) * p2) ≤ Real.log (x ^ (11 / 20 + ε)) := by
      rw [Real.log_mul hp1'.ne' hp2'.ne']
      linarith
    exact (Real.log_le_log_iff (mul_pos hp1' hp2') hYpos).mp h3
  · have hX : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ scaleZ ε x ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by rw [hZ]; linarith) (by norm_num)
    refine hX.trans ?_
    rw [Real.rpow_def_of_pos hZpos, ← Real.exp_log hp2']
    apply Real.exp_le_exp.mpr
    linarith

/-- P0069 page 51 display 5.17 with page 50 display 5.15. The E2 sum over `p1 p2 n3 = m`
written as a sum over all pairs up to `N ≥ m`, with the divisibility condition explicit:
a divisor of `m` is at most `m`, and `p1 p2 ∣ m` forces `p1` and `p2` to divide `m`. -/
theorem lowerTwoTerms_eq_family (ε x : ℝ) {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    lowerTwoTerms ε x m =
      ∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ =>
          i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
            lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
        if i.1 * i.2 ∣ m then Task308.roughIndicator (m / (i.1 * i.2)) i.2 else 0 := by
  rw [Finset.sum_filter, Finset.sum_product]
  show lowerTwoTerms ε x m = ∑ p1 ∈ Finset.Icc 1 N, ∑ p2 ∈ Finset.Icc 1 N,
    (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
        lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
      then (if p1 * p2 ∣ m then Task308.roughIndicator (m / (p1 * p2)) p2 else 0)
      else 0)
  unfold lowerTwoTerms
  have hm0 : m ≠ 0 := by omega
  have hsub : m.divisors ⊆ Finset.Icc 1 N := fun d hd => by
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd, (Nat.divisor_le hd).trans hmN⟩
  have key : ∀ p1 : ℕ, ∑ p2 ∈ m.divisors,
        (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
          then rough (m / (p1 * p2)) p2 else 0) =
      ∑ p2 ∈ Finset.Icc 1 N,
        (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
          then (if p1 * p2 ∣ m then Task308.roughIndicator (m / (p1 * p2)) p2 else 0)
          else 0) := by
    intro p1
    have hpt : ∀ p2 : ℕ, (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧ p1 * p2 ∣ m ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
          then rough (m / (p1 * p2)) p2 else 0) =
        (if p1.Prime ∧ p2.Prime ∧ p2 < p1 ∧
            lowerTwoDiscarded ε (expo ε x p1) (expo ε x p2)
          then (if p1 * p2 ∣ m then Task308.roughIndicator (m / (p1 * p2)) p2 else 0)
          else 0) := by
      intro p2
      rw [rough_eq_roughIndicator]
      split_ifs <;> first | rfl | (exfalso; tauto)
    rw [Finset.sum_congr rfl fun p2 _ => hpt p2]
    refine Finset.sum_subset hsub fun p2 _ hp2 => ?_
    have hnd : ¬ p1 * p2 ∣ m := fun hd =>
      hp2 (Nat.mem_divisors.mpr ⟨dvd_of_mul_left_dvd hd, hm0⟩)
    rw [if_neg hnd, ite_self]
  refine (Finset.sum_congr rfl fun p1 _ => key p1).trans ?_
  refine Finset.sum_subset hsub fun p1 _ hp1 => Finset.sum_eq_zero fun p2 _ => ?_
  have hnd : ¬ p1 * p2 ∣ m := fun hd =>
    hp1 (Nat.mem_divisors.mpr ⟨dvd_of_mul_right_dvd hd, hm0⟩)
  rw [if_neg hnd, ite_self]

/-- P0069 page 51 display 5.17. The reciprocal sum over the outer pairs `p1 p2` of a
subtracted sum of 5.15 is at most the square of the harmonic sum, hence a fixed log power. -/
theorem pair_reciprocal_sum_le (N : ℕ) (I : Finset (ℕ × ℕ))
    (hI : I ⊆ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)) :
    ∑ i ∈ I, (1 : ℝ) / ((i.1 * i.2 : ℕ) : ℝ) ≤ (1 + Real.log N) ^ 2 := by
  have hh : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log N := by
    have h1 := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    simpa [one_div] using h1
  have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ i ∈ I, (1 : ℝ) / ((i.1 * i.2 : ℕ) : ℝ)
      ≤ ∑ i ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), (1 : ℝ) / ((i.1 * i.2 : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => by positivity)
    _ = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ^ 2 := by
        rw [Finset.sum_product, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        push_cast
        ring
    _ ≤ _ := pow_le_pow_left₀ h0 hh 2

/-- P0069 page 51 display 5.17. On the interval `(Y, 2Y]` the prefix cutoff `m ≤ t` with
`t ≥ 0` is the interval `(Y, min (2Y) t]`. -/
theorem rightInterval_filter_eq (ε x t : ℝ) (ht : 0 ≤ t) :
    (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊) := by
  ext m
  simp only [rightInterval, Finset.mem_filter, Finset.mem_Ioc, le_min_iff, Nat.le_floor_iff ht]
  tauto

/-- P0069 page 51 display 5.17 with page 50 display 5.15. On `(L, U]` with `U ≤ N` the
character sum of the E2 coefficient is the character sum of the family of rough indicators
of the cofactors `m / (p1 p2)` at level `p2`. -/
theorem lowerTwo_sum_eq_family (ε x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) {L U N : ℕ}
    (hU : U ≤ N) :
    ∑ m ∈ Finset.Ioc L U, ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
      ∑ m ∈ Finset.Ioc L U,
        ((∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          if i.1 * i.2 ∣ m then Task308.roughIndicator (m / (i.1 * i.2)) i.2 else 0 : ℝ) : ℂ) *
            χ (m : ZMod q) := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_Ioc.mp hm
  rw [lowerTwoTerms_eq_family ε x (N := N) (by omega) (hm'.2.trans hU)]

/-- P0069 page 3 display 1.8 with page 51 display 5.17. The scale `Y = x ^ (11/20 + ε)` is at
least `c` once `x ≥ c ^ 2`. -/
theorem shortY_ge_of_sq_le {ε x c : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) (hc : c ^ 2 ≤ x) :
    c ≤ x ^ (11 / 20 + ε) := by
  have h1 : c ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hc
  rw [Real.sqrt_eq_rpow] at h1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))

/-- P0069 page 51 display 5.17. The logarithm of the scale `2 Y` is comparable with
`log x`: it lies between `log x / 2` and `2 log x`. -/
theorem log_scale_bounds {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 0 < x)
    (hl : 1 ≤ Real.log x) :
    Real.log x / 2 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ∧
      Real.log (2 * x ^ (11 / 20 + ε)) ≤ 2 * Real.log x := by
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx _
  rw [Real.log_mul (by norm_num) hY.ne', Real.log_rpow hx]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h3 : 0 ≤ ε * Real.log x := mul_nonneg hε.le (by linarith)
  have h4 : ε * Real.log x ≤ 1 / 10 ^ 8 * Real.log x :=
    mul_le_mul_of_nonneg_right hε8 (by linarith)
  constructor <;> nlinarith

/-- P0069 page 51 display 5.17 with page 3 display 1.8. Bookkeeping of log powers between the
scale `2 Y` and `x`: with `log x / 2 ≤ lX ≤ 2 log x` and `log x ≥ 2 ^ (A + 1)`, a modulus
bound `log x ^ A` is a bound `lX ^ (A + 2)`, and the saving `lX ^ (-(A + 2))` absorbs the
factor `(2 lX) ^ 2` from the outer prime pairs. -/
theorem log_power_transfer {A l lX : ℝ} (hA : 0 < A) (hl : (2 : ℝ) ^ (A + 1) ≤ l)
    (h1 : l / 2 ≤ lX) (h2 : lX ≤ 2 * l) :
    l ^ A ≤ lX ^ (A + 2) ∧
      lX ^ (-(A + 2)) * (2 * lX) ^ 2 ≤ 4 * (2 : ℝ) ^ A * l ^ (-A) ∧ 1 ≤ lX := by
  have h2A : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hpow : (2 : ℝ) ^ (A + 1) = (2 : ℝ) ^ A * 2 := Real.rpow_add_one (by norm_num) A
  have hl2 : 2 * (2 : ℝ) ^ A ≤ l := by rw [hpow] at hl; linarith
  have hlpos : 0 < l := by linarith
  have hX : (2 : ℝ) ^ A ≤ lX := by linarith
  have hX1 : 1 ≤ lX := h2A.trans hX
  have hXpos : 0 < lX := by linarith
  have hsq : (0 : ℝ) < lX ^ 2 := pow_pos hXpos 2
  refine ⟨?_, ?_, hX1⟩
  · calc l ^ A ≤ (2 * lX) ^ A := Real.rpow_le_rpow hlpos.le (by linarith) hA.le
      _ = (2 : ℝ) ^ A * lX ^ A := Real.mul_rpow (by norm_num) hXpos.le
      _ ≤ lX ^ 2 * lX ^ A := by
          have hA0 : 0 ≤ lX ^ A := Real.rpow_nonneg hXpos.le A
          have h3 : (2 : ℝ) ^ A ≤ lX ^ 2 := by
            have h4 := mul_le_mul_of_nonneg_left hX1 hXpos.le
            nlinarith
          exact mul_le_mul_of_nonneg_right h3 hA0
      _ = lX ^ (A + 2) := by
          rw [Real.rpow_add hXpos, Real.rpow_two]
          ring
  · have e1 : lX ^ (-(A + 2)) = lX ^ (-A) * (lX ^ 2)⁻¹ := by
      rw [show -(A + 2) = -A + -2 by ring, Real.rpow_add hXpos, Real.rpow_neg hXpos.le 2,
        Real.rpow_two]
    have e2 : lX ^ (-A) ≤ (2 : ℝ) ^ A * l ^ (-A) := by
      have hh : (0 : ℝ) < l / 2 := by linarith
      calc lX ^ (-A) ≤ (l / 2) ^ (-A) := Real.rpow_le_rpow_of_nonpos hh h1 (by linarith)
        _ = l ^ (-A) / (2 : ℝ) ^ (-A) := Real.div_rpow hlpos.le (by norm_num) _
        _ = (2 : ℝ) ^ A * l ^ (-A) := by
            rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
            ring
    have e3 : (lX ^ 2)⁻¹ * lX ^ 2 = 1 := inv_mul_cancel₀ hsq.ne'
    calc lX ^ (-(A + 2)) * (2 * lX) ^ 2
        = 4 * lX ^ (-A) * ((lX ^ 2)⁻¹ * lX ^ 2) := by rw [e1]; ring
      _ = 4 * lX ^ (-A) := by rw [e3, mul_one]
      _ ≤ 4 * ((2 : ℝ) ^ A * l ^ (-A)) := by linarith
      _ = 4 * (2 : ℝ) ^ A * l ^ (-A) := by ring

/-- P0069 page 51 display 5.17 and page 3 display 1.8.
The nonprincipal prime number theorem input for this one unnormalized term of 5.15.
For a rough term this requires the ordered prime expansion of its rough variable.
The prime input and the two rough inputs are separate. PROVED here from
`Rough514.rough_family_character_sum` and the E2 family lemmas above. -/
theorem leaf_two_rough_siegel_walfisz {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0, hbb⟩ := Rough514.rough_family_character_sum (c := 1 / 10) (by norm_num)
    (A + 2) (by linarith)
  refine ⟨max (8 * C0 * (2 : ℝ) ^ A)
    (max ((2 : ℝ) ^ 36) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (C0 ^ 2))), ?_⟩
  generalize hCdef : max (8 * C0 * (2 : ℝ) ^ A)
    (max ((2 : ℝ) ^ 36) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (C0 ^ 2))) = C
  have hC1 : 8 * C0 * (2 : ℝ) ^ A ≤ C := by rw [← hCdef]; exact le_max_left _ _
  have hC2 : (2 : ℝ) ^ 36 ≤ C := by
    rw [← hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ C := by
    rw [← hCdef]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC4 : C0 ^ 2 ≤ C := by
    rw [← hCdef]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  intro x hx q hq hqA χ hχ t ht
  have hx36 : (2 : ℝ) ^ 36 ≤ x := hC2.trans hx
  have hxe : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x := hC3.trans hx
  have hxC : C0 ^ 2 ≤ x := hC4.trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYC : C0 ≤ x ^ (11 / 20 + ε) := shortY_ge_of_sq_le hε hx1 hxC
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hYpos : 0 < x ^ (11 / 20 + ε) := by linarith
  have hl : (2 : ℝ) ^ (A + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have h2A : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.rpow_add_one (by norm_num) A] at hl
    linarith
  obtain ⟨hlX1, hlX2⟩ := log_scale_bounds hε hε8 hxpos hl1
  obtain ⟨hqpow, hout, hlXone⟩ := log_power_transfer hA hl hlX1 hlX2
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg hYpos.le (Real.rpow_nonneg (by linarith) _)
  have hC0A : 0 ≤ 8 * C0 * (2 : ℝ) ^ A :=
    mul_nonneg (mul_nonneg (by norm_num) hC0.le) (by linarith)
  have hfinal : 8 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ≤
      C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
    mul_le_mul_of_nonneg_right hC1 hscale
  rcases lt_or_ge t 0 with ht0 | ht0
  · have hemp : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun m _ hmt => ?_
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmt' : (m : ℝ) ≤ t := hmt
      linarith
    rw [hemp, Finset.sum_empty, norm_zero]
    calc (0 : ℝ) ≤ 8 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_nonneg hC0A hscale
      _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hfinal
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
  · rw [rightInterval_filter_eq ε x t ht0,
      lowerTwo_sum_eq_family ε x χ (min_le_left ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊)]
    have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by linarith)
    have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
      Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hUle : ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      (Nat.cast_le.mpr (min_le_left _ _)).trans hNle
    refine le_trans (hbb (2 * x ^ (11 / 20 + ε)) (by linarith) q hq (hqA.trans hqpow) χ hχ _
      (fun i : ℕ × ℕ => i.1 * i.2) (fun i : ℕ × ℕ => i.2) _ _
      ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2) ?_ hUle ?_) ?_
    · intro i hi
      obtain ⟨-, hp1, hp2, -, hdisc⟩ := Finset.mem_filter.mp hi
      obtain ⟨hb1, hb2⟩ := lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hdisc
      exact ⟨Nat.mul_pos hp1.pos hp2.pos, hb1, hb2⟩
    · refine le_trans (pair_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
        (Finset.filter_subset _ _)) ?_
      have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
      have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
          Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    · have h0 : 0 ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 :=
        mul_nonneg hC0.le (sq_nonneg _)
      have h1 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) :=
        Real.rpow_nonneg (by linarith) _
      calc C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 *
            ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2))
          ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 * (2 * x ^ (11 / 20 + ε)) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUle h0) h1
        _ = 2 * C0 * x ^ (11 / 20 + ε) * (Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) *
            (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2) := by ring
        _ ≤ 2 * C0 * x ^ (11 / 20 + ε) * (4 * (2 : ℝ) ^ A * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hout
              (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hYpos.le)
        _ = 8 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
        _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hfinal
        _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring

/-- P0069 page 51 display 5.17 with page 50 display 5.15. For an exponent quadruple in E4 the
outer product `p1 p2 p3 p4 = Z ^ (β1 + β2 + β3 + β4)` has exponent sum at most `3 / 4`, since
`β4 ≤ β3 ≤ β2 ≤ β1` and `β1 + β2 + β3 < 0.532`, so it is at most `Y`, and the level
`p4 = Z ^ β4` has `β4 ≥ c1 - ε ≥ 1 / 10`, so it is at least `(2 Y) ^ (1 / 10)`. -/
theorem four_outer_bounds {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hY : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε)) {p1 p2 p3 p4 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp3 : p3.Prime) (hp4 : p4.Prime)
    (h : lowerFourRegion ε (expo ε x p1) (expo ε x p2) (expo ε x p3) (expo ε x p4)) :
    p1 * p2 * p3 * p4 ≤ ⌊x ^ (11 / 20 + ε)⌋₊ ∧
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (p4 : ℝ) := by
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY
  have hZ : scaleZ ε x = 4 * x ^ (11 / 20 + ε) := rfl
  have hZpos : 0 < scaleZ ε x := by rw [hZ]; linarith
  have hlZ : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
    rw [hZ, Real.log_mul (by norm_num) hYpos.ne']
  have hlY : 3 * Real.log 4 ≤ Real.log (x ^ (11 / 20 + ε)) := by
    have h9 := Real.log_le_log (by norm_num) hY
    rw [Real.log_pow] at h9
    exact_mod_cast h9
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlZpos : 0 < Real.log (scaleZ ε x) := by linarith
  obtain ⟨hd, hdc, hcb, hba, -, habc, -⟩ := h
  have hp1' : (0 : ℝ) < p1 := by exact_mod_cast hp1.pos
  have hp2' : (0 : ℝ) < p2 := by exact_mod_cast hp2.pos
  have hp3' : (0 : ℝ) < p3 := by exact_mod_cast hp3.pos
  have hp4' : (0 : ℝ) < p4 := by exact_mod_cast hp4.pos
  have hc : (1 / 10 : ℝ) ≤ (1+7*(2*(1/16-1/10^5)))/15-ε := by
    have : (1/10 : ℝ) + 1/10^8 ≤ (1+7*(2*(1/16-1/10^5)))/15 := by norm_num
    linarith
  have hsum : expo ε x p1 + expo ε x p2 + expo ε x p3 + expo ε x p4 ≤ 3 / 4 := by
    have hk : (1/2 : ℝ)+(2*(1/16-1/10^5))/4 ≤ 9 / 16 := by norm_num
    linarith
  have he : ∀ p : ℕ, Real.log p = expo ε x p * Real.log (scaleZ ε x) := fun p => by
    unfold expo
    rw [div_mul_cancel₀ _ hlZpos.ne']
  have h4 : 1 / 10 * Real.log (scaleZ ε x) ≤ Real.log p4 := by
    rw [he p4]
    exact mul_le_mul_of_nonneg_right (hc.trans hd) hlZpos.le
  have h1234 : Real.log p1 + Real.log p2 + Real.log p3 + Real.log p4 ≤
      3 / 4 * Real.log (scaleZ ε x) := by
    rw [he p1, he p2, he p3, he p4, ← add_mul, ← add_mul, ← add_mul]
    exact mul_le_mul_of_nonneg_right hsum hlZpos.le
  constructor
  · apply Nat.le_floor
    push_cast
    have h3 : Real.log ((p1 : ℝ) * p2 * p3 * p4) ≤ Real.log (x ^ (11 / 20 + ε)) := by
      rw [Real.log_mul (by positivity) hp4'.ne', Real.log_mul (by positivity) hp3'.ne',
        Real.log_mul hp1'.ne' hp2'.ne']
      linarith
    exact (Real.log_le_log_iff (by positivity) hYpos).mp h3
  · have hX : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ scaleZ ε x ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by rw [hZ]; linarith) (by norm_num)
    refine hX.trans ?_
    rw [Real.rpow_def_of_pos hZpos, ← Real.exp_log hp4']
    apply Real.exp_le_exp.mpr
    linarith

/-- P0069 page 51 display 5.17 with page 50 display 5.15. A fourfold sum over the divisors of
`m ≠ 0` whose terms vanish unless `p1 p2 p3 p4 ∣ m` may be extended to any larger range of
each variable: `p1 p2 p3 p4 ∣ m` forces each `pj` to be a divisor of `m`. -/
theorem four_sum_extend {m : ℕ} (hm0 : m ≠ 0) {S : Finset ℕ} (hsub : m.divisors ⊆ S)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ p1 p2 p3 p4 : ℕ, ¬ p1 * p2 * p3 * p4 ∣ m → F p1 p2 p3 p4 = 0) :
    ∑ p1 ∈ m.divisors, ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors,
        F p1 p2 p3 p4 =
      ∑ p1 ∈ S, ∑ p2 ∈ S, ∑ p3 ∈ S, ∑ p4 ∈ S, F p1 p2 p3 p4 := by
  have hnd : ∀ p : ℕ, p ∉ m.divisors → ¬ p ∣ m := fun p hp hd =>
    hp (Nat.mem_divisors.mpr ⟨hd, hm0⟩)
  have e4 : ∀ p1 p2 p3 : ℕ, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4 = ∑ p4 ∈ S, F p1 p2 p3 p4 :=
    fun p1 p2 p3 => Finset.sum_subset hsub fun p4 _ hp4 =>
      hF _ _ _ _ fun hd => hnd p4 hp4 (dvd_of_mul_left_dvd hd)
  have e3 : ∀ p1 p2 : ℕ, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors, F p1 p2 p3 p4 =
      ∑ p3 ∈ S, ∑ p4 ∈ S, F p1 p2 p3 p4 := fun p1 p2 => by
    rw [Finset.sum_congr rfl fun p3 _ => e4 p1 p2 p3]
    exact Finset.sum_subset hsub fun p3 _ hp3 => Finset.sum_eq_zero fun p4 _ =>
      hF _ _ _ _ fun hd => hnd p3 hp3 (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd hd))
  have e2 : ∀ p1 : ℕ, ∑ p2 ∈ m.divisors, ∑ p3 ∈ m.divisors, ∑ p4 ∈ m.divisors,
      F p1 p2 p3 p4 = ∑ p2 ∈ S, ∑ p3 ∈ S, ∑ p4 ∈ S, F p1 p2 p3 p4 := fun p1 => by
    rw [Finset.sum_congr rfl fun p2 _ => e3 p1 p2]
    exact Finset.sum_subset hsub fun p2 _ hp2 => Finset.sum_eq_zero fun p3 _ =>
      Finset.sum_eq_zero fun p4 _ => hF _ _ _ _ fun hd => hnd p2 hp2
        (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd (dvd_of_mul_right_dvd hd)))
  rw [Finset.sum_congr rfl fun p1 _ => e2 p1]
  exact Finset.sum_subset hsub fun p1 _ hp1 => Finset.sum_eq_zero fun p2 _ =>
    Finset.sum_eq_zero fun p3 _ => Finset.sum_eq_zero fun p4 _ => hF _ _ _ _ fun hd =>
      hnd p1 hp1 (dvd_of_mul_right_dvd (dvd_of_mul_right_dvd (dvd_of_mul_right_dvd hd)))

/-- P0069 page 51 display 5.17 with page 50 display 5.15. The E4 sum over
`p1 p2 p3 p4 n5 = m` written as a sum over all quadruples up to `N ≥ m`, with the divisibility
condition explicit: a divisor of `m` is at most `m`, and `p1 p2 p3 p4 ∣ m` forces each prime
to divide `m`. -/
theorem four_terms_eq_family (ε x : ℝ) {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    lowerFourTerms ε x m =
      ∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ
          (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
          i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
            i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
            lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
              (expo ε x i.2.2.2)),
        if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
          Task308.roughIndicator (m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)) i.2.2.2 else 0 := by
  have hm0 : m ≠ 0 := by omega
  have hsub : m.divisors ⊆ Finset.Icc 1 N := fun d hd => by
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_mem_divisors hd, (Nat.divisor_le hd).trans hmN⟩
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]
  unfold lowerFourTerms
  refine (four_sum_extend hm0 hsub _ ?_).trans ?_
  · intro p1 p2 p3 p4 hnd
    exact ite_eq_right_iff.mpr fun h => absurd h.2.2.2.2.2.2.2.1 hnd
  · refine Finset.sum_congr rfl fun p1 _ => Finset.sum_congr rfl fun p2 _ =>
      Finset.sum_congr rfl fun p3 _ => Finset.sum_congr rfl fun p4 _ => ?_
    rw [rough_eq_roughIndicator]
    split_ifs <;> first | rfl | (exfalso; tauto)

/-- P0069 page 51 display 5.17. The reciprocal sum over the outer quadruples `p1 p2 p3 p4` of
a subtracted sum of 5.15 is at most the fourth power of the harmonic sum, hence a fixed log
power. -/
theorem four_reciprocal_sum_le (N : ℕ) (I : Finset (ℕ × ℕ × ℕ × ℕ))
    (hI : I ⊆ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)) :
    ∑ i ∈ I, (1 : ℝ) / ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ) ≤
      (1 + Real.log N) ^ 4 := by
  have hh : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log N := by
    have h1 := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    simpa [one_div] using h1
  have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have e4 : ∀ a b c : ℕ, ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / ((a * b * c * d : ℕ) : ℝ) =
      1 / (a : ℝ) * (1 / (b : ℝ)) * (1 / (c : ℝ)) *
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := fun a b c => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    ring
  have e3 : ∀ a b : ℕ, ∑ c ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
      (1 : ℝ) / ((a * b * c * d : ℕ) : ℝ) =
      1 / (a : ℝ) * (1 / (b : ℝ)) * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ^ 2 :=
    fun a b => by
    simp only [e4]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have e2 : ∀ a : ℕ, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
      (1 : ℝ) / ((a * b * c * d : ℕ) : ℝ) =
      1 / (a : ℝ) * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ^ 3 := fun a => by
    simp only [e3]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  calc ∑ i ∈ I, (1 : ℝ) / ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ)
      ≤ ∑ i ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          (1 : ℝ) / ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => by positivity)
    _ = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ^ 4 := by
        simp only [Finset.sum_product, e2]
        rw [← Finset.sum_mul]
        ring
    _ ≤ _ := pow_le_pow_left₀ h0 hh 4

/-- P0069 page 51 display 5.17. On the interval `(Y, 2Y]` the prefix cutoff `m ≤ t` with
`t ≥ 0` is the interval `(Y, min (2Y) t]`. -/
theorem four_rightInterval_filter_eq (ε x t : ℝ) (ht : 0 ≤ t) :
    (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊) := by
  ext m
  simp only [rightInterval, Finset.mem_filter, Finset.mem_Ioc, le_min_iff, Nat.le_floor_iff ht]
  tauto

/-- P0069 page 51 display 5.17 with page 50 display 5.15. On `(L, U]` with `U ≤ N` the
character sum of the E4 coefficient is the character sum of the family of rough indicators
of the cofactors `m / (p1 p2 p3 p4)` at level `p4`. -/
theorem four_sum_eq_family (ε x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) {L U N : ℕ}
    (hU : U ≤ N) :
    ∑ m ∈ Finset.Ioc L U, ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) =
      ∑ m ∈ Finset.Ioc L U,
        ((∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ
            (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
              i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
            Task308.roughIndicator (m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)) i.2.2.2
          else 0 : ℝ) : ℂ) * χ (m : ZMod q) := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_Ioc.mp hm
  rw [four_terms_eq_family ε x (N := N) (by omega) (hm'.2.trans hU)]

/-- P0069 page 3 display 1.8 with page 51 display 5.17. The scale `Y = x ^ (11/20 + ε)` is at
least `c` once `x ≥ c ^ 2`. -/
theorem four_shortY_ge_of_sq_le {ε x c : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) (hc : c ^ 2 ≤ x) :
    c ≤ x ^ (11 / 20 + ε) := by
  have h1 : c ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hc
  rw [Real.sqrt_eq_rpow] at h1
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))

/-- P0069 page 51 display 5.17. The logarithm of the scale `2 Y` is at least `log x / 2`. -/
theorem four_log_scale_ge {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) (hl : 1 ≤ Real.log x) :
    Real.log x / 2 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := by
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx _
  rw [Real.log_mul (by norm_num) hY.ne', Real.log_rpow hx]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 ≤ ε * Real.log x := mul_nonneg hε.le (by linarith)
  nlinarith

/-- P0069 page 51 display 5.17 with page 3 display 1.8. Bookkeeping of log powers between the
scale `2 Y` and `x`: with `log x / 2 ≤ lX` and `log x ≥ 2 ^ (A + 1)`, a modulus bound
`log x ^ A` is a bound `lX ^ (A + 4)`, and the saving `lX ^ (-(A + 4))` absorbs the factor
`(2 lX) ^ 4` from the outer prime quadruples. -/
theorem four_log_power_transfer {A l lX : ℝ} (hA : 0 < A) (hl : (2 : ℝ) ^ (A + 1) ≤ l)
    (h1 : l / 2 ≤ lX) :
    l ^ A ≤ lX ^ (A + 4) ∧
      lX ^ (-(A + 4)) * (2 * lX) ^ 4 ≤ 16 * (2 : ℝ) ^ A * l ^ (-A) ∧ 1 ≤ lX := by
  have h2A : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hpow : (2 : ℝ) ^ (A + 1) = (2 : ℝ) ^ A * 2 := Real.rpow_add_one (by norm_num) A
  have hl2 : 2 * (2 : ℝ) ^ A ≤ l := by rw [hpow] at hl; linarith
  have hlpos : 0 < l := by linarith
  have hX : (2 : ℝ) ^ A ≤ lX := by linarith
  have hX1 : 1 ≤ lX := h2A.trans hX
  have hXpos : 0 < lX := by linarith
  have hq : (0 : ℝ) < lX ^ 4 := pow_pos hXpos 4
  have e4 : lX ^ (4 : ℝ) = lX ^ 4 := by exact_mod_cast Real.rpow_natCast lX 4
  refine ⟨?_, ?_, hX1⟩
  · calc l ^ A ≤ (2 * lX) ^ A := Real.rpow_le_rpow hlpos.le (by linarith) hA.le
      _ = (2 : ℝ) ^ A * lX ^ A := Real.mul_rpow (by norm_num) hXpos.le
      _ ≤ lX ^ 4 * lX ^ A := by
          have hA0 : 0 ≤ lX ^ A := Real.rpow_nonneg hXpos.le A
          have h3 : (2 : ℝ) ^ A ≤ lX ^ 4 := hX.trans (le_self_pow₀ hX1 (by norm_num))
          exact mul_le_mul_of_nonneg_right h3 hA0
      _ = lX ^ (A + 4) := by
          rw [Real.rpow_add hXpos, e4]
          ring
  · have e1 : lX ^ (-(A + 4)) = lX ^ (-A) * (lX ^ 4)⁻¹ := by
      rw [show -(A + 4) = -A + -4 by ring, Real.rpow_add hXpos, Real.rpow_neg hXpos.le 4, e4]
    have e2 : lX ^ (-A) ≤ (2 : ℝ) ^ A * l ^ (-A) := by
      have hh : (0 : ℝ) < l / 2 := by linarith
      calc lX ^ (-A) ≤ (l / 2) ^ (-A) := Real.rpow_le_rpow_of_nonpos hh h1 (by linarith)
        _ = l ^ (-A) / (2 : ℝ) ^ (-A) := Real.div_rpow hlpos.le (by norm_num) _
        _ = (2 : ℝ) ^ A * l ^ (-A) := by
            rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
            ring
    have e3 : (lX ^ 4)⁻¹ * lX ^ 4 = 1 := inv_mul_cancel₀ hq.ne'
    calc lX ^ (-(A + 4)) * (2 * lX) ^ 4
        = 16 * lX ^ (-A) * ((lX ^ 4)⁻¹ * lX ^ 4) := by rw [e1]; ring
      _ = 16 * lX ^ (-A) := by rw [e3, mul_one]
      _ ≤ 16 * ((2 : ℝ) ^ A * l ^ (-A)) := by linarith
      _ = 16 * (2 : ℝ) ^ A * l ^ (-A) := by ring

/-- P0069 page 51 display 5.17 and page 3 display 1.8.
The nonprincipal prime number theorem input for this one unnormalized term of 5.15.
For a rough term this requires the ordered prime expansion of its rough variable.
The prime input and the two rough inputs are separate. PROVED here from
`Rough514.rough_family_character_sum` and the E4 family lemmas above. -/
theorem leaf_four_rough_siegel_walfisz {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0, hbb⟩ := Rough514.rough_family_character_sum (c := 1 / 10) (by norm_num)
    (A + 4) (by linarith)
  refine ⟨max (32 * C0 * (2 : ℝ) ^ A)
    (max ((2 : ℝ) ^ 12) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (C0 ^ 2))), ?_⟩
  generalize hCdef : max (32 * C0 * (2 : ℝ) ^ A)
    (max ((2 : ℝ) ^ 12) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (C0 ^ 2))) = C
  have hC1 : 32 * C0 * (2 : ℝ) ^ A ≤ C := by rw [← hCdef]; exact le_max_left _ _
  have hC2 : (2 : ℝ) ^ 12 ≤ C := by
    rw [← hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ C := by
    rw [← hCdef]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC4 : C0 ^ 2 ≤ C := by
    rw [← hCdef]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  intro x hx q hq hqA χ hχ t ht
  have hx12 : (2 : ℝ) ^ 12 ≤ x := hC2.trans hx
  have hxe : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x := hC3.trans hx
  have hxC : C0 ^ 2 ≤ x := hC4.trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx12
  have hxpos : 0 < x := by linarith
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := by
    refine four_shortY_ge_of_sq_le hε hx1 ?_
    have h43 : ((4 : ℝ) ^ 3) ^ 2 = (2 : ℝ) ^ 12 := by norm_num
    rw [h43]
    exact hx12
  have hYC : C0 ≤ x ^ (11 / 20 + ε) := four_shortY_ge_of_sq_le hε hx1 hxC
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY43
  have hYpos : 0 < x ^ (11 / 20 + ε) := by linarith
  have hl : (2 : ℝ) ^ (A + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have h2A : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.rpow_add_one (by norm_num) A] at hl
    linarith
  have hlX1 := four_log_scale_ge hε hxpos hl1
  obtain ⟨hqpow, hout, hlXone⟩ := four_log_power_transfer hA hl hlX1
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg hYpos.le (Real.rpow_nonneg (by linarith) _)
  have hC0A : 0 ≤ 32 * C0 * (2 : ℝ) ^ A :=
    mul_nonneg (mul_nonneg (by norm_num) hC0.le) (by linarith)
  have hfinal : 32 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ≤
      C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
    mul_le_mul_of_nonneg_right hC1 hscale
  rcases lt_or_ge t 0 with ht0 | ht0
  · have hemp : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun m _ hmt => ?_
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmt' : (m : ℝ) ≤ t := hmt
      linarith
    rw [hemp, Finset.sum_empty, norm_zero]
    calc (0 : ℝ) ≤ 32 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_nonneg hC0A hscale
      _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hfinal
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
  · rw [four_rightInterval_filter_eq ε x t ht0,
      four_sum_eq_family ε x χ (min_le_left ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊)]
    have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by linarith)
    have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
      Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hUle : ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      (Nat.cast_le.mpr (min_le_left _ _)).trans hNle
    refine le_trans (hbb (2 * x ^ (11 / 20 + ε)) (by linarith) q hq (hqA.trans hqpow) χ hχ _
      (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
      (fun i : ℕ × ℕ × ℕ × ℕ => i.2.2.2) _ _
      ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4) ?_ hUle ?_) ?_
    · intro i hi
      obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
      obtain ⟨hb1, hb2⟩ := four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
      exact ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos,
        hb1, hb2⟩
    · refine le_trans (four_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
        (Finset.filter_subset _ _)) ?_
      have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
      have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
          Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
      exact pow_le_pow_left₀ (by linarith) (by linarith) 4
    · have h0 : 0 ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 :=
        mul_nonneg hC0.le (by positivity)
      have h1 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) :=
        Real.rpow_nonneg (by linarith) _
      calc C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 *
            ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4))
          ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 * (2 * x ^ (11 / 20 + ε)) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUle h0) h1
        _ = 2 * C0 * x ^ (11 / 20 + ε) * (Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) *
            (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4) := by ring
        _ ≤ 2 * C0 * x ^ (11 / 20 + ε) * (16 * (2 : ℝ) ^ A * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hout
              (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hYpos.le)
        _ = 32 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
        _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hfinal
        _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring

open MeasureTheory Set in
/-- P0069 page 51 display 5.17. Measure theory helper for the E2 density: two integrable
functions that differ by at most `K1` off a band of length `d - c` and by at most `K2`
everywhere have integrals within `K1 * (hi - lo) + K2 * (d - c)`. -/
theorem two_density_band_bound (f g : ℝ → ℝ) {lo hi c d K1 K2 : ℝ} (hlo : lo ≤ hi)
    (hcd : c ≤ d) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hf : IntegrableOn f (Ioc lo hi)) (hg : IntegrableOn g (Ioc lo hi))
    (h1 : ∀ x ∈ Ioc lo hi, x ∉ Ioc c d → |f x - g x| ≤ K1)
    (h2 : ∀ x ∈ Ioc lo hi, |f x - g x| ≤ K2) :
    |(∫ x in lo..hi, f x) - ∫ x in lo..hi, g x| ≤ K1 * (hi - lo) + K2 * (d - c) := by
  rw [intervalIntegral.integral_of_le hlo, intervalIntegral.integral_of_le hlo,
    ← integral_sub hf hg,
    ← integral_inter_add_sdiff (f := fun x => f x - g x) (t := Ioc c d) measurableSet_Ioc
      (hf.sub hg)]
  have hA : ‖∫ x in Ioc lo hi ∩ Ioc c d, (f x - g x)‖ ≤
      K2 * volume.real (Ioc lo hi ∩ Ioc c d) :=
    norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono inter_subset_left) measure_Ioc_lt_top)
      (fun x hx => h2 x hx.1)
  have hB : ‖∫ x in Ioc lo hi \ Ioc c d, (f x - g x)‖ ≤
      K1 * volume.real (Ioc lo hi \ Ioc c d) :=
    norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_lt (measure_mono sdiff_subset) measure_Ioc_lt_top)
      (fun x hx => h1 x hx.1 hx.2)
  have hA' : volume.real (Ioc lo hi ∩ Ioc c d) ≤ d - c := by
    rw [← Real.volume_real_Ioc_of_le hcd]
    exact measureReal_mono inter_subset_right measure_Ioc_lt_top.ne
  have hB' : volume.real (Ioc lo hi \ Ioc c d) ≤ hi - lo := by
    rw [← Real.volume_real_Ioc_of_le hlo]
    exact measureReal_mono sdiff_subset measure_Ioc_lt_top.ne
  rw [Real.norm_eq_abs] at hA hB
  have hA2 := mul_le_mul_of_nonneg_left hA' hK2
  have hB2 := mul_le_mul_of_nonneg_left hB' hK1
  have ht := abs_add_le (∫ x in Ioc lo hi ∩ Ioc c d, (f x - g x))
    (∫ x in Ioc lo hi \ Ioc c d, (f x - g x))
  linarith

/-- P0069 page 51 display 5.17. Buchstab's function with the zero extension is nonnegative. -/
theorem two_density_buchstab_nonneg {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) (u : ℝ) : 0 ≤ ω u := by
  by_cases hu : u < 1
  · rw [hz u hu]
  · exact buchstab_nonneg hω (not_lt.1 hu)

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[1, 2]`, where it
is `1 / u`. -/
theorem two_density_buchstab_lipschitz_low {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 2) : |ω u - ω v| ≤ v - u := by
  rw [hω.2.1 u hu (huv.trans hv), hω.2.1 v (hu.trans huv) hv]
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have he : 1/u - 1/v = (v-u)/(u*v) := by field_simp
  have huv1 : 1 ≤ u*v := by nlinarith
  rw [he, abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
    div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 huv) (sub_nonneg.2 huv1)]

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[2, ∞)`, by the mean
value theorem applied to `v * ω v`, whose derivative is `ω (v - 1)`. -/
theorem two_density_buchstab_lipschitz_high {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) : |ω u - ω v| ≤ v - u := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · simp
  have hc : ContinuousOn (fun w : ℝ => w * ω w) (Set.Icc u v) :=
    continuousOn_id.mul (hω.1.mono (fun w hw => by
      have := hw.1
      simp only [Set.mem_Ici]; linarith))
  obtain ⟨c, hcm, hce⟩ := exists_hasDerivAt_eq_slope (fun w : ℝ => w * ω w)
    (fun w : ℝ => ω (w - 1)) hlt hc
    (fun w hw => hω.2.2 w (by have := hw.1; linarith))
  have hvu : 0 < v - u := by linarith
  have hce' : ω (c - 1) * (v - u) = v * ω v - u * ω u := by
    rw [hce]; field_simp
  have hA0 := two_density_buchstab_nonneg hω hz u
  have hB0 := two_density_buchstab_nonneg hω hz v
  have hC0 := two_density_buchstab_nonneg hω hz (c-1)
  have hA1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz u
  have hB1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz v
  have hC1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz (c-1)
  have hv0 : 0 < v := by linarith
  have hid : v * (ω v - ω u) = (ω (c-1) - ω u) * (v - u) := by linarith
  have hk1 : v * (ω v - ω u) ≤ v * (v - u) := by
    rw [hid]
    nlinarith [mul_nonneg hvu.le (by linarith : 0 ≤ 1 - (ω (c-1) - ω u)),
      mul_nonneg (by linarith : (0:ℝ) ≤ v - 1) hvu.le]
  have hk2 : v * (ω u - ω v) ≤ v * (v - u) := by
    have : v * (ω u - ω v) = (ω u - ω (c-1)) * (v - u) := by linarith
    rw [this]
    nlinarith [mul_nonneg hvu.le (by linarith : 0 ≤ 1 - (ω u - ω (c-1))),
      mul_nonneg (by linarith : (0:ℝ) ≤ v - 1) hvu.le]
  have h1 := le_of_mul_le_mul_left hk1 hv0
  have h2 := le_of_mul_le_mul_left hk2 hv0
  rw [abs_le]
  constructor <;> linarith

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[1, ∞)`. -/
theorem two_density_buchstab_lipschitz {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : |ω u - ω v| ≤ v - u := by
  by_cases hv : v ≤ 2
  · exact two_density_buchstab_lipschitz_low hω hu huv hv
  by_cases hu2 : 2 ≤ u
  · exact two_density_buchstab_lipschitz_high hω hz hu2 huv
  have hv2 : (2:ℝ) ≤ v := by linarith
  have hu2' : u ≤ 2 := by linarith
  have h1 := two_density_buchstab_lipschitz_low hω hu hu2' le_rfl
  have h2 := two_density_buchstab_lipschitz_high hω hz le_rfl hv2
  have ht := abs_sub_le (ω u) (ω 2) (ω v)
  linarith

/-- P0069 page 51 display 5.17. Buchstab's function with the zero extension is measurable. -/
theorem two_density_buchstab_measurable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) : Measurable ω := by
  have h : ω = (Set.Ici (1:ℝ)).piecewise ω (fun _ => 0) := by
    funext u
    by_cases hu : u ∈ Set.Ici (1:ℝ)
    · rw [Set.piecewise_eq_of_mem _ _ _ hu]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hu]
      exact hz u (not_le.1 hu)
  rw [h]
  exact hω.1.measurable_piecewise continuousOn_const measurableSet_Ici

/-- P0069 page 51, the set `E₂`: it is a measurable subset of the plane, as a boolean
combination of closed half planes. -/
theorem two_density_region_measurable (ε : ℝ) :
    MeasurableSet {p : ℝ × ℝ | lowerTwoDiscarded ε p.1 p.2} := by
  have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
      MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
  unfold lowerTwoDiscarded upperPairRegion
  simp only [Set.ofPred_and, Set.ofPred_or, ← Set.compl_ofPred]
  repeat' first
    | apply MeasurableSet.inter
    | apply MeasurableSet.union
    | (apply hle <;> fun_prop)
    | apply MeasurableSet.compl

/-- P0069 page 51 display 5.17. The E2 density integrand is jointly measurable. -/
theorem two_density_integrand_measurable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) (ε s : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      if lowerTwoDiscarded ε p.1 p.2 then ω ((s-p.1-p.2)/p.2)/(p.1*p.2^2) else 0) := by
  have hm := two_density_buchstab_measurable hω hz
  exact Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const

/-- P0069 page 51 display 5.17. The E2 density integrand lies between 0 and 1000. -/
theorem two_density_integrand_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) (s a b : ℝ) :
    0 ≤ (if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) ∧
      (if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) ≤ 1000 := by
  by_cases hD : lowerTwoDiscarded ε a b
  · simp only [hD, ↓reduceIte]
    obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
    have h0 := two_density_buchstab_nonneg hω hz ((s-a-b)/b)
    have h1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
      ((s-a-b)/b)
    have hb2 : (1/100:ℝ) ≤ b^2 := by nlinarith
    have hab : (1/10:ℝ)*(1/100) ≤ a*b^2 :=
      mul_le_mul (by linarith) hb2 (by norm_num) (by linarith)
    have hpos : 0 < a*b^2 := by linarith
    refine ⟨div_nonneg h0 hpos.le, ?_⟩
    rw [div_le_iff₀ hpos]
    linarith
  · simp only [hD, ↓reduceIte]
    norm_num

/-- P0069 page 51 display 5.17. Pointwise comparison of the E2 density integrands at `s ≤ s'`:
off the band where the Buchstab argument crosses 1 the difference is `O(s' - s)`. -/
theorem two_density_pointwise {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) {s s' : ℝ} (hss : s ≤ s') (a b : ℝ)
    (hband : b ∉ Set.Ioc ((s-a)/2) ((s'-a)/2)) :
    |(if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) -
      (if lowerTwoDiscarded ε a b then ω ((s'-a-b)/b)/(a*b^2) else 0)| ≤ 10^4 * (s'-s) := by
  have hΔ : 0 ≤ 10^4 * (s'-s) := by linarith
  by_cases hD : lowerTwoDiscarded ε a b
  · simp only [hD, ↓reduceIte]
    obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
    have hb0 : 0 < b := by linarith
    have hb2 : (1/100:ℝ) ≤ b^2 := by nlinarith
    have hab : (1/10:ℝ)*(1/100) ≤ a*b^2 :=
      mul_le_mul (by linarith) hb2 (by norm_num) (by linarith)
    have hpos : 0 < a*b^2 := by linarith
    have huu : (s-a-b)/b ≤ (s'-a-b)/b := div_le_div_of_nonneg_right (by linarith) hb0.le
    have hdiff : (s'-a-b)/b - (s-a-b)/b = (s'-s)/b := by field_simp; ring
    by_cases hu : 1 ≤ (s-a-b)/b
    · have hL := two_density_buchstab_lipschitz hω hz hu huu
      rw [hdiff] at hL
      have hq : (s'-s)/b ≤ 10*(s'-s) := by
        rw [div_le_iff₀ hb0]
        nlinarith [mul_nonneg (sub_nonneg.2 hss) (by linarith : (0:ℝ) ≤ b - 1/10)]
      rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      nlinarith [mul_nonneg (sub_nonneg.2 hss) (by linarith : (0:ℝ) ≤ a*b^2 - 1/1000)]
    · have hu' : (s-a-b)/b < 1 := not_le.1 hu
      by_cases hv : (s'-a-b)/b < 1
      · rw [hz _ hu', hz _ hv]
        simpa using hΔ
      · exfalso
        apply hband
        rw [div_lt_one hb0] at hu'
        have hv' := (one_le_div hb0).1 (not_lt.1 hv)
        constructor <;> linarith
  · simp only [hD, ↓reduceIte]
    simpa using hΔ

/-- P0069 page 51 display 5.17. For each `a` the inner E2 density integrand is integrable. -/
theorem two_density_inner_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) (s a : ℝ) :
    MeasureTheory.IntegrableOn
      (fun b : ℝ => if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0)
      (Set.Ioc (1/10:ℝ) (1/2)) := by
  have hm : Measurable
      (fun b : ℝ => if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) :=
    (two_density_integrand_measurable hω hz ε s).comp measurable_prodMk_left
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1000) measure_Ioc_lt_top.ne
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have hb := two_density_integrand_bound hω hz hε8 s a b
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- P0069 page 51 display 5.17. For each `a` the inner E2 integrals at `s ≤ s'` differ by
at most `4500 * (s' - s)`: the Lipschitz part plus the band where the Buchstab argument
crosses 1. -/
theorem two_density_inner_diff {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) {s s' : ℝ} (hss : s ≤ s') (a : ℝ) :
    |(∫ b in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) -
      ∫ b in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε a b then ω ((s'-a-b)/b)/(a*b^2) else 0| ≤ 4500 * (s'-s) := by
  refine (two_density_band_bound _ _ (c := (s-a)/2) (d := (s'-a)/2) (K1 := 10^4*(s'-s))
    (K2 := 1000) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (two_density_inner_integrable hω hz hε8 s a)
    (two_density_inner_integrable hω hz hε8 s' a)
    (fun b _ hb => two_density_pointwise hω hz hε8 hss a b hb)
    (fun b _ => ?_)).trans (le_of_eq (by ring))
  have h1 := two_density_integrand_bound hω hz hε8 s a b
  have h2 := two_density_integrand_bound hω hz hε8 s' a b
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- P0069 page 51 display 5.17. The inner E2 integral is interval integrable in `a`. -/
theorem two_density_outer_integrable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) (s : ℝ) :
    IntervalIntegrable (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0)
      MeasureTheory.volume (1/10) (1/2) := by
  have hG : (fun a : ℝ => ∫ b in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) =
      fun a : ℝ => ∫ b in Set.Ioc (1/10:ℝ) (1/2:ℝ),
        if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0 :=
    funext fun a => intervalIntegral.integral_of_le (by norm_num)
  have hm : MeasureTheory.StronglyMeasurable (fun a : ℝ => ∫ b in Set.Ioc (1/10:ℝ) (1/2:ℝ),
        if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := MeasureTheory.volume.restrict (Set.Ioc (1/10:ℝ) (1/2:ℝ)))
      (two_density_integrand_measurable hω hz ε s).stronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1000 * |(1/2:ℝ) - 1/10|)
    measure_Ioc_lt_top.ne (hG ▸ hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => ?_)
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun b _ => ?_
  have hb := two_density_integrand_bound hω hz hε8 s a b
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- P0069 page 51 display 5.17. The E2 density is Lipschitz in `s` for ordered arguments. -/
theorem two_density_lipschitz_ordered {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) {s s' : ℝ} (hss : s ≤ s') :
    |lowerTwoDensityAt ω ε s - lowerTwoDensityAt ω ε s'| ≤ 1800 * (s' - s) := by
  unfold lowerTwoDensityAt
  rw [← intervalIntegral.integral_sub (two_density_outer_integrable hω hz hε8 s)
    (two_density_outer_integrable hω hz hε8 s'), ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 4500 * (s'-s))
    fun a _ => ?_).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs]
    exact two_density_inner_diff hω hz hε8 hss a
  · have : |(1/2:ℝ) - 1/10| = 2/5 := by rw [abs_of_pos] <;> norm_num
    rw [this]; ring

/-- P0069 page 51 display 5.17. Local Lipschitz estimate near one for the E2 density of the
lab normalization factor, the input named in the doc comment of `leaf_factor_increment`. -/
theorem two_density_lipschitz (ω : ℝ → ℝ) (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ ∀ s s' : ℝ, 1 - δ ≤ s → s ≤ 1 → 1 - δ ≤ s' → s' ≤ 1 →
      |lowerTwoDensityAt ω ε s - lowerTwoDensityAt ω ε s'| ≤ L * |s - s'| := by
  refine ⟨1800, 1, by norm_num, by norm_num, fun s s' _ _ _ _ => ?_⟩
  rcases le_total s s' with h | h
  · rw [abs_sub_comm s s', abs_of_nonneg (sub_nonneg.2 h)]
    exact two_density_lipschitz_ordered hω hz hε8 h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact two_density_lipschitz_ordered hω hz hε8 h

/-- P0069 page 51 display 5.17. Buchstab's function with the zero extension is nonnegative. -/
theorem four_density_buchstab_nonneg {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) (u : ℝ) : 0 ≤ ω u := by
  by_cases hu : u < 1
  · rw [hz u hu]
  · exact buchstab_nonneg hω (not_lt.1 hu)

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[1, 2]`, where it
is `1 / u`. -/
theorem four_density_buchstab_lipschitz_low {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 2) : |ω u - ω v| ≤ v - u := by
  rw [hω.2.1 u hu (huv.trans hv), hω.2.1 v (hu.trans huv) hv]
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have he : 1/u - 1/v = (v-u)/(u*v) := by field_simp
  have huv1 : 1 ≤ u*v := by nlinarith
  rw [he, abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
    div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 huv) (sub_nonneg.2 huv1)]

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[2, ∞)`, by the mean
value theorem applied to `v * ω v`, whose derivative is `ω (v - 1)`. -/
theorem four_density_buchstab_lipschitz_high {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) : |ω u - ω v| ≤ v - u := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · simp
  have hc : ContinuousOn (fun w : ℝ => w * ω w) (Set.Icc u v) :=
    continuousOn_id.mul (hω.1.mono (fun w hw => by
      have := hw.1
      simp only [Set.mem_Ici]; linarith))
  obtain ⟨c, hcm, hce⟩ := exists_hasDerivAt_eq_slope (fun w : ℝ => w * ω w)
    (fun w : ℝ => ω (w - 1)) hlt hc
    (fun w hw => hω.2.2 w (by have := hw.1; linarith))
  have hvu : 0 < v - u := by linarith
  have hce' : ω (c - 1) * (v - u) = v * ω v - u * ω u := by
    rw [hce]; field_simp
  have hA0 := four_density_buchstab_nonneg hω hz u
  have hB0 := four_density_buchstab_nonneg hω hz v
  have hC0 := four_density_buchstab_nonneg hω hz (c-1)
  have hA1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz u
  have hB1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz v
  have hC1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz (c-1)
  have hv0 : 0 < v := by linarith
  have hid : v * (ω v - ω u) = (ω (c-1) - ω u) * (v - u) := by linarith
  have hk1 : v * (ω v - ω u) ≤ v * (v - u) := by
    rw [hid]
    nlinarith [mul_nonneg hvu.le (by linarith : 0 ≤ 1 - (ω (c-1) - ω u)),
      mul_nonneg (by linarith : (0:ℝ) ≤ v - 1) hvu.le]
  have hk2 : v * (ω u - ω v) ≤ v * (v - u) := by
    have : v * (ω u - ω v) = (ω u - ω (c-1)) * (v - u) := by linarith
    rw [this]
    nlinarith [mul_nonneg hvu.le (by linarith : 0 ≤ 1 - (ω u - ω (c-1))),
      mul_nonneg (by linarith : (0:ℝ) ≤ v - 1) hvu.le]
  have h1 := le_of_mul_le_mul_left hk1 hv0
  have h2 := le_of_mul_le_mul_left hk2 hv0
  rw [abs_le]
  constructor <;> linarith

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[1, ∞)`, ordered
arguments. -/
theorem four_density_buchstab_lipschitz_ordered {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : |ω u - ω v| ≤ v - u := by
  by_cases hv : v ≤ 2
  · exact four_density_buchstab_lipschitz_low hω hu huv hv
  by_cases hu2 : 2 ≤ u
  · exact four_density_buchstab_lipschitz_high hω hz hu2 huv
  have hv2 : (2:ℝ) ≤ v := by linarith
  have hu2' : u ≤ 2 := by linarith
  have h1 := four_density_buchstab_lipschitz_low hω hu hu2' le_rfl
  have h2 := four_density_buchstab_lipschitz_high hω hz le_rfl hv2
  have ht := abs_sub_le (ω u) (ω 2) (ω v)
  linarith

/-- P0069 page 51 display 5.17. Buchstab's function is 1-Lipschitz on `[1, ∞)`. -/
theorem four_density_buchstab_lipschitz {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) : |ω u - ω v| ≤ |u - v| := by
  rcases le_total u v with h | h
  · rw [abs_sub_comm u v, abs_of_nonneg (sub_nonneg.2 h)]
    exact four_density_buchstab_lipschitz_ordered hω hz hu h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact four_density_buchstab_lipschitz_ordered hω hz hv h

/-- P0069 page 51 display 5.17. Buchstab's function with the zero extension is measurable. -/
theorem four_density_buchstab_measurable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) : Measurable ω := by
  have h : ω = (Set.Ici (1:ℝ)).piecewise ω (fun _ => 0) := by
    funext u
    by_cases hu : u ∈ Set.Ici (1:ℝ)
    · rw [Set.piecewise_eq_of_mem _ _ _ hu]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hu]
      exact hz u (not_le.1 hu)
  rw [h]
  exact hω.1.measurable_piecewise continuousOn_const measurableSet_Ici

/-- P0069 page 51, the set `E₄`: on the conservative region the exponents satisfy
`1/10 ≤ d ≤ c ≤ b ≤ a`, `d ≤ 9/50` and `a + b + c + d ≤ 18/25`. -/
theorem four_density_region_box {ε a b c d : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hR : lowerFourRegion ε a b c d) :
    1/10 ≤ d ∧ d ≤ c ∧ c ≤ b ∧ b ≤ a ∧ d ≤ 9/50 ∧ a+b+c+d ≤ 18/25 := by
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := hR
  norm_num at h1 h6 hε8
  refine ⟨?_, h2, h3, h4, ?_, ?_⟩ <;> linarith

/-- P0069 page 51, the set `E₄`: it is a measurable subset of four space, as a boolean
combination of closed half spaces and slabs. -/
theorem four_density_region_measurable (ε : ℝ) :
    MeasurableSet {p : ((ℝ × ℝ) × ℝ) × ℝ | lowerFourRegion ε p.1.1.1 p.1.1.2 p.1.2 p.2} := by
  have hle : ∀ f g : ((ℝ × ℝ) × ℝ) × ℝ → ℝ, Continuous f → Continuous g →
      MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
  unfold lowerFourRegion lowerFourCovered upperPrimeCovered upperPairRegion
  simp only [Set.ofPred_and, Set.ofPred_or, ← Set.compl_ofPred]
  repeat' first
    | apply MeasurableSet.inter
    | apply MeasurableSet.union
    | (apply hle <;> fun_prop)
    | apply MeasurableSet.compl

/-- P0069 page 51 display 5.17. The E4 density integrand is jointly measurable. -/
theorem four_density_integrand_measurable {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) (ε s : ℝ) :
    Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      if lowerFourRegion ε p.1.1.1 p.1.1.2 p.1.2 p.2 then
        (if (s-p.1.1.1-p.1.1.2-p.1.2-p.2)/p.2 < 1 then 0
          else ω ((s-p.1.1.1-p.1.1.2-p.1.2-p.2)/p.2)/(p.1.1.1*p.1.1.2*p.1.2*p.2^2))
      else 0) := by
  have hm := four_density_buchstab_measurable hω hz
  refine Measurable.ite (four_density_region_measurable ε) ?_ measurable_const
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact measurableSet_lt (by fun_prop) measurable_const

/-- P0069 page 51 display 5.17. The E4 density integrand lies between 0 and `10^5`. -/
theorem four_density_integrand_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b c d : ℝ) :
    |(if lowerFourRegion ε a b c d then
        (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2))
      else 0)| ≤ 10^5 := by
  by_cases hR : lowerFourRegion ε a b c d
  · simp only [hR, ↓reduceIte]
    obtain ⟨hd, hdc, hcb, hba, -, -⟩ := four_density_region_box hε hε8 hR
    by_cases hu : (s-a-b-c-d)/d < 1
    · simp only [hu, ↓reduceIte]; norm_num
    · simp only [hu, ↓reduceIte]
      have h0 := four_density_buchstab_nonneg hω hz ((s-a-b-c-d)/d)
      have h1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
        ((s-a-b-c-d)/d)
      have hd2 : (1/100:ℝ) ≤ d^2 := by nlinarith
      have hab : (1/10:ℝ)*(1/10) ≤ a*b :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
      have habc : (1/10:ℝ)*(1/10)*(1/10) ≤ a*b*c :=
        mul_le_mul hab (by linarith) (by norm_num) (by linarith)
      have hall : (1/10:ℝ)*(1/10)*(1/10)*(1/100) ≤ a*b*c*d^2 :=
        mul_le_mul habc hd2 (by norm_num) (by linarith)
      have hpos : 0 < a*b*c*d^2 := by linarith
      rw [abs_of_nonneg (div_nonneg h0 hpos.le), div_le_iff₀ hpos]
      linarith
  · simp only [hR, ↓reduceIte]
    norm_num

/-- P0069 page 51 display 5.17. Pointwise comparison of the E4 density integrands at
`s, s' ≥ 99/100`: on the region the Buchstab argument stays above one, so the cutoff is never
active and the difference is `O(|s - s'|)`. -/
theorem four_density_pointwise {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {s s' : ℝ} (hs : 99/100 ≤ s)
    (hs' : 99/100 ≤ s') (a b c d : ℝ) :
    |(if lowerFourRegion ε a b c d then
        (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2))
      else 0) -
      (if lowerFourRegion ε a b c d then
        (if (s'-a-b-c-d)/d < 1 then 0 else ω ((s'-a-b-c-d)/d)/(a*b*c*d^2))
      else 0)| ≤ 10^6 * |s - s'| := by
  by_cases hR : lowerFourRegion ε a b c d
  · simp only [hR, ↓reduceIte]
    obtain ⟨hd, hdc, hcb, hba, hd18, hsum⟩ := four_density_region_box hε hε8 hR
    have hd0 : 0 < d := by linarith
    have hu : 1 ≤ (s-a-b-c-d)/d := by rw [one_le_div hd0]; linarith
    have hu' : 1 ≤ (s'-a-b-c-d)/d := by rw [one_le_div hd0]; linarith
    simp only [not_lt.2 hu, not_lt.2 hu', ↓reduceIte]
    have hd2 : (1/100:ℝ) ≤ d^2 := by nlinarith
    have hab : (1/10:ℝ)*(1/10) ≤ a*b :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    have habc : (1/10:ℝ)*(1/10)*(1/10) ≤ a*b*c :=
      mul_le_mul hab (by linarith) (by norm_num) (by linarith)
    have hall : (1/10:ℝ)*(1/10)*(1/10)*(1/100) ≤ a*b*c*d^2 :=
      mul_le_mul habc hd2 (by norm_num) (by linarith)
    have hpos : 0 < a*b*c*d^2 := by linarith
    have hL := four_density_buchstab_lipschitz hω hz hu hu'
    have hdiff : (s-a-b-c-d)/d - (s'-a-b-c-d)/d = (s-s')/d := by field_simp; ring
    rw [hdiff, abs_div, abs_of_pos hd0] at hL
    have hq : |s-s'|/d ≤ 10*|s-s'| := by
      rw [div_le_iff₀ hd0]
      nlinarith [mul_nonneg (abs_nonneg (s-s')) (by linarith : (0:ℝ) ≤ d - 1/10)]
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    nlinarith [mul_nonneg (abs_nonneg (s-s')) (by linarith : (0:ℝ) ≤ a*b*c*d^2 - 1/100000)]
  · simp only [hR, ↓reduceIte]
    simp

open MeasureTheory Set in
/-- P0069 page 51 display 5.17. One level of the nested E4 integral: a jointly measurable
bounded integrand has a measurable and bounded parametric interval integral. -/
theorem four_density_level {α : Type*} [MeasurableSpace α] (φ : α → ℝ → ℝ)
    (hm : Measurable (fun p : α × ℝ => φ p.1 p.2)) {M : ℝ} (hM : ∀ x y, |φ x y| ≤ M)
    (lo hi : ℝ) :
    Measurable (fun x => ∫ y in lo..hi, φ x y) ∧
      ∀ x, |∫ y in lo..hi, φ x y| ≤ M * |hi - lo| := by
  constructor
  · have h1 := (StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc lo hi)) hm.stronglyMeasurable).measurable
    have h2 := (StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc hi lo)) hm.stronglyMeasurable).measurable
    exact h1.sub h2
  · intro x
    rw [← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => by
      rw [Real.norm_eq_abs]; exact hM x y

open MeasureTheory Set in
/-- P0069 page 51 display 5.17. One level of the nested E4 integral: two jointly measurable
bounded integrands within `K` of each other have parametric interval integrals within
`K * |hi - lo|`. -/
theorem four_density_level_diff {α : Type*} [MeasurableSpace α] (φ ψ : α → ℝ → ℝ)
    (hφ : Measurable (fun p : α × ℝ => φ p.1 p.2))
    (hψ : Measurable (fun p : α × ℝ => ψ p.1 p.2)) {M K : ℝ}
    (hφM : ∀ x y, |φ x y| ≤ M) (hψM : ∀ x y, |ψ x y| ≤ M)
    (hK : ∀ x y, |φ x y - ψ x y| ≤ K) (lo hi : ℝ) (x : α) :
    |(∫ y in lo..hi, φ x y) - ∫ y in lo..hi, ψ x y| ≤ K * |hi - lo| := by
  have hint : ∀ χ : α → ℝ → ℝ, Measurable (fun p : α × ℝ => χ p.1 p.2) →
      (∀ x y, |χ x y| ≤ M) → IntervalIntegrable (χ x) volume lo hi := by
    intro χ hχ hχM
    have hmx : Measurable (χ x) := hχ.comp measurable_prodMk_left
    have hb : ∀ s : Set ℝ, ∀ᵐ y ∂(volume.restrict s), ‖χ x y‖ ≤ M :=
      fun s => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hχM x y
    exact ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmx.aestronglyMeasurable
        (hb _),
      Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmx.aestronglyMeasurable (hb _)⟩
  rw [← intervalIntegral.integral_sub (hint φ hφ hφM) (hint ψ hψ hψM), ← Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => by
    rw [Real.norm_eq_abs]; exact hK x y

/-- P0069 page 51 display 5.17. Four nested levels: two jointly measurable bounded integrands
on four space within `K` of each other have fourfold iterated integrals within
`K * |hi - lo| ^ 4`. -/
theorem four_density_nested (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hf : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ => f p.1.1.1 p.1.1.2 p.1.2 p.2))
    (hg : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ => g p.1.1.1 p.1.1.2 p.1.2 p.2))
    {M K : ℝ} (hfM : ∀ a b c d, |f a b c d| ≤ M) (hgM : ∀ a b c d, |g a b c d| ≤ M)
    (hK : ∀ a b c d, |f a b c d - g a b c d| ≤ K) (lo hi : ℝ) :
    |(∫ a in lo..hi, ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, f a b c d) -
      ∫ a in lo..hi, ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, g a b c d| ≤
      K * |hi - lo| ^ 4 := by
  -- level d
  have f1 := four_density_level (fun (q : (ℝ × ℝ) × ℝ) d => f q.1.1 q.1.2 q.2 d) hf
    (fun q d => hfM _ _ _ _) lo hi
  have g1 := four_density_level (fun (q : (ℝ × ℝ) × ℝ) d => g q.1.1 q.1.2 q.2 d) hg
    (fun q d => hgM _ _ _ _) lo hi
  have d1 := four_density_level_diff (fun (q : (ℝ × ℝ) × ℝ) d => f q.1.1 q.1.2 q.2 d)
    (fun (q : (ℝ × ℝ) × ℝ) d => g q.1.1 q.1.2 q.2 d) hf hg
    (fun q d => hfM _ _ _ _) (fun q d => hgM _ _ _ _) (fun q d => hK _ _ _ _) lo hi
  -- level c
  have f2 := four_density_level
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, f r.1 r.2 c d) f1.1 (fun r c => f1.2 (r, c)) lo hi
  have g2 := four_density_level
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, g r.1 r.2 c d) g1.1 (fun r c => g1.2 (r, c)) lo hi
  have d2 := four_density_level_diff
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, f r.1 r.2 c d)
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, g r.1 r.2 c d) f1.1 g1.1
    (fun r c => f1.2 (r, c)) (fun r c => g1.2 (r, c)) (fun r c => d1 (r, c)) lo hi
  -- level b
  have f3 := four_density_level
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, f a b c d) f2.1
    (fun a b => f2.2 (a, b)) lo hi
  have g3 := four_density_level
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, g a b c d) g2.1
    (fun a b => g2.2 (a, b)) lo hi
  have d3 := four_density_level_diff
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, f a b c d)
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, g a b c d) f2.1 g2.1
    (fun a b => f2.2 (a, b)) (fun a b => g2.2 (a, b)) (fun a b => d2 (a, b)) lo hi
  -- level a
  have d4 := four_density_level_diff
    (fun (_ : Unit) a => ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, f a b c d)
    (fun (_ : Unit) a => ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, g a b c d)
    (f3.1.comp measurable_snd) (g3.1.comp measurable_snd)
    (fun _ a => f3.2 a) (fun _ a => g3.2 a) (fun _ a => d3 a) lo hi ()
  refine d4.trans (le_of_eq ?_)
  ring

/-- P0069 page 51 display 5.17. Local Lipschitz estimate near one for the E4 density of the
lab normalization factor, the input named in the doc comment of `leaf_factor_increment`. -/
theorem four_density_lipschitz (ω : ℝ → ℝ) (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω) (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ ∀ s s' : ℝ, 1 - δ ≤ s → s ≤ 1 → 1 - δ ≤ s' → s' ≤ 1 →
      |lowerFourDensityAt ω ε s - lowerFourDensityAt ω ε s'| ≤ L * |s - s'| := by
  refine ⟨10^6, 1/100, by norm_num, by norm_num, fun s s' hs _ hs' _ => ?_⟩
  have hs1 : (99/100:ℝ) ≤ s := by linarith
  have hs1' : (99/100:ℝ) ≤ s' := by linarith
  have h := four_density_nested
    (fun a b c d => if lowerFourRegion ε a b c d then
        (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2)) else 0)
    (fun a b c d => if lowerFourRegion ε a b c d then
        (if (s'-a-b-c-d)/d < 1 then 0 else ω ((s'-a-b-c-d)/d)/(a*b*c*d^2)) else 0)
    (four_density_integrand_measurable hω hz ε s)
    (four_density_integrand_measurable hω hz ε s')
    (fun a b c d => four_density_integrand_bound hω hz hε hε8 s a b c d)
    (fun a b c d => four_density_integrand_bound hω hz hε hε8 s' a b c d)
    (fun a b c d => four_density_pointwise hω hz hε hε8 hs1 hs1' a b c d)
    (lowerFourGridReal 0) (lowerFourGridReal 128)
  have hlen : |lowerFourGridReal 128 - lowerFourGridReal 0| ^ 4 ≤ 1 := by
    have : |lowerFourGridReal 128 - lowerFourGridReal 0| ≤ 1 := by
      rw [abs_le]
      norm_num [lowerFourGridReal, lowerFourGridPoint]
    exact pow_le_one₀ (abs_nonneg _) this
  unfold lowerFourDensityAt
  refine h.trans ?_
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 10^6 * |s - s'|)
    (sub_nonneg.2 hlen)]

/-- P0069 page 51 display 5.17, partial summation against the lab factor: the clipping map
`t ↦ max 0 (min 1 t)` used in `lowerFactor` is 1-Lipschitz. -/
theorem clip_lipschitz (t t' : ℝ) :
    |max 0 (min 1 t) - max 0 (min 1 t')| ≤ |t - t'| := by
  obtain ⟨h1, h2⟩ := abs_le.mp (le_refl |t - t'|)
  have h3 := abs_nonneg (t - t')
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- P0069 page 51 display 5.17, partial summation against the lab factor: the increment of
`c / V` between two values of the density `V` that both stay within `|v0| / 2` of `v0 ≠ 0`. -/
theorem recip_increment {v0 c Vi Vj D : ℝ} (hv : v0 ≠ 0) (hi : |Vi - v0| ≤ |v0| / 2)
    (hj : |Vj - v0| ≤ |v0| / 2) (hc : |c| ≤ 2 * |v0|) (hD : |Vi - Vj| ≤ D) :
    |c / Vj - c / Vi| ≤ 8 * D / |v0| := by
  have ha : 0 < |v0| := abs_pos.mpr hv
  have hVi : |v0| / 2 ≤ |Vi| := by
    have := abs_sub_abs_le_abs_sub v0 Vi
    rw [abs_sub_comm] at this; linarith
  have hVj : |v0| / 2 ≤ |Vj| := by
    have := abs_sub_abs_le_abs_sub v0 Vj
    rw [abs_sub_comm] at this; linarith
  have hVi0 : Vi ≠ 0 := abs_pos.mp (by linarith)
  have hVj0 : Vj ≠ 0 := abs_pos.mp (by linarith)
  have e : c / Vj - c / Vi = c * (Vi - Vj) / (Vi * Vj) := by field_simp
  have hpos : 0 < |Vi| * |Vj| := mul_pos (by linarith) (by linarith)
  rw [e, abs_div, abs_mul, abs_mul, div_le_div_iff₀ hpos ha]
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have h1 : |c| * |Vi - Vj| ≤ 2 * |v0| * D := mul_le_mul hc hD (abs_nonneg _) (by linarith)
  have h2 : |v0| / 2 * (|v0| / 2) ≤ |Vi| * |Vj| :=
    mul_le_mul hVi hVj (by linarith) (abs_nonneg _)
  calc |c| * |Vi - Vj| * |v0| ≤ 2 * |v0| * D * |v0| := mul_le_mul_of_nonneg_right h1 ha.le
    _ = 8 * D * (|v0| / 2 * (|v0| / 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)

/-- P0069 page 51 display 5.17: for an integer `m` in the dyadic range `Y / 2 ≤ m ≤ 2 Y` the
exponent `log m / log Z` with `Z = 4 Y` is at most one and within `4 / log Z` of one. -/
theorem log_ratio_near_one {Y : ℝ} (hY : 3 ≤ Y) (m : ℕ) (h1 : Y / 2 ≤ m) (h2 : (m : ℝ) ≤ 2 * Y) :
    Real.log m / Real.log (4 * Y) ≤ 1 ∧
      1 - Real.log m / Real.log (4 * Y) ≤ 4 / Real.log (4 * Y) := by
  have hYp : 0 < Y := by linarith
  have hm : 0 < (m : ℝ) := by linarith
  have hlZ : Real.log (4 * Y) = Real.log 4 + Real.log Y := Real.log_mul (by norm_num) hYp.ne'
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hl4p : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hup : Real.log m ≤ Real.log (4 * Y) := Real.log_le_log hm (by linarith)
  have hlow : Real.log Y - Real.log 2 ≤ Real.log m := by
    rw [← Real.log_div hYp.ne' (by norm_num)]; exact Real.log_le_log (by positivity) h1
  have hZp : 0 < Real.log (4 * Y) := by linarith
  refine ⟨(div_le_one hZp).mpr hup, ?_⟩
  rw [one_sub_div hZp.ne']
  exact div_le_div_of_nonneg_right (by linarith) hZp.le

/-- P0069 page 51 display 5.17 after partial summation against the lab factor: the local slope
estimate for `lowerFactor` on the integer interval from floor Y to floor 2Y, deduced from
Lipschitz bounds near one for the E2 and E4 densities of pages 51 and 52. -/
theorem factor_increment_of_lipschitz (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (h2 : ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ ∀ s s' : ℝ, 1 - δ ≤ s → s ≤ 1 → 1 - δ ≤ s' → s' ≤ 1 →
      |lowerTwoDensityAt ω ε s - lowerTwoDensityAt ω ε s'| ≤ L * |s - s'|)
    (h4 : ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ ∀ s s' : ℝ, 1 - δ ≤ s → s ≤ 1 → 1 - δ ≤ s' → s' ≤ 1 →
      |lowerFourDensityAt ω ε s - lowerFourDensityAt ω ε s'| ≤ L * |s - s'|) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 1 ≤ x →
      ∀ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤
          1 / (2 * x ^ (11 / 20 + ε)) := by
  obtain ⟨L2, δ2, hL2, hδ2, H2⟩ := h2
  obtain ⟨L4, δ4, hL4, hδ4, H4⟩ := h4
  by_cases hv : lowerV0 ω ε = 0
  · refine ⟨0, fun x _ hx i _ => ?_⟩
    have h0 : ∀ m : ℕ, lowerFactor ω ε x m = 0 := by
      intro m; unfold lowerFactor; rw [hv]; simp
    rw [h0, h0, sub_zero, abs_zero]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) (11 / 20 + ε)
    exact div_nonneg zero_le_one (by linarith)
  · have ha : 0 < |lowerV0 ω ε| := abs_pos.mpr hv
    obtain ⟨δ, hδeq⟩ : ∃ δ, δ = min (min δ2 δ4) (1 / 2) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδeq]; exact lt_min (lt_min hδ2 hδ4) (by norm_num)
    have hδ2' : δ ≤ δ2 := by rw [hδeq]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ4' : δ ≤ δ4 := by rw [hδeq]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδh : δ ≤ 1 / 2 := by rw [hδeq]; exact min_le_right _ _
    obtain ⟨L0, hL0eq⟩ : ∃ L0, L0 = 4 + L2 + L4 := ⟨_, rfl⟩
    have hL0 : 0 < L0 := by linarith
    have hLip : ∀ s s' : ℝ, 1 - δ ≤ s → s ≤ 1 → 1 - δ ≤ s' → s' ≤ 1 →
        |lowerDensityAt ω ε s - lowerDensityAt ω ε s'| ≤ L0 * |s - s'| := by
      intro s s' hs hs1 hs' hs1'
      have e2 := abs_le.mp (H2 s s' (by linarith) hs1 (by linarith) hs1')
      have e4 := abs_le.mp (H4 s s' (by linarith) hs1 (by linarith) hs1')
      have hsp : (1 / 2 : ℝ) ≤ s := by linarith
      have hsp' : (1 / 2 : ℝ) ≤ s' := by linarith
      have hprod : (1 / 4 : ℝ) ≤ s * s' := by nlinarith
      have e1 : |1 / s - 1 / s'| ≤ 4 * |s - s'| := by
        have hs0 : s ≠ 0 := by linarith
        have hs0' : s' ≠ 0 := by linarith
        have e : 1 / s - 1 / s' = (s' - s) / (s * s') := by field_simp
        rw [e, abs_div, abs_of_pos (show 0 < s * s' by linarith), div_le_iff₀ (by linarith),
          abs_sub_comm s' s]
        nlinarith [abs_nonneg (s - s'), mul_nonneg (abs_nonneg (s - s'))
          (show (0 : ℝ) ≤ s * s' - 1 / 4 by linarith)]
      have e1' := abs_le.mp e1
      unfold lowerDensityAt
      rw [abs_le, hL0eq]
      constructor <;> linarith [e1'.1, e1'.2, e2.1, e2.2, e4.1, e4.2]
    obtain ⟨K, hKeq⟩ : ∃ K, K = max 3 (max (4 / δ) (32 * L0 / |lowerV0 ω ε|)) := ⟨_, rfl⟩
    have hK3 : 3 ≤ K := by rw [hKeq]; exact le_max_left _ _
    have hKδ : 4 / δ ≤ K := by
      rw [hKeq]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hKa : 32 * L0 / |lowerV0 ω ε| ≤ K := by
      rw [hKeq]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨Real.exp (2 * K), fun x hC hx i hi => ?_⟩
    have hxp : 0 < x := by linarith
    have hlogx : 2 * K ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hC
      rwa [Real.log_exp] at this
    obtain ⟨Y, hYeq⟩ : ∃ Y, Y = x ^ (11 / 20 + ε) := ⟨_, rfl⟩
    have hYp : 0 < Y := by rw [hYeq]; exact Real.rpow_pos_of_pos hxp _
    have hlY : Real.log Y = (11 / 20 + ε) * Real.log x := by
      rw [hYeq]; exact Real.log_rpow hxp _
    have hKY : K ≤ Real.log Y := by
      rw [hlY]
      nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ Real.log x by linarith)]
    have hlYp : 0 < Real.log Y := by linarith
    have hY3 : 3 ≤ Y := by
      have h1 := Real.add_one_le_exp (Real.log Y)
      rw [Real.exp_log hYp] at h1; linarith
    have hZ : scaleZ ε x = 4 * Y := by rw [hYeq]; rfl
    have hlZ : Real.log (4 * Y) = Real.log 4 + Real.log Y :=
      Real.log_mul (by norm_num) hYp.ne'
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have hl4p : 0 < Real.log 4 := Real.log_pos (by norm_num)
    obtain ⟨lZ, hlZeq⟩ : ∃ lZ, lZ = Real.log (4 * Y) := ⟨_, rfl⟩
    have hKZ : K ≤ lZ := by linarith
    have hZY : lZ ≤ 2 * Real.log Y := by linarith
    have hlZp : 0 < lZ := by linarith
    have h4δ : 4 / lZ ≤ δ := by
      rw [div_le_iff₀ hlZp]
      have h := (div_le_iff₀ hδ).mp hKδ
      have h' := mul_le_mul_of_nonneg_right hKZ hδ.le
      linarith
    have hLa : L0 * (4 / lZ) ≤ |lowerV0 ω ε| / 2 := by
      have h := (div_le_iff₀ ha).mp hKa
      have h' := mul_le_mul_of_nonneg_right hKZ ha.le
      rw [← mul_div_assoc, div_le_iff₀ hlZp]
      linarith
    have hm : ∀ m : ℕ, Y / 2 ≤ m → (m : ℝ) ≤ 2 * Y →
        1 - δ ≤ Real.log m / lZ ∧ Real.log m / lZ ≤ 1 ∧
          |lowerDensityAt ω ε (Real.log m / lZ) - lowerV0 ω ε| ≤ |lowerV0 ω ε| / 2 := by
      intro m h1 h2
      obtain ⟨hs1, hs2⟩ := log_ratio_near_one hY3 m h1 h2
      rw [← hlZeq] at hs1 hs2
      have hsδ : 1 - δ ≤ Real.log m / lZ := by linarith
      refine ⟨hsδ, hs1, ?_⟩
      have h := hLip _ 1 hsδ hs1 (by linarith) le_rfl
      rw [lowerDensityAt_one] at h
      have habs : |Real.log m / lZ - 1| = 1 - Real.log m / lZ := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [habs] at h
      calc _ ≤ L0 * (1 - Real.log m / lZ) := h
        _ ≤ L0 * (4 / lZ) := mul_le_mul_of_nonneg_left hs2 hL0.le
        _ ≤ |lowerV0 ω ε| / 2 := hLa
    rw [← hYeq] at hi ⊢
    rw [Finset.mem_Ico] at hi
    have hi1 : Y - 1 < (i : ℝ) :=
      lt_of_lt_of_le (Nat.sub_one_lt_floor Y) (by exact_mod_cast hi.1)
    have hi2 : ((i + 1 : ℕ) : ℝ) ≤ 2 * Y :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt hi.2) (Nat.floor_le (by linarith))
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hip : 0 < (i : ℝ) := by linarith
    have hA := hm i (by linarith) (by rw [hcast] at hi2; linarith)
    have hB := hm (i + 1) (by rw [hcast]; linarith) hi2
    have hds : |Real.log (i : ℝ) / lZ - Real.log ((i + 1 : ℕ) : ℝ) / lZ| ≤ (2 / Y) / lZ := by
      rw [← sub_div, abs_div, abs_of_pos hlZp]
      apply div_le_div_of_nonneg_right _ hlZp.le
      rw [hcast]
      have hle : Real.log (i : ℝ) ≤ Real.log ((i : ℝ) + 1) := Real.log_le_log hip (by linarith)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have h := Real.log_le_sub_one_of_pos (show 0 < ((i : ℝ) + 1) / i from div_pos (by linarith) hip)
      rw [Real.log_div (by linarith) hip.ne'] at h
      have h' : ((i : ℝ) + 1) / i - 1 = 1 / i := by field_simp; ring
      have h'' : 1 / (i : ℝ) ≤ 2 / Y := by rw [div_le_div_iff₀ hip hYp]; linarith
      linarith
    have hD := hLip _ _ hA.1 hA.2.1 hB.1 hB.2.1
    have hD' : |lowerDensityAt ω ε (Real.log (i : ℝ) / lZ) -
        lowerDensityAt ω ε (Real.log ((i + 1 : ℕ) : ℝ) / lZ)| ≤ L0 * ((2 / Y) / lZ) :=
      le_trans hD (mul_le_mul_of_nonneg_left hds hL0.le)
    have hc : |lowerV0 ω ε * lZ / Real.log Y| ≤ 2 * |lowerV0 ω ε| := by
      rw [abs_div, abs_mul, abs_of_pos hlZp, abs_of_pos hlYp, div_le_iff₀ hlYp]
      have := mul_le_mul_of_nonneg_left hZY (abs_nonneg (lowerV0 ω ε))
      linarith
    have hrec := recip_increment hv hA.2.2 hB.2.2 hc hD'
    unfold lowerFactor
    rw [hZ, ← hYeq, ← hlZeq, div_mul_eq_div_div, div_mul_eq_div_div]
    refine le_trans (clip_lipschitz _ _) (le_trans hrec ?_)
    rw [div_le_div_iff₀ ha (by linarith)]
    have h := (div_le_iff₀ ha).mp hKa
    have h' := mul_le_mul_of_nonneg_right hKZ ha.le
    have e : 8 * (L0 * (2 / Y / lZ)) * (2 * Y) = 32 * L0 / lZ := by field_simp; ring
    rw [e, one_mul, div_le_iff₀ hlZp]
    linarith

/-- P0069 page 51 display 5.17 after partial summation against the lab factor.
The local slope estimate is needed only on the integer interval from floor Y to floor 2Y.
The paper does not define this factor. Its local Buchstab density needs a positive lower bound
and a Lipschitz estimate near one to justify this bound. PROVED here from
`factor_increment_of_lipschitz`, `two_density_lipschitz` and `four_density_lipschitz`. -/
theorem leaf_factor_increment (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 1 ≤ x →
      ∀ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤
          1 / (2 * x ^ (11 / 20 + ε)) := by
  exact factor_increment_of_lipschitz ω hε hε8 (two_density_lipschitz ω hω hz hε hε8)
    (four_density_lipschitz ω hω hz hε hε8)

/-- P0069 page 51 display 5.17. Sum the local increment bound across the integer interval.
CONDITIONAL on the local density regularity estimate for the lab normalization factor. -/
theorem leaf_factor_variation (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤ 1 := by
  obtain ⟨C0, h0⟩ := leaf_factor_increment ω hω hz hε hε8
  refine ⟨max C0 1, fun x hx => ?_⟩
  have hx0 : C0 ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hU : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by positivity)
  have hcard : ((Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊
      ⌊2 * x ^ (11 / 20 + ε)⌋₊).card : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
    rw [Nat.card_Ico]
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hU
  calc _ ≤ ∑ _i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊
        ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / (2 * x ^ (11 / 20 + ε)) :=
      Finset.sum_le_sum fun i hi => h0 x hx0 hx1 i hi
    _ = ((Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊
        ⌊2 * x ^ (11 / 20 + ε)⌋₊).card : ℝ) *
          (1 / (2 * x ^ (11 / 20 + ε))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * x ^ (11 / 20 + ε)) * (1 / (2 * x ^ (11 / 20 + ε))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 := by field_simp

/-- P0069 page 51 display 5.17 and page 3 display 1.8.
CONDITIONAL on a nonprincipal prefix estimate and the variation bound for the lab factor.
Partial summation preserves every logarithmic saving and doubles the bound. -/
theorem weighted_nonprincipal_transfer (ω : ℝ → ℝ) (ε : ℝ) (a : ℝ → ℕ → ℝ)
    (hraw : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (a x m : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (hvar : ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤ 1) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * a x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, h0⟩ := hraw A hA
  obtain ⟨Cv, hv⟩ := hvar
  let K := max (max C0 Cv) 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have h0K : C0 ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hvK : Cv ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨2 * K, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hxK : K ≤ x := by linarith
  have hx1 : 1 ≤ x := hK1.trans hxK
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hp : ∀ u : ℝ, u ≤ 2 * x ^ (11 / 20 + ε) →
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u),
        (a x m : ℂ) * χ (m : ZMod q)‖ ≤ K * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    intro u hu
    exact (h0 x (h0K.trans hxK) q hq hqA χ hχ u hu).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h0K hscale)
  have hb := normalized_term_bound ω ε x χ (a x)
    (R := K * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (by rw [mul_assoc]; exact mul_nonneg (by linarith) hscale) ht hp
    (hv x (hvK.trans hxK))
  calc _ ≤ 2 * (K * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hb
    _ = _ := by ring

/-- LEAF. P0069 Section 5 page 51 display 5.17 and page 3 display 1.8.
The prime term of 5.15 after multiplication by the lab normalization factor. Siegel Walfisz and partial summation are required.
This concerns the explicit sealed coefficient only. CONDITIONAL on the corresponding raw estimate and the factor increment leaf. -/
theorem leaf_nonprincipal_prime (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * primeWeight m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact weighted_nonprincipal_transfer ω ε (fun _ m => primeWeight m)
    (leaf_prime_siegel_walfisz hε hε8) (leaf_factor_variation ω hω hz hε hε8)

/-- LEAF. P0069 Section 5 page 51 display 5.17 and page 3 display 1.8.
The E2 rough number term subtracted on page 51. Expand the rough variable into ordered prime factors and use Siegel Walfisz in its last prime variable.
This concerns the explicit sealed coefficient only. CONDITIONAL on the corresponding raw estimate and the factor increment leaf. -/
theorem leaf_nonprincipal_two_rough (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact weighted_nonprincipal_transfer ω ε (lowerTwoTerms ε)
    (leaf_two_rough_siegel_walfisz hε hε8) (leaf_factor_variation ω hω hz hε hε8)

/-- LEAF. P0069 Section 5 page 51 display 5.17 and page 3 display 1.8.
The E4 rough number term subtracted on page 51. The four outer prime factors remain fixed while Siegel Walfisz treats the last prime in the rough variable.
This concerns the explicit sealed coefficient only. CONDITIONAL on the corresponding raw estimate and the factor increment leaf. -/
theorem leaf_nonprincipal_four_rough (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  exact weighted_nonprincipal_transfer ω ε (lowerFourTerms ε)
    (leaf_four_rough_siegel_walfisz hε hε8) (leaf_factor_variation ω hω hz hε hε8)

end LeanLab.BHP1997.Decomp514a
