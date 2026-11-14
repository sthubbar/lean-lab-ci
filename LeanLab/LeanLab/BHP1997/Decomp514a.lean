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

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Abel514
import LeanLab.BHP1997.Prime514
import LeanLab.BHP1997.Rough308
import LeanLab.BHP1997.Decomp308a
import LeanLab.BHP1997.DecompC165dBase312

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

/-- LEAF. P0069 page 51 display 5.17 and page 3 display 1.8.
The nonprincipal prime number theorem input for this one unnormalized term of 5.15.
For a rough term this requires the ordered prime expansion of its rough variable.
The prime input and the two rough inputs are separate. OPEN analytic input. -/
theorem leaf_two_rough_siegel_walfisz {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF. P0069 page 51 display 5.17 and page 3 display 1.8.
The nonprincipal prime number theorem input for this one unnormalized term of 5.15.
For a rough term this requires the ordered prime expansion of its rough variable.
The prime input and the two rough inputs are separate. OPEN analytic input. -/
theorem leaf_four_rough_siegel_walfisz {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF. P0069 page 51 display 5.17 after partial summation against the lab factor.
The local slope estimate is needed only on the integer interval from floor Y to floor 2Y.
The paper does not define this factor. Its local Buchstab density needs a positive lower bound
and a Lipschitz estimate near one to justify this bound. OPEN analytic input. -/
theorem leaf_factor_increment (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 1 ≤ x →
      ∀ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤
          1 / (2 * x ^ (11 / 20 + ε)) := by
  sorry

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
