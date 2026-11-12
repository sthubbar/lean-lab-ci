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
OPEN here: display 5.17 for the principal character, its non-principal analogue, and
display 1.9 through Lemma 29 and 5.18 to 5.23.
These three leaves are about this one explicit family, not about an arbitrary family, so the
CODEX refutation `sealed_exceptional_leaf_type_false` of the old general transfer does not apply.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Total
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

/-! ### The analytic leaves -/

/-- LEAF, OPEN. P0069 Baker Harman Pintz 1997, Section 5, page 51, display 5.17, "a
straightforward consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`",
in the form condition iii of Theorem 2, display 1.8 on page 3, takes for the principal
character. With the U-1624 factor the density is the constant `v0 / log Y`. The prime factors of
every term exceed `Z ^ c1`, so the principal character modulo `q ≤ L^A` is one on the support
for large `x`. -/
theorem lower_principal_distribution (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
            lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF, OPEN. P0069 Baker Harman Pintz 1997, Section 5, page 51, display 5.17 and page 3,
display 1.8, the non-principal characters: here `δχ = 0`. This is the Siegel-Walfisz form of
the prime number theorem used for 5.17, applied to each term of display 5.15, whose rough
factors have no prime factor below `Z ^ c1`. -/
theorem lower_nonprincipal_distribution (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF, OPEN. P0069 Baker Harman Pintz 1997, Section 5, page 52, displays 5.18 to 5.23,
condition iv of Theorem 2, display 1.9 on page 3, for b0. Lemmas 33 to 35 on pages 48 to 50 give
5.1 and 5.2 for every retained term of 5.15, Lemma 29 on page 43 then gives 5.18 and 5.19,
and 5.20 to 5.23 replace `W(y, z)` by `z y v0 / log Y`. The U-1624 factor is constant to
within `L^(-K)` on blocks of length `Y L^(-K)`, which is how it passes through Lemma 29.
CONDITIONAL on the cited Theorem 4 and Lemma 9, the inputs of Lemmas 29 to 35. -/
theorem lower_exceptional_mean_square (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-! ### Assembly of condition iii -/

/-- P0069 Baker Harman Pintz 1997, page 3, display 1.8 for b0, with 5.17 on page 51: the principal and non-principal cases together. -/
theorem lower_short_distribution (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := lower_principal_distribution ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := lower_nonprincipal_distribution ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) 1, fun x hx q hq hqA χ t ht => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hY : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have := Real.rpow_nonneg hx0.le (11 / 20 + ε)
    have hl : 0 ≤ Real.log x := Real.log_nonneg (le_trans (le_max_right _ _) hx)
    have := Real.rpow_nonneg hl (-A)
    positivity
  have hm1 : C1 ≤ max (max C1 C2) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hm2 : C2 ≤ max (max C1 C2) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  by_cases hχ : χ = 1
  · subst hχ
    have h := hC1 x hx1 q hq hqA t ht
    have hd : Thm2.delta (1 : DirichletCharacter ℂ q) = 1 := by simp [Thm2.delta]
    rw [hd, one_mul]
    calc _ ≤ C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := h
      _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hm1 hY
  · have h := hC2 x hx2 q hq hqA χ hχ t ht
    have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
    rw [hd, zero_mul, zero_div]
    simp only [sub_zero]
    calc _ ≤ C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := h
      _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hm2 hY

end LeanLab.BHP1997.LowerShortC165
