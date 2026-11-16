/-
Split of `leaf_section4Block_mean_value_positive_large` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value.
The sealed statement stays exactly as it is and this file never uses it.

The claim is the mean value of display 4.1 for the concrete tapered block, at the positive
height alone and over the wider printed exponent region. The split cuts it into the three
ingredients the estimate actually uses. First, the two endpoints of the height range are
ordered and that range is at most x^(1/2) long. Second, the L1 integral in the height is
controlled by the L2 mean square over the same range through Cauchy-Schwarz. Third, the L2
mean square itself is asserted on the three subregions of the exponent geometry (m at most
0.45 with n at most 0.225; m at least 0.45 with n at most 0.225; and n at least 0.225),
which together cover exactly the region hypothesis of the sealed statement.

Each leaf is strictly easier than the sealed statement. The first two are elementary
inequalities about real functions with no arithmetic content at all, so neither mentions the
block, the characters or the coefficients. Each of the three mean square leaves carries two
extra hypotheses cutting one subregion out of the printed region, so it asserts the estimate
on a strict subset of the parameter range, with a strictly smaller set of exponent pairs to
control. None of the five restates the sealed statement, which needs the whole region at
once, and none assumes it.

None is vacuous. The region hypotheses of the three mean square leaves are met at m = n = 0,
at m = 1/2 and n = 1/10, and at m = 1/10 and n = 3/10 respectively; the divisor hypotheses
are met by the zero coefficient families, which also meet every conclusion, so no conclusion
is contradicted; and the endpoint leaf is a statement about the real functions
exp((log x)^(1/3)) and x^(0.45 - 2ε/3) alone, with the explicit threshold 1/200 and the
explicit range x at least e^30.

The assembly takes the minimum of the two thresholds, resolves the exponent region by the
three-way case split on m at 0.45 and n at 0.225, and finishes each case with the same
private step: Cauchy-Schwarz in the height, the length replaced by x^(1/2), and the two
occurrences of x^(1/4) multiplied out to x^(1/2).
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- LEAF 1 of 5. Step: the endpoints of the height range are ordered and the range is at
most x^(1/2) long. The lower endpoint exp((log x)^(1/3)) is nonnegative; it is at most the
upper endpoint x^(0.45 - 2ε/3) once log x is at least 30, because the cube root of the
logarithm is then smaller than 0.4 log x and the exponent 0.45 - 2ε/3 stays above 0.4 for
ε below 1/200; and the distance between them is at most x^(1/2), since the upper endpoint is
already at most x^(1/2). This is the pure real-variable step that makes the mean square
usable, and it carries no arithmetic input. -/
theorem leaf_section4Block_positive_large_endpoints :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η → ∀ x : ℝ, Real.exp 30 ≤ x →
      0 ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) ∧
        Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (0.45 - 2 * ε / 3) ∧
          x ^ (0.45 - 2 * ε / 3) - Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 2 : ℝ) := by
  sorry

/-- LEAF 2 of 5. Step: Cauchy-Schwarz in the height. For a nonnegative function on a range
whose endpoints are ordered, the square of the integral is at most the length of the range
times the integral of the square. This is the general inequality that converts the L2 mean
square into the L1 bound the sealed statement asks for; it mentions no particular function,
so it is strictly weaker than any bound on the block. -/
theorem leaf_section4Block_positive_large_cauchy_schwarz (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : ∀ t, 0 ≤ f t) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  sorry

/-- LEAF 3 of 5. Step: the L2 mean square of the block over the height range, on the
subregion where the first exponent m is at most 0.45 and the second exponent n is at most
0.225. The conclusion is the mean square only, at the size x^(1/2) (log x)^(-2A) rewritten
as a square, so it is a strict restatement of no more than one factor of the sealed bound,
and it is asked for on one of the three subregions. The hypotheses on m and n are
compatible: m = n = 0 satisfies them together with the region hypothesis. -/
theorem leaf_section4Block_positive_large_mean_square_low
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A)
    (m n : ℝ) (hm0 : 0 ≤ m) (hn0 : 0 ≤ n)
    (hreg : max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775)
    (hm45 : m ≤ 0.45) (hn225 : n ≤ 0.225)
    (a b : ℝ → ℕ → ℝ)
    (ha : ∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B)
    (hb : ∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖ ^ 2) ≤
        (C * x ^ (1 / 4 : ℝ) * Real.log x ^ (-A)) ^ 2 := by
  sorry

/-- LEAF 4 of 5. Step: the same L2 mean square on the subregion where the first exponent m
is at least 0.45 and the second exponent n is still at most 0.225. Here the region
hypothesis forces m at most 0.55, so this is the subregion where the first factor is allowed
to grow; it is a different range of exponent pairs from leaf 3, so neither implies the
other. Compatible: m = 1/2 and n = 1/10 satisfy every hypothesis. -/
theorem leaf_section4Block_positive_large_mean_square_m_high
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A)
    (m n : ℝ) (hm0 : 0 ≤ m) (hn0 : 0 ≤ n)
    (hreg : max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775)
    (hm45 : 0.45 ≤ m) (hn225 : n ≤ 0.225)
    (a b : ℝ → ℕ → ℝ)
    (ha : ∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B)
    (hb : ∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖ ^ 2) ≤
        (C * x ^ (1 / 4 : ℝ) * Real.log x ^ (-A)) ^ 2 := by
  sorry

/-- LEAF 5 of 5. Step: the same L2 mean square on the subregion where the second exponent n
is at least 0.225, the case in which both factors may be large. The region hypothesis then
forces n at most 0.325 and the first exponent m at most 0.55, so this is the third and last
of the exponent cases. Compatible: m = 1/10 and n = 3/10 satisfy every hypothesis. -/
theorem leaf_section4Block_positive_large_mean_square_n_high
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A)
    (m n : ℝ) (hm0 : 0 ≤ m) (hn0 : 0 ≤ n)
    (hreg : max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775)
    (hn225 : 0.225 ≤ n)
    (a b : ℝ → ℕ → ℝ)
    (ha : ∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B)
    (hb : ∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖ ^ 2) ≤
        (C * x ^ (1 / 4 : ℝ) * Real.log x ^ (-A)) ^ 2 := by
  sorry

/-- The two elementary steps followed by one mean square bound, with a full proof. The
squared Cauchy-Schwarz inequality bounds the square of the height integral by the length of
the range times the mean square; the length is at most x^(1/2) and the mean square is at
most the square of C x^(1/4) (log x)^(-A); the two factors x^(1/4) multiply to x^(1/2), so
the square of the height integral is at most the square of C x^(1/2) (log x)^(-A), and the
square root is taken through `abs_le_of_sq_le_sq'`. The range x at least e^30 makes every
power nonnegative, so nothing is lost in that step. -/
private theorem positive_large_of_mean_square (ε A : ℝ) (m n : ℝ) (a b : ℝ → ℕ → ℝ)
    (hend : ∀ x : ℝ, Real.exp 30 ≤ x →
      0 ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) ∧
        Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (0.45 - 2 * ε / 3) ∧
          x ^ (0.45 - 2 * ε / 3) - Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 2 : ℝ))
    (hms : ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖ ^ 2) ≤
        (C * x ^ (1 / 4 : ℝ) * Real.log x ^ (-A)) ^ 2) :
    ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖) ≤
        C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨C, X, hC, H⟩ := hms
  refine ⟨C, max X (Real.exp 30), ?_⟩
  intro x hx q hq hlog χ
  have hx30 : Real.exp 30 ≤ x := le_trans (le_max_right _ _) hx
  have hXx : X ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨he0, heu, hlen⟩ := hend x hx30
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 30) hx30
  have hone : (1 : ℝ) ≤ Real.exp 30 := by linarith [Real.add_one_le_exp 30]
  have hx1 : 1 ≤ x := le_trans hone hx30
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog0 _
  have hxq : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hxhalf : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hq2 : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num]
  have hK : 0 ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg hC hxhalf) hL
  have hPi : 0 ≤ ∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume) heu (fun t => sq_nonneg _)
  have hcs := leaf_section4Block_positive_large_cauchy_schwarz
    (fun t => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t‖)
    (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (0.45 - 2 * ε / 3)) heu
    (fun t => norm_nonneg _)
  have hmsq := H x hXx q hq hlog χ
  have hkey : x ^ (1 / 2 : ℝ) * (C * x ^ (1 / 4 : ℝ) * Real.log x ^ (-A)) ^ 2 =
      (C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) ^ 2 := by
    rw [← hq2]
    ring
  have hstep : (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
      ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
          (k : ℂ) ^ Thm4.half t‖) ^ 2 ≤
      (C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) ^ 2 := by
    calc (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half t‖) ^ 2
        ≤ (x ^ (0.45 - 2 * ε / 3) - Real.exp (Real.log x ^ (1 / 3 : ℝ))) *
            ∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖ ^ 2 := hcs
      _ ≤ x ^ (1 / 2 : ℝ) *
            ∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hlen hPi
      _ ≤ x ^ (1 / 2 : ℝ) * (C * x ^ (1 / 4 : ℝ) * Real.log x ^ (-A)) ^ 2 :=
          mul_le_mul_of_nonneg_left hmsq hxhalf
      _ = (C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) ^ 2 := hkey
  exact (abs_le_of_sq_le_sq' hstep hK).2

/-- The assembly, with nothing open. The same statement as the sealed leaf, proved from the
five leaves above and never from the sealed leaf. The threshold is the minimum of the leaf
threshold and 1/200; the exponent region is resolved by the three-way case split on m at
0.45 and n at 0.225, which is exhaustive; and each case then runs the same private step from
the endpoints, the Cauchy-Schwarz inequality and its own mean square bound. -/
theorem leaf_section4Block_mean_value_positive_large_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half t‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η₀, hη₀, H₀⟩ := leaf_section4Block_positive_large_endpoints
  refine ⟨min η₀ (1 / 200), lt_min hη₀ (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hreg a b ha hb A hA
  have hε₀ : ε < η₀ := lt_of_lt_of_le hεη (min_le_left _ _)
  have hend : ∀ x : ℝ, Real.exp 30 ≤ x →
      0 ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) ∧
        Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (0.45 - 2 * ε / 3) ∧
          x ^ (0.45 - 2 * ε / 3) - Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 2 : ℝ) :=
    fun x hx => H₀ ε hε hε₀ x hx
  by_cases hn225 : n ≤ 0.225
  · by_cases hm45 : m ≤ 0.45
    · exact positive_large_of_mean_square ε A m n a b hend
        (leaf_section4Block_positive_large_mean_square_low h4 B hB ε A hε hA m n hm0 hn0
          hreg hm45 hn225 a b ha hb)
    · push Not at hm45
      exact positive_large_of_mean_square ε A m n a b hend
        (leaf_section4Block_positive_large_mean_square_m_high h4 B hB ε A hε hA m n hm0 hn0
          hreg hm45.le hn225 a b ha hb)
  · push Not at hn225
    exact positive_large_of_mean_square ε A m n a b hend
      (leaf_section4Block_positive_large_mean_square_n_high h4 B hB ε A hε hA m n hm0 hn0
        hreg hn225.le a b ha hb)

end LeanLab.BHP1997.Decomp528a
