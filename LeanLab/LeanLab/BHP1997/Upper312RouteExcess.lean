/-
P0069 Baker, Harman and Pintz 1997, page 3 condition iii display 1.8, and page 53.
Audit lemmas for the OPEN leaf upper_short_coefficient of DecompC165dBase312, which is
SUSPECTED FALSE. They reduce the suspected falsity of the leaf to one explicit inequality on
the page 53 raw weight: a recurring excess of size c Y / (log x)^2 of the total raw weight
over J above the count of J times v1 / log Y. That inequality is a HYPOTHESIS here.
These lemmas neither prove nor refute the leaf by themselves. The leaf stays OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Upper312RouteNecessary

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex DecompC165b DecompC165d

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8 at the trivial character
and at t = 2Y, and page 53, "so that rho(m) <= b1(m)", for an ARBITRARY weight f in place of
the raw page 53 weight. If b satisfies condition iii with density v and dominates f on J for
large x, then the total of f over J is at most the count of J times v / log Y, up to
Y L^(-A). Audit lemma: it helps reduce the suspected falsity of the OPEN leaf
upper_short_coefficient to one explicit inequality on the page 53 raw weight, and it neither
proves nor refutes that leaf by itself. PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `Σ_{m ∈ J} f(m) ≤ #J v / log Y + C Y L^(-A)` for x ≥ C. -/
theorem short_majorant_total_le {ε v : ℝ} {f b : ℝ → ℕ → ℝ}
    (hdist : Task308.ShortDistribution ε v b)
    (hmaj : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, f x m ≤ b x m) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ m ∈ rightInterval ε x, f x m ≤
        ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε)) +
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hCe, hC⟩ := short_distribution_real_prefix hdist A hA
  obtain ⟨X, hX⟩ := hmaj
  refine ⟨max C X, fun x hx => ?_⟩
  have hxC : C ≤ x := (le_max_left _ _).trans hx
  have hxX : X ≤ x := (le_max_right _ _).trans hx
  have hxe : Real.exp 1 ≤ x := hCe.trans hxC
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (by linarith) _
  have hconst : C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
      max C X * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY) hL
  have h2Y : (0 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
  have hfilter : (rightInterval ε x).filter
      (fun m : ℕ => (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε)) = rightInterval ε x := by
    apply Finset.filter_true_of_mem
    intro m hm
    have h1 : m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := (Finset.mem_Ioc.mp hm).2
    have h2 : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le h2Y
    have h3 : (m : ℝ) ≤ ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    exact h3.trans h2
  have h1 := (le_abs_self _).trans (hC x hxC (2 * x ^ (11 / 20 + ε)) le_rfl)
  rw [hfilter] at h1
  have hsum : ∑ m ∈ rightInterval ε x, f x m ≤ ∑ m ∈ rightInterval ε x, b x m :=
    Finset.sum_le_sum fun m hm => hX x hxX m hm
  have hsplit : ∑ m ∈ rightInterval ε x, (b x m - v / Real.log (x ^ (11 / 20 + ε))) =
      ∑ m ∈ rightInterval ε x, b x m -
        ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsplit] at h1
  linarith

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8 at the trivial character
and at t = 2Y, and page 53, "so that rho(m) <= b1(m)", for an ARBITRARY weight f in place of
the raw page 53 weight. Generic refutation: if for arbitrarily large x the total of f over J
exceeds the count of J times v / log Y by at least c Y / (log x)^2 with c > 0, then no
coefficient b satisfies condition iii with density v and dominates f on J for large x.
The excess is a HYPOTHESIS. Audit lemma: it reduces the suspected falsity of the OPEN leaf
upper_short_coefficient to one explicit inequality on the page 53 raw weight, and it neither
proves nor refutes that leaf by itself. PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `c Y / L^2 ≤ Σ_{m ∈ J} f(m) - #J v / log Y` infinitely often contradicts
`Σ_{m ∈ J} f(m) - #J v / log Y ≤ C Y L^(-3)`. -/
theorem short_majorant_false_of_excess {ε v c : ℝ} {f : ℝ → ℕ → ℝ} (hc : 0 < c)
    (hex : ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * x ^ (11 / 20 + ε) / (Real.log x) ^ 2 ≤
        ∑ m ∈ rightInterval ε x, f x m -
          ((rightInterval ε x).card : ℝ) * v / Real.log (x ^ (11 / 20 + ε))) :
    ¬ ∃ b : ℝ → ℕ → ℝ, Task308.ShortDistribution ε v b ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, f x m ≤ b x m := by
  rintro ⟨b, hdist, hmaj⟩
  obtain ⟨C, hC⟩ := short_majorant_total_le hdist hmaj 3 (by norm_num)
  obtain ⟨x, hx, hexx⟩ := hex (max (max C (Real.exp 1)) (Real.exp (C / c) + 1))
  have hxC : C ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxe : Real.exp 1 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxE : Real.exp (C / c) < x := by
    have := (le_max_right (max C (Real.exp 1)) (Real.exp (C / c) + 1)).trans hx
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hlog0 : 0 < Real.log x := by linarith
  have hlogC : C / c < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr hxE
  have hCL : C < c * Real.log x := by
    have := (div_lt_iff₀ hc).mp hlogC
    linarith
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hpow : Real.log x ^ (-3 : ℝ) = (Real.log x ^ 3)⁻¹ := by
    rw [Real.rpow_neg hlog0.le]
    norm_cast
  have hup := hC x hxC
  rw [hpow] at hup
  have hL3 : 0 < Real.log x ^ 3 := pow_pos hlog0 3
  have hmain : c * x ^ (11 / 20 + ε) / (Real.log x) ^ 2 ≤
      C * x ^ (11 / 20 + ε) * (Real.log x ^ 3)⁻¹ := by linarith
  have hrew : c * x ^ (11 / 20 + ε) / (Real.log x) ^ 2 =
      c * Real.log x * x ^ (11 / 20 + ε) * (Real.log x ^ 3)⁻¹ := by
    field_simp
  rw [hrew] at hmain
  have h4 : c * Real.log x * x ^ (11 / 20 + ε) ≤ C * x ^ (11 / 20 + ε) :=
    le_of_mul_le_mul_right hmain (inv_pos.mpr hL3)
  have h5 : c * Real.log x ≤ C := le_of_mul_le_mul_right h4 hY
  linarith

/-- P0069 Baker Harman Pintz 1997, page 3, condition iii, display 1.8 at the trivial character
and at t = 2Y, and page 53, "so that rho(m) <= b1(m)", with the page 53 raw weight and the
page 53 density v1 = omega(1/c4)/c4 + deleted integral. If for arbitrarily large x the total
of the raw page 53 weight over J exceeds the count of J times v1 / log Y by at least
c Y / (log x)^2 with c > 0, then the conclusion of the OPEN leaf upper_short_coefficient of
DecompC165dBase312, copied verbatim, is false: no such b1 exists. The excess is a HYPOTHESIS
and is not established here. Audit lemma: it reduces the suspected falsity of that leaf to
one explicit inequality on the page 53 raw weight, and it neither proves nor refutes the leaf
by itself. PROVED. AI wrote the Lean code. Goldbach is open.
Plain math: `c Y / L^2 ≤ Σ_{m ∈ J} raw(m) - #J v1 / log Y` infinitely often excludes b1. -/
theorem upper_short_coefficient_false_of_excess {ω : ℝ → ℝ} {B ε c : ℝ} (hc : 0 < c)
    (hex : ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧
      c * x ^ (11 / 20 + ε) / (Real.log x) ^ 2 ≤
        ∑ m ∈ rightInterval ε x, upperRawWeight ε (x ^ (11 / 20 + ε)) m -
          ((rightInterval ε x).card : ℝ) *
            (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
              upperDeletedIntegral ω ε) /
            Real.log (x ^ (11 / 20 + ε))) :
    ¬ ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤ b1 x m := by
  rintro ⟨b1, -, hdist, -, hmaj⟩
  exact short_majorant_false_of_excess
    (f := fun x m => upperRawWeight ε (x ^ (11 / 20 + ε)) m) hc hex ⟨b1, hdist, hmaj⟩

end LeanLab.BHP1997.Upper312Route
