/-
Split S129 burst-20261122 of `leaf_upper_sifted_tapered` in
LeanLab.BHP1997.Decomp312bFeed1122UpperSupply, P0069 Section 4, pages 41 and 42.

The parent leaf asks for a free tapered family `b` that agrees with the sifted
family on I and on I1. Here `b` is no longer free: it is the sifted family times
an explicit smooth taper of `k / x`, a Mathlib `ContDiffBump` centred at 9/8 with
inner radius 3/8 and outer radius 1/2. The taper is 1 on [3/4, 3/2] and vanishes
outside (5/8, 13/8), so it is supported strictly inside the range (x/2, 2x] of
display 4.1. PROVED below with no sorry: the taper bounds, the divisor bound of
`b` from that of the sifted family, and the agreement of `b` with the sifted family
on I and on I1 for all large `x`. What remains is the single LEAF
`leaf_upper_sieve_majorant_tapered`: the page 41 to 42 construction with Lemma 17 c
and Lemma 28, the final density u1 < 1.0001, and the mean value 4.1 for this one
explicit tapered family.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312bFeed1122UpperSupply

namespace LeanLab.BHP1997.Decomp312bFeed1122
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- The page 42 taper used by this split: a smooth bump on the real line, centred at
9/8 with inner radius 3/8 and outer radius 1/2. -/
noncomputable abbrev upperTaperBump : ContDiffBump (9 / 8 : ℝ) :=
  ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩

/-- LEAF: P0069 pages 41 and 42, the upper seven step Buchstab construction with the
final identity of page 41, Lemma 17 c and Lemma 28 for the discarded C5 regions, the
final density count u1 < 1.0001 of page 42, and display 4.1 of page 24 for the
explicit taper `upperTaperBump (k / x)` times the sifted family, by Theorem 4 through
Lemmas 10 and 12 to 17. For fixed `ε ∈ (0, 1/10]` it supplies `u1 ∈ [1, 1.0001)` and
the sifted coefficient family `c1` with its divisor bound, the I1 density, the
eventual domination of the prime indicator on I, and the mean value 4.1 of the
tapered family. Class HARD. Strictly smaller than the parent: the tapered family is
fixed, and its divisor bound and agreement on I and I1 are proved here. -/
theorem leaf_upper_sieve_majorant_tapered (h4 : Thm4.Theorem4Paper) (B0 : ℝ)
    (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ (u1 : ℝ) (c1 : ℝ → ℕ → ℝ),
      1 ≤ u1 ∧ u1 < 1.0001 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε (fun x k => upperTaperBump ((k : ℝ) / x) * section4SiftedFamily c1 x k) ∧
      ReferenceDensity u1 (section4SiftedFamily c1) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        primeWeight k ≤ section4SiftedFamily c1 x k) := by
  sorry

/-- The taper takes values in [0, 1]. PROVED. -/
theorem upperTaper_abs_le_one (r : ℝ) : |upperTaperBump r| ≤ 1 := by
  rw [abs_of_nonneg (upperTaperBump.nonneg' r)]
  exact upperTaperBump.le_one

/-- The taper is smooth. PROVED. -/
theorem upperTaper_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => upperTaperBump r) :=
  upperTaperBump.contDiff

/-- The taper vanishes outside (5/8, 13/8), strictly inside (1/2, 2). PROVED. -/
theorem upperTaper_support :
    Function.support (fun r : ℝ => upperTaperBump r) = Metric.ball (9 / 8 : ℝ) (1 / 2) :=
  upperTaperBump.support_eq

/-- The taper is 1 on [3/4, 3/2]. PROVED. -/
theorem upperTaper_eq_one {r : ℝ} (h1 : 3 / 4 ≤ r) (h2 : r ≤ 3 / 2) :
    upperTaperBump r = 1 := by
  apply upperTaperBump.one_of_mem_closedBall
  have hr : upperTaperBump.rIn = (3 / 8 : ℝ) := rfl
  rw [Metric.mem_closedBall, Real.dist_eq, hr, abs_le]
  constructor <;> linarith

/-- On an interval `(⌊a⌋, ⌊x⌋]` with `a ≥ 3x/4`, the taper of `k / x` is 1. PROVED. -/
theorem upperTaper_eq_one_of_mem {x a : ℝ} (hx : 0 < x) (ha : 3 / 4 * x ≤ a) {k : ℕ}
    (hk : k ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊) : upperTaperBump ((k : ℝ) / x) = 1 := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
  have hlow : a < (k : ℝ) := Nat.lt_of_floor_lt hk1
  have hup : (k : ℝ) ≤ x := le_trans (by exact_mod_cast hk2) (Nat.floor_le hx.le)
  apply upperTaper_eq_one
  · rw [le_div_iff₀ hx]; linarith
  · rw [div_le_iff₀ hx]; linarith

/-- For large `x` the left end of I is at least 3x/4. PROVED. -/
theorem eventually_left_end_I (ε : ℝ) (hε10 : ε ≤ 1 / 10) :
    ∀ᶠ x : ℝ in atTop, 3 / 4 * x ≤ x - 2 * x ^ (11 / 20 + ε) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 20)).eventually_ge_atTop 8,
    eventually_ge_atTop (1 : ℝ)] with x h8 hx1
  have hx0 : 0 < x := by linarith
  have hmono : x ^ (11 / 20 + ε) ≤ x ^ (13 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsplit : x = x ^ (13 / 20 : ℝ) * x ^ (7 / 20 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hpos : 0 ≤ x ^ (13 / 20 : ℝ) := Real.rpow_nonneg hx0.le _
  have : 8 * x ^ (13 / 20 : ℝ) ≤ x := by
    calc 8 * x ^ (13 / 20 : ℝ) ≤ x ^ (7 / 20 : ℝ) * x ^ (13 / 20 : ℝ) :=
          mul_le_mul_of_nonneg_right h8 hpos
      _ = x := by rw [mul_comm]; exact hsplit.symm
  linarith

/-- For large `x` the left end of I1 is at least 3x/4. PROVED. -/
theorem eventually_left_end_I1 :
    ∀ᶠ x : ℝ in atTop, 3 / 4 * x ≤ x - referenceWidth x := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have hL3 : 1 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have he : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ Real.exp (-3) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have hm3 : Real.exp (-3) ≤ 1 / 4 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have hw : referenceWidth x ≤ x * (1 / 4) := by
    unfold referenceWidth
    exact mul_le_mul_of_nonneg_left (he.trans hm3) hx0.le
  linarith

/-- The exact statement of `leaf_upper_sifted_tapered`, from the single LEAF
`leaf_upper_sieve_majorant_tapered` with no other sorry. -/
theorem leaf_upper_sifted_tapered_split (h4 : Thm4.Theorem4Paper) (B0 : ℝ) (hB0 : 1 ≤ B0)
    (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
      1 ≤ u1 ∧ u1 < 1.0001 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u1 (section4SiftedFamily c1) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        primeWeight k ≤ section4SiftedFamily c1 x k) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        b x k = section4SiftedFamily c1 x k) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        b x k = section4SiftedFamily c1 x k) := by
  obtain ⟨u1, c1, hu, hu', ⟨C, hC⟩, hm, hd, hdom⟩ :=
    leaf_upper_sieve_majorant_tapered h4 B0 hB0 ε hε hε10
  refine ⟨u1, c1, fun x k => upperTaperBump ((k : ℝ) / x) * section4SiftedFamily c1 x k,
    hu, hu', ⟨C, hC⟩, ⟨C, fun x k => ?_⟩, hm, hd, hdom, ?_, ?_⟩
  · rw [abs_mul]
    calc |upperTaperBump ((k : ℝ) / x)| * |section4SiftedFamily c1 x k|
        ≤ 1 * |section4SiftedFamily c1 x k| :=
          mul_le_mul_of_nonneg_right (upperTaper_abs_le_one _) (abs_nonneg _)
      _ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0 := by rw [one_mul]; exact hC x k
  · filter_upwards [eventually_left_end_I ε hε10, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    intro k hk
    have : upperTaperBump ((k : ℝ) / x) = 1 := by
      unfold leftInterval at hk
      exact upperTaper_eq_one_of_mem hx0 hx hk
    simp only [this, one_mul]
  · filter_upwards [eventually_left_end_I1, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    intro k hk
    have : upperTaperBump ((k : ℝ) / x) = 1 := upperTaper_eq_one_of_mem hx0 hx hk
    simp only [this, one_mul]

end LeanLab.BHP1997.Decomp312bFeed1122
