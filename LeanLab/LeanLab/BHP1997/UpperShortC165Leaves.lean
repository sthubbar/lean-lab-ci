/-
P0069 Baker Harman Pintz 1997, Section 5, page 53, with display 5.17 on page 51 and displays 5.18 to 5.23 on page 52.
Faithful split of the OPEN leaf `upper_short_coefficient` of DecompC165dBase312.
The elementary pieces are PROVED here: the identity raw b1 = psi(m, Y^c4) + deleted part,
the bound of at most 18 prime factors at least Y^c1 for m <= 2Y, the resulting uniform
bound for the raw weight on J, its nonnegativity on J, and the assembly.
The analytic input, display 5.17 from the prime number theorem with the Buchstab integrals and
the mean square 1.9 via Lemma 29, Theorem 4 and Lemma 9, is one LEAF, CITED-LEFT.
The assembly `upper_short_coefficient_of_leaf` has exactly the statement of
`upper_short_coefficient`; the old sorry stays, since this file imports DecompC165dBase312.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- P0069, page 53. The deleted part of k_m: the terms of k_m for which Lemma 33 applies to no
arrangement, so that b1 = psi(m, Y^c4) plus this part. -/
noncomputable def upperDeletedSum (ε Y : ℝ) (m : ℕ) : ℝ :=
  upperK ε Y m - upperKept ε Y m

/-- P0069, page 53, "We obtain b1(m) from psi(m, Y^c4) by deleting from k_m the terms ...":
b1(m) = psi(m, Y^c4) + the deleted part of k_m. This is the split behind the two summands of
v1 = w(1/c4)/c4 + the integral over E. PROVED. -/
theorem upper_raw_eq_rough_add_deleted (ε : ℝ) {Y : ℝ} (hY : 1 ≤ Y) (m : ℕ) :
    upperRawWeight ε Y m = upperRough m (Y ^ upperC4 ε) + upperDeletedSum ε Y m := by
  rw [upper_rough_four_term ε hY m]
  unfold upperRawWeight upperDeletedSum
  ring

/-- P0069, page 53. The sifting indicator psi is at most one. -/
theorem upperRough_le_one (n : ℕ) (w : ℝ) : upperRough n w ≤ 1 := by
  unfold upperRough; split_ifs <;> norm_num

/-- P0069, page 53. The raw weight b1 is nonnegative on J for Y >= 1, since it is at least
psi(m, Y^c4). PROVED. -/
theorem upper_raw_nonneg (ε : ℝ) {Y : ℝ} (hY : 1 ≤ Y) (m : ℕ) :
    0 ≤ upperRawWeight ε Y m := by
  have h := upper_four_term_le_raw ε Y m
  rw [← upper_rough_four_term ε hY m] at h
  exact (upperRough_nonneg _ _).trans h

/-- P0069, page 53. Distinct prime factors of m that are all at least w have product at most m,
so w to the power of their number is at most m. PROVED. -/
theorem upper_large_primes_pow_le {w : ℝ} (hw : 0 ≤ w) {m : ℕ} (hm : m ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ m.primeFactors) (hSw : ∀ p ∈ S, w ≤ (p : ℝ)) :
    w ^ S.card ≤ (m : ℝ) := by
  have hdvd : (∏ p ∈ S, p) ∣ m :=
    (Finset.prod_dvd_prod_of_subset S m.primeFactors (fun p => p) hS).trans
      (Nat.prod_primeFactors_dvd m)
  have hle : (∏ p ∈ S, p) ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
  calc w ^ S.card = ∏ _p ∈ S, w := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, (p : ℝ) := by gcongr with p hp; exact hSw p hp
    _ = ((∏ p ∈ S, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (m : ℝ) := by exact_mod_cast hle

/-- P0069, page 53 with page 50: c1 = (1 + 7 theta2)/15 - eps is at least 1/9 for eps <= 10^-8. -/
theorem upperC1_ge {ε : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) : 1 / 9 ≤ upperC1 ε := by
  unfold upperC1; norm_num at hε8 ⊢; linarith

/-- P0069, page 53. Every prime in the sums for g, h, j, k is at least Y^c1 with c1 >= 1/9,
and m <= 2Y <= Y^2, so at most 18 distinct such primes divide m. PROVED. -/
theorem upper_large_prime_card_le {ε Y : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) (hY : 2 ≤ Y)
    {m : ℕ} (hm : m ≠ 0) (hmY : (m : ℝ) ≤ 2 * Y)
    (S : Finset ℕ) (hS : S ⊆ m.primeFactors) (hSw : ∀ p ∈ S, Y ^ upperC1 ε ≤ (p : ℝ)) :
    S.card ≤ 18 := by
  have hY0 : 0 < Y := by linarith
  have h1 := upper_large_primes_pow_le (Real.rpow_nonneg hY0.le _) hm S hS hSw
  rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le] at h1
  have h2 : (m : ℝ) ≤ Y ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
  have h3 : upperC1 ε * (S.card : ℝ) ≤ 2 :=
    (Real.rpow_le_rpow_left_iff (by linarith)).mp (h1.trans h2)
  have h4 := upperC1_ge hε8
  have h5 : (S.card : ℝ) ≤ 18 := by nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  exact_mod_cast h5

/-- A sum of terms in [0, a] over a finset with at most N elements is in [0, N a]. -/
theorem upper_sum_bound {S : Finset ℕ} {f : ℕ → ℝ} {a : ℝ} {N : ℕ} (ha : 0 ≤ a)
    (hN : S.card ≤ N)
    (hf : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ a) : 0 ≤ ∑ p ∈ S, f p ∧ ∑ p ∈ S, f p ≤ N * a := by
  refine ⟨Finset.sum_nonneg fun p hp => (hf p hp).1, ?_⟩
  calc ∑ p ∈ S, f p ≤ ∑ _p ∈ S, a := Finset.sum_le_sum fun p hp => (hf p hp).2
    _ = S.card * a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * a := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) ha

/-- P0069, page 53. The divisor bound for the raw b1 on m <= 2Y with Y >= 2:
|b1(m)| <= 1 + 18 + 18^2 + 18^3, since g is at most 1 and h, j and the kept part of k are sums
over at most 18, 18^2 and 18^3 tuples of primes at least Y^c1, each term in [0, 1]. PROVED. -/
theorem upper_raw_abs_le {ε Y : ℝ} (hε8 : ε ≤ 1 / 10 ^ 8) (hY : 2 ≤ Y)
    {m : ℕ} (hm : m ≠ 0) (hmY : (m : ℝ) ≤ 2 * Y) :
    |upperRawWeight ε Y m| ≤ 1 + 18 + 18 ^ 2 + 18 ^ 3 := by
  have hcard : ∀ n : ℕ, n ∣ m → ∀ P : ℕ → Prop,
      ((n.primeFactors.filter fun p : ℕ => Y ^ upperC1 ε ≤ (p : ℝ) ∧ P p).card ≤ 18) := by
    intro n hn P
    apply upper_large_prime_card_le hε8 hY hm hmY
    · intro p hp
      exact Nat.primeFactors_mono hn hm (Finset.mem_filter.mp hp).1
    · intro p hp; exact (Finset.mem_filter.mp hp).2.1
  have hdivp : ∀ {n p : ℕ}, p ∈ n.primeFactors → n / p ∣ n := fun hp =>
    Nat.div_dvd_of_dvd (Nat.mem_primeFactors.mp hp).2.1
  -- the three nested ranges
  have hG := upperRough_nonneg m (Y ^ upperC1 ε)
  have hG' := upperRough_le_one m (Y ^ upperC1 ε)
  have hH : 0 ≤ upperH ε Y m ∧ upperH ε Y m ≤ (18 : ℕ) * 1 := by
    unfold upperH
    exact upper_sum_bound (by positivity) (hcard m dvd_rfl _)
      (fun p _ => ⟨upperRough_nonneg _ _, upperRough_le_one _ _⟩)
  have hJ : 0 ≤ upperJ ε Y m ∧ upperJ ε Y m ≤ (18 : ℕ) * ((18 : ℕ) * 1) := by
    unfold upperJ
    apply upper_sum_bound (by positivity) (hcard m dvd_rfl _)
    intro p1 hp1
    exact upper_sum_bound (by positivity) (hcard (m / p1) (hdivp (Finset.mem_filter.mp hp1).1) _)
      (fun p _ => ⟨upperRough_nonneg _ _, upperRough_le_one _ _⟩)
  have hK : 0 ≤ upperKept ε Y m ∧
      upperKept ε Y m ≤ (18 : ℕ) * ((18 : ℕ) * ((18 : ℕ) * 1)) := by
    unfold upperKept
    apply upper_sum_bound (by positivity) (hcard m dvd_rfl _)
    intro p1 hp1
    have h1 := hdivp (Finset.mem_filter.mp hp1).1
    apply upper_sum_bound (by positivity) (hcard (m / p1) h1 _)
    intro p2 hp2
    apply upper_sum_bound (by positivity) (hcard (m / p1 / p2) ((hdivp (Finset.mem_filter.mp hp2).1).trans h1) _)
    intro p3 _
    split_ifs
    · exact ⟨upperRough_nonneg _ _, upperRough_le_one _ _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  unfold upperRawWeight upperG
  push_cast at hH hJ hK
  rw [abs_le]
  constructor <;> nlinarith [hH.1, hH.2, hJ.1, hJ.2, hK.1, hK.2]

/-- P0069, page 53 with Audit1624 and U-1624. The coefficient used for b1 in the lab: the raw
page 53 weight times a normalizing factor lam, on J, for Y = x^(11/20+eps) >= 2, and zero
elsewhere. -/
noncomputable def upperNormCoeff (ε : ℝ) (lam : ℝ → ℕ → ℝ) (x : ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
    lam x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m
  else 0

/-- LEAF, OPEN, CITED-LEFT. P0069 Baker Harman Pintz 1997, Section 5, page 53, with display 5.17
on page 51 and displays 5.18 to 5.23 on page 52.
Analytic input for b1: "We use Lemma 34 to obtain (5.1) and (5.2) for g_m, h_m and j_m",
Lemma 33 for the kept part of k_m, "the constant v = v1 in (1.8) is seen to be
w(1/c4)/c4 + the integral over E from the prime number theorem", and "We may now repeat for
b1(m) the argument" of 5.18 to 5.23, which uses Lemma 29, Theorem 4 and Lemma 9.
The prime number theorem in short intervals with the Buchstab integrals is a citation wall.
The normalizing factor lam is the U-1624 slowly varying rescaling: Audit1624 proves that the raw
weight itself cannot satisfy condition iii with a constant center, so lam is bounded and at
least one on J eventually. See the QUESTION in research/burst-20261112/BHP1997-upper_short_coefficient.md:
lam at least one with the exact density v1 may be too strong at second order. -/
theorem upper_normalized_raw_conditions
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam) ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam) := by
  sorry

/-- P0069, page 3: for x >= 4 the parameter Y = x^(11/20+eps) is at least 2. -/
theorem upper_Y_ge_two {ε x : ℝ} (hε : 0 < ε) (hx : 4 ≤ x) : 2 ≤ x ^ (11 / 20 + ε) := by
  have hx1 : 1 ≤ x := by linarith
  have h1 : x ^ (1 / 2 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have h3 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- P0069, page 53 with page 3 condition ii: the divisor bound for the normalized coefficient,
with B >= 0, from the raw bound `upper_raw_abs_le` and the bound on lam. PROVED. -/
theorem upper_norm_coeff_divisor_bound {ε B : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hlam : ∀ x m, |lam x m| ≤ Λ) :
    ∃ C : ℝ, ∀ x k, |upperNormCoeff ε lam x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (hlam 0 0)
  refine ⟨Λ * (1 + 18 + 18 ^ 2 + 18 ^ 3), fun x k => ?_⟩
  have hC : 0 ≤ Λ * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by positivity
  unfold upperNormCoeff
  split_ifs with h
  · obtain ⟨hY, hk⟩ := h
    have hk' := Finset.mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkY : (k : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
      have : (k : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hk'.2
      exact this.trans (Nat.floor_le (by linarith))
    have hraw := upper_raw_abs_le hε8 hY hk0 hkY
    have hd : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      have : 1 ≤ k.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd k, hk0⟩⟩
      exact_mod_cast this
    have hdB : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.one_le_rpow hd hB
    rw [abs_mul]
    calc |lam x k| * |upperRawWeight ε (x ^ (11 / 20 + ε)) k|
        ≤ Λ * (1 + 18 + 18 ^ 2 + 18 ^ 3) :=
          mul_le_mul (hlam x k) hraw (abs_nonneg _) hΛ
      _ = Λ * (1 + 18 + 18 ^ 2 + 18 ^ 3) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdB hC
  · rw [abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- P0069, page 53, assembly of `upper_short_coefficient` from the CITED-LEFT analytic LEAF
`upper_normalized_raw_conditions`. The statement is exactly that of `upper_short_coefficient`.
Domination: on J, eventually, b1 = lam times the raw weight, the raw weight is nonnegative and
lam is at least one. PROVED modulo the one LEAF. -/
theorem upper_short_coefficient_of_leaf
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ b1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        upperRawWeight ε (x ^ (11 / 20 + ε)) m ≤ b1 x m := by
  obtain ⟨lam, Λ, hlam, ⟨X, hX⟩, hdist, hms⟩ :=
    upper_normalized_raw_conditions h4 h9 hω hz hε hε8
  refine ⟨upperNormCoeff ε lam, upper_norm_coeff_divisor_bound hB hε hε8 hlam, hdist, hms,
    max X 4, fun x hx m hm => ?_⟩
  have hx4 : 4 ≤ x := le_of_max_le_right hx
  have hY := upper_Y_ge_two hε hx4
  have hraw := upper_raw_nonneg ε (Y := x ^ (11 / 20 + ε)) (by linarith) m
  have hl := hX x (le_of_max_le_left hx) m hm
  unfold upperNormCoeff
  simp only [hY, hm, and_self, ↓reduceIte]
  nlinarith

/-- LEAF, OPEN, CITED-LEFT. P0069 Baker Harman Pintz 1997, Section 5, page 53, display 5.17 on
page 51 and displays 5.18 to 5.23 on page 52, with an arbitrarily small loss delta in the
density. The same cited inputs as `upper_normalized_raw_conditions`: Lemma 34 for g, h, j,
Lemma 33 for the kept part of k, the prime number theorem with the Buchstab integrals for
v1 = w(1/c4)/c4 + the integral over E, and the repeat of 5.18 to 5.23 through Lemma 29,
Theorem 4 and Lemma 9. Citation wall, not split.
This is the proposed fix of the QUESTION on the exact leaf: the paper only uses v1 < 2.2,
so a density v1 + delta suffices, and lam = (v1 + delta) over the true local density is at
least one eventually as soon as that local density tends to v1 uniformly on J. -/
theorem upper_normalized_raw_conditions_slack
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  sorry

/-- P0069, page 53. Domination on J: for x >= 4 the prime weight is at most the
normalized coefficient, through rho(m) <= psi(m, Y^c4) = g - h + j - k <= b1 <= lam b1. PROVED. -/
theorem upper_prime_le_norm_coeff {ε x : ℝ} (hε : 0 < ε) (hx : 4 ≤ x)
    {lam : ℝ → ℕ → ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) (hl : 1 ≤ lam x m) :
    primeWeight m ≤ upperNormCoeff ε lam x m := by
  have hY := upper_Y_ge_two hε hx
  have h1 := upper_prime_le_rough hε (by linarith) hm
  rw [upper_rough_four_term ε (by linarith) m] at h1
  have h2 := h1.trans (upper_four_term_le_raw ε _ m)
  have hraw := upper_raw_nonneg ε (Y := x ^ (11 / 20 + ε)) (by linarith) m
  unfold upperNormCoeff
  simp only [hY, hm, and_self, ↓reduceIte]
  nlinarith

/-- P0069, page 53 and the end of Section 5: the slack route. The exact statement of
`DecompC165d.upper_short_weight` of DecompC165d.lean, assembled from the slack LEAF
`upper_normalized_raw_conditions_slack`, the certified bound `upper_density_bound`, the
divisor bound and the domination above. The density is v1 = the paper value + delta, with
delta half the margin below 2.2. PROVED modulo the one slack LEAF and the inputs h4, h9. -/
theorem upper_short_weight_of_slack_leaf
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  obtain ⟨B0, η, hη, hrange⟩ := upper_thresholds
  refine ⟨B0, η, hη, fun B ε hB hε hεη => ?_⟩
  obtain ⟨hB0, hε0, hε8⟩ := hrange B ε hB hε hεη
  set P := ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
    upperDeletedIntegral ω ε with hP
  have hP22 : P < 2.2 := upper_density_bound hω hz hε0.le hε8 le_rfl
  have hδ : 0 < (2.2 - P) / 2 := by linarith
  obtain ⟨lam, Λ, hlam, ⟨X, hX⟩, hdist, hms⟩ :=
    upper_normalized_raw_conditions_slack h4 h9 hω hz hε0 hε8 hδ
  refine ⟨P + (2.2 - P) / 2, upperNormCoeff ε lam, by linarith,
    Task308.right_conditions_of_parts (upper_norm_coeff_divisor_bound hB0 hε0 hε8 hlam)
      hdist hms, max X 4, fun x hx m hm => ?_⟩
  exact upper_prime_le_norm_coeff hε0 (le_of_max_le_right hx) hm
    (hX x (le_of_max_le_left hx) m hm)

end LeanLab.BHP1997.DecompC165d
