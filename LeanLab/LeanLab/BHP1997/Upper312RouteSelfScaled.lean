/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 53, with page 3 conditions ii, iii, iv,
display 5.17 on page 51 and displays 5.18 to 5.23 on page 52.
A route to upper_short_weight_analytic of DecompC165dBase312 that does not pass through the
leaf upper_short_coefficient, which is SUSPECTED FALSE: the page 53 raw weight with levels
frozen at powers of Y gets denser toward the top of J, so nothing that dominates it can have
the constant center v1 / log Y.
Here the page 53 construction is read with every level and exponent measured against m itself,
upperRawWeight eps m m, times the recentering factor log m / log Y. No new definition is made:
the coefficient is written out in each statement.
PROVED here: a prime is dominated, the divisor bound, and the two assemblies.
One LEAF: conditions 1.8 and 1.9 for this coefficient at the paper density v1.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- P0069 Baker Harman Pintz 1997, Section 5, page 53, first inequality rho(m) <= psi(m, Y^c4),
read at the level m^c4: a prime m is at least m^c4, so it has no prime factor below m^c4.
PROVED. AI wrote the Lean code. Goldbach is open. -/
theorem upper_prime_le_self_rough {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    primeWeight m ≤ upperRough m ((m : ℝ) ^ upperC4 ε) := by
  unfold primeWeight
  split_ifs with hp
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hp.one_lt.le
    have hc : (m : ℝ) ^ upperC4 ε ≤ (m : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (m : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hm1 (by unfold upperC4; linarith)
    unfold upperRough
    rw [if_pos]
    intro p hpm
    rw [Nat.Prime.primeFactors hp, Finset.mem_singleton] at hpm
    subst hpm
    exact hc
  · exact upperRough_nonneg _ _

/-- P0069 Baker Harman Pintz 1997, Section 5, page 53, "so that rho(m) <= b1(m)", for the self
scaled coefficient: on J, for x at least 4, the prime weight is at most log m / log Y times
the page 53 raw weight with levels measured against m. The factor is at least one because m
exceeds Y, and the raw weight is at least psi(m, m^c4) by the four term identity.
PROVED. AI wrote the Lean code. Goldbach is open. -/
theorem upper_self_scaled_prime_le {ε x : ℝ} (hε : 0 < ε) (hx : 4 ≤ x) {m : ℕ}
    (hm : m ∈ rightInterval ε x) :
    primeWeight m ≤
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m := by
  have hY := upper_Y_ge_two hε hx
  have hm' := Finset.mem_Ioc.mp hm
  have hmY : x ^ (11 / 20 + ε) < (m : ℝ) := by
    have h2 := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
    have h3 : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm'.1
    linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos (by linarith)
  have hlog : Real.log (x ^ (11 / 20 + ε)) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by linarith) hmY.le
  have hratio : 1 ≤ Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) := by
    rw [le_div_iff₀ hlogY]
    linarith
  have hraw : upperRough m ((m : ℝ) ^ upperC4 ε) ≤ upperRawWeight ε (m : ℝ) m := by
    rw [upper_rough_four_term ε hm1 m]
    exact upper_four_term_le_raw ε _ m
  have h0 : 0 ≤ upperRawWeight ε (m : ℝ) m := upper_raw_nonneg ε hm1 m
  calc primeWeight m ≤ upperRough m ((m : ℝ) ^ upperC4 ε) := upper_prime_le_self_rough hε m
    _ ≤ upperRawWeight ε (m : ℝ) m := hraw
    _ = 1 * upperRawWeight ε (m : ℝ) m := (one_mul _).symm
    _ ≤ Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m :=
        mul_le_mul_of_nonneg_right hratio h0

/-- P0069 Baker Harman Pintz 1997, page 3 condition ii and Section 5 page 53: the divisor bound
for the self scaled coefficient, for every B at least 0. On J with Y at least 2 the raw weight
with levels at m is at most 1 + 18 + 18^2 + 18^3 in absolute value and the factor
log m / log Y is at most 2, since m is at most 2Y.
PROVED. AI wrote the Lean code. Goldbach is open. -/
theorem upper_self_scaled_divisor_bound {ε B : ℝ} (hB : 0 ≤ B) (hε8 : ε ≤ 1 / 10 ^ 8)
    {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
  refine ⟨2 * (1 + 18 + 18 ^ 2 + 18 ^ 3), fun x k => ?_⟩
  have hC : (0 : ℝ) ≤ 2 * (1 + 18 + 18 ^ 2 + 18 ^ 3) := by norm_num
  rw [hb x k]
  split_ifs with h
  · obtain ⟨hY, hk⟩ := h
    have hk' := Finset.mem_Ioc.mp hk
    have hkY : (k : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
      have : (k : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hk'.2
      exact this.trans (Nat.floor_le (by linarith))
    have hYk : x ^ (11 / 20 + ε) < (k : ℝ) := by
      have h2 := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
      have h3 : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk'.1
      linarith
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by linarith
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hk2
    have hraw := upper_raw_abs_le hε8 hk2 hk0 (by linarith : (k : ℝ) ≤ 2 * (k : ℝ))
    have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos (by linarith)
    have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log 2 ≤ Real.log (x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by norm_num) hY
    have hlogle : Real.log (k : ℝ) ≤ 2 * Real.log (x ^ (11 / 20 + ε)) := by
      have h1 : Real.log (k : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
        Real.log_le_log (by linarith) hkY
      rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith))] at h1
      linarith
    have hratio : |Real.log (k : ℝ) / Real.log (x ^ (11 / 20 + ε))| ≤ 2 := by
      rw [abs_of_nonneg (div_nonneg hlogk hlogY.le), div_le_iff₀ hlogY]
      exact hlogle
    have hd : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      have : 1 ≤ k.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd k, hk0⟩⟩
      exact_mod_cast this
    have hdB : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.one_le_rpow hd hB
    rw [abs_mul]
    calc |Real.log (k : ℝ) / Real.log (x ^ (11 / 20 + ε))| * |upperRawWeight ε (k : ℝ) k|
        ≤ 2 * (1 + 18 + 18 ^ 2 + 18 ^ 3) :=
          mul_le_mul hratio hraw (abs_nonneg _) (by norm_num)
      _ = 2 * (1 + 18 + 18 ^ 2 + 18 ^ 3) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdB hC
  · rw [abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-
Background for the LEAF below.
Paper inputs: "We use Lemma 34 to obtain (5.1) and (5.2) for g_m, h_m and j_m", Lemma 33 for
the kept part of k_m, "from the prime number theorem" for the constant v1, display 5.17 of
page 51, and "We may now repeat for b1(m) the argument" of displays 5.18 to 5.23 on page 52
through Lemma 29, Theorem 4 and Lemma 9. The prime number estimate is a citation wall and is
not split.
Why this reading: with levels frozen at powers of Y the density of the raw weight at
m = Y^(1+theta) is D(theta) / log Y with D(0) = v1 and right derivative about +0.0164, so the
frozen leaf upper_short_coefficient is SUSPECTED FALSE. With levels at powers of m the density
at m is v1 / log m, by comparison with frozen levels in short windows, and the factor
log m / log Y recenters it to v1 / log Y. An independent numeric agent tried to refute this
and did not: exact counts at Y from 1e12 to 1e18 are flat across J and approach v1.
This is the lab's repair of the constant center of 1.8, a QUESTION for review; the paper
prints levels Y^c1 and Y^c4. Not examined: whether Lemmas 33 and 34 keep their Type I and II
structure when the levels move with m.
Non-vacuity: the hypothesis hb fixes b1, which is 1 or more at every prime of J, so b1 = 0 is
excluded and the density v1 is forced to be the true one.
-/

/-- LEAF: P0069 Baker Harman Pintz 1997, Section 5, page 53, conditions 1.8 and 1.9 of page 3
for b1 at the density v1 = w(1/c4)/c4 plus the integral over E, in the self scaled reading.
OPEN, CITED-LEFT. The coefficient is log m / log Y times the page 53 raw weight
g - h + j - kept part of k with every level m^c1, m^c4 and every exponent log p / log m
measured against m, on J for Y at least 2, and zero elsewhere. Inputs: Lemmas 33 and 34,
the prime number theorem for v1, display 5.17, and displays 5.18 to 5.23. -/
theorem upper_self_scaled_conditions
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 := by
  sorry

/-- P0069 Baker Harman Pintz 1997, Section 5, pages 43 to 53. The exact statement of
`DecompC165d.upper_short_weight_analytic` of DecompC165dBase312, assembled from the LEAF
`upper_self_scaled_conditions` and the proved divisor bound and prime domination of the self
scaled coefficient. It does not use the leaf upper_short_coefficient.
CONDITIONAL ON the one LEAF. AI wrote the Lean code. Goldbach is open. -/
theorem upper_short_weight_analytic_of_self_scaled
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
          v1 ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) /
              (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε ∧
          RightConditions ε B v1 b1 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  obtain ⟨B0, η, hη, hrange⟩ := upper_thresholds
  refine ⟨ω, hω, hz, B0, η, hη, fun B ε hB hε hεη => ?_⟩
  obtain ⟨hB0, hε0, hε8⟩ := hrange B ε hB hε hεη
  have hb : ∀ (x : ℝ) (m : ℕ),
      (fun (x : ℝ) (m : ℕ) => if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
        Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m
        else 0) x m =
      if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
        Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m
        else 0 := fun _ _ => rfl
  obtain ⟨hdist, hms⟩ := upper_self_scaled_conditions h4 h9 hω hz hε0 hε8 hb
  refine ⟨_, _, le_rfl,
    Task308.right_conditions_of_parts (upper_self_scaled_divisor_bound hB0 hε8 hb) hdist hms,
    4, ?_⟩
  intro x hx m hm
  have hY := upper_Y_ge_two hε0 hx
  show primeWeight m ≤ if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
    Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0
  rw [if_pos ⟨hY, hm⟩]
  exact upper_self_scaled_prime_le hε0 hx hm

/-- P0069 Baker Harman Pintz 1997, Section 5, page 53, "A computer calculation yields
v1 < 2.2". The exact statement of `DecompC165d.upper_short_weight` of DecompC165d.lean,
from the self scaled assembly and the certified bound `upper_density_bound`.
CONDITIONAL ON the one LEAF `upper_self_scaled_conditions`. AI wrote the Lean code.
Goldbach is open. -/
theorem upper_short_weight_of_self_scaled
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m := by
  obtain ⟨ω, hω, hz, B0, η, hη, hweight⟩ := upper_short_weight_analytic_of_self_scaled h4 h9
  refine ⟨B0, min η (1/10^8), lt_min hη (by norm_num), ?_⟩
  intro B ε hB hε hεη
  have hεsmall : ε ≤ 1/10^8 :=
    (lt_of_lt_of_le hεη (min_le_right _ _)).le
  obtain ⟨v1, b1, hdensity, hright, X, hsandwich⟩ :=
    hweight B ε hB hε (lt_of_lt_of_le hεη (min_le_left _ _))
  exact ⟨v1, b1, upper_density_bound hω hz hε.le hεsmall hdensity,
    hright, X, hsandwich⟩

end LeanLab.BHP1997.Upper312Route
