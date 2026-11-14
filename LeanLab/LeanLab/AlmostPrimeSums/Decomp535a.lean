import LeanLab.AlmostPrimeSums.RosserDefect
import LeanLab.AlmostPrimeSums.RosserFirst

/-!
AI wrote this Lean code for CODEX task535. Goldbach is open.
The stopping index k in this file denotes the paper index k plus one.
The recursion is Nathanson pp. 242 to 245, equations 9.10, 9.14 and 9.15.
No bounded cutoff constant occurs here.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b
open Finset Real BoundingSieve
attribute [local instance] Classical.propDecidable

/-- The paper stopping term T at index k plus one. The first term uses
its cube stopping boundary. Later odd terms require the first prime cube
strictly below D. Nathanson p. 242 and pp. 244 to 245 Lemma 9.4. -/
noncomputable def stopping535 (s : BoundingSieve) : ℕ → ℝ → ℝ → ℝ
  | 0, D, z =>
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        if D ≤ (p : ℝ) ^ 3 then
          s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)
        else 0
  | k + 1, D, z =>
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        if (k + 2) % 2 = 1 ∧ D ≤ (p : ℝ) ^ 3 then 0
        else s.nu p * stopping535 s k (D / p) p

/-- Every recursively defined stopping term is nonnegative. This is the
finite positivity statement in Nathanson p. 242 Lemma 9.3. -/
theorem stopping535_nonneg (s : BoundingSieve) (k : ℕ) (D z : ℝ) :
    0 ≤ stopping535 s k D z := by
  induction k generalizing D z with
  | zero =>
    unfold stopping535
    apply Finset.sum_nonneg
    intro p hp
    split_ifs
    · apply mul_nonneg
      · exact (s.nu_pos_of_prime p
          (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
          (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
      · exact Finset.prod_nonneg fun q hq => (sub_pos.mpr
          (s.nu_lt_one_of_prime q
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
            (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))).le
    · exact le_rfl
  | succ k ih =>
    unfold stopping535
    apply Finset.sum_nonneg
    intro p hp
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (s.nu_pos_of_prime p
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le (ih _ _)

/-- A prime prefix below p is strictly smaller than a prefix containing p.
This is the finite termination argument for Nathanson p. 242 equation 9.10. -/
theorem stopping535_prefix_card_lt (s : BoundingSieve) (z : ℝ) {p : ℕ}
    (hp : p ∈ s.prodPrimes.primeFactors) (hpz : (p : ℝ) < z) :
    (s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < p)).card <
      (s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < z)).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro q hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
      (Finset.mem_filter.mp hq).2.trans hpz⟩
  · intro heq
    have hmem : p ∈ s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < z) :=
      Finset.mem_filter.mpr ⟨hp, hpz⟩
    rw [← heq] at hmem
    exact (lt_irrefl (p : ℝ)) (Finset.mem_filter.mp hmem).2

/-- A stopping chain longer than its available prime prefix has zero mass.
This makes the odd series in Nathanson p. 242 equation 9.10 finite for
an actual finite sieve. No analytic estimate or density condition is used. -/
theorem stopping535_eq_zero_of_card (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (hcard : (s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).card ≤ k) :
    stopping535 s k D z = 0 := by
  induction k generalizing D z with
  | zero =>
    have he : s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    simp [stopping535, he]
  | succ k ih =>
    unfold stopping535
    apply Finset.sum_eq_zero
    intro p hp
    have hc := stopping535_prefix_card_lt s z
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
    have he := ih (D / p) p (by omega)
    split_ifs <;> simp [he]

/-- Enlarging the prime prefix increases every stopping term.
Derived monotonicity of the positive sums in Nathanson p. 242. -/
theorem stopping535_mono_cutoff (s : BoundingSieve) (k : ℕ) (D : ℝ)
    {w z : ℝ} (hwz : w ≤ z) : stopping535 s k D w ≤ stopping535 s k D z := by
  cases k <;> unfold stopping535
  all_goals
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2.trans_le hwz⟩
    · intro p hp _
      split_ifs
      all_goals first
        | exact le_rfl
        | exact mul_nonneg (s.nu_pos_of_prime p
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
              (stopping535_nonneg s _ _ _)
        | exact mul_nonneg (s.nu_pos_of_prime p
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le
              (Finset.prod_nonneg fun q hq => (sub_pos.mpr
                (s.nu_lt_one_of_prime q
                  (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
                  (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))).le)

/-- The first recursively defined term is exactly the existing first
boundary when every sifting prime lies below z. Nathanson p. 245
calculation of T one preceding equation 9.14. -/
theorem stopping535_zero_eq_first (s : BoundingSieve) (D z : ℝ) (hD : 0 < D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    stopping535 s 0 D z = rosserFirstBoundary s (exp (log D / 3)) := by
  have hfilter : s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) =
      s.prodPrimes.primeFactors := Finset.filter_eq_self.mpr hP
  rw [stopping535, hfilter]
  unfold rosserFirstBoundary
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have he := rosser_first_threshold_cube D hD
  have hiff : D ≤ (p : ℝ) ^ 3 ↔ exp (log D / 3) ≤ p := by
    constructor
    · intro hh
      exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hp0 (by simpa only [he] using hh)
    · intro hh
      simpa only [he] using pow_le_pow_left₀ (exp_pos (log D / 3)).le hh 3
  simp only [hiff]

/-- The stopping term vanishes at and above its power support boundary.
Nathanson p. 244 equation 9.12 and the conclusion of Lemma 9.3. -/
theorem stopping535_eq_zero_of_level (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (hz : 2 ≤ z) (hD : z ^ (k + 3) ≤ D) : stopping535 s k D z = 0 := by
  induction k generalizing D z with
  | zero =>
    unfold stopping535
    apply Finset.sum_eq_zero
    intro p hp
    have hpz := (Finset.mem_filter.mp hp).2
    have hc : (p : ℝ) ^ 3 < z ^ 3 :=
      pow_lt_pow_left₀ hpz (Nat.cast_nonneg p) (by norm_num)
    have hn : ¬D ≤ (p : ℝ) ^ 3 := by norm_num at hD; linarith
    simp [hn]
  | succ k ih =>
    unfold stopping535
    apply Finset.sum_eq_zero
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    have hpz := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).two_le
    have hp0 : 0 < (p : ℝ) := by linarith
    have hc : (p : ℝ) ^ (k + 4) ≤ D :=
      (pow_le_pow_left₀ hp0.le hpz.le _).trans (by simpa [Nat.add_assoc] using hD)
    have hd : (p : ℝ) ^ (k + 3) ≤ D / p := by
      apply (le_div_iff₀ hp0).mpr
      simpa [show k + 4 = (k + 3) + 1 by omega, pow_succ] using hc
    have he := ih (D / p) p hp2 hd
    split_ifs <;> simp [he]

/-- A nonnegative local comparison propagates through one stopping step.
This is the elementary sum comparison in Nathanson p. 254 after the
induction hypothesis, before the analytic partial summation. -/
theorem stopping535_step_le (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (U : ℝ → ℝ → ℝ)
    (hU : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z →
      ¬((k + 2) % 2 = 1 ∧ D ≤ (p : ℝ) ^ 3) →
      stopping535 s k (D / p) p ≤ U (D / p) p) :
    stopping535 s (k + 1) D z ≤
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        if (k + 2) % 2 = 1 ∧ D ≤ (p : ℝ) ^ 3 then 0
        else s.nu p * U (D / p) p := by
  rw [stopping535]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs with he
  · exact le_rfl
  · apply mul_le_mul_of_nonneg_left
      (hU p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2 he)
    exact (s.nu_pos_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).le

/-- Induction on the stopping index reduces an envelope estimate to its
first term and a local comparison of the next weighted prime sum.
This is only the finite induction mechanism in Nathanson pp. 253 to 256.
It assumes the local comparisons explicitly and proves no sieve estimate. -/
theorem stopping535_le_envelope (s : BoundingSieve) (U : ℕ → ℝ → ℝ → ℝ)
    (hbase : ∀ D z, stopping535 s 0 D z ≤ U 0 D z)
    (hstep : ∀ k D z,
      (∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        if (k + 2) % 2 = 1 ∧ D ≤ (p : ℝ) ^ 3 then 0
        else s.nu p * U k (D / p) p) ≤ U (k + 1) D z)
    (k : ℕ) (D z : ℝ) : stopping535 s k D z ≤ U k D z := by
  induction k generalizing D z with
  | zero => exact hbase D z
  | succ k ih =>
    exact (stopping535_step_le s k D z (U k)
      (fun p _ _ _ => ih (D / p) p)).trans (hstep k D z)

/-- For an even paper index the first prime has no extra cube restriction.
Nathanson p. 244 equation 9.14. -/
theorem stopping535_succ_even (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (hk : (k + 2) % 2 = 0) :
    stopping535 s (k + 1) D z =
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * stopping535 s k (D / p) p := by
  simp [stopping535, hk]

/-- For an odd paper index at least three the first prime cube is below D.
Nathanson p. 245 equation 9.15, with both cutoff regimes retained. -/
theorem stopping535_succ_odd (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (hk : (k + 2) % 2 = 1) :
    stopping535 s (k + 1) D z =
      ∑ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < z ∧ (p : ℝ) ^ 3 < D),
        s.nu p * stopping535 s k (D / p) p := by
  simp only [stopping535, hk, true_and, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpz : (p : ℝ) < z <;> by_cases hpD : D ≤ (p : ℝ) ^ 3 <;>
    simp [hpz, hpD, lt_of_not_ge, not_lt_of_ge]

/-- Above the cube boundary each higher odd stopping term is independent
of the outer cutoff. This is the exact first equality used on Nathanson
p. 256. It concerns the unnormalized term, so no factor V is discarded. -/
theorem stopping535_odd_cutoff_stable (s : BoundingSieve) (k : ℕ) (D w z : ℝ)
    (hk : (k + 2) % 2 = 1) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hDw : D ≤ w ^ 3) (hDz : D ≤ z ^ 3) :
    stopping535 s (k + 1) D w = stopping535 s (k + 1) D z := by
  rw [stopping535_succ_odd s k D w hk, stopping535_succ_odd s k D z hk]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  have hw' : (p : ℝ) ^ 3 < D → (p : ℝ) < w := by
    intro hp
    by_contra hn
    have hc := pow_le_pow_left₀ hw (le_of_not_gt hn) 3
    linarith
  have hz' : (p : ℝ) ^ 3 < D → (p : ℝ) < z := by
    intro hp
    by_contra hn
    have hc := pow_le_pow_left₀ hz (le_of_not_gt hn) 3
    linarith
  tauto

/-- A higher odd term can be evaluated exactly at the moving cube cutoff
throughout the range one through three. Nathanson p. 256 equation 9.15. -/
theorem stopping535_odd_eq_cube_cutoff (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (hk : (k + 2) % 2 = 1) (hD : 0 < D) (hz : 0 ≤ z) (hDz : D ≤ z ^ 3) :
    stopping535 s (k + 1) D z =
      stopping535 s (k + 1) D (exp (log D / 3)) := by
  exact stopping535_odd_cutoff_stable s k D z (exp (log D / 3)) hk hz
    (exp_pos _).le hDz (rosser_first_threshold_cube D hD).symm.le

/-- On the range above three the extra first prime restriction is automatic.
Nathanson p. 244 equation 9.14. This includes the ratio three endpoint. -/
theorem stopping535_succ_of_cube_le (s : BoundingSieve) (k : ℕ) (D z : ℝ)
    (_hz : 0 ≤ z) (hDz : z ^ 3 ≤ D) :
    stopping535 s (k + 1) D z =
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * stopping535 s k (D / p) p := by
  rw [stopping535]
  apply Finset.sum_congr rfl
  intro p hp
  have hpz := (Finset.mem_filter.mp hp).2
  have hc : (p : ℝ) ^ 3 < D :=
    (pow_lt_pow_left₀ hpz (Nat.cast_nonneg p) (by norm_num : (3 : ℕ) ≠ 0)).trans_le hDz
  simp [not_le.mpr hc]

/-- The finite higher odd stopping sum removes the first term from the
odd series of Nathanson p. 242 equation 9.10. Cardinal termination makes
the displayed upper bound on k exact for every finite sieve. -/
noncomputable def higherOdd535 (s : BoundingSieve) (D z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range s.prodPrimes.primeFactors.card,
    if k % 2 = 0 ∧ 2 ≤ k then stopping535 s k D z else 0

/-- The higher odd stopping sum is nonnegative. Nathanson p. 242, the
positivity of every term in equation 9.10. -/
theorem higherOdd535_nonneg (s : BoundingSieve) (D z : ℝ) :
    0 ≤ higherOdd535 s D z := by
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact stopping535_nonneg s k D z
  · exact le_rfl

/-- Every higher odd term stabilizes at the cube cutoff on the first
explicit F range, so their finite sum does too. Nathanson p. 256. -/
theorem higherOdd535_eq_cube_cutoff (s : BoundingSieve) (D z : ℝ)
    (hD : 0 < D) (hz : 0 ≤ z) (hDz : D ≤ z ^ 3) :
    higherOdd535 s D z = higherOdd535 s D (exp (log D / 3)) := by
  unfold higherOdd535
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with he
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact stopping535_odd_eq_cube_cutoff s j D z (by omega) hD hz hDz
  · rfl

/-- The density condition compares the moving prefix product to the full
product. This retains the factor needed when transporting the stable
unnormalized higher odd sum on Nathanson p. 256. -/
theorem prefix535_le_density (s : BoundingSieve) (K w z : ℝ)
    (hK : 0 ≤ K) (hden : LinearDensity s K) (hw : 2 ≤ w) (hwz : w ≤ z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < w),
      (1 - s.nu p)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (log z / log w * (1 + K / log w)) := by
  have hV : 0 ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_nonneg fun p hp => (sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))).le
  rcases eq_or_lt_of_le hwz with he | he
  · subst z
    rw [Finset.filter_eq_self.mpr hP, div_self (log_pos (by linarith : 1 < w)).ne']
    have hh := mul_nonneg hV (div_nonneg hK (log_pos (by linarith : 1 < w)).le)
    nlinarith
  · have hh := rosserFirstBoundary_le_density s K w z hden hw he hP
    rw [rosserFirstBoundary_eq_product_sub] at hh
    nlinarith

/-- Scalar transport of an endpoint bound at ratio three to ratios one
through three. This retains both the density error and its product with
the endpoint error. Derived bookkeeping for Nathanson p. 256. -/
theorem higherOdd535_scalar_transport (A C K L u : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 1 ≤ L) (hu : 1 ≤ u) :
    (3 / u * (1 + 3 * K / L)) * (A / 3 + C * L ^ (-(1 / 3 : ℝ))) ≤
      A / u + (3 * A * K + 3 * C + 9 * K * C) * L ^ (-(1 / 3 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  let e := L ^ (-(1 / 3 : ℝ))
  have he : 0 ≤ e := (rpow_pos_of_pos hL0 _).le
  have hInv : L⁻¹ ≤ e := by
    rw [← rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hInv1 : L⁻¹ ≤ 1 := (inv_le_one₀ hL0).mpr hL
  have hAu : A / u ≤ A := (div_le_self hA hu)
  have hru : 3 / u ≤ 3 := (div_le_self (by norm_num : (0 : ℝ) ≤ 3) hu)
  have h1 := mul_le_mul_of_nonneg_left hInv (show 0 ≤ 3 * K by positivity)
  have h2 := mul_le_mul_of_nonneg_left hInv1 (show 0 ≤ 3 * K by positivity)
  have h3 := mul_le_mul_of_nonneg_left h1 hA
  have h4 := mul_le_mul_of_nonneg_right hAu (show 0 ≤ 3 * K / L by positivity)
  have h5 := mul_le_mul_of_nonneg_right hru (mul_nonneg hC he)
  have h6 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 3 * C * e by positivity)
  have h7 := mul_le_mul_of_nonneg_right hru
    (show 0 ≤ (3 * K / L) * C * e by positivity)
  have hid : (3 / u * (1 + 3 * K / L)) * (A / 3 + C * e) =
      A / u + (A / u) * (3 * K / L) + (3 / u) * (C * e) +
        (3 / u) * ((3 * K / L) * C * e) := by field_simp; ring
  change _ ≤ A / u + (3 * A * K + 3 * C + 9 * K * C) * e
  rw [hid]
  simp only [div_eq_mul_inv] at h1 h2 h3 h4 h5 h6 h7 ⊢
  nlinarith only [h3, h4, h5, h6, h7]

/-- An endpoint estimate for the actual higher odd stopping sum transports
to the complete ratio one through three range. This is CONDITIONAL ON the
stated endpoint estimate. It includes the density factor from V at the
cube cutoff to V at z, as required by Nathanson p. 256. -/
theorem higherOdd535_small_of_endpoint (s : BoundingSieve) (K A C D z : ℝ)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 8 ≤ D)
    (hz : 2 ≤ z) (hzD : z ≤ D) (hDz : D ≤ z ^ 3)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hden : LinearDensity s K)
    (hend : higherOdd535 s D (exp (log D / 3)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < exp (log D / 3)), (1 - s.nu p)) *
        (A / 3 + C * log D ^ (-(1 / 3 : ℝ)))) :
    higherOdd535 s D z / (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
      A / (log D / log z) +
        (3 * A * K + 3 * C + 9 * K * C) * log D ^ (-(1 / 3 : ℝ)) := by
  have hD0 : 0 < D := by linarith
  have hL : 1 ≤ log D := by
    have hh := log_lt_log (exp_pos 1)
      (exp_one_lt_three.trans_le (by linarith : (3 : ℝ) ≤ D))
    simpa only [log_exp] using hh.le
  have hlogz : 0 < log z := log_pos (by linarith)
  have hu : 1 ≤ log D / log z := by
    apply (le_div_iff₀ hlogz).mpr
    simpa using log_le_log (by linarith : 0 < z) hzD
  have hw : 2 ≤ exp (log D / 3) := by
    apply (log_le_log_iff (by norm_num : (0 : ℝ) < 2) (exp_pos _)).mp
    rw [log_exp]
    have hh := log_le_log (by norm_num : (0 : ℝ) < 8) hD
    have he : log (8 : ℝ) = 3 * log 2 := by
      convert log_pow (2 : ℝ) 3 using 1; norm_num
    rw [he] at hh
    linarith
  have hwz : exp (log D / 3) ≤ z := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by linarith : 0 ≤ z)
    simpa only [rosser_first_threshold_cube D hD0] using hDz
  have hpref := prefix535_le_density s K (exp (log D / 3)) z hK hden hw hwz hP
  rw [log_exp] at hpref
  have hratio : log z / (log D / 3) = 3 / (log D / log z) := by field_simp
  have herror : K / (log D / 3) = 3 * K / log D := by ring
  rw [hratio, herror] at hpref
  have he0 : 0 ≤ A / 3 + C * log D ^ (-(1 / 3 : ℝ)) := by positivity
  have hH : higherOdd535 s D z ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ((3 / (log D / log z) * (1 + 3 * K / log D)) *
          (A / 3 + C * log D ^ (-(1 / 3 : ℝ)))) := by
    rw [higherOdd535_eq_cube_cutoff s D z hD0 (by linarith) hDz]
    exact hend.trans ((mul_le_mul_of_nonneg_right hpref he0).trans_eq (by ring))
  have hV : 0 < ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_pos fun p hp => sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  apply le_trans ((div_le_iff₀ hV).mpr (by simpa only [mul_comm] using hH))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    higherOdd535_scalar_transport A C K (log D) (log D / log z) hA hC hK hL hu

/-- A finite four prime model for the stopping identities in Nathanson
pp. 242 to 245. The sifting primes are three, five, seven and eleven.
Every prime density is one half. This is a vacuity model, not an
instance of the small uniform density loss in Theorem 9.5. -/
noncomputable def stoppingExample535 : BoundingSieve where
  support := {1}
  prodPrimes := 1155
  prodPrimes_squarefree := by
    change Squarefree (3 * (5 * (7 * 11)) : ℕ)
    apply (Nat.squarefree_mul (by norm_num : Nat.Coprime 3 (5 * (7 * 11)))).mpr
    refine ⟨Nat.prime_three.squarefree, ?_⟩
    apply (Nat.squarefree_mul (by norm_num : Nat.Coprime 5 (7 * 11))).mpr
    refine ⟨(by decide : Nat.Prime 5).squarefree, ?_⟩
    exact (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 11)).mpr
      ⟨(by decide : Nat.Prime 7).squarefree, (by decide : Nat.Prime 11).squarefree⟩
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := 1
  nu := ArithmeticFunction.prodPrimeFactors (fun _ => (1 / 2 : ℝ))
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := by
    intro p hp _
    norm_num [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]
  nu_lt_one_of_prime := by
    intro p hp _
    norm_num [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]

/-- In the four prime model a higher odd term is nonzero and stable as
z changes from eight to twelve. This tests the exact stopping range in
Nathanson p. 256 and does not test its density hypothesis. -/
theorem stoppingExample535_nonzero :
    stopping535 stoppingExample535 2 512 8 = 1 / 8 ∧
      stopping535 stoppingExample535 2 512 12 = 1 / 8 := by
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have h7 : Nat.Prime 7 := by decide
  have h11 : Nat.Prime 11 := by decide
  have hP : (1155 : ℕ).primeFactors = {3, 5, 7, 11} := by
    rw [show (1155 : ℕ) = 3 * (5 * (7 * 11)) by norm_num,
      Nat.primeFactors_mul (by norm_num : (3 : ℕ) ≠ 0)
        (by norm_num : (5 * (7 * 11) : ℕ) ≠ 0),
      Nat.primeFactors_mul (by norm_num : (5 : ℕ) ≠ 0)
        (by norm_num : (7 * 11 : ℕ) ≠ 0),
      Nat.primeFactors_mul (by norm_num : (7 : ℕ) ≠ 0)
        (by norm_num : (11 : ℕ) ≠ 0),
      h3.primeFactors, h5.primeFactors, h7.primeFactors, h11.primeFactors]
    decide
  norm_num [stopping535, stoppingExample535, hP, Finset.sum_filter, Finset.prod_filter,
    ArithmeticFunction.prodPrimeFactors_apply, h3.primeFactors,
    h5.primeFactors, h7.primeFactors, h11.primeFactors]

/-- Stable unnormalized stopping terms have different normalized values
when the prefix product changes. This is a check on the factor needed in
Nathanson p. 256, not a counterexample to its analytic theorem. -/
theorem stoppingExample535_normalization :
    stopping535 stoppingExample535 2 512 8 /
      (∏ p ∈ stoppingExample535.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < 8), (1 - stoppingExample535.nu p)) = 1 ∧
    stopping535 stoppingExample535 2 512 12 /
      (∏ p ∈ stoppingExample535.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < 12), (1 - stoppingExample535.nu p)) = 2 := by
  rw [stoppingExample535_nonzero.1, stoppingExample535_nonzero.2]
  have h3 : Nat.Prime 3 := by decide
  have h5 : Nat.Prime 5 := by decide
  have h7 : Nat.Prime 7 := by decide
  have h11 : Nat.Prime 11 := by decide
  have hP : (1155 : ℕ).primeFactors = {3, 5, 7, 11} := by
    rw [show (1155 : ℕ) = 3 * (5 * (7 * 11)) by norm_num,
      Nat.primeFactors_mul (by norm_num : (3 : ℕ) ≠ 0)
        (by norm_num : (5 * (7 * 11) : ℕ) ≠ 0),
      Nat.primeFactors_mul (by norm_num : (5 : ℕ) ≠ 0)
        (by norm_num : (7 * 11 : ℕ) ≠ 0),
      Nat.primeFactors_mul (by norm_num : (7 : ℕ) ≠ 0)
        (by norm_num : (11 : ℕ) ≠ 0),
      h3.primeFactors, h5.primeFactors, h7.primeFactors, h11.primeFactors]
    decide
  norm_num [stoppingExample535, hP, Finset.prod_filter, ArithmeticFunction.prodPrimeFactors_apply,
    h3.primeFactors, h5.primeFactors, h7.primeFactors, h11.primeFactors]

/-- Multiplication by a new largest prime prepends that prime to the
ordered list. This is the finite reindexing in Nathanson p. 245, the
proof of the stopping recurrence. -/
theorem decPrimes_mul_largest535 {d p : ℕ} (hd : d ≠ 0) (hp : p.Prime)
    (hmax : ∀ q ∈ d.primeFactors, q < p) :
    decPrimes (p * d) = p :: decPrimes d := by
  have hnot : p ∉ d.primeFactors := fun hm => (lt_irrefl p) (hmax p hm)
  unfold decPrimes
  rw [Nat.primeFactors_mul hp.ne_zero hd, hp.primeFactors, Finset.singleton_union]
  exact Finset.sort_insert (· ≥ ·) (fun q hq => (hmax q hq).le) hnot

/-- Removing the largest prime toggles the Rosser parity and divides the
level by that prime. Only the upper weight has an initial cube test.
Nathanson pp. 243 to 245, the finite first prime decomposition used to
obtain equations 9.14 and 9.15. -/
theorem rosserWeight_mul_largest535 (D : ℝ) (b : Bool) {d p : ℕ}
    (hd : Squarefree d) (hp : p.Prime) (hmax : ∀ q ∈ d.primeFactors, q < p) :
    rosserWeight D b (p * d) =
      if b = true ∧ D ≤ (p : ℝ) ^ 3 then 0
      else -rosserWeight (D / p) (!b) d := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hnot : ¬p ∣ d := by
    intro hpd
    exact (lt_irrefl p) (hmax p (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd.ne_zero⟩))
  have hcop : p.Coprime d := hp.coprime_iff_not_dvd.mpr hnot
  have hpd : Squarefree (p * d) := Nat.squarefree_mul_iff.mpr ⟨hcop, hp.squarefree, hd⟩
  have hmu : (ArithmeticFunction.moebius (p * d) : ℝ) =
      -(ArithmeticFunction.moebius d : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  let A : ℝ → Bool → List ℕ → Prop := fun L upper l =>
    ∀ m < l.length, (upper = true ↔ m % 2 = 0) →
      ((l.take m).prod : ℝ) * (l.getD m 0 : ℝ) ^ 3 < L
  have hiff : A D b (p :: decPrimes d) ↔
      (b = true → (p : ℝ) ^ 3 < D) ∧ A (D / p) (!b) (decPrimes d) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro hb
        have hh := h 0 (by simp) (by simpa using hb)
        simpa using hh
      · intro m hm hb
        have hpar : b = true ↔ (m + 1) % 2 = 0 := by
          cases b <;> simp_all <;> omega
        have hh := h (m + 1) (by simpa using Nat.succ_lt_succ hm) hpar
        apply (lt_div_iff₀ hp0).mpr
        simpa [List.take_succ_cons, List.prod_cons, Nat.cast_mul,
          mul_comm, mul_left_comm, mul_assoc] using hh
    · rintro ⟨hzero, htail⟩ m hm hb
      cases m with
      | zero =>
        have hh := hzero (by simpa using hb)
        simpa using hh
      | succ m =>
        have hml : m < (decPrimes d).length := by simpa using hm
        have hpar : (!b) = true ↔ m % 2 = 0 := by
          cases b <;> simp_all <;> omega
        have hh := (lt_div_iff₀ hp0).mp (htail m hml hpar)
        simpa [List.take_succ_cons, List.prod_cons, Nat.cast_mul,
          mul_comm, mul_left_comm, mul_assoc] using hh
  change (if Squarefree (p * d) ∧ A D b (decPrimes (p * d)) then
      (ArithmeticFunction.moebius (p * d) : ℝ) else 0) =
    if _ then 0 else -(if Squarefree d ∧ A (D / p) (!b) (decPrimes d) then
      (ArithmeticFunction.moebius d : ℝ) else 0)
  rw [decPrimes_mul_largest535 hd.ne_zero hp hmax]
  simp only [hpd, hd, true_and, hiff, hmu]
  by_cases ht : A (D / p) (!b) (decPrimes d) <;>
    cases b <;> by_cases hc : (p : ℝ) ^ 3 < D <;> simp_all

/-- The original Rosser main sum restricted to a finite subset of the
sifting primes, expressed through its subsets. Nathanson p. 243 expansion
of G before the first failure partition. -/
noncomputable def subsetMain535 (s : BoundingSieve) (Q : Finset ℕ) (D : ℝ)
    (b : Bool) : ℝ :=
  ∑ T ∈ Q.powerset, rosserWeight D b (∏ p ∈ T, p) * ∏ p ∈ T, s.nu p

/-- The subset expression over the full prime set equals the original
Rosser divisor main sum. This reuses the existing squarefree divisor
bridge rather than introducing a replacement weight. Nathanson p. 243. -/
theorem subsetMain535_eq_mainSum (s : BoundingSieve) (D : ℝ) (b : Bool) :
    subsetMain535 s s.prodPrimes.primeFactors D b = s.mainSum (rosserWeight D b) := by
  have hh := mainSum_primeFactors_eq_block_main s
    (fun T => rosserWeight D b (∏ p ∈ T, p))
  change _ = subsetMain535 s s.prodPrimes.primeFactors D b at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only
  rw [Nat.prod_primeFactors_of_squarefree
    (s.prodPrimes_squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1)]

/-- Peeling the largest prime from the actual subset main sum toggles
parity at level D over p. This is the finite first prime identity behind
Nathanson pp. 243 to 245 equations 9.14 and 9.15. -/
theorem subsetMain535_insert_largest (s : BoundingSieve) (Q : Finset ℕ)
    (D : ℝ) (b : Bool) {p : ℕ} (hp : p.Prime)
    (hQ : Q ⊆ s.prodPrimes.primeFactors) (hmax : ∀ q ∈ Q, q < p) :
    subsetMain535 s (insert p Q) D b = subsetMain535 s Q D b +
      if b = true ∧ D ≤ (p : ℝ) ^ 3 then 0
      else -s.nu p * subsetMain535 s Q (D / p) (!b) := by
  have hpQ : p ∉ Q := fun h => (lt_irrefl p) (hmax p h)
  unfold subsetMain535
  rw [Finset.sum_powerset_insert hpQ]
  congr 1
  calc
    _ = ∑ T ∈ Q.powerset, if b = true ∧ D ≤ (p : ℝ) ^ 3 then 0
        else -s.nu p * (rosserWeight (D / p) (!b) (∏ q ∈ T, q) *
          ∏ q ∈ T, s.nu q) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTQ : T ⊆ Q := Finset.mem_powerset.mp hT
      have hpT : p ∉ T := fun h => hpQ (hTQ h)
      have hTP : ∀ q ∈ T, q.Prime := fun q hq =>
        Nat.prime_of_mem_primeFactors (hQ (hTQ hq))
      have hdiv : (∏ q ∈ T, q) ∣ s.prodPrimes := by
        calc
          _ ∣ ∏ q ∈ s.prodPrimes.primeFactors, q :=
            Finset.prod_dvd_prod_of_subset T s.prodPrimes.primeFactors _ (hTQ.trans hQ)
          _ = s.prodPrimes := Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree
      have hsq := s.prodPrimes_squarefree.squarefree_of_dvd hdiv
      have hmaxT : ∀ q ∈ (∏ r ∈ T, r).primeFactors, q < p := by
        rw [Nat.primeFactors_prod hTP]
        exact fun q hq => hmax q (hTQ hq)
      rw [Finset.prod_insert hpT, Finset.prod_insert hpT,
        rosserWeight_mul_largest535 D b hsq hp hmaxT]
      split_ifs <;> ring
    _ = _ := by
      split_ifs <;> simp [Finset.mul_sum]

/-- Partition the finite subset main sum by its first prime. Every
child is the original Rosser weight with toggled parity. Nathanson
p. 243 finite expansion and p. 245 first prime reindexing. -/
theorem subsetMain535_first_prime (s : BoundingSieve) (Q : Finset ℕ)
    (hQ : Q ⊆ s.prodPrimes.primeFactors) (D : ℝ) (b : Bool) :
    subsetMain535 s Q D b = 1 -
      ∑ p ∈ Q, if b = true ∧ D ≤ (p : ℝ) ^ 3 then 0
        else s.nu p * subsetMain535 s (Q.filter (fun q => q < p)) (D / p) (!b) := by
  induction Q using Finset.induction_on_max with
  | empty => simp [subsetMain535, rosserWeight, decPrimes]
  | insert p Q hmax ih =>
    have hpQ : p ∉ Q := fun h => (lt_irrefl p) (hmax p h)
    have hQ' : Q ⊆ s.prodPrimes.primeFactors := (Finset.subset_insert p Q).trans hQ
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hQ (Finset.mem_insert_self p Q))
    have hprefix : (insert p Q).filter (fun q => q < p) = Q := by
      simp only [Finset.filter_insert, lt_self_iff_false, ↓reduceIte]
      exact Finset.filter_eq_self.mpr hmax
    have hprefix' : ∀ q ∈ Q,
        (insert p Q).filter (fun r => r < q) = Q.filter (fun r => r < q) := by
      intro q hq
      simp [Finset.filter_insert, not_lt.mpr (hmax q hq).le]
    have hsum : (∑ q ∈ Q, if b = true ∧ D ≤ (q : ℝ) ^ 3 then 0
        else s.nu q * subsetMain535 s ((insert p Q).filter (fun r => r < q))
          (D / q) (!b)) =
        ∑ q ∈ Q, if b = true ∧ D ≤ (q : ℝ) ^ 3 then 0
        else s.nu q * subsetMain535 s (Q.filter (fun r => r < q)) (D / q) (!b) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hprefix' q hq]
    rw [subsetMain535_insert_largest s Q D b hp hQ' hmax,
      Finset.sum_insert hpQ, hprefix, hsum, ih hQ']
    split_ifs <;> ring

/-- The complete parity selected stopping sum. For upper weights it
contains all odd paper indices. For lower weights it contains all even
paper indices. Nathanson p. 242 equations 9.10 and 9.11. -/
noncomputable def allStopping535 (s : BoundingSieve) (b : Bool) (D z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range s.prodPrimes.primeFactors.card,
    if b = true ↔ k % 2 = 0 then stopping535 s k D z else 0

/-- Shifting the stopping index toggles parity. The last term is exactly
zero by cardinal termination, so the finite range incurs no tail error.
Derived finite summation step for Nathanson p. 244 equations 9.10 and 9.11. -/
theorem allStopping535_shift (s : BoundingSieve) (b : Bool) (D z : ℝ) :
    allStopping535 s b D z =
      (if b then stopping535 s 0 D z else 0) +
      ∑ k ∈ Finset.range s.prodPrimes.primeFactors.card,
        if (!b) = true ↔ k % 2 = 0 then stopping535 s (k + 1) D z else 0 := by
  let f : ℕ → ℝ := fun k =>
    if b = true ↔ k % 2 = 0 then stopping535 s k D z else 0
  have hlast : f s.prodPrimes.primeFactors.card = 0 := by
    dsimp [f]
    rw [stopping535_eq_zero_of_card s _ D z
      (Finset.card_filter_le _ _)]
    split_ifs <;> rfl
  calc
    _ = ∑ k ∈ Finset.range (s.prodPrimes.primeFactors.card + 1), f k := by
      rw [Finset.sum_range_succ, hlast, add_zero]
      rfl
    _ = f 0 + ∑ k ∈ Finset.range s.prodPrimes.primeFactors.card, f (k + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    _ = _ := by
      congr 1
      · cases b <;> simp [f]
      · apply Finset.sum_congr rfl
        intro k hk
        have hpar : (b = true ↔ (k + 1) % 2 = 0) ↔
            ((!b) = true ↔ k % 2 = 0) := by
          cases b <;> simp <;> omega
        simp only [f, hpar]

/-- The complete stopping sums satisfy the same first prime recurrence
as the original upper and lower main sums, with the first boundary
separated. Nathanson pp. 244 to 245 equations 9.14 and 9.15. -/
theorem allStopping535_first_prime (s : BoundingSieve) (b : Bool) (D z : ℝ) :
    allStopping535 s b D z =
      (if b then stopping535 s 0 D z else 0) +
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        if b = true ∧ D ≤ (p : ℝ) ^ 3 then 0
        else s.nu p * allStopping535 s (!b) (D / p) p := by
  rw [allStopping535_shift]
  congr 1
  simp only [stopping535, allStopping535, Finset.mul_sum]
  simp_rw [Finset.ite_sum_zero, Finset.ite_zero_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  have hr : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hr with h | h <;> cases b <;> simp [h]


/-- The finite prefix product V at the current cutoff. Nathanson p. 241
Lemma 9.2. It is distinct from the full product when primes remain above z. -/
noncomputable def prefixVolume535 (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (1 - s.nu p)

/-- Expanding the prefix product by its first prime gives the exact
boundary partition. Nathanson p. 241 equation 9.9. -/
theorem prefixVolume535_first_prime (s : BoundingSieve) (z : ℝ) :
    prefixVolume535 s z = 1 -
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * prefixVolume535 s p := by
  unfold prefixVolume535
  rw [Finset.prod_one_sub_ordered]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  congr 1
  ext q
  simp only [Finset.mem_filter, Nat.cast_lt]
  have hpz := (Finset.mem_filter.mp hp).2
  have hqp : q < p → (q : ℝ) < z := fun hh => (Nat.cast_lt.mpr hh).trans hpz
  tauto

/-- The exact finite first failure expansion for the original Rosser
weights, in both parities and in every moving prime prefix. Nathanson
pp. 242 to 244 equations 9.10 and 9.11. This is a combinatorial identity,
with no continuous sieve estimate or density hypothesis. -/
theorem subsetMain535_eq_stopping (s : BoundingSieve) (D z : ℝ) (b : Bool) :
    subsetMain535 s
      (s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)) D b =
      prefixVolume535 s z +
        if b then allStopping535 s b D z else -allStopping535 s b D z := by
  have haux : ∀ n : ℕ, ∀ z : ℝ,
      (s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)).card ≤ n →
      ∀ D : ℝ, ∀ b : Bool,
        subsetMain535 s
          (s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)) D b =
          prefixVolume535 s z +
            if b then allStopping535 s b D z else -allStopping535 s b D z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hz D b
      let S := s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)
      have hprefix : ∀ p ∈ S, S.filter (fun q => q < p) =
          s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < p) := by
        intro p hp
        ext q
        simp only [S, Finset.mem_filter, Nat.cast_lt]
        have hpz := (Finset.mem_filter.mp hp).2
        have hqp : q < p → (q : ℝ) < z := fun hh => (Nat.cast_lt.mpr hh).trans hpz
        tauto
      have hchild : ∀ p ∈ S, ∀ b : Bool,
          subsetMain535 s (S.filter (fun q => q < p)) (D / p) b =
            prefixVolume535 s p +
              if b then allStopping535 s b (D / p) p else -allStopping535 s b (D / p) p := by
        intro p hp b
        rw [hprefix p hp]
        exact ih _ ((stopping535_prefix_card_lt s z
          (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2).trans_le hz)
          p le_rfl (D / p) b
      have hrec := subsetMain535_first_prime s S (Finset.filter_subset _ _) D b
      have hV := prefixVolume535_first_prime s z
      have hT := allStopping535_first_prime s b D z
      cases b with
      | false =>
        simp only [Bool.false_eq_true, false_and, ↓reduceIte, Bool.not_false,
          zero_add] at hrec hT ⊢
        have hsum : (∑ p ∈ S, s.nu p * subsetMain535 s
            (S.filter (fun q => q < p)) (D / p) true) =
            (∑ p ∈ S, s.nu p * prefixVolume535 s p) +
              ∑ p ∈ S, s.nu p * allStopping535 s true (D / p) p := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          rw [hchild p hp true]
          simp only [↓reduceIte]
          ring
        rw [hrec, hsum, hV, hT]
        change 1 - (_ + _) = 1 - _ + -_
        ring
      | true =>
        simp only [true_and, ↓reduceIte, Bool.not_true] at hrec hT ⊢
        have hsum : (∑ p ∈ S, if D ≤ (p : ℝ) ^ 3 then 0
            else s.nu p * subsetMain535 s (S.filter (fun q => q < p)) (D / p) false) =
            (∑ p ∈ S, s.nu p * prefixVolume535 s p) -
              (∑ p ∈ S, if D ≤ (p : ℝ) ^ 3 then s.nu p * prefixVolume535 s p else 0) -
              ∑ p ∈ S, if D ≤ (p : ℝ) ^ 3 then 0
                else s.nu p * allStopping535 s false (D / p) p := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          rw [hchild p hp false]
          simp only [Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> ring
        have hbase : stopping535 s 0 D z =
            ∑ p ∈ S, if D ≤ (p : ℝ) ^ 3 then s.nu p * prefixVolume535 s p else 0 := by
          simp only [stopping535, prefixVolume535, Nat.cast_lt]
          rfl
        rw [hbase] at hT
        rw [hrec, hsum, hV, hT]
        change 1 - (_ - _ - _) = 1 - _ + (_ + _)
        ring
  exact haux _ z le_rfl D b

/-- Removing the first term from the complete upper stopping sum leaves
exactly the higher odd sum. Nathanson p. 242 equation 9.10. -/
theorem allStopping535_upper_eq_first_add (s : BoundingSieve) (D z : ℝ) :
    allStopping535 s true D z = stopping535 s 0 D z + higherOdd535 s D z := by
  have hpoint : ∀ k : ℕ,
      (if k % 2 = 0 then stopping535 s k D z else 0) =
        (if k = 0 then stopping535 s 0 D z else 0) +
          (if k % 2 = 0 ∧ 2 ≤ k then stopping535 s k D z else 0) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · by_cases he : k % 2 = 0
      · have hk2 : 2 ≤ k := by omega
        simp [hk, he, hk2]
      · simp [hk, he]
  by_cases hn : s.prodPrimes.primeFactors.card = 0
  · have hstop : stopping535 s 0 D z = 0 :=
      stopping535_eq_zero_of_card s 0 D z (by
        have hh := Finset.card_filter_le s.prodPrimes.primeFactors
          (fun p : ℕ => (p : ℝ) < z)
        omega)
    simp [allStopping535, higherOdd535, hn, hstop]
  · simp only [allStopping535, true_iff, hpoint, Finset.sum_add_distrib]
    have hsum : (∑ k ∈ Finset.range s.prodPrimes.primeFactors.card,
        if k = 0 then stopping535 s 0 D z else 0) = stopping535 s 0 D z := by
      simp [Nat.pos_of_ne_zero hn]
    rw [hsum]
    rfl

/-- The upper divisor defect moment is the complete odd stopping sum
normalized by the full sieve product. This connects Nathanson equation
9.10 to the original explicit Rosser weights without an analytic input. -/
theorem upper_defect_eq_stopping535 (s : BoundingSieve) (D z : ℝ)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) =
      allStopping535 s true D z /
        (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) := by
  have hfilter := Finset.filter_eq_self.mpr hP
  have hraw := subsetMain535_eq_stopping s D z true
  simp only [↓reduceIte] at hraw
  rw [hfilter, subsetMain535_eq_mainSum, rosser_mainSum_eq_defect] at hraw
  simp only [↓reduceIte, prefixVolume535, hfilter] at hraw
  have hV : 0 < ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_pos fun p hp => sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  apply (eq_div_iff hV.ne').mpr
  nlinarith only [hraw]

/-- The exact remaining expression in jr_upper_small_ratio326 is the
normalized higher odd stopping sum. This is the first term subtraction
in Nathanson p. 242 equation 9.10, with the original weights retained. -/
theorem upper_higher_defect_eq_stopping535 (s : BoundingSieve) (D z : ℝ)
    (hD : 0 < D) (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) -
        rosserFirstBoundary s (exp (log D / 3)) /
          (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) =
      higherOdd535 s D z / (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) := by
  rw [upper_defect_eq_stopping535 s D z hP, allStopping535_upper_eq_first_add,
    stopping535_zero_eq_first s D z hD hP]
  ring

/-- The integral range has no first stopping term, so its exact sealed
left side is again the normalized higher odd sum. Nathanson pp. 244 to
245 equation 9.13 on the range at least three. -/
theorem upper_integral_defect_eq_stopping535 (s : BoundingSieve) (D z : ℝ)
    (hz : 2 ≤ z) (hDz : z ^ 3 ≤ D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) =
      higherOdd535 s D z / (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) := by
  rw [upper_defect_eq_stopping535 s D z hP, allStopping535_upper_eq_first_add,
    stopping535_eq_zero_of_level s 0 D z hz (by simpa using hDz), zero_add]

/-- A direct insertion of the varying logarithmic scale into the printed
ninety nine hundredths contraction does not contract after a cube range
level reduction. This is a negative scalar result for the attempted
induction, not a counterexample to Nathanson p. 253 Theorem 9.5. -/
theorem stopping535_naive_contraction_fails :
    1 < (99 / 100 : ℝ) * (3 / 2 : ℝ) ^ (1 / 3 : ℝ) := by
  have hh : ((11 / 10 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) <
      (3 / 2 : ℝ) ^ (1 / 3 : ℝ) := by
    exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  rw [← rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 11 / 10) 3 (1 / 3 : ℝ)] at hh
  norm_num at hh
  nlinarith only [hh]

/-- The first explicit F range for the original remaining odd defect
follows from its actual cube endpoint estimate. This is CONDITIONAL ON
hend. The explicit error constant depends only on K and the endpoint
constant C. It contains no bounded cutoff parameter B.
Nathanson pp. 256 and 266 Theorems 9.6 and 9.8. -/
theorem upper_small_ratio_of_endpoint535 (s : BoundingSieve) (K C D z : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 8 ≤ D) (hz : 2 ≤ z) (hzD : z ≤ D)
    (hs3 : log D / log z ≤ 3)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hden : LinearDensity s K)
    (hend : higherOdd535 s D (exp (log D / 3)) ≤
      prefixVolume535 s (exp (log D / 3)) *
        ((2 * exp eulerMascheroniConstant - 3) / 3 +
          C * log D ^ (-(1 / 3 : ℝ)))) :
    (∑ n ∈ s.prodPrimes.divisors, s.selbergTerms n * rosserDefect D true n) -
        rosserFirstBoundary s (exp (log D / 3)) /
          (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) ≤
      (2 * exp eulerMascheroniConstant - 3) / (log D / log z) +
        (3 * (2 * exp eulerMascheroniConstant - 3) * K + 3 * C + 9 * K * C) *
          log D ^ (-(1 / 3 : ℝ)) := by
  have hA : 0 ≤ 2 * exp eulerMascheroniConstant - 3 := by
    linarith [LeanLab.AlmostPrimeSums.Decomp1527a.sieve_exp_gamma_bounds.1]
  have hDz : D ≤ z ^ 3 := by
    apply (log_le_log_iff (by linarith : 0 < D) (pow_pos (by linarith : 0 < z) 3)).mp
    rw [log_pow]
    norm_num
    exact (div_le_iff₀ (log_pos (by linarith : 1 < z))).mp hs3
  rw [upper_higher_defect_eq_stopping535 s D z (by linarith) hP]
  exact higherOdd535_small_of_endpoint s K (2 * exp eulerMascheroniConstant - 3) C D z
    hK hA hC hD hz hzD hDz hP hden hend

/-- On the integral F range the higher odd sum is exactly a weighted
prime sum of the complete even stopping sums. This is the alternating
recursion needed for an analytic induction. Nathanson p. 244 equation
9.14, after the vanishing first term is removed. -/
theorem higherOdd535_integral_recursion (s : BoundingSieve) (D z : ℝ)
    (hz : 2 ≤ z) (hDz : z ^ 3 ≤ D) :
    higherOdd535 s D z =
      ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z),
        s.nu p * allStopping535 s false (D / p) p := by
  have hh := allStopping535_first_prime s true D z
  rw [allStopping535_upper_eq_first_add,
    stopping535_eq_zero_of_level s 0 D z hz (by simpa using hDz)] at hh
  simp only [zero_add, ↓reduceIte, true_and, Bool.not_true] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro p hp
  have hc : (p : ℝ) ^ 3 < D :=
    (pow_lt_pow_left₀ (Finset.mem_filter.mp hp).2 (Nat.cast_nonneg p)
      (by norm_num : (3 : ℕ) ≠ 0)).trans_le hDz
  simp [not_le.mpr hc]

/-- The continuous higher odd coefficient has its exact alternating
integral recurrence on three through five. The initial value is the
explicit F formula at three. Nathanson p. 260 Lemma 9.10 and pp. 266 to
267 Theorem 9.8. This is a model identity, not a discrete comparison. -/
theorem sieve_remainder_integral535 (u : ℝ) (hu3 : 3 ≤ u) (hu5 : u ≤ 5) :
    u * (LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve u - 1) =
      2 * exp eulerMascheroniConstant - 3 -
        ∫ t in (3 : ℝ)..u, (1 - LeanLab.AlmostPrimeSums.Decomp1527a.fsieve (t - 1)) := by
  let F := LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve
  let f := LeanLab.AlmostPrimeSums.Decomp1527a.fsieve
  have hcf : ContinuousOn (fun t : ℝ => f (t - 1)) (Set.Icc 3 u) := by
    apply LeanLab.AlmostPrimeSums.Decomp1527a.fsieve_continuousOn.comp
      (continuousOn_id.sub continuousOn_const)
    intro t ht
    change 0 < t - 1
    linarith [ht.1]
  have hcF : ContinuousOn (fun t : ℝ => t * F t) (Set.Icc 3 u) := by
    apply continuousOn_id.mul
    apply LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve_continuousOn.mono
    intro t ht
    change 0 < t
    linarith [ht.1]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu3 hcF
    (fun t ht => LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve_hasDerivAt t
      (by linarith [ht.1]) (by linarith [ht.2])) (hcf.intervalIntegrable_of_Icc hu3)
  have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
    (f := fun _ : ℝ => (1 : ℝ)) intervalIntegrable_const
    (hcf.intervalIntegrable_of_Icc hu3)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hsub
  change (∫ t in (3 : ℝ)..u, f (t - 1)) = u * F u - 3 * F 3 at hi
  have hF3 : 3 * F 3 = 2 * exp eulerMascheroniConstant := by
    dsimp [F]
    rw [LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve_three]
    ring
  change u * (F u - 1) = 2 * exp eulerMascheroniConstant - 3 -
    ∫ t in (3 : ℝ)..u, (1 - f (t - 1))
  rw [hsub, hi, hF3]
  ring

/-- The cube endpoint input used in the first range transport has a
concrete nonempty density instance. This checks satisfiability only.
Nathanson p. 256 endpoint transport, derived finite model. -/
theorem stopping535_endpoint_instance : ∃ s : BoundingSieve,
    s.prodPrimes = 2 ∧ LinearDensity s (log 2) ∧
      higherOdd535 s 512 (exp (log 512 / 3)) ≤
        prefixVolume535 s (exp (log 512 / 3)) *
          ((2 * exp eulerMascheroniConstant - 3) / 3 +
            log (512 : ℝ) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨s, hP, _, _, hden, _⟩ := single_prime_density_instance
  have hzero : higherOdd535 s 512 (exp (log 512 / 3)) = 0 := by
    simp [higherOdd535, hP, Nat.prime_two.primeFactors]
  refine ⟨s, hP, hden, ?_⟩
  rw [hzero]
  apply mul_nonneg
  · unfold prefixVolume535
    exact Finset.prod_nonneg fun p hp => (sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))).le
  · have hA : 0 ≤ 2 * exp eulerMascheroniConstant - 3 := by
      linarith [LeanLab.AlmostPrimeSums.Decomp1527a.sieve_exp_gamma_bounds.1]
    positivity

/-- Every finite even part of the printed geometric error series is
strictly below fifty one. Nathanson p. 256, the geometric series estimate
in the proof of Theorem 9.6. -/
theorem stopping535_even_geometric_budget (N : ℕ) :
    (∑ k ∈ Finset.range N, (99 / 100 : ℝ) ^ (2 * k)) < 51 := by
  have hs : (∑ k ∈ Finset.range N, (99 / 100 : ℝ) ^ (2 * k)) =
      ∑ k ∈ Finset.range N, (9801 / 10000 : ℝ) ^ k := by
    simp_rw [pow_mul]
    norm_num
  rw [hs]
  have hh := geom_sum_mul (9801 / 10000 : ℝ) N
  have hp : 0 < (9801 / 10000 : ℝ) ^ N := pow_pos (by norm_num) _
  norm_num at hh
  nlinarith only [hh, hp]

end LeanLab.AlmostPrimeSums.Decomp1527b
