import LeanLab.AlmostPrimeSums.Decomp1527b

/-!
AI wrote this Lean code for CODEX task258. Goldbach is open.
The first Rosser stopping term is T1 of BJS p. 10 equation 28,
with level D equal to w cubed. The product difference and its density
bound are the base case printed on BJS p. 11.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- The first stopping term at the prime threshold w. It is T1 at level
w cubed for nonnegative w. BJS p. 10 equation 28. -/
noncomputable def rosserFirstBoundary (s : BoundingSieve) (w : ℝ) : ℝ :=
  ∑ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
    s.nu p * ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)

/-- The first stopping term is the lower cutoff product minus the full
sieve product. This is the T1 product difference on BJS p. 11. -/
theorem rosserFirstBoundary_eq_product_sub (s : BoundingSieve) (w : ℝ) :
    rosserFirstBoundary s w =
      (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < w), (1 - s.nu p)) -
        ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  classical
  let P := s.prodPrimes.primeFactors
  let L := P.filter (fun p : ℕ => (p : ℝ) < w)
  let f : ℕ → ℝ := fun p => s.nu p * ∏ q ∈ P.filter (fun q => q < p), (1 - s.nu q)
  have hprefix : ∀ p ∈ L, L.filter (fun q => q < p) = P.filter (fun q => q < p) := by
    intro p hp
    have hpw := (Finset.mem_filter.mp hp).2
    ext q
    simp only [L, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, _⟩, hqp⟩; exact ⟨hq, hqp⟩
    · rintro ⟨hq, hqp⟩
      exact ⟨⟨hq, (Nat.cast_lt.mpr hqp).trans hpw⟩, hqp⟩
  have hlow := Finset.prod_one_sub_ordered L s.nu
  have hsum : (∑ p ∈ L, s.nu p * ∏ q ∈ L.filter (fun q => q < p), (1 - s.nu q)) =
      ∑ p ∈ L, f p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hprefix p hp]
  rw [hsum] at hlow
  have hfull := Finset.prod_one_sub_ordered P s.nu
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) < w) f
  simp only [not_lt] at hsplit
  change (∑ p ∈ P.filter (fun p : ℕ => w ≤ (p : ℝ)), f p) =
    (∏ p ∈ L, (1 - s.nu p)) - ∏ p ∈ P, (1 - s.nu p)
  linarith

/-- The first stopping term is nonnegative. Derived sign consequence of
the finite expression in BJS p. 10 equation 28. -/
theorem rosserFirstBoundary_nonneg (s : BoundingSieve) (w : ℝ) :
    0 ≤ rosserFirstBoundary s w := by
  apply Finset.sum_nonneg
  intro p hp
  have hpP := (Finset.mem_filter.mp hp).1
  apply mul_nonneg (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
    (Nat.dvd_of_mem_primeFactors hpP)).le
  exact Finset.prod_nonneg fun q hq =>
    (sub_pos.mpr (s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1))).le

/-- Normalizing the first stopping term gives the inverse interval product
minus one. Derived finite form of the T1 identity on BJS p. 11. -/
theorem rosserFirstBoundary_eq_relative (s : BoundingSieve) (w z : ℝ)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    rosserFirstBoundary s w =
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        ((∏ p ∈ s.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - s.nu p)⁻¹) - 1) := by
  classical
  let Q := s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hfilter : s.prodPrimes.primeFactors.filter (fun p : ℕ => ¬(p : ℝ) < w) = Q := by
    ext p
    simp only [Q, Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hp, hw⟩; exact ⟨hp, hw, hP p hp⟩
    · rintro ⟨hp, hw, _⟩; exact ⟨hp, hw⟩
  have hsplit := Finset.prod_filter_mul_prod_filter_not s.prodPrimes.primeFactors
    (fun p : ℕ => (p : ℝ) < w) (fun p => 1 - s.nu p)
  rw [hfilter] at hsplit
  have hQ : (∏ p ∈ Q, (1 - s.nu p)) ≠ 0 :=
    (Finset.prod_pos fun p hp => sub_pos.mpr
      (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1))).ne'
  rw [rosserFirstBoundary_eq_product_sub]
  change _ = _ * ((∏ p ∈ Q, (1 - s.nu p)⁻¹) - 1)
  rw [Finset.prod_inv_distrib, ← hsplit]
  field_simp [hQ]

/-- The dimension one density condition bounds the first stopping term.
This is the base estimate on BJS p. 11, with the lab density parameter. -/
theorem rosserFirstBoundary_le_density (s : BoundingSieve) (K w z : ℝ)
    (h : LinearDensity s K) (hw : 2 ≤ w) (hwz : w < z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    rosserFirstBoundary s w ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (log z / log w * (1 + K / log w) - 1) := by
  rw [rosserFirstBoundary_eq_relative s w z hP]
  apply mul_le_mul_of_nonneg_left (sub_le_sub_right (h w z hw hwz) 1)
  exact Finset.prod_nonneg fun p hp =>
    (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp))).le

/-- If every sifting prime is below w, the first stopping term is zero.
This is the vanishing T1 case on BJS p. 11. -/
theorem rosserFirstBoundary_eq_zero (s : BoundingSieve) (w : ℝ)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < w) :
    rosserFirstBoundary s w = 0 := by
  have he : s.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    exact not_le_of_gt (hP p (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2
  simp [rosserFirstBoundary, he]

/-- The logarithmic threshold used for T1 has cube exactly D for positive
D. Derived change of parameter for BJS p. 11. -/
theorem rosser_first_threshold_cube (D : ℝ) (hD : 0 < D) :
    (exp (log D / 3)) ^ 3 = D := by
  rw [← exp_nat_mul]
  convert exp_log hD using 1 <;> congr 1 <;> ring

/-- The first stopping term vanishes when the sieve level is at least
z cubed. This extends the printed strict T1 range on BJS p. 11 to its endpoint. -/
theorem rosserFirstBoundary_zero_of_cube_le (s : BoundingSieve) (z D : ℝ)
    (hz : 2 ≤ z) (hD : z ^ 3 ≤ D)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    rosserFirstBoundary s (exp (log D / 3)) = 0 := by
  have hz0 : 0 < z := by linarith
  have hD0 : 0 < D := (pow_pos hz0 3).trans_le hD
  have hlog := log_le_log (pow_pos hz0 3) hD
  rw [log_pow] at hlog
  have hw : z ≤ exp (log D / 3) := by
    calc
      z = exp (log z) := (exp_log hz0).symm
      _ ≤ exp (log D / 3) := exp_le_exp.mpr (by norm_num at hlog; linarith)
  exact rosserFirstBoundary_eq_zero s _ fun p hp => (hP p hp).trans_le hw

/-- The first stopping term has the paper's three over s coefficient,
with the lab density loss made explicit. BJS p. 11, T1 base case. -/
theorem rosserFirstBoundary_le_three_div (s : BoundingSieve) (K z D : ℝ)
    (h : LinearDensity s K) (hz : 2 ≤ z) (hD : 1 < D)
    (hw : 2 ≤ exp (log D / 3)) (hwz : exp (log D / 3) < z)
    (hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    rosserFirstBoundary s (exp (log D / 3)) ≤
      (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) *
        (3 / (log D / log z) * (1 + 3 * K / log D) - 1) := by
  have hh := rosserFirstBoundary_le_density s K (exp (log D / 3)) z h hw hwz hP
  rw [log_exp] at hh
  have hlD : log D ≠ 0 := (log_pos hD).ne'
  have hlz : log z ≠ 0 := (log_pos (by linarith : 1 < z)).ne'
  convert hh using 1 <;> field_simp <;> ring

end LeanLab.AlmostPrimeSums.Decomp1527b
