/-
P0069, Section 3, pages 11 to 15. Finer leaves for the mean value
input used by the sieve decomposition in DecompC165b.
Every analytic leaf is OPEN. The exact final assembly is CONDITIONAL.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165
import LeanLab.BHP1997.Thm4Exponents
import LeanLab.Akeno2026.Decomp86

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- Pages 11 and 12. The multiplicative character weight in each Dirichlet term. -/
noncomputable def characterWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℕ →* ℂ where
  toFun n := χ (n : ZMod q) / (n : ℂ) ^ s
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
    exact mul_div_mul_comm _ _ _ _
/-- Pages 11 and 12. The coefficient sequence truncated to the actual polynomial support.
Multiplication in the Mathlib monoid algebra is finite Dirichlet convolution. -/
noncomputable def truncatedCoeffs (a : ℕ → ℂ) (c1 c2 F : ℝ) : MonoidAlgebra ℂ ℕ :=
  ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F), MonoidAlgebra.single n (a n)
/-- Page 12, the polynomial is evaluation of its truncated coefficient algebra. -/
theorem dirPoly_eq_lift (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Thm4.dirPoly a c1 c2 F χ s =
      MonoidAlgebra.lift ℂ ℂ ℕ (characterWeight χ s) (truncatedCoeffs a c1 c2 F) := by
  classical
  simp [truncatedCoeffs, Thm4.dirPoly, characterWeight, mul_div_assoc]

/-- LEAF. Page 11, Lemma 1, display 3.3. Montgomery reference 21,
Lemma 1.4 and Theorem 6.4. The hybrid mean square estimate is CITED.
This leaf is OPEN and does not follow from the finite kernel estimates. -/
theorem hybrid_mean_square : Lemma1MeanSquare := by
  sorry

/-- LEAF. Page 11, Lemma 1, display 3.4. Page 12 cites Montgomery
reference 21, Theorem 8.3, then Huxley reference 14, Section 2.
The weak Chebyshev consequence of 3.3 is insufficient. CITED and OPEN. -/
theorem hybrid_large_values : Lemma1LargeValues := by
  sorry

/-- LEAF. Pages 12 to 15, Theorem 4 proof. Dyadically split the three
norms, apply 3.3 and 3.4 to the powers of each polynomial, and sum the
resulting level sets. The finite exponent inequalities in all four cases
are proved in Thm4Exponents. The remaining polynomial power coefficients,
dyadic decomposition and norm interpolation form this OPEN analytic leaf.
The coefficient divisor exponent determines the small epsilon cutoff. -/
theorem dyadic_mean_value (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues) :
    Thm4.Theorem4Paper := by
  sorry

/-- Pages 11 to 15, the exact Section 3 mean value statement used by
DecompC165b.section3_mean_values. CONDITIONAL on the three OPEN leaves.
There is no direct sorry in this assembly. -/
theorem section3_mean_values : Thm4.Theorem4Paper := by
  exact dyadic_mean_value hybrid_mean_square hybrid_large_values

/-- Page 12, powers are evaluated finite Dirichlet convolutions. -/
theorem dirPoly_pow_eq_lift (a : ℕ → ℂ) (c1 c2 F : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (g : ℕ) :
    Thm4.dirPoly a c1 c2 F χ s ^ g =
      MonoidAlgebra.lift ℂ ℂ ℕ (characterWeight χ s) (truncatedCoeffs a c1 c2 F ^ g) := by
  rw [dirPoly_eq_lift, map_pow]

/-- Pages 11 and 12, truncation preserves precisely the support coefficients. -/
theorem truncatedCoeffs_coeff (a : ℕ → ℂ) (c1 c2 F : ℝ) (n : ℕ) :
    (truncatedCoeffs a c1 c2 F).coeff n =
      if c1 * F < n ∧ (n : ℝ) < c2 * F then a n else 0 := by
  classical
  have hrange (h : (n : ℝ) < c2 * F) : n < ⌊c2 * F⌋₊ + 1 := by
    exact Nat.lt_succ_of_le (Nat.le_floor h.le)
  simp only [truncatedCoeffs, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases h : c1 * F < n ∧ (n : ℝ) < c2 * F
  · simp [h, Finset.mem_filter, Finset.mem_range, hrange h.2]
  · simp [h, Finset.mem_filter]

/-- Page 12, convolution support is multiplicative in its length. -/
theorem coeff_pow_bounds (p : MonoidAlgebra ℂ ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hp : ∀ n ∈ p.coeff.support, lo ≤ n ∧ (n : ℝ) ≤ hi) (g : ℕ) :
    ∀ n ∈ (p ^ g).coeff.support, lo ^ g ≤ n ∧ (n : ℝ) ≤ hi ^ g := by
  classical
  induction g with
  | zero =>
    intro n hn
    have : n = 1 := by simpa [MonoidAlgebra.one_def] using hn
    subst n
    simp
  | succ g ih =>
    intro n hn
    rw [pow_succ] at hn
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp
      (MonoidAlgebra.support_coeff_mul_subset _ _ hn)
    obtain ⟨hu1, hu2⟩ := ih u hu
    obtain ⟨hv1, hv2⟩ := hp v hv
    push_cast
    rw [pow_succ, pow_succ]
    exact ⟨mul_le_mul hu1 hv1 hlo.le (by positivity),
      mul_le_mul hu2 hv2 (hlo.le.trans hv1) (by positivity)⟩

/-- Page 12, positive convolution powers have strict multiplicative support endpoints. -/
theorem coeff_pow_strict_bounds (p : MonoidAlgebra ℂ ℕ) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hp : ∀ n ∈ p.coeff.support, lo < n ∧ (n : ℝ) < hi) (g : ℕ) (hg : 0 < g) :
    ∀ n ∈ (p ^ g).coeff.support, lo ^ g < n ∧ (n : ℝ) < hi ^ g := by
  classical
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
  intro n hn
  rw [pow_succ] at hn
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp
    (MonoidAlgebra.support_coeff_mul_subset _ _ hn)
  obtain ⟨hu1, hu2⟩ := coeff_pow_bounds p hlo hhi.le
    (fun n hn => ⟨(hp n hn).1.le, (hp n hn).2.le⟩) g u hu
  obtain ⟨hv1, hv2⟩ := hp v hv
  push_cast
  rw [pow_succ, pow_succ]
  constructor
  · calc
      lo ^ g * lo < lo ^ g * v := mul_lt_mul_of_pos_left hv1 (pow_pos hlo _)
      _ ≤ u * v := mul_le_mul_of_nonneg_right hu1 (hlo.le.trans hv1.le)
  · calc
      (u : ℝ) * v ≤ hi ^ g * v := mul_le_mul_of_nonneg_right hu2 (hlo.le.trans hv1.le)
      _ < hi ^ g * hi := mul_lt_mul_of_pos_left hv2 (pow_pos hhi _)

/-- Page 12, a finite convolution with the indicated support is a Dirichlet polynomial. -/
theorem lift_eq_dirPoly (p : MonoidAlgebra ℂ ℕ) (c1 c2 F : ℝ)
    (hp : ∀ n ∈ p.coeff.support, c1 * F < n ∧ (n : ℝ) < c2 * F)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    MonoidAlgebra.lift ℂ ℂ ℕ (characterWeight χ s) p =
      Thm4.dirPoly p.coeff c1 c2 F χ s := by
  classical
  have hsub : p.coeff.support ⊆ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
      (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_floor (hp n hn).2.le)), hp n hn⟩
  rw [MonoidAlgebra.lift_apply', Finsupp.sum_of_support_subset p.coeff hsub]
  · simp [Thm4.dirPoly, characterWeight, mul_div_assoc]
  · intro n hn; simp

/-- Page 12, display 3.10. A positive polynomial power is a polynomial of its truncated convolution. -/
theorem dirPoly_pow (a : ℕ → ℂ) {c1 c2 F : ℝ}
    (hc1 : 0 < c1) (hc2 : c1 < c2) (hF : 0 < F)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (g : ℕ) (hg : 0 < g) :
    Thm4.dirPoly a c1 c2 F χ s ^ g =
      Thm4.dirPoly (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) χ s := by
  rw [dirPoly_pow_eq_lift]
  apply lift_eq_dirPoly
  have hp : ∀ n ∈ (truncatedCoeffs a c1 c2 F).coeff.support,
      c1 * F < n ∧ (n : ℝ) < c2 * F := by
    intro n hn
    have hn' := Finsupp.mem_support_iff.mp hn
    rw [truncatedCoeffs_coeff] at hn'
    split_ifs at hn' with h
    · exact h
    · exact False.elim (hn' rfl)
  intro n hn
  simpa only [mul_pow] using coeff_pow_strict_bounds (truncatedCoeffs a c1 c2 F)
    (mul_pos hc1 hF) (mul_pos (hc1.trans hc2) hF) hp g hg n hn

/-- Page 12, the finite convolution formula at a positive index. -/
theorem coeff_mul_divisors (p r : MonoidAlgebra ℂ ℕ) {n : ℕ} (hn : n ≠ 0) :
    (p * r).coeff n = ∑ d ∈ n.divisors, p.coeff d * r.coeff (n / d) := by
  rw [MonoidAlgebra.coeff_mul_antidiag p r n n.divisorsAntidiagonal
    (by intro z; simp [Nat.mem_divisorsAntidiagonal, hn])]
  exact Nat.sum_divisorsAntidiagonal (fun d e => p.coeff d * r.coeff e)

/-- Pages 11 and 12, finite convolution of sequences vanishing at zero also vanishes there. -/
theorem coeff_mul_zero (p r : MonoidAlgebra ℂ ℕ)
    (hp : p.coeff 0 = 0) (hr : r.coeff 0 = 0) : (p * r).coeff 0 = 0 := by
  classical
  by_contra h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_mul.mp
    (MonoidAlgebra.support_coeff_mul_subset _ _ (Finsupp.mem_support_iff.mpr h))
  rcases mul_eq_zero.mp huv with h | h
  · subst u; exact (Finsupp.mem_support_iff.mp hu) hp
  · subst v; exact (Finsupp.mem_support_iff.mp hv) hr

/-- Page 12, divisor counts increase along divisibility at a positive index. -/
theorem divisor_count_mono {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    (d.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd)

/-- Page 12, a divisor-bounded sequence can be bounded by the ambient index. -/
theorem coeff_bound_at_divisor {a : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (ha : Thm4.CoeffBound a B) {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    ‖a d‖ ≤ (n.divisors.card : ℝ) ^ B := by
  exact (ha d).trans (Real.rpow_le_rpow (by positivity) (divisor_count_mono hn hd) hB)

/-- Page 12, convolution increases the divisor exponent by at most the sum plus one. -/
theorem coeff_mul_bound (p r : MonoidAlgebra ℂ ℕ) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0)
    (hp : Thm4.CoeffBound p.coeff B) (hr : Thm4.CoeffBound r.coeff D) :
    Thm4.CoeffBound (p * r).coeff (B + D + 1) := by
  intro n
  by_cases hn : n = 0
  · subst n
    rw [coeff_mul_zero p r hp0 hr0, norm_zero]
    positivity
  have ht : 0 < (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  rw [coeff_mul_divisors p r hn]
  calc
    ‖∑ d ∈ n.divisors, p.coeff d * r.coeff (n / d)‖ ≤
        ∑ d ∈ n.divisors, ‖p.coeff d * r.coeff (n / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (n.divisors.card : ℝ) ^ B * (n.divisors.card : ℝ) ^ D := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      exact mul_le_mul (coeff_bound_at_divisor hB hp hn (Nat.mem_divisors.mp hd).1)
        (coeff_bound_at_divisor hD hr hn (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1))
        (norm_nonneg _) (by positivity)
    _ = (n.divisors.card : ℝ) ^ (B + D + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Real.rpow_add ht, Real.rpow_add ht, Real.rpow_one]
      ring

/-- Page 12, every convolution power of a zero-at-zero sequence still vanishes at zero. -/
theorem coeff_pow_zero (p : MonoidAlgebra ℂ ℕ) (hp : p.coeff 0 = 0) (g : ℕ) :
    (p ^ g).coeff 0 = 0 := by
  induction g with
  | zero => simp [MonoidAlgebra.one_def]
  | succ g ih => rw [pow_succ]; exact coeff_mul_zero _ _ ih hp

/-- Page 12, the convolution identity coefficient sequence has divisor exponent zero. -/
theorem coeff_one_bound : Thm4.CoeffBound (1 : MonoidAlgebra ℂ ℕ).coeff 0 := by
  intro n
  by_cases hn : n = 1 <;> simp [MonoidAlgebra.one_def, hn]

/-- Page 12, repeated convolution preserves a divisor bound with a larger exponent. -/
theorem coeff_pow_bound (p : MonoidAlgebra ℂ ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hp0 : p.coeff 0 = 0) (hp : Thm4.CoeffBound p.coeff B) (g : ℕ) :
    Thm4.CoeffBound (p ^ g).coeff ((g : ℝ) * (B + 1)) := by
  induction g with
  | zero => simpa using coeff_one_bound
  | succ g ih =>
    have hh := coeff_mul_bound (p ^ g) p (by positivity) hB (coeff_pow_zero p hp0 g) hp0 ih hp
    rw [pow_succ]
    convert hh using 1 <;> push_cast <;> ring

/-- Pages 11 and 12, increasing a divisor exponent preserves a zero-at-zero coefficient bound. -/
theorem coeffBound_mono {a : ℕ → ℂ} {B D : ℝ} (ha0 : a 0 = 0)
    (ha : Thm4.CoeffBound a B) (hBD : B ≤ D) : Thm4.CoeffBound a D := by
  intro n
  by_cases hn : n = 0
  · subst n; rw [ha0, norm_zero]; positivity
  have ht : 1 ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩
  exact (ha n).trans (Real.rpow_le_rpow_of_exponent_le ht hBD)

/-- Page 12, truncation preserves the original divisor bound. -/
theorem truncatedCoeffs_bound {a : ℕ → ℂ} {B : ℝ} (ha : Thm4.CoeffBound a B)
    (c1 c2 F : ℝ) : Thm4.CoeffBound (truncatedCoeffs a c1 c2 F).coeff B := by
  intro n
  rw [truncatedCoeffs_coeff]
  split_ifs
  · exact ha n
  · rw [norm_zero]; positivity

/-- Page 12, a positive lower support endpoint excludes coefficient zero. -/
theorem truncatedCoeffs_zero (a : ℕ → ℂ) {c1 c2 F : ℝ} (h : 0 ≤ c1 * F) :
    (truncatedCoeffs a c1 c2 F).coeff 0 = 0 := by
  rw [truncatedCoeffs_coeff]
  simp [not_lt_of_ge h]

/-- Pages 11 and 12, a uniform coefficient bound controls the normalized coefficient energy. -/
theorem energy_le_uniform (a : ℕ → ℂ) {c1 c2 F M : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hF : 1 ≤ F) (hM : 0 ≤ M)
    (ha : ∀ n : ℕ, c1 * F < n → (n : ℝ) < c2 * F → ‖a n‖ ≤ M) :
    energy a c1 c2 F ≤ (c2 + 1) / c1 * M ^ 2 := by
  classical
  let S := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hF0 : 0 < F := by linarith
  have hcard : (S.card : ℝ) ≤ (c2 + 1) * F := by
    have hh : S.card ≤ ⌊c2 * F⌋₊ + 1 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (show 0 ≤ c2 * F by positivity)
    have hh' : (S.card : ℝ) ≤ (⌊c2 * F⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    nlinarith
  calc
    energy a c1 c2 F ≤ ∑ _n ∈ S, M ^ 2 / (c1 * F) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
      have hn0 : 0 < (n : ℝ) := (mul_pos hc1 hF0).trans hn1
      exact (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (ha n hn1 hn2) 2) hn0.le).trans
        (div_le_div_of_nonneg_left (sq_nonneg M) (mul_pos hc1 hF0) hn1.le)
    _ = (S.card : ℝ) * (M ^ 2 / (c1 * F)) := by simp
    _ ≤ ((c2 + 1) * F) * (M ^ 2 / (c1 * F)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (c2 + 1) / c1 * M ^ 2 := by field_simp

/-- Pages 11 and 12, a positive-power divisor bound gives positive-power coefficient growth. -/
theorem coeff_small_power
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    : ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ δ := by
  have hB1 : 0 < B + 1 := by linarith
  obtain ⟨C, hC, hbound⟩ := Akeno2026.Decomp86.card_divisors_le_rpow (ε := δ / (B + 1)) (div_pos hδ hB1)
  refine ⟨C ^ B, Real.rpow_pos_of_pos hC _, ?_⟩
  intro a ha n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have he : δ / (B + 1) * B ≤ δ := by
    have hh := div_mul_cancel₀ δ (ne_of_gt hB1)
    nlinarith [div_pos hδ hB1]
  calc
    ‖a n‖ ≤ (n.divisors.card : ℝ) ^ B := ha n
    _ ≤ (C * (n : ℝ) ^ (δ / (B + 1))) ^ B :=
      Real.rpow_le_rpow (by positivity) (hbound n) hB
    _ = C ^ B * (n : ℝ) ^ (δ / (B + 1) * B) := by
      rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by positivity)]
    _ ≤ C ^ B * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 he) (by positivity)

/-- Page 12, the coefficient energy is bounded by every positive power of the length. -/
theorem energy_small_power
    {B δ c1 c2 : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ F : ℝ, 1 ≤ F → energy a c1 c2 F ≤ C * F ^ δ := by
  obtain ⟨K, hK, hbound⟩ := coeff_small_power hB
    (show 0 < δ / 2 by linarith)
  refine ⟨(c2 + 1) / c1 * K ^ 2 * c2 ^ δ, by positivity, ?_⟩
  intro a ha F hF
  have hF0 : 0 < F := by linarith
  calc
    energy a c1 c2 F ≤ (c2 + 1) / c1 * (K * (c2 * F) ^ (δ / 2)) ^ 2 := by
      apply energy_le_uniform a hc1 hc2 hF (by positivity)
      intro n hn1 hn2
      have hn0 : 0 < (n : ℝ) := (mul_pos hc1 hF0).trans hn1
      have hn : 1 ≤ n := by exact_mod_cast (show 0 < (n : ℝ) from hn0)
      exact (hbound a ha n hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hn2.le (by linarith)) hK.le)
    _ = ((c2 + 1) / c1 * K ^ 2 * c2 ^ δ) * F ^ δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      norm_num
      rw [Real.mul_rpow hc2.le hF0.le]
      ring

/-- Page 12, apply moment estimates at a larger ambient x when taking a polynomial power. -/
theorem power_ambient_range {x F T : ℝ} {q g : ℕ}
    (hx : 2 ≤ x) (hF : 2 ≤ F) (hFx : F ≤ x) (hT : T ≤ x / 4)
    (hq : (q : ℝ) ≤ x) (hg : 1 ≤ g) :
    2 ≤ x ^ g ∧ 2 ≤ F ^ g ∧ F ^ g ≤ x ^ g ∧
      T ≤ x ^ g / 4 ∧ (q : ℝ) ≤ x ^ g ∧ Real.log (x ^ g) = (g : ℝ) * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hF1 : 1 ≤ F := by linarith
  have hxpow : x ≤ x ^ g := le_self_pow₀ hx1 (by omega)
  have hFpow : F ≤ F ^ g := le_self_pow₀ hF1 (by omega)
  exact ⟨hx.trans hxpow, hF.trans hFpow, pow_le_pow_left₀ (by linarith) hFx g,
    hT.trans (div_le_div_of_nonneg_right hxpow (by norm_num)), hq.trans hxpow,
    Real.log_pow x g⟩

/-- Page 12, display 3.10. Truncated convolution powers obey a uniform enlarged divisor exponent. -/
theorem truncated_power_bound {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (ha : Thm4.CoeffBound a B) (hc1 : 0 ≤ c1) (hF : 0 ≤ F) (g : ℕ) :
    Thm4.CoeffBound (truncatedCoeffs a c1 c2 F ^ g).coeff
      ((g : ℝ) * (max B 0 + 1)) := by
  have hz := truncatedCoeffs_zero a (c2 := c2) (mul_nonneg hc1 hF)
  exact coeff_pow_bound _ (le_max_right B 0) hz
    (coeffBound_mono hz (truncatedCoeffs_bound ha c1 c2 F) (le_max_left B 0)) g

/-- Page 12, display 3.10. Each fixed convolution power has energy bounded by every positive power of the original length. -/
theorem truncated_power_energy (B c1 c2 δ : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hδ : 0 < δ) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B → ∀ F : ℝ, 1 ≤ F →
      energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) ≤ C * F ^ δ := by
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨C, hC, he⟩ := energy_small_power
    (B := (g : ℝ) * (max B 0 + 1)) (by positivity) (div_pos hδ hgR)
    (pow_pos hc1 g) (pow_pos hc2 g)
  refine ⟨C, hC, ?_⟩
  intro a ha F hF
  have hh := he (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) (F ^ g) (one_le_pow₀ hF)
  rw [← Real.rpow_natCast_mul (by linarith : 0 ≤ F)] at hh
  have hexp : (g : ℝ) * (δ / (g : ℝ)) = δ := by field_simp
  rwa [hexp] at hh

/-- Page 12, display 3.10. The mean square input applies to every fixed polynomial power at a larger ambient x. -/
theorem power_mean_square (hmean : Lemma1MeanSquare) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∑ p ∈ S, ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖ ^ (2 * g)) ≤
        C * Real.log x * ((q : ℝ) * T + F ^ g) *
          energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) := by
  have hg0 : g ≠ 0 := by omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨C, hC, hm⟩ := hmean ((g : ℝ) * (max B 0 + 1)) (c1 ^ g) (c2 ^ g)
    (pow_pos hc1 _) (pow_lt_pow_left₀ hc2 hc1.le hg0)
  refine ⟨C * g, mul_pos hC hgR, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
  obtain ⟨hxg, hFg, hFxg, hTxg, hqxg, hlog⟩ := power_ambient_range hx hF hFx hTx hqx hg
  have hh := hm (x ^ g) (F ^ g) T q S (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) hxg hFg hFxg hT hTxg hq hqxg hspace htimes
  calc
    _ = ∑ p ∈ S, ‖Thm4.dirPoly (truncatedCoeffs a c1 c2 F ^ g).coeff
        (c1 ^ g) (c2 ^ g) (F ^ g) p.2 (Thm4.half p.1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← dirPoly_pow a hc1 hc2 (by linarith) p.2 (Thm4.half p.1) g (by omega), norm_pow,
        ← pow_mul, Nat.mul_comm g 2]
    _ ≤ _ := hh
    _ = _ := by rw [hlog]; ring

/-- Page 12, display 3.10. The large value input applies to each fixed power with ambient x enlarged. -/
theorem power_large_values (hlarge : Lemma1LargeValues) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      (S.card : ℝ) ≤ C * Real.log x ^ 2 *
        (energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) * F ^ g / V ^ (2 * g) +
          energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) ^ 3 *
            F ^ g * (q : ℝ) * T / V ^ (6 * g)) := by
  have hg0 : g ≠ 0 := by omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g by omega)
  obtain ⟨C, hC, hl⟩ := hlarge ((g : ℝ) * (max B 0 + 1)) (c1 ^ g) (c2 ^ g)
    (pow_pos hc1 _) (pow_lt_pow_left₀ hc2 hc1.le hg0)
  refine ⟨C * (g : ℝ) ^ 2, mul_pos hC (sq_pos_of_pos hgR), ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  obtain ⟨hxg, hFg, hFxg, hTxg, hqxg, hlog⟩ := power_ambient_range hx hF hFx hTx hqx hg
  have hh := hl (x ^ g) (F ^ g) T (V ^ g) q S (truncatedCoeffs a c1 c2 F ^ g).coeff
    (truncated_power_bound ha hc1.le (by linarith) g) hxg hFg hFxg hT hTxg hq hqxg
    (pow_pos hV _) hspace htimes (by
      intro p hp
      rw [← dirPoly_pow a hc1 hc2 (by linarith) p.2 (Thm4.half p.1) g (by omega), norm_pow]
      exact pow_le_pow_left₀ hV.le (hpoint p hp) g)
  calc
    (S.card : ℝ) ≤ _ := hh
    _ = _ := by
      simp only [hlog, mul_pow, ← pow_mul, Nat.mul_comm g 2, Nat.mul_comm g 6]
      ring

/-- Page 12, the integer dyadic levels between two positive norm cutoffs. -/
noncomputable def dyadicLevels (v V : ℝ) : Finset ℤ := Finset.Icc (Int.log 2 v) (Int.log 2 V)
/-- Page 12, a cell of the three polynomial norm levels. -/
noncomputable def dyadicCell {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    (k : ℤ × ℤ × ℤ) : Finset α := by
  classical
  exact S.filter (fun p => (Int.log 2 ‖f1 p‖, Int.log 2 ‖f2 p‖, Int.log 2 ‖f3 p‖) = k)
/-- Page 12, every value in a dyadic cell lies between its lower level and twice that level. -/
theorem dyadic_cell_bounds {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    (k : ℤ × ℤ × ℤ) {p : α} (hp : p ∈ dyadicCell S f1 f2 f3 k)
    (h1 : 0 < ‖f1 p‖) (h2 : 0 < ‖f2 p‖) (h3 : 0 < ‖f3 p‖) :
    (2 : ℝ) ^ k.1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ < 2 * (2 : ℝ) ^ k.1 ∧
    (2 : ℝ) ^ k.2.1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ < 2 * (2 : ℝ) ^ k.2.1 ∧
    (2 : ℝ) ^ k.2.2 ≤ ‖f3 p‖ ∧ ‖f3 p‖ < 2 * (2 : ℝ) ^ k.2.2 := by
  have he := (Finset.mem_filter.mp hp).2
  have hb (v : ℝ) (hv : 0 < v) :
      (2 : ℝ) ^ Int.log 2 v ≤ v ∧ v < 2 * (2 : ℝ) ^ Int.log 2 v := by
    refine ⟨Int.zpow_log_le_self (by norm_num) hv, ?_⟩
    simpa only [Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using
      (Int.lt_zpow_succ_log_self (R := ℝ) (by norm_num : 1 < 2) v)
  rw [← he]
  exact ⟨(hb _ h1).1, (hb _ h1).2, (hb _ h2).1, (hb _ h2).2, (hb _ h3).1, (hb _ h3).2⟩

/-- Page 12, the finite dyadic partition preserves the sum exactly. -/
theorem dyadic_partition {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    {v V : ℝ} (hv : 0 < v)
    (h1 : ∀ p ∈ S, v ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ V)
    (h2 : ∀ p ∈ S, v ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ V)
    (h3 : ∀ p ∈ S, v ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ V) (w : α → ℝ) :
    ∑ k ∈ dyadicLevels v V ×ˢ dyadicLevels v V ×ˢ dyadicLevels v V,
      ∑ p ∈ dyadicCell S f1 f2 f3 k, w p = ∑ p ∈ S, w p := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro p hp
  have hmem (f : α → ℂ) (h : v ≤ ‖f p‖ ∧ ‖f p‖ ≤ V) :
      Int.log 2 ‖f p‖ ∈ dyadicLevels v V := by
    exact Finset.mem_Icc.mpr ⟨Int.log_mono_right hv h.1,
      Int.log_mono_right (hv.trans_le h.1) h.2⟩
  exact Finset.mem_product.mpr ⟨hmem f1 (h1 p hp),
    Finset.mem_product.mpr ⟨hmem f2 (h2 p hp), hmem f3 (h3 p hp)⟩⟩

/-- Page 12, summing a uniform cell bound costs at most the cube of the number of levels. -/
theorem dyadic_sum_bound {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    {v V H : ℝ} (hv : 0 < v)
    (h1 : ∀ p ∈ S, v ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ V)
    (h2 : ∀ p ∈ S, v ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ V)
    (h3 : ∀ p ∈ S, v ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ V)
    (hcell : ∀ k ∈ dyadicLevels v V ×ˢ dyadicLevels v V ×ˢ dyadicLevels v V,
      (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤ H) :
    (∑ p ∈ S, ‖f1 p * f2 p * f3 p‖) ≤ (dyadicLevels v V).card ^ 3 * H := by
  classical
  rw [← dyadic_partition S f1 f2 f3 hv h1 h2 h3 (fun p => ‖f1 p * f2 p * f3 p‖)]
  calc
    _ ≤ ∑ _k ∈ dyadicLevels v V ×ˢ dyadicLevels v V ×ˢ dyadicLevels v V, H :=
      Finset.sum_le_sum hcell
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul]; ring

/-- Page 12, the number of dyadic levels is the explicit integer interval cardinality. -/
theorem dyadic_level_count (v V : ℝ) :
    (dyadicLevels v V).card = (Int.log 2 V - Int.log 2 v + 1).toNat := by
  simpa [dyadicLevels, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Int.card_Icc (Int.log 2 v) (Int.log 2 V)

/-- Page 12, the dyadic level count is at most the logarithmic range plus two. -/
theorem dyadic_level_count_le {v V : ℝ} (hv : 0 < v) (hV : v ≤ V) :
    ((dyadicLevels v V).card : ℝ) ≤ Real.logb 2 V - Real.logb 2 v + 2 := by
  have hm := Int.log_mono_right (b := 2) hv hV
  have hc : ((dyadicLevels v V).card : ℤ) = Int.log 2 V + 1 - Int.log 2 v :=
    Int.card_Icc_of_le (Int.log 2 v) (Int.log 2 V) (by omega)
  have hcR : ((dyadicLevels v V).card : ℝ) =
      (Int.log 2 V : ℝ) + 1 - (Int.log 2 v : ℝ) := by exact_mod_cast hc
  have hlow := Int.lt_floor_add_one (Real.logb 2 v)
  have hhigh := Int.floor_le (Real.logb 2 V)
  rw [show ⌊Real.logb 2 v⌋ = Int.log 2 v from
    Real.floor_logb_natCast (b := 2) hv.le] at hlow
  rw [show ⌊Real.logb 2 V⌋ = Int.log 2 V from
    Real.floor_logb_natCast (b := 2) (hv.le.trans hV)] at hhigh
  rw [hcR]
  linarith

/-- Page 12, points with one tiny polynomial have a direct product bound. -/
theorem tiny_product_bound {a b c : ℂ} {v U : ℝ} (hv : 0 ≤ v) (hU : 0 ≤ U)
    (ha : ‖a‖ ≤ U) (hb : ‖b‖ ≤ U) (hc : ‖c‖ ≤ U)
    (htiny : ‖a‖ ≤ v ∨ ‖b‖ ≤ v ∨ ‖c‖ ≤ v) :
    ‖a * b * c‖ ≤ v * U ^ 2 := by
  rw [norm_mul, norm_mul]
  rcases htiny with h | h | h
  · have hh := mul_le_mul (mul_le_mul h hb (norm_nonneg _) hv) hc
      (norm_nonneg _) (mul_nonneg hv hU)
    nlinarith
  · have hh := mul_le_mul (mul_le_mul ha h (norm_nonneg _) hU) hc
      (norm_nonneg _) (mul_nonneg hU hv)
    nlinarith
  · have hh := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hU) h
      (norm_nonneg _) (mul_nonneg hU hU)
    nlinarith

/-- Page 12, a tiny-value contribution costs at most the cardinality times its pointwise bound. -/
theorem tiny_sum_bound {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    {v U : ℝ} (hv : 0 ≤ v) (hU : 0 ≤ U)
    (h1 : ∀ p ∈ S, ‖f1 p‖ ≤ U) (h2 : ∀ p ∈ S, ‖f2 p‖ ≤ U)
    (h3 : ∀ p ∈ S, ‖f3 p‖ ≤ U) :
    (∑ p ∈ S.filter (fun p => ‖f1 p‖ ≤ v ∨ ‖f2 p‖ ≤ v ∨ ‖f3 p‖ ≤ v),
      ‖f1 p * f2 p * f3 p‖) ≤ (S.card : ℝ) * v * U ^ 2 := by
  classical
  let R := S.filter (fun p => ‖f1 p‖ ≤ v ∨ ‖f2 p‖ ≤ v ∨ ‖f3 p‖ ≤ v)
  calc
    (∑ p ∈ R, ‖f1 p * f2 p * f3 p‖) ≤ ∑ _p ∈ R, v * U ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpS := (Finset.mem_filter.mp hp).1
      exact tiny_product_bound hv hU (h1 p hpS) (h2 p hpS) (h3 p hpS)
        (Finset.mem_filter.mp hp).2
    _ = (R.card : ℝ) * (v * U ^ 2) := by simp
    _ ≤ (S.card : ℝ) * (v * U ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = (S.card : ℝ) * v * U ^ 2 := by ring

/-- Page 14, one finite power cutoff works uniformly in the theta parameter. -/
theorem exists_uniform_power_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ g0 : ℕ, 1 ≤ g0 ∧ ∀ θ : ℝ, 0 ≤ θ → θ < 1 → θ - ε / 2 < Thm4.d θ g0 := by
  obtain ⟨g0, hg0⟩ := exists_nat_gt (1 / ε)
  have hgpos : 0 < (g0 : ℝ) := (one_div_pos.mpr hε).trans hg0
  refine ⟨g0, by exact_mod_cast (show (0 : ℝ) < g0 from hgpos), ?_⟩
  intro θ hθ0 hθ1
  have hh := Thm4.theta_sub_d θ g0 (Nat.cast_nonneg _)
  have hd : 0 < 2 * (g0 : ℝ) + 1 := by positivity
  have he : (1 - θ) / (2 * (g0 : ℝ) + 1) < ε / 2 := by
    rw [div_lt_iff₀ hd]
    have hg := (div_lt_iff₀ hε).mp hg0
    nlinarith
  linarith

/-- Pages 12 to 14, the admissible first exponent selects one of finitely many polynomial powers. -/
theorem exists_bounded_power {ε θ m n : ℝ} {g0 : ℕ} (hε : 0 < ε)
    (hθ : θ < 7 / 12) (h36 : |m - n| < 2 * θ - 1 - ε)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε) (hl : 0 ≤ 1 - m - n)
    (hg0 : θ - ε / 2 < Thm4.d θ g0) :
    ∃ g : ℕ, 1 ≤ g ∧ g ≤ g0 ∧ Thm4.d θ ((g : ℝ) - 1) < m ∧ m ≤ Thm4.d θ g := by
  obtain ⟨hm0, hm1⟩ := Thm4.alpha1_range hε (by linarith) h36 h37 hl
  exact Thm4.exists_g g0 hm0 (hm1.trans hg0).le

/-- Pages 12 to 15, every fixed logarithmic loss is bounded by a small positive power. -/
theorem log_power_le_small_power {x A δ : ℝ} (hx : 1 ≤ x) (hA : 0 < A) (hδ : 0 < δ) :
    Real.log x ^ A ≤ (δ / A) ^ (-A) * x ^ δ := by
  have hx0 : 0 < x := by linarith
  have he : 0 < δ / A := div_pos hδ hA
  have hh := Real.rpow_le_rpow (Real.log_nonneg hx) (Real.log_le_rpow_div hx0.le he) hA.le
  calc
    Real.log x ^ A ≤ (x ^ (δ / A) / (δ / A)) ^ A := hh
    _ = (δ / A) ^ (-A) * x ^ δ := by
      rw [Real.div_rpow (by positivity) he.le, ← Real.rpow_mul hx0.le,
        div_mul_cancel₀ δ (ne_of_gt hA), Real.rpow_neg he.le A]
      ring

/-- Pages 12 to 15, a fixed power saving supplies every required logarithmic saving. -/
theorem power_saving_to_log_saving {x A δ β : ℝ}
    (hx : 1 < x) (hA : 0 < A) (hδ : 0 < δ) :
    x ^ (β - δ) ≤ (δ / A) ^ (-A) * x ^ β * Real.log x ^ (-A) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_neg hlog.le A, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hlog A)]
  calc
    x ^ (β - δ) * Real.log x ^ A ≤ x ^ (β - δ) * ((δ / A) ^ (-A) * x ^ δ) :=
      mul_le_mul_of_nonneg_left (log_power_le_small_power hx.le hA hδ) (by positivity)
    _ = (δ / A) ^ (-A) * x ^ β := by
      rw [mul_left_comm, ← Real.rpow_add hx0, sub_add_cancel]

/-- Page 13, Case 2 i has an epsilon over four power saving. -/
theorem case2i_margin {θ ε l : ℝ} (hl : l < Thm4.gam θ - ε) :
    (1 - θ) + l / 4 < 1 / 2 - ε / 4 := by
  have := Thm4.gam_le_one θ
  linarith

/-- Page 13, the first term of Case 2 ii has saving eleven epsilon over twenty-four. -/
theorem case2ii_I1_margin {θ ε l : ℝ} (hl : l < Thm4.gam θ - ε) :
    5 / 6 * (1 - θ) + (1 - l) / 24 + l / 2 < 1 / 2 - 11 * ε / 24 := by
  have := Thm4.gam_le_two θ
  linarith

/-- Page 13, the second term of Case 2 ii has saving eleven epsilon over seventy-two. -/
theorem case2ii_I2_margin {θ ε l : ℝ} (hl : l < Thm4.gam θ - ε) :
    (1 - θ) + (1 - l) / 72 + l / 6 < 1 / 2 - 11 * ε / 72 := by
  have := Thm4.gam_le_three θ
  linarith

/-- Page 14, Case 3 i has an epsilon over four power saving. -/
theorem case3i_margin {θ ε m n : ℝ} (h36 : |m - n| < 2 * θ - 1 - ε) :
    m / 2 + (1 - θ) / 2 + (1 - m - n) / 4 < 1 / 2 - ε / 4 := by
  have := Thm4.eq314 h36
  linarith

/-- Page 14, repaired Case 3 ii first term has a uniform epsilon over four saving for g at least two. -/
theorem case3ii_T1_margin {θ ε m n g : ℝ} (hg : 2 ≤ g) (hε : 0 < ε)
    (h36 : |m - n| < 2 * θ - 1 - ε) (hd : Thm4.d θ (g - 1) < m) :
    m / 2 + (1 - m - n) / 2 + (1 / 2 - 1 / (2 * g)) * (1 - θ) + n / (4 * g) <
      1 / 2 - ε / 4 := by
  have h1 := Thm4.eq314 h36
  have h2 := Thm4.corrected_sign hd
  have hg0 : 0 < g := by linarith
  have hd0 : 0 < 2 * g - 1 := by linarith
  have hn : (2 * g - 2) * (1 - θ) + (2 * g - 1) * ε < (2 * g - 1) * n := by
    have hh : 1 - m - n + m + ε < (1 + (2 * g - 2) * θ) / (2 * g - 1) := by linarith
    rw [lt_div_iff₀ hd0] at hh
    nlinarith
  have hid : m / 2 + (1 - m - n) / 2 + (1 / 2 - 1 / (2 * g)) * (1 - θ) + n / (4 * g) -
      (1 / 2 - ε / 4) =
      ((2 * g - 2) * (1 - θ) - (2 * g - 1) * n + g * ε) / (4 * g) := by
    field_simp
    ring
  rw [← sub_neg, hid]
  have hgap : 0 ≤ (g - 1) * ε := mul_nonneg (by linarith) hε.le
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- Page 14, repaired Case 3 ii second term has a uniform epsilon over twelve saving. -/
theorem case3ii_T2_margin {θ ε m n g : ℝ} (hg : 1 ≤ g) (hε : 0 < ε)
    (h36 : |m - n| < 2 * θ - 1 - ε) (hd : m ≤ Thm4.d θ g) :
    m / 2 + (1 - m - n) / 6 + (1 - θ) / 2 + n / (12 * g) <
      1 / 2 - ε / 12 := by
  have h1 := Thm4.eq314 h36
  have h2 := Thm4.eq316_of_d hg hd
  have hg0 : 0 < g := by linarith
  have hd0 : 0 < 2 * g - 1 := by linarith
  have hl : (2 * g - 1) * (1 - m - n + ε) < 6 * g * θ - 1 - (6 * g - 1) * m := by
    have hh : 1 - m - n + ε < (6 * g * θ - 1 - (6 * g - 1) * m) / (2 * g - 1) := by linarith
    simpa only [mul_comm] using (lt_div_iff₀ hd0).mp hh
  have hid : m / 2 + (1 - m - n) / 6 + (1 - θ) / 2 + n / (12 * g) -
      (1 / 2 - ε / 12) =
      ((2 * g - 1) * (1 - m - n) - (6 * g * θ - 1 - (6 * g - 1) * m) + g * ε) / (12 * g) := by
    field_simp
    ring
  rw [← sub_neg, hid]
  have hgap : 0 ≤ (g - 1) * ε := mul_nonneg (by linarith) hε.le
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- Page 14, the repaired g equal to one branch has an absolute one over 144 power saving. -/
theorem g1_uniform_margin {θ ε m n σ : ℝ} (hε : 0 < ε) (hθ : θ < 7 / 12)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε) (hd : m ≤ Thm4.d θ 1)
    (hc : n * Thm4.c σ < 1 - θ) :
    m / 2 + (1 - m - n) / 2 + n * (σ - 1 / 2) < 1 / 2 - 1 / 144 := by
  have hh := (Thm4.g1_repair hε hθ h37 hd hc).2
  have hg := Thm4.gam_le_one θ
  have hd1 : Thm4.d θ 1 = (4 * θ - 1) / 3 := by unfold Thm4.d; ring
  rw [hd1] at hd
  have hmin : 1 / 144 < min (n / 4) (n / 2 - (1 - θ) / 4) := by
    apply lt_min <;> linarith
  linarith

/-- Pages 11 and 12, positive-index small-power growth holds for every real divisor exponent. -/
theorem coeff_small_power_any (B δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B →
      ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ δ := by
  obtain ⟨C, hC, hc⟩ := coeff_small_power (le_max_right B 0) hδ
  refine ⟨C, hC, ?_⟩
  intro a ha n hn
  let b : ℕ → ℂ := fun k => if k = 0 then 0 else a k
  have hb0 : b 0 = 0 := by simp [b]
  have hb : Thm4.CoeffBound b B := by
    intro k
    by_cases hk : k = 0
    · subst k; rw [hb0, norm_zero]; positivity
    · simpa [b, hk] using ha k
  have hh := hc b (coeffBound_mono hb0 hb (le_max_left B 0)) n hn
  simpa [b, show n ≠ 0 by omega] using hh

/-- Page 12, a uniform polynomial upper bound controls the finite dyadic range. -/
theorem dirPoly_norm_uniform (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ → ℂ, Thm4.CoeffBound a B → ∀ F : ℝ, 1 ≤ F →
      ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ≤ C * F ^ 2 := by
  classical
  obtain ⟨K, hK, hk⟩ := coeff_small_power_any B 1 (by norm_num)
  refine ⟨(c2 + 1) * K * c2, by positivity, ?_⟩
  intro a ha F hF q χ t
  have hF0 : 0 < F := by linarith
  let S := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  have hcard : (S.card : ℝ) ≤ (c2 + 1) * F := by
    have hh : S.card ≤ ⌊c2 * F⌋₊ + 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (show 0 ≤ c2 * F by positivity)
    have hh' : (S.card : ℝ) ≤ (⌊c2 * F⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    nlinarith
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ≤ K * c2 * F := by
    obtain ⟨hn1, hn2⟩ := (Finset.mem_filter.mp hn).2
    have hnpos : 0 < n := by exact_mod_cast ((mul_pos hc1 hF0).trans hn1)
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
    have hden : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hnR (by norm_num)
    rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
    have hre : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [hre]
    calc
      ‖a n‖ * ‖χ (n : ZMod q)‖ / (n : ℝ) ^ (1 / 2 : ℝ) ≤ ‖a n‖ * ‖χ (n : ZMod q)‖ :=
        div_le_self (by positivity) hden
      _ ≤ ‖a n‖ := mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      _ ≤ K * n := by simpa using hk a ha n (by omega)
      _ ≤ K * c2 * F := by nlinarith
  calc
    ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ≤ ∑ n ∈ S,
        ‖a n * χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, K * c2 * F := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (K * c2 * F) := by simp
    _ ≤ ((c2 + 1) * F) * (K * c2 * F) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((c2 + 1) * K * c2) * F ^ 2 := by ring

/-- Page 12, display 3.10. Chebyshev for the powered polynomial gives its level cardinality estimate. -/
theorem power_square_cardinal (hmean : Lemma1MeanSquare) (B c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      (S.card : ℝ) ≤ C * Real.log x * ((q : ℝ) * T + F ^ g) *
        energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) / V ^ (2 * g) := by
  obtain ⟨C, hC, hm⟩ := power_mean_square hmean B c1 c2 hc1 hc2 g hg
  refine ⟨C, hC, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hh := cardinal_of_square_sum S
    (fun p => Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1) ^ g) (pow_pos hV _)
    (by
      intro p hp
      rw [norm_pow]
      exact pow_le_pow_left₀ hV.le (hpoint p hp) g)
    (by
      simpa only [norm_pow, ← pow_mul, Nat.mul_comm g 2] using
        hm x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes)
  simpa only [← pow_mul, Nat.mul_comm g 2] using hh

/-- Page 12, combining the second and sixth moment alternatives gives the minimum in 3.10. -/
theorem level_min_of_bounds {R H P Q V : ℝ} (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hmean : R ≤ H * (P / V ^ 2 + Q / V ^ 2))
    (hlarge : R ≤ H * (P / V ^ 2 + P * Q / V ^ 6)) :
    R ≤ H * (P / V ^ 2 + Q * min (1 / V ^ 2) (P / V ^ 6)) := by
  have hh := le_min hmean hlarge
  have hid : min (H * (P / V ^ 2 + Q / V ^ 2))
      (H * (P / V ^ 2 + P * Q / V ^ 6)) =
      H * (P / V ^ 2 + Q * min (1 / V ^ 2) (P / V ^ 6)) := by
    rw [mul_min_of_nonneg _ _ hQ, mul_add, mul_add, min_add_add_left,
      ← mul_min_of_nonneg _ _ hH]
    ring
  rwa [hid] at hh

/-- Pages 13 and 14, weighted interpolation of three nonnegative cardinal bounds. -/
theorem interpolate_three_bounds {R A B C u v w : ℝ}
    (hR : 0 ≤ R) (hA : R ≤ A) (hB : R ≤ B) (hC : R ≤ C)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hsum : u + v + w = 1) :
    R ≤ A ^ u * B ^ v * C ^ w := by
  have hA0 : 0 ≤ A := hR.trans hA
  have hB0 : 0 ≤ B := hR.trans hB
  have hC0 : 0 ≤ C := hR.trans hC
  rcases hR.eq_or_lt with hzero | hpos
  · rw [← hzero]
    positivity
  calc
    R = R ^ u * R ^ v * R ^ w := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos, hsum, Real.rpow_one]
    _ ≤ A ^ u * B ^ v * C ^ w := by
      exact mul_le_mul (mul_le_mul
        (Real.rpow_le_rpow hR hA hu) (Real.rpow_le_rpow hR hB hv)
        (by positivity) (by positivity)) (Real.rpow_le_rpow hR hC hw)
        (by positivity) (by positivity)

/-- Page 12, a cell contributes at most eight times its cardinality times its three lower levels. -/
theorem dyadic_cell_sum_le {α : Type*} (S : Finset α) (f1 f2 f3 : α → ℂ)
    (k : ℤ × ℤ × ℤ)
    (hpos : ∀ p ∈ S, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖) :
    (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
      (dyadicCell S f1 f2 f3 k).card * (8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := by
  classical
  calc
    _ ≤ ∑ _p ∈ dyadicCell S f1 f2 f3 k,
        8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hpos p (Finset.mem_filter.mp hp).1
      obtain ⟨-, h1', -, h2', -, h3'⟩ := dyadic_cell_bounds S f1 f2 f3 k hp h1 h2 h3
      rw [norm_mul, norm_mul]
      have hh := mul_le_mul (mul_le_mul h1'.le h2'.le (norm_nonneg _) (by positivity))
        h3'.le (norm_nonneg _) (by positivity)
      nlinarith
    _ = _ := by simp

/-- Page 12, the cardinality terms for a polynomial power have exactly the printed exponents. -/
theorem power_level_exponents {F σ : ℝ} (hF : 1 ≤ F) (g : ℕ) :
    F ^ g / (F ^ (σ - 1 / 2)) ^ (2 * g) = (F ^ g) ^ (2 - 2 * σ) ∧
    1 / (F ^ (σ - 1 / 2)) ^ (2 * g) = (F ^ g) ^ (1 - 2 * σ) ∧
    F ^ g / (F ^ (σ - 1 / 2)) ^ (6 * g) = (F ^ g) ^ (4 - 6 * σ) := by
  have hF0 : 0 < F := by linarith
  have he (k : ℕ) : (F ^ (σ - 1 / 2)) ^ (k * g) =
      F ^ ((σ - 1 / 2) * ((k : ℝ) * g)) := by
    rw [← Real.rpow_mul_natCast hF0.le]
    norm_cast
  constructor
  · rw [he 2, ← Real.rpow_natCast F g, ← Real.rpow_sub hF0, ← Real.rpow_mul hF0.le]
    congr 1
    ring
  constructor
  · rw [he 2, one_div, ← Real.rpow_neg hF0.le, ← Real.rpow_natCast_mul hF0.le]
    congr 1
    ring
  · rw [he 6, ← Real.rpow_natCast F g, ← Real.rpow_sub hF0, ← Real.rpow_mul hF0.le]
    congr 1
    ring

/-- Pages 12 and 13, the minimum of the second and sixth moment powers is f of sigma. -/
theorem min_level_exponents {F σ : ℝ} (hF : 1 ≤ F) (g : ℕ) :
    min (1 / (F ^ (σ - 1 / 2)) ^ (2 * g))
      (F ^ g / (F ^ (σ - 1 / 2)) ^ (6 * g)) = (F ^ g) ^ Thm4.f σ := by
  obtain ⟨-, h2, h6⟩ := power_level_exponents hF g
  rw [h2, h6]
  unfold Thm4.f
  rcases le_total (1 - 2 * σ) (4 - 6 * σ) with h | h
  · rw [min_eq_left h, min_eq_left]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hF) h
  · rw [min_eq_right h, min_eq_right]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hF) h

/-- Page 12, one common coefficient-energy factor combines both supplied moment estimates. -/
theorem level_bound_of_energy {R Cm Cl L E G F Q V : ℝ}
    (hCm : 0 ≤ Cm) (hCl : 0 ≤ Cl) (hL : 0 ≤ L) (hE : 0 ≤ E) (hEG : E ≤ G)
    (hF : 0 ≤ F) (hQ : 0 ≤ Q) (hV : 0 < V)
    (hmean : R ≤ Cm * L * (Q + F) * E / V ^ 2)
    (hlarge : R ≤ Cl * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6)) :
    R ≤ (Cm + Cl) * (L + L ^ 2) * (G + G ^ 3) *
      (F / V ^ 2 + Q * min (1 / V ^ 2) (F / V ^ 6)) := by
  have hG : 0 ≤ G := hE.trans hEG
  have hG3 : 0 ≤ G ^ 3 := by positivity
  have hfactor : 0 ≤ (Cm + Cl) * (L + L ^ 2) * (G + G ^ 3) := by positivity
  apply level_min_of_bounds hfactor hQ
  · calc
      R ≤ Cm * L * (Q + F) * E / V ^ 2 := hmean
      _ ≤ (Cm + Cl) * (L + L ^ 2) * (Q + F) * (G + G ^ 3) / V ^ 2 := by
        gcongr
        · linarith
        · nlinarith [sq_nonneg L]
        · linarith
      _ = _ := by ring
  · have hE3 : E ^ 3 ≤ G ^ 3 := pow_le_pow_left₀ hE hEG 3
    have hE1 : E ≤ G + G ^ 3 := by linarith
    have hE3' : E ^ 3 ≤ G + G ^ 3 := by linarith
    calc
      R ≤ Cl * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6) := hlarge
      _ ≤ (Cm + Cl) * (L + L ^ 2) *
          ((G + G ^ 3) * F / V ^ 2 + (G + G ^ 3) * F * Q / V ^ 6) := by
        gcongr
        · linarith
        · linarith
      _ = _ := by ring

/-- Page 12, display 3.10. Both supplied moments give the exact minimum-form level bound for every fixed power. -/
theorem power_level_min (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      let E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g)
      (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
  obtain ⟨Cm, hCm, hm⟩ := power_square_cardinal hmean B c1 c2 hc1 hc2 g hg
  obtain ⟨Cl, hCl, hl⟩ := power_large_values hlarge B c1 c2 hc1 hc2 g hg
  refine ⟨Cm + Cl, add_pos hCm hCl, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hhM := hm x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hhL := hl x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  have hE : 0 ≤ energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g) := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hh := level_bound_of_energy (R := (S.card : ℝ)) (Cm := Cm) (Cl := Cl)
    (L := Real.log x) (E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g))
    (G := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g))
    (F := F ^ g) (Q := (q : ℝ) * T) (V := V ^ g)
    hCm.le hCl.le (Real.log_nonneg (by linarith)) hE (le_refl _)
    (by positivity) (by positivity) (pow_pos hV _)
    (by simpa only [← pow_mul, Nat.mul_comm g 2] using hhM)
    (by simpa only [← pow_mul, Nat.mul_comm g 2, Nat.mul_comm g 6, mul_assoc] using hhL)
  simpa only [← pow_mul, Nat.mul_comm g 2, Nat.mul_comm g 6, mul_assoc] using hh

/-- Pages 12 and 13, both branches of Case 2 give a uniform saving for a dyadic cell exponent. -/
theorem case2_cell_exponent {θ ε m n l σ1 σ2 σ3 s : ℝ}
    (hε : 0 < ε) (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l)
    (hsum : m + n + l = 1) (h37 : l < Thm4.gam θ - ε)
    (hM : s ≤ 1 - θ + m * Thm4.f σ1) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : s ≤ max (3 * l * (2 - 2 * σ3)) (1 - θ + 3 * l * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + l * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  by_cases h3 : σ3 ≤ 3 / 4
  · have hb := Thm4.case2i_bound (k := 1 - θ) (σ₁ := σ1) (σ₂ := σ2) hm hn hl h3
    have hf := case2i_margin h37
    nlinarith
  rcases le_max_iff.mp hL with hLa | hLb
  · have hi := Thm4.interp hM hN hLa
      (w₁ := 5 / 12) (w₂ := 5 / 12) (w₃ := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hb := Thm4.case2ii_I1 (1 - θ) m n l σ1 σ2 σ3 hm hn
    have hf := case2ii_I1_margin h37
    nlinarith
  · have hi := Thm4.interp hM hN hLb
      (w₁ := 17 / 36) (w₂ := 17 / 36) (w₃ := 1 / 18)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hb := Thm4.case2ii_I2 (1 - θ) m n l σ1 σ2 σ3 hm hn
    have hf := case2ii_I2_margin h37
    nlinarith

/-- Page 14, Case 3 i gives a uniform saving for a dyadic cell exponent. -/
theorem case3i_cell_exponent {θ ε m n σ1 σ2 σ3 s : ℝ}
    (hε : 0 < ε) (hn : 0 ≤ n) (hl : 0 ≤ 1 - m - n)
    (h36 : |m - n| < 2 * θ - 1 - ε) (h3 : σ3 ≤ 3 / 4)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  have hb := Thm4.case3i_bound (k := 1 - θ) (m := m) (σ₁ := σ1) (σ₂ := σ2) hn hl h3
  have hf := case3i_margin h36
  nlinarith

/-- Page 14, both Case 3 ii branches at g at least two give a uniform cell saving. -/
theorem case3ii_cell_exponent {θ ε m n σ1 σ2 σ3 s g : ℝ}
    (hε : 0 < ε) (hg : 2 ≤ g) (hn : 0 ≤ n)
    (h36 : |m - n| < 2 * θ - 1 - ε)
    (hdlo : Thm4.d θ (g - 1) < m) (hdhi : m ≤ Thm4.d θ g)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : s ≤ max (g * (1 - m - n) * (2 - 2 * σ3))
      (1 - θ + g * (1 - m - n) * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  have hg0 : 0 < g := by linarith
  have h2 : 1 / (2 * g) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h6 : 1 / (6 * g) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rcases le_max_iff.mp hL with hLa | hLb
  · have hi := Thm4.interp hM hN hLa
      (w₁ := 1 / 2) (w₂ := 1 / 2 - 1 / (2 * g)) (w₃ := 1 / (2 * g))
      (by norm_num) (by linarith) (by positivity) (by ring)
    have hb := Thm4.case3ii_T1 hg (1 - θ) m n (1 - m - n) σ1 σ2 σ3 hn
    have hf := case3ii_T1_margin hg hε h36 hdlo
    linarith
  · have hi := Thm4.interp hM hN hLb
      (w₁ := 1 / 2) (w₂ := 1 / 2 - 1 / (6 * g)) (w₃ := 1 / (6 * g))
      (by norm_num) (by linarith) (by positivity) (by ring)
    have hb := Thm4.case3ii_T2 (by linarith : 1 ≤ g) (1 - θ) m n (1 - m - n) σ1 σ2 σ3 hn
    have hf := case3ii_T2_margin (by linarith : 1 ≤ g) hε h36 hdhi
    linarith

/-- Page 14, the repaired g equal to one branch gives the same uniform cell saving. -/
theorem g1_cell_exponent {θ ε m n σ1 σ2 σ3 s : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) (hθ : θ < 7 / 12) (hn : 0 ≤ n)
    (h36 : |m - n| < 2 * θ - 1 - ε)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε) (hd : m ≤ Thm4.d θ 1)
    (hc : n * Thm4.c σ2 < 1 - θ)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : s ≤ max ((1 - m - n) * (2 - 2 * σ3))
      (1 - θ + (1 - m - n) * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  rcases le_max_iff.mp hL with hLa | hLb
  · have hf := g1_uniform_margin hε hθ h37 hd hc
    nlinarith
  · have hi := Thm4.interp hM hN hLb
      (w₁ := 1 / 2) (w₂ := 1 / 3) (w₃ := 1 / 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hb := Thm4.case3ii_T2 (g := 1) (by norm_num) (1 - θ) m n (1 - m - n) σ1 σ2 σ3 hn
    have hf := case3ii_T2_margin (g := 1) (by norm_num) hε h36 hd
    norm_num at hb hf
    linarith

/-- Page 13, Case 1 cancels the first two cell norm exponents exactly. -/
theorem case1_cell_exponent {m n σ1 σ2 s : ℝ}
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ n * (2 - 2 * σ2)) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) ≤ m / 2 + n / 2 := by
  have hh := Thm4.case1 m n σ1 σ2
  linarith

/-- Page 14, the mixed dominance case selects a bounded polynomial power and uses the repaired g equal to one branch. -/
theorem mixed_cell_exponent {θ ε m n σ1 σ2 σ3 s : ℝ} {g0 : ℕ}
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) (hθ : θ < 7 / 12)
    (hn : 0 ≤ n) (hl : 0 ≤ 1 - m - n)
    (h36 : |m - n| < 2 * θ - 1 - ε)
    (h37 : 1 - (m + n) < Thm4.gam θ - ε)
    (hcut : θ - ε / 2 < Thm4.d θ g0)
    (hc : n * Thm4.c σ2 < 1 - θ)
    (hM : s ≤ m * (2 - 2 * σ1)) (hN : s ≤ 1 - θ + n * Thm4.f σ2)
    (hL : ∀ g : ℕ, 1 ≤ g → g ≤ g0 →
      s ≤ max ((g : ℝ) * (1 - m - n) * (2 - 2 * σ3))
        (1 - θ + (g : ℝ) * (1 - m - n) * (4 - 6 * σ3))) :
    s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + (1 - m - n) * (σ3 - 1 / 2) <
      1 / 2 - ε / 72 := by
  by_cases h3 : σ3 ≤ 3 / 4
  · exact case3i_cell_exponent hε hn hl h36 h3 hM hN
  obtain ⟨g, hg1, hgg0, hdlo, hdhi⟩ := exists_bounded_power hε hθ h36 h37 hl hcut
  have hLg := hL g hg1 hgg0
  by_cases hg : g = 1
  · subst g
    simp only [Nat.cast_one, one_mul] at hLg hdhi
    exact g1_cell_exponent hε hεu hθ hn h36 h37 hdhi hc hM hN hLg
  · exact case3ii_cell_exponent hε (by exact_mod_cast (show 2 ≤ g by omega)) hn
      h36 hdlo hdhi hM hN hLg

/-- Pages 13 to 15, the four dominance cases reduce every cell to Case 1 or a uniform power saving. -/
theorem classify_cell_exponent {θ ε m n l σ1 σ2 σ3 s : ℝ} {g0 : ℕ}
    (hε : 0 < ε) (hεu : ε ≤ 1 / 2) (hθ : θ < 7 / 12)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hl : 0 ≤ l) (hsum : m + n + l = 1)
    (h36 : |m - n| < 2 * θ - 1 - ε) (h37 : l < Thm4.gam θ - ε)
    (hg0 : 3 ≤ g0) (hcut : θ - ε / 2 < Thm4.d θ g0)
    (hM : s ≤ max (m * (2 - 2 * σ1)) (1 - θ + m * Thm4.f σ1))
    (hN : s ≤ max (n * (2 - 2 * σ2)) (1 - θ + n * Thm4.f σ2))
    (hL : ∀ g : ℕ, 1 ≤ g → g ≤ g0 →
      s ≤ max ((g : ℝ) * l * (2 - 2 * σ3)) (1 - θ + (g : ℝ) * l * (4 - 6 * σ3))) :
    (s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) ≤ m / 2 + n / 2) ∨
    (s + m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + l * (σ3 - 1 / 2) < 1 / 2 - ε / 72) := by
  have hdom (a σ : ℝ) (hh : s ≤ max (a * (2 - 2 * σ)) (1 - θ + a * Thm4.f σ))
      (hd : 1 - θ ≤ a * Thm4.c σ) : s ≤ a * (2 - 2 * σ) := by
    rw [max_eq_left (Thm4.dominance.mpr hd)] at hh
    exact hh
  have hsmall (a σ : ℝ) (hh : s ≤ max (a * (2 - 2 * σ)) (1 - θ + a * Thm4.f σ))
      (hd : ¬ 1 - θ ≤ a * Thm4.c σ) : s ≤ 1 - θ + a * Thm4.f σ := by
    have hb : a * (2 - 2 * σ) ≤ 1 - θ + a * Thm4.f σ := by
      exact le_of_lt (lt_of_not_ge (fun h => hd (Thm4.dominance.mp h)))
    rwa [max_eq_right hb] at hh
  by_cases hdM : 1 - θ ≤ m * Thm4.c σ1
  · by_cases hdN : 1 - θ ≤ n * Thm4.c σ2
    · exact Or.inl (case1_cell_exponent (hdom m σ1 hM hdM) (hdom n σ2 hN hdN))
    · right
      have hlid : l = 1 - m - n := by linarith
      subst l
      exact mixed_cell_exponent hε hεu hθ hn hl h36 (by linarith) hcut
        (lt_of_not_ge hdN) (hdom m σ1 hM hdM) (hsmall n σ2 hN hdN) hL
  · by_cases hdN : 1 - θ ≤ n * Thm4.c σ2
    · right
      have hls : l = 1 - n - m := by linarith
      have hh := mixed_cell_exponent (m := n) (n := m) (σ1 := σ2) (σ2 := σ1)
        (σ3 := σ3) (s := s) hε hεu hθ hm (by linarith)
        (by simpa only [abs_sub_comm] using h36) (by linarith) hcut (lt_of_not_ge hdM)
        (hdom n σ2 hN hdN) (hsmall m σ1 hM hdM)
        (by intro g hg1 hgg0; simpa only [← hls] using hL g hg1 hgg0)
      rw [← hls] at hh
      linarith
    · right
      have hhL := hL 3 (by norm_num) hg0
      norm_num only [Nat.cast_ofNat] at hhL
      exact case2_cell_exponent hε hm hn hl hsum h37
        (hsmall m σ1 hM hdM) (hsmall n σ2 hN hdN) hhL

/-- Page 12, display 3.10 with an arbitrarily small power loss instead of a fixed logarithmic coefficient-energy loss. -/
theorem power_level_small_power (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (B c1 c2 δ : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) (hδ : 0 < δ) (g : ℕ) (hg : 1 ≤ g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      Thm4.CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x →
      2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x → 0 < V →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) →
      (S.card : ℝ) ≤ C * (1 + Real.log x) ^ 2 * F ^ δ *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
  obtain ⟨C0, hC0, hlevel⟩ := power_level_min hmean hlarge B c1 c2 hc1 hc2 g hg
  obtain ⟨D, hD, he⟩ := truncated_power_energy B c1 c2 (δ / 3) hc1 (hc1.trans hc2)
    (by linarith) g hg
  refine ⟨C0 * (D + D ^ 3), by positivity, ?_⟩
  intro x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  let E := energy (truncatedCoeffs a c1 c2 F ^ g).coeff (c1 ^ g) (c2 ^ g) (F ^ g)
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hEF : E ≤ D * F ^ (δ / 3) := he a ha F (by linarith)
  have hF0 : 0 < F := by linarith
  have hEcube : E ^ 3 ≤ D ^ 3 * F ^ δ := by
    calc
      E ^ 3 ≤ (D * F ^ (δ / 3)) ^ 3 := pow_le_pow_left₀ hE hEF 3
      _ = D ^ 3 * F ^ δ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hF0.le]
        norm_num
  have hEsingle : E ≤ D * F ^ δ := hEF.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) hD.le)
  have hEall : E + E ^ 3 ≤ (D + D ^ 3) * F ^ δ := by nlinarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogs : Real.log x + Real.log x ^ 2 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hh := hlevel x F T V q S a ha hx hF hFx hT hTx hq hqx hV hspace htimes hpoint
  change (S.card : ℝ) ≤ C0 * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * _ at hh
  calc
    (S.card : ℝ) ≤ _ := hh
    _ ≤ C0 * (1 + Real.log x) ^ 2 * ((D + D ^ 3) * F ^ δ) *
        (F ^ g / V ^ (2 * g) + (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) := by
      gcongr
    _ = _ := by ring

/-- Pages 12 and 13, a positive-power energy loss cannot be absorbed by a fixed logarithmic allowance in Case 1. -/
theorem positive_power_not_log_bounded {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → x ^ δ ≤ C * Real.log x ^ A := by
  rintro ⟨C, hC⟩
  let c := 1 / (|C| + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall := (isLittleO_log_rpow_rpow_atTop A hδ).def hc
  obtain ⟨x, hxsmall, hx⟩ := (hsmall.and (Filter.eventually_ge_atTop (2 : ℝ))).exists
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hxsmall
  have hpow : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 _
  have hratio : |C| * c < 1 := by
    dsimp [c]
    rw [one_div, ← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith
  have hh : x ^ δ ≤ |C| * (c * x ^ δ) := calc
    x ^ δ ≤ C * Real.log x ^ A := hC x hx
    _ ≤ |C| * Real.log x ^ A := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (c * x ^ δ) := mul_le_mul_of_nonneg_left hxsmall (abs_nonneg C)
  nlinarith [mul_lt_mul_of_pos_right hratio hpow]

/-- Page 13, Case 1 has a uniform constant energy bound when the original divisor exponent is nonpositive. -/
theorem energy_nonpositive_exponent {a : ℕ → ℂ} {B c1 c2 F : ℝ}
    (hB : B ≤ 0) (ha : Thm4.CoeffBound a B) (hc1 : 0 < c1) (hc2 : 0 < c2) (hF : 1 ≤ F) :
    energy a c1 c2 F ≤ (c2 + 1) / c1 := by
  have hh := energy_le_uniform a hc1 hc2 hF (M := 1) (by norm_num) (by
    intro n hn1 hn2
    have hn0 : n ≠ 0 := by
      intro he
      subst n
      have : 0 < c1 * F := mul_pos hc1 (by linarith)
      norm_num at hn1
      linarith
    have ht : 1 ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
    exact (ha n).trans (Real.rpow_le_one_of_one_le_of_nonpos ht hB))
  simpa using hh

end LeanLab.BHP1997.DecompC165c
