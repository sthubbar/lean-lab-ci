import LeanLab.ChenDoubleSieve.Decomp348h

/-!
Elementary removal of reciprocal totient weights in Wu 2004 equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39, prime sums before partial summation.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348

/-- A shifted reciprocal has a uniform relative error above a positive cutoff. -/
theorem reciprocal_shift_error {x z : ℝ} (hx : 2 ≤ x) (hz : 0 < z) (hzx : z ≤ x) :
    0 ≤ 1 / (x - 1) - 1 / x ∧
      1 / (x - 1) - 1 / x ≤ (2 / z) * (1 / x) ∧ 1 / (x - 1) ≤ 2 * (1 / x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hid : 1 / (x - 1) - 1 / x = 1 / (x * (x - 1)) := by field_simp; ring
  refine ⟨by rw [hid]; positivity, ?_, ?_⟩
  · rw [hid, show (2 / z) * (1 / x) = 2 / (z * x) by ring,
      div_le_div_iff₀ (mul_pos hx0 hx1) (mul_pos hz hx0)]
    have he := mul_le_mul_of_nonneg_right (show z ≤ 2 * (x - 1) by linarith) hx0.le
    nlinarith
  · rw [show 2 * (1 / x) = 2 / x by ring, div_le_div_iff₀ hx1 hx0]
    linarith

/-- The reciprocal totient error for a distinct prime pair saves an extra cutoff factor. -/
theorem reciprocal_totient_pair_error {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {z : ℝ} (hz : 0 < z) (hzp : z ≤ p) (hzq : z ≤ q) :
    |1 / (Nat.totient (p * q) : ℝ) - 1 / ((p : ℝ) * q)| ≤
      (6 / z) * (1 / ((p : ℝ) * q)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  obtain ⟨hp0, hpE, _⟩ := reciprocal_shift_error hpR hz hzp
  obtain ⟨hq0, hqE, hqT⟩ := reciprocal_shift_error hqR hz hzq
  have hφ : (Nat.totient (p * q) : ℝ) = ((p : ℝ) - 1) * ((q : ℝ) - 1) := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq),
      Nat.totient_prime hp, Nat.totient_prime hq]
    simp only [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le, Nat.cast_one]
  have hid : 1 / (Nat.totient (p * q) : ℝ) - 1 / ((p : ℝ) * q) =
      (1 / ((p : ℝ) - 1) - 1 / p) * (1 / ((q : ℝ) - 1)) +
      (1 / (p : ℝ)) * (1 / ((q : ℝ) - 1) - 1 / q) := by
    rw [hφ]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hid, abs_of_nonneg (add_nonneg (mul_nonneg hp0 (div_nonneg zero_le_one (by linarith)))
    (mul_nonneg (by positivity) hq0))]
  calc
    _ ≤ ((2 / z) * (1 / (p : ℝ))) * (2 * (1 / (q : ℝ))) +
        (1 / (p : ℝ)) * ((2 / z) * (1 / (q : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul hpE hqT (div_nonneg zero_le_one (by linarith)) (by positivity)
      · exact mul_le_mul_of_nonneg_left hqE (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

/-- The error from replacing phi of p q by p q is bounded on any finite prime pair domain. -/
theorem totient_sum_error (R : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℝ)
    {M z : ℝ} (hM : 0 ≤ M) (hz : 0 < z)
    (hR : ∀ q ∈ R, q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧ z ≤ q.1 ∧ z ≤ q.2)
    (hg : ∀ q ∈ R, |g q| ≤ M) :
    |(∑ q ∈ R, g q / (Nat.totient (q.1 * q.2) : ℝ)) -
      ∑ q ∈ R, g q / ((q.1 : ℝ) * q.2)| ≤ (6 * M / z) * pairMass R := by
  have he : (∑ q ∈ R, g q / (Nat.totient (q.1 * q.2) : ℝ)) -
      ∑ q ∈ R, g q / ((q.1 : ℝ) * q.2) =
      ∑ q ∈ R, g q * (1 / (Nat.totient (q.1 * q.2) : ℝ) - 1 / ((q.1 : ℝ) * q.2)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intros
    ring
  rw [he]
  calc
    _ ≤ ∑ q ∈ R, |g q * (1 / (Nat.totient (q.1 * q.2) : ℝ) -
        1 / ((q.1 : ℝ) * q.2))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ R, (6 * M / z) * (1 / ((q.1 : ℝ) * q.2)) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hp, hq', hpq, hzp, hzq⟩ := hR q hq
      rw [abs_mul]
      calc
        _ ≤ M * ((6 / z) * (1 / ((q.1 : ℝ) * q.2))) :=
          mul_le_mul (hg q hq) (reciprocal_totient_pair_error hp hq' hpq hz hzp hzq)
            (abs_nonneg _) hM
        _ = _ := by ring
    _ = _ := by simp only [pairMass, mul_sum]

/-- The full reciprocal mass of a pair rectangle is at most a squared harmonic bound. -/
theorem pairMass_le_log_square (P Q : Finset ℕ) (R : Finset (ℕ × ℕ))
    {N : ℕ} (hN : 1 ≤ N) (hsub : R ⊆ P ×ˢ Q)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ p ≤ N) (hQ : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) :
    pairMass R ≤ (1 + log N) ^ 2 := by
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ pairMass (P ×ˢ Q) := pairMass_mono hsub
    _ = (∑ p ∈ P, 1 / (p : ℝ)) * (∑ q ∈ Q, 1 / (q : ℝ)) := pairMass_product P Q
    _ ≤ (1 + log N) * (1 + log N) :=
      mul_le_mul (reciprocal_sum_le P N hP) (reciprocal_sum_le Q N hQ)
        (sum_nonneg (by intros; positivity)) (by linarith)
    _ = _ := by ring

/-- The explicit reciprocal totient error bound tends to zero for every power cutoff. -/
theorem totient_bound_tendsto {κ : ℝ} (hκ : 0 < κ) (M : ℝ) :
    Tendsto (fun x : ℝ => (6 * M / x ^ κ) * (1 + log x) ^ 2) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => 1 / x ^ κ) atTop (𝓝 0) := by
    simpa only [rpow_zero] using
      (isLittleO_log_rpow_rpow_atTop (0 : ℝ) hκ).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => log x / x ^ κ) atTop (𝓝 0) := by
    simpa only [rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hκ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => log x ^ 2 / x ^ κ) atTop (𝓝 0) := by
    simpa only [rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hκ).tendsto_div_nhds_zero
  have ht := ((h0.add (h1.const_mul 2)).add h2).const_mul (6 * M)
  convert ht using 1
  · ext x
    ring
  · simp

end LeanLab.ChenDoubleSieve.Task348
