/-
AI wrote this Lean code. Binary Goldbach is open.
HBP pages 30 to 31 displays 45 to 46 and P0026 page 174 display 4.10.
-/
import LeanLab.PlattTrudgian2014.Decomp421a

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Finset

/-- HBP page 31, a repeated phase multiplies its frequency. -/
theorem phase_nat_mul421 (u : ℝ) (n : ℕ) : phase (u * n) = phase u ^ n := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- HBP page 31, a single integer frequency has its largest grid sum at zero shift. -/
theorem phase_grid_max421 (k : ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ) :
    (∑ r ∈ range q, (phase ((k : ℝ) * ((β + r) / (q : ℝ)))).re) ≤
      ∑ r ∈ range q, (phase ((k : ℝ) * ((r : ℝ) / (q : ℝ)))).re := by
  let z : ℂ := phase ((k : ℝ) / q)
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hzq : z ^ q = 1 := by
    dsimp only [z]
    rw [← phase_nat_mul421]
    have he : (k : ℝ) / q * q = k := by field_simp [hqr]
    rw [he]
    unfold phase
    rw [Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  have he (γ : ℝ) :
      (∑ r ∈ range q, phase ((k : ℝ) * ((γ + r) / (q : ℝ)))) =
        phase ((k : ℝ) * γ / q) * ∑ r ∈ range q, z ^ r := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    dsimp only [z]
    rw [← phase_nat_mul421, phase_mul421]
    congr 1
    ring
  have he0 : (∑ r ∈ range q, phase ((k : ℝ) * ((r : ℝ) / (q : ℝ)))) =
      ∑ r ∈ range q, z ^ r := by
    simpa [phase] using he 0
  rw [← Complex.re_sum, ← Complex.re_sum, he, he0]
  by_cases hz : z = 1
  · have hs : (∑ r ∈ range q, z ^ r) = (q : ℂ) := by simp [hz]
    rw [hs]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    have hb : (phase ((k : ℝ) * β / q)).re ≤ 1 :=
      (Complex.re_le_norm _).trans_eq (norm_phase _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg q)
  · have hs : (∑ r ∈ range q, z ^ r) = 0 := by
      have hh := geom_sum_mul z q
      rw [hzq, sub_self] at hh
      exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hz)
    simp [hs]

/-- P0026 page 176 and HBP page 31, the finite mixed tuple expansion before averaging. -/
theorem G_mixed_tuples421 (L a b : ℕ) (x : ℝ) :
    (G L x) ^ a * (star (G L x)) ^ b =
      ∑ u : Fin a → Fin L, ∑ v : Fin b → Fin L,
        phase (((∑ i : Fin a, (2 : ℕ) ^ (u i : ℕ) : ℤ) -
          (∑ i : Fin b, (2 : ℕ) ^ (v i : ℕ) : ℤ) : ℝ) * x) := by
  rw [show (star (G L x)) ^ b = star ((G L x) ^ b) by simp]
  rw [G_power_tuples421 L a x, G_power_tuples421 L b x]
  simp_rw [star_sum, phase_star421]
  rw [sum_mul]
  apply sum_congr rfl
  intro u hu
  rw [mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [phase_mul421]
  congr 1
  push_cast
  ring

/-- HBP page 31, summing the single frequency maximum over the finite mixed tuples. -/
theorem mixed_grid_max421 (L a b q : ℕ) (hq : 0 < q) (β : ℝ) :
    (∑ r ∈ range q,
      ((G L ((β + r) / (q : ℝ))) ^ a * (star (G L ((β + r) / (q : ℝ)))) ^ b).re) ≤
      ∑ r ∈ range q,
        ((G L ((r : ℝ) / (q : ℝ))) ^ a * (star (G L ((r : ℝ) / (q : ℝ)))) ^ b).re := by
  have hswap (f : ℕ → (Fin a → Fin L) → (Fin b → Fin L) → ℝ) :
      (∑ r ∈ range q, ∑ u : Fin a → Fin L, ∑ v : Fin b → Fin L, f r u v) =
        ∑ u : Fin a → Fin L, ∑ v : Fin b → Fin L, ∑ r ∈ range q, f r u v := by
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    rw [sum_comm]
  simp_rw [G_mixed_tuples421, Complex.re_sum]
  rw [hswap, hswap]
  apply sum_le_sum
  intro u hu
  apply sum_le_sum
  intro v hv
  simp only [← Int.cast_sub]
  exact phase_grid_max421 _ q hq β

/-- HBP pages 30 to 31, the polynomial dyadic maximum before the exponential series. -/
theorem dyadic_power_sum_proved421 (M n : ℕ) (hM : 0 < M)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (∑ r ∈ range (2 ^ M), (G M ((β + r) / (2 : ℝ) ^ M)).re ^ n) ≤
      ∑ r ∈ range (2 ^ M), (G M ((r : ℝ) / (2 : ℝ) ^ M)).re ^ n := by
  let q : ℕ := 2 ^ M
  have hq : 0 < q := by positivity
  have he (γ : ℝ) :
      (2 : ℝ) ^ n * (∑ r ∈ range q, (G M ((γ + r) / (q : ℝ))).re ^ n) =
        ∑ k ∈ range (n + 1), (n.choose k : ℝ) *
          ∑ r ∈ range q, ((G M ((γ + r) / (q : ℝ))) ^ k *
            (star (G M ((γ + r) / (q : ℝ)))) ^ (n - k)).re := by
    rw [mul_sum]
    simp_rw [real_power_binomial421]
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    rw [mul_sum]
  have hm : (2 : ℝ) ^ n * (∑ r ∈ range q, (G M ((β + r) / (q : ℝ))).re ^ n) ≤
      (2 : ℝ) ^ n * (∑ r ∈ range q, (G M ((0 + r) / (q : ℝ))).re ^ n) := by
    rw [he, he]
    apply sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa only [zero_add] using mixed_grid_max421 M k (n - k) q hq β
  have hh : (∑ r ∈ range q, (G M ((β + r) / (q : ℝ))).re ^ n) ≤
      ∑ r ∈ range q, (G M ((0 + r) / (q : ℝ))).re ^ n :=
    (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp
    (by simpa only [mul_comm] using hm)
  simpa only [q, zero_add, Nat.cast_pow, Nat.cast_ofNat] using hh

set_option format.width 240
#print axioms phase_nat_mul421
#print axioms phase_grid_max421
#print axioms G_mixed_tuples421
#print axioms mixed_grid_max421
#print axioms dyadic_power_sum_proved421

end LeanLab.PlattTrudgian2014
