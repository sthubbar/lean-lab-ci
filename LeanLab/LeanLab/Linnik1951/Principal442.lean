/-
P0093 page 159 before equation 5.3. Full period principal square mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357g
import LeanLab.Linnik1951.SPLIT1622_exceptional
import LeanLab.Linnik1951.Mass435
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 159 trivial full period bound before equation 5.3.
Parseval for an absolutely summable negative natural Fourier series. -/
theorem series_square_integral442 (a : ℕ → ℂ) (ha : Summable a) :
    (∫ α in (0 : ℝ)..1, ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) =
        ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have hf : Continuous (fun α : ℝ => ∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) := by
    apply continuous_tsum (u := fun n => ‖a n‖)
    · intro n
      fun_prop
    · exact ha.norm
    · intro n α
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  have hs : IntervalIntegrable (fun α : ℝ => ‖∑' n : ℕ, a n *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2) volume 0 1 :=
    (hf.norm.pow 2).intervalIntegrable 0 1
  have hL2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hs.1
  calc
    _ = ∑' i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun α => ∑' n : ℕ, a n *
          Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)) i‖ ^ 2 := by
      simpa using (tsum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hL2).symm
    _ = _ := negative_modes_sum111 _ _ (negative_series_coefficient_proved357 a ha)

/-- P0093 page 159 before equation 5.3. Natural coefficient zero
extension of the character prime series, with absolute summability. -/
theorem character_coefficients_summable442 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun n : ℕ => if n.Prime then
      χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (damping_summable111 N hN)
  intro n
  by_cases hn : n.Prime
  · simp only [if_pos hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (χ.norm_le_one _)
  · simp [hn, (Real.exp_pos _).le]

/-- P0093 page 159 before equation 5.3. The subtype prime series
equals its zero extension over the natural frequencies. -/
theorem character_series_nat442 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (α : ℝ) :
    characterPrime280 χ N α = ∑' n : ℕ,
      (if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0) *
        Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I) := by
  classical
  let f : ℕ → ℂ := fun n => if n.Prime then χ n *
    (Real.exp (-(n : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I) else 0
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hp : n.Prime
    · exact ⟨⟨n, hp⟩, rfl⟩
    · exact absurd (by simp [f, hp] : f n = 0) hn
  calc
    _ = ∑' p : Nat.Primes, f (p : ℕ) := by
      unfold characterPrime280
      apply tsum_congr
      intro p
      simp only [f, if_pos p.property]
    _ = ∑' n : ℕ, f n := Nat.Primes.coe_nat_injective.tsum_eq hsupp
    _ = _ := by
      apply tsum_congr
      intro n
      by_cases hn : n.Prime <;> simp [f, hn]

/-- P0093 page 159 before equation 5.3. Every character has full
period square mass at most two N. The estimate discards primality and
uses the geometric damping sum. No prime number theorem is needed. -/
theorem character_full_mass442 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖characterPrime280 χ N α‖ ^ 2) ≤ 2 * (N : ℝ) := by
  classical
  simp_rw [character_series_nat442]
  rw [series_square_integral442 _ (character_coefficients_summable442 χ N hN)]
  have he : ∀ n : ℕ,
      ‖if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0‖ ^ 2 ≤
        Real.exp (-2 * (n : ℝ) / N) := by
    intro n
    by_cases hn : n.Prime
    · simp only [if_pos hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc := pow_le_pow_left₀ (norm_nonneg (χ n)) (χ.norm_le_one n) 2
      have heq : Real.exp (-(n : ℝ) / N) ^ 2 = Real.exp (-2 * (n : ℝ) / N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc
        _ = ‖χ n‖ ^ 2 * Real.exp (-(n : ℝ) / N) ^ 2 := by ring
        _ ≤ 1 * Real.exp (-(n : ℝ) / N) ^ 2 :=
          mul_le_mul_of_nonneg_right (by simpa using hc) (by positivity)
        _ = _ := by rw [one_mul, heq]
    · simp [hn, (Real.exp_pos _).le]
  have hh := laplace_bound111 (fun _ => (1 : ℝ)) 1 N hN (by norm_num)
    (fun _ => by norm_num) (by intro M; simp)
  have hg : Summable (fun n : ℕ => Real.exp (-2 * (n : ℝ) / N)) := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hr : ‖Real.exp (-2 / (N : ℝ))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hNp)
    have hs := summable_geometric_of_norm_lt_one hr
    convert hs using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ ∑' n : ℕ, Real.exp (-2 * (n : ℝ) / N) :=
      (Summable.of_nonneg_of_le (fun n => sq_nonneg _) he hg).tsum_le_tsum he hg
    _ ≤ _ := by simpa using hh

/-- P0093 page 159 before equation 5.3. Integer frequency character
sums have period one in the additive phase. -/
theorem character_periodic442 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    Function.Periodic (characterPrime280 χ N) 1 := by
  intro α
  unfold characterPrime280
  apply tsum_congr
  intro p
  congr 1
  have he : ((-(2 * Real.pi * (α + 1) * (p : ℕ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) : ℂ) * Complex.I +
        ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  have hp : Complex.exp ((-((p : ℕ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(p : ℕ) : ℤ) using 1 <;> push_cast <;> ring
  rw [hp, mul_one]

/-- P0093 page 159 before equation 5.3. The local square mass on a
symmetric interval of radius at most one half is at most the full
period square mass. -/
theorem character_local_mass442 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    (∫ α in -r..r, ‖characterPrime280 χ N α‖ ^ 2) ≤ 2 * (N : ℝ) := by
  have hc := (continuous_character_prime357 χ N hN).norm.pow 2
  have hp : Function.Periodic (fun α => ‖characterPrime280 χ N α‖ ^ 2) 1 :=
    (character_periodic442 χ N).comp (fun z => ‖z‖ ^ 2)
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hrh
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖characterPrime280 χ N α‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
  have he := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num only at he
  exact hi.trans (he.trans_le (character_full_mass442 χ N hN))

/-- P0093 page 159 full period comparison before equation 5.3.
The principal character modulo one has strictly positive square mass
for every positive N. The prime two Fourier coefficient certifies this. -/
theorem principal_full_mass_pos442 (N : ℕ) (hN : 1 ≤ N) :
    0 < (∫ α in (0 : ℝ)..1,
      ‖characterPrime280 (1 : DirichletCharacter ℂ 1) N α‖ ^ 2) := by
  classical
  let a : ℕ → ℂ := fun n => if n.Prime then
    (1 : DirichletCharacter ℂ 1) n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0
  have ha : Summable a := character_coefficients_summable442 1 N hN
  have hp := ha.norm.mul_of_nonneg ha.norm (fun n => norm_nonneg (a n))
    (fun n => norm_nonneg (a n))
  have hs : Summable (fun n : ℕ => ‖a n‖ ^ 2) := by
    have hi : Function.Injective (fun n : ℕ => (n, n)) := fun n m h => congrArg Prod.fst h
    convert! hp.comp_injective hi using 1
    funext n
    simp only [Function.comp_apply, pow_two]
  have htwo : 0 < ‖a 2‖ ^ 2 := by
    have he : (2 : ZMod 1) = 1 := Subsingleton.elim _ _
    dsimp [a]
    rw [if_pos Nat.prime_two, he, map_one, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    positivity
  simp_rw [character_series_nat442]
  change 0 < ∫ α in (0 : ℝ)..1, ‖∑' n : ℕ, a n *
    Complex.exp ((-(2 * Real.pi * α * n) : ℝ) * Complex.I)‖ ^ 2
  rw [series_square_integral442 a ha]
  exact hs.tsum_pos (fun n => sq_nonneg _) 2 htwo

/-- P0093 page 159 before equation 5.3. Exact principal_mass1622
statement with B equal to two. -/
theorem principal_mass_proved442 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) (r : ℝ), 1 ≤ N → 0 ≤ r → r ≤ 1 / 2 →
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤ B * (N : ℝ) := by
  exact ⟨2, by norm_num, fun N q r hN hr hrh => character_local_mass442 1 N hN r hr hrh⟩

/-- P0093 page 166 equation 9.3. Exact totient_sqrt_lower1622
statement from the proved lab square totient inequality. -/
theorem totient_sqrt_lower_proved442 (q : ℕ) (hq : 1 ≤ q) :
    Real.sqrt q ≤ 2 * (q.totient : ℝ) := by
  apply (Real.sqrt_le_iff).mpr
  have hb : (q : ℝ) ≤ 2 * (q.totient : ℝ) ^ 2 := by
    exact_mod_cast LeanLab.Perelli1996.Totient.le_two_totient_sq q
  exact ⟨by positivity, by nlinarith⟩

end LeanLab.Linnik1951
