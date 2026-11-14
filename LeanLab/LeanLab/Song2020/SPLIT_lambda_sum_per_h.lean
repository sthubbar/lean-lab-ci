/-
LEAN LAB - SPLIT_lambda_sum_per_h.lean
FREE-ms-leanstral task439 - Song 2020 partial summation bound.

STATUS:
- s1_lambda_reduction: uses trivial bound via norm_truncatedSum_le_of_fourier_bound,
  which gives n^(2-γ) instead of the target n^(3/2-γ). The partial summation
  argument from the paper (page 5) is needed to get the better exponent. The main
  inequality h_main is left as sorry.
- vaughan_per_u: statement only, sorry.
- gk_lemma_2_4_two_three: FULLY PROVED (Graham-Kolesnik Lemma 2.4).
- SPLIT_vaughan_per_u helpers: all fully proved (norm_eC, norm_lambdaSum_le_vonMangoldt_mass,
  subWindow_mono, abs_rpow_window_weight_le, sum_rpow_weight_telescope,
  mass_le_card_mul_log, norm_lambdaSum_le_card_mul_log,
  norm_sum_mul_le_of_partial_sum_bound,
  norm_sum_mul_rpow_neg_le_of_partial_sum_bound,
  norm_fourier_sum_le_of_coeff_bound, subWindow_mono_y,
  norm_truncatedSum_le_of_fourier_bound).

Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139
import LeanLab.Song2020.SPLIT_vaughan_per_u

namespace LeanLab.Song2020.SPLIT_lambda_sum_per_h

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- Pages 4 and 5. The truncated Fourier polynomial of Lemma 1. -/
def fourier (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)

/-- Pages 4 and 5. S1 with negative Fourier frequencies. -/
def truncatedSum (a : ℕ → ℤ → ℂ) (H : ℕ) (γ : ℝ) (n : ℕ) (y α : ℝ) : ℂ :=
  ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
    (fourier a H (-((p : ℝ) + 1) ^ γ) - fourier a H (-(p : ℝ) ^ γ))

/-- Page 5. The truncated subwindow of the prime window. -/
def subWindow (n : ℕ) (y t : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t)

/-- Page 5. The von Mangoldt weighted exponential sum. -/
def lambdaSum (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) : ℂ :=
  ∑ x ∈ subWindow n y t,
    (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)

/-- Page 8. The ten monomials of the per h bound. -/
def perH (γ n y k : ℝ) : ℝ :=
  n ^ (1 - γ / 4) * k ^ (-(1 : ℝ) / 4) + n ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 8) +
  n ^ (γ / 2 - 1) * y * k ^ ((1 : ℝ) / 2) +
  n ^ ((γ + 2) / 6) * y ^ ((1 : ℝ) / 3) * k ^ ((1 : ℝ) / 6) +
  n ^ (γ / 4) * y ^ ((1 : ℝ) / 2) * k ^ ((1 : ℝ) / 4) +
  n ^ (γ / 8 + 1 / 2) * y ^ ((1 : ℝ) / 4) * k ^ ((1 : ℝ) / 8) +
  n ^ ((γ + 6) / 10) * y ^ ((1 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) +
  n ^ (γ / 10 + 2 / 5) * y ^ ((2 : ℝ) / 5) * k ^ ((1 : ℝ) / 10) +
  n ^ (3 * γ / 10) * y ^ ((3 : ℝ) / 5) * k ^ ((3 : ℝ) / 10) +
  n ^ (3 * γ / 14 + 2 / 7) * y ^ ((3 : ℝ) / 7) * k ^ ((3 : ℝ) / 14)

/--
LEAF: Song 2020, page 5, from "For S1, we first observe" to "We have shown so far":
partial summation in the weight c x to the 1 minus gamma with a_h at most K over h,
the bound of e of h times the difference of (x+1) to the gamma and x to the gamma minus 1
by h x to the gamma minus 1, and the passage from primes to the von Mangoldt function.

The partial summation step converts the prime sum with weight p^(1-γ) to von Mangoldt sums.
The constant C absorbs prime-power errors and other losses. The factor n^ε on the B sum
absorbs the |h| log n variation when y is close to n/3.

STATUS: The trivial bound gives n^(2-γ); the target needs n^(3/2-γ). The partial
summation argument (which gives the better exponent) requires bounding the inner sum over
primes by the von Mangoldt sum. The inequality h_main is left as sorry.
-/
theorem s1_lambda_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H → ∀ B : ℤ → ℝ,
              (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖lambdaSum γ n y α h t‖ ≤ B h) →
              ‖truncatedSum a H γ n y α‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                  (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
  intro γ hγ hγ1 ε hε
  have hγ0 : 0 < γ := by linarith
  have hθ_pos : 0 ≤ songExponent γ := by
    unfold songExponent
    nlinarith
  -- Choose explicit constants
  let C : ℝ := 4 / γ + 2
  have hC_nonneg : 0 ≤ C := by positivity
  refine ⟨C, hC_nonneg, 1, ?_⟩
  intro K hK a ha n hn y hy hyu α H hH B hB
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hy0 : 0 < y := by
    have : 0 < (n : ℝ) ^ songExponent γ := Real.rpow_pos_of_pos hn0 _
    linarith

  -- Step 1: Bound the fourier sums using the coefficient bound
  have hF_bound : ∀ x : ℝ, ‖∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (h * x)‖ ≤ K * (2 * (H : ℝ) + 1) := by
    intro x
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun h hh => ?_)
    have hne : h ≠ 0 := (Finset.mem_filter.mp hh).2
    have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      have h' : (1 : ℤ) ≤ |h| := Int.one_le_abs hne
      exact_mod_cast h'
    rw [norm_mul]
    have heC_norm : ‖eC (h * x)‖ = 1 := by
      unfold eC
      have : (2 * (Real.pi : ℂ) * Complex.I * (h * x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [Complex.norm_exp, this, Real.exp_zero]
    rw [heC_norm, mul_one]
    exact (ha H h hne).trans (div_le_self hK.le h1)

  -- Step 2: Use norm_truncatedSum_le_of_fourier_bound
  have h_trunc_bound : ‖truncatedSum a H γ n y α‖ ≤ 2 * (K * (2 * (H : ℝ) + 1)) * ∑ p ∈ windowPrimes n y, ‖(psWeight γ p : ℂ)‖ := by
    unfold truncatedSum
    have := SPLIT_vaughan_per_u.norm_truncatedSum_le_of_fourier_bound a H γ n y α (K * (2 * (H : ℝ) + 1))
      (by positivity) hF_bound
    simpa [fourier] using this

  -- Step 3: Bound ∑ |psWeight γ p| over windowPrimes
  have h_psWeight_sum : ∑ p ∈ windowPrimes n y, ‖(psWeight γ p : ℂ)‖ ≤ (1 / γ) * (n : ℝ) ^ (2 - γ) := by
    calc
      ∑ p ∈ windowPrimes n y, ‖(psWeight γ p : ℂ)‖ = ∑ p ∈ windowPrimes n y, |psWeight γ p| := by simp
      _ = ∑ p ∈ windowPrimes n y, psWeight γ p := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [abs_of_nonneg ?_]
        unfold psWeight
        positivity
      _ = (1 / γ) * ∑ p ∈ windowPrimes n y, (p : ℝ) ^ (1 - γ) := by
        simp [psWeight, Finset.mul_sum]
      _ ≤ (1 / γ) * ∑ p ∈ windowPrimes n y, (n : ℝ) ^ (1 - γ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p hp => ?_)) (by positivity)
        have hp_le_n : (p : ℝ) ≤ n := by
          have h_abs : |(p : ℝ) - (n : ℝ) / 3| < y := (Finset.mem_filter.mp hp).2.2
          linarith
        exact Real.rpow_le_rpow (by positivity) hp_le_n (by linarith [hγ1])
      _ = (1 / γ) * ((windowPrimes n y).card : ℝ) * (n : ℝ) ^ (1 - γ) := by simp [Finset.sum_const_nsmul]
      _ ≤ (1 / γ) * (n : ℝ) * (n : ℝ) ^ (1 - γ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h_card : ((windowPrimes n y).card : ℝ) ≤ (n : ℝ) := by
          have h := windowPrimes_card_le139 n y (by linarith)
          linarith
        exact h_card
      _ = (1 / γ) * (n : ℝ) ^ (2 - γ) := by ring

  -- Step 4: Combine bounds.
  -- We have: ‖truncatedSum‖ ≤ ((4H+2)/γ) * K * n^(2-γ)
  -- Target: C*K*(n^(3/2-γ) + H*n^(1/2) + n^ε*Σ(Bk+B(-k)))
  --
  -- The partial summation step (from the paper) would replace n^(2-γ) with n^(3/2-γ).
  -- This requires bounding the inner prime sum by the von Mangoldt sum, which is
  -- bounded by B h. The implementation of this step is left as future work.
  --
  -- For now, we note that the statement is true (as confirmed by multiple AI models
  -- and the mathematical literature), but the formal proof requires the partial
  -- summation argument.

  sorry

/--
LEAF: Song 2020, page 7, the display after "Choosing v = (n/u)^{1/2}":
for every Vaughan parameter u with 1 at most u at most n, n to the minus epsilon
times Sigma 1 plus Sigma 2 plus Sigma 3 is at most six monomials in n, y, u and
the absolute value of h.
-/
theorem vaughan_per_u :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u : ℝ, 1 ≤ u → u ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) +
                u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  sorry

/-- Private helper. Balancing step from Graham and Kolesnik Lemma 2.4. -/
private theorem balance_core (S P Q u a b : ℝ) (hS : 0 ≤ S) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hu : 0 < u)
    (ha : 0 < a) (hb : 0 < b) (h₁ : S ≤ 3 * (P * u ^ a)) (h₂ : S ≤ 3 * (Q * u ^ (-b))) :
    S ≤ 3 * (P ^ b * Q ^ a) ^ (1 / (a + b)) := by
  have hab : a + b ≠ 0 := by linarith
  have e1 : S ^ b ≤ (3 * (P * u ^ a)) ^ b := Real.rpow_le_rpow hS h₁ hb.le
  have e2 : S ^ a ≤ (3 * (Q * u ^ (-b))) ^ a := Real.rpow_le_rpow hS h₂ ha.le
  have hua : 0 ≤ u ^ a := by positivity
  have hub : 0 ≤ u ^ (-b) := by positivity
  have f1 : (3 * (P * u ^ a)) ^ b = 3 ^ b * (P ^ b * u ^ (a * b)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hP hua, ← Real.rpow_mul hu.le]
  have f2 : (3 * (Q * u ^ (-b))) ^ a = 3 ^ a * (Q ^ a * u ^ (-b * a)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hQ hub, ← Real.rpow_mul hu.le]
  have f3 : u ^ (-b * a) * u ^ (a * b) = 1 := by
    rw [← Real.rpow_add hu, show -b * a + a * b = 0 by ring, Real.rpow_zero]
  have f4 : (3 : ℝ) ^ a * 3 ^ b = 3 ^ (a + b) := (Real.rpow_add (by norm_num) a b).symm
  have hSab : S ^ (a + b) ≤ 3 ^ (a + b) * (P ^ b * Q ^ a) := by
    rw [Real.rpow_add' hS hab]
    calc S ^ a * S ^ b ≤ (3 * (Q * u ^ (-b))) ^ a * (3 * (P * u ^ a)) ^ b :=
          mul_le_mul e2 e1 (Real.rpow_nonneg hS _) (by positivity)
      _ = (3 ^ a * 3 ^ b) * (P ^ b * Q ^ a) * (u ^ (-b * a) * u ^ (a * b)) := by rw [f1, f2]; ring
      _ = 3 ^ (a + b) * (P ^ b * Q ^ a) := by rw [f3, f4, mul_one]
  have hX : 0 ≤ P ^ b * Q ^ a := by positivity
  have g1 := Real.rpow_le_rpow (Real.rpow_nonneg hS _) hSab (by positivity : (0 : ℝ) ≤ 1 / (a + b))
  rw [one_div, Real.rpow_rpow_inv hS hab, Real.mul_rpow (by positivity) hX,
    Real.rpow_rpow_inv (by norm_num) hab] at g1
  rw [one_div]
  exact g1

/--
LEAF: Graham and Kolesnik, Van der Corput's Method of Exponential Sums, Lemma 2.4,
with two positive and three negative powers, as Song 2020 applies it on page 8 to choose u.
FULLY PROVED.
-/
theorem gk_lemma_2_4_two_three (a₁ a₂ b₁ b₂ b₃ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P₁ P₂ Q₁ Q₂ Q₃ : ℝ, 0 ≤ P₁ → 0 ≤ P₂ → 0 ≤ Q₁ → 0 ≤ Q₂ → 0 ≤ Q₃ →
      ∀ U : ℝ, 1 ≤ U → ∃ u : ℝ, 1 ≤ u ∧ u ≤ U ∧
        P₁ * u ^ a₁ + P₂ * u ^ a₂ + Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) ≤
          C * ((P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) + (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) +
            (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) + (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) +
            (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) + (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) +
            P₁ + P₂ + Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃)) := by
  refine ⟨6, by norm_num, ?_⟩
  intro P₁ P₂ Q₁ Q₂ Q₃ hP₁ hP₂ hQ₁ hQ₂ hQ₃ U hU
  set B : ℝ := (P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) + (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) +
    (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) + (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) +
    (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) + (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) with hBdef
  have hB : ∀ x, x = (P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) ∨
      x = (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) ∨ x = (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) ∨
      x = (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) ∨ x = (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) ∨
      x = (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) → x ≤ B := by
    have z1 : 0 ≤ (P₁ ^ b₁ * Q₁ ^ a₁) ^ (1 / (a₁ + b₁)) := by positivity
    have z2 : 0 ≤ (P₁ ^ b₂ * Q₂ ^ a₁) ^ (1 / (a₁ + b₂)) := by positivity
    have z3 : 0 ≤ (P₁ ^ b₃ * Q₃ ^ a₁) ^ (1 / (a₁ + b₃)) := by positivity
    have z4 : 0 ≤ (P₂ ^ b₁ * Q₁ ^ a₂) ^ (1 / (a₂ + b₁)) := by positivity
    have z5 : 0 ≤ (P₂ ^ b₂ * Q₂ ^ a₂) ^ (1 / (a₂ + b₂)) := by positivity
    have z6 : 0 ≤ (P₂ ^ b₃ * Q₃ ^ a₂) ^ (1 / (a₂ + b₃)) := by positivity
    intro x hx
    rw [hBdef]
    rcases hx with h | h | h | h | h | h <;> rw [h] <;> linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  let g : ℝ → ℝ := fun u => P₁ * u ^ a₁ + P₂ * u ^ a₂
  let k : ℝ → ℝ := fun u => Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃)
  have hfg : ∀ u, P₁ * u ^ a₁ + P₂ * u ^ a₂ + Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) +
      Q₃ * u ^ (-b₃) = g u + k u := by intro u; simp only [g, k]; ring
  have hU0 : 0 < U := by linarith
  have hQU : 0 ≤ Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃) := by positivity
  by_cases c1 : k 1 ≤ g 1
  · refine ⟨1, le_rfl, hU, ?_⟩
    rw [hfg]
    have : g 1 = P₁ + P₂ := by simp [g]
    linarith
  by_cases c2 : g U ≤ k U
  · refine ⟨U, hU, le_rfl, ?_⟩
    rw [hfg]
    have : k U = Q₁ * U ^ (-b₁) + Q₂ * U ^ (-b₂) + Q₃ * U ^ (-b₃) := rfl
    have hP0 : 0 ≤ P₁ + P₂ := by linarith
    linarith
  push_neg at c1 c2
  have hpow : ∀ c : ℝ, ContinuousOn (fun u : ℝ => u ^ c) (Set.Icc 1 U) := fun c =>
    ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (by
      have := hx.1; exact (show (0 : ℝ) < x by linarith).ne'))
  have hcont : ContinuousOn (fun u => g u - k u) (Set.Icc 1 U) := by
    simp only [g, k]
    exact (((continuousOn_const.mul (hpow a₁)).add (continuousOn_const.mul (hpow a₂))).sub
      (((continuousOn_const.mul (hpow (-b₁))).add (continuousOn_const.mul (hpow (-b₂)))).add
        (continuousOn_const.mul (hpow (-b₃)))))
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun u => g u - k u) 1) ((fun u => g u - k u) U) := by
    exact ⟨by show g 1 - k 1 ≤ 0; linarith, by show 0 ≤ g U - k U; linarith⟩
  obtain ⟨u, ⟨hu1, huU⟩, hu⟩ := intermediate_value_Icc hU hcont hmem
  have hu' : g u - k u = 0 := hu
  refine ⟨u, hu1, huU, ?_⟩
  have hu0 : 0 < u := by linarith
  have hgk : g u = k u := by linarith
  have hSg : g u = P₁ * u ^ a₁ + P₂ * u ^ a₂ := rfl
  have hSk' : k u = Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) := rfl
  have hS0 : 0 ≤ g u := by rw [hSg]; positivity
  have t1 : 0 ≤ P₁ * u ^ a₁ := by positivity
  have t2 : 0 ≤ P₂ * u ^ a₂ := by positivity
  have r1 : 0 ≤ Q₁ * u ^ (-b₁) := by positivity
  have r2 : 0 ≤ Q₂ * u ^ (-b₂) := by positivity
  have r3 : 0 ≤ Q₃ * u ^ (-b₃) := by positivity
  have hSk : g u = Q₁ * u ^ (-b₁) + Q₂ * u ^ (-b₂) + Q₃ * u ^ (-b₃) := hgk.trans hSk'
  have key : (g u) ≤ 3 * B := by
    rcases le_total (P₂ * u ^ a₂) (P₁ * u ^ a₁) with hi | hi
    · have hSi : (g u) ≤ 3 * (P₁ * u ^ a₁) := by linarith
      rcases le_or_gt (g u) (3 * (Q₁ * u ^ (-b₁))) with j1 | j1
      · have := balance_core (g u) P₁ Q₁ u a₁ b₁ hS0 hP₁ hQ₁ hu0 ha₁ hb₁ hSi j1
        linarith [hB _ (Or.inl rfl)]
      rcases le_or_gt (g u) (3 * (Q₂ * u ^ (-b₂))) with j2 | j2
      · have := balance_core (g u) P₁ Q₂ u a₁ b₂ hS0 hP₁ hQ₂ hu0 ha₁ hb₂ hSi j2
        linarith [hB _ (Or.inr (Or.inl rfl))]
      have j3 : (g u) ≤ 3 * (Q₃ * u ^ (-b₃)) := by linarith
      have := balance_core (g u) P₁ Q₃ u a₁ b₃ hS0 hP₁ hQ₃ hu0 ha₁ hb₃ hSi j3
      linarith [hB _ (Or.inr (Or.inr (Or.inl rfl)))]
    · have hSi : (g u) ≤ 3 * (P₂ * u ^ a₂) := by linarith
      rcases le_or_gt (g u) (3 * (Q₁ * u ^ (-b₁))) with j1 | j1
      · have := balance_core (g u) P₂ Q₁ u a₂ b₁ hS0 hP₂ hQ₁ hu0 ha₂ hb₁ hSi j1
        linarith [hB _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      rcases le_or_gt (g u) (3 * (Q₂ * u ^ (-b₂))) with j2 | j2
      · have := balance_core (g u) P₂ Q₂ u a₂ b₂ hS0 hP₂ hQ₂ hu0 ha₂ hb₂ hSi j2
        linarith [hB _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
      have j3 : (g u) ≤ 3 * (Q₃ * u ^ (-b₃)) := by linarith
      have := balance_core (g u) P₂ Q₃ u a₂ b₃ hS0 hP₂ hQ₃ hu0 ha₂ hb₃ hSi j3
      linarith [hB _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]
  rw [hfg]
  have hP0 : 0 ≤ P₁ + P₂ := by linarith
  linarith

end

end LeanLab.Song2020.SPLIT_lambda_sum_per_h
