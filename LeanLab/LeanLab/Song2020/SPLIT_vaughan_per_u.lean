/-
AI wrote the Lean code. OMOS repair of claude/Song2020-vaughan_per_u, 2026-11-13.
Source: https://arxiv.org/pdf/2012.06322, printed pages 5 through 8.
The two analytic steps that Decomp139 carried as sorry are stated in this new file, so that
the existing file Decomp139 gains no sorry and proves its own steps from these leaves.
The gate rejects any new def, not even a private one, so this file defines nothing: the
definitions Decomp139 uses are written out in full in the statement of each leaf, with the
left hand sides substituted by their bodies from Decomp139. Decomp139 transfers a leaf back
by unfolding its own fourier, truncatedSum, subWindow and lambdaSum.

s1_lambda_reduction, page 5, the displays from "For S1, we first observe" to "We have shown
so far": partial summation in the weight c x to the 1 minus gamma, the bound a_h at most K
over h for the Fourier coefficients, the bound of e of h times the difference of x plus 1 to
the gamma and x to the gamma minus 1 by h x to the gamma minus 1, and the passage from primes
to the von Mangoldt function. The paper writes the maximum over centred windows and a saving
1 over log n; this form keeps instead the initial segments that partial summation really
produces, drops the log saving, and writes out the prime power error as K H n to the 1/2,
which the paper absorbs into its O of n to the 3/2 minus gamma. Any bound B on the von
Mangoldt sums for 1 at most |h| at most H then bounds S1. The factor n to the epsilon on the
B sum was added in the check of 2026-11-12: for y close to n/3 the window reaches down to
small x, and the total variation of the partial summation weight x to the 1 minus gamma times
e of h times the gamma difference minus 1 is then of size |h| log n, not |h|; the paper's y is
a power of n below 1, where this loss does not arise, and n to the epsilon absorbs it.

vaughan_uv, pages 5 to 7, the bounds for the three Vaughan pieces with both parameters u and v
free, 1 at most u, 1 at most v and u v at most n, before the choice v = (n/u)^{1/2}: the
Sigma 1 display of page 6, u |h|^{1/2} x^{gamma/2-1} y plus x^{1-gamma/2} |h|^{-1/2}, with its
log squared factor absorbed in n to the epsilon, plus the display for x^{-epsilon} times
Sigma 2 plus Sigma 3 on page 7, n v^{-1/2} plus n^{1/2} (u v)^{1/2} plus the four u and h
monomials. Here x is replaced by n, since x is of size n over 3. Published inputs: Dirichlet
approximation and the Ramanujan sum splitting, page 5; the Vaughan identity, the paper's
Lemma 3.2, page 5; Iwaniec and Kowalski Corollary 8.13 for Sigma 1, page 6; dyadic division
into T(R,S) and Graham and Kolesnik Lemma 2.5, page 6; Iwaniec and Kowalski Corollary 8.13 for
the inner r sum and Graham and Kolesnik Lemma 2.4 for L, page 7.

Binary Goldbach is open.
-/
import LeanLab.Song2020.Characteristic139

namespace LeanLab.Song2020.SPLIT_vaughan_per_u

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- LEAF: Song 2020, page 5, from "For S1, we first observe" to "We have shown so far":
partial summation over the prime window with a_h at most K over h reduces S1 to the von
Mangoldt sums over an initial segment, with n to the epsilon absorbing the weight variation
when y is close to n/3. The header of this file carries the full reading. -/
theorem s1_lambda_reduction :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ K : ℝ, 1 ≤ K → ∀ a : ℕ → ℤ → ℂ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
            ∀ H : ℕ, 1 ≤ H → ∀ B : ℤ → ℝ,
              (∀ h : ℤ, h ≠ 0 → |h| ≤ (H : ℤ) → ∀ t : ℝ, ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ B h) →
              ‖∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
      (∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * (-((p : ℝ) + 1) ^ γ)) -
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h : ℤ => h ≠ 0), a H h * eC (h * (-(p : ℝ) ^ γ)))‖ ≤
                C * K * ((n : ℝ) ^ (3 / 2 - γ) + (H : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) +
                  (n : ℝ) ^ ε * ∑ k ∈ Finset.Icc 1 H, (B k + B (-(k : ℤ)))) := by
  sorry

/-- LEAF: Song 2020, pages 6 and 7, with u and v both free: the Sigma 1 display and the
display for x to the minus epsilon times Sigma 2 plus Sigma 3, before the choice
v = (n/u)^{1/2}. The header of this file carries the full reading. -/
theorem vaughan_uv :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u * v ≤ n →
            ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ C * (n : ℝ) ^ ε *
              (u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                (n : ℝ) ^ (1 - γ / 2) * |(h : ℝ)| ^ (-(1 : ℝ) / 2) +
                (n : ℝ) * v ^ (-(1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2) * (u * v) ^ ((1 : ℝ) / 2) +
                (n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  sorry

/-- PROVED. The modulus of the additive character is one, so the triangle inequality leaves
the von Mangoldt mass of the window: the first step inside the partial summation leaf. -/
private theorem norm_eC (θ : ℝ) : ‖eC θ‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- PROVED. Triangle inequality for the window sum: the exponential sum is at most the
von Mangoldt mass over the same initial segment, since each term has modulus Lambda of x. -/
theorem norm_lambdaSum_le_vonMangoldt_mass (γ : ℝ) (n : ℕ) (y α : ℝ) (h : ℤ) (t : ℝ) :
    ‖∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℂ) * eC (α * x + h * (x : ℝ) ^ γ)‖ ≤ ∑ x ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t),
      (ArithmeticFunction.vonMangoldt x : ℝ) := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro x hx
  rw [norm_mul, Complex.norm_real, norm_eC, mul_one, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- PROVED. The window is monotone in the upper endpoint, which is what partial summation
needs when it replaces the weight by its total variation. -/
theorem subWindow_mono (n : ℕ) (y : ℝ) {t t' : ℝ} (htt : t ≤ t') :
    (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t) ⊆
      (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
        (fun x : ℕ => |(x : ℝ) - (n : ℝ) / 3| < y ∧ (x : ℝ) ≤ t') := by
  intro x hx
  simp only [Finset.mem_filter] at *
  exact ⟨hx.1, hx.2.1, hx.2.2.trans htt⟩

/-- PROVED. The weight difference of the partial summation: for 0 < gamma < 1 and x at
least 1, the increment of the weight t to the 1 minus gamma over the step from x to x plus 1
is at most the derivative at the left endpoint, 1 minus gamma times x to the minus gamma.
This is Lagrange's mean value theorem with the derivative of t to the 1 minus gamma equal to
1 minus gamma times t to the minus gamma, decreasing, so the intermediate point gives the
bound. This is the step the paper records as bounding the difference of x plus 1 to the gamma
and x to the gamma by x to the gamma minus 1, inside the partial summation leaf. -/
theorem abs_rpow_window_weight_le (γ x : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx : 1 ≤ x) :
    |(x + 1) ^ (1 - γ) - x ^ (1 - γ)| ≤ (1 - γ) * x ^ (-γ) := by
  have hx0 : 0 < x := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (1 - γ)) (Set.Icc x (x + 1)) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 ht.1)))
  have hderiv : ∀ t ∈ Set.Ioo x (x + 1),
      HasDerivAt (fun t : ℝ => t ^ (1 - γ)) ((1 - γ) * t ^ ((1 - γ) - 1)) t := by
    intro t ht
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hx0 ht.1)))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 - γ))
    (fun t : ℝ => (1 - γ) * t ^ ((1 - γ) - 1)) (by linarith : x < x + 1) hcont hderiv
  rw [show x + 1 - x = 1 by ring, div_one] at hslope
  have hc0 : 0 < c := lt_trans hx0 hc.1
  have hcle : c ^ ((1 - γ) - 1) ≤ x ^ ((1 - γ) - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 hc.1.le (by linarith)
  have hkey : (x + 1) ^ (1 - γ) - x ^ (1 - γ) ≤ (1 - γ) * x ^ ((1 - γ) - 1) := by
    rw [← hslope]
    exact mul_le_mul_of_nonneg_left hcle h1γ.le
  have hexp : (1 - γ) - 1 = -γ := by ring
  rw [hexp] at hkey
  have hnn : 0 ≤ (x + 1) ^ (1 - γ) - x ^ (1 - γ) := by
    have := Real.rpow_le_rpow hx0.le (by linarith : x ≤ x + 1) h1γ.le
    linarith
  rw [abs_of_nonneg hnn]
  exact hkey

/-- PROVED. The weight of the partial summation telescopes: the sum of the increments of
t to the 1 minus gamma over the first m steps is the weight at m, since the weight at 0
vanishes for a positive exponent. This is the total variation the paper charges when it sums
the weight difference by parts, inside the partial summation leaf. -/
theorem sum_rpow_weight_telescope (γ : ℝ) (hγ1 : γ < 1) (m : ℕ) :
    ∑ k ∈ Finset.range m, (((k + 1 : ℕ) : ℝ) ^ (1 - γ) - (k : ℝ) ^ (1 - γ)) =
      (m : ℝ) ^ (1 - γ) := by
  have h := Finset.sum_range_sub (fun k : ℕ => (k : ℝ) ^ (1 - γ)) m
  rw [h, show ((0 : ℕ) : ℝ) = 0 by norm_num,
    Real.zero_rpow (by linarith : (1 : ℝ) - γ ≠ 0), sub_zero]

end

end LeanLab.Song2020.SPLIT_vaughan_per_u
