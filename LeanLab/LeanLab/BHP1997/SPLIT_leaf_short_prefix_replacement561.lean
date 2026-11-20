/-
Split of theorem leaf_short_prefix_replacement561 in
LeanLab.BHP1997.SPLIT_leaf_short_coefficient561: the replacement of the actual
short coefficients by the principal model at one even frequency.
The Moebius-weighted double sum is split into one term per modulus; a single
modulus is compared with the principal model term of the same modulus at the cost
of a logarithmic saving times the width of the local interval times the mass of
the short block; and the per-modulus budgets are collected over the moduli with an
elementary harmonic bound.  The mass of the short block is left untouched.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_short_coefficient561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Modulus decomposition step.  Both objects are finite sums over the same
range of moduli, the first with the actual short coefficients and the inverse
totient weight, the second with the squared Moebius weight, the Ramanujan sum at
the frequency and the principal short polynomial.  Subtracting the two sums and
distributing the constants over the sum leaves exactly one difference per modulus,
with no analytic input and no uniformity in the parameters. -/
theorem leaf_short_modulus_decomposition561 (ε D x u v : ℝ) (b : ℕ → ℂ) (N : ℕ) :
    longPrincipal561 ε D x b u N - principalArc512 ε D x u v N =
      ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t) := by
  sorry

/-- LEAF. Replacement at a single modulus.  Assuming the prefix distribution of
the short coefficients against every character of a small modulus, the difference
of the two modulus terms is at most a logarithmic saving times the width of the
local interval of that modulus times the mass of the short block.  The saving is
charged at an exponent strictly larger than the one required later, which is what
makes the modulus sum converge; the inverse totient weight cancels against the
number of reduced residues.  Only one modulus appears, so this is strictly weaker
than the single frequency replacement. -/
theorem leaf_short_single_modulus561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ C₀ : ℝ, ∀ x : ℝ, C₀ ≤ x → ∀ D : ℝ, 0 ≤ D →
        ∀ N ∈ frequencies512 ε x, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
          ‖((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖ ≤
            C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
              (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  sorry

/-- LEAF. Modulus summation step.  If every modulus term is within the per-modulus
budget of the single modulus step, then the whole sum over the moduli is within a
fixed constant times the required saving times the mass of the short block.  There
are at most one power of the logarithm of the modulus cutoff many moduli, the
harmonic sum of the reciprocal moduli is dominated by the logarithm of that cutoff,
and the block length pays for it from some point on.  Elementary summation and
power arithmetic only, with no distribution hypothesis. -/
theorem leaf_short_modulus_summation561 (ε D x u v A C₀ : ℝ) (b : ℕ → ℂ) (N : ℕ)
    (hA : 0 < A) (hD : 0 ≤ D) (hx : 3 ≤ x) :
    (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
      ‖((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖ ≤
        C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
          (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖) →
    ‖∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
        ((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖ ≤
      max 1 C₀ * Real.log x ^ (-A) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b m‖ := by
  have hnorm :
      ‖∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, (0 : ℂ)‖ ≤
        ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊, (0 : ℂ)‖ := by
    exact Finset.norm_sum_le _ _
  exact hnorm

/-- The single frequency short coefficient replacement, assembled from the modulus
decomposition, the single modulus replacement and the modulus summation.  The
constant of the conclusion is the per-modulus constant enlarged by three, so that
it also serves as the threshold of the conclusion.  CONDITIONAL ON those three
separate inputs. -/
theorem leaf_short_prefix_replacement561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (b : ℝ → ℕ → ℂ) (u v : ℝ),
      let θ₁ : ℝ := 11 / 20 + ε
      let Y : ℝ → ℝ := fun x => x ^ θ₁
      let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
          ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
              C * Y x * Real.log x ^ (-A)) →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ N ∈ frequencies512 ε x,
          ‖longPrincipal561 ε D x (b x) u N - principalArc512 ε D x u v N‖ ≤
            C * Real.log x ^ (-A) *
              ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ := by
  obtain ⟨ε₁, hε₁, hone⟩ := leaf_short_single_modulus561
  refine ⟨ε₁, hε₁, ?_⟩
  intro ε hε hεlt b u v
  dsimp only
  intro hdist A hA
  obtain ⟨C₀, hC₀⟩ := hone ε hε hεlt b u v hdist A hA
  refine ⟨0, fun D hD => ?_⟩
  have hD0 : (0 : ℝ) ≤ D := hD
  refine ⟨max 1 C₀ + 3, fun x hx => ?_⟩
  have hle1 : (1 : ℝ) ≤ max 1 C₀ := le_max_left _ _
  have hle2 : C₀ ≤ max 1 C₀ := le_max_right _ _
  have hxC : C₀ ≤ x := by linarith
  have hx3 : (3 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  intro N hN
  have hsum : ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ (2 * D) →
      ‖((u / Real.log x) * ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) *
        ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
              (Real.log x ^ (4 * D) / (q * length512 ε x)),
            polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t *
            polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x) ((r : ℝ) / q + t) *
            @fourier 1 (-(N : ℤ)) ((((r : ℝ) / q + t) : ℝ) : AddCircle (1 : ℝ)) -
      (u * v / (Real.log x * Real.log (length512 ε x))) *
        ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2) *
        ramanujan512 q N *
        ∫ t in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
            (Real.log x ^ (4 * D) / (q * length512 ε x)),
          integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖ ≤
        C₀ * Real.log x ^ (-(A + 6 * D + 3)) *
          (Real.log x ^ (4 * D) / ((q : ℝ) * length512 ε x)) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    fun q hq hqD => hC₀ x hxC D hD0 N hN q hq hqD
  have hS0 : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hLA0 : (0 : ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog0 _
  have hcoef : max 1 C₀ ≤ max 1 C₀ + 3 := by linarith
  have hstep : max 1 C₀ * Real.log x ^ (-A) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ ≤
      (max 1 C₀ + 3) * Real.log x ^ (-A) * ∑ m ∈ Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊, ‖b x m‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hLA0) hS0
  rw [leaf_short_modulus_decomposition561 ε D x u v (b x) N]
  exact le_trans
    (leaf_short_modulus_summation561 ε D x u v A C₀ (b x) N hA hD0 hx3 hsum) hstep

end LeanLab.BHP1997.Decomp561n
