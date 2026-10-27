/-
P0087 M. Akeno, "On the level of distribution of Goldbach primes and its applications",
arXiv 2606.29559, v1 dated 2026-06-30, read 2026-10-17.
Abstract: for almost all even N > 0 the set of Goldbach primes P ∩ (N - P) has level of
distribution 1/6; almost all even N are p₁ + p₂ with p₁ - p₂ + 1 ∈ P₄; almost all N with
6 ∣ N are p₁ + p₂ with 2 p₁ p₂ + 1 ∈ P₁₃.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves it; the cited results are almost all statements.

Asymptotic notation. Every `≪` and every `O(·)` of the paper is encoded by an explicit
existential constant `C`, `C₁` or `C₂`, chosen after all the parameters that the paper lets
the implied constant depend on, and before `X`, `N` and the other variables.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Akeno2026
open Real Finset
open scoped ContDiff ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-! ### Basic objects -/

/-- The Goldbach primes for `N`: the set `P ∩ (N - P)` of the paper, the primes `p` such that
`N - p` is also prime. Natural subtraction is harmless, since `N - p` prime forces `p < N`. -/
def GoldbachPrimes (N : ℕ) : Set ℕ := {p | p.Prime ∧ (N - p).Prime}

/-- `P_k`, the paper's set of products of at most `k` primes, as positive integers whose number
of prime factors counted with multiplicity is at most `k`. -/
def InP (k n : ℕ) : Prop := 0 < n ∧ n.primeFactorsList.length ≤ k

/-- `#{N ∈ (X/2, X] : S N ∧ ¬ P N}`, the exceptions to `P` among the `N` of type `S`. -/
noncomputable def excCount (S P : ℕ → Prop) (X : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => X / 2 < (N : ℝ) ∧ S N ∧ ¬ P N)).card

/-- "For all `A > 0` and `X ≥ 2`, `P N` holds for all but `O(X (ln X)^{-A})` integers
`N ∈ (X/2, X]` of type `S`", the constant `C` depending only on `A`. -/
def AlmostAllDyadic (S P : ℕ → Prop) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → (excCount S P X : ℝ) ≤ C * X / Real.log X ^ A

/-- The Ramanujan sum `c_p(N)` at a prime `p`: `p - 1` when `p ∣ N`, else `-1`. -/
noncomputable def cp (p N : ℕ) : ℝ := if p ∣ N then (p : ℝ) - 1 else -1

/-- The singular series `S(N) = ∏_p (1 + c_p(N)/φ(p)^2)` of the introduction. The product
converges absolutely; that fact is not proved here, and `tprod` is Mathlib's unconditional
infinite product. The factor at `p = 2` is `2` for even `N` and `0` for odd `N`, which matches
the form `S(N) = 2·1_{2|N} ∏_{p>2} (1 + c_p(N)/φ(p)^2)` of Theorem 3.1. -/
noncomputable def singSeries (N : ℕ) : ℝ :=
  ∏' p : Nat.Primes, (1 + cp p N / (((p : ℕ).totient : ℝ)) ^ 2)

/-- `S'(N) = 2·1_{2∤N} ∏_{p>2} (1 + c_p(N)/φ(p)^2)` of Theorem 3.1. -/
noncomputable def singSeries' (N : ℕ) : ℝ :=
  (if 2 ∣ N then 0 else 2) *
    ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else 1 + cp p N / (((p : ℕ).totient : ℝ)) ^ 2)

/-- `ψ_N(d) = d ∏_{p|d, p|N} (1 - 1/p) ∏_{p|d, p∤N} (1 - 2/p)`. -/
noncomputable def psiN (N d : ℕ) : ℝ :=
  d * ∏ p ∈ d.primeFactors, (if p ∣ N then 1 - 1 / (p : ℝ) else 1 - 2 / (p : ℝ))

/-- The smooth weights of Theorems 1.1 and 3.1: smooth, supported on `[η, 1]`. -/
def SmoothWeight (η : ℝ) (w : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ w ∧ Function.support w ⊆ Set.Icc η 1

/-- `R_{d,l}(N)` of Theorem 1.1:
`Σ_{m+n=N, m≡l mod d} Λ(m)Λ(n)w₁(m/X)w₂(n/X) - S(N)/ψ_N(d) Σ_{m+n=N} w₁(m/X)w₂(n/X)`.
Here `m, n ≥ 0`; the terms with `m = 0` or `n = 0` vanish since `Λ 0 = 0` and the weights
vanish at `0`. -/
noncomputable def Rdl (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) (l : ℤ) : ℝ :=
  (∑ m ∈ Finset.range (N + 1),
      if (m : ℤ) ≡ l [ZMOD d] then
        Λ m * Λ (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X) else 0)
  - singSeries N / psiN N d *
      ∑ m ∈ Finset.range (N + 1), w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)

/-- `sup_{l : (d, l(N-l)) = 1} |R_{d,l}(N)|`, as a supremum in `ℝ≥0` so that the supremum over
the empty set is `0`, the paper's convention. `R_{d,l}` and the coprimality condition depend
only on `l mod d`, so `l` runs over the residues `0, …, d-1`. -/
noncomputable def supR (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N d : ℕ) : NNReal :=
  ((Finset.range d).filter (fun l : ℕ => Int.gcd d ((l : ℤ) * ((N : ℤ) - l)) = 1)).sup
    (fun l => ‖Rdl w₁ w₂ X N d l‖₊)

/-- The weighted error sum `Σ_{d ≤ X^θ} τ(d)^k sup_l |R_{d,l}(N)|` of Theorem 1.1. -/
noncomputable def levelSum (θ : ℝ) (k : ℕ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, ((d.divisors.card : ℕ) : ℝ) ^ k * (supR w₁ w₂ X N d : ℝ)

/-- The Goldbach primes have level of distribution `θ` in the sense of Theorem 1.1: for every
`A > 0`, `k ≥ 0`, and smooth `w₁, w₂` supported on `[η, 1]` with `η > 0`, there are `C₁, C₂`
such that for `X ≥ 2`, all but at most `C₁ X (ln X)^{-A}` integers `N ∈ (X/2, X]` satisfy
`Σ_{d ≤ X^θ} τ(d)^k sup_l |R_{d,l}(N)| ≤ C₂ X (ln X)^{-A}`. -/
def LevelGP (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ k : ℕ, ∀ η : ℝ, 0 < η → ∀ w₁ w₂ : ℝ → ℝ,
    SmoothWeight η w₁ → SmoothWeight η w₂ →
    ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X →
      (excCount (fun _ => True)
        (fun N => levelSum θ k w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
        ≤ C₁ * X / Real.log X ^ A

/-! ### Theorem 3.1, the general level of distribution -/

/-- `β(n) = Σ_{n₁⋯n_k = n, N_i < n_i ≤ N_i'} Λ(n₁)⋯Λ(n_k)`. The bounds are real; for an integer
`n_i` and real `0 ≤ N_i`, `N_i < n_i ≤ N_i'` is `⌊N_i⌋ < n_i ≤ ⌊N_i'⌋`. -/
noncomputable def beta (k : ℕ) (lo hi : Fin k → ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ (Fintype.piFinset fun i => Finset.Ioc ⌊lo i⌋₊ ⌊hi i⌋₊).filter (fun v => ∏ i, v i = n),
    ∏ i, Λ (v i)

/-- The admissible ranges of Theorem 3.1: `N₁ = 1, N₁' = X` if `k = 1`; and if `k > 1`,
`X^η < N_i < N_i' ≤ 2 N_i` and `N₁ ⋯ N_k ≤ X`. -/
def AdmissibleBeta (η X : ℝ) (k : ℕ) (lo hi : Fin k → ℝ) : Prop :=
  (k = 1 ∧ ∀ i, lo i = 1 ∧ hi i = X) ∨
  (1 < k ∧ (∀ i, X ^ η < lo i ∧ lo i < hi i ∧ hi i ≤ 2 * lo i) ∧ ∏ i, lo i ≤ X)

/-- First sum of Theorem 3.1:
`Σ_{d ≤ X^θ} sup_{(d, l(N-l))=1} |Σ_{m+n=N, m≡l (d)} Λ(m)β(n)w₁(m/X)w₂(n/X) - M₀|`,
`M₀ = S(N)/ψ_N(d) Σ_{m+n=N} β(n) w₁(m/X) w₂(n/X)`. -/
noncomputable def betaSum (θ : ℝ) (b : ℕ → ℝ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊X ^ θ⌋₊, (((Finset.range d).filter
    (fun l : ℕ => Int.gcd d ((l : ℤ) * ((N : ℤ) - l)) = 1)).sup (fun l : ℕ =>
      ‖(∑ m ∈ Finset.range (N + 1), if (m : ℤ) ≡ l [ZMOD d] then
          Λ m * b (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X) else 0)
        - singSeries N / psiN N d *
          ∑ m ∈ Finset.range (N + 1), b (N - m) * w₁ ((m : ℝ) / X) * w₂ (((N - m : ℕ) : ℝ) / X)‖₊)
      : NNReal)

/-- Second sum of Theorem 3.1, the switched problem `2m + n = N`, over odd `d ≤ X^θ`:
`sup_{(d, l(N-2l))=1} |Σ_{2m+n=N, m≡l (d)} Λ(m)β(n)w₁(m/X)w₂(n/X) - M₀'|`,
`M₀' = S'(N)/(2ψ_N(d)) Σ_{2m+n=N} β(n) w₁(m/X) w₂(n/X)`. -/
noncomputable def betaSum' (θ : ℝ) (b : ℕ → ℝ) (w₁ w₂ : ℝ → ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 ⌊X ^ θ⌋₊).filter (fun d => ¬ 2 ∣ d), (((Finset.range d).filter
    (fun l : ℕ => Int.gcd d ((l : ℤ) * ((N : ℤ) - 2 * l)) = 1)).sup (fun l : ℕ =>
      ‖(∑ m ∈ Finset.range (N / 2 + 1), if (m : ℤ) ≡ l [ZMOD d] then
          Λ m * b (N - 2 * m) * w₁ ((m : ℝ) / X) * w₂ (((N - 2 * m : ℕ) : ℝ) / X) else 0)
        - singSeries' N / (2 * psiN N d) *
          ∑ m ∈ Finset.range (N / 2 + 1),
            b (N - 2 * m) * w₁ ((m : ℝ) / X) * w₂ (((N - 2 * m : ℕ) : ℝ) / X)‖₊)
      : NNReal)

/-- Theorem 3.1 at exponent `θ` with given `η`: uniformly over admissible ranges, all but
`O(X (ln X)^{-A})` integers `N ∈ (X/2, X]` satisfy both bounds `≪ X (ln X)^{-A}`.
Reading: the implied constants depend on `θ, η, k, A, w₁, w₂` and not on the `N_i`. -/
def BetaLevel (θ η : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ w₁ w₂ : ℝ → ℝ, SmoothWeight η w₁ → SmoothWeight η w₂ →
    ∀ A : ℝ, 0 < A → ∃ C₁ C₂ : ℝ, ∀ X : ℝ, 2 ≤ X → ∀ lo hi : Fin k → ℝ,
      AdmissibleBeta η X k lo hi →
      (excCount (fun _ => True)
          (fun N => betaSum θ (beta k lo hi) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
          ≤ C₁ * X / Real.log X ^ A ∧
      (excCount (fun _ => True)
          (fun N => betaSum' θ (beta k lo hi) w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
          ≤ C₁ * X / Real.log X ^ A

/-! ### Theorem 2.1, the exponential sum estimate -/

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- The left side of (2): `Σ_{d∼D} Σ_{b ∈ ℤ/dℤ} |Σ_n Λ(n) e((α + b/d)n) w(n/X)|²`, with
`d ∼ D` meaning `D < d ≤ 2D`. Since `w` is supported on `[0,1]`, `n` runs over `0 ≤ n ≤ X`. -/
noncomputable def expSumLHS (w : ℝ → ℝ) (X D α : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc ⌊D⌋₊ ⌊2 * D⌋₊, ∑ b ∈ Finset.range d,
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        (Λ n : ℂ) * e ((α + (b : ℝ) / d) * n) * (w ((n : ℝ) / X) : ℂ)‖ ^ 2

/-- Theorem 2.1 as a Prop. The constant depends on `ε` and `w`. `X ≥ 1` and `D > 0` are
implicit in the paper. -/
def ExpSumBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → Function.support w ⊆ Set.Icc 0 1 →
    ∃ C : ℝ, ∀ X D α : ℝ, 1 ≤ X → 0 < D → D ≤ X → 0 ≤ α → α ≤ 1 →
      ∀ (a : ℤ) (q : ℕ), 1 ≤ q → Int.gcd a q = 1 → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
        expSumLHS w X D α ≤
          C * X ^ (2 + ε) * (D ^ 2 / q + q * D / X + D ^ 2 * X ^ (-(1 : ℝ) / 3))

/-! ### The applications -/

/-- Theorem 1.2 property: `N = p₁ + p₂` with `p₁ - p₂ + 1 ∈ P_k`. Membership in `P_k` forces
`p₁ - p₂ + 1 > 0`, that is `p₂ ≤ p₁`, so natural subtraction is exact. The paper's proof
arranges `m - n + 1 > 0`, section 4.1. -/
def DiffForm (k N : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ + p₂ = N ∧ p₂ ≤ p₁ ∧ InP k (p₁ - p₂ + 1)

/-- Theorem 1.3 property: `N = p₁ + p₂` with `2 p₁ p₂ + 1 ∈ P_k`. -/
def ProdForm (k N : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ + p₂ = N ∧ InP k (2 * p₁ * p₂ + 1)

/-! ### The paper's results, cited, with `sorry` -/

/-- Cited. Theorem 1.1: for every `θ ∈ (0, 1/6)` the Goldbach primes have level of
distribution `θ` in the sense of `LevelGP`. -/
theorem akeno_thm1_1 : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ := by sorry

/-- Cited. Theorem 3.1: for `θ ∈ (0, 1/6)` and `η > 0` sufficiently small, both bounds hold. -/
theorem akeno_thm3_1 : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η := by sorry

/-- Cited. Theorem 2.1, the exponential sum estimate (2). -/
theorem akeno_thm2_1 : ExpSumBound := by sorry

/-- Cited. Theorem 1.2: for all but `O(X (ln X)^{-A})` even `N ∈ (X/2, X]` there are primes
with `p₁ + p₂ = N` and `p₁ - p₂ + 1 ∈ P₄`. -/
theorem akeno_thm1_2 : AlmostAllDyadic Even (DiffForm 4) := by sorry

/-- Cited. Theorem 1.3: for all but `O(X (ln X)^{-A})` integers `N ∈ (X/2, X]` with `6 ∣ N`
there are primes with `p₁ + p₂ = N` and `2 p₁ p₂ + 1 ∈ P₁₃`. -/
theorem akeno_thm1_3 : AlmostAllDyadic (fun N => 6 ∣ N) (ProdForm 13) := by sorry

/-! ### Sanity facts, zero sorry -/

theorem lt_of_mem_goldbachPrimes {N p : ℕ} (h : p ∈ GoldbachPrimes N) : p < N := by
  have := h.2.two_le; omega

/-- `P ∩ (N - P)` is symmetric under `p ↦ N - p`. -/
theorem sub_mem_goldbachPrimes {N p : ℕ} (h : p ∈ GoldbachPrimes N) :
    N - p ∈ GoldbachPrimes N := by
  have hp := lt_of_mem_goldbachPrimes h
  refine ⟨h.2, ?_⟩
  rw [show N - (N - p) = p by omega]; exact h.1

/-- `N` has a Goldbach prime iff `N` is a sum of two primes. -/
theorem goldbachPrimes_nonempty_iff (N : ℕ) :
    (GoldbachPrimes N).Nonempty ↔ IsGoldbachSum N := by
  constructor
  · rintro ⟨p, hp⟩
    have := lt_of_mem_goldbachPrimes hp
    exact ⟨p, N - p, hp.1, hp.2, by omega⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    exact ⟨p, hp, by simpa using hq⟩

theorem psiN_one (N : ℕ) : psiN N 1 = 1 := by simp [psiN]

theorem psiN_prime_dvd {N p : ℕ} (hp : p.Prime) (h : p ∣ N) : psiN N p = p - 1 := by
  have h0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp [psiN, hp.primeFactors, h]; field_simp

theorem psiN_prime_not_dvd {N p : ℕ} (hp : p.Prime) (h : ¬ p ∣ N) : psiN N p = p - 2 := by
  have h0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp [psiN, hp.primeFactors, h]; field_simp

/-- The singular series vanishes at odd `N`: the factor at `p = 2` is `1 + c₂(N)/φ(2)² = 0`. -/
theorem singSeries_odd {N : ℕ} (hN : ¬ 2 ∣ N) : singSeries N = 0 := by
  unfold singSeries
  refine (hasProd_zero_of_exists_eq_zero ⟨⟨2, Nat.prime_two⟩, ?_⟩).tprod_eq
  simp [cp, hN]

/-- The factor at `p = 2` is `2` for even `N`. -/
theorem singSeries_factor_two {N : ℕ} (hN : 2 ∣ N) :
    1 + cp 2 N / (((2 : ℕ).totient : ℝ)) ^ 2 = 2 := by
  simp [cp, hN]

theorem singSeries'_even {N : ℕ} (hN : 2 ∣ N) : singSeries' N = 0 := by
  simp [singSeries', hN]

theorem inP_mono {k k' n : ℕ} (h : k ≤ k') (hn : InP k n) : InP k' n :=
  ⟨hn.1, hn.2.trans h⟩

theorem inP_of_prime {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) : InP k p :=
  ⟨hp.pos, by rw [Nat.primeFactorsList_prime hp]; simpa using hk⟩

theorem inP_one (k : ℕ) : InP k 1 := ⟨one_pos, by simp⟩

/-- The paper: "the number 13 arises as 13 = 2 × 6 + 1". -/
theorem thirteen_eq : (13 : ℕ) = 2 * 6 + 1 := rfl

/-- The numerical margin used for Theorem 1.2: `0.1635 < 1/6`. -/
theorem margin_thm1_2 : (0.1635 : ℝ) < 1 / 6 := by norm_num

/-- The weighted sieve parameters in the proof of Theorem 1.2 satisfy `t < s` and `s > 1/θ`,
as Proposition 4.4 requires. -/
theorem params_thm1_2 : (9.5 : ℝ) < 33.5 ∧ 1 / (0.1635 : ℝ) < 33.5 ∧ (2 : ℝ) < 33.5 := by
  norm_num

/-- The proof of Theorem 1.3: `s = 4/γ = 48 > 8` and `1/12 = 0.0833… > 0.0785…`. -/
theorem params_thm1_3 : (4 : ℝ) / (1 / 12) = 48 ∧ (8 : ℝ) < 48 ∧ (0.0785 : ℝ) < 1 / 12 := by
  norm_num

/-! ### Monotonicity in the level and links, zero sorry -/

/-- A smaller exponent `θ' ≤ θ` gives a smaller sum, since the terms are nonnegative. -/
theorem levelSum_mono {θ' θ : ℝ} (hθ : θ' ≤ θ) (k : ℕ) (w₁ w₂ : ℝ → ℝ) {X : ℝ} (hX : 1 ≤ X)
    (N : ℕ) : levelSum θ' k w₁ w₂ X N ≤ levelSum θ k w₁ w₂ X N := by
  unfold levelSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    refine ⟨hd.1, hd.2.trans (Nat.floor_le_floor ?_)⟩
    exact Real.rpow_le_rpow_of_exponent_le hX hθ
  · intro d _ _
    positivity

theorem excCount_mono {S P Q : ℕ → Prop} (hPQ : ∀ N, S N → P N → Q N) (X : ℝ) :
    excCount S Q X ≤ excCount S P X := by
  unfold excCount
  apply Finset.card_le_card
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  exact ⟨hN.1, hN.2.1, hN.2.2.1, fun hP => hN.2.2.2 (hPQ N hN.2.2.1 hP)⟩

/-- Level of distribution `θ` implies level `θ'` for every `θ' ≤ θ`, with the same constants. -/
theorem levelGP_mono {θ' θ : ℝ} (hθ : θ' ≤ θ) (h : LevelGP θ) : LevelGP θ' := by
  intro A hA k η hη w₁ w₂ h₁ h₂
  obtain ⟨C₁, C₂, hC⟩ := h A hA k η hη w₁ w₂ h₁ h₂
  refine ⟨C₁, C₂, fun X hX => le_trans ?_ (hC X hX)⟩
  exact_mod_cast excCount_mono
    (fun N _ hN => (levelSum_mono hθ k w₁ w₂ (by linarith) N).trans hN) X

/-- The statement of Theorem 1.1 gives the exponent `0.1635` used for Theorem 1.2. -/
theorem levelGP_0_1635 (h : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ) : LevelGP 0.1635 :=
  h _ (by norm_num) (by norm_num)

/-- The statement of Theorem 1.1 gives every exponent below `1/6`, including nonpositive ones. -/
theorem levelGP_of_lt (h : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ) (θ : ℝ) (hθ : θ < 1 / 6) :
    LevelGP θ :=
  levelGP_mono (le_max_of_le_left (by linarith) : θ ≤ max ((θ + 1 / 6) / 2) (1 / 12))
    (h _ (lt_max_of_lt_right (by norm_num)) (max_lt (by linarith) (by norm_num)))

theorem almostAll_mono {S P Q : ℕ → Prop} (hPQ : ∀ N, S N → P N → Q N)
    (h : AlmostAllDyadic S P) : AlmostAllDyadic S Q := by
  intro A hA
  obtain ⟨C, hC⟩ := h A hA
  exact ⟨C, fun X hX => le_trans (by exact_mod_cast excCount_mono hPQ X) (hC X hX)⟩

theorem diffForm_mono {k k' N : ℕ} (h : k ≤ k') (hN : DiffForm k N) : DiffForm k' N := by
  obtain ⟨p, q, hp, hq, hs, hle, hP⟩ := hN
  exact ⟨p, q, hp, hq, hs, hle, inP_mono h hP⟩

theorem prodForm_mono {k k' N : ℕ} (h : k ≤ k') (hN : ProdForm k N) : ProdForm k' N := by
  obtain ⟨p, q, hp, hq, hs, hP⟩ := hN
  exact ⟨p, q, hp, hq, hs, inP_mono h hP⟩

theorem isGoldbachSum_of_diffForm {k N : ℕ} (h : DiffForm k N) : IsGoldbachSum N := by
  obtain ⟨p, q, hp, hq, hs, -⟩ := h; exact ⟨p, q, hp, hq, hs⟩

theorem isGoldbachSum_of_prodForm {k N : ℕ} (h : ProdForm k N) : IsGoldbachSum N := by
  obtain ⟨p, q, hp, hq, hs, -⟩ := h; exact ⟨p, q, hp, hq, hs⟩

/-- The literal wording of Theorem 1.2, "`p₁ - p₂ + 1` has at most `k` prime factors", read on
the integer `p₁ - p₂ + 1` through its absolute value, follows from `DiffForm k`. -/
theorem diffForm_int {k N : ℕ} (h : DiffForm k N) : ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    p₁ + p₂ = N ∧ ((p₁ : ℤ) - p₂ + 1).natAbs.primeFactorsList.length ≤ k := by
  obtain ⟨p, q, hp, hq, hs, hle, hP⟩ := h
  refine ⟨p, q, hp, hq, hs, ?_⟩
  have : ((p : ℤ) - q + 1).natAbs = p - q + 1 := by omega
  rw [this]; exact hP.2

/-- The statement of Theorem 1.2 implies the `P_k` versions for every `k ≥ 4`. -/
theorem thm1_2_Pk (h : AlmostAllDyadic Even (DiffForm 4)) (k : ℕ) (hk : 4 ≤ k) :
    AlmostAllDyadic Even (DiffForm k) :=
  almostAll_mono (fun _ _ => diffForm_mono hk) h

/-- Lab form: the statement of Theorem 1.2 implies that all but `O(X (ln X)^{-A})` even `N ∈ (X/2, X]` are sums
of two primes. This is far weaker than binary Goldbach, which is OPEN. -/
theorem almostAll_goldbach_of_thm1_2 (h : AlmostAllDyadic Even (DiffForm 4)) :
    AlmostAllDyadic Even IsGoldbachSum :=
  almostAll_mono (fun _ _ => isGoldbachSum_of_diffForm) h

/-- Lab form from the statement of Theorem 1.3, for multiples of `6`. -/
theorem almostAll_goldbach_six_of_thm1_3 (h : AlmostAllDyadic (fun N => 6 ∣ N) (ProdForm 13)) :
    AlmostAllDyadic (fun N => 6 ∣ N) IsGoldbachSum :=
  almostAll_mono (fun _ _ => isGoldbachSum_of_prodForm) h

/-- Restricting the type `S` of the `N` can only remove exceptions. -/
theorem almostAll_restrict {S S' P : ℕ → Prop} (hS : ∀ N, S' N → S N)
    (h : AlmostAllDyadic S P) : AlmostAllDyadic S' P := by
  intro A hA
  obtain ⟨C, hC⟩ := h A hA
  refine ⟨C, fun X hX => le_trans ?_ (hC X hX)⟩
  unfold excCount
  exact_mod_cast Finset.card_le_card (fun N hN => by
    simp only [Finset.mem_filter] at hN ⊢
    exact ⟨hN.1, hN.2.1, hS N hN.2.2.1, hN.2.2.2⟩)

theorem excCount_eq_zero {S P : ℕ → Prop} (h : ∀ N, S N → P N) (X : ℝ) :
    excCount S P X = 0 := by
  unfold excCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro N hN
  rw [Finset.mem_filter] at hN
  exact hN.2.2.2 (h N hN.2.2.1)

/-- Binary Goldbach would make the exceptional count for sums of two primes zero among even
`N ≥ 4`. The case `N = 2` is excluded since `2` is not a sum of two primes. -/
theorem almostAll_goldbach_of_binaryGoldbach (h : BinaryGoldbach) :
    AlmostAllDyadic (fun N => Even N ∧ 4 ≤ N) IsGoldbachSum := by
  intro A _
  refine ⟨0, fun X _ => ?_⟩
  have : excCount (fun N => Even N ∧ 4 ≤ N) IsGoldbachSum X = 0 := by
    exact excCount_eq_zero (fun N hN => h N hN.1 hN.2) X
  simp [this]

/-! ### Small kernel checks, zero sorry -/

theorem diffForm_6 : DiffForm 4 6 := ⟨3, 3, by norm_num, by norm_num, rfl, le_rfl, inP_one 4⟩
theorem diffForm_8 : DiffForm 4 8 :=
  ⟨5, 3, by norm_num, by norm_num, rfl, by norm_num, inP_of_prime (by norm_num) (by norm_num)⟩
theorem diffForm_10 : DiffForm 4 10 :=
  ⟨7, 3, by norm_num, by norm_num, rfl, by norm_num, inP_of_prime (by norm_num) (by norm_num)⟩
theorem diffForm_18 : DiffForm 4 18 :=
  ⟨13, 5, by norm_num, by norm_num, rfl, by norm_num, ⟨by norm_num, by simp⟩⟩
theorem prodForm_6 : ProdForm 13 6 :=
  ⟨3, 3, by norm_num, by norm_num, rfl, inP_of_prime (by norm_num) (by norm_num)⟩
theorem prodForm_12 : ProdForm 13 12 :=
  ⟨5, 7, by norm_num, by norm_num, rfl, inP_of_prime (by norm_num) (by norm_num)⟩
theorem prodForm_18 : ProdForm 13 18 :=
  ⟨5, 13, by norm_num, by norm_num, rfl, inP_of_prime (by norm_num) (by norm_num)⟩

end LeanLab.Akeno2026
