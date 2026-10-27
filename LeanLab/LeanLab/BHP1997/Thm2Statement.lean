/-
P0069 Baker, Harman, Pintz 1997, Theorem 2, page 3, with the notation of pages 1 and 2 and the
singular series of page 6, read from the page images papers/P0069-original.pdf. Unit U-5050,
CLOUD 20261019T0213Z-cloud14.

STATED as a cited Prop: `Theorem2`, sequences a(k) on I = (x - 2Y, x] and b(m) on J = (Y, 2Y]
with (i) to (iv) satisfy the asymptotic (1.6) for almost all even 2n in [x, x + x^{θ₁θ₂}].
Readings, see STATEMENTS.md: the N of Theorem 2 is the x of (1.2); β(m) in (1.9) is b(m) and the
inner index n is m; C₂(A) and the implied constants are one constant per A.
PROVED: `sing_printed_zero`, the singular series exactly as printed on page 6, with the product
of 1 - 1/(p-1)² over every prime p, is 0, since the factor at p = 2 is 0; the paper says 𝔖(2n)
is always positive, page 2, so the product must run over p > 2, as `sing` does. Cosmetic.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Thm2

open Complex Classical

/-- The twin prime factor `∏_{p > 2} (1 - 1/(p-1)²)`, as an unconditional product over primes. -/
noncomputable def C2 : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The singular series `𝔖(2n) = 2 ∏_{p>2} (1 - 1/(p-1)²) ∏_{p | n, p > 2} (p-1)/(p-2)`, page 6,
with the first product over `p > 2`. -/
noncomputable def sing (n : ℕ) : ℝ :=
  2 * C2 * ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The singular series exactly as printed, the first product over every prime `p`. -/
noncomputable def singPrinted (n : ℕ) : ℝ :=
  2 * (∏' p : {p : ℕ // p.Prime}, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
    ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- FINDING, cosmetic: the printed product has the factor `1 - 1/(2-1)² = 0` at `p = 2`, and a
`tprod` with a zero factor is zero, so the printed `𝔖(2n)` is identically 0. -/
theorem sing_printed_zero (n : ℕ) : singPrinted n = 0 := by
  unfold singPrinted
  have h : (∏' p : {p : ℕ // p.Prime}, (1 - 1 / ((p : ℝ) - 1) ^ 2)) = 0 := by
    apply tprod_of_exists_eq_zero
    exact ⟨⟨2, Nat.prime_two⟩, by norm_num⟩
  rw [h]; ring

/-- `δ_χ`: 1 for the principal character, 0 otherwise. -/
noncomputable def delta {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := if χ = 1 then 1 else 0

/-- `P(z) = ∏_{p < z} p`. -/
noncomputable def primorialBelow (z : ℝ) : ℕ :=
  ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z), p

/-- Theorem 2, page 3, CITED. `Y = x^{θ₁}`, `θ₁ = 11/20 + ε`, `θ₂ = 2(1/16 - 10^-5)`,
`H = Y^{θ₂}`, `Q = ⌊H^{1/2}/2⌋`, `ℒ = log x`, `ℒ' = log Y`, `I = (x - 2Y, x]`, `J = (Y, 2Y]`.
The sequences may depend on `x`. Hypotheses, each for every `A > 0` and `x > C(A)`:
(i) `|Σ_{k ∈ I, k ≤ t} (a(k)χ(k) - δ_χ u/ℒ)| ≪ Yℒ^{-A}` for `t ≤ x`, `χ mod q`, `q ≤ ℒ^A`;
(ii) `a(k) = O(τ(k)^B)`, `b(m) = O(τ(m)^B)`, `a(k) = 0` unless `(k, P(ℒ^A)) = 1`;
(iii) `|Σ_{m ∈ J, m ≤ t} (b(m)χ(m) - δ_χ v/ℒ')| ≪ Yℒ^{-A}` for `t ≤ 2Y`, `q ≤ ℒ^A`;
(iv) for `q ≤ Q` and `z ∈ [qQ/6Y, 6qQ/Y]`,
`Σ_{χ mod q, χ ∉ E_q} ∫_{Y/2}^{3Y} |Σ_{m ∈ J_y} (b(m)χ(m) - δ_χ v/ℒ')|² dy ≪ (qQ)² Yℒ^{-A}`,
`J_y = [y, y + yz]`, with `|E_q| ≪ q^{1/2} ℒ^{-2A}`.
Conclusion (1.6): `Σ_{k+m=2n} a(k)b(m) = uv Y/(ℒℒ') 𝔖(2n)(1 + O(ℒ^{-1}))` for all even `2n` in
`[x, x + x^{θ₁θ₂}]` but fewer than `x^{θ₁θ₂}/log^A x`. -/
def Theorem2 (ε B : ℝ) : Prop :=
  ∀ (a b : ℝ → ℕ → ℂ) (u v : ℝ) (E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)),
    let θ₁ : ℝ := 11 / 20 + ε
    let θ₂ : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    let Y : ℝ → ℝ := fun x => x ^ θ₁
    let Q : ℝ → ℕ := fun x => ⌊(Y x ^ θ₂) ^ (1 / 2 : ℝ) / 2⌋₊
    let I : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊x - 2 * Y x⌋₊ ⌊x⌋₊
    let J : ℝ → Finset ℕ := fun x => Finset.Ioc ⌊Y x⌋₊ ⌊2 * Y x⌋₊
    -- (i)
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (I x).filter (fun k : ℕ => (k : ℝ) ≤ t),
          (a x k * χ (k : ZMod q) - delta χ * u / Real.log x)‖ ≤ C * Y x * Real.log x ^ (-A)) →
    -- (ii)
    (∃ C : ℝ, ∀ x k, ‖a x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖b x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0) →
    -- (iii)
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * Y x →
        ‖∑ m ∈ (J x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ≤
            C * Y x * Real.log x ^ (-A)) →
    -- (iv)
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ Q x →
      ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, (q * Q x : ℝ) / (6 * Y x) ≤ z → z ≤ 6 * q * Q x / Y x →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (Y x / 2)..(3 * Y x),
            ‖∑ m ∈ (J x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m * χ (m : ZMod q) - delta χ * v / Real.log (Y x))‖ ^ 2 ≤
          C * ((q : ℝ) * Q x) ^ 2 * Y x * Real.log x ^ (-A)) →
    -- (1.6) for almost all even 2n in [x, x + x^{θ₁θ₂}]
    ∀ A : ℝ, 0 < A → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x →
      (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ (θ₁ * θ₂)⌋₊).filter (fun N : ℕ => Even N ∧
          K * |u * v| * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2) / Real.log x <
          ‖(∑ k ∈ I x, ∑ m ∈ J x, if k + m = N then a x k * b x m else 0) -
            u * v * Y x / (Real.log x * Real.log (Y x)) * sing (N / 2)‖)).card : ℝ) <
        x ^ (θ₁ * θ₂) / Real.log x ^ A

/-- Theorem 2 as the paper asserts it: `ε` is a small positive constant, chosen so that `Bε` is
small, page 3. -/
def Theorem2Paper : Prop :=
  ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → Theorem2 ε B

end LeanLab.BHP1997.Thm2
