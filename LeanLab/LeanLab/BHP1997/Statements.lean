/-
P0069 R. C. Baker, G. Harman, J. Pintz, The exceptional set for Goldbach's problem in short
intervals, in Sieve Methods, Exponential Sums, and their Applications in Number Theory,
Cambridge University Press 1996/1997, chapter 1, pages 1 to 54. Read 2026-10-19 from the page
images papers/P0069-original.pdf, pages 1 to 4. Unit U-5032.
STATED as cited Props: Theorem 1, Theorem 3 (I) as printed and as the lab reads it with
`1/φ(q)`, Theorem 3 (II) and (III). Theorems 2 and 4, on sequences and Dirichlet polynomials,
are not stated yet.
PROVED: the Remark's decimals; that θ₁ θ₂ < 11/160 for the paper's θ₁ = 11/20 + ε,
θ₂ = 2(1/16 - 10^-5) once ε < 8.8 · 10^-5, so (1.2) on intervals of length x^{θ₁θ₂} covers
[x, x + x^θ]; the positivity u₀v₁ + u₁v₀ - u₁v₁ > 0 from (1.5); and `thm3I_printed_false`:
Theorem 3 (I) exactly as printed, with M/ℒ and no 1/φ(q), is inconsistent, since the residues
1 and 2 mod 3 would hold more than 1.98 M/ℒ primes while q = 1 allows fewer than 1.01 M/ℒ.
A misprint, the intended bound surely has 1/φ(q); the proof of Theorem 1 is not affected.
Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.BHP1997
open Real Filter Classical

/-- The number of even `n` in `[x, x + y]` that are not sums of two primes. -/
noncomputable def exceptions (x y : ℝ) : ℕ :=
  ((Finset.Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => Even n ∧ ¬ IsGoldbachSum n)).card

/-- Theorem 1: for `θ ≥ 11/160`, almost all even numbers in `[x, x + x^θ]` are Goldbach numbers,
with fewer than `x^θ / log^A x` exceptions for `x > C₁(A, θ)`. CITED. -/
def Theorem1 : Prop :=
  ∀ θ : ℝ, 11 / 160 ≤ θ → ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
    (exceptions x (x ^ θ) : ℝ) < x ^ θ / Real.log x ^ A

/-- `π(x; q, a) - π(x - M; q, a)`, the primes `p ≡ a (mod q)` in `(x - M, x]`. -/
noncomputable def piAP (x M : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Ioc ⌊x - M⌋₊ ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card

/-- Theorem 3 (I) exactly as printed on page 4, ℒ = log x: for `x^{0.55+ε} ≤ M ≤ x ℒ^{-1}`,
all `q ≤ ℒ^A`, `x > C₃(A)` and `(a, q) = 1`, `0.99 M/ℒ < π(x;q,a) - π(x-M;q,a) < 1.01 M/ℒ`. -/
def Theorem3I_printed (ε A : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ M : ℝ, x ^ (0.55 + ε) ≤ M → M ≤ x / Real.log x →
    ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → Nat.Coprime a q →
      0.99 * M / Real.log x < piAP x M q a ∧ (piAP x M q a : ℝ) < 1.01 * M / Real.log x

/-- Theorem 3 (I) as the lab reads it, with `1/φ(q)`. CITED, the intended statement. -/
def Theorem3I (ε A : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ M : ℝ, x ^ (0.55 + ε) ≤ M → M ≤ x / Real.log x →
    ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → Nat.Coprime a q →
      0.99 * M / (q.totient * Real.log x) < piAP x M q a ∧
        (piAP x M q a : ℝ) < 1.01 * M / (q.totient * Real.log x)

/-- Theorem 3 (II): for `λ ≥ 1/16 - 10^-5`, all integers `h ≤ Y` with `O(Y ℒ^{-A})` exceptions
satisfy `π(h) - π(h - h^λ) > 0.05 h^λ / log h`. Here `Y = x^{θ₁}`; the lab states it for every
large `Y`, with ℒ read as `log Y`. CITED; QUESTION whether ℒ is `log x` here. -/
def Theorem3II : Prop :=
  ∀ lam : ℝ, 1 / 16 - 1 / 10 ^ 5 ≤ lam → ∀ A : ℝ, 0 < A → ∃ B C : ℝ, ∀ Y : ℝ, C ≤ Y →
    (((Finset.Icc 2 ⌊Y⌋₊).filter (fun h : ℕ => ¬ (0.05 * (h : ℝ) ^ lam / Real.log h
      < (Nat.primeCounting h : ℝ) - ((Finset.Iic ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊).filter Nat.Prime).card))).card : ℝ)
      ≤ B * Y / Real.log Y ^ A

/-- Theorem 3 (III): for `x > C₄` the interval `[x, x + x^μ]`, `μ = 0.0335`, contains Goldbach
numbers, even sums of two primes. CITED. -/
def Theorem3III : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∃ n : ℕ, x ≤ n ∧ (n : ℝ) ≤ x + x ^ (0.0335 : ℝ) ∧
    Even n ∧ IsGoldbachSum n

/-- The Remark: `7/81 = 0.08641...` and `11/160 = 0.06875`. -/
theorem remark : (0.08641 : ℝ) < 7 / 81 ∧ (7 / 81 : ℝ) < 0.08642 ∧ (11 / 160 : ℝ) = 0.06875 := by
  norm_num

/-- `θ₁ θ₂ < 11/160` for `θ₁ = 11/20 + ε`, `θ₂ = 2(1/16 - 10^-5)` and `0 < ε < 8.8 · 10^-5`;
and `θ₁ θ₂ > 0.06873`, so the subintervals are long. -/
theorem theta12 {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 8.8 / 10 ^ 5) :
    (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) < 11 / 160 ∧
    0.06873 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) := by
  constructor <;> nlinarith

/-- From (1.5): `u₀ v₁ + u₁ v₀ - u₁ v₁ > 0`, given also `u₀ ≤ u₁` and `v₀ ≤ v₁`, which hold
since `a₀ ≤ ρ ≤ a₁` and `b₀ ≤ ρ ≤ b₁`. -/
theorem constants15 {u0 u1 v0 v1 : ℝ} (hu0 : 0.99 < u0) (hu : u0 ≤ u1) (hu1 : u1 < 1.01)
    (hv0 : 0.05 < v0) (hv : v0 ≤ v1) (hv1 : v1 < 2.2) : 0 < u0 * v1 + u1 * v0 - u1 * v1 := by
  nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ v1)]

/-- The residue classes 1 and 2 mod 3 are disjoint parts of all primes. -/
theorem piAP_three_le (x M : ℝ) : piAP x M 3 1 + piAP x M 3 2 ≤ piAP x M 1 0 := by
  unfold piAP
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter] at hp ⊢
    rcases hp with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> exact ⟨h1, h2, by simp [Nat.mod_one]⟩
  · rw [Finset.disjoint_filter]
    intro p _ h1 h2
    omega

/-- Theorem 3 (I) as printed is inconsistent: for every `ε ∈ (0, 0.45)` and `A > 0` it fails. -/
theorem thm3I_printed_false {ε A : ℝ} (hε : 0 < ε) (hε1 : ε < 0.45) (hA : 0 < A) :
    ¬ Theorem3I_printed ε A := by
  rintro ⟨C, hC⟩
  have r : (0 : ℝ) < 0.45 - ε := by linarith
  have e1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (0.45 - ε) := by
    filter_upwards [(isLittleO_log_rpow_atTop r).bound (show (0 : ℝ) < 1 by norm_num),
      eventually_ge_atTop 1] with x hx hx1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact hx
  have e2 : ∀ᶠ x : ℝ in atTop, 3 ≤ Real.log x ^ A :=
    ((tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 3)
  have e3 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have e4 : ∀ᶠ x : ℝ in atTop, max C 1 ≤ x := eventually_ge_atTop _
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := (e1.and (e2.and (e3.and e4))).exists
  have hxC : C ≤ x := le_trans (le_max_left _ _) hx4
  have hx0 : 0 < x := by linarith [le_max_right C 1]
  have hL0 : 0 < Real.log x := by linarith
  set L := Real.log x with hL
  have hM1 : x ^ (0.55 + ε) ≤ x / L := by
    rw [le_div_iff₀ hL0]
    have h := mul_le_mul_of_nonneg_left hx1 (Real.rpow_nonneg hx0.le (0.55 + ε))
    rw [← Real.rpow_add hx0, show (0.55 + ε) + (0.45 - ε) = (1 : ℝ) by ring, Real.rpow_one] at h
    exact h
  have hq1 : ((1 : ℕ) : ℝ) ≤ L ^ A := by push_cast; linarith
  have hq3 : ((3 : ℕ) : ℝ) ≤ L ^ A := by push_cast; linarith
  obtain ⟨-, h10⟩ := hC x hxC (x / L) hM1 le_rfl 1 0 le_rfl hq1 (by norm_num)
  obtain ⟨h31, -⟩ := hC x hxC (x / L) hM1 le_rfl 3 1 (by norm_num) hq3 (by norm_num)
  obtain ⟨h32, -⟩ := hC x hxC (x / L) hM1 le_rfl 3 2 (by norm_num) hq3 (by norm_num)
  have hsum : (piAP x (x / L) 3 1 : ℝ) + piAP x (x / L) 3 2 ≤ piAP x (x / L) 1 0 := by
    exact_mod_cast piAP_three_le x (x / L)
  have hpos : 0 < x / L / L := by positivity
  have e : ∀ c : ℝ, c * (x / L) / L = c * (x / L / L) := fun c => by ring
  rw [e] at h10 h31 h32
  linarith

/-- Page 5: the constant 0.0335 is larger than 0.535/16, and than 0.535 λ for every
`λ ≤ 1/16`. -/
theorem mu_check : (0.535 : ℝ) / 16 < 0.0335 ∧ ∀ lam : ℝ, lam ≤ 1 / 16 → 0.535 * lam < 0.0335 := by
  refine ⟨by norm_num, fun lam h => by nlinarith⟩

end LeanLab.BHP1997
