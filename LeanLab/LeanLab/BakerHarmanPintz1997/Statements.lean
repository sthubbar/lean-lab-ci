/-
P0069 R. C. Baker, G. Harman, J. Pintz, The exceptional set for Goldbach's problem in short
intervals, chapter 1, pages 1-54, of Sieve Methods, Exponential Sums, and their Applications in
Number Theory, LMS Lecture Note Series 237, Cambridge 1997. Scan without text layer; every
formula below was read on page images rendered at 130 dpi, the constants checked again at 300 dpi.
Book page `p` is PDF page `p + 13` of the scanned volume.

* Theorem 1, p. 1: for `θ ≥ 11/160` almost all even numbers in `[x, x + x^θ]` are Goldbach
  numbers, fewer than `x^θ / log^A x` exceptions. CITED, sorry.
* The choice `θ₁ = 11/20 + ε`, `θ₂ = 2(1/16 - 10⁻⁵)`, statement (1.2), Theorem 2, Theorem 3,
  Theorem 4, Lemmas 1 to 16, 19, 20, 22, 24, 26, 29, 30, 32 to 35: CITED, sorry, as Lean `Prop`s.
  Lemmas 17, 18, 21, 23, 25, 27, 28 describe steps of the decomposition procedure and are not
  stated in Lean; their exponent checks are PROVED below where they are pure arithmetic.
* PROVED here: the exponent arithmetic of Sections 1, 3, 4, 5. The deductions, Theorem 1 from
  (1.2), Theorem 1 to the lab's exceptional set, Theorem 3 (III) from Theorem 3 (II) and Baker and
  Harman's lower bound, and Lemma 31, are in `LeanLab.BakerHarmanPintz1997.Deductions`.

AI-written Lean code, Claude, 2026-10-18, run 20261018T1603Z-12862.
Checked only by the Lean kernel. Binary Goldbach is OPEN; Theorem 1 says exceptions, if any,
are rare in short intervals.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.ExceptionalSet.Statements
import LeanLab.LanguascoPerelli1996.Statements
import LeanLab.PerelliPintz1992.Statements

namespace LeanLab.BakerHarmanPintz1997
open Real Filter Topology ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ### Conventions -/

/-- `E(x,H)` of the lab, `LanguascoPerelli1996.EH`: even `n ∈ [x, x+H]` not a sum of two primes. -/
noncomputable abbrev EH (x H : ℝ) : ℕ := LeanLab.LanguascoPerelli1996.EH x H

/-- `𝓛 = log x`. -/
noncomputable def L (x : ℝ) : ℝ := Real.log x

/-- The divisor function `τ(n)` as a real number. -/
noncomputable def tau (n : ℕ) : ℝ := (ArithmeticFunction.sigma 0 n : ℝ)

/-- `𝔖(N)` for even `N = 2n`, reused from `PerelliPintz1992.S2k`:
`𝔖(2n) = 2 ∏_{p>2} (1 - 1/(p-1)²) ∏_{p ∣ n, p>2} (p-1)/(p-2)`, p. 6. -/
noncomputable def SS (N : ℕ) : ℝ := LeanLab.PerelliPintz1992.S2k (N / 2)

/-- `δ_χ`, `1` for the principal character and `0` otherwise, p. 3. -/
noncomputable def delta {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ := if χ = 1 then 1 else 0

/-- `(n, P(z)) = 1`: no prime `p < z` divides `n`. -/
def Rough (n : ℕ) (z : ℝ) : Prop := ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ n

/-- `ψ(n,z)`, (4.6), p. 25. -/
noncomputable def psi (n : ℕ) (z : ℝ) : ℂ := if Rough n z then 1 else 0

/-- `f ≫ g` for functions of `x`: `c g(x) ≤ f(x)` for large `x`, some `c > 0`. -/
def GG (f g : ℝ → ℝ) : Prop := ∃ c : ℝ, 0 < c ∧ ∃ X1 : ℝ, ∀ x : ℝ, X1 ≤ x → c * g x ≤ f x

/-- `f ≪ g` for functions of `x`. -/
def LL (f g : ℝ → ℝ) : Prop := GG g f

/-- Eventually in `x`. -/
def Ev (P : ℝ → Prop) : Prop := ∃ X1 : ℝ, ∀ x : ℝ, X1 ≤ x → P x

/-! ### Section 1, pages 1-4 -/

/-- "Almost all even numbers in `[x, x + x^θ]` are Goldbach numbers", p. 1: for every `A > 0`
and `x > C₁(A,θ)` there are fewer than `x^θ / log^A x` exceptions. -/
def AlmostAllShort (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → (EH x (x ^ θ) : ℝ) < x ^ θ / Real.log x ^ A

/-- **Theorem 1**, p. 1: for `θ ≥ 11/160` almost all even numbers in `[x, x + x^θ]` are Goldbach
numbers. -/
def Theorem1 : Prop := ∀ θ : ℝ, 11 / 160 ≤ θ → AlmostAllShort θ

/-- CITED. Baker, Harman, Pintz 1997, Theorem 1. -/
theorem theorem1 : Theorem1 := by sorry

/-- Ramachandra [26], condition 1.1 as quoted on page 1.
CONDITIONAL ON the cited theorem1 through the exponent comparison. -/
theorem ramachandra : ∀ θ : ℝ, 3 / 5 < θ → AlmostAllShort θ := by
  intro θ hθ
  exact theorem1 θ (by linarith)

/-- Li [18], θ greater than 7/81 as quoted on page 1.
CONDITIONAL ON the cited theorem1 through the exponent comparison. -/
theorem li : ∀ θ : ℝ, 7 / 81 < θ → AlmostAllShort θ := by
  intro θ hθ
  exact theorem1 θ (by linarith)

/-- `θ₁ = 11/20 + ε`, p. 1. -/
noncomputable def theta1 (ε : ℝ) : ℝ := 11 / 20 + ε

/-- `θ₂ = 2(1/16 - 10⁻⁵)`, p. 1. -/
noncomputable def theta2 : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)

/-- `Y = x^{θ₁}`, p. 1. -/
noncomputable def Yof (ε x : ℝ) : ℝ := x ^ theta1 ε

/-- `S(n)` of (1.2) for `N = 2n`, counted: pairs `k + m = N`, `k ∈ I = (x - 2Y, x]`,
`m ∈ J = (Y, 2Y]`, both prime. -/
noncomputable def Scount (ε x : ℝ) (N : ℕ) : ℕ :=
  ((Finset.Ioc ⌊x - 2 * Yof ε x⌋₊ ⌊x⌋₊).filter (fun k => k ≤ N ∧ k.Prime ∧ (N - k).Prime ∧
    Yof ε x < ((N - k : ℕ) : ℝ) ∧ ((N - k : ℕ) : ℝ) ≤ 2 * Yof ε x)).card

/-- (1.2), p. 1: `S(n) > 0` for almost all even `2n ∈ K = [x, x + x^{θ₁θ₂}]`. -/
def Prop12 (ε : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
    ((((Finset.Icc ⌈x⌉₊ ⌊x + x ^ (theta1 ε * theta2)⌋₊).filter
      (fun N => Even N ∧ Scount ε x N = 0)).card : ℕ) : ℝ) <
      x ^ (theta1 ε * theta2) / Real.log x ^ A

/-- CITED. (1.2) for `ε` small, the content of Sections 2 to 5. -/
theorem prop12 : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Prop12 ε := by sorry

/-- `H = Y^{θ₂}`, p. 3. -/
noncomputable def Hof (ε x : ℝ) : ℝ := Yof ε x ^ theta2

/-- `Q = [H^{1/2}/2]`, p. 3. -/
noncomputable def Qof (ε x : ℝ) : ℕ := ⌊Hof ε x ^ (1 / 2 : ℝ) / 2⌋₊

/-- The interval `I = (x - 2Y, x]` as a set of integers. -/
noncomputable def Iset (ε x : ℝ) : Finset ℕ := Finset.Ioc ⌊x - 2 * Yof ε x⌋₊ ⌊x⌋₊

/-- The interval `J = (Y, 2Y]` as a set of integers. -/
noncomputable def Jset (ε x : ℝ) : Finset ℕ := Finset.Ioc ⌊Yof ε x⌋₊ ⌊2 * Yof ε x⌋₊

/-- `J_y = [y, y + yz]` as a set of integers. -/
noncomputable def Jy (y z : ℝ) : Finset ℕ := Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊

/-- `Σ_{k+m=N, k ∈ I, m ∈ J} a(k) b(m)`. -/
noncomputable def convIJ (ε x : ℝ) (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ (Iset ε x).filter (fun k => k ≤ N ∧ N - k ∈ Jset ε x), a k * b (N - k)

/-- **Theorem 2**, p. 3. Sequences `a(k)`, `k ∈ I`, and `b(m)`, `m ∈ J`, depending on `x`,
with constants `u, v`, satisfying (i) to (iv) for every `A > 0`, give (1.6),
`Σ_{k+m=2n} a(k)b(m) = uv Y/(𝓛𝓛') 𝔖(2n)(1 + O(𝓛⁻¹))`, for almost all even `2n ∈ [x, x+x^{θ₁θ₂}]`.
`E_q` is a set of `O(q^{1/2}𝓛^{-2A})` characters mod `q`. In (1.9) the paper prints `β(m)` and
`n ∈ J_y`; we read `b(m)`, `m ∈ J_y`. -/
def Theorem2 (ε : ℝ) : Prop :=
  ∀ (a b : ℝ → ℕ → ℝ) (u v B : ℝ)
    (Ex : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q)),
  -- `u, v > 0`: not printed on p. 3, but (1.6) with relative error `1 + O(𝓛⁻¹)` is degenerate
  -- for `uv = 0`, where it would force the convolution to vanish exactly; every use in the
  -- paper has `u, v` near 1, (1.5). Added by audit U-1009, run 20261019T0503Z-10740.
  0 < u → 0 < v →
  -- (i), (1.7)
  (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ t : ℝ, t ≤ x →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖∑ k ∈ (Iset ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - ((delta χ * u / L x : ℝ) : ℂ))‖ ≤
        C * Yof ε x / L x ^ A) →
  -- (ii)
  (∃ C : ℝ, ∀ x k, |a x k| ≤ C * tau k ^ B) → (∃ C : ℝ, ∀ x m, |b x m| ≤ C * tau m ^ B) →
  (∀ A : ℝ, 0 < A → Ev fun x => ∀ k, a x k ≠ 0 → Rough k (L x ^ A)) →
  -- (iii), (1.8), with `𝓛' = log Y`
  (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ t : ℝ, t ≤ 2 * Yof ε x →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ (Jset ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b x m : ℂ) * χ (m : ZMod q) - ((delta χ * v / Real.log (Yof ε x) : ℝ) : ℂ))‖ ≤
        C * Yof ε x / L x ^ A) →
  -- (iv), (1.9), and the size of `E_q`
  (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
    (∀ q : ℕ, ((Ex x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) / L x ^ (2 * A)) ∧
    ∀ (q : ℕ) [NeZero q], q ≤ Qof ε x → ∀ z : ℝ, q * Qof ε x / (6 * Yof ε x) ≤ z →
      z ≤ 6 * q * Qof ε x / Yof ε x →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ∉ Ex x q),
        ∫ y in (Yof ε x / 2)..(3 * Yof ε x),
          ‖∑ m ∈ Jy y z, ((b x m : ℂ) * χ (m : ZMod q) -
            ((delta χ * v / Real.log (Yof ε x) : ℝ) : ℂ))‖ ^ 2 ≤
        C * ((q : ℝ) * Qof ε x) ^ 2 * Yof ε x / L x ^ A) →
  -- conclusion: (1.6) for almost all `2n` in `[x, x + x^{θ₁θ₂}]`
  ∃ C : ℝ, ∀ A : ℝ, 0 < A → ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
    ((((Finset.Icc ⌈x⌉₊ ⌊x + x ^ (theta1 ε * theta2)⌋₊).filter (fun N => Even N ∧
      C * |u * v * Yof ε x / (L x * Real.log (Yof ε x)) * SS N| / L x <
        |convIJ ε x (a x) (b x) N - u * v * Yof ε x / (L x * Real.log (Yof ε x)) * SS N|)).card
        : ℕ) : ℝ) < x ^ (theta1 ε * theta2) / L x ^ A

/-- CITED. Theorem 2, proved in Section 2. -/
theorem theorem2 : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Theorem2 ε := by sorry

/-- `π(x; q, a)`, primes `p ≤ x` with `p ≡ a mod q`. -/
noncomputable def piAP (x : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card

/-- **Theorem 3 (I) as printed**, p. 4: for `x^{0.55+ε} ≤ M ≤ x𝓛⁻¹`, `q ≤ 𝓛^A`, `(a,q) = 1`,
`x > C₃(A)`, `0.99M/𝓛 < π(x;q,a) - π(x-M;q,a) < 1.01M/𝓛`. The paper writes `N > C₃(A)` for
`x > C₃(A)`. FALSE as printed, the factor `1/φ(q)` is missing: see
`Theorem3ILiteral.not_theorem3I_literal`, PROVED, audit U-1009. -/
def Theorem3I_literal : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C3 : ℝ, ∀ x : ℝ, C3 < x → ∀ M : ℝ,
    x ^ (0.55 + ε) ≤ M → M ≤ x / L x → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ L x ^ A → Nat.Coprime a q →
      0.99 * M / L x < (piAP x q a : ℝ) - piAP (x - M) q a ∧
      (piAP x q a : ℝ) - piAP (x - M) q a < 1.01 * M / L x

/-- **Theorem 3 (I)**, p. 4, with the evident `φ(q)`: the paper's proof picks out the class
`a mod q` "using characters in standard fashion", which gives the main term `M/(φ(q)𝓛)`.
Audit U-1009, run 20261019T0503Z-10740. -/
def Theorem3I : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ C3 : ℝ, ∀ x : ℝ, C3 < x → ∀ M : ℝ,
    x ^ (0.55 + ε) ≤ M → M ≤ x / L x → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ L x ^ A → Nat.Coprime a q →
      0.99 * M / (Nat.totient q * L x) < (piAP x q a : ℝ) - piAP (x - M) q a ∧
      (piAP x q a : ℝ) - piAP (x - M) q a < 1.01 * M / (Nat.totient q * L x)

/-- CITED. Theorem 3 (I), read with `φ(q)`. -/
theorem theorem3I : Theorem3I := by sorry

/-- `λ₀ = 1/16 - 10⁻⁵`, p. 4. -/
noncomputable def lam0 : ℝ := 1 / 16 - 1 / 10 ^ 5

/-- `π(h) - π(h - h^λ) > 0.05 h^λ / log h`. -/
def GapGood (lam : ℝ) (h : ℕ) : Prop :=
  0.05 * (h : ℝ) ^ lam / Real.log h <
    (Nat.primeCounting h : ℝ) - Nat.primeCounting ⌊(h : ℝ) - (h : ℝ) ^ lam⌋₊

/-- The exceptional `h ≤ Y` of Theorem 3 (II). -/
noncomputable def gapExc (lam Y : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊Y⌋₊).filter (fun h => ¬ GapGood lam h)).card

/-- Theorem 3 (II), p. 4, literally: for `λ ≥ 1/16 - 10⁻⁵`, all integers `h ≤ Y` but
`O(Y𝓛^{-A})` satisfy `π(h) - π(h - h^λ) > 0.05h^λ/log h`. No upper bound on `λ` is printed;
see `Deductions.not_theorem3II_literal`, it fails for `λ = 2`. -/
def Theorem3II_literal : Prop :=
  ∀ lam : ℝ, lam0 ≤ lam → ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y →
    (gapExc lam Y : ℝ) ≤ C * Y / Real.log Y ^ A

/-- **Theorem 3 (II)** with the evident range `λ ≤ 1`. -/
def Theorem3II : Prop :=
  ∀ lam : ℝ, lam0 ≤ lam → lam ≤ 1 → ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y →
    (gapExc lam Y : ℝ) ≤ C * Y / Real.log Y ^ A

/-- Theorem 3 (II) at `λ = λ₀` only. Audit U-1009, run 20261019T0503Z-10740: the paper's
proof, the sequence `b₀` of Section 5, is built for `λ₀`; that the same constant `0.05` holds for
every `λ ∈ [λ₀, 1]` is not shown on p. 4, and intervals for larger `λ` contain the `λ₀` ones but
need the larger bound `0.05h^λ/log h`, so it does not follow by monotonicity. Theorem 3 (III) uses
only `λ₀`, see `Deductions.theorem3III_of_at`. -/
def Theorem3IIAt : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → (gapExc lam0 Y : ℝ) ≤ C * Y / Real.log Y ^ A

theorem theorem3IIAt_of (h : Theorem3II) : Theorem3IIAt :=
  fun A hA => h lam0 le_rfl (by unfold lam0; norm_num) A hA

/-- CITED. Theorem 3 (II) at `λ = λ₀`, from the sequence `b₀` of Section 5. This replaces the
earlier cited `theorem3II` for every `λ ∈ [λ₀, 1]`, audit U-1009; `Theorem3II` is kept as a def. -/
theorem theorem3IIAt : Theorem3IIAt := by sorry

/-- `μ = 0.0335`, p. 4. -/
noncomputable def mu : ℝ := 0.0335

/-- **Theorem 3 (III)**, p. 4: for `x > C₄` the interval `[x, x + x^μ]` contains a Goldbach
number, `μ = 0.0335`. -/
def Theorem3III : Prop :=
  ∃ C4 : ℝ, ∀ x : ℝ, C4 < x → ∃ n : ℕ, x ≤ n ∧ (n : ℝ) ≤ x + x ^ mu ∧ Even n ∧ IsGoldbachSum n

/-- Baker and Harman [2], quoted p. 5: `π(x) - π(x-y) ≫ y/log x` for `x^{0.535} ≤ y ≤ x`. -/
def BakerHarmanLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ y : ℝ, x ^ (0.535 : ℝ) ≤ y → y ≤ x →
    c * y / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting ⌊x - y⌋₊

/-- CITED. Baker and Harman, Proc. LMS 72, 1996. -/
theorem bakerHarman : BakerHarmanLower := by sorry

/-! ### Section 3, Dirichlet polynomials, pages 11-24 -/

/-- A Dirichlet polynomial `Σ_{n ∈ supp} a(n) χ(n) n^{-s}`. -/
structure DP where
  coef : ℕ → ℂ
  supp : Finset ℕ

/-- Its value at `s` for a character `χ`. -/
noncomputable def DP.eval (P : DP) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ P.supp, P.coef n * χ (n : ZMod q) * (n : ℂ) ^ (-s)

/-- Length `F`, `n ≍ F`: `c₁F < n < c₂F` on the support, p. 11. -/
def DP.HasLen (P : DP) (F c1 c2 : ℝ) : Prop := ∀ n ∈ P.supp, c1 * F < n ∧ (n : ℝ) < c2 * F

/-- (3.1): `abs a(n) ≤ τ(n)^B`. -/
def DP.Coef31 (P : DP) (B : ℝ) : Prop := ∀ n ∈ P.supp, ‖P.coef n‖ ≤ tau n ^ B

/-- `G(F) = Σ abs a(n)² / n`, Lemma 1. -/
noncomputable def DP.G (P : DP) : ℝ := ∑ n ∈ P.supp, ‖P.coef n‖ ^ 2 / n

/-- A set `𝒮` of pairs `(t, χ)`, `χ mod q`, together with `T`. -/
structure Cfg where
  q : ℕ
  T : ℝ
  S : Finset (ℝ × DirichletCharacter ℂ q)

/-- Well-spaced, p. 11: `t ∈ [-T,T]` and `abs (t - t') ≥ 1` for distinct `(t,χ), (t',χ)`. -/
def Cfg.WellSpaced (c : Cfg) : Prop :=
  ∀ e ∈ c.S, |e.1| ≤ c.T ∧ ∀ e' ∈ c.S, e.2 = e'.2 → e ≠ e' → 1 ≤ |e.1 - e'.1|

/-- The standing ranges of Section 3: `𝒮` well-spaced, `1 ≤ q ≤ x`, `2 < T ≤ x/4`. -/
def Cfg.Std (c : Cfg) (x : ℝ) : Prop :=
  c.WellSpaced ∧ 1 ≤ c.q ∧ (c.q : ℝ) ≤ x ∧ 2 < c.T ∧ c.T ≤ x / 4

/-- `1/2 + it`. -/
noncomputable def half (t : ℝ) : ℂ := 1 / 2 + t * Complex.I

/-- `‖F‖_p = (Σ_{(t,χ) ∈ 𝒮} abs F(1/2+it,χ)^p)^{1/p}`. -/
noncomputable def pnorm (P : DP) (c : Cfg) (p : ℝ) : ℝ :=
  (∑ e ∈ c.S, ‖P.eval e.2 (half e.1)‖ ^ p) ^ (1 / p)

/-- `‖F₁ ⋯ F_r‖₁` for a product of polynomials. -/
noncomputable def norm1prod (Ps : List DP) (c : Cfg) : ℝ :=
  ∑ e ∈ c.S, ‖(Ps.map (fun P => P.eval e.2 (half e.1))).prod‖

/-- (3.2) for a family of polynomials of length `F(x)` on a family of sets `𝒮(x)`:
`‖F‖_∞ ≪ F^{1/2}𝓛^{-A}` for all `A > 0`. -/
def Cond32 (P : ℝ → DP) (F : ℝ → ℝ) (𝒮 : ℝ → Set Cfg) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ c ∈ 𝒮 x, ∀ e ∈ c.S,
    ‖(P x).eval e.2 (half e.1)‖ ≤ C * F x ^ (1 / 2 : ℝ) / L x ^ A

/-- (3.9) with `X = x`: `‖Π Fᵢ‖₁ ≪ X^{1/2}𝓛^{-A}` for all `A > 0`. -/
def Concl39 (Ps : ℝ → List DP) (𝒮 : ℝ → Set Cfg) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ c ∈ 𝒮 x,
    norm1prod (Ps x) c ≤ C * x ^ (1 / 2 : ℝ) / L x ^ A

/-- Every polynomial of the family has length `F i x` and satisfies (3.1). -/
def FamOK (Ps : ℝ → List DP) (Fs : List (ℝ → ℝ)) (B c1 c2 : ℝ) : Prop :=
  ∀ x, (Ps x).length = Fs.length ∧ ∀ i (h1 : i < (Ps x).length) (h2 : i < Fs.length),
    ((Ps x).get ⟨i, h1⟩).HasLen ((Fs.get ⟨i, h2⟩) x) c1 c2 ∧ ((Ps x).get ⟨i, h1⟩).Coef31 B

/-- **Lemma 1**, p. 11, (3.3) and (3.4). -/
def Lemma1 : Prop :=
  ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K : ℝ, ∀ x F : ℝ, 2 ≤ F → F ≤ x →
    ∀ P : DP, P.HasLen F c1 c2 → P.Coef31 B → ∀ c : Cfg, c.Std x →
      pnorm P c 2 ^ 2 ≤ K * L x * (c.q * c.T + F) * P.G ∧
      ∀ V : ℝ, 0 < V → (∀ e ∈ c.S, V ≤ ‖P.eval e.2 (half e.1)‖) →
        (c.S.card : ℝ) ≤ K * L x ^ 2 * (P.G * F / V ^ 2 + P.G ^ 3 * F * c.q * c.T / V ^ 6)

/-- CITED. Lemma 1, from Montgomery [21] and Huxley [14]. -/
theorem lemma1 : Lemma1 := by sorry

/-- `γ(θ) = min(4θ - 2, (20θ - 9)/11, (72θ - 37)/11)`, (3.8). -/
noncomputable def gam (θ : ℝ) : ℝ := min (4 * θ - 2) (min ((20 * θ - 9) / 11) ((72 * θ - 37) / 11))

/-- **Theorem 4**, p. 12, with `X = x`. `MNL = X`, `M = X^{α₁}`, `N = X^{α₂}`, (3.1) for all three,
(3.2) for `L`, `qT = X^{1-θ}`, `1/2 + ε < θ < 7/12`, (3.6), (3.7); then (3.9). -/
def Theorem4 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ θ α1 α2 : ℝ, 1 / 2 + ε < θ → θ < 7 / 12 → |α1 - α2| < 2 * θ - 1 - ε →
    1 - (α1 + α2) < gam θ - ε →
  ∀ (B c1 c2 : ℝ) (M N Lp : ℝ → DP) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x, Lp x])
      [fun x => x ^ α1, fun x => x ^ α2, fun x => x ^ (1 - α1 - α2)] B c1 c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) * c.T = x ^ (1 - θ)) →
    Cond32 Lp (fun x => x ^ (1 - α1 - α2)) 𝒮 →
    Concl39 (fun x => [M x, N x, Lp x]) 𝒮

/-- CITED. Theorem 4, Section 3. -/
theorem theorem4 : Theorem4 := by sorry

/-- **Lemma 2**, p. 15: `qT ≤ M^γ`, `1 ≤ γ < B` with `B` of (3.1), `2 ≤ M ≤ x` for large `x` as on p. 11, (3.1), (3.2) give `‖M‖_β ≪ M^{1/2}𝓛^{-A}` when
`β ≥ 4γ - 2h + ε` (3.18) and `2h - ε < β < 6h - ε` (3.19), `h` a fixed integer. -/
def Lemma2 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (γ β : ℝ) (h : ℕ), 1 ≤ γ → 4 * γ - 2 * h + ε ≤ β → 2 * h - ε < β → β < 6 * h - ε →
  ∀ (B c1 c2 : ℝ) (M : ℝ → DP) (F : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x]) [F] B c1 c2 → γ < B →
    Ev (fun x => 2 ≤ F x ∧ F x ≤ x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) * c.T ≤ F x ^ γ) →
    Cond32 M F 𝒮 →
    ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (M x) c β ≤ C * F x ^ (1 / 2 : ℝ) / L x ^ A

/-- CITED. Lemma 2, after Harman [8], Lemma 4. -/
theorem lemma2 : Lemma2 := by sorry

/-- The cases (i) to (iv) of Lemma 3, on the lengths `L, N, R` as functions of `x`, `B₀ε` in (iv). -/
def Lemma3Cases (ε B0 : ℝ) (Ll Nl Rl : ℝ → ℝ) : Prop :=
  (GG Nl (fun x => x ^ (0.1125 : ℝ)) ∧ GG Rl (fun x => x ^ (0.225 : ℝ)) ∧
    GG Ll (fun x => x ^ (9 / 70 : ℝ))) ∨
  (GG Nl (fun x => x ^ (0.225 : ℝ)) ∧ GG Rl (fun x => x ^ (0.15 : ℝ)) ∧
    GG Ll (fun x => x ^ (0.1 : ℝ))) ∨
  (GG Nl (fun x => x ^ (0.15 : ℝ)) ∧ GG (fun x => Rl x ^ 2 * Ll x) (fun x => x ^ (0.45 : ℝ)) ∧
    GG Ll (fun x => x ^ (0.18 : ℝ))) ∨
  (LL Nl (fun x => x ^ (0.15 : ℝ)) ∧ LL Rl (fun x => x ^ (0.15 : ℝ)) ∧
    GG (fun x => Nl x * Rl x) (fun x => x ^ (9 / 35 : ℝ)) ∧
    GG (fun x => Ll x * Nl x * Rl x) (fun x => x ^ (63 / 130 + B0 * ε)))

/-- **Lemma 3**, p. 16. `LMNR = X`, (3.1) for all four, `qT ≤ X^{0.45-ε/2}` (3.23), `M ≥ qT`
(3.24), (3.2) for `L, N, R`; each of (i) to (iv) gives `‖LMNR‖₁ ≪ X^{1/2} log^{-A} X`. -/
def Lemma3 : Prop :=
  ∃ ε0 B0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (B c1 c2 : ℝ) (Lp M N R : ℝ → DP) (Ll Ml Nl Rl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg),
    0 < c1 → c1 < c2 →
    FamOK (fun x => [Lp x, M x, N x, R x]) [Ll, Ml, Nl, Rl] B c1 c2 →
    (∀ x, Ll x * Ml x * Nl x * Rl x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2) ∧ (c.q : ℝ) * c.T ≤ Ml x) →
    Cond32 Lp Ll 𝒮 → Cond32 N Nl 𝒮 → Cond32 R Rl 𝒮 →
    Lemma3Cases ε B0 Ll Nl Rl →
    Concl39 (fun x => [Lp x, M x, N x, R x]) 𝒮

/-- CITED. Lemma 3. -/
theorem lemma3 : Lemma3 := by sorry

/-- **Lemma 4**, p. 18. `MNL = X`, (3.1), (3.2) for `L`, (3.23), `max(M,N) ≤ X^{0.46+ε/2}`,
`L ≤ X^{8/35}` (3.30); then (3.9). -/
def Lemma4 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (B c1 c2 : ℝ) (M N Lp : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x, Lp x]) [Ml, Nl, Ll] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
    Cond32 Lp Ll 𝒮 →
    (∀ x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 2) ∧ Ll x ≤ x ^ (8 / 35 : ℝ)) →
    Concl39 (fun x => [M x, N x, Lp x]) 𝒮

/-- CITED. Lemma 4, a variant of Heath-Brown and Iwaniec [12], Lemma 2. -/
theorem lemma4 : Lemma4 := by sorry

/-- `χ ∈ E_q`, p. 19: `L(s,χ)` has a zero `β + iγ` with `β ≥ 1 - ε/𝓛^{4/5}`, `abs γ ≤ x`. -/
def InE (ε x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∃ hq : NeZero q, ∃ ρ : ℂ, @DirichletCharacter.LFunction q hq χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
    1 - ε / L x ^ (4 / 5 : ℝ) ≤ ρ.re ∧ |ρ.im| ≤ x

/-- `Σ_{m ≍ M, (m, P(z)) = 1} χ(m) m^{-s}`, the polynomial of Lemma 5. -/
noncomputable def roughPoly (lo hi z : ℝ) : DP where
  coef := fun _ => 1
  supp := (Finset.Ioo ⌊lo⌋₊ ⌈hi⌉₊).filter (fun m => Rough m z)

/-- **Lemma 5**, p. 20. If `min{abs t : (t,χ) ∈ 𝒮} ≫ 𝓛^A δ_χ` for all `A`, (3.33) `χ ∉ E_q`, and
`z ≥ exp(𝓛^{9/10})` (3.32), `2 ≤ M ≤ x` for large `x` as on p. 11, then `M(s,χ) = Σ_{m ≍ M, (m,P(z))=1} χ(m)m^{-s}` satisfies (3.2).
The paper refers to (3.31) for `z`; (3.32) is meant. -/
def Lemma5 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (c1 c2 : ℝ) (Ml z : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    Ev (fun x => 2 ≤ Ml x ∧ Ml x ≤ x) → (∀ x, Real.exp (L x ^ (9 / 10 : ℝ)) ≤ z x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ ∀ e ∈ c.S, ¬ InE ε x e.2) →
    (∀ A : ℝ, 0 < A → Ev fun x => ∀ c ∈ 𝒮 x, ∀ e ∈ c.S, e.2 = 1 → L x ^ A ≤ |e.1|) →
    Cond32 (fun x => roughPoly (c1 * Ml x) (c2 * Ml x) (z x)) Ml 𝒮

/-- CITED. Lemma 5, from Prachar [25] and Montgomery [21], Theorem 12.1. -/
theorem lemma5 : Lemma5 := by sorry

/-- **Lemma 6**, p. 21. For `x^ε ≤ N ≤ x`, `N ≤ N₁ ≤ 2N`, `q ≤ 𝓛^A`, `abs t ≤ x`,
`Σ_{N<n≤N₁} χ(n) n^{-1/2-it} ≪ N^{1/2-η} + N^{1/2}/(1 + abs t)`, `η = η(ε) > 0`. -/
def Lemma6 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∀ N N1 : ℝ, x ^ ε ≤ N → N ≤ x → N ≤ N1 → N1 ≤ 2 * N →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ x →
      ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
        C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|))

/-- CITED. Lemma 6, Fujii, Gallagher, Montgomery [6] and Titchmarsh [30]. -/
theorem lemma6 : Lemma6 := by sorry

/-- **Lemma 7**, p. 22: `Σ_χ ∫_{-T}^{T} abs L(1/2+it,χ)⁴ dt ≪ qT𝓛^B` for `q ≤ x`, `T ≤ x`. -/
def Lemma7 : Prop :=
  ∃ B C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ x → ∀ T : ℝ, 0 ≤ T → T ≤ x →
    ∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T, ‖DirichletCharacter.LFunction χ (half t)‖ ^ 4 ≤
      C * q * T * L x ^ B

/-- CITED. Lemma 7, Ramachandra [26]. -/
theorem lemma7 : Lemma7 := by sorry

/-- **Lemma 8**, p. 22: `L(σ+it,χ) ≪ (q(abs t + 1))^{1+ε-σ} + 1/abs (σ+it-1)`. No range of `σ` is
printed; the bound fails for fixed `σ > 1 + ε` as `abs t → ∞`, where `abs L ≥ ζ(2σ)/ζ(σ)`. It is
used for `1/2 ≤ σ ≤ 1 + 𝓛⁻¹`; we state it for `1/2 ≤ σ ≤ 1`. -/
def Lemma8 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ),
    1 / 2 ≤ σ → σ ≤ 1 → (σ : ℂ) + t * Complex.I ≠ 1 →
    ‖DirichletCharacter.LFunction χ (σ + t * Complex.I)‖ ≤
      C * (((q : ℝ) * (|t| + 1)) ^ (1 + ε - σ) + 1 / ‖(σ : ℂ) + t * Complex.I - 1‖)

/-- CITED. Lemma 8, Rademacher [28]. -/
theorem lemma8 : Lemma8 := by sorry

/-- **Lemma 9**, p. 22: for `N(s,χ) = Σ_{n ≤ N} χ(n) n^{-s}`, `2 ≤ T ≤ x`, `q ≤ x`, `N ≤ x`,
`‖N‖₄⁴ ≪ qT𝓛^B + 𝓛⁴ abs 𝒮 (q²/T² + N²/T⁴) + N² Σ_{(t,χ) ∈ 𝒮} δ_χ (1 + abs t)⁻⁴`. -/
def Lemma9 : Prop :=
  ∃ B K : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ N : ℕ, (N : ℝ) ≤ x → ∀ c : Cfg, c.WellSpaced → 1 ≤ c.q →
    (c.q : ℝ) ≤ x → 2 ≤ c.T → c.T ≤ x →
    pnorm ⟨fun _ => 1, Finset.Icc 1 N⟩ c 4 ^ 4 ≤
      K * (c.q * c.T * L x ^ B + L x ^ 4 * c.S.card * (c.q ^ 2 / c.T ^ 2 + (N : ℝ) ^ 2 / c.T ^ 4) +
        (N : ℝ) ^ 2 * ∑ e ∈ c.S, delta e.2 / (1 + |e.1|) ^ 4)

/-- CITED. Lemma 9, Titchmarsh [30], Theorem 3.19, with Lemma 7. -/
theorem lemma9 : Lemma9 := by sorry

/-- `T₀ = exp(𝓛^{1/3})`, p. 23. -/
noncomputable def T0 (x : ℝ) : ℝ := Real.exp (L x ^ (1 / 3 : ℝ))

/-- `T₁ = x^{0.45 - 2ε/3}`, p. 23. -/
noncomputable def T1 (ε x : ℝ) : ℝ := x ^ (0.45 - 2 * ε / 3)

/-- **Lemma 10**, p. 23. `LMN = x`, `M, N` with (3.1), `L(s,χ) = Σ_{l ≍ L} χ(l) l^{-s}`,
`q ≤ 𝓛^A`, `abs t ∈ [T/2, T]` for `(t, χ₀) ∈ 𝒮`, `T₀ ≤ T ≤ T₁` (3.37), and (3.38) or (3.39);
then (3.9). -/
def Lemma10 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮

/-- CITED. Lemma 10. -/
theorem lemma10 : Lemma10 := by sorry

/-! ### Section 4, sieving the interval `I`, pages 24-42 -/

/-- `y₁ = x exp(-3 log^{1/3} x)`, p. 24. -/
noncomputable def y1 (x : ℝ) : ℝ := x * Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ))

/-- (4.2), p. 24, for a family `c_k = c x k`: for all `A > 0`, all `χ mod q`, `q ≤ 𝓛^A`,
`Σ_{k ∈ I} c_k χ(k) = (Y/y₁) Σ_{k ∈ I₁} c_k χ(k) + O(Y𝓛^{-A})`, `I₁ = (x - y₁, x]`. -/
def Holds42 (ε : ℝ) (c : ℝ → ℕ → ℂ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A →
    ∀ χ : DirichletCharacter ℂ q,
      ‖∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) -
        ((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)‖ ≤
      C * Yof ε x / L x ^ A

/-- **Lemma 11**, p. 24. If `F(s,χ) = Σ_{k ~ x} c_k χ(k) k^{-s}` satisfies (3.1) and (4.1),
`∫_{T₀}^{T₁} abs F(1/2+it,χ) dt ≪ x^{1/2}𝓛^{-A}`, then (4.2). We read `k ~ x` as `x/2 < k ≤ 2x`. -/
def Lemma11 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (B : ℝ) (c : ℝ → ℕ → ℂ),
    (∀ x k, ‖c x k‖ ≤ tau k ^ B) →
    (∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A →
      ∀ χ : DirichletCharacter ℂ q,
        ∫ t in (T0 x)..(T1 ε x),
          ‖(⟨c x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) →
    Holds42 ε c

/-- CITED. Lemma 11, after Heath-Brown [10]. -/
theorem lemma11 : Lemma11 := by sorry

/-- `w = exp(log^{9/10} x)`, p. 25. -/
noncomputable def wof (x : ℝ) : ℝ := Real.exp (Real.log x ^ (9 / 10 : ℝ))

/-- `c_k = Σ_{mnl = k, m ~ M, n ~ N} a_m b_n ψ(l, z)`, (4.7), (4.17); `u ~ U` is `U < u ≤ 2U`. -/
noncomputable def conv2 (a b : ℕ → ℂ) (M N z : ℝ) (k : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
    if m * n ∣ k then a m * b n * psi (k / (m * n)) z else 0

/-- "(4.2) holds for `c_k = Σ_{mnl=k} a_m b_n ψ(l,z)`" for all `a, b` with (3.1) and all
`M, N, z` with the condition `cond`. -/
def Sieve42 (ε : ℝ) (cond : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop :=
  ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
    (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) → cond M N z →
    Holds42 ε (fun x k => conv2 (a x) (b x) (M x) (N x) (z x) k)

/-- **Lemma 12**, p. 26: `z = w`, and (4.8) `max(x^{0.45}, M) max(x^{0.225}, N) ≤ x^{0.775}` or
(4.9) `max(M,N) ≤ x^{0.46+ε/8}`. -/
def Lemma12 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Sieve42 ε fun M N z => ∀ x, z x = wof x ∧
    (max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
      max (M x) (N x) ≤ x ^ (0.46 + ε / 8))

/-- **Lemma 13**, p. 28: `x^{0.4} ≤ M ≤ x^{0.46}`, `N ≤ x^{0.46}`, `z ≪ x/MN` (4.18). -/
def Lemma13 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Sieve42 ε fun M N z =>
    Ev (fun x => x ^ (0.4 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.46 : ℝ) ∧ N x ≤ x ^ (0.46 : ℝ)) ∧
    LL z (fun x => x / (M x * N x))

/-- **Lemma 14**, p. 30: `x^{0.46} < M ≤ x^{0.5}`, `MN ≤ x^{0.775}`, `zM² ≤ x^{1.1}` (4.22). -/
def Cond422 : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop := fun M N z =>
  Ev fun x => x ^ (0.46 : ℝ) < M x ∧ M x ≤ x ^ (0.5 : ℝ) ∧ M x * N x ≤ x ^ (0.775 : ℝ) ∧
    z x * M x ^ 2 ≤ x ^ (1.1 : ℝ)

def Lemma14 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Sieve42 ε Cond422

/-- **Lemma 15**, p. 30: `z = x^{0.1}`, `M ≤ N ≤ x^{0.4}`. -/
def Lemma15 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Sieve42 ε fun M N z =>
    Ev fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)

/-- **Lemma 16**, p. 31: Lemma 14 holds under (4.23): `M ∈ [x^{α/10}, x^{(α+1)/10}]`,
`α ∈ {0,1,2,3,4}`, `x^{0.1} < z ≪ (x^{1.1}/M²)^{1/(9-2α)}`, `MN ≤ x^{0.775} z^{α-4}`. -/
def Lemma16 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ α : ℕ, α ≤ 4 → Sieve42 ε fun M N z =>
    Ev (fun x => x ^ ((α : ℝ) / 10) ≤ M x ∧ M x ≤ x ^ (((α : ℝ) + 1) / 10) ∧
      x ^ (0.1 : ℝ) < z x ∧ M x * N x ≤ x ^ (0.775 : ℝ) * z x ^ ((α : ℝ) - 4)) ∧
    LL z (fun x => (x ^ (1.1 : ℝ) / M x ^ 2) ^ (1 / (9 - 2 * (α : ℝ))))

/-- **Lemma 19**, p. 35: Lemma 14 holds if `N ≥ x^{0.18}`, `x^{0.3} ≤ M ≤ x^{0.36}`,
`MN ≤ x^{0.54}`, `MNz ≤ x^{0.775}`. -/
def Lemma19 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Sieve42 ε fun M N z =>
    Ev fun x => x ^ (0.18 : ℝ) ≤ N x ∧ x ^ (0.3 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.36 : ℝ) ∧
      M x * N x ≤ x ^ (0.54 : ℝ) ∧ M x * N x * z x ≤ x ^ (0.775 : ℝ)

/-- **Lemma 20**, p. 35: Lemma 14 holds if `N ≥ x^{0.15}`, `MNz² ≤ x^{0.82}`,
`x^{0.3} ≤ M ≤ x^{0.36}`, `MN ≤ x^{0.54}`. -/
def Lemma20 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Sieve42 ε fun M N z =>
    Ev fun x => x ^ (0.15 : ℝ) ≤ N x ∧ M x * N x * z x ^ 2 ≤ x ^ (0.82 : ℝ) ∧
      x ^ (0.3 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.36 : ℝ) ∧ M x * N x ≤ x ^ (0.54 : ℝ)

/-- CITED. Lemmas 12 to 16, 19, 20. -/
theorem lemma12 : Lemma12 := by sorry
theorem lemma13 : Lemma13 := by sorry
theorem lemma14 : Lemma14 := by sorry
theorem lemma15 : Lemma15 := by sorry
theorem lemma16 : Lemma16 := by sorry
theorem lemma19 : Lemma19 := by sorry
theorem lemma20 : Lemma20 := by sorry

/-- `c_k = Σ_{p₁ ~ M, p₂ ~ N, p₁p₂n₃ = k} ψ(n₃, p₂)`, Lemma 22, p. 36. The paper prints `p₂ ~ M`;
the conditions on `N` and the proof, `p₁p₂ = (p₁ · p₁p₂²)^{1/2}`, need `p₂ ~ N`. -/
noncomputable def conv3 (M N : ℝ) (k : ℕ) : ℂ :=
  ∑ p1 ∈ (Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊).filter Nat.Prime,
    ∑ p2 ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter Nat.Prime,
      if p1 * p2 ∣ k then psi (k / (p1 * p2)) p2 else 0

/-- "(4.2) holds for `conv3 M N`" for every `M, N` with `cond`. -/
def Prime42 (ε : ℝ) (cond : (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop :=
  ∀ M N : ℝ → ℝ, cond M N → Holds42 ε (fun x k => conv3 (M x) (N x) k)

/-- **Lemma 22**, p. 36, (4.26) or (4.27). -/
def Lemma22 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Prime42 ε fun M N =>
    Ev fun x => x ^ (0.23 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.3 : ℝ) ∧ x ^ (0.46 : ℝ) ≤ M x * N x ∧
      ((M x * N x ^ 2 ≤ x ^ (0.7 : ℝ) ∧ x ^ (0.18 : ℝ) ≤ N x) ∨ M x * N x ^ 3 ≤ x ^ (0.82 : ℝ))

/-- **Lemma 24**, p. 38: Lemma 22 under (4.30) `M ≥ x^{0.3}`, `N ≥ x^{0.3}`, `MN ≤ x^{0.64}`,
or (4.31) `x^{0.36} ≤ M ≤ x^{0.4}`, `N ≥ x^{0.3}`. -/
def Lemma24 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Prime42 ε fun M N =>
    Ev fun x => (x ^ (0.3 : ℝ) ≤ M x ∧ x ^ (0.3 : ℝ) ≤ N x ∧ M x * N x ≤ x ^ (0.64 : ℝ)) ∨
      (x ^ (0.36 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.4 : ℝ) ∧ x ^ (0.3 : ℝ) ≤ N x)

/-- **Lemma 26**, p. 40: Lemma 22 with `x^{0.46} ≤ M ≤ x^{0.5}`, `N ≥ x^{0.15}`, `MN² ≤ x^{0.82}`. -/
def Lemma26 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → Prime42 ε fun M N =>
    Ev fun x => x ^ (0.46 : ℝ) ≤ M x ∧ M x ≤ x ^ (0.5 : ℝ) ∧ x ^ (0.15 : ℝ) ≤ N x ∧
      M x * N x ^ 2 ≤ x ^ (0.82 : ℝ)

/-- CITED. Lemmas 22, 24, 26. -/
theorem lemma22 : Lemma22 := by sorry
theorem lemma24 : Lemma24 := by sorry
theorem lemma26 : Lemma26 := by sorry

/-! ### Section 5, sieving the interval `J`, pages 43-53 -/

/-- `T₂ = Y/(qQ)`, Lemma 29. -/
noncomputable def T2 (ε x : ℝ) (q : ℕ) : ℝ := Yof ε x / (q * Qof ε x)

/-- (5.1) and (5.2), p. 43, for `G(s,χ)` given as a function of `x, χ, s`, uniformly in
`1 ≤ q ≤ Q`; `F = E_q^c \ {χ₀}`. -/
def Holds512 (ε : ℝ) (G : ℝ → (q : ℕ) → DirichletCharacter ℂ q → ℂ → ℂ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], q ≤ Qof ε x →
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ¬ InE ε x χ ∧ χ ≠ 1),
      ∫ t in (-Yof ε x)..(Yof ε x), ‖G x q χ (half t)‖ ^ 2 / (T2 ε x q ^ 2 + t ^ 2) ≤
        C * Yof ε x / T2 ε x q ^ 2 / L x ^ A) ∧
    (∫ t in (Set.Icc (-Yof ε x) (Yof ε x) \ Set.Icc (-T0 x) (T0 x)),
      ‖G x q (1 : DirichletCharacter ℂ q) (half t)‖ ^ 2 / (T2 ε x q ^ 2 + t ^ 2) ≤
        C * Yof ε x / T2 ε x q ^ 2 / L x ^ A)

/-- `G(s,χ) = Σ_{c₁Y < m < c₂Y} b_m χ(m) m^{-s}`. -/
noncomputable def Gof (ε c1 c2 : ℝ) (b : ℝ → ℕ → ℂ) (x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (⟨b x, Finset.Ioo ⌊c1 * Yof ε x⌋₊ ⌈c2 * Yof ε x⌉₊⟩ : DP).eval χ s

/-- `W(y,z) = (1/2πi) ∫_{1/2-iT₀}^{1/2+iT₀} G(s,χ₀)((y+yz)^s - y^s)/s ds`, p. 43. -/
noncomputable def Wfun (ε c1 c2 : ℝ) (b : ℝ → ℕ → ℂ) (x y z : ℝ) (q : ℕ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T0 x)..(T0 x),
    Gof ε c1 c2 b x (1 : DirichletCharacter ℂ q) (half t) *
      (((y + y * z : ℝ) : ℂ) ^ (half t) - (y : ℂ) ^ (half t)) / half t

/-- **Lemma 29**, p. 43. `G` of length `Y` with (3.1), (5.1), (5.2) give
`‖Σ_{m ∈ J_y} b(m)χ(m) - δ_χ W(y,z)‖²_{E_q^c} ≪ (qQ)²Y𝓛^{-A}`. The printed `‖·‖_E` integrates
over `[Y/2, 3Y/2]` while (1.9) and the proof on p. 44 use `[Y/2, 3Y]`; we state `[Y/2, 3Y/2]`. -/
def Lemma29 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (B c1 c2 : ℝ) (b : ℝ → ℕ → ℂ),
    0 < c1 → c1 < c2 → (∀ x n, ‖b x n‖ ≤ tau n ^ B) → Holds512 ε (fun x q χ s => Gof ε c1 c2 b x (q := q) χ s) →
    ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], q ≤ Qof ε x →
      ∀ z : ℝ, q * Qof ε x / (6 * Yof ε x) ≤ z → z ≤ 6 * q * Qof ε x / Yof ε x →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ¬ InE ε x χ),
        ∫ y in (Yof ε x / 2)..(3 * Yof ε x / 2),
          ‖∑ m ∈ (Jy y z).filter (fun m : ℕ => c1 * Yof ε x < m ∧ (m : ℝ) < c2 * Yof ε x),
              b x m * χ (m : ZMod q) - (delta χ : ℂ) * Wfun ε c1 c2 b x y z q‖ ^ 2 ≤
        C * ((q : ℝ) * Qof ε x) ^ 2 * Yof ε x / L x ^ A

/-- CITED. Lemma 29. -/
theorem lemma29 : Lemma29 := by sorry

/-- `b_m = Σ_{n ~ N, nl = m} a_n ψ(l, z)`. -/
noncomputable def conv1 (a : ℕ → ℂ) (N z : ℝ) (m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, if n ∣ m then a n * psi (m / n) z else 0

/-- **Lemma 30**, p. 44: `b_m = Σ_{n~N, nl=m} a_n ψ(l,w)`, (3.1), `N ≪ Y^{1/2 + θ₂/4 - ε}` (5.5),
give (5.1) and (5.2). -/
def Lemma30 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (B c1 c2 : ℝ) (a : ℝ → ℕ → ℂ) (N : ℝ → ℝ),
    0 < c1 → c1 < c2 → (∀ x n, ‖a x n‖ ≤ tau n ^ B) →
    LL N (fun x => Yof ε x ^ (1 / 2 + theta2 / 4 - ε)) →
    Holds512 ε (fun x q χ s => Gof ε c1 c2 (fun x m => conv1 (a x) (N x) (wof x) m) x (q := q) χ s)

/-- CITED. Lemma 30. -/
theorem lemma30 : Lemma30 := by sorry

/-- **Lemma 32**, p. 46, with `X = Y`: `φ, j` as in Lemma 31, `qTY^ε = Y^{1-φ}`, `Y = MN`,
`Y^ε ≤ N ≤ Y^{φ + (1-φ)/(2j-1) - ε}`, (3.1) for `M, N`, (3.2) for `M`; then `‖MN‖₂² ≪ Y𝓛^{-A}`. -/
def Lemma32 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (φ : ℝ) (j : ℕ), 4 ≤ j → 1 / (2 * j + 2) < φ → φ ≤ 1 / (2 * j) →
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x = Yof ε x ∧ Yof ε x ^ ε ≤ Nl x ∧
      Nl x ≤ Yof ε x ^ (φ + (1 - φ) / (2 * j - 1) - ε)) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) * c.T * Yof ε x ^ ε = Yof ε x ^ (1 - φ)) →
    Cond32 M Ml 𝒮 →
    ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ c ∈ 𝒮 x,
      (∑ e ∈ c.S, ‖(M x).eval e.2 (half e.1) * (N x).eval e.2 (half e.1)‖ ^ 2) ≤
        C * Yof ε x / L x ^ A

/-- CITED. Lemma 32. -/
theorem lemma32 : Lemma32 := by sorry

/-- `c₁ = (1 + 7θ₂)/15 - ε`, p. 47. -/
noncomputable def cc1 (ε : ℝ) : ℝ := (1 + 7 * theta2) / 15 - ε
/-- `c₂ = (36θ₂ - 2)/11 - ε`, p. 47. -/
noncomputable def cc2 (ε : ℝ) : ℝ := (36 * theta2 - 2) / 11 - ε
/-- `c₃ = (1 + 22θ₂)/60 - 2ε`, p. 50. -/
noncomputable def cc3 (ε : ℝ) : ℝ := (1 + 22 * theta2) / 60 - 2 * ε
/-- `c₄ = 1/4 + θ₂/8 - ε`, p. 53. -/
noncomputable def cc4 (ε : ℝ) : ℝ := 1 / 4 + theta2 / 8 - ε

/-- The region of Lemma 33, p. 48: (5.13), the triangle `R`, the parallelograms `P₁, P₂`. -/
def Region33 (ε β1 β2 : ℝ) : Prop :=
  0 ≤ β2 ∧ β2 ≤ β1 ∧ β1 ≤ 1 / 2 ∧
  ((ε ≤ β2 ∧ β2 ≤ cc1 ε) ∨
   (cc1 ε < β2 ∧ 2 * β2 - theta2 + ε ≤ β1 ∧ β1 ≤ cc2 ε) ∨
   (|4 * β1 + 3 * β2 - 2| ≤ theta2 - ε ∧ cc1 ε ≤ β2 ∧ β2 ≤ cc2 ε) ∨
   (|4 * β1 + β2 - 2| ≤ theta2 - ε ∧ cc1 ε ≤ β2 ∧ β2 ≤ cc2 ε))

/-- (3.2) on the `(t, χ)` of (5.1), (5.2): `χ ∈ F` and `abs t ≤ Y`, or `χ = χ₀`, `T₀ ≤ abs t ≤ Y`. -/
def Cond32Sec5 (ε : ℝ) (P : ℝ → DP) (F : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], q ≤ Qof ε x →
    ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ Yof ε x →
      ((¬ InE ε x χ ∧ χ ≠ 1) ∨ (χ = 1 ∧ T0 x ≤ |t|)) →
      ‖(P x).eval χ (half t)‖ ≤ C * F x ^ (1 / 2 : ℝ) / L x ^ A

/-- **Lemma 33**, p. 48. `LMN = Y`, `M = Y^{β₁}`, `N = Y^{β₂}`, `0 ≤ β₂ ≤ β₁ ≤ 1/2`, (3.1) for all,
(3.2) for `M, N`, `(β₁,β₂)` in the region; then (5.1), (5.2) with `G = LMN`. The paper writes
`M = X^{β₁}`, `N = X^{β₂}`; with `LMN = Y` we read `Y`. -/
def Lemma33 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ β1 β2 : ℝ, Region33 ε β1 β2 →
  ∀ (B c1 c2 : ℝ) (Lp M N : ℝ → DP), 0 < c1 → c1 < c2 →
    FamOK (fun x => [Lp x, M x, N x]) [fun x => Yof ε x ^ (1 - β1 - β2),
      fun x => Yof ε x ^ β1, fun x => Yof ε x ^ β2] B c1 c2 →
    Cond32Sec5 ε M (fun x => Yof ε x ^ β1) → Cond32Sec5 ε N (fun x => Yof ε x ^ β2) →
    Holds512 ε (fun x _ χ s => (Lp x).eval χ s * (M x).eval χ s * (N x).eval χ s)

/-- CITED. Lemma 33. -/
theorem lemma33 : Lemma33 := by sorry

/-- **Lemma 34**, p. 49: `b_m = Σ_{nl = m, n ≤ Y^{1/2+θ₂/4-2ε}} a_n ψ(l, Y^{c₁})` with (3.1)
gives (5.1), (5.2). -/
def Lemma34 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (B c1 c2 : ℝ) (a : ℝ → ℕ → ℂ),
    0 < c1 → c1 < c2 → (∀ x n, ‖a x n‖ ≤ tau n ^ B) →
    Holds512 ε (fun x q χ s => Gof ε c1 c2 (fun x m =>
      ∑ n ∈ Finset.Icc 1 ⌊Yof ε x ^ (1 / 2 + theta2 / 4 - 2 * ε)⌋₊,
        if n ∣ m then a x n * psi (m / n) (Yof ε x ^ cc1 ε) else 0) x (q := q) χ s)

/-- CITED. Lemma 34. -/
theorem lemma34 : Lemma34 := by sorry

/-- The quadrilaterals `Q₁`, `Q₂` of Lemma 35, p. 50. -/
def Quad35 (ε β1 β2 : ℝ) : Prop :=
  (cc1 ε ≤ β2 ∧ β2 ≤ β1 ∧ 4 * β1 + 7 * β2 ≤ 2 + theta2 - ε ∧
    1 / 2 - (theta2 + 3 * cc1 ε) / 4 + ε ≤ β1 + β2) ∨
  (cc1 ε ≤ β2 ∧ β2 ≤ min β1 (cc2 ε) ∧ 4 * β1 + 5 * β2 ≤ 2 + cc1 ε ∧
    1 / 2 - (theta2 + cc1 ε) / 4 + ε ≤ β1 + β2)

/-- **Lemma 35**, p. 50: `b_m = Σ_{p₁p₂n₃ = m} ψ(n₃,p₂)`, `p₁ ~ Y^{β₁}`, `p₂ ~ Y^{β₂}`,
`(β₁,β₂) ∈ Q₁ ∪ Q₂`, gives (5.1), (5.2). The paper writes `x^{β}`; Section 5 measures in `Y`. -/
def Lemma35 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ β1 β2 : ℝ, Quad35 ε β1 β2 →
  ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 →
    Holds512 ε (fun x q χ s =>
      Gof ε c1 c2 (fun x m => conv3 (Yof ε x ^ β1) (Yof ε x ^ β2) m) x (q := q) χ s)

/-- CITED. Lemma 35. -/
theorem lemma35 : Lemma35 := by sorry

/-! ### PROVED: exponent arithmetic, Section 1 -/

/-- Remark, p. 1: `7/81 = 0.08641...`, `11/160 = 0.06875`. -/
theorem remark_values : (0.08641 : ℝ) < 7 / 81 ∧ (7 / 81 : ℝ) < 0.08642 ∧
    (11 / 160 : ℝ) = 0.06875 := by norm_num

theorem theta2_eq : theta2 = 2 * lam0 := by unfold theta2 lam0; ring

theorem theta2_val : theta2 = 1 / 8 - 1 / 50000 := by unfold theta2; norm_num

/-- `θ₁θ₂` at `ε = 0` is `11/160 - 11/10⁶`. -/
theorem theta12_zero : theta1 0 * theta2 = 11 / 160 - 11 / 10 ^ 6 := by
  rw [theta2_val]; unfold theta1; norm_num

/-- `θ₁θ₂ ≤ 11/160` for `0 ≤ ε ≤ 1/20000`, so (1.2) gives Theorem 1, p. 2. -/
theorem theta12_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 20000) : theta1 ε * theta2 ≤ 11 / 160 := by
  rw [theta2_val]; unfold theta1; nlinarith

theorem theta12_pos {ε : ℝ} (h0 : 0 ≤ ε) : 0 < theta1 ε * theta2 := by
  rw [theta2_val]; unfold theta1; nlinarith

/-- `θ₁θ₂ < 7/81`, Li's exponent, for the same `ε`. -/
theorem theta12_lt_li {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 20000) : theta1 ε * theta2 < 7 / 81 := by
  have := theta12_le h0 h1; linarith

/-- Perelli and Pintz [23] need `θ₁ ≥ 7/12 + ε`, `θ₂ ≥ 1/3 + ε`; both choices here are smaller. -/
theorem below_PP {ε : ℝ} (h1 : ε < 1 / 30) : theta1 ε < 7 / 12 ∧ theta2 < 1 / 3 := by
  rw [theta2_val]; unfold theta1; constructor <;> linarith

/-- (1.5) and the final constants: `u₀ > 0.99`, `u₁ < 1.01`, `v₀ > 0.05`, `v₁ < 2.2`, with
`u₀ ≤ u₁`, `v₀ ≤ v₁`, give `u₀v₁ + u₁v₀ - u₁v₁ > 0`, p. 2. -/
theorem uv_pos {u0 u1 v0 v1 : ℝ} (hu0 : 0.99 < u0) (hu1 : u1 < 1.01) (hv0 : 0.05 < v0)
    (hv1 : v1 < 2.2) (hu : u0 ≤ u1) (hv : v0 ≤ v1) : 0 < u0 * v1 + u1 * v0 - u1 * v1 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u0 - 0.99) (by linarith : (0 : ℝ) ≤ v1),
    mul_nonneg (sub_nonneg.mpr hv) (by linarith : (0 : ℝ) ≤ 1.01 - u1)]

/-- p. 41: the discarded integrals `< 0.0003, 0.002, 0.002, 0.0003` and `< 0.0001` give
`u₀ > 0.9953`. -/
theorem u0_bound {i2 i3 i4 iG i6 : ℝ} (h2 : i2 < 0.0003) (h3 : i3 < 0.002) (h4 : i4 < 0.002)
    (hG : iG < 0.0003) (h6 : i6 < 0.0001) : 0.9953 < 1 - (i2 + i3 + i4 + iG + i6) := by
  linarith

/-- The printed constants satisfy (1.5): `0.9953 > 0.99`, `1.0001 < 1.01`. -/
theorem constants_15 : (0.99 : ℝ) < 0.9953 ∧ (1.0001 : ℝ) < 1.01 := by norm_num

/-- The margin of p. 2 with the final constants: `u₀ > 0.9953`, `u₁ < 1.0001`, `v₀ > 0.05`,
`v₁ < 2.2`. -/
theorem uv_pos_final {u0 u1 v0 v1 : ℝ} (hu0 : 0.9953 < u0) (hu1 : u1 < 1.0001) (hv0 : 0.05 < v0)
    (hv1 : v1 < 2.2) (hu : u0 ≤ u1) (hv : v0 ≤ v1) : 0 < u0 * v1 + u1 * v0 - u1 * v1 :=
  uv_pos (by linarith) (by linarith) hv0 hv1 hu hv

/-- p. 5: `0.0335 > 0.535/16`, and also `> 0.535 λ₀`. -/
theorem mu_gt : 0.535 / 16 < mu ∧ 0.535 * lam0 < mu := by
  unfold mu lam0; norm_num

/-- p. 6: the singular series as printed has `∏_p (1 - 1/(p-1)²)` over all `p`; its factor at
`p = 2` is `0`, so the product must run over `p > 2`, as in `SS`. -/
theorem printed_SS_factor_two : (1 : ℝ) - 1 / ((2 : ℝ) - 1) ^ 2 = 0 := by norm_num

/-! ### PROVED: exponent arithmetic, Section 3 -/

/-- `f(σ) = min(1 - 2σ, 4 - 6σ)`, p. 13. -/
noncomputable def fsig (σ : ℝ) : ℝ := min (1 - 2 * σ) (4 - 6 * σ)

theorem fsig_three_quarters : fsig (3 / 4) = -1 / 2 := by unfold fsig; norm_num

/-- (3.13), p. 13: `αf(σ) + σ - 1/2 ≤ αf(3/4) + 3/4 - 1/2 = (1 - 2α)/4` for `α ∈ [1/6, 1/2]`. -/
theorem ineq313 {α σ : ℝ} (h1 : 1 / 6 ≤ α) (h2 : α ≤ 1 / 2) :
    α * fsig σ + σ - 1 / 2 ≤ (1 - 2 * α) / 4 := by
  unfold fsig
  rcases le_total σ (3 / 4) with h | h
  · have : min (1 - 2 * σ) (4 - 6 * σ) = 1 - 2 * σ := min_eq_left (by linarith)
    rw [this]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * α) (by linarith : (0 : ℝ) ≤ 3 / 4 - σ)]
  · have : min (1 - 2 * σ) (4 - 6 * σ) = 4 - 6 * σ := min_eq_right (by linarith)
    rw [this]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 6 * α - 1) (by linarith : (0 : ℝ) ≤ σ - 3 / 4)]

theorem ineq313_value (α : ℝ) : α * fsig (3 / 4) + 3 / 4 - 1 / 2 = (1 - 2 * α) / 4 := by
  rw [fsig_three_quarters]; ring

/-- `γ(θ) > 0` only for `θ > 37/72`, the last term of (3.8). -/
theorem gam_pos_iff {θ : ℝ} (h : 1 / 2 < θ) : 0 < gam θ ↔ 37 / 72 < θ := by
  unfold gam
  constructor
  · intro h0
    have := min_le_right (4 * θ - 2) (min ((20 * θ - 9) / 11) ((72 * θ - 37) / 11))
    have := min_le_right ((20 * θ - 9) / 11) ((72 * θ - 37) / 11)
    linarith
  · intro h0
    apply lt_min (by linarith) (lt_min (by linarith) (by linarith))

/-- Section 5 uses Theorem 4 with `θ = 1/2 + θ₂/4`; for `θ₂ ≤ 1/7`,
`γ(1/2 + θ₂/4) = (18θ₂ - 1)/11`, p. 48. -/
theorem gam_sec5 {t : ℝ} (h : t ≤ 1 / 7) : gam (1 / 2 + t / 4) = (18 * t - 1) / 11 := by
  unfold gam
  have e1 : (72 * (1 / 2 + t / 4) - 37) / 11 = (18 * t - 1) / 11 := by ring
  rw [min_eq_right (by linarith : (72 * (1 / 2 + t / 4) - 37) / 11 ≤ (20 * (1 / 2 + t / 4) - 9) / 11),
    e1, min_eq_right (by linarith)]

/-- Hence (3.7) in Lemma 33 reads `β₁ < c₂ + ε`, `c₂ = (36θ₂ - 2)/11 - ε`, p. 48. -/
theorem c2_from_gam {ε : ℝ} : 2 * gam (1 / 2 + theta2 / 4) = cc2 ε + ε := by
  rw [gam_sec5 (by rw [theta2_val]; norm_num)]; unfold cc2; ring

/-- In Lemma 33, `θ = 1/2 + θ₂/4` lies in `(1/2 + ε, 7/12)` for small `ε`. -/
theorem theta_sec5_range {ε : ℝ} (h : ε < 1 / 40) :
    1 / 2 + ε < 1 / 2 + theta2 / 4 ∧ 1 / 2 + theta2 / 4 < 7 / 12 := by
  rw [theta2_val]; constructor <;> linarith

/-- `α₁, α₂` for the triangle `R`, p. 48: with `N²L, LM, M` and `X = Y²`,
`α₁ = (1 + β₂ - β₁)/2`, `α₂ = (1 - β₂)/2`, `α₁ - α₂ = (2β₂ - β₁)/2`, `1 - α₁ - α₂ = β₁/2`. -/
theorem alphas_R (β1 β2 : ℝ) :
    (2 * β2 + (1 - β1 - β2)) / 2 = (1 + β2 - β1) / 2 ∧ ((1 - β1 - β2) + β1) / 2 = (1 - β2) / 2 ∧
    (2 * β2 + (1 - β1 - β2)) / 2 - ((1 - β1 - β2) + β1) / 2 = (2 * β2 - β1) / 2 ∧
    1 - (2 * β2 + (1 - β1 - β2)) / 2 - ((1 - β1 - β2) + β1) / 2 = β1 / 2 := by
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- `α₁, α₂` for `P₁`, p. 48: with `M²N, L², N`, `α₁ = (2β₁+β₂)/2`, `α₂ = 1 - β₁ - β₂`,
`α₁ - α₂ = (4β₁ + 3β₂ - 2)/2`, `1 - α₁ - α₂ = β₂/2`. -/
theorem alphas_P1 (β1 β2 : ℝ) :
    (2 * β1 + β2) / 2 - (1 - β1 - β2) = (4 * β1 + 3 * β2 - 2) / 2 ∧
    1 - (2 * β1 + β2) / 2 - (1 - β1 - β2) = β2 / 2 := by
  refine ⟨by ring, by ring⟩

/-- `qT₂ ≍ Y^{1 - θ₂/2} = X^{1-θ}` with `X = Y²`, `θ = 1/2 + θ₂/4`, p. 48. -/
theorem qT2_exponent (t : ℝ) : 2 * (1 - (1 / 2 + t / 4)) = 1 - t / 2 := by ring

/-- In the triangle `R`: `2c₁ ≥ c₂ - θ₂ + ε` for `0 < ε ≤ 1/20`, p. 48. -/
theorem R_check {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 20) : cc2 ε - theta2 + ε ≤ 2 * cc1 ε := by
  unfold cc1 cc2; rw [theta2_val]; linarith

/-- The Hölder exponents of Lemma 3: `Σ 1/βⱼ = 1/2` in (i) with `β₂ = 8`, (ii), (iv)(a). -/
theorem holder_lemma3 :
    (1 / 8 + 1 / 8 + 1 / 4 : ℝ) = 1 / 2 ∧ (1 / 4 + 1 / 12 + 1 / 6 : ℝ) = 1 / 2 ∧
    (1 / 10 + 1 / 4 + 1 / (20 / 3) : ℝ) = 1 / 2 ∧ (1 / 2 + 1 / 6 + 1 / 4 + 1 / 12 : ℝ) = 1 := by
  norm_num

/-- p. 16 prints `4β₂ = 8` in case (i); then `β₂ = 2` and `1/8 + 1/2 + 1/4 ≠ 1/2`, so the
intended value is `β₂ = 8`, the `β` of the Lemma 2 application there. -/
theorem printed_beta2_misprint : ∀ b2 : ℝ, 4 * b2 = 8 → 1 / 8 + 1 / b2 + 1 / 4 ≠ (1 / 2 : ℝ) := by
  intro b2 h; have : b2 = 2 := by linarith
  subst this; norm_num

/-- The conditions (3.18), (3.19) of Lemma 2. -/
def L2cond (ε γ β : ℝ) (h : ℕ) : Prop :=
  4 * γ - 2 * h + ε ≤ β ∧ 2 * h - ε < β ∧ β < 6 * h - ε

/-- The four applications of Lemma 2 in Lemma 3 meet (3.18), (3.19) for `0 < ε ≤ 1/10`:
(i) `β = 8, γ = 7/2 - ε, h = 3`; (ii) `β = 12, γ = 9/2 - ε, h = 3`; (iii) `β = 6, γ = 5/2 - ε,
h = 2`; (iv)(a) `β = 20/3, γ = 28/9, h = 3`. -/
theorem lemma2_apps {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 10) :
    L2cond ε (7 / 2 - ε) 8 3 ∧ L2cond ε (9 / 2 - ε) 12 3 ∧ L2cond ε (5 / 2 - ε) 6 2 ∧
    L2cond ε (28 / 9) (20 / 3) 3 := by
  unfold L2cond; push_cast
  refine ⟨⟨by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith⟩,
    ⟨by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith⟩⟩

/-- `γ = 0.45/(9/35 - 0.1125) = 28/9`, Lemma 3 (iv)(a), p. 17. -/
theorem gamma_iva : (0.45 : ℝ) / (9 / 35 - 0.1125) = 28 / 9 := by norm_num

/-- The `γ` of (i), (ii), (iii) match the thresholds: `(9/70)(7/2) = 0.1(9/2) = 0.18(5/2) = 0.45`. -/
theorem gamma_thresholds :
    (9 / 70 : ℝ) * (7 / 2) = 0.45 ∧ (0.1 : ℝ) * (9 / 2) = 0.45 ∧ (0.18 : ℝ) * (5 / 2) = 0.45 := by
  norm_num

/-- (3.27): `N ≫ (qT)^{2/β₁}` with `qT = X^{0.45}` gives the printed thresholds,
`0.9/8 = 0.1125`, `0.9/4 = 0.225`, `0.9/6 = 0.15`. -/
theorem thresholds_327 :
    (0.45 : ℝ) * 2 / 8 = 0.1125 ∧ (0.45 : ℝ) * 2 / 4 = 0.225 ∧ (0.45 : ℝ) * 2 / 6 = 0.15 := by
  norm_num

/-- In Lemma 3 (iv)(b), `S(α,α) = 2α/(1.8 - 6α) + (c - 2α)/(1.8 - 4(c - 2α))`; at `α = 2c/7`
both denominators equal `1.8 - 12c/7` and `S = c/(1.8 - 12c/7)`, p. 17. -/
theorem S_at_min {c : ℝ} (hD : 1.8 - 12 * c / 7 ≠ 0) :
    2 * (2 * c / 7) / (1.8 - 6 * (2 * c / 7)) +
      (c - 2 * (2 * c / 7)) / (1.8 - 4 * (c - 2 * (2 * c / 7))) = c / (1.8 - 12 * c / 7) := by
  have e1 : (1.8 : ℝ) - 6 * (2 * c / 7) = 1.8 - 12 * c / 7 := by ring
  have e2 : (1.8 : ℝ) - 4 * (c - 2 * (2 * c / 7)) = 1.8 - 12 * c / 7 := by ring
  rw [e1, e2, ← add_div]; congr 1; ring

/-- The minimum is `1/2` at `c = 63/130`, p. 17. -/
theorem S_min_value : (63 / 130 : ℝ) / (1.8 - 12 * (63 / 130) / 7) = 1 / 2 := by norm_num

/-- (3.29), p. 17, in full: for `α₁ ∈ (0, 0.45)`, `α₂, α₃ ∈ (0, 0.3)`,
`S = α₁/(1.8 - 4α₁) + α₂/(1.8 - 6α₂) + α₃/(1.8 - 6α₃) ≥ c/(1.8 - 12c/7)`, `c = α₁ + α₂ + α₃`,
not only on `α₂ = α₃`. -/
theorem S_core {b p r : ℝ} (hb : 0 < b) (hp : 0 < p) (hr : 0 < r) :
    ((1.8 - b) / 4 + (1.8 - p) / 6 + (1.8 - r) / 6) / ((6 * b + 4 * p + 4 * r) / 14) ≤
      (1.8 - b) / 4 / b + (1.8 - p) / 6 / p + (1.8 - r) / 6 / r := by
  have hW : 0 < 6 * b + 4 * p + 4 * r := by linarith
  rw [div_le_iff₀ (by positivity)]
  have e : ((1.8 - b) / 4 / b + (1.8 - p) / 6 / p + (1.8 - r) / 6 / r) *
      ((6 * b + 4 * p + 4 * r) / 14) - ((1.8 - b) / 4 + (1.8 - p) / 6 + (1.8 - r) / 6) =
      (1.8 * (b - p) ^ 2 * r + 1.8 * (b - r) ^ 2 * p + 1.2 * (p - r) ^ 2 * b) / (b * p * r) / 14 := by
    field_simp; ring
  have : 0 ≤ (1.8 * (b - p) ^ 2 * r + 1.8 * (b - r) ^ 2 * p + 1.2 * (p - r) ^ 2 * b) /
      (b * p * r) / 14 := by positivity
  linarith

theorem S_lower {a1 a2 a3 : ℝ} (h1 : 0 < a1) (h1' : a1 < 0.45) (h2 : 0 < a2) (h2' : a2 < 0.3)
    (h3 : 0 < a3) (h3' : a3 < 0.3) :
    (a1 + a2 + a3) / (1.8 - 12 * (a1 + a2 + a3) / 7) ≤
      a1 / (1.8 - 4 * a1) + a2 / (1.8 - 6 * a2) + a3 / (1.8 - 6 * a3) := by
  have key := S_core (b := 1.8 - 4 * a1) (p := 1.8 - 6 * a2) (r := 1.8 - 6 * a3)
    (by linarith) (by linarith) (by linarith)
  have e1 : (a1 + a2 + a3) / (1.8 - 12 * (a1 + a2 + a3) / 7) =
      ((1.8 - (1.8 - 4 * a1)) / 4 + (1.8 - (1.8 - 6 * a2)) / 6 + (1.8 - (1.8 - 6 * a3)) / 6) /
        ((6 * (1.8 - 4 * a1) + 4 * (1.8 - 6 * a2) + 4 * (1.8 - 6 * a3)) / 14) := by ring
  have e2 : a1 / (1.8 - 4 * a1) + a2 / (1.8 - 6 * a2) + a3 / (1.8 - 6 * a3) =
      (1.8 - (1.8 - 4 * a1)) / 4 / (1.8 - 4 * a1) + (1.8 - (1.8 - 6 * a2)) / 6 / (1.8 - 6 * a2) +
        (1.8 - (1.8 - 6 * a3)) / 6 / (1.8 - 6 * a3) := by ring
  rw [e1, e2]; exact key

/-- Hence `S ≥ 1/2` once `c ≥ 63/130`, the condition `LNR ≫ X^{63/130 + Bε}` of Lemma 3 (iv). -/
theorem S_ge_half {a1 a2 a3 : ℝ} (h1 : 0 < a1) (h1' : a1 < 0.45) (h2 : 0 < a2) (h2' : a2 < 0.3)
    (h3 : 0 < a3) (h3' : a3 < 0.3) (hc : 63 / 130 ≤ a1 + a2 + a3) :
    1 / 2 ≤ a1 / (1.8 - 4 * a1) + a2 / (1.8 - 6 * a2) + a3 / (1.8 - 6 * a3) := by
  refine le_trans ?_ (S_lower h1 h1' h2 h2' h3 h3')
  have hD : 0 < 1.8 - 12 * (a1 + a2 + a3) / 7 := by linarith
  rw [le_div_iff₀ hD]; linarith

/-- The ranges of case (iv)(b), `0.18 < α₁ < 0.225`, `0.1 < α₂, α₃ < 0.15`, lie inside those of
`S_lower`. -/
theorem ivb_ranges {a1 a2 a3 : ℝ} (h1 : 0.18 < a1) (h1' : a1 < 0.225) (h2 : 0.1 < a2)
    (h2' : a2 < 0.15) (h3 : 0.1 < a3) (h3' : a3 < 0.15) :
    0 < a1 ∧ a1 < 0.45 ∧ 0 < a2 ∧ a2 < 0.3 ∧ 0 < a3 ∧ a3 < 0.3 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Lemma 4, p. 18: `X^{1/16}L^{7/16}` with `L ≤ X^{8/35}` is `X^{13/80}`;
`(3/4)(0.45) + 13/80 = 1/2`; `1/16 - (1/24)(3/10) = 1/20` and `0.45 + 1/20 = 1/2`. -/
theorem lemma4_exponents :
    (1 / 16 + 7 / 16 * (8 / 35) : ℝ) = 13 / 80 ∧ (3 / 4 * 0.45 + 13 / 80 : ℝ) = 1 / 2 ∧
    (1 / 16 - 1 / 24 * (3 / 10) : ℝ) = 1 / 20 ∧ (0.45 + 1 / 20 : ℝ) = 1 / 2 := by norm_num

/-- Lemma 10, p. 24: `L^{3A}qT < x^{16/35}` needs `0.45 < 16/35`. -/
theorem lemma10_exponent : (0.45 : ℝ) < 16 / 35 := by norm_num

/-! ### PROVED: exponent arithmetic, Section 4 -/

/-- Lemma 13, p. 29: `Np/M < x^{0.9+0.375}/M³ ≤ x^{0.1}` for `M ≥ x^{0.4}`; `p³M² ≤ x^{2.7}M^{-4}`
with `x^{2.7 - 1.6} = x^{1.1}`. -/
theorem lemma13_exponents : (0.9 + 0.375 - 3 * 0.4 : ℝ) < 0.1 ∧ (3 * 0.9 - 4 * 0.4 : ℝ) = 1.1 := by
  norm_num

/-- Lemma 14, p. 30: `x^{1.1}/M² < x^{0.18}` for `M > x^{0.46}`. -/
theorem lemma14_exponent : (1.1 - 2 * 0.46 : ℝ) = 0.18 := by norm_num

/-- Lemma 17 (c), p. 34: `n₁n₂n₃ ≤ x^{0.775 × 0.6} < x^{0.5}`, `n₄n₅ < x^{0.775 - 0.3} < x^{0.5}`. -/
theorem lemma17_exponents : (0.775 * 0.6 : ℝ) < 0.5 ∧ (0.775 - 0.3 : ℝ) < 0.5 := by norm_num

/-- Lemma 22, p. 36: `x^{1.1 - 0.1 - 1.64/3} > x^{0.45}`. -/
theorem lemma22_exponent : (0.45 : ℝ) < 1.1 - 0.1 - 1.64 / 3 := by norm_num

/-- Lemma 26, p. 40: `2 - 0.5 - 0.82 - 0.225 ≥ 0.45`. -/
theorem lemma26_exponent : (2 - 0.5 - 0.82 - 0.225 : ℝ) = 0.455 ∧ (0.45 : ℝ) < 0.455 := by
  norm_num

/-- Lemma 28, p. 42: `0.4 × 4/3 + 0.175 < 0.75`. -/
theorem lemma28_exponent : (0.4 * (4 / 3) + 0.175 : ℝ) < 0.75 := by norm_num

/-! ### PROVED: exponent arithmetic, Section 5 -/

/-- `c₁ - 4c₃ = -θ₂ + 7ε`, the left end of the chain after (5.16), p. 51. -/
theorem c1_minus_4c3 (ε : ℝ) : cc1 ε - 4 * cc3 ε = -theta2 + 7 * ε := by
  unfold cc1 cc3; ring

/-- The chain of p. 51: `-θ₂ + ε ≤ 2 - 4c₃ + c₁ - 2` and
`2 - θ₂ + 8ε + 1/6 + c₃/3 - 2 < θ₂ - ε` for `0 ≤ ε ≤ 1/1000`. -/
theorem chain_516 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 1000) :
    -theta2 + ε ≤ 2 - 4 * cc3 ε + cc1 ε - 2 ∧
    2 - theta2 + 8 * ε + 1 / 6 + cc3 ε / 3 - 2 < theta2 - ε := by
  unfold cc1 cc3; rw [theta2_val]; constructor <;> linarith

/-- The chain needs `θ₂ > 31/338`, about `0.0917`, far below `θ₂ ≈ 1/8`. -/
theorem chain_threshold : (31 / 338 : ℝ) < theta2 := by rw [theta2_val]; norm_num

/-- `c₃ ≤ c₁`, so `p₁p₂ ≤ Y^{1/2 + c₃ - c₁} ≤ Y^{1/2}`, p. 51. -/
theorem c3_le_c1 {ε : ℝ} (h0 : 0 ≤ ε) : cc3 ε ≤ cc1 ε := by
  unfold cc1 cc3; rw [theta2_val]; linarith

/-- Numerical values: `c₁ ≈ 0.12499`, `c₂ ≈ 0.22721`, `c₄ ≈ 0.26562`, at `ε = 0`. -/
theorem cc_values :
    cc1 0 = (1 + 7 * (1 / 8 - 1 / 50000)) / 15 ∧ cc2 0 = (36 * (1 / 8 - 1 / 50000) - 2) / 11 ∧
    (0.1249 : ℝ) < cc1 0 ∧ cc1 0 < 0.125 ∧ (0.2271 : ℝ) < cc2 0 ∧ cc2 0 < 0.2273 := by
  unfold cc1 cc2; rw [theta2_val]; norm_num

end LeanLab.BakerHarmanPintz1997

open LeanLab.BakerHarmanPintz1997 in
section
#print axioms remark_values
#print axioms theta2_eq
#print axioms theta2_val
#print axioms theta12_zero
#print axioms theta12_le
#print axioms theta12_pos
#print axioms theta12_lt_li
#print axioms below_PP
#print axioms uv_pos
#print axioms u0_bound
#print axioms constants_15
#print axioms uv_pos_final
#print axioms mu_gt
#print axioms printed_SS_factor_two
#print axioms fsig_three_quarters
#print axioms ineq313
#print axioms ineq313_value
#print axioms gam_pos_iff
#print axioms gam_sec5
#print axioms c2_from_gam
#print axioms theta_sec5_range
#print axioms alphas_R
#print axioms alphas_P1
#print axioms qT2_exponent
#print axioms R_check
#print axioms holder_lemma3
#print axioms printed_beta2_misprint
#print axioms lemma2_apps
#print axioms gamma_iva
#print axioms gamma_thresholds
#print axioms thresholds_327
#print axioms S_at_min
#print axioms S_min_value
#print axioms S_core
#print axioms S_lower
#print axioms S_ge_half
#print axioms ivb_ranges
#print axioms lemma4_exponents
#print axioms lemma10_exponent
#print axioms lemma13_exponents
#print axioms lemma14_exponent
#print axioms lemma17_exponents
#print axioms lemma22_exponent
#print axioms lemma26_exponent
#print axioms lemma28_exponent
#print axioms c1_minus_4c3
#print axioms chain_516
#print axioms chain_threshold
#print axioms c3_le_c1
#print axioms cc_values
end

#print axioms LeanLab.BakerHarmanPintz1997.ramachandra
#print axioms LeanLab.BakerHarmanPintz1997.li
