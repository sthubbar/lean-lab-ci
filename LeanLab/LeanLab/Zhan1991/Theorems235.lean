/-
P0068 Zhan 1991, Theorems 2, 3 and 5, pages 260 and 261, read from the rendered page images of
copies/P0068.pdf by run 20261018T2303Z-8776. Statements only, as `Prop`s; nothing here is proved
except the exponent bookkeeping at the end.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Readings: `≪` is `∃ K N₀, ∀ N ≥ N₀, ‖·‖ ≤ K · bound`, with `K` and `N₀` allowed to depend on every
constant fixed before them. `e(x) = exp(2πix)`. `L = log N`.
-/
import Mathlib

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- `e(x) = exp(2πi x)`. -/
def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- The integers `n` with `N - A < n ≤ N`. -/
def shortWin (N : ℕ) (A : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => (N : ℝ) - A < n)

/-- `S(α; N, A) = Σ_{N-A < n ≤ N} Λ(n) e(nα)`, page 260. -/
def Sexp (α : ℝ) (N : ℕ) (A : ℝ) : ℂ :=
  ∑ n ∈ shortWin N A, (Λ n : ℂ) * ee (n * α)

/-- Condition (1.2): `α = a/q + λ`, `(a, q) = 1`, `|λ| ≤ 1/(qτ)`, `1 ≤ q ≤ τ`. -/
def Cond12 (α τ : ℝ) (a : ℤ) (q : ℕ) (lam : ℝ) : Prop :=
  α = a / q + lam ∧ Int.gcd a q = 1 ∧ |lam| ≤ 1 / (q * τ) ∧ 1 ≤ q ∧ (q : ℝ) ≤ τ

/-- Theorem 2, page 260: given `B > 0` there are `c₁, c₂, c₃ > 0` such that, under (1.2) with
`τ = A² N⁻¹ L^{-c₁}`, `q ≥ L^{c₂}` and `N^{3/5} L^{c₃} ≤ A ≤ N`, `S(α; N, A) ≪ A L^{-B}`. -/
def Theorem2 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ), N₀ ≤ N →
      (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
      Real.log N ^ c2 ≤ q →
      ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B)

/-- Theorem 3, page 260: given `c₁, c₂ > 0` and `B > 0` there is `c₃ > 0` such that (1.3) holds
under (1.2) with `τ = N⁻¹ A² L^{-c₁}`, `1 ≤ q ≤ L^{c₂}`, `|λ| ≥ A⁻¹ L^{B+1}` and
`N^{5/8} L^{c₃} ≤ A ≤ N`. -/
def Theorem3 : Prop :=
  ∀ c1 c2 B : ℝ, 0 < c1 → 0 < c2 → 0 < B → ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ), N₀ ≤ N →
      (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
      (q : ℝ) ≤ Real.log N ^ c2 →
      Real.log N ^ (B + 1) / A ≤ |lam| →
      ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B)

/-- `Σ_{N-A < n ≤ N} μ(n) e(nα)`, page 261. -/
def Smu (α : ℝ) (N : ℕ) (A : ℝ) : ℂ :=
  ∑ n ∈ shortWin N A, (μ n : ℂ) * ee (n * α)

/-- Theorem 5, page 261: for any `B > 0`, `ε > 0`, `Σ_{N-A<n≤N} μ(n) e(nα) ≪ A (log N)^{-B}`
uniformly in real `α`, for `N^{5/8+ε} ≤ A ≤ N`. The page prints `≤ a ≤ N`; read as `A`. -/
def Theorem5 : Prop :=
  ∀ B ε : ℝ, 0 < B → 0 < ε → ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α : ℝ), N₀ ≤ N →
    (N : ℝ) ^ (5 / 8 + ε) ≤ A → A ≤ N → ‖Smu α N A‖ ≤ K * A * Real.log N ^ (-B)

/-- Lemma 2 of the paper, Zhan [4], page 261, `k = 0, 1`: for `q ≥ 1`, `H ≥ T^{1/3}`,
`Σ_{χ mod q} ∫_T^{T+H} |L^{(k)}(1/2+it, χ)|² dt ≪ qH (log qH)^{2k+1}`. Cited. -/
def Lemma2 : Prop :=
  ∃ K T₀ : ℝ, ∀ (q : ℕ) [NeZero q] (T H : ℝ) (k : ℕ), k ≤ 1 → T₀ ≤ T → T ^ (1 / 3 : ℝ) ≤ H →
    ∑ χ : DirichletCharacter ℂ q, ∫ t in T..(T + H),
      ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
    ≤ K * q * H * Real.log (q * H) ^ (2 * k + 1)

/-- Lemma 3 of the paper, Jutila [3], page 261, `k = 0, 1`: for `ε > 0`, `H ≤ T`,
`Σ_χ ∫_T^{T+H} |L^{(k)}(1/2+it, χ)|⁴ dt ≪ (qH + qT^{2/3}) (qT)^ε`. Cited. -/
def Lemma3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K T₀ : ℝ, ∀ (q : ℕ) [NeZero q] (T H : ℝ) (k : ℕ), k ≤ 1 → T₀ ≤ T →
    0 < H → H ≤ T →
    ∑ χ : DirichletCharacter ℂ q, ∫ t in T..(T + H),
      ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4
    ≤ K * (q * H + q * T ^ (2 / 3 : ℝ)) * (q * T) ^ ε

/-! ### Exponent bookkeeping, PROVED -/

/-- At the bottom of Theorem 3's range, `A = N^{5/8}`, the major arc width `τ = A²/N` is
`N^{1/4}`, and at the bottom of Theorem 2's range, `A = N^{3/5}`, it is `N^{1/5}`; logs aside. -/
theorem tau_exponents : 2 * (5 / 8 : ℝ) - 1 = 1 / 4 ∧ 2 * (3 / 5 : ℝ) - 1 = 1 / 5 := by norm_num

/-- `τ ≥ 1` needs `A ≥ N^{1/2}`; both ranges clear it: `1/2 < 3/5 < 5/8`. -/
theorem ranges_clear_half : (1 / 2 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) < 5 / 8 := by norm_num

/-- Theorem 4's hypothesis has short interval `T^{9/16}`, inside Lemma 2's range `H ≥ T^{1/3}`
and below Lemma 3's crossover `T^{2/3}`: `1/3 < 9/16 < 2/3`. -/
theorem nine_sixteenths : (1 / 3 : ℝ) < 9 / 16 ∧ (9 / 16 : ℝ) < 2 / 3 := by norm_num

/-- Lemma 3 at `H = T^{9/16}` gives only `qT^{2/3+ε}`, short of the `T^{9/16+ε}` Theorem 4
assumes, which is why Theorem 4 is conditional: `9/16 < 2/3`. -/
theorem lemma3_short_of_hyp4 : (9 / 16 : ℝ) < 2 / 3 := by norm_num

end

end LeanLab.Zhan1991
