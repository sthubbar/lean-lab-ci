/-
P0068 Zhan Tao, "On the Representation of Large Odd Integer as a Sum of Three Almost Equal
Primes", Acta Math. Sinica, New Series 7 (1991), no. 3, 259-272. Read 2026-10-18 from
papers/P0068.pdf, pages 259 to 261 from the rendered page images; the OCR text alone was not
used for any exponent or formula.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. The ternary problem is settled by Helfgott 2013; this paper is about
the almost equal summands version, an asymptotic for large N.

Readings: `p_i` run over primes in `[N/3 - U, N/3 + U]`, display (1.1). `T(N, U)` counts the
ordered triples. The big-O of Theorem 1 is `∃ K N₀, ∀ N ≥ N₀`. `≪` in Theorem 4 has constants
depending on `ε` and `c₄`. The singular series is stated over all primes with `+ 1/(p-1)^3` for
`p ∤ N`; the paper prints `1 - 1/(p-1)^3` on page 260, which vanishes at `p = 2` for odd `N`,
see `singPrinted_odd_eq_zero` and STATEMENTS.md. Edited by run 20261018T2303Z-8776.
-/
import Mathlib

namespace LeanLab.Zhan1991
open Finset Real Complex

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The primes in `[N/3 - U, N/3 + U]`. -/
def Win (N U : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈N / 3 - U⌉₊ ⌊N / 3 + U⌋₊).filter Nat.Prime

/-- `T(N, U)`, the number of `(p₁, p₂, p₃)` with `p₁ + p₂ + p₃ = N` and every `p_i` in the
window. `N` is a natural number; the window is in terms of `(N : ℝ)`. -/
def T (N : ℕ) (U : ℝ) : ℕ :=
  ((Win N U ×ˢ Win N U).filter
    (fun p => p.1 + p.2 < N ∧ N - p.1 - p.2 ∈ Win N U)).card

/-- The singular series over ODD primes only, `∏_{p ∣ N, p > 2} (1 - 1/(p-1)²)
∏_{p ∤ N, p > 2} (1 + 1/(p-1)³)`. This was `Sing` in run 20261018T2020Z-cloud8. It leaves out the
factor `1 + 1/(2-1)³ = 2` at `p = 2` for odd `N`, so `3 SingOdd(N) U² L⁻³` is about half the
true count; VERIFY run 20261018T2303Z-8776 counted `T(N, N^{5/8})` for `N = 10⁷+1, 3·10⁷+7,
10⁸+3` and found ratios 1.98, 1.98, 2.07 against `3 SingOdd U² log(N/3)⁻³`. Kept for reference. -/
def SingOdd (N : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3

/-- The singular series of page 260 over ALL primes, with the standard sign:
`𝔖(N) = ∏_{p ∣ N} (1 - 1/(p-1)²) ∏_{p ∤ N} (1 + 1/(p-1)³)`. For odd `N` the factor at `p = 2`
is `2`. Fixed 2026-10-18 by run 20261018T2303Z-8776. -/
def Sing (N : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime},
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3

/-- The singular series as printed on page 260, over all primes as printed, with
`1 - 1/(p-1)³` for `p ∤ N`. -/
def SingPrinted (N : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime},
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 - 1 / ((p.1 : ℝ) - 1) ^ 3

/-- The printed product restricted to odd primes, the reading of run cloud8. -/
def SingPrintedOdd (N : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 - 1 / ((p.1 : ℝ) - 1) ^ 3

/-- Theorem 1, the asymptotic: for `U = N^{5/8} (log N)^c` with some absolute `c > 0` and every
large odd `N`, `T(N, U) = 3 𝔖(N) U² (log N)^{-3} + O(U² (log N)^{-4})`. -/
def Theorem1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
    |(T N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) : ℝ)
        - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-3 : ℝ)|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)


/-- The paper's claim `𝔖(N) > 1/2` for odd `N`, page 260, as a hypothesis on `Sing`. -/
def SingGtHalf : Prop := ∀ N : ℕ, Odd N → 1 / 2 < Sing N

/-- Solvability of (1.1): a representation `N = p₁ + p₂ + p₃` with all `p_i` in the window. -/
def Solvable (N : ℕ) (U : ℝ) : Prop := 0 < T N U

/-- Theorem 1, first assertion: (1.1) is solvable for `U = N^{5/8} (log N)^c`, every large odd
`N`. PROVED from the asymptotic and `𝔖(N) > 1/2`; the second assertion's error term is
dominated by the main term for large `N`. -/
theorem solvable_of_theorem1 (h1 : Theorem1) (hS : SingGtHalf) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      Solvable N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) := by
  obtain ⟨c, hc, K, N₀, h⟩ := h1
  refine ⟨c, hc, max N₀ (max (Real.exp (4 * (|K| + 1))) 3), fun N hN hle => ?_⟩
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hle
  have hexp : Real.exp (4 * (|K| + 1)) ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have h3 : (3 : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 4 * (|K| + 1) ≤ Real.log N := by
    rw [← Real.log_exp (4 * (|K| + 1))]; exact Real.log_le_log (Real.exp_pos _) hexp
  have hLpos : 0 < Real.log N := by have := abs_nonneg K; linarith
  set U : ℝ := (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c with hU
  have hUpos : 0 < U := by
    have := Real.rpow_pos_of_pos hNpos (5 / 8 : ℝ)
    have := Real.rpow_pos_of_pos hLpos c
    positivity
  have hb := h N hN hN₀
  have hSN := hS N hN
  set L := Real.log N with hLdef
  have hm4 : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) / L := by
    rw [show (-4 : ℝ) = -3 - 1 by norm_num, Real.rpow_sub hLpos, Real.rpow_one]
  have hm3 : 0 < L ^ (-3 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hbound : K * U ^ 2 * L ^ (-4 : ℝ) ≤ U ^ 2 * L ^ (-3 : ℝ) / 4 := by
    rw [hm4]
    have hK : K ≤ |K| := le_abs_self K
    have hKL : K / L ≤ 1 / 4 := by
      rw [div_le_iff₀ hLpos]; nlinarith [abs_nonneg K]
    have : K * U ^ 2 * (L ^ (-3 : ℝ) / L) = U ^ 2 * L ^ (-3 : ℝ) * (K / L) := by ring
    rw [this]
    have hpos : 0 < U ^ 2 * L ^ (-3 : ℝ) := by positivity
    nlinarith
  have hmain : 3 * Sing N * U ^ 2 * L ^ (-3 : ℝ) > 3 / 2 * (U ^ 2 * L ^ (-3 : ℝ)) := by
    have hpos : 0 < U ^ 2 * L ^ (-3 : ℝ) := by positivity
    nlinarith
  have hTpos : (0 : ℝ) < T N U := by
    have := (abs_le.mp hb).1
    nlinarith [show 0 < U ^ 2 * L ^ (-3 : ℝ) by positivity]
  exact_mod_cast hTpos

/-! ### Theorem 4, conditional on a fourth-moment hypothesis -/

/-- The hypothesis of Theorem 4: for every `ε > 0` and `c₄ > 0`, every Dirichlet character `χ`
modulo `q ≤ (log T)^{c₄}`, and `k = 0, 1`,
`∫_T^{T + T^{9/16}} |L^{(k)}(1/2 + it, χ)|⁴ dt ≪ T^{9/16 + ε}`, the constant depending on `ε`
and `c₄`. `L^{(k)}` is `iteratedDeriv k` of Mathlib's `DirichletCharacter.LFunction`. -/
def Hyp4 : Prop :=
  ∀ ε c₄ : ℝ, 0 < ε → 0 < c₄ → ∃ C T₀ : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) (k : ℕ), k ≤ 1 → T₀ ≤ T → (q : ℝ) ≤ Real.log T ^ c₄ →
      ∫ t in T..(T + T ^ (9 / 16 : ℝ)),
        ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 4
      ≤ C * T ^ (9 / 16 + ε)

/-- Theorem 4: under `Hyp4`, for every `ε > 0` the equation (1.1) is solvable for
`U = N^{3/5 + ε}` and large odd `N`. -/
def Theorem4 : Prop :=
  Hyp4 → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
    Solvable N ((N : ℝ) ^ (3 / 5 + ε))


/-! ### Exponents -/

/-- Theorem 4 beats Theorem 1: `3/5 < 5/8`, and `2/3` of Pan and Pan is above both. -/
theorem exponent_order : (3 : ℝ) / 5 < 5 / 8 ∧ (5 : ℝ) / 8 < 2 / 3 := by norm_num

/-- `U = N^{5/8}` leaves the almost equal primes within `N^{5/8}` of `N/3`, below the trivial
range `N^1`; the exponent of `N^{5/8 + ε}` of Zhan's later statements is still below `2/3`. -/
theorem exponent_five_eighths_lt_one : (5 : ℝ) / 8 < 1 := by norm_num

/-! ### The sign in the printed singular series, local densities at small primes

For a prime `p` and `N`, count `(x₁, x₂, x₃)` in `(ℤ/p)^3` with all `x_i ≠ 0` and
`x₁ + x₂ + x₃ = N`. The count is `((p-1)³ + 1)/p` for `p ∤ N` and `((p-1)³ - (p-1))/p` for
`p ∣ N`; the local density `p · count / (p-1)³` is `1 + 1/(p-1)³` and `1 - 1/(p-1)²`. -/

def localCount (p N : ℕ) : ℕ :=
  ((Finset.range p ×ˢ Finset.range p ×ˢ Finset.range p).filter
    (fun x => x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 ≠ 0 ∧ (x.1 + x.2.1 + x.2.2) % p = N % p)).card

theorem localCount_5_not_dvd : localCount 5 1 = 13 := by decide
theorem localCount_5_dvd : localCount 5 5 = 12 := by decide
theorem localCount_7_not_dvd : localCount 7 1 = 31 := by decide
theorem localCount_7_dvd : localCount 7 7 = 30 := by decide

/-- At `p = 5`, `N = 1`: `5 · 13 / 4³ = 65/64 = 1 + 1/4³`, not `1 - 1/4³ = 63/64`. -/
theorem local_density_5 : (5 : ℚ) * 13 / 4 ^ 3 = 1 + 1 / 4 ^ 3 ∧ (5 : ℚ) * 13 / 4 ^ 3 ≠ 1 - 1 / 4 ^ 3 := by
  norm_num

theorem local_density_7 : (7 : ℚ) * 31 / 6 ^ 3 = 1 + 1 / 6 ^ 3 ∧ (7 : ℚ) * 31 / 6 ^ 3 ≠ 1 - 1 / 6 ^ 3 := by
  norm_num

/-! ### The printed singular series vanishes for odd `N`, run 20261018T2303Z-8776 -/

/-- For odd `N` the printed factor at `p = 2` is `1 - 1/(2-1)³ = 0`, so the printed product is
`0`, contradicting the printed `𝔖(N) > 1/2`. The plus sign gives the factor `2` instead. -/
theorem singPrinted_odd_eq_zero (N : ℕ) (hN : Odd N) : SingPrinted N = 0 := by
  unfold SingPrinted
  apply tprod_of_exists_eq_zero
  refine ⟨⟨2, Nat.prime_two⟩, ?_⟩
  have h2 : ¬ (2 ∣ N) := by
    rcases hN with ⟨k, rfl⟩; omega
  simp only [h2, if_false]
  norm_num

/-- The printed inequality `𝔖(N) > 1/2` fails for the printed product at every odd `N`. -/
theorem printed_not_gt_half (N : ℕ) (hN : Odd N) : ¬ (1 / 2 < SingPrinted N) := by
  rw [singPrinted_odd_eq_zero N hN]; norm_num

/-- With the plus sign the factor at `p = 2` for odd `N` is `2`. -/
theorem sing_factor_two (N : ℕ) (hN : Odd N) :
    (if 2 ∣ N then 1 - 1 / ((2 : ℝ) - 1) ^ 2 else 1 + 1 / ((2 : ℝ) - 1) ^ 3) = 2 := by
  have h2 : ¬ (2 ∣ N) := by
    rcases hN with ⟨k, rfl⟩; omega
  simp only [h2, if_false]
  norm_num

end

end LeanLab.Zhan1991
