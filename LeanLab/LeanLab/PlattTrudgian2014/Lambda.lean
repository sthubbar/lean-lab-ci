/-
Platt, Trudgian 2014, P0024, arXiv 1404.5669v2: the definition of λ by display (5) and the two
λ bounds, unit U-0328, run 20261017T1402Z-26900.
Display (4): G_L(x) = Σ_{j=0}^{L-1} e(2^j x), L = ⌊log N / log 2⌋.
Display (5), as extracted: "For c > 0 we seek to find the smallest positive value of λ such
that Δ = max(x ∈ [0, 1] : |G_L(x)| > λL) < N^{-c/log 2}." The operator reads "max" in the text
we could extract. Read literally it can never hold for λ < 1, `printed_max_fails` below,
because x = 1 lies in the set. We state the measure reading, as in Pintz-Ruzsa, and for all
large N; both readings are a QUESTION in STATEMENTS.md, not a FINDING.
Cited with sorry: "λ ≤ 0.8594000 unconditionally and λ ≤ 0.7163436 on GRH". On GRH only the
exponent changes, c = 1/2 instead of 109/154; the λ computation itself uses no GRH, so both
bounds are stated unconditionally with their c.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PlattTrudgian2014.Statements

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex

/-- L = ⌊log N / log 2⌋, display (4). -/
noncomputable def Lof (N : ℕ) : ℕ := ⌊Real.log N / Real.log 2⌋₊

/-- G_L(x) = Σ_{0 ≤ j < L} e(2^j x), display (4). -/
noncomputable def G (L : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range L, Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ j * x))

/-- {x ∈ [0, 1] : |G_L(x)| > λL}, the set in display (5). -/
def bigSet (N : ℕ) (lam : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ lam * Lof N < ‖G (Lof N) x‖}

/-- Display (5) AS PRINTED, measure reading, for all large N: `meas < N^{-c/log 2}`. A `def`
only since audit U-1007, run 20261019T0202Z-9877: with `L = ⌊log₂ N⌋`, `N^{-c/log 2} ≈ 2^{-cL/log 2}`
and at `c = 109/154` that is `2^{-1.021 L}`, but `|G_L(x)| > λL` already holds on `[0, 2^{-k}/16]`
for `k ≈ (1 + λ)L/1.98`, a set of measure about `2^{-0.94 L}` at `λ = 0.8594`. So the printed
form fails for every large N and citing it was unsound. -/
def LambdaOKPrinted (c lam : ℝ) : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (volume (bigSet N lam)).toReal < (N : ℝ) ^ (-(c / Real.log 2))

/-- Display (5), REPAIRED reading `meas < N^{-c}`, Heath-Brown and Puchta's `E(λ) > c` form,
for all large N. The cited bounds below use this reading; the page check of which form
Heath-Brown and Puchta and Platt and Trudgian intend is open, QUESTION in STATEMENTS.md. -/
def LambdaOK (c lam : ℝ) : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → (volume (bigSet N lam)).toReal < (N : ℝ) ^ (-c)

/-- Cited, P0024 §3: λ = 0.8594 satisfies (5) with Heath-Brown and Puchta's c = 109/154. -/
theorem pt_lambda_uncond : LambdaOK (109 / 154) 0.8594 := by sorry

/-- Cited, P0024 §3: λ = 0.7163436 satisfies (5) with the GRH value c = 1/2. -/
theorem pt_lambda_GRH : LambdaOK (1 / 2) 0.7163436 := by sorry

/-! ### Links, PROVED -/

theorem bigSet_subset {N : ℕ} {lam lam' : ℝ} (h : lam ≤ lam') : bigSet N lam' ⊆ bigSet N lam := by
  intro x hx
  refine ⟨hx.1, lt_of_le_of_lt ?_ hx.2⟩
  exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)

theorem volume_bigSet_ne_top (N : ℕ) (lam : ℝ) : volume (bigSet N lam) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono (fun x hx => hx.1))

/-- A larger λ still satisfies (5): "smallest" is the only content of minimality. -/
theorem lambdaOK_mono {c lam lam' : ℝ} (h : lam ≤ lam') (hok : LambdaOK c lam) :
    LambdaOK c lam' := by
  obtain ⟨N0, hN⟩ := hok
  refine ⟨N0, fun N hN0 => lt_of_le_of_lt ?_ (hN N hN0)⟩
  exact ENNReal.toReal_mono (volume_bigSet_ne_top N lam) (measure_mono (bigSet_subset h))

/-- A smaller c is easier: (5) for c gives (5) for every c' ≤ c. -/
theorem lambdaOK_c_mono {c c' lam : ℝ} (h : c' ≤ c) (hok : LambdaOK c lam) :
    LambdaOK c' lam := by
  obtain ⟨N0, hN⟩ := hok
  refine ⟨max N0 1, fun N hN0 => lt_of_lt_of_le (hN N (le_trans (le_max_left _ _) hN0)) ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN0
  apply Real.rpow_le_rpow_of_exponent_le hN1
  linarith

/-- Since 1/2 ≤ 109/154, the unconditional line already gives (5) at c = 1/2 with λ = 0.8594;
the GRH line improves λ to 0.7163436 at that c. -/
theorem uncond_at_half : LambdaOK (1 / 2) 0.8594 :=
  lambdaOK_c_mono (by norm_num) pt_lambda_uncond

theorem G_one (L : ℕ) : G L 1 = L := by
  unfold G
  have : ∀ j ∈ Finset.range L, Complex.exp (2 * Real.pi * I * ((2 : ℂ) ^ j * (1 : ℝ))) = 1 := by
    intro j _
    rw [Complex.exp_eq_one_iff]
    exact ⟨2 ^ j, by push_cast; ring⟩
  rw [Finset.sum_congr rfl this]
  simp

theorem one_le_Lof {N : ℕ} (hN : 2 ≤ N) : 1 ≤ Lof N := by
  unfold Lof
  rw [Nat.one_le_floor_iff]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hl, one_mul]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)

/-- The printed operator "max", read as a supremum, makes (5) fail for every λ < 1, c ≥ 0
and N ≥ 2, since x = 1 has |G_L(1)| = L > λL. Support for the QUESTION, not a FINDING. -/
theorem printed_max_fails {N : ℕ} (hN : 2 ≤ N) {lam c : ℝ} (hlam : lam < 1) (hc : 0 ≤ c) :
    ¬ (sSup (bigSet N lam) < (N : ℝ) ^ (-(c / Real.log 2))) := by
  have hL : (1 : ℝ) ≤ Lof N := by exact_mod_cast one_le_Lof hN
  have h1 : (1 : ℝ) ∈ bigSet N lam := by
    refine ⟨⟨by norm_num, le_rfl⟩, ?_⟩
    rw [G_one, Complex.norm_natCast]
    nlinarith
  have hbdd : BddAbove (bigSet N lam) := ⟨1, fun x hx => hx.1.2⟩
  have hs : 1 ≤ sSup (bigSet N lam) := le_csSup hbdd h1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (-(c / Real.log 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by have := div_nonneg hc hl.le; linarith)
  linarith

end LeanLab.PlattTrudgian2014
