/-
Unit U-1513, track T1, PC run 20261025T0803Z-22023, idea I-0113, paper P0022 Kaniecki 1995.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Rewire of `SchnirelmannBounds.kaniecki1995_theorem` of SchnirelmannBounds/Discharged.lean onto
the zero-count inputs and the sharper J_ψ constant.

`kaniecki1995_theorem` takes the bundle `KanieckiInputs`: the J_ψ bound with constant 2.2258,
even Goldbach to 4 · 10^18, Schoenfeld 1976 Corollary 1 `SchoenfeldTheta` under RH, and
Liu-Wang's e^3100. Here:

* Schoenfeld's θ bound is dropped. In its place are `HSWN70 gZ`, `HSWHead14 gZ`, `Ordinates14 gZ`
  for the true ordinates, used through `Routes.U1505.goldbach_445_of_J_hsw`, which rests on
  `PNTPort.ExplicitPsi1.Trivial.theta_schoenfeld_large`, valid for `u ≥ 10^11`; the only use is
  `ThetaRel6`, which needs `u ≥ 10^16`, so the range matches, see `thetaRel6_of_large`.
* The J_ψ constant 2.2258 is replaced by 1.0069, the conclusion of
  `ChirreHagen2025.SmoothT2.theorem2_u6806`. `kaniecki1995_theorem_hsw` takes the 1.0069 bound
  as a hypothesis; `kaniecki1995_theorem_u6806_hsw` discharges it by `theorem2_u6806` from
  `ExplicitA`, `HadamardK`, `Ordinates14`, `BPTN` for an ordinate family `γ`; it is in
  U1513KanieckiU6806.lean, which imports the split `U6806Theorem2Sp` chain.
* The one range gap: Kaniecki's assembly needs `KanieckiGap.G10`, an interval
  `(x, x + 10 log² x)` for every `x ≥ 2`, while the 4.45 line is stated for `x ≥ 3`.
  `g10_of_445` closes `2 ≤ x < 3` by hand with `6 = 3 + 3`, PROVED.
-/
import Mathlib
import LeanLab.KanieckiGap.AssemblyEven
import LeanLab.Kaniecki1995.Statements
import LeanLab.SchnirelmannBounds.Statements
import LeanLab.Routes.U1505Theta6HSW

namespace LeanLab.Kaniecki1995.U1513
open Real LeanLab.SchnirelmannConstant LeanLab.KanieckiGap
open LeanLab.ChirreHagen2025
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)
open LeanLab.Dudek2014.SigmaH (HSWN70)

/-- `G10` from a Goldbach number in `(x, x + 4.45 log² x)` for `x ≥ 3`. PROVED; the part
`2 ≤ x < 3` is `6 = 3 + 3` with `10 log² 2 > 4`. -/
theorem g10_of_445
    (h : ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2) : G10 := by
  intro x hx
  rcases lt_or_ge x 3 with h3 | h3
  · refine ⟨6, ⟨3, 3, Nat.prime_three, Nat.prime_three, ⟨1, rfl⟩, ⟨1, rfl⟩, rfl⟩, ?_, ?_⟩
    · push_cast; linarith
    · have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
      have h2 := Real.log_two_gt_d9
      have hsq : (0.6931471803 : ℝ) ^ 2 ≤ Real.log x ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 2
      push_cast
      nlinarith
  · obtain ⟨n, hn, h1, h2⟩ := h x h3
    have hl : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    exact ⟨n, hn, h1, by nlinarith⟩

/-- `G10` under RH from the J_ψ constant 1.0069, the 4 · 10^18 check and the three HSW
zero-count inputs for `gZ`. CONDITIONAL ON `h2`, `hE`, `HSWN70 gZ`, `HSWHead14 gZ`,
`Ordinates14 gZ`. -/
theorem g10_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hN : HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : SmoothT2.Ordinates14 gZ) : RiemannHypothesis → G10 := fun hRH =>
  g10_of_445 (LeanLab.Routes.U1505.goldbach_445_of_J_hsw h2 hE hN hH h14 hRH)

/-- **P0022 Kaniecki, even half**, as `Kaniecki1995.TheoremEven`. CONDITIONAL ON the J_ψ bound
`h2` with constant 1.0069, `EvenGoldbachUpTo (4 · 10^18)`, Liu-Wang's `TernaryAbove (e^3100)`,
`HSWN70 gZ`, `HSWHead14 gZ`, `Ordinates14 gZ`. RH is the antecedent, as printed. The G2
hypothesis of the statement is not used. -/
theorem kaniecki_even_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hN : HSWN70 gZ) (hH : HSWHead14 gZ) (h14 : SmoothT2.Ordinates14 gZ) :
    LeanLab.Kaniecki1995.TheoremEven := fun hRH _ =>
  even_atMost4_of (g10_hsw h2 hE hN hH h14 hRH) hE hLW

/-- **P0022 Kaniecki, odd half**, as `Kaniecki1995.TheoremOdd`: odd `n > 1` is 3 plus an even
number. Same inputs as `kaniecki_even_hsw`. -/
theorem kaniecki_odd_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hN : HSWN70 gZ) (hH : HSWHead14 gZ) (h14 : SmoothT2.Ordinates14 gZ) :
    LeanLab.Kaniecki1995.TheoremOdd := by
  intro hRH n ho h1
  have hev : Even (n - 3) := by obtain ⟨k, hk⟩ := ho; exact ⟨k - 1, by omega⟩
  have h4 := even_atMost4_of (g10_hsw h2 hE hN hH h14 hRH) hE hLW (n - 3) hev
  have h' : AtMostPrimes (1 + 4) (3 + (n - 3)) := (AtMostPrimes.prime Nat.prime_three).add h4
  have e : 3 + (n - 3) = n := by obtain ⟨k, hk⟩ := ho; omega
  rw [e] at h'
  exact h'

/-- **P0022's Theorem, both halves**, the counterpart of `kaniecki1995_theorem` with
Schoenfeld's θ bound dropped and J_ψ constant 1.0069 in place of 2.2258. Same inputs as
`kaniecki_even_hsw`. -/
theorem kaniecki1995_theorem_hsw
    (h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      Jpsi x δ ≤ 1.0069 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100))
    (hN : HSWN70 gZ) (hH : HSWHead14 gZ) (h14 : SmoothT2.Ordinates14 gZ) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven :=
  ⟨kaniecki_odd_hsw h2 hE hLW hN hH h14, kaniecki_even_hsw h2 hE hLW hN hH h14⟩

/-- Faithfulness: the targets are the statements `kaniecki1995_theorem` proves. -/
example : LeanLab.Kaniecki1995.TheoremOdd = LeanLab.SchnirelmannBounds.kaniecki_odd_stmt := rfl
example : LeanLab.Kaniecki1995.TheoremEven = LeanLab.SchnirelmannBounds.kaniecki_even_stmt := rfl

/-- Vacuity check, small instances of two input shapes: `Ordinates14` holds for the empty
family, and even Goldbach holds up to 10. -/
example : SmoothT2.Ordinates14 (Empty.elim : Empty → ℝ) := fun i => i.elim
example : EvenGoldbachUpTo 10 := by
  intro n hn h4 h10
  obtain ⟨k, rfl⟩ := hn
  have : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  · exact ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  · exact ⟨3, 5, Nat.prime_three, Nat.prime_five, rfl⟩
  · exact ⟨3, 7, Nat.prime_three, (by norm_num), rfl⟩

end LeanLab.Kaniecki1995.U1513
