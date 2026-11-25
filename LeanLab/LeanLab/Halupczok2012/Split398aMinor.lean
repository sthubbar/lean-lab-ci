import LeanLab.Halupczok2012.Decomp398a
import LeanLab.Halupczok2012.B1btChebyshev
import LeanLab.Halupczok2012.Split398aMajor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Order

/-!
# Split of `Decomp398a.minor_energy` into paper leaves

Source: A. Perelli and J. Pintz, On the exceptional set for Goldbach's problem in short
intervals, J. London Math. Soc. 47, 1993, pages 41 to 49, here PP1993.
The minor arc half is PP1993 p. 44 displays 3 and 5, with the proof of display 5 in
section 5 on pages 46 to 48.

Plan: the reread note of 2026-11-22, Part 2, leaves B1 to B14, which was checked against the
page images of PP1993. No copy of PP1993 is in `papers/`; that note is the source authority.

Route, in the notation of PP1993 p. 43, with `L = log N`, `H = Y^(1/3+ε)`, `Q = sqrt H / 2`
and `B = 3/ε (2A + 25)`.
* B1 is display 3, B2 the window cover after display 3. Together they reduce the minor arc
  energy to display 5, the local bound `∫ |S2|^2 ≤ Y L^(-2A-3)` on windows of length `2/H`.
* B3 is display 14, the Farey cover; B4 is display 15, the principal part `μ/φ T2`.
* B5 to B8 are displays 16 to 20, good and bad characters; B9 to B13 are displays 21 to 25,
  Gallagher, the explicit formula, Saffari and Vaughan and the zero sum; B14 is display 26.
* B1 needs a Brun Titchmarsh type short interval bound, isolated as the extra leaf B1bt.

Deviations from the note, each also stated at its leaf:
* B1: the note suggests replacing Brun Titchmarsh by `Λ ≤ log` and absorbing the loss by a
  larger A. That does not wire: the minor arcs depend on A and shrink as A grows. So B1 takes
  the short interval bound as a hypothesis and B1bt is a separate cited leaf.
* B11 and B14 carry `ε < 1/3`: the bound `q^2 Q ≤ Y L^(-2A-3)` of display 23 holds only then.
  Hence the exact wiring `minor_energy_of_leaves` is ABSENT; the file proves
  `minor_energy_small_of_leaves`, the same statement restricted to `ε < 1/3`.
* The rectangle of display 16 and the ranges in displays 24 and 25 are not transcribed in the
  note. They are reconstructed here, following P0083 display 18, which copies PP1993, and are
  marked QUESTION in the leaf docs.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMinor

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt
open LeanLab.Halupczok2012.Decomp398a

noncomputable section

/-! ## Notation of PP1993 p. 43 -/

/-- PP1993 p. 43, the window length `H = Y^(1/3+ε)`. -/
def Hs (Y ε : ℝ) : ℝ := Y ^ (1 / 3 + ε)

/-- PP1993 p. 43, the Farey order `Q = sqrt H / 2`, as in `arcBase`. -/
def Qs (Y ε : ℝ) : ℝ := Real.sqrt (Hs Y ε) / 2

/-- PP1993 p. 43, the major arc exponent `B = 3/ε (2A + 25)`, as in `majorArcs`. -/
def Bs (ε A : ℝ) : ℝ := 3 / ε * (2 * A + 25)

/-- PP1993 p. 43, the minor arcs `m`, the base interval minus the major arcs `M`. -/
def minorArcs (N Y ε A : ℝ) : Set ℝ := arcBase Y ε \ majorArcs N Y ε A

/-- PP1993 p. 44 display 3, the distance `‖x‖` to the nearest integer. -/
def nnd (x : ℝ) : ℝ := |x - round x|

/-- PP1993 p. 44 display 3, the kernel `min(H, 1/‖2θ‖)` of the sum over `n` of `e(2nθ)`.
At the null set where `‖2θ‖ = 0` Lean reads `1/0` as `0`; integrals are unaffected. -/
def kern (H θ : ℝ) : ℝ := min H (1 / nnd (2 * θ))

/-- PP1993 p. 44 display 3, the weighted minor arc integral of `|S2|^2` centred at `ξ`. -/
def weightedS2 (N Y ε A ξ : ℝ) : ℝ :=
  ∫ α in minorArcs N Y ε A, ‖secondPoly Y α‖ ^ 2 * kern (Hs Y ε) (α - ξ) ^ 2

/-- PP1993 p. 44 display 5, the integral of `|S2|^2` over `m` and the window `|α - ξ| ≤ 1/H`. -/
def localS2 (N Y ε A ξ : ℝ) : ℝ :=
  ∫ α in minorArcs N Y ε A ∩ Set.Icc (ξ - 1 / Hs Y ε) (ξ + 1 / Hs Y ε), ‖secondPoly Y α‖ ^ 2

/-- PP1993 p. 44 display 5 for one pair `ε, A`, uniformly in `ξ`. -/
def Display5 (ε A : ℝ) : Prop :=
  ∃ C N0 : ℝ, ∀ N Y : ℝ, N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∀ ξ : ℝ, localS2 N Y ε A ξ ≤ C * Y * Real.log N ^ (-(2 * A + 3))

/-- PP1993 p. 43, the Dirichlet arc `I_{q,a}`, centre `a/q` and half width `1/(qQ)`. -/
def fareyArc (Y ε : ℝ) (q a : ℕ) : Set ℝ :=
  Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * Qs Y ε)) ((a : ℝ) / q + 1 / ((q : ℝ) * Qs Y ε))

/-- PP1993 p. 46 display 14, the integral of `|S2|^2` over the punctured arc `I''_{q,a}`,
read as the arc `I_{q,a}` intersected with the minor arcs. -/
def arcS2 (N Y ε A : ℝ) (q a : ℕ) : ℝ :=
  ∫ α in fareyArc Y ε q a ∩ minorArcs N Y ε A, ‖secondPoly Y α‖ ^ 2

/-- PP1993 p. 43, `T2(η) = ∑_{j ≤ Y} e(jη)`. -/
def T2 (Y η : ℝ) : ℂ := ∑ j ∈ kRange 0 Y, phase ((j : ℝ) * η)

/-- PP1993 p. 43 and p. 47 display 15, `R2(η, q, a) = S2(a/q + η) - μ(q)/φ(q) T2(η)`. -/
def R2 (Y : ℝ) (q a : ℕ) (η : ℝ) : ℂ :=
  secondPoly Y ((a : ℝ) / q + η) -
    ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * T2 Y η

/-- PP1993 p. 43, `δ_χ`, equal to 1 for the principal character and 0 otherwise. -/
def deltaChi {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := if χ = 1 then 1 else 0

/-- PP1993 p. 43, `W2(η, χ) = ∑_{j ≤ Y} (Λ(j) χ(j) - δ_χ) e(jη)`. -/
def W2 (Y : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  ∑ j ∈ kRange 0 Y, ((Λ j : ℂ) * χ j - deltaChi χ) * phase ((j : ℝ) * η)

/-- PP1993 p. 47 display 21, the window sum `∑_{x < n ≤ x + h, n ≤ Y} (Λ(n) χ(n) - δ_χ)`. -/
def winSum (Y : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (x h : ℝ) : ℂ :=
  ∑ n ∈ Finset.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h) (kRange 0 Y),
    ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ)

/-- PP1993 p. 48 display 24, the untruncated sum `∑_{x < n ≤ x + Θx} (Λ(n) χ(n) - δ_χ)`. -/
def shortDelta {q : ℕ} (χ : DirichletCharacter ℂ q) (x Θ : ℝ) : ℂ :=
  ∑ n ∈ kRange x (Θ * x), ((Λ n : ℂ) * χ n - deltaChi χ)

/-- PP1993 p. 43, the nontrivial zeros `ρ` of `L(s, χ)` with `σ ≤ Re ρ` and `|Im ρ| ≤ T`. -/
def zeroSet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Set ℂ :=
  {ρ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- PP1993 p. 47 display 16, the width of the rectangle of bad zeros.
QUESTION: the note does not transcribe display 16. The width `B log L / L` is reconstructed
from P0083 display 18, which uses `10 B/ε log L / L` in the same argument. -/
def rectWidth (ε A N : ℝ) : ℝ := Bs ε A * Real.log (Real.log N) / Real.log N

/-- PP1993 p. 47 display 16, a bad character: `L(s, χ)` has a zero in the rectangle
`σ ≥ 1 - rectWidth`, `|t| ≤ Y`. -/
def badChar (N Y ε A : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ 1 - rectWidth ε A N ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ Y

/-! ## Display 3 and the window cover -/

/-- LEAF: PP1993 p. 44 display 3, Brun Titchmarsh input of the Cauchy Schwarz step.
Short interval upper bound `∑_{N-Y<h≤N} Λ(h) ≪ Y` for `Y ≥ N^(7/12+ε)`, and Chebyshev for S2.
Class HARD. PROVED by S135 in `B1btChebyshev`, from Mathlib's Chebyshev bounds and the lab's
proved Brun Titchmarsh `PNTPort.LargeSieve.brun_titchmarsh_montgomery`; no cited input remains.
Not in the note's list; split off from B1, see B1. -/
theorem leaf_B1_bt : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    (∑ h ∈ kRange (N - Y) Y, Λ h) ≤ c * Y ∧ (∑ j ∈ kRange 0 Y, Λ j) ≤ c * Y :=
  B1btChebyshev.leaf_B1_bt

/-- LEAF: PP1993 p. 44 display 3, Sigma_m is at most `(YL)^(3/2)` times the root of the
supremum over ξ of the weighted integral of `|S2|^2`. Class MEDIUM.
Cauchy Schwarz twice and Parseval for S1 and S2. The supremum is passed as a bound `M^2`.
The note proposes `Λ ≤ log` instead of Brun Titchmarsh; that loses `L^(3/2)` which cannot be
absorbed since the minor arcs depend on A, so the short interval bound with constant `c`
is a hypothesis here, supplied by `leaf_B1_bt`. -/
theorem leaf_B1 : ∃ C : ℝ, 0 < C ∧ ∀ ε A N Y c M : ℝ, 0 < ε → 0 < A → 3 ≤ N → 1 ≤ Y →
    Y ≤ N → 0 ≤ c → 0 ≤ M →
    (∑ h ∈ kRange (N - Y) Y, Λ h) ≤ c * Y → (∑ j ∈ kRange 0 Y, Λ j) ≤ c * Y →
    (∀ ξ : ℝ, weightedS2 N Y ε A ξ ≤ M ^ 2) →
    ∑ k ∈ kRange (N / 2) (Hs Y ε / 2), ‖arcCoeff N Y (2 * k) (minorArcs N Y ε A)‖ ^ 2 ≤
      C * (c * Y * Real.log N) ^ (3 / 2 : ℝ) * M := by
  sorry

/-! ### Helpers for the window cover, leaf B2, added by S135 -/

/-- `∑_{k ≤ K} 1/(k+1)^2 ≤ 2 - 1/(K+1)`. -/
theorem b2_sum_inv_sq (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => norm_num [Finset.sum_range_one]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have key : (1 : ℝ) / ((K : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

/-- PP1993 p. 44 after display 3, the window of a point: for `H ≥ 1` and every `θ` there is an
integer `j` with `|j| ≤ H`, `|θ - round(2θ)/2 - j/H| ≤ 1/H` and `0 ≤ kern H θ ≤ 2H/(1 + |j|)`. -/
theorem b2_window (H θ : ℝ) (hH : 1 ≤ H) :
    ∃ j : ℤ, |(j : ℝ)| ≤ H ∧ |θ - (round (2 * θ) : ℝ) / 2 - (j : ℝ) / H| ≤ 1 / H ∧
      0 ≤ kern H θ ∧ kern H θ ≤ 2 * H / (1 + |(j : ℝ)|) := by
  have hH0 : 0 < H := by linarith
  set t := 2 * θ with ht
  set s := (t - round t) / 2 with hs
  have hts : |t - round t| ≤ 1 / 2 := abs_sub_round t
  have hs4 : |s| ≤ 1 / 4 := by
    rw [hs, abs_div, abs_two]; linarith
  set j := round (H * s) with hj
  have hj2 : |H * s - j| ≤ 1 / 2 := abs_sub_round _
  have hjs : |(j : ℝ)| ≤ H * |s| + 1 / 2 := by
    have h := abs_sub_abs_le_abs_sub (j : ℝ) (H * s)
    rw [abs_sub_comm] at h
    rw [abs_mul, abs_of_pos hH0] at h
    linarith
  have hnnd : nnd t = 2 * |s| := by
    unfold nnd
    rw [hs, abs_div, abs_two]; ring
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · have : H * |s| ≤ H * (1 / 4) := mul_le_mul_of_nonneg_left hs4 hH0.le
    linarith
  · have e : θ - (round t : ℝ) / 2 - (j : ℝ) / H = (H * s - j) / H := by
      rw [hs, ht]; first | (field_simp; done) | (field_simp; ring)
    rw [e, abs_div, abs_of_pos hH0]
    exact div_le_div_of_nonneg_right (by linarith) hH0.le
  · unfold kern
    exact le_min hH0.le (div_nonneg zero_le_one (by rw [← ht]; unfold nnd; exact abs_nonneg _))
  · unfold kern
    rw [← ht, hnnd]
    by_cases hj0 : (j : ℝ) = 0
    · rw [hj0, abs_zero, add_zero, div_one]
      exact (min_le_left _ _).trans (by linarith)
    · have hj1 : 1 ≤ |(j : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (by exact_mod_cast hj0)
      have hspos : 0 < |s| := by
        by_contra hc
        push_neg at hc
        have : |s| = 0 := le_antisymm hc (abs_nonneg _)
        rw [this, mul_zero] at hjs
        linarith
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

set_option maxHeartbeats 1000000 in
/-- LEAF: PP1993 p. 44 sentence after display 3, display 5 for all ξ bounds the weighted
integral: cover by windows of length `2/H` around `ξ + j/H` and `ξ + 1/2 + j/H`, each with
weight at most `H^2 / (1 + |j|)^2`. Class MEDIUM. PROVED by S135 with `C = 144`: the points
of the minor arcs lie in `[0, 3]`, each lies in a window `ξ + n/2 + j/H` with `n` among nine
consecutive integers and `|j| ≤ ⌈H⌉`, where the kernel is at most `2H/(1 + |j|)`; the sum of
`4H^2/(1+|j|)^2` over the windows is at most `144 H^2`. -/
theorem leaf_B2 : ∃ C : ℝ, 0 < C ∧ ∀ ε A N Y V : ℝ, 0 < ε → 0 < A → 3 ≤ N → 1 ≤ Y →
    Y ≤ N → 0 ≤ V → (∀ ξ : ℝ, localS2 N Y ε A ξ ≤ V) →
    ∀ ξ : ℝ, weightedS2 N Y ε A ξ ≤ C * Hs Y ε ^ 2 * V := by
  refine ⟨144, by norm_num, ?_⟩
  intro ε A N Y V hε hA hN hY1 hYN hV hloc ξ
  have hH1 : 1 ≤ Hs Y ε := by unfold Hs; exact Real.one_le_rpow hY1 (by linarith)
  set H := Hs Y ε with hHdef
  have hH0 : 0 < H := by linarith
  set F : ℝ → ℝ := fun α => ‖secondPoly Y α‖ ^ 2 with hFdef
  have hFc : Continuous F := by
    rw [hFdef]; unfold secondPoly phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hF0 : ∀ α, 0 ≤ F α := fun α => by rw [hFdef]; positivity
  set m := minorArcs N Y ε A with hmdef
  have hm03 : m ⊆ Set.Icc 0 3 := by
    intro α hα
    have hb := hα.1
    simp only [arcBase, Set.mem_Icc] at hb
    have hsq : 1 ≤ Real.sqrt (Y ^ (1 / 3 + ε)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (Real.one_le_rpow hY1 (by linarith))
    have hQ : 0 < Real.sqrt (Y ^ (1 / 3 + ε)) / 2 := by positivity
    have h2 : 1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2) ≤ 2 := by
      rw [one_div_div]; exact div_le_self (by norm_num) hsq
    have h0 : 0 < 1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2) := by positivity
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  -- the windows
  set n0 : ℤ := ⌊-(2 * ξ)⌋ - 1 with hn0
  set J : ℕ := ⌈H⌉₊ with hJ
  set I : Finset (ℕ × ℕ × ℕ) := (Finset.range 9) ×ˢ (Finset.range 2) ×ˢ (Finset.range (J + 1))
    with hIdef
  set cen : ℕ × ℕ × ℕ → ℝ := fun i => ξ + ((n0 + (i.1 : ℤ) : ℤ) : ℝ) / 2 +
    (if i.2.1 = 0 then (i.2.2 : ℝ) else -(i.2.2 : ℝ)) / H with hcen
  set w : ℕ × ℕ × ℕ → ℝ := fun i => 4 * H ^ 2 / (1 + (i.2.2 : ℝ)) ^ 2 with hw
  set Wd : ℕ × ℕ × ℕ → Set ℝ := fun i => Set.Icc (cen i - 1 / H) (cen i + 1 / H) with hWd
  set K : Set ℝ := (Set.Icc (0 : ℝ) 3)ᶜ with hK
  set g : ℝ → ℝ := fun α => ∑ i ∈ I, w i * (Wd i).indicator F α + H ^ 2 * K.indicator F α
    with hg
  have hw0 : ∀ i, 0 ≤ w i := fun i => by rw [hw]; positivity
  have hind0 : ∀ (T : Set ℝ) α, 0 ≤ T.indicator F α :=
    fun T α => Set.indicator_nonneg (fun x _ => hF0 x) α
  -- pointwise bound
  have hpt : ∀ α, F α * kern H (α - ξ) ^ 2 ≤ g α := by
    intro α
    have hsum0 : 0 ≤ ∑ i ∈ I, w i * (Wd i).indicator F α :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (hind0 _ α))
    have h3 : 0 ≤ H ^ 2 * K.indicator F α := mul_nonneg (by positivity) (hind0 _ α)
    obtain ⟨j, hjH, hwin, hk0, hk⟩ := b2_window H (α - ξ) hH1
    by_cases hαK : α ∈ K
    · have hkH : kern H (α - ξ) ≤ H := min_le_left _ _
      have hk2 : kern H (α - ξ) ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hk0 hkH 2
      have : F α * kern H (α - ξ) ^ 2 ≤ H ^ 2 * K.indicator F α := by
        rw [Set.indicator_of_mem hαK, mul_comm (H ^ 2)]
        exact mul_le_mul_of_nonneg_left hk2 (hF0 α)
      simp only [hg]; linarith
    · have hα : α ∈ Set.Icc (0 : ℝ) 3 := by
        rw [hK, Set.mem_compl_iff, not_not] at hαK; exact hαK
      set nZ : ℤ := round (2 * (α - ξ)) with hnZ
      have hr : |2 * (α - ξ) - nZ| ≤ 1 / 2 := abs_sub_round _
      have hfl := Int.floor_le (-(2 * ξ))
      have hfl2 := Int.lt_floor_add_one (-(2 * ξ))
      have hlo : n0 < nZ := by
        have : ((n0 : ℤ) : ℝ) < (nZ : ℝ) := by
          rw [hn0]; push_cast
          linarith [(abs_le.mp hr).2, hα.1]
        exact_mod_cast this
      have hhi : nZ - n0 < 9 := by
        have : (nZ : ℝ) - (n0 : ℝ) < 9 := by
          rw [hn0]; push_cast
          linarith [(abs_le.mp hr).1, hα.2]
        exact_mod_cast this
      set i : ℕ × ℕ × ℕ := ((nZ - n0).toNat, (if 0 ≤ j then 0 else 1), j.natAbs) with hi
      have hcast : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      have hiI : i ∈ I := by
        rw [hi, hIdef, Finset.mem_product, Finset.mem_product, Finset.mem_range, Finset.mem_range,
          Finset.mem_range]
        refine ⟨by omega, by split_ifs <;> norm_num, ?_⟩
        have h1 : ((j.natAbs : ℕ) : ℝ) ≤ (J : ℝ) := by
          rw [hcast]; exact hjH.trans (Nat.le_ceil H)
        have h2 : j.natAbs ≤ J := by exact_mod_cast h1
        exact Nat.lt_succ_of_le h2
      have hsign : (if i.2.1 = 0 then (i.2.2 : ℝ) else -(i.2.2 : ℝ)) = (j : ℝ) := by
        rw [hi]
        by_cases hj0 : 0 ≤ j
        · simp only [hj0, if_true]
          rw [hcast, abs_of_nonneg (by exact_mod_cast hj0)]
        · simp only [hj0, if_false, one_ne_zero]
          rw [hcast, abs_of_neg (by exact_mod_cast (not_le.mp hj0))]; ring
      have hn : ((n0 + (i.1 : ℤ) : ℤ) : ℝ) = (nZ : ℝ) := by
        rw [hi]
        have : ((nZ - n0).toNat : ℤ) = nZ - n0 := Int.toNat_of_nonneg (by omega)
        simp only [this]
        push_cast; ring
      have hc : cen i = ξ + (nZ : ℝ) / 2 + (j : ℝ) / H := by
        rw [hcen]; simp only []; rw [hsign, hn]
      have hαW : α ∈ Wd i := by
        rw [hWd]; simp only [Set.mem_Icc]; rw [hc]
        have e : α - ξ - (nZ : ℝ) / 2 - (j : ℝ) / H = α - (ξ + (nZ : ℝ) / 2 + (j : ℝ) / H) := by
          ring
        rw [e] at hwin
        constructor <;> linarith [(abs_le.mp hwin).1, (abs_le.mp hwin).2]
      have hkw : kern H (α - ξ) ^ 2 ≤ w i := by
        rw [hw]; simp only []
        rw [hi]; simp only []
        rw [hcast]
        calc kern H (α - ξ) ^ 2 ≤ (2 * H / (1 + |(j : ℝ)|)) ^ 2 := pow_le_pow_left₀ hk0 hk 2
          _ = 4 * H ^ 2 / (1 + |(j : ℝ)|) ^ 2 := by rw [div_pow]; ring
      have h1 : F α * kern H (α - ξ) ^ 2 ≤ w i * (Wd i).indicator F α := by
        rw [Set.indicator_of_mem hαW, mul_comm (w i)]
        exact mul_le_mul_of_nonneg_left hkw (hF0 α)
      have h2 : w i * (Wd i).indicator F α ≤ ∑ i ∈ I, w i * (Wd i).indicator F α :=
        Finset.single_le_sum (f := fun i => w i * (Wd i).indicator F α)
          (fun i _ => mul_nonneg (hw0 i) (hind0 _ α)) hiI
      simp only [hg]; linarith
  -- integrability
  have hIcc : ∀ T : Set ℝ, MeasurableSet T → IntegrableOn (T.indicator F) m := fun T hT =>
    ((hFc.continuousOn.integrableOn_compact isCompact_Icc).indicator hT).mono_set hm03
  have hWm : ∀ i, MeasurableSet (Wd i) := fun i => measurableSet_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.compl
  have hgint : IntegrableOn g m := by
    rw [hg]
    exact (integrable_finsetSum _ (fun i _ => (hIcc _ (hWm i)).const_mul (w i))).add
      ((hIcc K hKm).const_mul _)
  -- the sum of the weights
  have hwsum : ∑ i ∈ I, w i ≤ 144 * H ^ 2 := by
    have hS : ∑ k ∈ Finset.range (J + 1), 4 * H ^ 2 / (1 + (k : ℝ)) ^ 2 ≤ 8 * H ^ 2 := by
      have := b2_sum_inv_sq J
      have hJ0 : 0 < 1 / ((J : ℝ) + 1) := by positivity
      calc ∑ k ∈ Finset.range (J + 1), 4 * H ^ 2 / (1 + (k : ℝ)) ^ 2
          = 4 * H ^ 2 * ∑ k ∈ Finset.range (J + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [add_comm (1 : ℝ) (k : ℝ)]; ring
        _ ≤ 4 * H ^ 2 * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        _ = 8 * H ^ 2 := by ring
    calc ∑ i ∈ I, w i = ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 2,
          ∑ k ∈ Finset.range (J + 1), 4 * H ^ 2 / (1 + (k : ℝ)) ^ 2 := by
          rw [hIdef, Finset.sum_product]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_product]
      _ = 9 * (2 * ∑ k ∈ Finset.range (J + 1), 4 * H ^ 2 / (1 + (k : ℝ)) ^ 2) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 144 * H ^ 2 := by nlinarith
  unfold weightedS2
  rw [← hHdef]
  change ∫ α in m, F α * kern H (α - ξ) ^ 2 ≤ 144 * H ^ 2 * V
  by_cases hfi : IntegrableOn (fun α => F α * kern H (α - ξ) ^ 2) m
  · have hint_eq : ∫ α in m, g α =
        ∑ i ∈ I, w i * localS2 N Y ε A (cen i) + H ^ 2 * 0 := by
      rw [hg, integral_add (integrable_finsetSum _ (fun i _ => (hIcc _ (hWm i)).const_mul (w i)))
        ((hIcc K hKm).const_mul _), integral_finsetSum _
          (fun i _ => (hIcc _ (hWm i)).const_mul (w i))]
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_const_mul, setIntegral_indicator (hWm i)]
        rfl
      · rw [integral_const_mul, setIntegral_indicator hKm]
        have : m ∩ K = ∅ := by
          ext α; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          intro hα hαK; exact hαK (hm03 hα)
        rw [this, Measure.restrict_empty, integral_zero_measure]
    calc ∫ α in m, F α * kern H (α - ξ) ^ 2 ≤ ∫ α in m, g α := integral_mono hfi hgint hpt
      _ = ∑ i ∈ I, w i * localS2 N Y ε A (cen i) + H ^ 2 * 0 := hint_eq
      _ ≤ ∑ i ∈ I, w i * V + H ^ 2 * 0 := by
          gcongr with i hi
          exact hloc _
      _ = (∑ i ∈ I, w i) * V := by rw [Finset.sum_mul]; ring
      _ ≤ 144 * H ^ 2 * V := mul_le_mul_of_nonneg_right hwsum hV
  · rw [integral_undef hfi]; positivity

/-! ## Section 5, displays 14 to 20 -/
theorem secondPoly_continuous (Y : ℝ) : Continuous (fun α => ‖secondPoly Y α‖ ^ 2) := by
  unfold secondPoly phase LeanLab.PNTPort.LargeSieve.e
  fun_prop

/-- A set integral of a nonnegative continuous function over a set covered by two bounded sets
is at most the sum of the two integrals. PROVED. -/
theorem setInt_union_le_aux {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {U s t : Set ℝ} {lo hi : ℝ} (hs : s ⊆ Set.Icc lo hi) (ht : t ⊆ Set.Icc lo hi)
    (hU : U ⊆ s ∪ t) :
    ∫ x in U, f x ≤ (∫ x in s, f x) + ∫ x in t, f x := by
  have hI : IntegrableOn f (Set.Icc lo hi) := hf.integrableOn_Icc
  have hIs : IntegrableOn f s := hI.mono_set hs
  have hIt : IntegrableOn f t := hI.mono_set ht
  have h1 : ∫ x in U, f x ≤ ∫ x in s ∪ t, f x :=
    setIntegral_mono_set (hIs.union hIt) (Filter.Eventually.of_forall hf0)
      (Filter.Eventually.of_forall hU)
  refine h1.trans ?_
  rw [← integral_add_measure hIs hIt]
  exact integral_mono_measure (Measure.restrict_union_le s t)
    (Filter.Eventually.of_forall hf0) (hIs.integrable.add_measure hIt)
/-- Dirichlet approximation on the base interval: `α` lies in an arc `I_{q,a}` with
`1 ≤ q ≤ Q`, a reduced and `a ≤ 2q`. PROVED. -/
theorem dirichlet_cover {Q α : ℝ} (hQ : 2 ≤ Q) (hα1 : 1 / Q ≤ α) (hα2 : α ≤ 1 + 1 / Q) :
    ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a.Coprime q ∧ a ≤ 2 * q ∧
      |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q) := by
  have hQ0 : 0 < Q := by linarith
  have hc : Q ≤ (⌈Q⌉₊ : ℝ) := Nat.le_ceil Q
  have hc2 : (⌈Q⌉₊ : ℝ) < Q + 1 := Nat.ceil_lt_add_one hQ0.le
  have hc1 : 2 ≤ ⌈Q⌉₊ := by
    have : (2 : ℝ) ≤ ⌈Q⌉₊ := hQ.trans hc
    exact_mod_cast this
  set n := ⌈Q⌉₊ - 1 with hn
  have hnpos : 0 < n := by omega
  have hn1 : ((n : ℝ) + 1) = ⌈Q⌉₊ := by
    rw [hn]; push_cast [show 1 ≤ ⌈Q⌉₊ by omega]; ring
  obtain ⟨r, hr1, hr2⟩ := Real.exists_rat_abs_sub_le_and_den_le α hnpos
  have hq1 : 1 ≤ r.den := r.den_pos
  have hqpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hqQ : (r.den : ℝ) ≤ Q := by
    have : (r.den : ℝ) ≤ n := by exact_mod_cast hr2
    linarith
  have hb : 1 / (((n : ℝ) + 1) * r.den) ≤ 1 / ((r.den : ℝ) * Q) := by
    rw [hn1]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hr : |α - r| ≤ 1 / ((r.den : ℝ) * Q) := hr1.trans hb
  have hw : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q := by
    apply one_div_le_one_div_of_le hQ0
    have : (1 : ℝ) ≤ r.den := by exact_mod_cast hq1
    nlinarith
  have hr0 : (0 : ℝ) ≤ r := by
    have := (abs_le.mp hr).2; linarith
  have hr0' : 0 ≤ r := by exact_mod_cast hr0
  have hnum : 0 ≤ r.num := Rat.num_nonneg.mpr hr0'
  have hcast : ((r.num.toNat : ℕ) : ℝ) / (r.den : ℝ) = (r : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum
    exact_mod_cast this
  refine ⟨r.den, r.num.toNat, hq1, hqQ, ?_, ?_, ?_⟩
  · have h := r.reduced
    have : r.num.natAbs = r.num.toNat := by omega
    rwa [this] at h
  · have hr2' : (r : ℝ) ≤ 2 := by
      have := (abs_le.mp hr).1
      have : 1 / Q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hQ
      linarith
    rw [← hcast, div_le_iff₀ hqpos] at hr2'
    exact_mod_cast hr2'
  · rw [hcast]; exact hr

/-- For `N ≥ 2^24` and `Y ≥ N^(7/12+ε)` the Farey order is at least 2. PROVED. -/
theorem Qs_ge_two {N Y ε : ℝ} (hε : 0 < ε) (hN : 2 ^ 24 ≤ N) (hY : N ^ (7 / 12 + ε) ≤ Y) :
    2 ≤ Qs Y ε := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have h1 : N ^ ((1 : ℝ) / 2) ≤ N ^ (7 / 12 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : (4096 : ℝ) ≤ N ^ ((1 : ℝ) / 2) := by
    have e : (4096 : ℝ) = (((4096 : ℝ) ^ (2 : ℕ)) ^ ((2 : ℕ) : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
    rw [e, show ((1 : ℝ) / 2) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_le_rpow (by positivity) (by norm_num at hN ⊢; linarith) (by norm_num)
  have hY4 : (4096 : ℝ) ≤ Y := h2.trans (h1.trans hY)
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY4
  have h3 : Y ^ ((1 : ℝ) / 3) ≤ Y ^ (1 / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have h4 : (16 : ℝ) ≤ Y ^ ((1 : ℝ) / 3) := by
    have e : (16 : ℝ) = (((16 : ℝ) ^ (3 : ℕ)) ^ ((3 : ℕ) : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
    rw [e, show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  have h5 : (16 : ℝ) ≤ Hs Y ε := h4.trans h3
  unfold Qs
  have : (4 : ℝ) ≤ Real.sqrt (Hs Y ε) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h5
  linarith

/-- `H = 4 Q^2`. PROVED. -/
theorem Hs_eq {Y : ℝ} (ε : ℝ) (hY : 0 ≤ Y) : Hs Y ε = 4 * Qs Y ε ^ 2 := by
  unfold Qs
  have h0 : 0 ≤ Hs Y ε := Real.rpow_nonneg hY _
  rw [div_pow, Real.sq_sqrt h0]; ring


/-- Statement of the next LEAF, PP1993 p. 46 display 14 and the lines above it, the Farey cover. Distinct centres
with `q ≤ Q` are at least `4/H` apart, so a window of length `2/H` meets at most two Farey
arcs, each inside some `I_{q,a}`. Class MEDIUM. -/
def StmtB3 : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → ∀ V : ℝ,
    (∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Qs Y ε → a.Coprime q → arcS2 N Y ε A q a ≤ V) →
    ∀ ξ : ℝ, localS2 N Y ε A ξ ≤ 2 * V

/-- LEAF: PP1993 p. 46 display 14, the Farey cover `StmtB3`. Class MEDIUM. PROVED. -/
theorem leaf_B3 : StmtB3 := by
  intro ε A hε hA
  refine ⟨2 ^ 24, ?_⟩
  intro N Y hN hY hYN V hV ξ
  have hQ2 : 2 ≤ Qs Y ε := Qs_ge_two hε hN hY
  have hY0 : 0 ≤ Y := le_trans (Real.rpow_nonneg (by linarith) _) hY
  set Q := Qs Y ε with hQdef
  have hH : Hs Y ε = 4 * Q ^ 2 := Hs_eq ε hY0
  have hQ0 : 0 < Q := by linarith
  set lo := ξ - 1 / Hs Y ε
  set hi := ξ + 1 / Hs Y ε
  let c : ℕ × ℕ → ℝ := fun p => (p.2 : ℝ) / p.1
  let w : ℕ × ℕ → ℝ := fun p => 1 / ((p.1 : ℝ) * Q)
  let valid : ℕ × ℕ → Prop := fun p => 1 ≤ p.1 ∧ (p.1 : ℝ) ≤ Q ∧ p.2.Coprime p.1 ∧ p.2 ≤ 2 * p.1
  let F : Finset (ℕ × ℕ) :=
    ((Finset.range (⌊Q⌋₊ + 1)) ×ˢ (Finset.range (2 * ⌊Q⌋₊ + 1))).filter valid
  have hF : ∀ p, valid p ↔ p ∈ F := by
    intro p
    constructor
    · intro hp
      have h1 : p.1 ≤ ⌊Q⌋₊ := Nat.le_floor hp.2.1
      simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by have := hp.2.2.2; omega⟩, hp⟩
    · intro hp
      exact (Finset.mem_filter.mp hp).2
  have harc : ∀ p : ℕ × ℕ, fareyArc Y ε p.1 p.2 = Set.Icc (c p - w p) (c p + w p) := by
    intro p; rfl
  have hwle : ∀ p, valid p → w p ≤ 1 / 2 := by
    intro p hp
    have h1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
    show 1 / ((p.1 : ℝ) * Q) ≤ 1 / 2
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hwge : ∀ p, valid p → 2 / Hs Y ε ≤ w p := by
    intro p hp
    have h1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
    have h2 : (p.1 : ℝ) ≤ Q := hp.2.1
    show 2 / Hs Y ε ≤ 1 / ((p.1 : ℝ) * Q)
    rw [hH, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcle : ∀ p, valid p → 0 ≤ c p ∧ c p ≤ 2 := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := by have : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1
                                  linarith
    refine ⟨by positivity, ?_⟩
    show (p.2 : ℝ) / p.1 ≤ 2
    rw [div_le_iff₀ h1]
    exact_mod_cast hp.2.2.2
  have harcsub : ∀ p, valid p →
      fareyArc Y ε p.1 p.2 ∩ minorArcs N Y ε A ⊆ Set.Icc (-1) 3 := by
    intro p hp x hx
    have hx' := hx.1
    rw [harc] at hx'
    have := hwle p hp
    have := hcle p hp
    have hw0 : 0 ≤ w p := by
      show 0 ≤ 1 / ((p.1 : ℝ) * Q)
      have : (0 : ℝ) ≤ p.1 := by positivity
      positivity
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  -- the cover
  have hcover : ∃ p1 p2, valid p1 ∧ valid p2 ∧
      minorArcs N Y ε A ∩ Set.Icc lo hi ⊆
        (fareyArc Y ε p1.1 p1.2 ∩ minorArcs N Y ε A) ∪
          (fareyArc Y ε p2.1 p2.2 ∩ minorArcs N Y ε A) := by
    have hdir : ∀ α ∈ minorArcs N Y ε A, ∃ p ∈ F, |α - c p| ≤ w p := by
      intro α hα
      have hb := hα.1
      simp only [arcBase, Set.mem_Icc] at hb
      have hb1 : 1 / Q ≤ α := hb.1
      have hb2 : α ≤ 1 + 1 / Q := hb.2
      obtain ⟨q, a, h1, h2, h3, h4, h5⟩ := dirichlet_cover hQ2 hb1 hb2
      exact ⟨(q, a), (hF (q, a)).mp ⟨h1, h2, h3, h4⟩, h5⟩
    by_cases hmid : ∃ p ∈ F, lo ≤ c p ∧ c p ≤ hi
    · obtain ⟨p, hpF, hp1, hp2⟩ := hmid
      have hp := (hF p).mpr hpF
      refine ⟨p, p, hp, hp, ?_⟩
      intro α hα
      left
      refine ⟨?_, hα.1⟩
      rw [harc]
      have hw := hwge p hp
      have h1 := hα.2.1
      have h2 := hα.2.2
      have : hi - lo = 2 / Hs Y ε := by simp only [hi, lo]; ring
      constructor <;> linarith
    · push Not at hmid
      have hL : ∃ pL, valid pL ∧ ∀ p ∈ F, c p < lo → (c pL < lo ∧ c p + w p ≤ c pL + w pL) := by
        by_cases hne : (F.filter (fun p => c p < lo)).Nonempty
        · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ (fun p => c p + w p) hne
          have hm' := Finset.mem_filter.mp hm
          refine ⟨m, (hF m).mpr hm'.1, fun p hp hcp => ⟨hm'.2, hmax p ?_⟩⟩
          exact Finset.mem_filter.mpr ⟨hp, hcp⟩
        · refine ⟨(1, 0), ⟨le_refl _, by push_cast; linarith, by norm_num, by norm_num⟩,
            fun p hp hcp => ?_⟩
          exact absurd ⟨p, Finset.mem_filter.mpr ⟨hp, hcp⟩⟩ hne
      have hR : ∃ pR, valid pR ∧ ∀ p ∈ F, hi < c p → (hi < c pR ∧ c pR - w pR ≤ c p - w p) := by
        by_cases hne : (F.filter (fun p => hi < c p)).Nonempty
        · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image _ (fun p => c p - w p) hne
          have hm' := Finset.mem_filter.mp hm
          refine ⟨m, (hF m).mpr hm'.1, fun p hp hcp => ⟨hm'.2, hmin p ?_⟩⟩
          exact Finset.mem_filter.mpr ⟨hp, hcp⟩
        · refine ⟨(1, 0), ⟨le_refl _, by push_cast; linarith, by norm_num, by norm_num⟩,
            fun p hp hcp => ?_⟩
          exact absurd ⟨p, Finset.mem_filter.mpr ⟨hp, hcp⟩⟩ hne
      obtain ⟨pL, hpL, hLmax⟩ := hL
      obtain ⟨pR, hpR, hRmin⟩ := hR
      refine ⟨pL, pR, hpL, hpR, ?_⟩
      intro α hα
      obtain ⟨p, hpF, hpα⟩ := hdir α hα.1
      have hab := abs_le.mp hpα
      have h1 := hα.2.1
      have h2 := hα.2.2
      by_cases hcl : c p < lo
      · obtain ⟨hcL, hle⟩ := hLmax p hpF hcl
        have hw0 : 0 ≤ w pL := by
          show 0 ≤ 1 / ((pL.1 : ℝ) * Q)
          have : (0 : ℝ) ≤ pL.1 := by positivity
          positivity
        left
        refine ⟨?_, hα.1⟩
        rw [harc]
        constructor <;> linarith
      · have hch : hi < c p := by
          by_contra hcon
          push Not at hcon hcl
          exact absurd (hmid p hpF hcl) (not_lt.mpr hcon)
        obtain ⟨hcR, hle⟩ := hRmin p hpF hch
        have hw0 : 0 ≤ w pR := by
          show 0 ≤ 1 / ((pR.1 : ℝ) * Q)
          have : (0 : ℝ) ≤ pR.1 := by positivity
          positivity
        right
        refine ⟨?_, hα.1⟩
        rw [harc]
        constructor <;> linarith
  obtain ⟨p1, p2, hp1, hp2, hsub⟩ := hcover
  have hV1 := hV p1.1 p1.2 hp1.1 hp1.2.1 hp1.2.2.1
  have hV2 := hV p2.1 p2.2 hp2.1 hp2.2.1 hp2.2.2.1
  unfold arcS2 at hV1 hV2
  unfold localS2
  have := setInt_union_le_aux (secondPoly_continuous Y) (fun x => by positivity)
    (harcsub p1 hp1) (harcsub p2 hp2) hsub
  linarith

/-! ### Helpers for display 15, leaf B4, added by S135 -/

/-- `n ≤ φ(n) d(n)`, from `∑_{d ∣ n} φ(d) = n` and `φ(d) ∣ φ(n)`. -/
theorem b4_le_totient_mul_card (n : ℕ) (hn : 1 ≤ n) :
    n ≤ n.totient * n.divisors.card := by
  calc n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors, n.totient := by
        apply Finset.sum_le_sum
        intro d hd
        exact Nat.le_of_dvd (Nat.totient_pos.2 (by omega))
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = n.divisors.card * n.totient := by rw [Finset.sum_const, smul_eq_mul]
    _ = n.totient * n.divisors.card := mul_comm _ _

/-- The number of divisors of `n` is at most `2 √n`. -/
theorem b4_card_divisors_le (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
  set S := n.divisors.filter (fun d => d * d ≤ n) with hSdef
  have hsub : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
    intro d hd
    rw [Finset.mem_union]
    by_cases h : d * d ≤ n
    · exact Or.inl (Finset.mem_filter.2 ⟨hd, h⟩)
    · right
      have hn0 : n ≠ 0 := (Nat.mem_divisors.1 hd).2
      obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have he0 : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · rw [h0, mul_zero] at he; exact absurd he hn0
        · exact h0
      have hed : e < d := by
        by_contra hc
        push_neg at hc
        apply h
        rw [he]
        exact Nat.mul_le_mul_left d hc
      refine Finset.mem_image.2 ⟨e, Finset.mem_filter.2
        ⟨Nat.mem_divisors.2 ⟨⟨d, by rw [he]; ring⟩, hn0⟩, ?_⟩, ?_⟩
      · rw [he]; exact Nat.mul_le_mul_right e hed.le
      · rw [he]; exact Nat.mul_div_cancel d he0
  have hS : S ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro d hd
    rw [hSdef, Finset.mem_filter] at hd
    exact Finset.mem_Icc.2 ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_sqrt.2 hd.2⟩
  have h1 : n.divisors.card ≤ 2 * Nat.sqrt n := by
    have hc := Finset.card_le_card hS
    rw [Nat.card_Icc] at hc
    calc n.divisors.card ≤ (S ∪ S.image (fun d => n / d)).card := Finset.card_le_card hsub
      _ ≤ S.card + (S.image (fun d => n / d)).card := Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
      _ ≤ 2 * Nat.sqrt n := by omega
  calc (n.divisors.card : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 2 * (Nat.sqrt n : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt n := by
        have := Real.nat_sqrt_le_real_sqrt (a := n)
        linarith

/-- `n ≤ 4 φ(n)^2`, the crude lower bound for `φ` used for the large moduli of display 15. -/
theorem b4_le_four_totient_sq (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ≤ 4 * (n.totient : ℝ) ^ 2 := by
  have h1 : (n : ℝ) ≤ n.totient * n.divisors.card := by exact_mod_cast b4_le_totient_mul_card n hn
  have h2 := b4_card_divisors_le n
  have hφ : (0 : ℝ) ≤ n.totient := by positivity
  have h3 : (n : ℝ) ≤ n.totient * (2 * Real.sqrt n) := h1.trans (mul_le_mul_of_nonneg_left h2 hφ)
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h4 : Real.sqrt n ≤ 2 * n.totient := by
    by_contra hc
    push_neg at hc
    have : (n.totient : ℝ) * (2 * Real.sqrt n) < Real.sqrt n * Real.sqrt n := by nlinarith
    linarith
  nlinarith

/-- Translation of a set integral by `c`. -/
theorem b4_translate (F : ℝ → ℝ) (c : ℝ) (K : Set ℝ) :
    ∫ α in (fun α => α - c) ⁻¹' K, F (α - c) = ∫ η in K, F η :=
  (measurePreserving_sub_right volume c).setIntegral_preimage_emb
    (Homeomorph.subRight c).measurableEmbedding F K

/-- Statement of the next LEAF, PP1993 p. 47 display 15, the term `μ(q)/φ(q) T2` of `S2 = μ/φ T2 + R2` contributes
`O(Y L^(-2A-3))` on `I''_{q,a}`: `|T2(η)| ≤ 1/(2‖η‖)` with `|η| ≥ L^(2B)/(qY)` for
`q ≤ L^B`, Parseval and `φ(q) ≥ L^B / log L` for larger q. Class MEDIUM. -/
def StmtB4 : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Qs Y ε →
    a.Coprime q →
    ∫ α in fareyArc Y ε q a ∩ minorArcs N Y ε A,
      ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * T2 Y (α - (a : ℝ) / q)‖ ^ 2 ≤
      C * Y * Real.log N ^ (-(2 * A + 3))

set_option maxHeartbeats 1000000 in
/-- LEAF: PP1993 p. 47 display 15, `StmtB4`. Class MEDIUM. PROVED by S135: for `q ≤ L^B` and
`1 ≤ a ≤ q` the minor part of the arc has `|η| ≥ L^(2B)/(qY)`, so `|T2(η)| ≤ 1/(2|η|)` gives
`O(Y L^(-B))`; for `q > L^B` Parseval and `q ≤ 4 φ(q)^2` give `O(Y L^(-B))`; the remaining
residues `a = 0` and `a > q` meet the base interval in at most one point. `B ≥ 2A + 3`. -/
theorem leaf_B4 : StmtB4 := by
  intro ε A hε hA
  set B := 3 / ε * (2 * A + 25) with hBdef
  have hB0 : 0 < B := by positivity
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    (((Split398aMajor.log_rpow_le_eventually (2 * B) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)).and
      (Split398aMajor.log_rpow_le_eventually B (show (0 : ℝ) < 7 / 72 by norm_num)
      (show (0 : ℝ) < 1 / 8 by norm_num))).and
      ((Filter.eventually_ge_atTop (Real.exp 1)).and (Filter.eventually_ge_atTop (2 ^ 24 : ℝ))))
  refine ⟨8, N1, ?_⟩
  intro N Y hN hY hYN q a hq1 hqQ hcop
  obtain ⟨⟨hw2, hLB⟩, hNe, hN24⟩ := hN1 N hN
  have hN1' : 1 ≤ N := le_trans (by norm_num) hN24
  have hNpos : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hL0 : 0 < L := by linarith
  have hP : N ^ ((7 : ℝ) / 12) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)).trans hY
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hN1' (by norm_num)).trans hP
  have hY0 : 0 < Y := by linarith
  have hε5 : ε ≤ 5 / 12 := by
    by_contra hc
    push_neg at hc
    have h1 : N ^ (1 : ℝ) < N ^ (7 / 12 + ε) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    rw [Real.rpow_one] at h1
    linarith
  have hBA : 2 * A + 3 ≤ B := by
    rw [hBdef]
    have : (1 : ℝ) ≤ 3 / ε := by rw [le_div_iff₀ hε]; linarith
    nlinarith
  have hLBpos : 0 < L ^ B := Real.rpow_pos_of_pos hL0 _
  have hLBA : L ^ (-B) ≤ L ^ (-(2 * A + 3)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLnegB : L ^ (-B) = 1 / L ^ B := by rw [Real.rpow_neg hL0.le, one_div]
  have hL2B : L ^ (2 * B) = L ^ B * L ^ B := by
    rw [two_mul, Real.rpow_add hL0]
  have hRHS0 : 0 ≤ 8 * Y * L ^ (-(2 * A + 3)) := by positivity
  set Q := Qs Y ε with hQdef
  have hQ2 : 2 ≤ Q := Qs_ge_two hε hN24 hY
  have hQ0 : 0 < Q := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqQ1 : 1 / ((q : ℝ) * Q) ≤ 1 / 2 := by
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  set c : ℝ := (a : ℝ) / q with hcdef
  set m : ℂ := (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) with hmdef
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hm : ‖m‖ ≤ 1 / (q.totient : ℝ) := by
    rw [hmdef, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hm0 : 0 ≤ ‖m‖ := norm_nonneg _
  have hm1 : ‖m‖ ≤ 1 := hm.trans (by rw [div_le_one (by linarith)]; exact hφ1)
  set F : ℝ → ℝ := fun η => ‖m‖ ^ 2 * ‖T2 Y η‖ ^ 2 with hFdef
  have hT2c : Continuous (fun η => T2 Y η) := by
    unfold T2 phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hFc : Continuous F := by rw [hFdef]; fun_prop
  have hfun : (fun α => ‖m * T2 Y (α - c)‖ ^ 2) = fun α => F (α - c) := by
    funext α; rw [hFdef, norm_mul, mul_pow]
  change ∫ α in fareyArc Y ε q a ∩ minorArcs N Y ε A, ‖m * T2 Y (α - c)‖ ^ 2 ≤ _
  rw [hfun]
  set S := fareyArc Y ε q a ∩ minorArcs N Y ε A with hSdef
  -- membership facts for α in S
  have hSfar : ∀ α ∈ S, |α - c| ≤ 1 / ((q : ℝ) * Q) := by
    intro α hα
    have h := hα.1
    simp only [fareyArc, Set.mem_Icc] at h
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  -- the general bound through a measurable compact `K` containing the shifted set
  have hgen : ∀ K : Set ℝ, IsCompact K → (∀ α ∈ S, α - c ∈ K) →
      ∫ α in S, F (α - c) ≤ ∫ η in K, F η := by
    intro K hK hSK
    have hTc : IsCompact ((fun α => α - c) ⁻¹' K) :=
      (Homeomorph.subRight c).isCompact_preimage.2 hK
    have hint : IntegrableOn (fun α => F (α - c)) ((fun α => α - c) ⁻¹' K) volume :=
      (hFc.comp (continuous_sub_right c)).continuousOn.integrableOn_compact hTc
    calc ∫ α in S, F (α - c) ≤ ∫ α in (fun α => α - c) ⁻¹' K, F (α - c) :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => by positivity)
            (Filter.Eventually.of_forall fun α hα => hSK α hα)
      _ = ∫ η in K, F η := b4_translate F c K
  have hFK : ∀ K : Set ℝ, MeasurableSet K →
      ∫ η in K, F η = ‖m‖ ^ 2 * ∫ η in K, ‖T2 Y η‖ ^ 2 := by
    intro K _
    rw [hFdef]; exact integral_const_mul _ _
  by_cases hbig : L ^ B < q
  · -- large moduli: Parseval
    have hK : ∀ α ∈ S, α - c ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      intro α hα
      have := (hSfar α hα).trans hqQ1
      exact ⟨by linarith [(abs_le.mp this).1], by linarith [(abs_le.mp this).2]⟩
    refine (hgen _ isCompact_Icc hK).trans ?_
    rw [hFK _ measurableSet_Icc]
    have hpar : ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖T2 Y η‖ ^ 2 ≤ Y + 1 :=
      Split398aMajor.parseval_window 0 Y hY0.le subset_rfl
    have hφq : (q : ℝ) ≤ 4 * (q.totient : ℝ) ^ 2 := b4_le_four_totient_sq q hq1
    have hm2 : ‖m‖ ^ 2 ≤ 4 / (q : ℝ) := by
      calc ‖m‖ ^ 2 ≤ (1 / (q.totient : ℝ)) ^ 2 := pow_le_pow_left₀ hm0 hm 2
        _ = 1 / (q.totient : ℝ) ^ 2 := by rw [one_div_pow]
        _ ≤ 4 / (q : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hq0]; linarith
    have h4q : 4 / (q : ℝ) ≤ 4 * L ^ (-B) := by
      rw [hLnegB, mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) hLBpos hbig.le
    have hI0 : 0 ≤ ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖T2 Y η‖ ^ 2 :=
      setIntegral_nonneg measurableSet_Icc (fun _ _ => by positivity)
    calc ‖m‖ ^ 2 * ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖T2 Y η‖ ^ 2
        ≤ (4 * L ^ (-B)) * (Y + 1) := mul_le_mul (hm2.trans h4q) hpar hI0 (by positivity)
      _ ≤ (4 * L ^ (-(2 * A + 3))) * (2 * Y) := by
          apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = 8 * Y * L ^ (-(2 * A + 3)) := by ring
  push_neg at hbig
  by_cases hagood : 1 ≤ a ∧ a ≤ q
  · -- small moduli, a reduced residue: the arc minus the major arc
    set w := L ^ (2 * B) / ((q : ℝ) * Y) with hwdef
    have hW : 0 < L ^ (2 * B) := Real.rpow_pos_of_pos hL0 _
    have hw0 : 0 < w := by rw [hwdef]; positivity
    have hw : w ≤ 1 / 2 := by
      rw [hwdef, div_le_iff₀ (by positivity)]
      have hqY : Y ≤ (q : ℝ) * Y := le_mul_of_one_le_left hY0.le (by exact_mod_cast hq1)
      nlinarith
    have hK : ∀ α ∈ S, α - c ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w := by
      intro α hα
      have h1 := (hSfar α hα).trans hqQ1
      refine ⟨⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩, ?_⟩
      rintro ⟨hlo, hhi⟩
      have hmin := hα.2
      simp only [minorArcs, Set.mem_diff] at hmin
      apply hmin.2
      refine ⟨hmin.1, q, a, hq1, ?_, hagood.1, hagood.2, hcop, ?_⟩
      · exact hbig
      · rw [abs_lt]; exact ⟨hlo, hhi⟩
    have hKc : IsCompact (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w) :=
      isCompact_Icc.diff isOpen_Ioo
    have hKm : MeasurableSet (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w) :=
      measurableSet_Icc.diff measurableSet_Ioo
    refine (hgen _ hKc hK).trans ?_
    rw [hFK _ hKm]
    have hpt : ∀ η ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w,
        ‖T2 Y η‖ ^ 2 ≤ 1 / (4 * η ^ 2) := by
      intro η hη
      have habs1 : |η| ≤ 1 / 2 := abs_le.mpr ⟨hη.1.1, hη.1.2⟩
      have habs0 : w ≤ |η| := by
        by_contra hc
        rw [not_le, abs_lt] at hc
        exact hη.2 hc
      have hpos : 0 < |η| := by linarith
      have b2 := Split398aMajor.window_bound 0 Y le_rfl hY0.le hpos habs1
      have hT : ‖T2 Y η‖ ≤ 1 / (2 * |η|) := b2
      calc ‖T2 Y η‖ ^ 2 ≤ (1 / (2 * |η|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
        _ = 1 / (4 * η ^ 2) := by
            rw [show η ^ 2 = |η| ^ 2 from (sq_abs η).symm]; field_simp; ring
    have hint2 : IntegrableOn (fun η : ℝ => 1 / (4 * η ^ 2))
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w) := by
      apply ContinuousOn.integrableOn_compact hKc
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx
      have : w ≤ |x| := by
        by_contra hc
        rw [not_le, abs_lt] at hc
        exact hx.2 hc
      have : x ≠ 0 := by intro h0; rw [h0, abs_zero] at this; linarith
      positivity
    have hTi : IntegrableOn (fun η => ‖T2 Y η‖ ^ 2)
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w) :=
      (hT2c.norm.pow 2).continuousOn.integrableOn_compact hKc
    have hI : ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w, ‖T2 Y η‖ ^ 2 ≤
        1 / (2 * w) :=
      (setIntegral_mono_on hTi hint2 hKm hpt).trans (Split398aMajor.tail_integral hw0 hw)
    have hI0 : 0 ≤ ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w, ‖T2 Y η‖ ^ 2 :=
      setIntegral_nonneg hKm (fun _ _ => by positivity)
    have hm2 : ‖m‖ ^ 2 ≤ 1 := by nlinarith
    have hw' : 1 / (2 * w) ≤ Y * L ^ (-B) / 2 := by
      have hqne : (q : ℝ) ≠ 0 := hq0.ne'
      have hYne : Y ≠ 0 := hY0.ne'
      have hLne : L ^ B ≠ 0 := hLBpos.ne'
      have e1 : 1 / (2 * w) = (q : ℝ) * Y / (2 * (L ^ B * L ^ B)) := by
        rw [hwdef, hL2B]
        first | (field_simp; done) | (field_simp; ring)
      have e2 : L ^ B * Y / (2 * (L ^ B * L ^ B)) = Y * L ^ (-B) / 2 := by
        rw [hLnegB]
        first | (field_simp; done) | (field_simp; ring)
      rw [e1, ← e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hbig hY0.le
    generalize hIg : (∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w, ‖T2 Y η‖ ^ 2) = I
      at hI hI0 ⊢
    have hIb : I ≤ Y * L ^ (-B) / 2 := hI.trans hw'
    have hmI : ‖m‖ ^ 2 * I ≤ 1 * I := mul_le_mul_of_nonneg_right hm2 hI0
    have h3 : Y * L ^ (-B) ≤ Y * L ^ (-(2 * A + 3)) :=
      mul_le_mul_of_nonneg_left hLBA hY0.le
    have h4 : 0 ≤ Y * L ^ (-(2 * A + 3)) := by positivity
    linarith
  · -- a = 0 or a > q: the arc meets the base interval in at most the point 1/Q
    have hsing : S ⊆ {1 / Q} := by
      intro α hα
      have hfa := hα.1
      have hbase := hα.2.1
      simp only [fareyArc, Set.mem_Icc] at hfa
      simp only [arcBase, Set.mem_Icc] at hbase
      have hQe : Real.sqrt (Y ^ (1 / 3 + ε)) / 2 = Q := rfl
      rw [hQe] at hbase
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · -- a = 0 forces q = 1
        have hq : q = 1 := by rw [ha0] at hcop; exact Nat.coprime_zero_left q |>.mp hcop
        subst hq
        rw [ha0] at hfa
        simp only [Nat.cast_zero, Nat.cast_one, zero_div, zero_add, one_mul] at hfa
        exact le_antisymm hfa.2 hbase.1
      · exfalso
        have haq : q + 1 ≤ a := by
          by_contra hc; push_neg at hc; exact hagood ⟨hapos, by omega⟩
        have haq' : ((q : ℝ) + 1) ≤ a := by exact_mod_cast haq
        -- Q ≥ N^(7/72)/2 > 2 L^B ≥ 2 q, so q < Q - 1
        have hQlow : N ^ ((7 : ℝ) / 72) / 2 ≤ Q := by
          rw [hQdef]; unfold Qs Hs
          have h1 : Y ^ ((1 : ℝ) / 3) ≤ Y ^ (1 / 3 + ε) :=
            Real.rpow_le_rpow_of_exponent_le hY1 (le_add_of_nonneg_right hε.le)
          have h2 : N ^ ((7 : ℝ) / 36) ≤ Y ^ ((1 : ℝ) / 3) := by
            rw [show ((7 : ℝ) / 36) = 7 / 12 * (1 / 3) by norm_num, Real.rpow_mul hNpos.le]
            exact Real.rpow_le_rpow (by positivity) hP (by norm_num)
          have h3 : N ^ ((7 : ℝ) / 72) = Real.sqrt (N ^ ((7 : ℝ) / 36)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]; norm_num
          rw [h3]
          have h4 := Real.sqrt_le_sqrt (h2.trans h1)
          linarith only [h4]
        have hqsmall : (q : ℝ) ≤ 1 / 8 * N ^ ((7 : ℝ) / 72) := hbig.trans hLB
        have hNp : 0 < N ^ ((7 : ℝ) / 72) := Real.rpow_pos_of_pos hNpos _
        have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
        have hlt : (q : ℝ) < Q - 1 := by linarith only [hq1r, hqsmall, hQlow]
        -- from the two intervals: (q+1)/q - 1/(qQ) ≤ α ≤ 1 + 1/Q
        have hle : (a : ℝ) / q - 1 / ((q : ℝ) * Q) ≤ 1 + 1 / Q := hfa.1.trans hbase.2
        have hge : ((q : ℝ) + 1) / q ≤ (a : ℝ) / q := div_le_div_of_nonneg_right haq' hq0.le
        have key : ((q : ℝ) + 1) / q - 1 / ((q : ℝ) * Q) ≤ 1 + 1 / Q := by linarith
        have hqne : (q : ℝ) ≠ 0 := hq0.ne'
        have hQne : Q ≠ 0 := hQ0.ne'
        have hid : ((q : ℝ) + 1) / q - 1 / ((q : ℝ) * Q) - (1 + 1 / Q) =
            (Q - 1 - q) / ((q : ℝ) * Q) := by
          first | (field_simp; done) | (field_simp; ring)
        have hpos : 0 < (Q - 1 - q) / ((q : ℝ) * Q) :=
          div_pos (by linarith only [hlt]) (by positivity)
        linarith only [key, hid, hpos]
    have hnull : volume S = 0 := measure_mono_null hsing (Real.volume_singleton)
    rw [setIntegral_measure_zero _ hnull]
    exact hRHS0

/-- PP1993 p. 47 display 15, the splitting `S2(a/q + η) = μ(q)/φ(q) T2(η) + R2(η, q, a)`.
PROVED, by the definition of R2. -/
theorem display15_split (Y : ℝ) (q a : ℕ) (η : ℝ) :
    secondPoly Y ((a : ℝ) / q + η) =
      ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) * T2 Y η + R2 Y q a η := by
  unfold R2; ring

/-- PP1993 p. 47 displays 16 and 17, the hypothesis form of `leaf_B5`. -/
def ZeroFreeHyp : Prop :=
  ∀ ε' c0 : ℝ, 0 < ε' → 0 < c0 → ∃ c N0 : ℝ, 0 < c ∧ ∀ N : ℝ, N0 ≤ N →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      χ.LFunction ρ = 0 → 1 - c0 * Real.log (Real.log N) / Real.log N ≤ ρ.re → ρ.re < 1 →
      |ρ.im| ≤ N → c * Real.log N ^ (1 / (2 * ε')) ≤ q

/-- LEAF: PP1993 p. 47 displays 16 and 17, zero free region with Siegel's theorem: a zero of
`L(s, χ)`, χ mod q, in the rectangle forces `q ≥ c L^(1/(2ε'))`. Stated for every width
constant `c0` of a rectangle `σ ≥ 1 - c0 log L / L`, `|t| ≤ N`, which covers display 16 under
the reconstruction of `rectWidth`. Class HARD. Citation wall: Prachar 1957 ch. 8, ref 7,
papers/Prachar1957-ch8.pdf, the region with `log^(4/5)`, and Siegel's theorem, ineffective. -/
theorem leaf_B5 : ZeroFreeHyp := by
  sorry

/-- PP1993 p. 47 display 18, the density estimate in hypothesis form. -/
def DensityHyp : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ →
    σ ≤ 1 → ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
      (∀ χ ρ, ρ ∈ Z χ → χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        C * ((q : ℝ) * T) ^ ((12 / 5 + δ) * (1 - σ)) * Real.log ((q : ℝ) * T) ^ 14

/-- LEAF: PP1993 p. 47 display 18, `∑_{χ mod q} N(σ, T, χ) ≪ (qT)^((12/5+δ)(1-σ)) log^14 qT`.
Class HARD. Citation wall: Montgomery LNM 227 Theorem 12.1, ref 3,
papers/Montgomery1971-LNM227.pdf, and Huxley 1975, ref 2, papers/Huxley1975-AA26.pdf. -/
theorem leaf_B6 : DensityHyp := by
  sorry

/-- Statement of the next LEAF, PP1993 p. 47 display 19, the conclusion: at most `L^(6B)` bad characters mod q
for every `q ≤ Q`. Class MEDIUM. -/
def StmtB7 : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Qs Y ε →
    ((univ.filter (fun χ : DirichletCharacter ℂ q => badChar N Y ε A χ)).card : ℝ) ≤
      Real.log N ^ (6 * Bs ε A)

/-- PP1993 p. 47 display 19, a zero of `L(s, χ)` other than `s = 1` has multiplicity at
least 1. Same proof as `Perelli1996.Decomp582a.lfunction_zero_order_pos`. -/
theorem zero_order_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hz : χ.LFunction ρ = 0) (hρ : ρ ≠ 1) :
    1 ≤ analyticOrderNatAt χ.LFunction ρ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (χ.differentiableAt_LFunction z (Or.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (1 : ℂ)).isPreconnected
  have ht : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    apply ha.analyticOrderAt_ne_top_of_isPreconnected hconn
      (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hρ
    simp [(ha 2 (by norm_num)).analyticOrderAt_eq_zero.mpr
      (χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num))]
  have hn : analyticOrderAt χ.LFunction ρ ≠ 0 :=
    (ha ρ hρ).analyticOrderAt_ne_zero.mpr hz
  simp only [Nat.one_le_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨hn, ht⟩

/-- PP1993 p. 47 display 19, the bad characters mod q are counted by a finite zero family. -/
theorem bad_card_le_family {q : ℕ} [NeZero q] (N Y ε A : ℝ) :
    ∃ Z : DirichletCharacter ℂ q → Finset ℂ,
      (∀ χ ρ, ρ ∈ Z χ → χ.LFunction ρ = 0 ∧ 1 - rectWidth ε A N ≤ ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ Y) ∧
      ((univ.filter (fun χ : DirichletCharacter ℂ q => badChar N Y ε A χ)).card : ℝ) ≤
        ∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ) := by
  set S := univ.filter (fun χ : DirichletCharacter ℂ q => badChar N Y ε A χ)
  have hex : ∀ χ : DirichletCharacter ℂ q, ∃ ρ : ℂ, χ ∈ S → χ.LFunction ρ = 0 ∧
      1 - rectWidth ε A N ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ Y := by
    intro χ
    by_cases hχ : χ ∈ S
    · obtain ⟨ρ, hρ⟩ := (mem_filter.mp hχ).2
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨0, fun h => (hχ h).elim⟩
  choose r hr using hex
  let Z : DirichletCharacter ℂ q → Finset ℂ := fun χ => if χ ∈ S then {r χ} else ∅
  refine ⟨Z, ?_, ?_⟩
  · intro χ ρ hρ
    by_cases hχ : χ ∈ S
    · have he : ρ = r χ := by simpa [Z, hχ] using hρ
      subst ρ
      exact hr χ hχ
    · simp [Z, hχ] at hρ
  · have heq : (∑ χ : DirichletCharacter ℂ q,
        ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
        ∑ χ ∈ S, (analyticOrderNatAt χ.LFunction (r χ) : ℝ) := by
      have hi (χ : DirichletCharacter ℂ q) :
          (∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) =
            if χ ∈ S then (analyticOrderNatAt χ.LFunction (r χ) : ℝ) else 0 := by
        by_cases hχ : χ ∈ S <;> simp [Z, hχ]
      simp_rw [hi]
      exact Finset.sum_ite_mem_eq S _
    rw [heq]
    calc (S.card : ℝ) = ∑ χ ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ χ ∈ S, (analyticOrderNatAt χ.LFunction (r χ) : ℝ) := by
        apply Finset.sum_le_sum
        intro χ hχ
        have hh := hr χ hχ
        have hne : r χ ≠ 1 := by
          intro he
          have := hh.2.2.1
          simp [he] at this
        exact_mod_cast zero_order_pos χ hh.1 hne

/-- LEAF: PP1993 p. 47 display 19, the number of bad characters, from display 18 at
`σ = 1 - rectWidth`, `T = Y`. Class MEDIUM, given B6. PROVED, CONDITIONAL ON B6. -/
theorem leaf_B7 (hD : DensityHyp) : StmtB7 := by
  intro ε A hε hA
  obtain ⟨C, hC, hdens⟩ := hD (1 / 10) (by norm_num)
  set B := Bs ε A with hBdef
  refine ⟨max (Real.exp (C * 2 ^ 14 + 16 * B ^ 2 + 1)) 3, ?_⟩
  intro N Y hN hlow hYN q _ hqQ
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  have hNe : Real.exp (C * 2 ^ 14 + 16 * B ^ 2 + 1) ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hL
  have hLbig : C * 2 ^ 14 + 16 * B ^ 2 + 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hN0]; exact hNe
  have hB0 : 0 < B := by rw [hBdef, Bs]; positivity
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg B]
  have hL0 : 0 < L := by linarith
  -- ε ≤ 5/12
  have hexp : 7 / 12 + ε ≤ 1 := by
    have h1 : N ^ (7 / 12 + ε) ≤ N ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hlow.trans hYN
    exact (Real.rpow_le_rpow_left_iff (by linarith)).mp h1
  have hB15 : 15 ≤ B := by
    rw [hBdef, Bs, div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
  -- Y bounds
  have hY1 : 1 ≤ Y := (Real.one_le_rpow (by linarith) (by linarith)).trans hlow
  have hY2 : 2 ≤ Y := by
    have hN16 : 16 ≤ N := by
      have := Real.add_one_le_exp (C * 2 ^ 14 + 16 * B ^ 2 + 1)
      nlinarith [sq_nonneg B]
    have h1 : N ^ (7 / 12 : ℝ) ≤ N ^ (7 / 12 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (16 : ℝ) ^ (7 / 12 : ℝ) ≤ N ^ (7 / 12 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hN16 (by norm_num)
    have h3 : (2 : ℝ) ≤ 16 ^ (7 / 12 : ℝ) := by
      have e : (16 : ℝ) ^ (7 / 12 : ℝ) = 2 ^ (7 / 3 : ℝ) := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [e]
      have h4 : (2 : ℝ) ^ (1 : ℝ) ≤ 2 ^ (7 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using h4
    linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  -- q ≤ N
  have hqN : (q : ℝ) ≤ N := by
    have hH1 : 1 ≤ Hs Y ε := Real.one_le_rpow hY1 (by linarith)
    have hHY : Hs Y ε ≤ Y := by
      unfold Hs
      calc Y ^ (1 / 3 + ε) ≤ Y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
        _ = Y := Real.rpow_one Y
    have hs : Real.sqrt (Hs Y ε) ≤ Hs Y ε := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have : Qs Y ε ≤ Hs Y ε := by
      unfold Qs; linarith [Real.sqrt_nonneg (Hs Y ε)]
    linarith
  -- the width
  set w := rectWidth ε A N with hw
  have hll : Real.log L ≤ 2 * Real.sqrt L := by
    have := Real.log_le_rpow_div (x := L) hL0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this; linarith
  have hll0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hw0 : 0 ≤ w := by rw [hw, rectWidth]; positivity
  have hsqL : 4 * B ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by positivity) hL0.le]; nlinarith
  have hw12 : w ≤ 1 / 2 := by
    rw [hw, rectWidth, div_le_iff₀ hL0]
    have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    have : B * Real.log L ≤ B * (2 * Real.sqrt L) := mul_le_mul_of_nonneg_left hll hB0.le
    nlinarith [Real.sqrt_nonneg L]
  obtain ⟨Z, hZ, hcard⟩ := bad_card_le_family (q := q) N Y ε A
  have hb := hdens q Y (1 - w) hY2 (by linarith) (by linarith) Z hZ
  have hqY1 : 1 ≤ (q : ℝ) * Y := by nlinarith
  have hqYN : (q : ℝ) * Y ≤ N * N := mul_le_mul hqN hYN (by linarith) hN0.le
  -- the power factor
  have hpow : ((q : ℝ) * Y) ^ ((12 / 5 + 1 / 10) * (1 - (1 - w))) ≤ L ^ (5 * B) := by
    have e1 : ((q : ℝ) * Y) ^ ((12 / 5 + 1 / 10) * (1 - (1 - w))) ≤
        (N * N) ^ ((12 / 5 + 1 / 10) * (1 - (1 - w))) :=
      Real.rpow_le_rpow (by linarith) hqYN (by nlinarith)
    have e2 : (N * N) ^ ((12 / 5 + 1 / 10) * (1 - (1 - w))) = L ^ (5 * B) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hL0,
        Real.log_mul hN0.ne' hN0.ne', hw, rectWidth, ← hL, ← hBdef]
      congr 1
      field_simp
      ring
    linarith
  have hlog : Real.log ((q : ℝ) * Y) ^ 14 ≤ 2 ^ 14 * L ^ 14 := by
    have h0 : 0 ≤ Real.log ((q : ℝ) * Y) := Real.log_nonneg hqY1
    have h1 : Real.log ((q : ℝ) * Y) ≤ 2 * L := by
      have := Real.log_le_log (by linarith) hqYN
      rw [Real.log_mul hN0.ne' hN0.ne'] at this; linarith
    calc Real.log ((q : ℝ) * Y) ^ 14 ≤ (2 * L) ^ 14 := pow_le_pow_left₀ h0 h1 14
      _ = 2 ^ 14 * L ^ 14 := by ring
  have hfin : C * L ^ (5 * B) * (2 ^ 14 * L ^ 14) ≤ L ^ (6 * B) := by
    have s1 : L ^ (6 * B) = L ^ (5 * B) * L ^ B := by
      rw [← Real.rpow_add hL0]; ring_nf
    have s2 : L ^ (15 : ℝ) ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 hB15
    have s3 : L ^ (15 : ℝ) = L * L ^ 14 := by
      rw [show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have s4 : C * 2 ^ 14 ≤ L := by nlinarith [sq_nonneg B]
    have s5 : 0 ≤ L ^ (5 * B) := Real.rpow_nonneg hL0.le _
    have s6 : 0 ≤ L ^ 14 := by positivity
    rw [s1]
    have : C * 2 ^ 14 * L ^ 14 ≤ L ^ B := by
      calc C * 2 ^ 14 * L ^ 14 ≤ L * L ^ 14 := mul_le_mul_of_nonneg_right s4 s6
        _ = L ^ (15 : ℝ) := s3.symm
        _ ≤ L ^ B := s2
    calc C * L ^ (5 * B) * (2 ^ 14 * L ^ 14) = L ^ (5 * B) * (C * 2 ^ 14 * L ^ 14) := by ring
      _ ≤ L ^ (5 * B) * L ^ B := mul_le_mul_of_nonneg_left this s5
  calc ((univ.filter (fun χ : DirichletCharacter ℂ q => badChar N Y ε A χ)).card : ℝ)
      ≤ _ := hcard
    _ ≤ _ := hb
    _ ≤ C * L ^ (5 * B) * (2 ^ 14 * L ^ 14) := by
        gcongr
    _ ≤ _ := hfin

/-- Statement of the next LEAF, PP1993 p. 47 display 20, the conclusion: with `ε' = 1/(30B)`, the integral of
`|R2|^2` over `I''_{q,a}` is at most `q/φ(q)` times the sum over good χ of the integral of
`|W2|^2` over `|η| ≤ 1/(qQ)`, plus `Y L^(-2A-3)`, up to a constant. Class MEDIUM. -/
def StmtB8 : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → ∀ (q : ℕ) [NeZero q] (a : ℕ),
    (q : ℝ) ≤ Qs Y ε → a.Coprime q →
    ∫ α in fareyArc Y ε q a ∩ minorArcs N Y ε A, ‖R2 Y q a (α - (a : ℝ) / q)‖ ^ 2 ≤
      C * ((q : ℝ) / q.totient *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => ¬ badChar N Y ε A χ),
          ∫ η in Set.Icc (-(1 / ((q : ℝ) * Qs Y ε))) (1 / ((q : ℝ) * Qs Y ε)),
            ‖W2 Y χ η‖ ^ 2 +
        Y * Real.log N ^ (-(2 * A + 3)))

/-- LEAF: PP1993 p. 47 display 20, character expansion of R2 with error `O(sqrt Y)`,
`|τ(χ)| ≤ q^(1/2)`, Cauchy Schwarz, and the bad characters removed by B5 and B7.
Class MEDIUM, given B5 and B7, the latter from B6. -/
theorem leaf_B8 (hZ : ZeroFreeHyp) (hD : DensityHyp) : StmtB8 := by
  sorry

/-! ## Section 5, displays 21 to 26 -/

/-- Statement of the next LEAF, PP1993 p. 47 display 21, Gallagher's lemma: the integral of `|W2|^2` over
`|η| ≤ 1/h` is `≪ h^(-2)` times the integral over x of the square of the window sum of
length `h/2`, split at `100h`; on the page `h = qQ`. Class HARD. Citation wall:
Gallagher 1970 Lemma 1, ref 1, papers/Gallagher1970.pdf. A discrete form is proved in
`LeanLab.PNTPort.Gallagher.gallagher`. -/
def StmtB9 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Y h : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 ≤ Y → 2 ≤ h →
    ∫ η in Set.Icc (-(1 / h)) (1 / h), ‖W2 Y χ η‖ ^ 2 ≤
      C / h ^ 2 * ((∫ x in Set.Icc (100 * h) Y, ‖winSum Y χ x (h / 2)‖ ^ 2) +
        ∫ x in Set.Icc (-(h / 2)) (100 * h), ‖winSum Y χ x (h / 2)‖ ^ 2)

/-- LEAF: PP1993 p. 47 display 21, `StmtB9`. Class HARD. Citation wall: Gallagher 1970,
ref 1, papers/Gallagher1970.pdf. -/
theorem leaf_B9 : StmtB9 := by
  sorry

/-- PP1993 p. 48 display 22, the truncated explicit formula in hypothesis form. -/
def ExplicitFormulaHyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
    2 ≤ Y → (q : ℝ) ≤ Y → 4 ≤ x → x ≤ 2 * Y →
    (∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 / Real.log Y ≤ ‖ρ‖) →
    ‖(∑ n ∈ kRange 0 x, (Λ n : ℂ) * χ n) - deltaChi χ * x +
      ∑ᶠ ρ ∈ zeroSet χ 0 Y, (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      C * Real.log Y ^ 2

/-- LEAF: PP1993 p. 48 display 22, truncated explicit formula: for `q ≤ Y`, `4 ≤ x ≤ 2Y`,
`ψ(x, χ) - δ_χ x = -∑_{|γ| ≤ Y} x^ρ/ρ + O(L^2)`. The hypothesis that no nontrivial zero lies
within `1/log Y` of 0 keeps the term `b(χ)` inside `O(L^2)`; good characters satisfy it, and
display 22 is used only for them. Class HARD. Citation wall: Prachar 1957 ch. 7 Satz 4.4,
ref 7. Prachar ch. 7 is NOT in papers/; only ch. 8 is, papers/Prachar1957-ch8.pdf. -/
theorem leaf_B10 : ExplicitFormulaHyp := by
  sorry

/-- Statement of the next LEAF, PP1993 p. 48 display 23, the second term of display 21 summed over χ mod q with
weight `q/φ(q)` is `O(q^2 Q L^2)`, which is at most `Y L^(-2A-3)`. Class MEDIUM.
The last step needs `ε < 1/3`, since `q^2 Q ≤ Q^3 = Y^((1+3ε)/2)/8`. -/
def StmtB11 : Prop :=
  ∀ ε A : ℝ, 0 < ε → ε < 1 / 3 → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Qs Y ε →
    (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
      1 / ((q : ℝ) * Qs Y ε) ^ 2 *
        ∫ x in Set.Icc (-((q : ℝ) * Qs Y ε / 2)) (100 * ((q : ℝ) * Qs Y ε)),
          ‖winSum Y χ x ((q : ℝ) * Qs Y ε / 2)‖ ^ 2 ≤
      C * Y * Real.log N ^ (-(2 * A + 3))

/-- PP1993 p. 48 display 23, the window `x < n ≤ x + h` holds at most `h + 1` integers. -/
theorem win_card (Y x h : ℝ) (hh : 0 ≤ h) :
    ((Finset.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h) (kRange 0 Y)).card : ℝ)
      ≤ h + 1 := by
  set s := Finset.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h) (kRange 0 Y)
  have hsub : s ⊆ Finset.Icc ⌈x⌉₊ (⌈x⌉₊ + ⌊h⌋₊) := by
    intro n hn
    have hn' := (Finset.mem_filter.mp hn).2
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.ceil_le.mpr hn'.1.le
    · have h1 : (n : ℝ) - ⌈x⌉₊ ≤ h := by
        rcases le_or_gt 0 x with hx | hx
        · have := Nat.le_ceil x; linarith [hn'.2]
        · have : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hx.le
          rw [this]; push_cast; linarith [hn'.2]
      have h2 : n - ⌈x⌉₊ ≤ ⌊h⌋₊ := by
        apply Nat.le_floor
        rcases le_or_gt ⌈x⌉₊ n with hc | hc
        · rw [Nat.cast_sub hc]; exact h1
        · rw [Nat.sub_eq_zero_of_le hc.le]; simpa using hh
      omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have : ((⌈x⌉₊ + ⌊h⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) = ⌊h⌋₊ + 1 := by
    rw [show ⌈x⌉₊ + ⌊h⌋₊ + 1 - ⌈x⌉₊ = ⌊h⌋₊ + 1 by omega]; push_cast; ring
  calc (s.card : ℝ) ≤ ((⌈x⌉₊ + ⌊h⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ⌊h⌋₊ + 1 := this
    _ ≤ h + 1 := by linarith [Nat.floor_le hh]

/-- PP1993 p. 48 display 23, the trivial bound `|winSum| ≤ (h + 1)(log Y + 1)`. -/
theorem win_norm_le (Y : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x h : ℝ)
    (hY : 1 ≤ Y) (hh : 0 ≤ h) :
    ‖winSum Y χ x h‖ ≤ (h + 1) * (Real.log Y + 1) := by
  unfold winSum
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.filter (fun m : ℕ => x < (m : ℝ) ∧ (m : ℝ) ≤ x + h) (kRange 0 Y),
      ‖(Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ‖ ≤ Real.log Y + 1 := by
    intro n hn
    have hk := (Finset.mem_filter.mp hn).1
    have hk' := (Fourier398.window_mem 0 Y n).mp hk
    have hn0 : (0 : ℝ) < n := by simpa using hk'.1
    have hnY : (n : ℝ) ≤ Y := by simpa using hk'.2
    have hΛ : Λ n ≤ Real.log Y :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnY)
    have hδ : ‖deltaChi χ‖ ≤ 1 := by unfold deltaChi; split_ifs <;> simp
    calc ‖(Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ‖
        ≤ ‖(Λ n : ℂ) * χ (n : ZMod q)‖ + ‖deltaChi χ‖ := norm_sub_le _ _
      _ ≤ Λ n * 1 + 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          gcongr
          exact DirichletCharacter.norm_le_one χ _
      _ ≤ Real.log Y + 1 := by linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hl : 0 ≤ Real.log Y + 1 := by linarith [Real.log_nonneg hY]
  exact mul_le_mul_of_nonneg_right (win_card Y x h hh) hl

/-- PP1993 p. 48 display 23, the trivial bound on the integral of `|winSum|^2`. -/
theorem win_int_le (Y : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b h : ℝ)
    (hY : 1 ≤ Y) (hh : 0 ≤ h) (hab : a ≤ b) :
    ∫ x in Set.Icc a b, ‖winSum Y χ x h‖ ^ 2 ≤ ((h + 1) * (Real.log Y + 1)) ^ 2 * (b - a) := by
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc a b)
    (f := fun x => ‖winSum Y χ x h‖ ^ 2) (C := ((h + 1) * (Real.log Y + 1)) ^ 2)
    measure_Icc_lt_top (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (win_norm_le Y χ x h hY hh) 2)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hb
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hb)

/-- PP1993 p. 48 display 23, a fixed power of `log N` is below any power of `N`. -/
theorem log_pow_le_rpow (D δ : ℝ) (hδ : 0 < δ) : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
    (Real.log N + 1) ^ 2 * Real.log N ^ D ≤ N ^ δ := by
  have ho := (isLittleO_log_rpow_rpow_atTop (D + 2) hδ).bound (show (0:ℝ) < 1 / 4 by norm_num)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp ho
  refine ⟨max N1 (Real.exp 1), fun N hN => ?_⟩
  have hNe : Real.exp 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hNe
  have hL1 : 1 ≤ Real.log N := by rw [Real.le_log_iff_exp_le hN0]; exact hNe
  have h := hN1 N ((le_max_left _ _).trans hN)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg hN0.le _)] at h
  have hsplit : Real.log N ^ (D + 2) = Real.log N ^ D * Real.log N ^ 2 := by
    rw [Real.rpow_add (by linarith), Real.rpow_two]
  have h4 : (Real.log N + 1) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
  have hD0 : 0 ≤ Real.log N ^ D := Real.rpow_nonneg (by linarith) _
  calc (Real.log N + 1) ^ 2 * Real.log N ^ D ≤ 4 * Real.log N ^ 2 * Real.log N ^ D :=
        mul_le_mul_of_nonneg_right h4 hD0
    _ = 4 * Real.log N ^ (D + 2) := by rw [hsplit]; ring
    _ ≤ N ^ δ := by linarith

/-- LEAF: PP1993 p. 48 display 23, `StmtB11`, by the trivial bound on window sums.
Class MEDIUM. PROVED. -/
theorem leaf_B11 : StmtB11 := by
  intro ε A hε hε3 hA
  set δ := (1 - 3 * ε) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨N1, hN1⟩ := log_pow_le_rpow (2 * A + 3) (7 / 12 * δ) (by positivity)
  refine ⟨227 / 8, max N1 ((2 : ℝ) ^ (24 : ℝ)), ?_⟩
  intro N Y hN hlow hYN q _ hqQ
  have hNbig : (2 : ℝ) ^ (24 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN1' : 1 ≤ N := le_trans (Real.one_le_rpow (by norm_num) (by norm_num)) hNbig
  have hN0 : 0 < N := by linarith
  have hN712 : N ^ (7 / 12 : ℝ) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)).trans hlow
  have hY14 : (2 : ℝ) ^ (14 : ℝ) ≤ Y := by
    have h1 : ((2 : ℝ) ^ (24 : ℝ)) ^ (7 / 12 : ℝ) ≤ N ^ (7 / 12 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hNbig (by norm_num)
    have h3 : ((2 : ℝ) ^ (24 : ℝ)) ^ (7 / 12 : ℝ) = 2 ^ (14 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by norm_num) (by norm_num)) hY14
  have hY0 : 0 < Y := by linarith
  have hH4 : 4 ≤ Hs Y ε := by
    unfold Hs
    have a1 : Y ^ (1 / 3 : ℝ) ≤ Y ^ (1 / 3 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have a2 : ((2 : ℝ) ^ (14 : ℝ)) ^ (1 / 3 : ℝ) ≤ Y ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hY14 (by norm_num)
    have a3 : ((2 : ℝ) ^ (14 : ℝ)) ^ (1 / 3 : ℝ) = 2 ^ (14 / 3 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    have a4 : (2 : ℝ) ^ (2 : ℝ) ≤ 2 ^ (14 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have a5 : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [Real.rpow_two]; norm_num
    linarith
  have hH0 : 0 ≤ Hs Y ε := by linarith
  have hsq2 : 2 ≤ Real.sqrt (Hs Y ε) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hH4
  have hQ1 : 1 ≤ Qs Y ε := by unfold Qs; linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Q := Qs Y ε with hQ
  set h := (q : ℝ) * Q with hh
  have hh1 : 1 ≤ h := by rw [hh]; nlinarith
  have hpos : 0 < h := by linarith
  have hlg : 0 ≤ Real.log Y + 1 := by linarith [Real.log_nonneg hY1]
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      1 / h ^ 2 * ∫ x in Set.Icc (-(h / 2)) (100 * h), ‖winSum Y χ x (h / 2)‖ ^ 2 ≤
        227 * h * (Real.log Y + 1) ^ 2 := by
    intro χ
    have hi := win_int_le Y χ (-(h / 2)) (100 * h) (h / 2) hY1 (by linarith) (by linarith)
    have hb1 : (h / 2 + 1) ^ 2 ≤ (3 / 2 * h) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hb2 : ((h / 2 + 1) * (Real.log Y + 1)) ^ 2 * (100 * h - -(h / 2)) ≤
        (3 / 2 * h) ^ 2 * (Real.log Y + 1) ^ 2 * (100 * h + h / 2) := by
      rw [mul_pow, sub_neg_eq_add]
      gcongr
    have hb3 : (3 / 2 * h) ^ 2 * (Real.log Y + 1) ^ 2 * (100 * h + h / 2) ≤
        227 * h * (Real.log Y + 1) ^ 2 * h ^ 2 := by
      have : 0 ≤ h ^ 3 * (Real.log Y + 1) ^ 2 := by positivity
      nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have htot : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hsum : ∑ χ : DirichletCharacter ℂ q,
      1 / h ^ 2 * ∫ x in Set.Icc (-(h / 2)) (100 * h), ‖winSum Y χ x (h / 2)‖ ^ 2 ≤
        (q.totient : ℝ) * (227 * h * (Real.log Y + 1) ^ 2) := by
    refine (Finset.sum_le_sum fun χ _ => hchar χ).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hc : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    rw [hc]
  -- Q^3 in terms of Y
  have hQ3 : Q ^ 3 = Y / Y ^ δ / 8 := by
    rw [hQ, Qs, div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hH0,
      Hs, ← Real.rpow_mul hY0.le]
    rw [show (1 / 3 + ε) * ((1 / 2 : ℝ) * ((3 : ℕ) : ℝ)) = 1 - δ by rw [hδ]; push_cast; ring,
      Real.rpow_sub hY0, Real.rpow_one]
    norm_num
  set P := Real.log N ^ (2 * A + 3) with hP
  have hLpos : 0 < Real.log N := Real.log_pos (by
    have : (1 : ℝ) < 2 ^ (24 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    linarith)
  have hP0 : 0 < P := Real.rpow_pos_of_pos hLpos _
  have hYd : 0 < Y ^ δ := Real.rpow_pos_of_pos hY0 _
  have hkey : (Real.log Y + 1) ^ 2 * P ≤ Y ^ δ := by
    have e1 := hN1 N ((le_max_left _ _).trans hN)
    have e2 : N ^ (7 / 12 * δ) ≤ Y ^ δ := by
      rw [Real.rpow_mul hN0.le]
      exact Real.rpow_le_rpow (by positivity) hN712 hδ0.le
    have e3 : (Real.log Y + 1) ^ 2 ≤ (Real.log N + 1) ^ 2 :=
      pow_le_pow_left₀ hlg (by linarith [Real.log_le_log hY0 hYN]) 2
    calc (Real.log Y + 1) ^ 2 * P ≤ (Real.log N + 1) ^ 2 * P :=
          mul_le_mul_of_nonneg_right e3 hP0.le
      _ ≤ _ := e1.trans e2
  have hqQ' : (q : ℝ) * h ≤ Q ^ 3 := by
    rw [hh]
    have : (q : ℝ) * q ≤ Q * Q := mul_le_mul hqQ hqQ (by linarith) (by linarith)
    nlinarith
  rw [Real.rpow_neg hLpos.le, ← hP]
  calc (q : ℝ) / q.totient * ∑ χ : DirichletCharacter ℂ q,
        1 / h ^ 2 * ∫ x in Set.Icc (-(h / 2)) (100 * h), ‖winSum Y χ x (h / 2)‖ ^ 2
      ≤ (q : ℝ) / q.totient * ((q.totient : ℝ) * (227 * h * (Real.log Y + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 227 * ((q : ℝ) * h) * (Real.log Y + 1) ^ 2 := by field_simp
    _ ≤ 227 * Q ^ 3 * (Real.log Y + 1) ^ 2 := by gcongr
    _ = 227 / 8 * (Y * ((Real.log Y + 1) ^ 2 / Y ^ δ)) := by rw [hQ3]; ring
    _ ≤ 227 / 8 * (Y * P⁻¹) := by
        gcongr
        rw [div_le_iff₀ hYd, inv_mul_eq_div, le_div_iff₀ hP0]
        linarith
    _ = 227 / 8 * Y * P⁻¹ := by ring

/-- Statement of the next LEAF, PP1993 p. 48 display 24, Saffari Vaughan: the first term of display 21 is
`≪ L` times the supremum over `M` and `Θ` of `∫_M^(3M) |∑_{x<n≤x+Θx}|^2`, plus the
truncation error `h^3 L^2` for windows crossing `Y`. QUESTION: the ranges
`50h ≤ M ≤ Y/2`, `h/(64M) ≤ Θ ≤ 4h/M` are reconstructed, taken generous so the leaf is
weaker; the note does not transcribe them.
Class HARD. Citation wall: Saffari and Vaughan 1977 Lemmas 5 and 6, ref 10, NO COPY,
INTAKE needed; and Perelli Pintz 1992 section 5, ref 5, papers/P0070.txt. -/
def StmtB12 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Y h V : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    2 ≤ h → 100 * h ≤ Y → 0 ≤ V →
    (∀ M Θ : ℝ, 50 * h ≤ M → M ≤ Y / 2 → h / (64 * M) ≤ Θ → Θ ≤ 4 * h / M →
      ∫ x in Set.Icc M (3 * M), ‖shortDelta χ x Θ‖ ^ 2 ≤ V) →
    ∫ x in Set.Icc (100 * h) Y, ‖winSum Y χ x (h / 2)‖ ^ 2 ≤
      C * Real.log Y * V + C * h ^ 3 * Real.log Y ^ 2

/-- LEAF: PP1993 p. 48 display 24, `StmtB12`. Class HARD. Citation wall: Saffari Vaughan
1977, ref 10, NO COPY, INTAKE needed; PP1992 section 5, ref 5, papers/P0070.txt. -/
theorem leaf_B12 : StmtB12 := by
  sorry

/-- PP1993 p. 48 display 25, the zero sum `∑_ρ M^(2β) Θ^2/(1 + Θ^2 γ^2)` over the zeros
`ρ = β + iγ` of `L(s, χ)` with `β ≥ 1/2` and `|γ| ≤ Y`, counted with multiplicity.
The weight is within a factor 2 of `min(Θ^2, 1/γ^2)` and stays right at `γ = 0`. -/
def zeroWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (M Θ Y : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zeroSet χ (1 / 2) Y,
    (analyticOrderNatAt χ.LFunction ρ : ℝ) * M ^ (2 * ρ.re) * (Θ ^ 2 / (1 + Θ ^ 2 * ρ.im ^ 2))

/-- Statement of the next LEAF, PP1993 p. 48 display 25, the conclusion: for a good χ,
display 22 at `x` and `x + Θx` inserted into display 24 and the mean value
`∫_M^(3M) x^(ρ + ρ') ≪ M^(1+β+β') / (1 + |γ - γ'|)` bound `∫_M^(3M) |∑_{x<n≤x+Θx}|^2` by
`M L^6` times the zero sum `zeroWeight` plus `qQ + 1`; the term `qQ` carries the zeros with
`β < 1/2`. QUESTION: the note does not transcribe display 25, which is stated with
`N(σ, 20M/(qQ), χ)` and `N(σ, K, χ)`; this zero sum is the line before it, from which
display 25 follows by partial summation in σ and a dyadic split in K at `20M/(qQ)`. -/
def StmtB13 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), (q : ℝ) ≤ Qs Y ε →
    ¬ badChar N Y ε A χ → ∀ M Θ : ℝ,
    50 * ((q : ℝ) * Qs Y ε) ≤ M → M ≤ Y / 2 →
    (q : ℝ) * Qs Y ε / (64 * M) ≤ Θ → Θ ≤ 4 * ((q : ℝ) * Qs Y ε) / M →
    ∫ x in Set.Icc M (3 * M), ‖shortDelta χ x Θ‖ ^ 2 ≤
      C * M * Real.log N ^ 6 * (zeroWeight χ M Θ Y + (q : ℝ) * Qs Y ε + 1)

/-- LEAF: PP1993 p. 48 display 25, `StmtB13`, from display 22 at `x` and `x + Θx`.
Class HARD. Citation wall: Perelli Pintz 1992 section 5, ref 5, papers/P0070.pdf. -/
theorem leaf_B13 (hEF : ExplicitFormulaHyp) : StmtB13 := by
  sorry

/-- LEAF: PP1993 p. 48 display 26 and the line after: the critical height is `20M/(qQ)`;
with display 18 the right side of display 25 is at most `Y L^(-2A-3)`, and with displays 14,
15, 20, 21, 23 and 24 this gives display 5. Stated as the implication from the earlier leaf
conclusions, for `ε < 1/3` as display 23 requires. Class MEDIUM, given B6 and B13. -/
theorem leaf_B14 (hD : DensityHyp) (h3 : StmtB3) (h4 : StmtB4) (h7 : StmtB7) (h8 : StmtB8)
    (h9 : StmtB9) (h11 : StmtB11) (h12 : StmtB12) (h13 : StmtB13) :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 3 → 0 < A → Display5 ε A := by
  sorry

/-- PP1993 p. 44 display 5 for `ε < 1/3`, CONDITIONAL ON the LEAF theorems B3 to B14. -/
theorem display5_of_leaves : ∀ ε A : ℝ, 0 < ε → ε < 1 / 3 → 0 < A → Display5 ε A :=
  leaf_B14 leaf_B6 leaf_B3 leaf_B4 (leaf_B7 leaf_B6) (leaf_B8 leaf_B5 leaf_B6) leaf_B9
    leaf_B11 leaf_B12 (leaf_B13 leaf_B10)

/-! ## Wiring -/

/-- `Decomp398a.minor_energy` restricted to `ε < 1/3`, from the leaves by displays 3 and 5.
No sorry of its own; CONDITIONAL ON the LEAF theorems of this file. The exact statement for
all ε is not wired: B11 and hence B14 need `ε < 1/3`. -/
theorem minor_energy_small_of_leaves :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 3 → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
      ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)‖ ^ 2 ≤
        C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A) := by
  intro ε A hε hε3 hA
  obtain ⟨c, hc, hbt⟩ := leaf_B1_bt
  obtain ⟨N1, hN1⟩ := hbt ε hε
  obtain ⟨C1, hC1, h1⟩ := leaf_B1
  obtain ⟨C2, hC2, h2⟩ := leaf_B2
  obtain ⟨C5, N5, h5⟩ := display5_of_leaves ε A hε hε3 hA
  set C5' := max C5 0 with hC5'
  have hC5'0 : 0 ≤ C5' := le_max_right _ _
  refine ⟨C1 * c ^ (3 / 2 : ℝ) * Real.sqrt (C2 * C5'), max 3 (max N1 N5), ?_⟩
  intro N Y hN hlow hYN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNN1 : N1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNN5 : N5 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hN1' (by linarith)).trans hlow
  have hY0 : 0 < Y := by linarith
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  obtain ⟨hS1, hS2⟩ := hN1 N Y hNN1 hlow hYN
  set H := Hs Y ε with hH
  have hH0 : 0 ≤ H := Real.rpow_nonneg hY0.le _
  set V := C5' * Y * Real.log N ^ (-(2 * A + 3)) with hV
  have hV0 : 0 ≤ V := by positivity
  have hloc : ∀ ξ : ℝ, localS2 N Y ε A ξ ≤ V := by
    intro ξ
    refine (h5 N Y hNN5 hlow hYN ξ).trans ?_
    have : 0 ≤ Y * Real.log N ^ (-(2 * A + 3)) := by positivity
    have hle : C5 ≤ C5' := le_max_left _ _
    rw [hV, mul_assoc C5', mul_assoc C5]
    exact mul_le_mul_of_nonneg_right hle this
  have hw := h2 ε A N Y V hε hA hN3 hY1 hYN hV0 hloc
  set M := Real.sqrt (C2 * H ^ 2 * V) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hwM : ∀ ξ : ℝ, weightedS2 N Y ε A ξ ≤ M ^ 2 := by
    intro ξ
    rw [hM, Real.sq_sqrt (by positivity)]
    exact hw ξ
  have hmain := h1 ε A N Y c M hε hA hN3 hY1 hYN hc.le hM0 hS1 hS2 hwM
  -- the value of M
  have hMval : M = Real.sqrt (C2 * C5') * H * Real.sqrt Y *
      Real.log N ^ (-(A + 3 / 2)) := by
    rw [hM, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    symm
    have hsq1 : Real.sqrt (C2 * C5') ^ 2 = C2 * C5' := Real.sq_sqrt (by positivity)
    have hsq2 : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
    have hsq3 : (Real.log N ^ (-(A + 3 / 2))) ^ 2 = Real.log N ^ (-(2 * A + 3)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1; push_cast; ring
    calc (Real.sqrt (C2 * C5') * H * Real.sqrt Y * Real.log N ^ (-(A + 3 / 2))) ^ 2
        = Real.sqrt (C2 * C5') ^ 2 * H ^ 2 * Real.sqrt Y ^ 2 *
            (Real.log N ^ (-(A + 3 / 2))) ^ 2 := by ring
      _ = C2 * H ^ 2 * V := by rw [hsq1, hsq2, hsq3, hV]; ring
  have hpow : (c * Y * Real.log N) ^ (3 / 2 : ℝ) * Real.sqrt Y *
      Real.log N ^ (-(A + 3 / 2)) = c ^ (3 / 2 : ℝ) * Y ^ 2 * Real.log N ^ (-A) := by
    rw [Real.mul_rpow (by positivity) hL0.le, Real.mul_rpow hc.le hY0.le,
      Real.sqrt_eq_rpow]
    have e1 : Y ^ (3 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) = Y ^ 2 := by
      rw [← Real.rpow_add hY0]; norm_num
    have e2 : Real.log N ^ (3 / 2 : ℝ) * Real.log N ^ (-(A + 3 / 2)) =
        Real.log N ^ (-A) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    calc c ^ (3 / 2 : ℝ) * Y ^ (3 / 2 : ℝ) * Real.log N ^ (3 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) *
          Real.log N ^ (-(A + 3 / 2))
        = c ^ (3 / 2 : ℝ) * (Y ^ (3 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) *
            (Real.log N ^ (3 / 2 : ℝ) * Real.log N ^ (-(A + 3 / 2))) := by ring
      _ = _ := by rw [e1, e2]
  calc ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (arcBase Y ε \ majorArcs N Y ε A)‖ ^ 2
      = ∑ k ∈ kRange (N / 2) (Hs Y ε / 2),
          ‖arcCoeff N Y (2 * k) (minorArcs N Y ε A)‖ ^ 2 := rfl
    _ ≤ C1 * (c * Y * Real.log N) ^ (3 / 2 : ℝ) * M := hmain
    _ = C1 * Real.sqrt (C2 * C5') * H *
          ((c * Y * Real.log N) ^ (3 / 2 : ℝ) * Real.sqrt Y *
            Real.log N ^ (-(A + 3 / 2))) := by rw [hMval]; ring
    _ = C1 * c ^ (3 / 2 : ℝ) * Real.sqrt (C2 * C5') * Y ^ (1 / 3 + ε) * Y ^ 2 *
          Real.log N ^ (-A) := by rw [hpow, hH, Hs]; ring

end

end LeanLab.Halupczok2012.Split398aMinor
