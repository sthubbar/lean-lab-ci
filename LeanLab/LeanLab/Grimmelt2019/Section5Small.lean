/-
P0074 L. Grimmelt, "Goldbach Numbers in Short Intervals: A Nonnegative Model Approach",
arXiv 1910.05187 v2. Unit U-1324, run 20261021T0003Z-5661.

Repair of the refutable bundle `Prop21.Section5Inputs`, see `MainTerm.not_section5Inputs`.

* `Section5InputsSmall`: the Section 5 objects of `MainTerm.Sec5ObjectsMT`, so with the main
  term derived from condition (29) and the truncated singular series, for `0 < ε < 1/18` only.
  The paper's Lemma 5.1 says "Let ε > 0", but its proof needs `H^{1/2} < Y^{1/9}`, which is
  exactly `ε < 1/18`, see `Bookkeeping.rough_support`.
* `ShortIntervalLogSavingBelow`, `ExactLengthLogSavingBelow`: the estimate (1) for `ε < δ` only;
  `logSaving_of_below` recovers every `ε` by monotonicity, and
  `logSavingBelow_of_exactLengthBelow` is the covering step of `logSaving_of_exactLength` with
  `ε` restricted; its proof calls the single length estimate at `ε/2` only.
* `thm1_1_of_section5Small`: Theorem 1.1, CONDITIONAL ON `ShortSecondMoment` and
  `Section5InputsSmall`.
* Vacuity tests: `window_large` shows that for `ε < 1/18` the support window of `ω` lies in
  `[X/2, X]` and has length `2Y ≥ 2` for large `X`, so the `ε = 1` argument, which forces `ω = 0`,
  does not apply. `prime_in_window_of_objects` shows why no cheap instance exists: any
  `Sec5ObjectsMT` with `c > 0` puts a prime in every window `[n - 2Y, n - Y)`, `n ∈ [X - H, X]`.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here proves Theorem 1.1; its analytic inputs stay cited.
-/
import LeanLab.Grimmelt2019.MainTerm

namespace LeanLab.Grimmelt2019.Section5Small
open Real LeanLab.Grimmelt2019 LeanLab.Grimmelt2019.Prop21 LeanLab.Grimmelt2019.MainTerm

attribute [local instance] Classical.propDecidable

/-! ### The repaired bundle -/

/-- Cited hypothesis bundle, Section 5 of P0074, with `ε` restricted to `0 < ε < 1/18`: for each
such `ε` there is `B` such that for every `A > 0` there are `K ≥ 0`, `c > 0`, `X0` with the
objects `Sec5ObjectsMT` at every `X ≥ X0`; Lemma 5.1, the model `Tν = cν ΛQ`, Lemma 4.2,
Corollary 4.3, condition (29) in residue class form and the singular series bound. -/
def Section5InputsSmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 18 → ∃ B : ℝ, ∀ A : ℝ, 0 < A → ∃ K c X0 : ℝ, 0 ≤ K ∧ 0 < c ∧
    ∀ X : ℝ, X0 ≤ X →
      Nonempty (Sec5ObjectsMT X (X ^ (21 / 40 + ε)) ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε))
        K B A c)

/-! ### Vacuity tests -/

/-- PROVED: for `0 ≤ ε < 1/18` and `X` large, `1 ≤ Y` and `6 Y ≤ X`, `Y = X^{21/40+ε}`. So the
window `(X - 3Y, X - Y]` lies in `[X/2, X]`; the step `Y ≥ X` of `not_section5Inputs` fails. -/
theorem window_large {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 18) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 1 ≤ X ^ (21 / 40 + ε) ∧ 6 * X ^ (21 / 40 + ε) ≤ X := by
  set e := 21 / 40 + ε with he
  have hd : 0 < 1 - e := by rw [he]; linarith
  refine ⟨max 1 ((6 : ℝ) ^ (1 / (1 - e))), fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hX6 : (6 : ℝ) ^ (1 / (1 - e)) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  refine ⟨Real.one_le_rpow hX1 (by rw [he]; linarith), ?_⟩
  have h6 : (6 : ℝ) ≤ X ^ (1 - e) := by
    calc (6 : ℝ) = ((6 : ℝ) ^ (1 / (1 - e))) ^ (1 - e) := by
          rw [← Real.rpow_mul (by norm_num), show 1 / (1 - e) * (1 - e) = 1 by field_simp,
            Real.rpow_one]
      _ ≤ X ^ (1 - e) := Real.rpow_le_rpow (by positivity) hX6 hd.le
  have hsplit : X = X ^ e * X ^ (1 - e) := by
    rw [← Real.rpow_add hXpos, show e + (1 - e) = 1 by ring, Real.rpow_one]
  have hXe : 0 ≤ X ^ e := Real.rpow_nonneg hXpos.le _
  calc 6 * X ^ e = X ^ e * 6 := by ring
    _ ≤ X ^ e * X ^ (1 - e) := mul_le_mul_of_nonneg_left h6 hXe
    _ = X := hsplit.symm

/-- PROVED: under the conclusion of `window_large`, the support window of `ω` inside `[1, X]`
contains the integer `⌊X - Y⌋`; so the support fields do not force `ω = 0`. -/
theorem window_has_integer {X Y : ℝ} (hY : 1 ≤ Y) (h6 : 6 * Y ≤ X) :
    ∃ n : ℤ, n ∈ supp X ∧ X - 3 * Y < (n : ℝ) ∧ (n : ℝ) ≤ X - Y := by
  refine ⟨⌊X - Y⌋, ?_, ?_, Int.floor_le _⟩
  · unfold supp
    rw [Finset.mem_Icc]
    constructor
    · have : (1 : ℝ) ≤ X - Y := by linarith
      exact Int.le_floor.mpr (by push_cast; exact this)
    · exact Int.floor_le_floor (by linarith)
  · have := Int.lt_floor_add_one (X - Y)
    linarith

/-- PROVED: any `Sec5ObjectsMT` with `c > 0`, `Y > 0`, `Q ≥ 1` and `s0 ≤ Q²` has a prime in every
window `[n - 2Y, n - Y)` with `n ∈ [X - H, X]`. Condition (29) at `q = 1` gives the mass of `ω` on
the window, the budget makes it positive, and `ω ≤ Λ'`. So an instance of the bundle contains
primes in all intervals of length `Y = X^{21/40+ε}`, a theorem of Baker, Harman and Pintz type;
no cheap instance exists. -/
theorem prime_in_window_of_objects {X Y H K B A c : ℝ} (o : Sec5ObjectsMT X Y H K B A c)
    (hc : 0 < c) (hY : 0 < Y) (hQ : 1 ≤ o.Q) (hs0 : o.s0 ≤ (o.Q : ℝ) ^ 2) :
    ∀ n ∈ win X H, ∃ m : ℤ, (n : ℝ) - 2 * Y ≤ m ∧ (m : ℝ) < n - Y ∧ 0 < m ∧ m.toNat.Prime := by
  intro n hn
  have hcY : 0 < c * Y := mul_pos hc hY
  have hb := o.budget
  have hcν0 := o.cnu_nonneg
  have hcω0 := o.comega_nonneg
  have hE0 := o.E_nonneg
  have hQ2 : (1 : ℝ) ≤ (o.Q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ o.Q := by exact_mod_cast hQ
    nlinarith
  -- `cν > 0`, and the main term beats the error
  have hcν : 0 < o.cν := by
    rcases hcν0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hb; simp at hb; linarith
  have hgap : (o.Q : ℝ) ^ 2 * o.E < o.cω * Y * o.s0 := by
    by_contra hng
    push Not at hng
    have : o.cν * o.cω * Y * o.s0 - o.cν * (o.Q : ℝ) ^ 2 * o.E ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hng hcν0
      nlinarith
    linarith
  have hEl : o.E < o.cω * Y := by
    have h1 : o.cω * Y * o.s0 ≤ o.cω * Y * (o.Q : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hs0 (mul_nonneg hcω0 hY.le)
    have h2 : o.E ≤ (o.Q : ℝ) ^ 2 * o.E := by nlinarith
    nlinarith
  -- condition (29) at `q = 1`, `r = 0`
  have hap := o.ap29 n hn 1 (by rw [Finset.mem_Icc]; exact ⟨le_rfl, hQ⟩) 0 (by simp)
  have hfil : (Wn X Y n).filter (fun m => m % ((1 : ℕ) : ℤ) = 0) = Wn X Y n := by
    apply Finset.filter_true_of_mem; intro m _; simp
  rw [hfil] at hap
  simp only [Int.gcd_zero_left, Nat.cast_one, Int.natAbs_one, if_true, Nat.totient_one,
    div_one] at hap
  have hmass : 0 < ∑ m ∈ Wn X Y n, o.ω m := by
    have := (abs_le.mp hap).1
    linarith
  obtain ⟨m, hm, hωm⟩ := Finset.exists_lt_of_sum_lt (s := Wn X Y n) (f := fun _ => (0 : ℝ))
    (g := o.ω) (by simpa using hmass)
  have hLm : 0 < LamP X m := lt_of_lt_of_le hωm (o.omega_le m)
  unfold Wn at hm
  rw [Finset.mem_filter] at hm
  refine ⟨m, hm.2.1, hm.2.2, ?_⟩
  unfold LamP at hLm
  split_ifs at hLm with hp
  · exact ⟨hp.1, hp.2.1⟩
  · exact absurd hLm (lt_irrefl 0)

/-! ### Restricted forms of the estimate (1) -/

/-- The estimate (1) for `0 < ε < δ` only. -/
def ShortIntervalLogSavingBelow (c δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < δ → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
    X ^ (c + ε) < H → (EXH X H : ℝ) ≤ C * H / Real.log X ^ A

/-- The single length estimate for `0 < ε < δ` only. -/
def ExactLengthLogSavingBelow (c δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < δ → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    (EXH X (X ^ (c + ε)) : ℝ) ≤ C * X ^ (c + ε) / Real.log X ^ A

/-- PROVED: monotonicity in `ε`; the estimate for small `ε` gives it for every `ε`, using
`ε0 = δ/2` when `ε ≥ δ`. -/
theorem logSaving_of_below {c δ : ℝ} (hδ : 0 < δ) (h : ShortIntervalLogSavingBelow c δ) :
    ShortIntervalLogSaving c := by
  intro ε hε A hA
  by_cases hεδ : ε < δ
  · exact h ε hε hεδ A hA
  · have hge : δ ≤ ε := not_lt.mp hεδ
    obtain ⟨C, X0, hC⟩ := h (δ / 2) (by linarith) (by linarith) A hA
    refine ⟨C, max X0 1, fun X H hX hH => hC X H (le_of_max_le_left hX) ?_⟩
    have hX1 : 1 ≤ X := le_of_max_le_right hX
    exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hH

/-- CONDITIONAL ON `LeanLab.ExceptionalSet.LogPowerSaving`, which the lab PROVED as
`LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving`: the copy of `logSaving_of_exactLength` with
`ε` restricted to `(0, δ)`. Its proof calls the single length estimate at `ε/2 < δ` only. -/
theorem logSavingBelow_of_exactLengthBelow {c δ : ℝ} (hc : 0 ≤ c)
    (hcore : ExactLengthLogSavingBelow c δ) (hfull : LeanLab.ExceptionalSet.LogPowerSaving) :
    ShortIntervalLogSavingBelow c δ := by
  intro ε hε hεδ A hA
  obtain ⟨C1, hC1⟩ := hfull A hA
  obtain ⟨C0, X0, hC0⟩ := hcore (ε / 2) (by linarith) (by linarith) A hA
  set e := c + ε / 2 with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  set M0 := max C0 0 with hM0def
  have hM0 : 0 ≤ M0 := le_max_right _ _
  refine ⟨max C1 0 * 2 ^ (A + 1) + M0 * 2 ^ A * (4 ^ e + 2),
    max (max 16 (4 * X0)) ((2 : ℝ) ^ (2 / ε)), fun X H hX hH => ?_⟩
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX0 : 4 * X0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ^ (2 / ε) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
  have hHpos : 0 < H := lt_of_le_of_lt (Real.rpow_nonneg hXpos.le _) hH
  have hC1' : 0 ≤ max C1 0 := le_max_right _ _
  have hfirst : 0 ≤ max C1 0 * 2 ^ (A + 1) * H / Real.log X ^ A := by positivity
  have hsecond : 0 ≤ M0 * 2 ^ A * (4 ^ e + 2) * H / Real.log X ^ A := by positivity
  rcases le_or_gt (X / 2) H with hbig | hsmall
  · calc (EXH X H : ℝ) ≤ (max C1 0 * 2 ^ (A + 1)) * H / Real.log X ^ A :=
          EXH_le_of_full hA.le hC1 hX16 hbig
      _ ≤ _ := by rw [add_mul, add_div]; linarith
  · have hXe2 : 2 ≤ X ^ (ε / 2) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (2 / ε)) ^ (ε / 2) := by
            rw [← Real.rpow_mul (by norm_num)]
            rw [show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one]
        _ ≤ X ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hX2 (by positivity)
    have hsplit : X ^ (c + ε) = X ^ e * X ^ (ε / 2) := by
      rw [← Real.rpow_add hXpos, he]; ring_nf
    have hXe_pos : 0 < X ^ e := Real.rpow_pos_of_pos hXpos _
    have hXeH : 2 * X ^ e < H := by
      have : X ^ e * 2 ≤ X ^ e * X ^ (ε / 2) := mul_le_mul_of_nonneg_left hXe2 hXe_pos.le
      rw [← hsplit] at this; linarith
    set h := (X / 4) ^ e with hdef
    have hh_pos : 0 < h := Real.rpow_pos_of_pos (by linarith) _
    have hhXe : h ≤ X ^ e := Real.rpow_le_rpow (by linarith) (by linarith) he0
    set N := ⌈H / h⌉₊ + 1 with hNdef
    have hceil1 : H / h ≤ (⌈H / h⌉₊ : ℝ) := Nat.le_ceil _
    have hceil2 : (⌈H / h⌉₊ : ℝ) < H / h + 1 := Nat.ceil_lt_add_one (by positivity)
    have hHh : H = H / h * h := by field_simp
    have hN : H < (N : ℝ) * h := by
      rw [hNdef]; push_cast
      nlinarith
    have hNh : (N : ℝ) * h ≤ H + 2 * h := by
      rw [hNdef]; push_cast
      nlinarith
    have hcover := EXH_le_sum_cover X H h hh_pos N hN
    have hpiece : ∀ j ∈ Finset.range N,
        (EXH (X - j * h) h : ℝ) ≤ M0 * 2 ^ A * X ^ e / Real.log X ^ A := by
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      have hj_le : (j : ℝ) ≤ ⌈H / h⌉₊ := by
        have : j ≤ ⌈H / h⌉₊ := by omega
        exact_mod_cast this
      have hjh : (j : ℝ) * h < H + h := by
        calc (j : ℝ) * h ≤ (⌈H / h⌉₊ : ℝ) * h := mul_le_mul_of_nonneg_right hj_le hh_pos.le
          _ < (H / h + 1) * h := mul_lt_mul_of_pos_right hceil2 hh_pos
          _ = H + h := by field_simp
      have hj0 : 0 ≤ (j : ℝ) * h := by positivity
      have hXj_low : X / 4 ≤ X - j * h := by linarith
      have hXj_le : X - j * h ≤ X := by linarith
      have hXj0 : X0 ≤ X - j * h := by linarith
      have hlen : h ≤ (X - j * h) ^ e := Real.rpow_le_rpow (by linarith) hXj_low he0
      have hlogXj : 0 < Real.log (X - j * h) := Real.log_pos (by linarith)
      calc (EXH (X - j * h) h : ℝ) ≤ EXH (X - j * h) ((X - j * h) ^ e) := by
            exact_mod_cast EXH_mono_H (X - j * h) hlen
        _ ≤ C0 * (X - j * h) ^ e / Real.log (X - j * h) ^ A := hC0 _ hXj0
        _ ≤ M0 * ((X - j * h) ^ e / Real.log (X - j * h) ^ A) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (div_nonneg (Real.rpow_nonneg (by linarith) _)
                (Real.rpow_nonneg hlogXj.le _))
        _ ≤ M0 * (2 ^ A * (X - j * h) ^ e / Real.log X ^ A) :=
            mul_le_mul_of_nonneg_left
              (div_logpow_le hX16 hXj_low (Real.rpow_nonneg (by linarith) _) hA.le) hM0
        _ ≤ M0 * (2 ^ A * X ^ e / Real.log X ^ A) := by
            gcongr
            linarith
        _ = M0 * 2 ^ A * X ^ e / Real.log X ^ A := by ring
    have hsum : (EXH X H : ℝ) ≤ N * (M0 * 2 ^ A * X ^ e / Real.log X ^ A) := by
      calc (EXH X H : ℝ) ≤ ∑ j ∈ Finset.range N, (EXH (X - j * h) h : ℝ) := by
            exact_mod_cast hcover
        _ ≤ ∑ _j ∈ Finset.range N, M0 * 2 ^ A * X ^ e / Real.log X ^ A :=
            Finset.sum_le_sum hpiece
        _ = N * (M0 * 2 ^ A * X ^ e / Real.log X ^ A) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hXe_eq : X ^ e = 4 ^ e * h := by
      rw [hdef, ← Real.mul_rpow (by norm_num) (by linarith)]; ring_nf
    have h4e : 0 < (4 : ℝ) ^ e := by positivity
    have hNX : (N : ℝ) * X ^ e ≤ (4 ^ e + 2) * H := by
      calc (N : ℝ) * X ^ e = 4 ^ e * ((N : ℝ) * h) := by rw [hXe_eq]; ring
        _ ≤ 4 ^ e * (H + 2 * h) := mul_le_mul_of_nonneg_left hNh h4e.le
        _ = 4 ^ e * H + 2 * X ^ e := by rw [hXe_eq]; ring
        _ ≤ (4 ^ e + 2) * H := by nlinarith
    have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
    calc (EXH X H : ℝ) ≤ N * (M0 * 2 ^ A * X ^ e / Real.log X ^ A) := hsum
      _ = M0 * 2 ^ A * ((N : ℝ) * X ^ e) / Real.log X ^ A := by ring
      _ ≤ M0 * 2 ^ A * ((4 ^ e + 2) * H) / Real.log X ^ A := by gcongr
      _ = M0 * 2 ^ A * (4 ^ e + 2) * H / Real.log X ^ A := by ring
      _ ≤ _ := by rw [add_mul, add_div]; linarith

/-! ### The Lemma 5.1 core and Theorem 1.1 from the repaired bundle -/

/-- CONDITIONAL ON `ShortSecondMoment` and `Section5InputsSmall`: the Lemma 5.1 core, the
estimate (1) at the single length `H = Y^{1/9+2ε}`, `Y = X^{21/40+ε}`, for `0 < ε < 1/18`. The
proof is that of `Prop21.core_of_section5`, with the objects converted by
`Sec5ObjectsMT.toSec5`. -/
theorem core_of_section5Small (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5InputsSmall) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 18 → ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (EXH X ((X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε)) : ℝ)
        ≤ C * (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) / Real.log X ^ A := by
  intro ε hε hεδ A' hA'
  obtain ⟨C0, hC0, hM⟩ := hMRT
  obtain ⟨B, hB⟩ := hS5 ε hε hεδ
  set B' : ℝ := max B 2 with hB'def
  have hB'2 : (2 : ℝ) ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  obtain ⟨K, c, X0, hK, hc, hobj⟩ := hB (A' + B') (by linarith)
  refine ⟨K + 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A', max X0 (Real.exp 2), fun X hX => ?_⟩
  have hXX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hXe
  have hlogX2 : 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe
  have hX1 : 1 ≤ X := by have := Real.add_one_le_exp 2; linarith
  obtain ⟨o'⟩ := hobj X hXX0
  set Y := X ^ (21 / 40 + ε) with hYdef
  set H := Y ^ (1 / 9 + 2 * ε) with hHdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hX1 (by linarith)
  have hYpos : 0 < Y := by linarith
  have o := o'.toSec5 hYpos.le
  have hH1 : 1 ≤ H := Real.one_le_rpow hY1 (by linarith)
  have hLY : Real.log X / 2 ≤ Real.log Y := logY_ge_half_logX hX1 hε.le
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hlXpos : 0 < Real.log X := by linarith
  have hP := prop21_finite hM (supp X) (LamCut X Y) (LamP X) o.ω o.ν o.T o.Tp X H
    (K * Y * L ^ (-(A' + B'))) (c * Y / 4) hH1 (by positivity)
    (LamCut_supp X Y) o.omega_supp o.nu_supp o.T_supp o.Tp_supp
    (LamCut_nonneg X Y) o.Tp_nonneg o.nu_le (omega_le_LamCut o) o.cor43 o.lemma42
  have hsplit := EXH_le_split X Y H c hc hYpos o.ω o.T
  have hmt := o.mainTerm
  have hsa : sqn (supp X) (LamCut X Y) ≤ 12 * Y * L ^ B' := by
    have h1 := sqn_LamCut_le hX1 hYpos.le
    have hlx : Real.log X ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have hL2 : L ^ 2 ≤ L ^ B' := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hL1 hB'2
    calc sqn (supp X) (LamCut X Y) ≤ (2 * Y + 1) * Real.log X ^ 2 := h1
      _ ≤ (3 * Y) * (4 * L ^ B') :=
          mul_le_mul (by linarith) (by linarith) (sq_nonneg _) (by linarith)
      _ = 12 * Y * L ^ B' := by ring
  have hsω : sqn (supp X) o.ω ≤ K * Y * L ^ B' :=
    le_trans o.omega_norm (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 hBB') (mul_nonneg hK hYpos.le))
  have hH0 : 0 ≤ H := by linarith
  have hlXL : Real.log X ≤ 2 * L := by linarith
  have harith := final_arith hC0 hK hc hYpos hH0 hL1 hlXpos hlXL hA'.le hsa hsω
  have hmt' : K * H / Real.log X ^ (A' + B') ≤ K * H / Real.log X ^ A' := by
    apply div_le_div_of_nonneg_left (mul_nonneg hK (by linarith))
      (Real.rpow_pos_of_pos hlXpos _)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc (EXH X H : ℝ) ≤ _ := hsplit
    _ ≤ K * H / Real.log X ^ (A' + B') +
        C0 * H * (sqn (supp X) (LamCut X Y) + sqn (supp X) o.ω) *
          (K * Y * L ^ (-(A' + B'))) / (c * Y / 4) ^ 2 := add_le_add hmt hP
    _ ≤ K * H / Real.log X ^ A' +
        16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A' * H / Real.log X ^ A' :=
        add_le_add hmt' harith
    _ = (K + 16 * C0 * K * (12 + K) / c ^ 2 * 2 ^ A') * H / Real.log X ^ A' := by ring

/-- P0074 Theorem 1.1, `ShortIntervalLogSaving (7/120)`, CONDITIONAL ON `ShortSecondMoment` and
`Section5InputsSmall`. The full interval input is the lab's unconditional
`exceptional_logPowerSaving`. If `ε' < 1/18` and `(21/40+ε)(1/9+2ε) = 7/120 + ε'`, then
`ε < ε' < 1/18`, so only the restricted bundle is used. -/
theorem thm1_1_of_section5Small (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5InputsSmall) : ShortIntervalLogSaving (7 / 120) := by
  apply logSaving_of_below (δ := 1 / 18) (by norm_num)
  apply logSavingBelow_of_exactLengthBelow (by norm_num) _
    LeanLab.PNTPort.PsiChi.exceptional_logPowerSaving
  intro ε' hε' hε'δ A hA
  obtain ⟨ε, hε, hεeq⟩ := exists_lemma51_eps hε'
  have hεε' : ε ≤ ε' := by rw [lemma51_exponent] at hεeq; nlinarith
  obtain ⟨C, X0, hC⟩ := core_of_section5Small hMRT hS5 ε hε (by linarith) A hA
  refine ⟨C, max X0 0, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
  have hrw : (X ^ (21 / 40 + ε)) ^ (1 / 9 + 2 * ε) = X ^ (7 / 120 + ε') := by
    rw [← Real.rpow_mul hX0, hεeq]
  have := hC X (le_trans (le_max_left _ _) hX)
  rwa [hrw] at this

/-- The goldbach corollary: CONDITIONAL ON `ShortSecondMoment` and `Section5InputsSmall`, every
interval `[X - H, X]` with `X^{7/120+ε} < H ≤ X`, `X` large, holds an even Goldbach sum. -/
theorem goldbach_short_of_section5Small (hMRT : ∃ C0 : ℝ, 0 ≤ C0 ∧ ShortSecondMoment C0)
    (hS5 : Section5InputsSmall) : GoldbachInShortIntervals (7 / 120) :=
  goldbach_in_short_intervals_of_grimmelt (thm1_1_of_section5Small hMRT hS5)

end LeanLab.Grimmelt2019.Section5Small
#print axioms LeanLab.Grimmelt2019.Section5Small.window_large
#print axioms LeanLab.Grimmelt2019.Section5Small.window_has_integer
#print axioms LeanLab.Grimmelt2019.Section5Small.prime_in_window_of_objects
#print axioms LeanLab.Grimmelt2019.Section5Small.logSaving_of_below
#print axioms LeanLab.Grimmelt2019.Section5Small.logSavingBelow_of_exactLengthBelow
#print axioms LeanLab.Grimmelt2019.Section5Small.core_of_section5Small
#print axioms LeanLab.Grimmelt2019.Section5Small.thm1_1_of_section5Small
#print axioms LeanLab.Grimmelt2019.Section5Small.goldbach_short_of_section5Small
