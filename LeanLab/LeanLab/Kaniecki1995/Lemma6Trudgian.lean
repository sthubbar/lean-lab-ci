/-
P0022, Kaniecki 1995. PC 20261020T1603Z-26078, unit U-1253, T1.
Lemma 6 of p. 371, the cited Schoenfeld 1976 consequence λ(x) < (1/4π) √((1 + 1/16597) x) log² x
under RH for x ≥ 2.3 · 10^9, is here PROVED CONDITIONAL ON Trudgian's N(T) bound `TrudgianN70`,
Schoenfeld's ψ - θ bounds `Schoenfeld` and the maximal gap input `GapBound1476`, through
CLOUD 20261020T1518Z-cloud45's `kaniecki_lemma6_RH_trudgian`, verified by PC U-1245, and a floor
bridge from the integer λ of KanieckiGap to the real λ of this folder. RH stays inside `Lemma6`.
Then the Theorem's two parts and the interval property no longer take Lemma 6.
AI wrote this Lean code. Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Eq23Use
import LeanLab.PNTPort.ExplicitPsi1.DudekCorollaries

namespace LeanLab.Kaniecki1995.L6T

open LeanLab.Kaniecki1995

/-- the real `λ` of this folder at `x ≥ 8` is the integer `λ` of KanieckiGap at `⌊x⌋` -/
theorem lam_eq_floor {x : ℝ} (hx : 8 ≤ x) : lam x = LeanLab.KanieckiGap.lam ⌊x⌋₊ := by
  have h1 : ¬ x ≤ 7 := by linarith
  have h2 : ¬ ⌊x⌋₊ ≤ 7 := by
    have : (8 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    omega
  unfold lam LeanLab.KanieckiGap.lam
  rw [if_neg h1, if_neg h2]
  rfl

/-- `gL6` is monotone on `[1, ∞)` -/
theorem gL6_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : gL6 a ≤ gL6 b := by
  unfold gL6
  have hc : (0 : ℝ) < 1 + 1 / 16597 := by norm_num
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hsq : √((1 + 1 / 16597) * a) ≤ √((1 + 1 / 16597) * b) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hpi : 0 ≤ 1 / (4 * Real.pi) := by positivity
  have hl2 : Real.log a ^ 2 ≤ Real.log b ^ 2 := by nlinarith
  have hs0 : 0 ≤ √((1 + 1 / 16597) * a) := Real.sqrt_nonneg _
  calc 1 / (4 * Real.pi) * √((1 + 1 / 16597) * a) * Real.log a ^ 2
      ≤ 1 / (4 * Real.pi) * √((1 + 1 / 16597) * b) * Real.log a ^ 2 := by gcongr
    _ ≤ 1 / (4 * Real.pi) * √((1 + 1 / 16597) * b) * Real.log b ^ 2 := by gcongr

/-- **Kaniecki 1995 Lemma 6**, CONDITIONAL ON `TrudgianN70`, `Schoenfeld` and `GapBound1476`;
RH is the hypothesis inside `Lemma6`. -/
theorem lemma6_of_trudgian
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) : Lemma6 := by
  intro hRH x hx
  set n := ⌊x⌋₊ with hn
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hn1 : (23 * 10 ^ 8 : ℕ) ≤ n := Nat.le_floor (by push_cast; linarith)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hn8 : (8 : ℝ) ≤ n := by
    have : (8 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have key := LeanLab.PNTPort.ExplicitPsi1.Trivial.kaniecki_lemma6_RH_trudgian hRH hN hSch hG n hn1
  rw [lam_eq_floor (by linarith)]
  calc (LeanLab.KanieckiGap.lam n : ℝ)
      < 1 / (4 * Real.pi) * √((1 + 1 / 16597) * n) * Real.log n ^ 2 := key
    _ = gL6 n := rfl
    _ ≤ gL6 x := gL6_mono (by linarith) hnx

/-- Interval property, CONDITIONAL ON RH, Lemma 5, Young-Potler and the three Dudek chain inputs. -/
theorem interval_of_trudgian (hRH : RiemannHypothesis) (h5 : Lemma5)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) : IntervalProperty :=
  interval_of' hRH h5 (lemma6_of_trudgian hN hSch hG) hYP

/-- Theorem, odd part, CONDITIONAL ON Lemma 5, Young-Potler, Sinisalo, Chen-Wang and the three
Dudek chain inputs; no Lemma 6. -/
theorem theoremOdd_of_trudgian (h5 : Lemma5)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) (hS : Sinisalo)
    (hCW : ChenWang) : TheoremOdd :=
  theoremOdd_of' h5 (lemma6_of_trudgian hN hSch hG) hYP hS hCW

/-- Theorem, even part, CONDITIONAL ON Lemma 5, Young-Potler, Chen-Wang and the three Dudek
chain inputs; no Lemma 6. -/
theorem theoremEven_of_trudgian (h5 : Lemma5)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) (hCW : ChenWang) :
    TheoremEven :=
  theoremEven_of' h5 (lemma6_of_trudgian hN hSch hG) hYP hCW

/-- vacuity of the range: `2.3 · 10^9` meets `8 ≤ x`, so the floor bridge applies on all of
Lemma 6's range -/
theorem range_ok : (8 : ℝ) ≤ 2.3e9 := by norm_num

end LeanLab.Kaniecki1995.L6T
