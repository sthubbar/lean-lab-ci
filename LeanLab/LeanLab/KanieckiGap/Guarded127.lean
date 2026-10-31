/-
P0022, pages 368 to 373. Preferred original-paper route with the existing
Selberg guard. The printed unguarded Lemma 5 is not used in this route.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.EndpointTransfer127
import LeanLab.Kaniecki1995.Lemma5U1416
import LeanLab.Kaniecki1995.U7152Parseval

namespace LeanLab.KanieckiGap.Guarded127

open LeanLab.SchnirelmannConstant

/-- Page 373. Transfer the paper interval property to the exact assigned Prop.
CONDITIONAL ON the paper interval property. -/
theorem intervalProp_of_paper (hI : LeanLab.Kaniecki1995.IntervalProperty) :
    IntervalProp (14045 * 10 ^ 8) ⌊LeanLab.Kaniecki1995.n0⌋₊ := by
  intro x hx
  have hxR : (x : ℝ) ≤ LeanLab.Kaniecki1995.n0 :=
    (by exact_mod_cast hx : (x : ℝ) ≤ (⌊LeanLab.Kaniecki1995.n0⌋₊ : ℝ)).trans
      (Nat.floor_le (Real.exp_pos _).le)
  obtain ⟨p, q, hp, hq, op, oq, hlo, hhi⟩ := hI x hxR
  exact ⟨p, q, hp, op, hq, oq, hlo, hhi⟩

/-- Pages 368 to 373. The exact cited interval Prop from the guarded Lemma 5.
CONDITIONAL ON RH, guarded Lemma 5, Schoenfeld61 and Young-Potler. -/
theorem interval_guarded (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.L5.Lemma5G) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) :
    IntervalProp (14045 * 10 ^ 8) ⌊LeanLab.Kaniecki1995.n0⌋₊ :=
  intervalProp_of_paper (LeanLab.Kaniecki1995.L5.interval_ofG hRH h5
    LeanLab.Kaniecki1995.eq23 (Decomp127.lemma6_real hS hY)
    (EndpointTransfer127.paper_of_right hY))

/-- Pages 368 to 373. The odd conclusion with the guard checked at the paper
parameters. CONDITIONAL ON RH, guarded Lemma 5, Schoenfeld61,
Young-Potler and Chen-Wang. -/
theorem odd_guarded (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.L5.Lemma5G) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := by
  apply KanieckiGap.kaniecki_odd_of (interval_guarded hRH h5 hS hY)
  · intro n ho hn
    exact hCW n ho (Nat.lt_of_floor_lt hn).le
  · exact hY

/-- Pages 368 to 373. The even conclusion from the guarded interval route.
CONDITIONAL ON RH, guarded Lemma 5, Schoenfeld61, Young-Potler,
Chen-Wang and the finite even check. -/
theorem even_guarded (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.L5.Lemma5G) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang)
    (hE : EvenGoldbachUpTo (1405 * 10 ^ 9)) :
    ∀ n : ℕ, Even n → AtMostPrimes 4 n := by
  apply PaperAssembly127.kaniecki_even_of_interval (interval_guarded hRH h5 hS hY) hE
  intro n ho hn
  exact hCW n ho (Nat.lt_of_floor_lt hn).le

/-- Pages 364 to 373, displays 8 and 18. Both conclusions with guarded Lemma 5
discharged by the existing Lemma 4 and Parseval reductions. CONDITIONAL ON
guarded Lemma 4, Parseval18BC, Schoenfeld61, Young-Potler, Chen-Wang,
the finite even check and RH. -/
theorem theorem_of_lemma4_parseval (h4 : LeanLab.Kaniecki1995.L5.Lemma4G)
    (hP : LeanLab.Kaniecki1995.U7152.Parseval18BC)
    (hS : LeanLab.DERZ1997.Schoenfeld61) (hY : KanieckiGap.YoungPotler)
    (hCW : LeanLab.Kaniecki1995.ChenWang) (hE : EvenGoldbachUpTo (1405 * 10 ^ 9)) :
    RiemannHypothesis →
      (∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n) ∧
      (∀ n : ℕ, Even n → AtMostPrimes 4 n) := by
  intro hRH
  have h5 := LeanLab.Kaniecki1995.L5U1416.lemma5G_of_U1416 h4
    (LeanLab.Kaniecki1995.U7152.parseval1920_of_18BC hP)
  exact ⟨odd_guarded hRH h5 hS hY hCW, even_guarded hRH h5 hS hY hCW hE⟩

end LeanLab.KanieckiGap.Guarded127

#print axioms LeanLab.KanieckiGap.Guarded127.intervalProp_of_paper
#print axioms LeanLab.KanieckiGap.Guarded127.interval_guarded
#print axioms LeanLab.KanieckiGap.Guarded127.odd_guarded
#print axioms LeanLab.KanieckiGap.Guarded127.even_guarded
#print axioms LeanLab.KanieckiGap.Guarded127.theorem_of_lemma4_parseval
