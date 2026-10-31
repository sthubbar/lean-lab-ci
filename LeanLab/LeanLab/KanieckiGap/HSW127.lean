/-
P0022, pages 371 to 373. Original guarded interval route with the existing
Hasanalizade-Shen-Wong zero count inputs in place of the Schoenfeld61 citation.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.Guarded127
import LeanLab.PNTPort.ExplicitPsi1.KanieckiGapHSW

namespace LeanLab.KanieckiGap.HSW127

open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.ChirreHagen2025.SmoothT2 (Ordinates14)
open LeanLab.SchnirelmannConstant

/-- Page 371, Lemma 6 in the real representation. Reuse lemma6_hsw and the
proved floor bridge. CONDITIONAL ON the HSW counts, ordinate exclusion,
Young-Potler and RH inside the paper statement. -/
theorem lemma6_real_hsw (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ)
    (h14 : Ordinates14 gZ) (hY : KanieckiGap.YoungPotler) :
    LeanLab.Kaniecki1995.Lemma6 := by
  intro hRH x hx
  have hx0 : 0 ≤ x := by linarith
  have hf : 23 * 10 ^ 8 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num at hx ⊢; exact hx)
  have hnat := KanieckiGap.lemma6_hsw hRH hNz hHz h14 hY ⌊x⌋₊ hf
  rw [LeanLab.Kaniecki1995.L6T.lam_eq_floor (by linarith)]
  calc (KanieckiGap.lam ⌊x⌋₊ : ℝ)
      < LeanLab.Kaniecki1995.gL6 ⌊x⌋₊ := hnat
    _ ≤ LeanLab.Kaniecki1995.gL6 x := LeanLab.Kaniecki1995.gL6_mono
      (by exact_mod_cast (show 1 ≤ ⌊x⌋₊ by omega)) (Nat.floor_le hx0)

/-- Pages 371 to 373. The exact cited interval input with Schoenfeld61
replaced by the existing HSW route. CONDITIONAL ON RH, guarded Lemma 5,
the HSW counts, ordinate exclusion and Young-Potler. -/
theorem interval_hsw (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.L5.Lemma5G) (hNz : HSWN70 gZ)
    (hHz : HSWHead14 gZ) (h14 : Ordinates14 gZ) (hY : KanieckiGap.YoungPotler) :
    IntervalProp (14045 * 10 ^ 8) ⌊LeanLab.Kaniecki1995.n0⌋₊ :=
  Guarded127.intervalProp_of_paper (LeanLab.Kaniecki1995.L5.interval_ofG hRH h5
    LeanLab.Kaniecki1995.eq23 (lemma6_real_hsw hNz hHz h14 hY)
    (EndpointTransfer127.paper_of_right hY))

/-- Pages 371 to 373. Both original paper conclusions through the guarded
interval route. CONDITIONAL ON RH, guarded Lemma 5, the HSW counts,
ordinate exclusion, Young-Potler, Chen-Wang and the finite even check. -/
theorem theorem_hsw (h5 : LeanLab.Kaniecki1995.L5.Lemma5G)
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14 : Ordinates14 gZ)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang)
    (hE : EvenGoldbachUpTo (1405 * 10 ^ 9)) :
    RiemannHypothesis →
      (∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n) ∧
      (∀ n : ℕ, Even n → AtMostPrimes 4 n) := by
  intro hRH
  have hI := interval_hsw hRH h5 hNz hHz h14 hY
  have hlarge : ∀ n : ℕ, Odd n → ⌊LeanLab.Kaniecki1995.n0⌋₊ < n → IsTernarySum n := by
    intro n ho hn
    exact hCW n ho (Nat.lt_of_floor_lt hn).le
  exact ⟨KanieckiGap.kaniecki_odd_of hI hlarge hY,
    PaperAssembly127.kaniecki_even_of_interval hI hE hlarge⟩

/-- Pages 364 to 373, displays 8 and 18. Both conclusions with guarded
Lemma 5 reduced to guarded Lemma 4 and Parseval18BC. CONDITIONAL ON
those formulas, the HSW counts, ordinate exclusion, Young-Potler,
Chen-Wang, the finite even check and RH. -/
theorem theorem_hsw_lemma4_parseval (h4 : LeanLab.Kaniecki1995.L5.Lemma4G)
    (hP : LeanLab.Kaniecki1995.U7152.Parseval18BC)
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14 : Ordinates14 gZ)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang)
    (hE : EvenGoldbachUpTo (1405 * 10 ^ 9)) :
    RiemannHypothesis →
      (∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n) ∧
      (∀ n : ℕ, Even n → AtMostPrimes 4 n) :=
  theorem_hsw (LeanLab.Kaniecki1995.L5U1416.lemma5G_of_U1416 h4
    (LeanLab.Kaniecki1995.U7152.parseval1920_of_18BC hP)) hNz hHz h14 hY hCW hE

/-- Pages 362 and 373. Exactly the lab's two cited paper Props, with RH
and the paper finite verification premise inside their sealed definitions.
CONDITIONAL ON guarded Lemma 5, the HSW counts, ordinate exclusion,
Young-Potler and Chen-Wang. -/
theorem exact_paper_statements (h5 : LeanLab.Kaniecki1995.L5.Lemma5G)
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) (h14 : Ordinates14 gZ)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven := by
  constructor
  · intro hRH
    have hI := interval_hsw hRH h5 hNz hHz h14 hY
    apply KanieckiGap.kaniecki_odd_of hI
    · intro n ho hn
      exact hCW n ho (Nat.lt_of_floor_lt hn).le
    · exact hY
  · intro hRH hG
    obtain ⟨G, hG, hGb⟩ := hG
    have hI := interval_hsw hRH h5 hNz hHz h14 hY
    apply PaperAssembly127.kaniecki_even_of_interval hI
    · intro n hn h4 hhi
      exact hGb n hn h4 (by omega)
    · intro n ho hn
      exact hCW n ho (Nat.lt_of_floor_lt hn).le

end LeanLab.KanieckiGap.HSW127

#print axioms LeanLab.KanieckiGap.HSW127.lemma6_real_hsw
#print axioms LeanLab.KanieckiGap.HSW127.interval_hsw
#print axioms LeanLab.KanieckiGap.HSW127.theorem_hsw
#print axioms LeanLab.KanieckiGap.HSW127.theorem_hsw_lemma4_parseval

#print axioms LeanLab.KanieckiGap.HSW127.exact_paper_statements
