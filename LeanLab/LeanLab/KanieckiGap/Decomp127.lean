/-
P0022, Section 3, pages 371 to 373. The cited interval input in the
KanieckiGap representation, assembled from the paper's existing range proofs.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.Final
import LeanLab.Kaniecki1995.Eq23Use

namespace LeanLab.KanieckiGap.Decomp127

open Real

/-- LEAF. Page 371, the gap definition. Both lab representations use the same successor. -/
theorem nextPrime_eq (p : ℕ) :
    LeanLab.Kaniecki1995.nextPrime p = KanieckiGap.nextPrime p := by
  rfl

/-- LEAF. Page 371, the gap definition. At a natural argument the two maxima agree. -/
theorem lam_nat_eq (x : ℕ) :
    LeanLab.Kaniecki1995.lam (x : ℝ) = KanieckiGap.lam x := by
  unfold LeanLab.Kaniecki1995.lam KanieckiGap.lam
  rw [Nat.floor_natCast]
  have hc : (x : ℝ) ≤ 7 ↔ x ≤ 7 := by norm_cast
  simp only [hc]
  rfl

/-- LEAF. Page 371 and reference 16. A bound on all left endpoints implies
 the assigned folder's weaker bound on right endpoints. CONDITIONAL ON Young-Potler. -/
theorem youngPotler_of_paper (hYP : LeanLab.Kaniecki1995.YoungPotler) :
    KanieckiGap.YoungPotler := by
  intro p hp hnext
  have hlt := (KanieckiGap.nextPrime_spec p).1
  have hpx : p ≤ 72630000000000 := by norm_num at hnext ⊢; omega
  have hgap := LeanLab.Kaniecki1995.gap_le_lam
    (x := 72630000000000) (by norm_num) hp (by exact_mod_cast hpx)
  have hmax : LeanLab.Kaniecki1995.lam 72630000000000 ≤ 778 := by
    unfold LeanLab.Kaniecki1995.YoungPotler at hYP
    exact_mod_cast hYP
  exact hgap.trans hmax

/-- LEAF. Page 371, Lemma 6. The integer version extends to real arguments
 because lambda depends only on the floor and the displayed bound increases.
 CONDITIONAL ON Schoenfeld61 and Young-Potler. -/
theorem lemma6_real (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) : LeanLab.Kaniecki1995.Lemma6 := by
  intro _ x hx
  have hx0 : 0 ≤ x := by linarith
  have hf : 23 * 10 ^ 8 ≤ ⌊x⌋₊ := by
    exact Nat.le_floor (by norm_num at hx ⊢; exact hx)
  have hx7 : ¬ x ≤ 7 := by linarith
  have hf7 : ¬ ⌊x⌋₊ ≤ 7 := by omega
  have hlam : LeanLab.Kaniecki1995.lam x = KanieckiGap.lam ⌊x⌋₊ := by
    simp only [LeanLab.Kaniecki1995.lam, KanieckiGap.lam,
      if_neg hx7, if_neg hf7]
    rfl
  rw [hlam]
  have h := KanieckiGap.lemma6 hS hY ⌊x⌋₊ hf
  change (KanieckiGap.lam ⌊x⌋₊ : ℝ) < LeanLab.Kaniecki1995.gL6 x
  exact h.trans_le (LeanLab.Kaniecki1995.gL6_mono
    (by exact_mod_cast (show 1 ≤ ⌊x⌋₊ by omega)) (Nat.floor_le hx0))

/-- LEAF. Page 371, first range. The paper's gap table gives an interval of
 length 18. CONDITIONAL ON Young-Potler, reference 16. -/
theorem small_range (hYP : LeanLab.Kaniecki1995.YoungPotler)
    (x : ℕ) (hx : x ≤ 72630000000000) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      x ≤ p + q ∧ p + q ≤ x + 14045 * 10 ^ 8 := by
  obtain ⟨p, q, hp, hq, op, oq, hlo, hhi⟩ := LeanLab.Kaniecki1995.range1 hYP x hx
  exact ⟨p, q, hp, op, hq, oq, hlo, by omega⟩

/-- LEAF. Page 371, second range. Reuse the paper reduction with its
 established extension to exp 78.5. CONDITIONAL ON RH, Schoenfeld61 and Young-Potler. -/
theorem middle_range (hRH : RiemannHypothesis) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hYP : LeanLab.Kaniecki1995.YoungPotler) (x : ℕ)
    (hx1 : 72630000000000 < x) (hx2 : (x : ℝ) ≤ Real.exp 78.5) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      x ≤ p + q ∧ p + q ≤ x + 14045 * 10 ^ 8 := by
  obtain ⟨p, q, hp, hq, op, oq, hlo, hhi⟩ := LeanLab.Kaniecki1995.range2 hRH
    (lemma6_real hS (youngPotler_of_paper hYP)) hYP x hx1 hx2
  exact ⟨p, q, hp, op, hq, oq, hlo, hhi⟩

/-- LEAF. Pages 372 and 373, displays 23 to 27. The measure and numerical
 steps are already proved in the paper folder. CONDITIONAL ON RH and Lemma 5. -/
theorem large_range (hRH : RiemannHypothesis) (h5 : LeanLab.Kaniecki1995.Lemma5)
    (x : ℕ) (hx1 : Real.exp 78.5 < (x : ℝ))
    (hx2 : (x : ℝ) ≤ LeanLab.Kaniecki1995.n0) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Prime ∧ Odd q ∧
      x ≤ p + q ∧ p + q ≤ x + 14045 * 10 ^ 8 := by
  obtain ⟨p, q, hp, hq, op, oq, hlo, hhi⟩ :=
    LeanLab.Kaniecki1995.range34 hRH h5 LeanLab.Kaniecki1995.eq23 x hx1 hx2
  refine ⟨p, q, hp, op, hq, oq, ?_, ?_⟩
  · exact_mod_cast hlo
  · have : ((p + q : ℕ) : ℝ) ≤ ((x + 14045 * 10 ^ 8 : ℕ) : ℝ) := by
      push_cast at hhi ⊢
      norm_num at hhi ⊢
      exact hhi
    exact_mod_cast this

/-- Page 373, the exact cited IntervalProp at the paper cutoff.
 The assembly has no admitted step. CONDITIONAL ON RH, Lemma 5,
 Schoenfeld61 and Young-Potler. -/
theorem interval_from_paper (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.Lemma5) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hYP : LeanLab.Kaniecki1995.YoungPotler) :
    KanieckiGap.IntervalProp (14045 * 10 ^ 8) ⌊LeanLab.Kaniecki1995.n0⌋₊ := by
  intro x hx
  by_cases hsmall : x ≤ 72630000000000
  · exact small_range hYP x hsmall
  · by_cases hmid : (x : ℝ) ≤ Real.exp 78.5
    · exact middle_range hRH hS hYP x (by omega) hmid
    · exact large_range hRH h5 x (lt_of_not_ge hmid)
        ((by exact_mod_cast hx : (x : ℝ) ≤ (⌊LeanLab.Kaniecki1995.n0⌋₊ : ℝ)).trans
          (Nat.floor_le (Real.exp_pos _).le))

end LeanLab.KanieckiGap.Decomp127

#print axioms LeanLab.KanieckiGap.Decomp127.nextPrime_eq
#print axioms LeanLab.KanieckiGap.Decomp127.lam_nat_eq
#print axioms LeanLab.KanieckiGap.Decomp127.youngPotler_of_paper
#print axioms LeanLab.KanieckiGap.Decomp127.lemma6_real
#print axioms LeanLab.KanieckiGap.Decomp127.small_range
#print axioms LeanLab.KanieckiGap.Decomp127.middle_range
#print axioms LeanLab.KanieckiGap.Decomp127.large_range
#print axioms LeanLab.KanieckiGap.Decomp127.interval_from_paper
