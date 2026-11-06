import LeanLab.LPZ2007.D4Asymptotic

/-!
P0045 preprint page 3, the finite residue dependence of C of k and N.
The count is display 18 and the coefficient series is display 23 on page 8.
DOI https://doi.org/10.1112/blms/bdm062.
The proved Romanov tail makes the cutoff uniform over all positive k.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Constant407

open Finset Filter Real

/-- P0045 page 8, display 18. The finite count depends only on N modulo d. -/
theorem jd_modEq {d k N M : ℕ} (h : N ≡ M [MOD d]) : jd d k N = jd d k M := by
  classical
  unfold jd
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ν hν
  have hdiff : (d : ℤ) ∣ (M : ℤ) - N := Nat.modEq_iff_dvd.1 h
  constructor
  · intro hN
    convert dvd_add hdiff hN using 1 <;> ring
  · intro hM
    convert dvd_sub hM hdiff using 1 <;> ring

/-- P0045 page 8, display 23. Each coefficient has the same residue dependence. -/
theorem cTerm_modEq {d k N M : ℕ} (h : N ≡ M [MOD d]) :
    cTerm k N d = cTerm k M d := by
  unfold cTerm
  rw [jd_modEq h]

/-- P0045 preprint page 3, the finite residue precision remark.
One cutoff suffices for every positive k. Only odd squarefree moduli are required. -/
theorem finite_residues_determine_constant (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ N M : ℕ,
      (∀ d : ℕ, d < D → OddSqf d → N ≡ M [MOD d]) →
        |Ckn k N - Ckn k M| < ε := by
  obtain ⟨D, hD⟩ := ((tendsto_order.1 (tendsto_sum_nat_add romanovTerm)).2
    (ε / 2) (by positivity)).exists_forall_of_atTop
  refine ⟨D, ?_⟩
  intro k hk N M hmod
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hhead : (∑ d ∈ range D, cTerm (j + 1) N d) =
      ∑ d ∈ range D, cTerm (j + 1) M d := by
    apply sum_congr rfl
    intro d hd
    by_cases ho : OddSqf d
    · exact cTerm_modEq (hmod d (mem_range.1 hd) ho)
    · simp only [cTerm, if_neg ho]
  obtain ⟨hN0, hN⟩ := D4Asymptotic.coefficient_tail D j N
  obtain ⟨hM0, hM⟩ := D4Asymptotic.coefficient_tail D j M
  have ht : (∑' n, romanovTerm (n + D)) < ε / 2 := hD D le_rfl
  have hleft : |Ckn (j + 1) N - ∑ d ∈ range D, cTerm (j + 1) N d| < ε / 2 := by
    rw [abs_of_nonneg hN0]
    exact hN.trans_lt ht
  have hright : |Ckn (j + 1) M - ∑ d ∈ range D, cTerm (j + 1) M d| < ε / 2 := by
    rw [abs_of_nonneg hM0]
    exact hM.trans_lt ht
  calc
    |Ckn (j + 1) N - Ckn (j + 1) M| =
        |(Ckn (j + 1) N - ∑ d ∈ range D, cTerm (j + 1) N d) -
          (Ckn (j + 1) M - ∑ d ∈ range D, cTerm (j + 1) M d)| := by
      rw [hhead]
      congr 1
      ring
    _ ≤ |Ckn (j + 1) N - ∑ d ∈ range D, cTerm (j + 1) N d| +
        |Ckn (j + 1) M - ∑ d ∈ range D, cTerm (j + 1) M d| := abs_sub _ _
    _ < ε := by linarith

/-- P0045 preprint page 3, a periodic form of the finite residue precision remark.
For each precision a positive common period approximates all positive k uniformly. -/
theorem common_approximate_period (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ,
      |Ckn k (N + Q) - Ckn k N| < ε := by
  obtain ⟨D, hD⟩ := finite_residues_determine_constant ε hε
  refine ⟨D.factorial, Nat.factorial_pos D, ?_⟩
  intro k hk N
  apply hD k hk (N + D.factorial) N
  intro d hd ho
  have hdpos : 0 < d := Nat.pos_of_ne_zero ho.2.ne_zero
  have hdiv : d ∣ D.factorial := Nat.dvd_factorial hdpos hd.le
  have hzero : D.factorial ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.2 hdiv
  simpa using hzero.add_left N

end LeanLab.LPZ2007.Constant407

#print axioms LeanLab.LPZ2007.Constant407.jd_modEq
#print axioms LeanLab.LPZ2007.Constant407.cTerm_modEq
#print axioms LeanLab.LPZ2007.Constant407.finite_residues_determine_constant
#print axioms LeanLab.LPZ2007.Constant407.common_approximate_period
