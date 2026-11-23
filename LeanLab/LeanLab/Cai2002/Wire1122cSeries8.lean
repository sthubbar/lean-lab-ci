/-
Wiring of the S77 proofs into Nathanson Theorem 9.4, the series solution of the linear sieve
system as quoted by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, page 6, displays 8 and 13 to 18. This file restates the assembly of
Split1122bBoundary8.lean and Split1122bSeries8.lean with the S71 and S77 twins in place of
the LEAFs they prove, so that the open steps under leaf306_series_solve8_wired1122c are
exactly the LEAFs still unproved.
No new LEAF and no new definition.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122cAdjQ8
import LeanLab.Cai2002.Prove1122cLimits8
import LeanLab.Cai2002.Prove1122cConst8

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- f(2) = 0, E(2) = 1, as eSumB8_two of Split1122bBoundary8.lean, with the S77 twins of
leafB8_IQ_const and leafB8_IQ_tendsto. -/
theorem eSumB8_two_1122c : eSumB8 2 = 1 := by
  have hev : qInvB8 =ᶠ[Filter.atTop] fun _ => qInvB8 3 :=
    Filter.eventually_atTop.2 ⟨3, fun s hs => leafB8_IQ_const_s77 leaf8_continuous_s77 s hs⟩
  have h1 : Filter.Tendsto qInvB8 Filter.atTop (nhds (qInvB8 3)) :=
    tendsto_const_nhds.congr' hev.symm
  have h0 : qInvB8 3 = 0 := tendsto_nhds_unique h1 leafB8_IQ_tendsto_s77
  have h3 := leafB8_IQ3_s77
  linarith

/-- F(3) = 2 e ^ γ / 3, as oSumB8_three of Split1122bBoundary8.lean, with the S77 twins. -/
theorem oSumB8_three_1122c : oSumB8 3 = 2 * exp eulerMascheroniConstant / 3 - 1 := by
  obtain ⟨q, hq, hK⟩ := leafB8_adjoint_proved1122c
  have hev : jInvB8 q =ᶠ[Filter.atTop] fun _ => jInvB8 q 3 :=
    Filter.eventually_atTop.2 ⟨3, fun s hs => leafB8_J_const_s77 leaf8_continuous_s77 q hq s hs⟩
  have h1 : Filter.Tendsto (jInvB8 q) Filter.atTop (nhds (jInvB8 q 3)) :=
    tendsto_const_nhds.congr' hev.symm
  have h2 : jInvB8 q 3 = 2 := tendsto_nhds_unique h1 (leafB8_J_tendsto_s77 q hq)
  rw [leafB8_J3_s77 q hq eSumB8_two_1122c, hK] at h2
  have hE : exp (-eulerMascheroniConstant) * exp eulerMascheroniConstant = 1 := by
    rw [← exp_add]; simp
  have h3 : 3 * (1 + oSumB8 3) = 2 * exp eulerMascheroniConstant := by
    calc 3 * (1 + oSumB8 3)
        = 3 * (1 + oSumB8 3) * (exp (-eulerMascheroniConstant) *
            exp eulerMascheroniConstant) := by rw [hE, mul_one]
      _ = 2 * exp eulerMascheroniConstant := by rw [← mul_assoc, h2]
  linarith

/-- Twin of leaf8_F3, statement verbatim, wired. -/
theorem leaf8_F3_1122c :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
  convert (parity_summableB8 Odd 3 (fun _ h => Or.inl ⟨h, by norm_num⟩) (by norm_num)).hasSum
    using 1
  exact oSumB8_three_1122c.symm

/-- Twin of leaf8_f2, statement verbatim, wired. -/
theorem leaf8_f2_1122c :
    HasSum (fun n : ℕ => if Even n then bjsF306 n 2 else 0) 1 := by
  convert (parity_summableB8 Even 2 (fun _ h => Or.inr ⟨h, le_rfl⟩) (by norm_num)).hasSum
    using 1
  exact eSumB8_two_1122c.symm

/-- BJS display 13 on [1, 3] from display 17 and F(3), as hasSum_odd_le3_s8 of
Split1122bSeries8.lean, with the wired twin of leaf8_F3. -/
theorem hasSum_odd_le3_1122c (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0)
      (2 * exp eulerMascheroniConstant / s - 1) := by
  have hs0 : 0 < s := by linarith
  have h3 : HasSum (fun n : ℕ => if Odd n ∧ 3 ≤ n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
    convert leaf8_F3_1122c using 1
    funext n
    match n with
    | 0 => simp
    | 1 => simp [bjsF306]
    | m + 2 =>
      by_cases ho : Odd (m + 2)
      · rw [if_pos ⟨ho, three_le_of_odd_s8 m ho⟩, if_pos ho]
      · rw [if_neg (fun h => ho h.1), if_neg ho]
  have hsum := (hasSum_ite_eq 1 ((3 - s) / s)).add (h3.mul_left (3 / s))
  convert hsum using 1
  · funext n
    rw [odd_terms_le3_s8 s hs1 hs3 n]
  · field_simp
    ring

/-- Twin of leaf306_series_solve8 of Split306Theorem6.lean, statement verbatim, Nathanson
Theorem 9.4 existence half, assembled by assembly_s8 from the S71 and S77 twins. Summability
comes from parity_summableB8, the Lemma 8 bound, not from leaf8_summable_twin, which goes
through display 18 with Table 2 and so through BJS Lemma 7, suspected false at n = 33. -/
theorem leaf306_series_solve8_wired1122c :
    ∃ F' f' : ℝ → ℝ, LeanLab.ChenExplicit.IsLinearSieveFns F' f' ∧
      (∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F' s - 1)) ∧
      (∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f' s)) := by
  refine assembly_s8 (fun s => ∑' n : ℕ, if Odd n then bjsF306 n s else 0)
    (fun s => ∑' n : ℕ, if Even n then bjsF306 n s else 0)
    (fun s hs => (parity_summableB8 Odd s (fun _ h => Or.inl ⟨h, hs⟩) (by linarith)).hasSum)
    (fun s hs => (parity_summableB8 Even s (fun _ h => Or.inr ⟨h, hs⟩) (by linarith)).hasSum)
    (fun s hs1 hs3 => (hasSum_odd_le3_1122c s hs1 hs3).tsum_eq) leaf8_f2_1122c.tsum_eq
    leaf8_continuous_s77.1 leaf8_continuous_s77.2 leaf8_deriv_even_twin
    leaf8_deriv_odd_twin.1 ?_
  have h := leaf8_deriv_odd_twin.2
  simpa [show (3 : ℝ) - 1 = 2 by norm_num] using h

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.eSumB8_two_1122c
#print axioms LeanLab.Cai2002.oSumB8_three_1122c
#print axioms LeanLab.Cai2002.leaf306_series_solve8_wired1122c
