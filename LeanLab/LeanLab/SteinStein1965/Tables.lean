/-
Stein and Stein 1965, P0073, unit U-0954, run 20261018T1603Z-12862.
Kernel checks of the paper's printed S-sequence data for small parameters, by
`decide +kernel` on the Lean S-algorithm of Statements.lean. No `native_decide`.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

/-! ### Section 3, p. 428: the first 22 terms of `{b_i}_3` and `{b_i}_11` -/

/-- p. 428: "The first 22 terms of `{b_i}_3` are: 3, 5, 7, 13, 19, 23, 31, 37, 43, 47, 53, 61,
79, 83, 109, 113, 101, 131, 139, 157, 167, 199." Run to `2n* = 224`. -/
theorem first22_p3 : (sPrime 3 224).1.take 22 =
    [3, 5, 7, 13, 19, 23, 31, 37, 43, 47, 53, 61, 79, 83, 109, 113, 101, 131, 139, 157, 167,
      199] := by
  decide +kernel

/-- p. 428: "For `{b_i}_11` the first 22 terms are: 11, 13, 17, 19, 29, 31, 41, 43, 53, 37,
59, 79, 73, 113, 109, 103, 107, 151, 163, 167, 179, 191." Run to `2n* = 256`. -/
theorem first22_p11 : (sPrime 11 256).1.take 22 =
    [11, 13, 17, 19, 29, 31, 41, 43, 53, 37, 59, 79, 73, 113, 109, 103, 107, 151, 163, 167,
      179, 191] := by
  decide +kernel

/-- The first 16 terms of `{b_i}_3`. -/
def first16 : List ℕ := [3, 5, 7, 13, 19, 23, 31, 37, 43, 47, 53, 61, 79, 83, 109, 113]

theorem sPrime3_122 : sPrime 3 122 = (first16, []) := by decide +kernel

theorem sPrime3_124 : sPrime 3 124 = (first16 ++ [101], []) := by decide +kernel

/-- pp. 428-429: "the first 16 terms constitute a 2-basis for the even numbers
`6 ≤ 2n ≤ 122`. To express `2n = 124` ... we must introduce the prime `b_16 = 101`:
`124 = 101 + 23`." -/
theorem backtrack_example :
    IsBasisFor first16 6 122 ∧ (¬ ∃ x ∈ first16, ∃ y ∈ first16, x + y = 124) ∧
      (sPrime 3 124).1 = first16 ++ [101] ∧ 101 + 23 = 124 ∧ 23 ∈ first16 := by
  refine ⟨?_, ?_, by rw [sPrime3_124], rfl, by decide⟩
  · have h := sAlg_basis_of_nil (primeA 3) 3 (nextA 3) 122 (by rw [← sPrime, sPrime3_122])
    rw [← sPrime, sPrime3_122] at h
    exact h
  · rw [← covers_iff]
    decide

/-! ### Table I, p. 430, header: the lower limits `N0` -/

/-- Boolean check of one header entry `(p0, N0)` on the run to `x`: every failure is below
`N0`, `2 p0 ≤ N0`, and `N0 - 2` is not a sum of two output elements. -/
def rowOK (x : ℕ) (r : ℕ × ℕ) : Bool :=
  let s := sPrime r.1 x
  s.2.all (· < r.2) && decide (2 * r.1 ≤ r.2) && !covers s.1 (r.2 - 2)

theorem rowOK_sound (x : ℕ) (r : ℕ × ℕ) (h : rowOK x r = true) :
    IsBasisFor (sPrime r.1 x).1 r.2 x ∧
      ¬ ∃ u ∈ (sPrime r.1 x).1, ∃ v ∈ (sPrime r.1 x).1, u + v = r.2 - 2 := by
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hf, h0⟩, hc⟩ := h
  refine ⟨sAlg_basis _ _ _ _ _ h0 hf, ?_⟩
  rw [← covers_iff, hc]
  simp

/-! Table I header, one declaration per `p0` so the kernel cache is freed between rows.
Each row: the failure list of the run to `2n* = 600`, and `rowOK`. -/

theorem row_1 : (sPrime 1 600).2 = [] ∧ rowOK 600 (1, 2) = true := by
  decide +kernel

theorem row_3 : (sPrime 3 600).2 = [] ∧ rowOK 600 (3, 6) = true := by
  decide +kernel

theorem row_5 : (sPrime 5 600).2 = [] ∧ rowOK 600 (5, 10) = true := by
  decide +kernel

theorem row_7 : (sPrime 7 600).2 = [16] ∧ rowOK 600 (7, 18) = true := by
  decide +kernel

theorem row_11 : (sPrime 11 600).2 = [] ∧ rowOK 600 (11, 22) = true := by
  decide +kernel

theorem row_13 : (sPrime 13 600).2 = [28] ∧ rowOK 600 (13, 30) = true := by
  decide +kernel

theorem row_71 : (sPrime 71 600).2 = [148, 164] ∧ rowOK 600 (71, 166) = true := by
  decide +kernel

theorem row_73 : (sPrime 73 600).2 = [148, 150, 154, 160, 164] ∧ rowOK 600 (73, 166) = true := by
  decide +kernel

theorem row_79 : (sPrime 79 600).2 = [160, 164, 170, 174] ∧ rowOK 600 (79, 176) = true := by
  decide +kernel

theorem row_83 : (sPrime 83 600).2 = [168, 170, 174, 176, 182, 188] ∧ rowOK 600 (83, 190) = true := by
  decide +kernel

theorem row_89 : (sPrime 89 600).2 = [180, 182, 184, 188] ∧ rowOK 600 (89, 190) = true := by
  decide +kernel

theorem row_97 : (sPrime 97 600).2 = [196] ∧ rowOK 600 (97, 198) = true := by
  decide +kernel

/-- Table I header, all twelve `N0` values, checked on the runs to `2n* = 600`:
`N0 = 2, 6, 10, 18, 22, 30, 166, 166, 176, 190, 190, 198` for
`p0 = 1, 3, 5, 7, 11, 13, 71, 73, 79, 83, 89, 97`. The paper's claim is for `x = 5 * 10^6`;
see STATEMENTS.md. -/
theorem tableI_N0_600 : TableI_N0Claim 600 := by
  intro r hr
  apply rowOK_sound
  simp only [tableI_N0, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_1.2
  · exact row_3.2
  · exact row_5.2
  · exact row_7.2
  · exact row_11.2
  · exact row_13.2
  · exact row_71.2
  · exact row_73.2
  · exact row_79.2
  · exact row_83.2
  · exact row_89.2
  · exact row_97.2

/-- `N0 - 2` is not a sum of two elements of the input set at all, so no extension of the
run can lower `N0`: for every header entry with `N0 > 2 p0`. -/
def forcedOK (r : ℕ × ℕ) : Bool :=
  decide (r.2 ≤ 2 * r.1) ||
    (List.range r.2).all fun u => !(primeA r.1 u && primeA r.1 (r.2 - 2 - u))

theorem forcedOK_sound (r : ℕ × ℕ) (h : forcedOK r = true) (h2 : 2 * r.1 < r.2) :
    ¬ ∃ u v, primeA r.1 u = true ∧ primeA r.1 v = true ∧ u + v = r.2 - 2 := by
  rintro ⟨u, v, hu, hv, huv⟩
  simp only [forcedOK, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff] at h
  rcases h with h | h
  · omega
  · rcases h u (by omega) with h | h
    · rw [hu] at h; exact absurd h (by simp)
    · have : r.2 - 2 - u = v := by omega
      rw [this, hv] at h; exact absurd h (by simp)

theorem tableI_N0_forced : ∀ r ∈ tableI_N0, 2 * r.1 < r.2 →
    ¬ ∃ u v, primeA r.1 u = true ∧ primeA r.1 v = true ∧ u + v = r.2 - 2 := by
  intro r hr h2
  exact forcedOK_sound r (List.all_eq_true.mp (show tableI_N0.all forcedOK = true by
    decide +kernel) r hr) h2

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.first22_p3
#print axioms LeanLab.SteinStein1965.first22_p11
#print axioms LeanLab.SteinStein1965.sPrime3_122
#print axioms LeanLab.SteinStein1965.sPrime3_124
#print axioms LeanLab.SteinStein1965.backtrack_example
#print axioms LeanLab.SteinStein1965.rowOK_sound
#print axioms LeanLab.SteinStein1965.row_1
#print axioms LeanLab.SteinStein1965.row_3
#print axioms LeanLab.SteinStein1965.row_5
#print axioms LeanLab.SteinStein1965.row_7
#print axioms LeanLab.SteinStein1965.row_11
#print axioms LeanLab.SteinStein1965.row_13
#print axioms LeanLab.SteinStein1965.row_71
#print axioms LeanLab.SteinStein1965.row_73
#print axioms LeanLab.SteinStein1965.row_79
#print axioms LeanLab.SteinStein1965.row_83
#print axioms LeanLab.SteinStein1965.row_89
#print axioms LeanLab.SteinStein1965.row_97
#print axioms LeanLab.SteinStein1965.tableI_N0_600
#print axioms LeanLab.SteinStein1965.tableI_N0_forced
