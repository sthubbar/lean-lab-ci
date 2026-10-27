import LeanLab.Zhao2025.InputEquivalence

/-!
One numerical bound for every case away from the small zero case.
The bound 0.999 is conservative for the existing case constants.
Source: Zhao 2025, Section 4, pages 14 to 16, and the lab layout C refinement.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025 LeanLab.Zhao2025.U6837 LeanLab.Zhao2025.U6900

/-- The square sum in the selected layout. -/
noncomputable def layoutEnergy (k : Fin 11) (n : ℕ) (R T S : ℕ → ℝ) : ℝ :=
  match k.val with
  | 0 | 1 | 2 | 3 => ∑ i ∈ Finset.range (n + 1), S i ^ 2
  | 4 => S 0 ^ 2 + S 1 ^ 2 + ∑ i ∈ Finset.range n, (R i + T i) ^ 2
  | 5 => S 0 ^ 2 + ∑ i ∈ Finset.range n, (R i + T i) ^ 2
  | _ => ∑ i ∈ Finset.range n, (R i + T i) ^ 2

/-- CONDITIONAL ON CaseInputs. The small branch names estimates 4.1, 4.3 and 4.4. -/
theorem non_small_bound (k : Fin 11) (n : ℕ) (l11 : ℝ) (R T S : ℕ → ℝ)
    (h : CaseInputs k n l11 R T S) (hlow : 0.01 ≤ l11) :
    layoutEnergy k n R T S < 0.999 := by
  fin_cases k <;> simp only [CaseInputs] at h <;> simp only [layoutEnergy]
  · obtain ⟨hl, hu, hsmall⟩ := h
    have hs := small_case_square_bound n l11 S hl hu hsmall
    have hcut := small_case_cutoff_spec l11 hl
    have hb := case1_bound l11 (smallCaseCutoff l11) hl hu hcut.2.1 hcut.2.2
    linarith
  · obtain ⟨hl, hl', hS0, h0, hS, hsum⟩ := h
    have := sub001_closes n S l11 hl hS0 h0 hS hsum
    linarith
  · obtain ⟨hl, hl', hS0, h0, hS, hsum⟩ := h
    have := sub010_closes n S l11 hl hS0 h0 hS hsum
    linarith
  · obtain ⟨hl, hl', hS0, h0, hS, hsum⟩ := h
    have := sub030_closes n S l11 hl hS0 h0 hS hsum
    linarith
  · obtain ⟨hl, hl', hS0, hS0', hS1, hS1', hR, hT, hsR, hsT⟩ := h
    have := sub040_i02_closes n R T (S 0) (S 1) ⟨hS0, hS0'⟩ ⟨hS1, hS1'⟩ hR hT hsR hsT
    linarith
  · obtain ⟨hl, hl', hS0, hS0', hR, hT, hsR, hsT⟩ := h
    have := sub040_i01_closes n R T (S 0) ⟨hS0, hS0'⟩ hR hT hsR hsT
    linarith
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    exact closes_below n R T 0.29940 0.23508 0.14790 0.57982 7.6236 0.10023 0.09272 0.09272 0.999 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    exact closes_below n R T 0.29306 0.25205 0.19150 0.59615 7.5381 0.09797 0.09241 0.09230 0.999 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    exact closes_below n R T 0.29738 0.27836 0.24889 0.66426 7.4466 0.09572 0.09321 0.09063 0.999 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])
  · obtain ⟨hl, hl', hR0, hT0, hsR, hsT, hcfg⟩ := h
    exact closes_below n R T 0.28824 0.27380 0.25104 0.64932 7.3632 0.09359 0.09166 0.08900 0.999 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])
  · obtain ⟨hl, hR0, hT0, hsR, hsT, hcfg⟩ := h
    exact closes_below n R T 0.28735 0.28342 0.27703 0.67914 7.2739 0.09121 0.09112 0.08733 0.999 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])

#print axioms non_small_bound

end LeanLab.Zhao2025.Task56
