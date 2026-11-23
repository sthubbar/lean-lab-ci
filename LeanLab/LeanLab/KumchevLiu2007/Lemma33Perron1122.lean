/-
P0088, Kumchev and Liu 2007, page 10, Lemma 3.3, the m < k case.
The paper omits the proof and cites Kumchev 2006 Lemma 2.7, a standard application of the
truncated Perron formula. This is a standard lemma, not a new result.

This file states the lemma faithfully as `Lemma33Statement` and
proves it from one LEAF, the overlapping range M < K < 2M, by PROVED reductions: the two degenerate ranges of M against K, the trivial
bound for B, and the case where B is already below the error term.

AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.KumchevLiu2007.Lemma33Perron1122

open Finset

/-- The bilinear form B(M, K) of Lemma 3.3: m ∼ M, k ∼ K, m < k. -/
noncomputable def bilinB (a b F : ℕ → ℂ) (M K : ℕ) : ℂ :=
  ∑ m ∈ Ico M (2 * M), ∑ k ∈ (Ico K (2 * K)).filter (fun k => m < k), a m * b k * F (m * k)

/-- The unrestricted bilinear form over m ∼ M, k ∼ K. -/
noncomputable def bilinFull (a b F : ℕ → ℂ) (M K : ℕ) : ℂ :=
  ∑ m ∈ Ico M (2 * M), ∑ k ∈ Ico K (2 * K), a m * b k * F (m * k)

/-- The conclusion of Lemma 3.3 for one choice of data and one constant C. -/
def Lemma33Concl (C X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ) : Prop :=
  ∃ a' b' : ℕ → ℂ, (∀ m, ‖a' m‖ ≤ ‖a m‖) ∧ (∀ k, ‖b' k‖ ≤ ‖b k‖) ∧
    ‖bilinB a b F M K‖ ≤
      C * Real.log (2 * M * K * X) * ‖bilinFull a' b' F M K‖ + (X * M * K)⁻¹

/-- P0088 page 10 Lemma 3.3 as printed, the m < k case, with the absolute implied
constant C quantified first. -/
def Lemma33Statement : Prop :=
  ∃ C : ℝ, ∀ (X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ),
    0 < X → (∀ n, ‖F n‖ ≤ X) → 2 ≤ M → 2 ≤ K →
    (∀ m, ‖a m‖ ≤ 1) → (∀ k, ‖b k‖ ≤ 1) → Lemma33Concl C X F M K a b

/-- If every k ∼ K is at most every m ∼ M, the form B is empty. -/
theorem bilinB_eq_zero_of_le (a b F : ℕ → ℂ) (M K : ℕ) (h : 2 * K ≤ M + 1) :
    bilinB a b F M K = 0 := by
  unfold bilinB
  refine Finset.sum_eq_zero (fun m hm => ?_)
  rw [Finset.mem_Ico] at hm
  refine Finset.sum_eq_zero (fun k hk => ?_)
  rw [Finset.mem_filter, Finset.mem_Ico] at hk
  omega

/-- If 2M ≤ K, the condition m < k is automatic and B is the full form. -/
theorem bilinB_eq_full_of_le (a b F : ℕ → ℂ) (M K : ℕ) (h : 2 * M ≤ K) :
    bilinB a b F M K = bilinFull a b F M K := by
  unfold bilinB bilinFull
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_Ico] at hm
  rw [Finset.filter_true_of_mem]
  intro k hk
  rw [Finset.mem_Ico] at hk
  omega

/-- Trivial bound: ‖B‖ ≤ M K X. -/
theorem norm_bilinB_le (a b F : ℕ → ℂ) (M K : ℕ) (X : ℝ)
    (hF : ∀ n, ‖F n‖ ≤ X) (ha : ∀ m, ‖a m‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1) :
    ‖bilinB a b F M K‖ ≤ (M : ℝ) * K * X := by
  have hX : 0 ≤ X := le_trans (norm_nonneg _) (hF 0)
  have hterm : ∀ m k, ‖a m * b k * F (m * k)‖ ≤ X := by
    intro m k
    rw [norm_mul, norm_mul]
    have h1 := ha m; have h2 := hb k; have h3 := hF (m * k)
    have := mul_le_mul (mul_le_one₀ h1 (norm_nonneg _) h2) h3 (norm_nonneg _) zero_le_one
    simpa using this
  unfold bilinB
  calc ‖∑ m ∈ Ico M (2 * M), ∑ k ∈ (Ico K (2 * K)).filter (fun k => m < k),
          a m * b k * F (m * k)‖
      ≤ ∑ m ∈ Ico M (2 * M), ‖∑ k ∈ (Ico K (2 * K)).filter (fun k => m < k),
          a m * b k * F (m * k)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ico M (2 * M), (K : ℝ) * X := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        calc _ ≤ ∑ k ∈ (Ico K (2 * K)).filter (fun k => m < k), ‖a m * b k * F (m * k)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ k ∈ (Ico K (2 * K)).filter (fun k => m < k), X :=
              Finset.sum_le_sum (fun k _ => hterm m k)
          _ = (((Ico K (2 * K)).filter (fun k => m < k)).card : ℝ) * X := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (K : ℝ) * X := by
              apply mul_le_mul_of_nonneg_right _ hX
              have h1 := Finset.card_filter_le (Ico K (2 * K)) (fun k => m < k)
              rw [Nat.card_Ico] at h1
              exact_mod_cast (show _ ≤ K by omega)
    _ = (M : ℝ) * K * X := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
        have : 2 * M - M = M := by omega
        rw [this]; ring

/-- If B is already below the error term, the conclusion holds with a' = b' = 0,
for every C. -/
theorem concl_of_small (C X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ)
    (h : ‖bilinB a b F M K‖ ≤ (X * M * K)⁻¹) : Lemma33Concl C X F M K a b := by
  refine ⟨fun _ => 0, fun _ => 0, fun m => by simp, fun k => by simp, ?_⟩
  simpa [bilinFull] using h

/-- If M K X ≤ 1, the conclusion holds trivially. -/
theorem concl_of_MKX_le_one (C X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ)
    (hX : 0 < X) (hM : 1 ≤ M) (hK : 1 ≤ K)
    (hF : ∀ n, ‖F n‖ ≤ X) (ha : ∀ m, ‖a m‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1)
    (hs : (M : ℝ) * K * X ≤ 1) : Lemma33Concl C X F M K a b := by
  apply concl_of_small
  have hB := norm_bilinB_le a b F M K X hF ha hb
  have hpos : 0 < X * M * K := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    positivity
  have h1 : (1 : ℝ) ≤ (X * M * K)⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hpos]; simpa [inv_one, mul_comm, mul_left_comm, mul_assoc] using hs
  linarith

/-- The range 2K ≤ M + 1: B = 0. -/
theorem concl_of_disjoint (C X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ)
    (hX : 0 < X) (h : 2 * K ≤ M + 1) : Lemma33Concl C X F M K a b := by
  apply concl_of_small
  rw [bilinB_eq_zero_of_le a b F M K h, norm_zero]
  positivity

/-- The range 2M ≤ K: take a' = a, b' = b, once C L ≥ 1. -/
theorem concl_of_separated (C X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ)
    (hX : 0 < X) (h : 2 * M ≤ K) (hCL : 1 ≤ C * Real.log (2 * M * K * X)) :
    Lemma33Concl C X F M K a b := by
  refine ⟨a, b, fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  rw [bilinB_eq_full_of_le a b F M K h]
  have h0 : 0 ≤ (X * M * K)⁻¹ := by positivity
  nlinarith [norm_nonneg (bilinFull a b F M K)]

/-- LEAF: P0088 page 10 Lemma 3.3, the overlapping range M < K < 2M with M K X > 1, the only
range not settled above. Class HARD. The constant may be taken at least 2 without loss, since
the conclusion is monotone in C once M K X > 1. The cited route is the truncated Perron
formula, as in Kumchev 2006 Lemma 2.7: write the indicator of m < k as a Perron integral in
y = k / (m + 1/2), separate the variables, bound the t integral by its largest inner bilinear
form times a logarithm, and absorb the truncation error into (X M K)⁻¹. -/
theorem lemma33_overlap : ∃ C : ℝ, 2 ≤ C ∧ ∀ (X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ),
    0 < X → (∀ n, ‖F n‖ ≤ X) → 2 ≤ M → 2 ≤ K →
    (∀ m, ‖a m‖ ≤ 1) → (∀ k, ‖b k‖ ≤ 1) →
    1 < (M : ℝ) * K * X → M + 1 < 2 * K → K < 2 * M → Lemma33Concl C X F M K a b := by
  sorry

/-- Reduction: P0088 page 10 Lemma 3.3 as printed follows from the overlapping range. PROVED. -/
theorem lemma33_of_overlap
    (hO : ∃ C : ℝ, 2 ≤ C ∧ ∀ (X : ℝ) (F : ℕ → ℂ) (M K : ℕ) (a b : ℕ → ℂ),
      0 < X → (∀ n, ‖F n‖ ≤ X) → 2 ≤ M → 2 ≤ K →
      (∀ m, ‖a m‖ ≤ 1) → (∀ k, ‖b k‖ ≤ 1) →
      1 < (M : ℝ) * K * X → M + 1 < 2 * K → K < 2 * M → Lemma33Concl C X F M K a b) :
    Lemma33Statement := by
  obtain ⟨C, hC2, hC⟩ := hO
  refine ⟨C, fun X F M K a b hX hF hM hK ha hb => ?_⟩
  by_cases hs : (M : ℝ) * K * X ≤ 1
  · exact concl_of_MKX_le_one C X F M K a b hX (by omega) (by omega) hF ha hb hs
  push_neg at hs
  by_cases h1 : 2 * K ≤ M + 1
  · exact concl_of_disjoint C X F M K a b hX h1
  by_cases h2 : 2 * M ≤ K
  · apply concl_of_separated C X F M K a b hX h2
    have hL : Real.log 2 ≤ Real.log (2 * M * K * X) := by
      apply Real.log_le_log (by norm_num)
      nlinarith
    have hl2 := Real.log_two_gt_d9
    nlinarith
  · exact hC X F M K a b hX hF hM hK ha hb hs (by omega) (by omega)

/-- P0088 page 10 Lemma 3.3 as printed, the m < k case. CONDITIONAL ON the LEAF
`lemma33_overlap`. -/
theorem lemma33 : Lemma33Statement := lemma33_of_overlap lemma33_overlap

/-- The form of the variant in Lemma 3.3: m ∼ M, k ∼ K, U ≤ m k < U'. -/
noncomputable def bilinBU (a b F : ℕ → ℂ) (M K U U' : ℕ) : ℂ :=
  ∑ m ∈ Ico M (2 * M), ∑ k ∈ (Ico K (2 * K)).filter (fun k => U ≤ m * k ∧ m * k < U'),
    a m * b k * F (m * k)

/-- The variant of P0088 page 10 Lemma 3.3 with U ≤ m k < U' in place of m < k, stated only;
not proved here. -/
def Lemma33UStatement : Prop :=
  ∃ C : ℝ, ∀ (X : ℝ) (F : ℕ → ℂ) (M K U U' : ℕ) (a b : ℕ → ℂ),
    0 < X → (∀ n, ‖F n‖ ≤ X) → 2 ≤ M → 2 ≤ K →
    (∀ m, ‖a m‖ ≤ 1) → (∀ k, ‖b k‖ ≤ 1) →
    ∃ a' b' : ℕ → ℂ, (∀ m, ‖a' m‖ ≤ ‖a m‖) ∧ (∀ k, ‖b' k‖ ≤ ‖b k‖) ∧
      ‖bilinBU a b F M K U U'‖ ≤
        C * Real.log (2 * M * K * X) * ‖bilinFull a' b' F M K‖ + (X * M * K)⁻¹

/-- In the variant, if U ≤ M K and 4 M K ≤ U', the condition is automatic. PROVED. -/
theorem bilinBU_eq_full_of (a b F : ℕ → ℂ) (M K U U' : ℕ) (hU : U ≤ M * K)
    (hU' : 4 * (M * K) ≤ U') : bilinBU a b F M K U U' = bilinFull a b F M K := by
  unfold bilinBU bilinFull
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_Ico] at hm
  rw [Finset.filter_true_of_mem]
  intro k hk
  rw [Finset.mem_Ico] at hk
  constructor
  · exact le_trans hU (Nat.mul_le_mul hm.1 hk.1)
  · calc m * k < (2 * M) * (2 * K) := Nat.mul_lt_mul'' hm.2 hk.2
      _ = 4 * (M * K) := by ring
      _ ≤ U' := hU'

/-- In the variant, if U' ≤ M K, the form is empty. PROVED. -/
theorem bilinBU_eq_zero_of (a b F : ℕ → ℂ) (M K U U' : ℕ) (hU' : U' ≤ M * K) :
    bilinBU a b F M K U U' = 0 := by
  unfold bilinBU
  refine Finset.sum_eq_zero (fun m hm => ?_)
  rw [Finset.mem_Ico] at hm
  refine Finset.sum_eq_zero (fun k hk => ?_)
  rw [Finset.mem_filter, Finset.mem_Ico] at hk
  have := Nat.mul_le_mul hm.1 hk.1.1
  omega

/-- Perron gap, the first step of the cited proof, PROVED: for k ∼ below 2K, y = k/(m + 1/2) stays 1/(4K) away from 1 in log scale. -/
theorem log_gap (m k K : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * K) :
    1 / (4 * (K : ℝ)) ≤ |Real.log ((k : ℝ) / (m + 1 / 2))| := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (2 * (k : ℝ) + 1) ≤ 4 * K := by
    have : k + 1 ≤ 2 * K := hk2
    have : ((k : ℝ) + 1) ≤ 2 * K := by exact_mod_cast this
    linarith
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hK0 : (0 : ℝ) < 4 * K := by linarith
  rcases lt_or_ge m k with h | h
  · -- y > 1
    have hmk : (m : ℝ) + 1 ≤ k := by exact_mod_cast h
    have hy : 0 < (k : ℝ) / (m + 1 / 2) := by positivity
    have hl := Real.one_sub_inv_le_log_of_pos hy
    rw [inv_div] at hl
    have h1 : 1 / (4 * (K : ℝ)) ≤ 1 - ((m : ℝ) + 1 / 2) / k := by
      rw [div_le_iff₀ hK0]
      rw [show (1 - ((m : ℝ) + 1 / 2) / k) * (4 * K) = (k - (m + 1/2)) / k * (4 * K) by
        field_simp]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    have : 0 ≤ Real.log ((k : ℝ) / (m + 1 / 2)) := by linarith [div_pos (by norm_num : (0:ℝ) < 1) hK0]
    rw [abs_of_nonneg this]; linarith
  · have hmk : (k : ℝ) ≤ m := by exact_mod_cast h
    have hy : 0 < (k : ℝ) / (m + 1 / 2) := by positivity
    have hle : Real.log ((k : ℝ) / (m + 1 / 2)) ≤ Real.log ((k : ℝ) / (k + 1 / 2)) := by
      apply Real.log_le_log hy
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hl := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) / (k + 1 / 2) by positivity)
    have h2 : (k : ℝ) / (k + 1 / 2) - 1 = -(1 / (2 * k + 1)) := by
      field_simp; ring
    have h3 : 1 / (4 * (K : ℝ)) ≤ 1 / (2 * k + 1) :=
      one_div_le_one_div_of_le (by positivity) hK
    have hneg : Real.log ((k : ℝ) / (m + 1 / 2)) ≤ 0 := by
      linarith [show (0:ℝ) < 1 / (2 * k + 1) by positivity]
    rw [abs_of_nonpos hneg]; linarith

end LeanLab.KumchevLiu2007.Lemma33Perron1122

#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.bilinB_eq_zero_of_le
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.bilinB_eq_full_of_le
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.norm_bilinB_le
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.concl_of_small
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.concl_of_MKX_le_one
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.concl_of_disjoint
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.concl_of_separated
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.lemma33_of_overlap
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.lemma33
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.bilinBU_eq_full_of
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.bilinBU_eq_zero_of
#print axioms LeanLab.KumchevLiu2007.Lemma33Perron1122.log_gap
