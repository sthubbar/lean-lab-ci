/-
BURST 2026-11-22, session S111, step case3-lemma33-wire.
P0088, Kumchev and Liu 2007, page 10 Lemma 3.3, as it is used on page 12 in Case 3 of
the proof of Lemma 3.4, D at least y x^(-1/2) L^(-B).

Finding of this step: none of the Case 3 LEAFs
`Case3Core1122.leaf_case3_lemma33_removal`,
`Lemma34Case3General1122.leaf_case3_lemma33_general` and
`Eq33RouteD.leaf_case3_lemma33_reduction` follows from
`Lemma33Perron1122.Lemma33Statement` alone. Each of them bounds a mean square over t
by a mean square with coefficients fixed before the t integral, while
`Lemma33Statement` gives coefficients a', b' chosen after F, and in Case 3 the function
F depends on t through the window t < n^2 ≤ t + y. Kumchev 2006 Lemma 2.7 is proved by
the truncated Perron formula, whose twists m^(-i tau), k^(i tau) do not depend on F, so
the proof gives the uniform form below; the printed statement does not record that.

* `lemma33_mean_square`, LEAF HARD: Lemma 3.3 uniformly over a finite weighted family
  F_i, one pair a', b' for the whole family, in mean square.
* `lemma33_of_mean_square`, PROVED reduction: the uniform form implies
  `Lemma33Statement`, the one point family, so the new LEAF is no weaker than the
  printed lemma.
* `lemma33_from_mean_square`: `Lemma33Statement` CONDITIONAL ON the new LEAF.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Lemma33Perron1122

namespace LeanLab.KumchevLiu2007.Lemma33MeanSquare1123

open Finset LeanLab.KumchevLiu2007.Lemma33Perron1122

/-- LEAF: P0088 page 10 Lemma 3.3, the m < k case, in the uniform mean square form that
page 12 Case 3 of Lemma 3.4 uses, coefficients chosen before the t integral. For a
finite family F_i, i in s, with weights w_i ≥ 0 and ‖F_i‖ ≤ X, one pair a', b' with
‖a'‖ ≤ ‖a‖, ‖b'‖ ≤ ‖b‖ serves every i:
sum_i w_i ‖B_i‖^2 ≤ (C L)^2 sum_i w_i ‖B'_i‖^2 + (sum_i w_i) (X M K)^(-2),
L = log (2 M K X). Class HARD. The cited route is the proof of Kumchev 2006 Lemma 2.7:
the truncated Perron formula for the indicator of k / (m + 1/2) > 1 with T a power of
M K X, Cauchy Schwarz against the kernel, whose total mass is O(L), then the choice of
the twist tau that maximises the weighted sum; a'_m = a_m m^(-i tau) / 2 and
b'_k = b_k k^(i tau) up to the kernel normalisation. -/
theorem lemma33_mean_square : ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ) (M K : ℕ) (a b : ℕ → ℂ)
    (s : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℕ → ℂ),
    0 < X → (∀ i n, ‖F i n‖ ≤ X) → 2 ≤ M → 2 ≤ K →
    (∀ m, ‖a m‖ ≤ 1) → (∀ k, ‖b k‖ ≤ 1) → (∀ i, 0 ≤ w i) →
    ∃ a' b' : ℕ → ℂ, (∀ m, ‖a' m‖ ≤ ‖a m‖) ∧ (∀ k, ‖b' k‖ ≤ ‖b k‖) ∧
      ∑ i ∈ s, w i * ‖bilinB a b (F i) M K‖ ^ 2 ≤
        (C * Real.log (2 * M * K * X)) ^ 2 * ∑ i ∈ s, w i * ‖bilinFull a' b' (F i) M K‖ ^ 2 +
          (∑ i ∈ s, w i) * ((X * M * K)⁻¹) ^ 2 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro X M K a b s w F hX hF hM hK ha hb hw
  by_cases hsmall : (M : ℝ) * K * X ≤ 1
  · refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩
    · intro m
      simp
    · intro k
      simp
    · have hB : ∀ i ∈ s, ‖bilinB a b (F i) M K‖ ≤ (M : ℝ) * K * X := by
        intro i hi
        exact norm_bilinB_le a b (F i) M K X (fun n => hF i n) ha hb
      have hMK : 1 ≤ (M : ℝ) * K := by
        have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
        have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
        nlinarith
      have he : 1 ≤ (X * M * K)⁻¹ := by
        rw [le_inv_comm₀ zero_lt_one (by positivity)]
        nlinarith
      have hsq : ∀ i ∈ s,
          ‖bilinB a b (F i) M K‖ ^ 2 ≤ ((X * M * K)⁻¹) ^ 2 := by
        intro i hi
        have hnonneg : 0 ≤ ‖bilinB a b (F i) M K‖ := norm_nonneg _
        have hbound := hB i hi
        nlinarith [sq_nonneg (‖bilinB a b (F i) M K‖ - (X * M * K)⁻¹)]
      calc
        (∑ i ∈ s, w i * ‖bilinB a b (F i) M K‖ ^ 2) ≤
            ∑ i ∈ s, w i * ((X * M * K)⁻¹) ^ 2 :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hsq i hi) (hw i))
        _ = (∑ i ∈ s, w i) * ((X * M * K)⁻¹) ^ 2 :=
          (Finset.sum_mul s w (((X * M * K)⁻¹) ^ 2)).symm
        _ ≤ (1 * Real.log (2 * M * K * X)) ^ 2 *
              ∑ i ∈ s, w i * ‖bilinFull (fun _ => 0) (fun _ => 0) (F i) M K‖ ^ 2 +
            (∑ i ∈ s, w i) * ((X * M * K)⁻¹) ^ 2 := by
          have hzero : (∑ i ∈ s,
              w i * ‖bilinFull (fun _ => 0) (fun _ => 0) (F i) M K‖ ^ 2) = 0 := by
            simp [bilinFull]
          rw [hzero]
          ring_nf
          linarith
  · sorry

/-- PROVED reduction: the uniform mean square form of Lemma 3.3 implies P0088 page 10
Lemma 3.3 as printed, `Lemma33Statement`, by the one point family s = {0}, w = 1,
F_0 = F, and the square root of x^2 ≤ y^2 + e^2 ≤ (y + e)^2. The range M K X ≤ 1 is
`concl_of_MKX_le_one`. -/
theorem lemma33_of_mean_square
    (hMS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ) (M K : ℕ) (a b : ℕ → ℂ)
      (s : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℕ → ℂ),
      0 < X → (∀ i n, ‖F i n‖ ≤ X) → 2 ≤ M → 2 ≤ K →
      (∀ m, ‖a m‖ ≤ 1) → (∀ k, ‖b k‖ ≤ 1) → (∀ i, 0 ≤ w i) →
      ∃ a' b' : ℕ → ℂ, (∀ m, ‖a' m‖ ≤ ‖a m‖) ∧ (∀ k, ‖b' k‖ ≤ ‖b k‖) ∧
        ∑ i ∈ s, w i * ‖bilinB a b (F i) M K‖ ^ 2 ≤
          (C * Real.log (2 * M * K * X)) ^ 2 *
            ∑ i ∈ s, w i * ‖bilinFull a' b' (F i) M K‖ ^ 2 +
            (∑ i ∈ s, w i) * ((X * M * K)⁻¹) ^ 2) :
    Lemma33Statement := by
  obtain ⟨C, hC0, hC⟩ := hMS
  refine ⟨C, fun X F M K a b hX hF hM hK ha hb => ?_⟩
  by_cases hs : (M : ℝ) * K * X ≤ 1
  · exact concl_of_MKX_le_one C X F M K a b hX (by omega) (by omega) hF ha hb hs
  push_neg at hs
  obtain ⟨a', b', ha', hb', hbd⟩ :=
    hC X M K a b {0} (fun _ => 1) (fun _ => F) hX (fun _ n => hF n) hM hK ha hb
      (fun _ => zero_le_one)
  refine ⟨a', b', ha', hb', ?_⟩
  simp only [Finset.sum_singleton, one_mul] at hbd
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hL : 0 ≤ Real.log (2 * M * K * X) := Real.log_nonneg (by nlinarith)
  have hCL : 0 ≤ C * Real.log (2 * M * K * X) := mul_nonneg hC0 hL
  have he : 0 ≤ (X * M * K)⁻¹ := by positivity
  set x := ‖bilinB a b F M K‖
  set y := C * Real.log (2 * M * K * X) * ‖bilinFull a' b' F M K‖
  set e := (X * M * K)⁻¹
  have hy : 0 ≤ y := mul_nonneg hCL (norm_nonneg _)
  have hx : 0 ≤ x := norm_nonneg _
  have h2 : x ^ 2 ≤ (y + e) ^ 2 := by
    have : x ^ 2 ≤ y ^ 2 + e ^ 2 := by
      have := hbd
      simp only [y, mul_pow] at this ⊢
      linarith
    nlinarith
  exact (pow_le_pow_iff_left₀ hx (add_nonneg hy he) two_ne_zero).mp h2

/-- P0088 page 10 Lemma 3.3 as printed. CONDITIONAL ON the LEAF `lemma33_mean_square`. -/
theorem lemma33_from_mean_square : Lemma33Statement :=
  lemma33_of_mean_square lemma33_mean_square

end LeanLab.KumchevLiu2007.Lemma33MeanSquare1123
