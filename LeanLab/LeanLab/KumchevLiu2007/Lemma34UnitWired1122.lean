/-
S81 burst-20261122. Wiring of P0088 page 11 Lemma 3.4 with M = 1 to the three
cited lemmas of page 10. Prep1122KLLemma34Cases.lemma34_unit_of_cases proves
Lemma 3.4 from three case LEAFs; S39 proved Cases 1 and 2 from Lemmas 3.1 and
3.2 in Prep1122KLLemma31Cases, and S81 proved Case 3 from Lemma 3.2 and a Lemma
3.3 LEAF in Lemma34Case3General1122. Replacing the case sorries in place would be
an import cycle, so this file repeats the dyadic proof with the case proofs.
Kumchev and Liu 2007, P0088, arXiv 0801.0130. AI wrote the Lean code. Binary
Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Lemma34Case3General1122

namespace LeanLab.KumchevLiu2007.Lemma34UnitWired1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
/-- The exact statement of Prep1122KLRoughLemma34.lemma34_unit, P0088 page 11
Lemma 3.4 with M = 1, by the proof of Prep1122KLLemma34Cases.lemma34_unit_of_cases
with its three case leaves replaced by their proofs: Case 1 from Lemma 3.1, Case 2
from Lemma 3.2, Case 3 from Lemma 3.2 and the Lemma 3.3 LEAF. No sorry of its own;
CONDITIONAL ON lemma31, lemma32 and leaf_case3_lemma33_general. -/
theorem lemma34_unit_wired (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        (∫ t in x..2 * x,
          ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
            roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  obtain ⟨B1, hB1, h1⟩ := Prep1122KLLemma31Cases.case_one_of_lemma31 (A + 2) (by linarith)
  obtain ⟨B2, hB2, h2⟩ := Prep1122KLLemma31Cases.case_two_of_lemma32 (A + 2) (by linarith)
  obtain ⟨B3, hB3, h3⟩ := Lemma34Case3General1122.case_three_of_leaves (A + 2) (by linarith)
  refine ⟨max B1 (max B2 B3), lt_max_of_lt_left hB1, fun B hB => ?_⟩
  obtain ⟨C1, x1, hC1, hx1, k1⟩ := h1 B ((le_max_left _ _).trans hB)
  obtain ⟨C2, x2, hC2, hx2, k2⟩ :=
    h2 B (((le_max_left _ _).trans (le_max_right _ _)).trans hB)
  obtain ⟨C3, x3, hC3, hx3, k3⟩ :=
    h3 B (((le_max_right _ _).trans (le_max_right _ _)).trans hB)
  refine ⟨9 * max C1 (max C2 C3), max (max x1 (max x2 x3)) 3,
    by positivity, hx1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro x y hx hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz
  have hxa : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxb : x2 ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx
  have hxc : x3 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  obtain ⟨J, hJ1, hJ2⟩ := dyadic_count hx3
  -- the Moebius expansion and the dyadic cut, inside the integral
  have hrw : (∫ t in x..2 * x,
      ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
          (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
        roughWeight z k * fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in x..2 * x,
      ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
          (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
        (∑ j ∈ Finset.range J, ∑ d ∈ (k.divisors.filter
            (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    refine congrArg (fun s : ℂ => ‖s‖ ^ 2) (Finset.sum_congr rfl fun k hk => ?_)
    obtain ⟨hkr, hkt, _⟩ := Finset.mem_filter.mp hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : (0 : ℝ) < t := lt_of_lt_of_le hx0 ht.1
      norm_num at hkt
      linarith
    rw [moebius_rough z hk0, dyadic_partition _ J _ fun d hd =>
      divisor_lt_pow hx3 hJ1 (Finset.mem_range.mp hkr) hk0 (Finset.mem_filter.mp hd).1]
  rw [hrw]
  have hLA2 : 0 < Real.log x ^ (A + 2) := Real.rpow_pos_of_pos hL _
  have hmax : ∀ c : ℝ, c ≤ max C1 (max C2 C3) →
      c * y ^ 2 / Real.log x ^ (A + 2) ≤ max C1 (max C2 C3) * y ^ 2 / Real.log x ^ (A + 2) :=
    fun c hc => (div_le_div_iff_of_pos_right hLA2).mpr
      (mul_le_mul_of_nonneg_right hc (sq_nonneg y))
  refine (dyadic_mean_square_le ((Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1))) J
    (fun j k => ∑ d ∈ (k.divisors.filter
        (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (fun k : ℕ => (fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    y x (2 * x) (max C1 (max C2 C3) * y ^ 2 / Real.log x ^ (A + 2)) (by linarith)
    (fun j _ => ?_)).trans ?_
  · have hD : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    by_cases c1 : (2 : ℝ) ^ j ≤ Real.log x ^ B
    · exact (k1 x y hxa hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz _ hD c1).trans
        (hmax C1 (le_max_left _ _))
    by_cases c2 : (2 : ℝ) ^ j ≤ y / Real.sqrt x / Real.log x ^ B
    · exact (k2 x y hxb hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz _
        (le_of_lt (not_le.mp c1)) c2).trans
        (hmax C2 ((le_max_left _ _).trans (le_max_right _ _)))
    · exact (k3 x y hxc hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz _
        (le_of_lt (not_le.mp c2))).trans
        (hmax C3 ((le_max_right _ _).trans (le_max_right _ _)))
  · have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL A
    have hpow : Real.log x ^ (A + 2) = Real.log x ^ A * Real.log x ^ 2 := by
      rw [Real.rpow_add hL, Real.rpow_two]
    rw [hpow]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log x ^ 2 := by nlinarith
    have hK : 0 ≤ max C1 (max C2 C3) * y ^ 2 / (Real.log x ^ A * Real.log x ^ 2) :=
      div_nonneg (mul_nonneg (hC1.le.trans (le_max_left _ _)) (sq_nonneg y))
        (mul_pos hLA (pow_pos hL 2)).le
    calc
      _ ≤ 9 * Real.log x ^ 2 *
          (max C1 (max C2 C3) * y ^ 2 / (Real.log x ^ A * Real.log x ^ 2)) :=
        mul_le_mul_of_nonneg_right hJsq hK
      _ = 9 * max C1 (max C2 C3) * y ^ 2 / Real.log x ^ A := by
        field_simp

example : type_of% @Prep1122KLRoughLemma34.lemma34_unit := lemma34_unit_of_cases

/-- PROVED. The wired theorem has the exact type of the S39 assembly. -/
example : type_of% @lemma34_unit_wired =
    type_of% @Prep1122KLLemma34Cases.lemma34_unit_of_cases := rfl

end LeanLab.KumchevLiu2007.Lemma34UnitWired1122

#print axioms LeanLab.KumchevLiu2007.Lemma34UnitWired1122.lemma34_unit_wired
