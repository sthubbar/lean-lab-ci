/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`F2085.leaf_second_sum_F2085`, ROUTE BURST S98 burst-20261122.

Page 15 after display 52: the prime p of the second sum runs from
z1 = Y^(1/6 + eta/2) up to z0 = Y^(1/4) P^(-2), P = (log X)^B. The range of p is
cut into J dyadic blocks 2^j at most p below 2^(j+1), J at most 3 log X, with
`Eq33RouteD.dyadic_partition`, and the Cauchy inequality over the blocks is
`Eq33RouteD.dyadic_mean_square_le`. Each block is Lemma 3.4 of page 11 with
A + 2 in place of A, the LEAF `leaf_second_sum_block_F2085`, HARD.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_rough_a23_hyp_F2085

namespace LeanLab.KumchevLiu2007.F2085

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/- Numerics for the block leaf. Lemma 3.4 needs 1 at most M at most
x^(1/4) L^(-2B) and 2 at most z at most y x^(-1/2) L^(-2B) with x = Y, y = H.
A nonempty block has M below z0 = Y^(1/4) P^(-2), so the M condition holds.
For z = z1 = Y^(1/6 + eta/2): z1 Y^(1/2) L^(2B) = Y^(2/3 + eta/2) L^(2B), which is
at most Y^(2/3 + eta), hence at most H, once Y^(eta/2) is at least L^(2B), true
for X large since Y = X^(7/12 + eps/2). The integral over Y/4 to Y is two
windows x to 2x with x = Y/4 and x = Y/2. -/
/-- LEAF: P0088 page 11 Lemma 3.4, as applied on page 15 after display 52 to the
second sum of display 52, with x = Y, y = H, (m, k) = (p, m / p),
z = z1 = Y^(1/6 + eta/2), for one dyadic block M at most p below 2M of the primes
from z1 up to z0 = Y^(1/4) P^(-2), in the range of hypothesis A2.3 on page 7.
Lemma 3.4 needs only y at most x, so H at most Y here. The bound is uniform
in M; for M above z0 the block is empty. The hypothesis on
alpha is display 41 with y = H. Class HARD. -/
theorem leaf_second_sum_block_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + η / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + η / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Assembly: the exact statement of `leaf_second_sum_F2085` from the block
leaf, by the dyadic partition and the Cauchy inequality over at most
3 log X blocks, with A + 2 in the block leaf. -/
theorem leaf_second_sum_F2085_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + η / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + η / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B2, hB2, h2⟩ := leaf_second_sum_block_F2085 (A + 2) (by linarith)
  refine ⟨B2, hB2, fun B hB ε hε hε' η hη => ?_⟩
  have hBpos : 0 < B := hB2.trans_le hB
  obtain ⟨C, X0, hC, hX0, k⟩ := h2 B hB ε hε hε' η hη
  refine ⟨9 * C, max X0 3, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hY0 : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hz0X : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ X := by
    have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hBpos.le
    have hw : (Real.log X ^ B) ^ (-2 : ℤ) ≤ 1 := by
      rw [zpow_neg]
      exact inv_le_one_of_one_le₀ (one_le_zpow₀ hP1 (by norm_num))
    have hY4 : windowY X ε ^ (1 / 4 : ℝ) ≤ X := by
      rw [windowY, ← Real.rpow_mul (by linarith)]
      calc
        X ^ ((7 / 12 + ε / 2) * (1 / 4)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
        _ = X := Real.rpow_one X
    have hY4' : 0 ≤ windowY X ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY0.le _
    calc
      _ ≤ windowY X ε ^ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hw hY4'
      _ ≤ X := by linarith
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, X < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log X := by
    refine ⟨⌊Real.logb 2 X⌋₊ + 1, ?_, ?_⟩
    · have h1 : Real.logb 2 X < ((⌊Real.logb 2 X⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
    · push_cast
      have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1.le
      have h1 : (⌊Real.logb 2 X⌋₊ : ℝ) ≤ Real.logb 2 X := Nat.floor_le hlb
      have h2 : Real.logb 2 X ≤ 2 * Real.log X := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      linarith
  have hpart : ∀ m : ℕ,
      (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + η / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
        roughWeight (windowY X ε ^ (1 / 6 + η / 2)) (m / p)) =
      ∑ j ∈ Finset.range J, ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + η / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
          (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j),
        roughWeight (windowY X ε ^ (1 / 6 + η / 2)) (m / p) := by
    intro m
    refine Eq33RouteD.dyadic_partition _ J _ fun p hp => ?_
    obtain ⟨_, hpp, _, hpz, _⟩ := Finset.mem_filter.mp hp
    have hlt : (p : ℝ) < (2 : ℝ) ^ J := by linarith
    exact ⟨hpp.ne_zero, by exact_mod_cast hlt⟩
  simp_rw [hpart]
  refine (Eq33RouteD.dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + η / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
        (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j),
      roughWeight (windowY X ε ^ (1 / 6 + η / 2)) (m / p))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ (C * H ^ 2 / Real.log X ^ (A + 2)) (by linarith)
    (fun j _ => k X H hXa hH ?_ α q a hcop hqP hqQ hclose ((2 : ℝ) ^ j)
      (one_le_pow₀ (by norm_num)))).trans ?_
  · refine hHX.trans ?_
    have hLA1 : 1 ≤ Real.log X ^ A := Real.one_le_rpow hL1 hA.le
    exact div_le_self hY0.le hLA1
  · have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
    have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
      rw [Real.rpow_add hL, Real.rpow_two]
    rw [hpow]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by nlinarith
    have hK : 0 ≤ C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2) :=
      div_nonneg (by positivity) (mul_pos hLA (pow_pos hL 2)).le
    calc
      _ ≤ 9 * Real.log X ^ 2 * (C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_right hJsq hK
      _ = 9 * C * H ^ 2 / Real.log X ^ A := by
        field_simp

/-- The split statement is character for character the parent leaf. -/
example : type_of% @leaf_second_sum_F2085 := leaf_second_sum_F2085_split

end LeanLab.KumchevLiu2007.F2085
