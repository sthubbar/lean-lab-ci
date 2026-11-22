/-
PREP 2026-11-21, KL-cited-p2 deepening pass. Cuts the two open leaves of
Prep1121KLRoughBulk.lean, first_sum_block and second_sum_block, into smaller
pieces. Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 15 after display 52
and Lemma 3.4 of page 11.

* first_sum_block. Cut at the sieve cutoff z = 2. For z at most 2 the rough
  weight is identically one, PROVED here, so the leaf is the unweighted mean
  square of the short quadratic Weyl sum, the case z = 2 of Lemma 3.4. For z
  above 2 the leaf is the genuinely rough case of Lemma 3.4.
* second_sum_block. Cut into one dyadic block M at most p below 2M of the
  primes p, the form Lemma 3.4 is applied in. The dyadic reduction, at most
  3 log X blocks with A + 2 in place of A, is PROVED here; it is the proof of
  Eq33RouteD.lemma34_second_sum carried over to the block range, where the
  only change is that eps at most 7/18 now comes from the hypothesis.

Each final result admits no step of its own and proves the exact statement of
the parent leaf. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLRoughBulk
import LeanLab.KumchevLiu2007.SmallCutoff674

namespace LeanLab.KumchevLiu2007.Prep1121DKLRoughCut

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. P0088 page 4 display 10: for a cutoff z at most 2 every prime factor
reaches z, so the rough weight is one. -/
theorem roughWeight_eq_one_of_le_two {z : ℝ} (hz : z ≤ 2) (m : ℕ) :
    roughWeight z m = 1 := by
  have h : ∀ p : ℕ, p.Prime → p ∣ m → z ≤ (p : ℝ) := fun p hp _ =>
    hz.trans (by exact_mod_cast hp.two_le)
  unfold roughWeight
  split_ifs
  · rfl

/-- LEAF: P0088 page 11 Lemma 3.4 with z = 2, applied on page 15 to the first sum
of display 52 when the cutoff is at most 2: the unweighted short quadratic Weyl
sum, x = Y, y = H, alpha satisfying display 41 with y = H, in the block range. -/
theorem first_small_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  refine ⟨A + 2, by linarith, ?_⟩
  intro B hB ε hε hε'
  obtain ⟨T1, ht1⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + 4 * B) (by norm_num : (0 : ℝ) < 7 / 72)).bound
      (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T2, ht2⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 7 / 24)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨64, max 3 (max T1 T2), by norm_num, by linarith [le_max_left (3 : ℝ) (max T1 T2)], ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact Real.exp_one_lt_three.le.trans hX3
  have hL : 0 < Real.log X := by linarith
  have hT : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL _
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  have hB0 : 0 ≤ B := by linarith
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB0
  have hT1 : 1 ≤ Real.log X ^ A := Real.one_le_rpow hL1 hA.le
  have hY : 1 ≤ windowY X ε := Real.one_le_rpow hX1 (by linarith : 0 ≤ 7 / 12 + ε / 2)
  have hR : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4) := by
    rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hR0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr (by linarith)
  have hAbs1 : Real.log X ^ A * (Real.log X ^ B) ^ 4 ≤ X ^ (7 / 72 : ℝ) := by
    have h := ht1 X (((le_max_left _ _).trans (le_max_right _ _)).trans hX)
    have heq : Real.log X ^ A * (Real.log X ^ B) ^ 4 = Real.log X ^ (A + 4 * B) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
      congr 1
      ring
    rw [heq]
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (A + 4 * B)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 72 : ℝ)), one_mul] using h
  have hAbs2 : Real.log X ^ (A + 1) ≤ X ^ (7 / 24 : ℝ) := by
    have h := ht2 X (((le_max_right _ _).trans (le_max_right _ _)).trans hX)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (A + 1)),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 24 : ℝ)), one_mul] using h
  have hP4 : 0 < (Real.log X ^ B) ^ 4 := by positivity
  have hlow' : X ^ (7 / 18 + ε) / (Real.log X ^ B) ^ 4 ≤ H := by
    simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using hlow
  have hRT : Real.sqrt (windowY X ε) * Real.log X ^ A ≤ H := by
    refine le_trans ((le_div_iff₀ hP4).mpr ?_) hlow'
    calc
      _ = Real.sqrt (windowY X ε) * (Real.log X ^ A * (Real.log X ^ B) ^ 4) := by ring
      _ ≤ Real.sqrt (windowY X ε) * X ^ (7 / 72 : ℝ) :=
        mul_le_mul_of_nonneg_left hAbs1 hR0.le
      _ = X ^ (7 / 24 + ε / 4 + 7 / 72) := by rw [hR, ← Real.rpow_add hX0]
      _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hroot : Real.sqrt (windowY X ε) ≤ H :=
    (le_mul_of_one_le_right hR0.le hT1).trans hRT
  have hH0 : 0 ≤ H := hR0.le.trans hroot
  have hHpos : 0 < H := hR0.trans_le hroot
  have hqpos : (0 : ℝ) < q := hP.trans hqP
  have hqn : 1 ≤ q := by exact_mod_cast (show 0 < q by exact_mod_cast hqpos)
  have hHX : H ≤ X := by
    have hP4one : 1 ≤ (Real.log X ^ B) ^ 4 := one_le_pow₀ hP1
    have hhigh' : H ≤ windowY X ε / (Real.log X ^ B) ^ 4 := by
      simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using hhigh
    refine hhigh'.trans ((div_le_self (by linarith : 0 ≤ windowY X ε) hP4one).trans ?_)
    simpa only [windowY, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : 7 / 12 + ε / 2 ≤ (1 : ℝ))
  have hqX : (q : ℝ) ≤ X := hqQ.trans ((div_le_self hH0 hP1).trans hHX)
  have hlogq : Real.log (q : ℝ) ≤ Real.log X := Real.log_le_log hqpos hqX
  have hJ : 1 + Real.log (q : ℝ) ≤ 2 * Real.log X := by linarith
  have hTq : Real.log X ^ A ≤ (q : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : A ≤ B)).trans hqP.le
  have hTL : Real.log X ^ A * Real.log X ≤ Real.log X ^ B := by
    calc
      Real.log X ^ A * Real.log X = Real.log X ^ (A + 1) := by
        rw [Real.rpow_add hL, Real.rpow_one]
      _ ≤ Real.log X ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hJR : (1 + Real.log (q : ℝ)) * Real.log X ^ A ≤ 2 * Real.sqrt (windowY X ε) := by
    calc
      _ ≤ (2 * Real.log X) * Real.log X ^ A := mul_le_mul_of_nonneg_right hJ hT.le
      _ = 2 * Real.log X ^ (A + 1) := by rw [Real.rpow_add hL, Real.rpow_one]; ring
      _ ≤ 2 * X ^ (7 / 24 : ℝ) := by gcongr
      _ ≤ 2 * Real.sqrt (windowY X ε) := by
        rw [hR]
        gcongr
        linarith
  have hqPJ : (q : ℝ) * Real.log X ^ B ≤ H := (le_div_iff₀ hP).mp hqQ
  have hqJ : (q : ℝ) * (1 + Real.log (q : ℝ)) * Real.log X ^ A ≤ 2 * H := by
    calc
      _ ≤ (q : ℝ) * (2 * Real.log X) * Real.log X ^ A := by gcongr
      _ = 2 * (q : ℝ) * (Real.log X ^ A * Real.log X) := by ring
      _ ≤ 2 * (q : ℝ) * Real.log X ^ B := by gcongr
      _ ≤ 2 * H := by nlinarith
  have happ : |α - (v : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 :=
    (Eq33RouteD.display41_of_minor (by omega : 0 < q) hqQ hclose).le
  exact (Task674.unweighted_square_energy_bound (windowY X ε) H α (windowY X ε / 4)
    (windowY X ε) hY hroot (by positivity) (by linarith) le_rfl
    hqn hcop happ).trans (Task674.quadratic_budget_le H (Real.sqrt (windowY X ε)) q
      (1 + Real.log q) (Real.log X ^ A) hH0 hR0 hT hRT hTq hJR hqJ)


/-- LEAF: P0088 page 11 Lemma 3.4, applied on page 15 to the first sum of display
52 with a cutoff z above 2 and at most z1 = Y^(1/6 + eps/2), the genuinely rough
case, x = Y, y = H, in the block range. -/
theorem first_rough_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- The exact statement of Prep1121KLRough.first_sum_block, from first_small_block,
first_rough_block and roughWeight_eq_one_of_le_two. No sorry of its own. -/
theorem first_sum_block_of_pieces (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := first_small_block A hA
  obtain ⟨B2, hB2, h2⟩ := first_rough_block A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨max C1 C2, max X1 X2, lt_max_of_lt_left hC1, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := by positivity
  have r1 : C1 * H ^ 2 / Real.log X ^ A ≤ max C1 C2 * H ^ 2 / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  have r2 : C2 * H ^ 2 / Real.log X ^ A ≤ max C1 C2 * H ^ 2 / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hq
  by_cases hz2 : z ≤ 2
  · simp only [roughWeight_eq_one_of_le_two hz2, one_mul]
    exact (k1 X H hXa hlo hhi α q a hcop hqP hqQ hclose).trans r1
  · exact (k2 X H hXb hlo hhi α q a hcop hqP hqQ hclose z (lt_of_not_ge hz2) hz).trans r2

example : type_of% @Prep1121KLRough.first_sum_block := first_sum_block_of_pieces

/-- LEAF: P0088 page 11 Lemma 3.4, applied on page 15 to the second sum of display
52 for one dyadic block M at most p below 2M, with (m, k) = (p, m/p), z = z1,
primes p from z1 to below z0 = Y^(1/4) P^(-2), in the block range. The same as
Eq33RouteD.lemma34_second_sum_dyadic with the block range of H. -/
theorem second_dyadic_block (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- The exact statement of Prep1121KLRough.second_sum_block, from second_dyadic_block
by the dyadic reduction of Eq33RouteD.lemma34_second_sum. No sorry of its own. -/
theorem second_sum_block_of_dyadic (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B2, hB2, h2⟩ := second_dyadic_block (A + 2) (by linarith)
  refine ⟨B2, hB2, fun B hB ε hε hε' => ?_⟩
  have hBpos : 0 < B := hB2.trans_le hB
  obtain ⟨C, X0, hC, hX0, k⟩ := h2 B hB ε hε hε'
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
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
        roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) =
      ∑ j ∈ Finset.range J, ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
          (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j),
        roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p) := by
    intro m
    refine dyadic_partition _ J _ fun p hp => ?_
    obtain ⟨_, hpp, _, hpz, _⟩ := Finset.mem_filter.mp hp
    have hlt : (p : ℝ) < (2 : ℝ) ^ J := by linarith
    exact ⟨hpp.ne_zero, by exact_mod_cast hlt⟩
  simp_rw [hpart]
  refine (dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
        (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j),
      roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ (C * H ^ 2 / Real.log X ^ (A + 2)) (by linarith)
    (fun j _ => k X H hXa hH hHX α q a hcop hqP hqQ hclose ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num)))).trans ?_
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
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

example : type_of% @Prep1121KLRough.second_sum_block := second_sum_block_of_dyadic

end LeanLab.KumchevLiu2007.Prep1121DKLRoughCut

#print axioms LeanLab.KumchevLiu2007.Prep1121DKLRoughCut.roughWeight_eq_one_of_le_two
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLRoughCut.first_sum_block_of_pieces
#print axioms LeanLab.KumchevLiu2007.Prep1121DKLRoughCut.second_sum_block_of_dyadic
