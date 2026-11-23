/-
Integration unit integrate1122c, burst-20261122, session S81. P0088, Kumchev and Liu,
arXiv 0801.0130, Theorem 1 on the written range of page 16, the Prop
Task129W.kumchev_liu_thm1_written, assembled from the twin proofs of the
burst-20261122 branches instead of the seven open leaves on main beneath
DQThm1Char.thm1_written_of_char_inputs.

The leaves on main cannot be replaced in place: the twin files import the files
that hold the leaves. So each assembly step of S33's proof whose proof used a leaf
is re-proved here with the leaf turned into an argument of its exact type, and the
twin is passed in.

* display 27: Burst1122B27.bound27_of_leaves, resting on the LEAF kernel_sum_bound.
* display 20: bound20_of_mean below, fed Prep1122KLGallagherCut's twin of
  S2_sub_S2star_major_mean_square, resting on the LEAF saffari_vaughan_device.
* display 24: S2starMinorSplit1122.bound24_unconditional, no sorry.
* display 26: bound26_of_parts below, fed Prep1122S1StarM0Cut's twin of
  S1_sub_S1star_on_M0 and Integrate1122cS2starL1, a copy of the gauss_coprime twin of S2star_M0_L1, no sorry.
* first sum of display 52: Split1122KLFirstRoughHalves.first_sum_block_of_halves,
  resting on the Lemma 3.4 case leaves case_one, case_two, case_three of
  Prep1122KLLemma34Cases.
* second sum of display 52: second_sum_block_of_dyadic_hyp below, fed
  Split1122SecondDyadicBlock.second_dyadic_block_of_cases, resting on the LEAFs
  case1_small_D, case2_middle_D, case3_large_D.

CONDITIONAL ON the cited A12Corr and A22Corr. This file has no sorry.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.DQThm1CharWiring
import LeanLab.KumchevLiu2007.Bound27Split1122
import LeanLab.KumchevLiu2007.Prep1122KLGallagherCut
import LeanLab.KumchevLiu2007.S2starMinorSplit1122
import LeanLab.KumchevLiu2007.Prep1122S1StarM0Cut
import LeanLab.KumchevLiu2007.Integrate1122cS2starL1
import LeanLab.KumchevLiu2007.Split1122KLFirstRoughHalves
import LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock

namespace LeanLab.KumchevLiu2007.DQThm1Integrate1122c

section Major

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open Prep1121DKLMajorCut
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 6 display 20, the statement of Prep1121KLMajor.bound20, from the
mean square of S2 - S2* over the major arcs given as hS in the exact form of the
leaf Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square. The proof of
Prep1121DKLMajorCut.bound20_of_pieces with that leaf made an argument. -/
theorem bound20_of_mean
    (hS : type_of% @Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square)
    (h : A22Corr) : BlockErrorBound termB := by
  intro B hB ε hε hε'
  obtain ⟨C, X0, hC, k⟩ := hS h B hB ε hε hε'
  refine ⟨Real.sqrt 2 * Real.sqrt C, max X0 3, by positivity, ?_⟩
  intro X H hX hlo hhi n
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY1 := Prep1121DKLMajorCut.windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  set Y := windowY X ε
  set P := Real.log X ^ B
  obtain ⟨m2, c2, b2⟩ := S2star_props Y H P
  have hG : Measurable (fun α => roughSum Y P α - S2star Y H P α) :=
    (cont_S2 Y P).measurable.sub m2
  obtain ⟨c3, b3⟩ : ∃ c : ℝ, ∀ α, ‖roughSum Y P α‖ ≤ c :=
    ⟨∑ m ∈ squareWindow Y, ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖, fun α => by
      unfold roughSum
      exact Prep1121DKLMajorCut.trig_norm_le _ _ _ _⟩
  have hc := cauchy_S1 X Y n _ (measurableSet_Ioc.inter (measurableSet_majorArcs H P))
    Set.inter_subset_left _ hG (c3 + c2) (fun α => (norm_sub_le _ _).trans
      (add_le_add (b3 α) (b2 α)))
  have h1 := S1_mean_square (sub_nonneg.mpr (windowY_le (by linarith) hε')) hY1
  have h3 := k X H hXa hlo hhi
  have hs1 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) ≤
      Real.sqrt 2 * Real.sqrt Y := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
        ‖roughSum Y P α - S2star Y H P α‖ ^ 2) ≤ Real.sqrt C * P ^ (-(1 / 4 : ℝ)) := by
    have hq : Real.sqrt (P ^ (-(1 / 2 : ℝ))) = P ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le]
      norm_num
    rw [← hq, ← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt h3
  have hnn1 : 0 ≤ Real.sqrt 2 * Real.sqrt Y := by positivity
  calc ‖termB X Y H P n‖ ≤ _ := hc
    _ ≤ (Real.sqrt 2 * Real.sqrt Y) * (Real.sqrt C * P ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul hs1 hs3 (Real.sqrt_nonneg _) hnn1
    _ = Real.sqrt 2 * Real.sqrt C * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by ring


/-- P0088 page 6 display 26, the statement of Prep1121KLMajor.bound26, from display 25
and the L1 bound of S2* over M0, given as hS1 and hS2 in the exact form of the leaves
S1_sub_S1star_on_M0 and S2star_M0_L1 of Prep1121DKLMajorCut. The proof of
Prep1121DKLMajorCut.bound26_of_pieces with those leaves made arguments. -/
theorem bound26_of_parts
    (hS1 : type_of% @Prep1121DKLMajorCut.S1_sub_S1star_on_M0)
    (hS2 : type_of% @Prep1121DKLMajorCut.S2star_M0_L1)
    (hA : A12Corr) (h2 : T2BoundProp) : BlockErrorBound termD := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, k1⟩ := hS1 hA B hB ε hε hε'
  obtain ⟨C2, X2, hC2, k2⟩ := hS2 h2 B hB ε hε hε'
  refine ⟨C1 * C2, max (max X1 X2) 3, by positivity, ?_⟩
  intro X H hX hlo hhi n
  have hXa : X1 ≤ X := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hX
  have hXb : X2 ≤ X := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY1 := Prep1121DKLMajorCut.windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  set Y := windowY X ε
  set P := Real.log X ^ B
  have hY : 0 < Y := by linarith
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hd := termD_le X Y H P _ n (k1 X H hXa hlo hhi)
  have hKnn : 0 ≤ C1 * Y * P ^ (-2 : ℝ) := by positivity
  refine hd.trans ((mul_le_mul_of_nonneg_left (k2 X H hXb hlo hhi) hKnn).trans (le_of_eq ?_))
  have hp : P ^ (-2 : ℝ) * P ^ (7 / 4 : ℝ) = P ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hP]; norm_num
  have hyy : Y / Real.sqrt Y = Real.sqrt Y := Real.div_sqrt
  calc C1 * Y * P ^ (-2 : ℝ) * (C2 * P ^ (7 / 4 : ℝ) / Real.sqrt Y)
      = C1 * C2 * (Y / Real.sqrt Y) * (P ^ (-2 : ℝ) * P ^ (7 / 4 : ℝ)) := by ring
    _ = C1 * C2 * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by rw [hp, hyy]


end Major

section Rough

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open Prep1121DKLRoughCut
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 15 display 52 second sum, the statement of Prep1121KLRough.second_sum_block,
from page 11 Lemma 3.4 on one dyadic block of primes given as hD in the exact form of
the leaf Prep1121DKLRoughCut.second_dyadic_block. The proof of
Prep1121DKLRoughCut.second_sum_block_of_dyadic with that leaf made an argument. -/
theorem second_sum_block_of_dyadic_hyp
    (hD : type_of% @Prep1121DKLRoughCut.second_dyadic_block) (A : ℝ) (hA : 0 < A) :
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
  obtain ⟨B2, hB2, h2⟩ := hD (A + 2) (by linarith)
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


end Rough

open LeanLab.KumchevLiu2007 Prep1121KLMajor

/-- The rough block bulk, the exact statement of Task628.rough_block_bulk, P0088 page 15
after display 52, from the twins of both Lemma 3.4 applications. It rests only on the
Lemma 3.4 case leaves of Prep1122KLLemma34Cases and Split1122SecondDyadicBlock.
No sorry of its own. -/
theorem rough_block_bulk_twin : type_of% @Task628.rough_block_bulk :=
  DQThm1Char.rough_block_bulk_of_sums Split1122KLFirstRoughHalves.first_sum_block_of_halves
    (second_sum_block_of_dyadic_hyp Split1122SecondDyadicBlock.second_dyadic_block_of_cases)

/-- P0088 page 7 display 28 squared, DQMajorArcBlock.MajorArcBlockHyp, from the four
twins of displays 27, 20, 24 and 26. CONDITIONAL ON A12Corr and A22Corr. -/
theorem majorArcBlockHyp_twin (hA12 : A12Corr) (hA22 : A22Corr) :
    DQMajorArcBlock.MajorArcBlockHyp :=
  DQMajorArcChar.major_arc_block_of_bounds
    (Burst1122B27.bound27_of_leaves T1_bound T2_bound)
    (bound20_of_mean Prep1122KLGallagherCut.S2_sub_S2star_major_mean_square_of_pieces hA22)
    S2starMinorSplit1122.bound24_unconditional
    (bound26_of_parts Prep1122S1StarM0Cut.S1_sub_S1star_on_M0_of_leaves
      Integrate1122cS2starL1.S2star_M0_L1_of_pieces hA12 T2_bound)

/-- Unit integrate1122c, the Palomar headline through the twins: P0088 Theorem 1 on the
written range of page 16, exactly Task129W.kumchev_liu_thm1_written, the conclusion of
DQThm1Char.thm1_written_of_char_inputs. CONDITIONAL ON the cited A12Corr and A22Corr.
No sorry of its own; its open LEAF pieces are those of the twin files. -/
theorem thm1_written_integrated (hA12 : A12Corr) (hA22 : A22Corr) :
    Task129W.kumchev_liu_thm1_written :=
  DQMajorArcBlock.thm1_written_of_hyps (majorArcBlockHyp_twin hA12 hA22) rough_block_bulk_twin

/-- Type check: the assembly has the exact type of the S33 headline. -/
example : type_of% @thm1_written_integrated =
    type_of% @DQThm1Char.thm1_written_of_char_inputs := rfl

example : type_of% @Task628.rough_block_bulk := rough_block_bulk_twin

end LeanLab.KumchevLiu2007.DQThm1Integrate1122c

#print axioms LeanLab.KumchevLiu2007.DQThm1Integrate1122c.bound20_of_mean
#print axioms LeanLab.KumchevLiu2007.DQThm1Integrate1122c.bound26_of_parts
#print axioms LeanLab.KumchevLiu2007.DQThm1Integrate1122c.second_sum_block_of_dyadic_hyp
#print axioms LeanLab.KumchevLiu2007.DQThm1Integrate1122c.rough_block_bulk_twin
#print axioms LeanLab.KumchevLiu2007.DQThm1Integrate1122c.majorArcBlockHyp_twin
#print axioms LeanLab.KumchevLiu2007.DQThm1Integrate1122c.thm1_written_integrated
