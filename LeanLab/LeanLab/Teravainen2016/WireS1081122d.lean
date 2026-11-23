/-
P0076, Theorem 1.1, the route after burst-20261122 S108. It rebuilds the nine inputs of
WireNine1122b.lean from the S108 proofs and splits, so theorem_1_1_S108 has the statement Theorem11
of theorem_1_1. Compared with theorem_1_1_S69 it no longer uses lemma71_choice, which S108 proved
FALSE as formalized in Lemma71Choice1122d.lean, and it no longer uses leaf_mertens_chi4,
leaf_geometric_interval, leaf_dual_count or singular_series_lower, all PROVED in S108.
The assembly bodies below are copies of gt42_all, paper_level_set_large_delta_of_leaves,
enveloping_v_decay_of_quadratic_bound and lemma52_dyad_S69, pointed at the S108 proofs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.WireS691122b
import LeanLab.Teravainen2016.GT42SmallSet1122d
import LeanLab.Teravainen2016.VDecayQuadratic1122d
import LeanLab.Teravainen2016.Lemma52DualProof1122d
import LeanLab.Teravainen2016.MertensChi4Tail1122d
import LeanLab.Teravainen2016.VDQLocalFactor1122d
import LeanLab.Teravainen2016.VDQSelbergDiagonal1122d
import LeanLab.Teravainen2016.Hyp64Arcs1122d

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.LevelSet1122b

open LeanLab.Teravainen2016

/-- Green and Tao, display 4.2 for every set B, the body of gt42_all with the small set case
taken from gt42_small_set_of_leaves of GT42SmallSet1122d.lean. -/
theorem gt42_all_S108 (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ B : Finset ℕ, B ⊆ range M →
          ∀ f : ℕ → ℂ, (∀ x, ‖f x‖ ≤ 1) →
            (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n *
              ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 ≤ K * (B.card : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨c, hc, K1, hK1, H⟩ := GT42SmallSet1122d.gt42_small_set_of_leaves A D hAD ε hε
  have hA := (hAD (ε * c) (mul_pos hε hc)).1
  refine ⟨K1 + A (ε * c), by linarith, ?_⟩
  intro J w hJ hw b hb hbW ham M hM hEB B hB f hf
  have hp : 0 ≤ (B.card : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases lt_or_ge (B.card : ℝ) ((M : ℝ) ^ c) with hs | hl
  · refine (H J w hJ hw b hb hbW ham M hM hEB B hB hs f hf).trans ?_
    nlinarith
  · refine (gt42_large_set A D hAD ε hε c hc J w hJ hw b hb hbW ham M hM hEB B hB hl f hf).trans ?_
    nlinarith

/-- Display 4.2 in the large delta form, the body of paper_level_set_large_delta_of_leaves on gt42_all_S108. -/
theorem paper_level_set_large_delta_S108 (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ → (M : ℝ) ^ (-c) < δ →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ K * δ ^ (-(2 + ε)) := by
  intro ε hε
  have he : 0 < ε / (2 + ε) := by positivity
  obtain ⟨K, hK, H⟩ := gt42_all_S108 A D hAD (ε / (2 + ε)) he
  refine ⟨1, one_pos, K ^ ((2 + ε) / 2), Real.rpow_pos_of_pos hK _, ?_⟩
  intro J w hJ hw b hb hbW ham M hM hEB a δ hδ _
  set Ξ := (range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖) with hΞ
  obtain ⟨f, hf, hdual⟩ := level_set_duality M hM (restrictionBeta w (WW J w) b M)
    (restrictionBeta_nonneg w (WW J w) b M) a δ hδ Ξ (fun ξ hξ => (mem_filter.mp hξ).2)
  have hg := H J w hJ hw b hb hbW ham M hM hEB Ξ (filter_subset _ _) f hf
  exact level_set_arith (Nat.cast_nonneg _) hδ hK hε (hdual.trans hg)

/-- Twin check against the LEAF paper_level_set_large_delta. -/
theorem paper_level_set_large_delta_twinS108 :
    type_of% @LeanLab.Teravainen2016.paper_level_set_large_delta :=
  paper_level_set_large_delta_S108

end LeanLab.Teravainen2016.LevelSet1122b

namespace LeanLab.Teravainen2016

/-- Proposition 4.1 v, the Ramare Ruzsa bound, the body of vdecay_quadratic_bound_of_leaves with the
local factor taken from vdq_local_factor_proved of VDQLocalFactor1122d.lean and the diagonalization
from vdq_selberg_diagonal_of_leaves of VDQSelbergDiagonal1122d.lean. -/
theorem vdecay_quadratic_bound_S108 :
    type_of% @LeanLab.Teravainen2016.vdecay_quadratic_bound := by
  refine ⟨21 / 5, by norm_num, ?_⟩
  intro w hw z hz q hq
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  rw [vdq_selberg_diagonal_of_leaves hw5 hz hq]
  set U := ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q then
          envelopingH w a * envelopingH w b *
            |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
        else 0) with hU
  have hg := vdq_density_pos hq
  have hG := envelopingG_one_le w hz
  have hG0 : 0 < envelopingG w 1 z := by linarith
  have hU0 : 0 ≤ U := by
    apply sum_nonneg; intro a _; apply sum_nonneg; intro b _
    split_ifs
    · have := envelopingH_nonneg w a
      have := envelopingH_nonneg w b
      positivity
    · exact le_refl 0
  have hloc := vdq_local_factor_proved hw5 (z := z) hq
  rw [← hU] at hloc
  set S := (envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q) with hS
  have hsum : |∑ n ∈ S, envelopingH w n *
      ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
          envelopingH w a * envelopingH w b *
            ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
        else 0)| ≤ envelopingG w 1 z * U := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ n ∈ S, (if (n : ℝ) ≤ z then envelopingH w n * U else 0) := by
          apply sum_le_sum
          intro n _
          rw [abs_mul, abs_of_nonneg (envelopingH_nonneg w n)]
          have hk := vdq_kernel_abs_le (w := w) (z := z) (q := q) (n := n)
          rw [← hU] at hk
          have hh := envelopingH_nonneg w n
          split_ifs at hk ⊢
          · exact mul_le_mul_of_nonneg_left hk hh
          · have : |∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
                (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
                  envelopingH w a * envelopingH w b *
                    ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
                else 0)| = 0 := le_antisymm hk (abs_nonneg _)
            rw [this, mul_zero]
      _ = (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ z), envelopingH w n) * U := by
          rw [← sum_filter, sum_mul]
      _ ≤ envelopingG w 1 z * U :=
          mul_le_mul_of_nonneg_right (vdq_truncated_mass w q) hU0
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos hg hG0)]
  calc 1 / (envelopingDensity w q * envelopingG w 1 z) * |_|
      ≤ 1 / (envelopingDensity w q * envelopingG w 1 z) * (envelopingG w 1 z * U) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = U / envelopingDensity w q := by field_simp
    _ ≤ (21 / 5 : ℝ) ^ q.primeFactors.card := by
        rw [div_le_iff₀ hg]; exact hloc

#print axioms vdq_truncated_mass
#print axioms vdq_density_pos
#print axioms vdq_kernel_abs_le
#print axioms vdecay_quadratic_bound_of_leaves

/-- Proposition 4.1 v, the body of enveloping_v_decay_of_quadratic_bound on vdecay_quadratic_bound_S108. -/
theorem enveloping_v_decay_S108 :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          ∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
            ‖envelopingV w (WW J w) b M q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1) := by
  obtain ⟨K, hK1, HB⟩ := vdecay_quadratic_bound_S108
  have hK2 : (1 : ℝ) ≤ 2 * K := by linarith
  choose C hC0 hC using fun (ε : ℝ) (hε : 0 < ε) => vdecay_omega_pow_le hK2 hε
  refine ⟨fun ε => if h : 0 < ε then C ε h else 1, ?_, ?_⟩
  · intro ε hε
    simp only [hε, dite_true]
    exact hC0 ε hε
  intro J w hJ hw b hb hbW hamen M hM ε hε q hq a ha hcop
  simp only [hε, dite_true]
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  have hz : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold envelopingV
  split_ifs with hs
  · obtain ⟨hqP, hsq, -, -, -⟩ := hs
    have hA := vdecay_local_eval_proved (J := J) hw5 b M hqP ha hcop
    have hBq := HB w hw _ hz q hqP
    have hD := vdecay_density_le w hsq
    have hc := hC ε hε q hq
    calc _ ≤ _ := hA
      _ ≤ (2 : ℝ) ^ q.primeFactors.card / q * K ^ q.primeFactors.card :=
          mul_le_mul hD hBq (abs_nonneg _) (by positivity)
      _ = (2 * K) ^ q.primeFactors.card / q := by rw [mul_pow]; ring
      _ ≤ C ε hε * (q : ℝ) ^ ε / q := div_le_div_of_nonneg_right hc hq0.le
      _ = C ε hε * (q : ℝ) ^ (ε - 1) := by
          rw [Real.rpow_sub_one hq0.ne', mul_div_assoc]
  · rw [norm_zero]
    exact mul_nonneg (hC0 ε hε).le (Real.rpow_nonneg hq0.le _)


/-- Twin check against the LEAF enveloping_v_decay. -/
theorem enveloping_v_decay_twinS108 : type_of% @LeanLab.Teravainen2016.enveloping_v_decay :=
  enveloping_v_decay_S108

/-- Proposition 5.1 for n ∼ N/3, the body of prop51_dyad_paper with Hypothesis 6.4 taken from
hyp64_exp_paper_of_leaves of Hyp64Arcs1122d.lean. -/
theorem prop51_dyad_S108 : type_of% @LeanLab.Teravainen2016.prop51_dyad :=
  prop51On_of_display71P dyad lemma71_choice_paper
    (display71OnP_of_leaves dyad rshape_dyad thm65_range hyp64_exp_paper_of_leaves
      (fun W b Q c₀ hA hQ hc => amenable_QW W b Q c₀ hA hQ hc))
    SingularLower1122d.singular_series_lower_proved

/-- Proposition 5.1 for N/3 < n < N/2, from the same inputs. -/
theorem prop51_half_S108 : type_of% @LeanLab.Teravainen2016.prop51_half :=
  prop51On_of_display71P half lemma71_choice_paper
    (display71OnP_of_leaves half rshape_half thm65_range hyp64_exp_paper_of_leaves
      (fun W b Q c₀ hA hQ hc => amenable_QW W b Q c₀ hA hQ hc))
    SingularLower1122d.singular_series_lower_proved

end LeanLab.Teravainen2016

namespace LeanLab.Teravainen2016.Nine1122b

/-- Lemma 5.2, page 18, for n ∼ N/3, on twisted_interval_bound_proved of Lemma52DualProof1122d.lean. -/
theorem lemma52_dyad_S108 : type_of% @LeanLab.Teravainen2016.lemma52_dyad :=
  lemma52On_of_twisted dyad (fun _ => Finset.filter_subset _ _) dyad_convex1122b
    twisted_interval_bound_proved

/-- Lemma 5.2, page 18, for N/3 < n < N/2, on twisted_interval_bound_proved. -/
theorem lemma52_half_S108 : type_of% @LeanLab.Teravainen2016.lemma52_half :=
  lemma52On_of_twisted half (fun _ => Finset.filter_subset _ _) half_convex1122b
    twisted_interval_bound_proved

/-- The nine inputs of theorem_1_1 after S108. -/
theorem nine_S108 : NineInputs :=
  ⟨leaf_mertens_chi4_proved1122d, LevelSet1122b.paper_level_set_large_delta_twinS108,
    enveloping_v_decay_twinS108, LeanLab.Teravainen2016.prop51_dyad_S108, LeanLab.Teravainen2016.prop51_half_S108, lemma52_dyad_S108, lemma52_half_S108,
    Lemma53Split.sum_bound_of_coprime_twin, QResCount1122b.leaf_qres_count_twin⟩

/-- Theorem 1.1, the statement Theorem11 of the sealed theorem_1_1, CONDITIONAL ON the open LEAFs
of the S108 files: leaf_pair_main of GT42SmallSet1122d.lean, vdq_G_yform and vdq_y_collapse of
VDQSelbergDiagonal1122d.lean, thm65_range of Display71Split1122d.lean, and hyp64_major_sem,
hyp64_major_lin, hyp64_minor_sem and hyp64_minor_lin of Hyp64Arcs1122d.lean. -/
theorem theorem_1_1_S108 : Theorem11 :=
  @theorem_1_1_of_nine nine_S108

end LeanLab.Teravainen2016.Nine1122b

#print axioms LeanLab.Teravainen2016.LevelSet1122b.gt42_all_S108
#print axioms LeanLab.Teravainen2016.LevelSet1122b.paper_level_set_large_delta_twinS108
#print axioms LeanLab.Teravainen2016.vdecay_quadratic_bound_S108
#print axioms LeanLab.Teravainen2016.enveloping_v_decay_twinS108
#print axioms LeanLab.Teravainen2016.prop51_dyad_S108
#print axioms LeanLab.Teravainen2016.prop51_half_S108
#print axioms LeanLab.Teravainen2016.Nine1122b.lemma52_dyad_S108
#print axioms LeanLab.Teravainen2016.Nine1122b.lemma52_half_S108
#print axioms LeanLab.Teravainen2016.Nine1122b.theorem_1_1_S108
