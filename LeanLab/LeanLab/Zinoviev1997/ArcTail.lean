/-
AI wrote this Lean code. Codex task69, 2026-10-25.
The elementary singular series tail in display 3.15, page 356.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.TotientTail
import LeanLab.Zinoviev1997.ModelBounds
import LeanLab.Zinoviev1997.SingularLower

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology ArithmeticFunction LeanLab.CircleOrth MeasureTheory
open LeanLab.PNTPort.Vinogradov
open LeanLab.HardyLittlewood1923.U1438
open scoped ArithmeticFunction.Moebius

/-- A shifted partial sum is the corresponding interval sum. -/
theorem shifted_totient_sum (Q M : ℕ) :
    (∑ i ∈ Finset.range M, 1 / (Nat.totient (i + (Q + 1)) : ℝ) ^ 2) =
      ∑ q ∈ Finset.Ioc Q (Q + M), 1 / (Nat.totient q : ℝ) ^ 2 := by
  apply Finset.sum_bij (fun i _ => i + (Q + 1))
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Ioc] at hi ⊢
    omega
  · intro i _ j _ hij
    omega
  · intro q hq
    simp only [Finset.mem_Ioc] at hq
    refine ⟨q - (Q + 1), ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intro i hi
    rfl

/-- The reciprocal totient square tail is summable from cutoff 2200. -/
theorem summable_totient_tail (Q : ℕ) (hQ : 2200 ≤ Q) :
    Summable (fun i : ℕ => 1 / (Nat.totient (i + (Q + 1)) : ℝ) ^ 2) := by
  apply summable_of_sum_range_le (fun i => by positivity)
  intro M
  rw [shifted_totient_sum]
  exact totientTail_Ioc_bound Q (Q + M) hQ

/-- The infinite reciprocal totient square tail is at most 7/240. -/
theorem tsum_totient_tail_le (Q : ℕ) (hQ : 2200 ≤ Q) :
    (∑' i : ℕ, 1 / (Nat.totient (i + (Q + 1)) : ℝ) ^ 2) ≤ 7 / 240 := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro M
  rw [shifted_totient_sum]
  exact totientTail_Ioc_bound Q (Q + M) hQ

/-- Every Ramanujan sum has norm at most the number of reduced residues. -/
theorem ramanujan_abs_le_totient (N q : ℕ) (hq : 0 < q) :
    |LeanLab.HeathBrown1985.ramanujan q N| ≤ Nat.totient q := by
  have h := ramanujan_sum hq N
  have hn : ‖(LeanLab.HeathBrown1985.ramanujan q N : ℂ)‖ ≤ Nat.totient q := by
    rw [← h]
    calc
      _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖LeanLab.PNTPort.LargeSieve.e ((N : ℝ) * a / q)‖ := norm_sum_le _ _
      _ = Nat.totient q := by
        simp only [LeanLab.PNTPort.LargeSieve.norm_e, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        rw [Nat.totient_eq_card_coprime]
        congr 1
        ext a
        simp only [Finset.mem_filter]
        exact and_congr_right (fun _ => Nat.coprime_comm)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hn

/-- Every term in the real singular series is bounded by the reciprocal totient square. -/
theorem abs_singTerm_le (N q : ℕ) (hq : 0 < q) :
    |singTerm N q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
  rw [singTerm_eq_fS, fS_apply hq N, abs_div, abs_mul]
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hmu : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hr := ramanujan_abs_le_totient N q hq
  rw [abs_of_pos (pow_pos hφ 3)]
  calc
    _ ≤ (1 * Nat.totient q) / (Nat.totient q : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul hmu hr (abs_nonneg _) (by norm_num)) (by positivity)
    _ = _ := by field_simp

/-- The singular series tail has absolute value at most 7/240. -/
theorem singular_tail_le (N Q : ℕ) (hQ : 2200 ≤ Q) :
    |∑' i : ℕ, singTerm N (i + (Q + 1))| ≤ 7 / 240 := by
  have hs : Summable (fun i : ℕ => |singTerm N (i + (Q + 1))|) :=
    (summable_nat_add_iff (f := fun q : ℕ => |singTerm N q|) (Q + 1)).mpr (summable_sing3 N)
  have hb : ∀ i : ℕ, |singTerm N (i + (Q + 1))| ≤
      1 / (Nat.totient (i + (Q + 1)) : ℝ) ^ 2 := by
    intro i
    exact abs_singTerm_le N _ (by omega)
  calc
    _ ≤ ∑' i : ℕ, |singTerm N (i + (Q + 1))| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i : ℕ => singTerm N (i + (Q + 1)))
          (by simpa only [Real.norm_eq_abs] using hs))
    _ ≤ ∑' i : ℕ, 1 / (Nat.totient (i + (Q + 1)) : ℝ) ^ 2 :=
      Summable.tsum_le_tsum hb hs (summable_totient_tail Q hQ)
    _ ≤ _ := tsum_totient_tail_le Q hQ

/-- The paper's cutoff lies above the sufficient cutoff 2200. -/
theorem arcCutoff_ge_2200 (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) : 2200 ≤ arcCutoff N := by
  have hl : (46 : ℝ) ≤ Real.log N :=
    le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  unfold arcCutoff
  apply Nat.le_floor
  push_cast
  nlinarith

/-- Display 3.15 with an explicit strict margin, without GRH. -/
theorem lemma32_tail_error (N Q : ℕ) (hN : 0 < N) (hQ : 2200 ≤ Q) :
    ‖(((∑' i : ℕ, singTerm N (i + (Q + 1)) : ℝ) : ℂ) * modelIntegral N)‖ <
      0.015 * (N : ℝ) ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have ht := singular_tail_le N Q hQ
  have hi := modelIntegral_norm_le N hN
  have hb := mul_le_mul ht hi (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 240)
  have hn : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  nlinarith

end LeanLab.Zinoviev1997
