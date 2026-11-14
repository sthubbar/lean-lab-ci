import Mathlib
open Real Finset
/-!
P0082 page 359 display 13 and pages 363 and 364 cases ii b and ii d.
Concrete exceptional correction sum and its elementary upper bounds.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.UpJ200.Decomp559d
/-- P0082 page 359 display 13. The finite weighted exceptional correction.
For P at least one this is exactly the sum over P less than k less than m minus P. -/
noncomputable def exceptionalJ (P β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 m).filter (fun k : ℕ => P < (k : ℝ) ∧ (k : ℝ) < m - P),
    ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1)

/-- P0082 page 359 display 13. The exceptional correction is nonnegative. -/
theorem exceptionalJ_nonneg (P β : ℝ) (m : ℕ) : 0 ≤ exceptionalJ P β m := by
  apply sum_nonneg
  intro k hk
  have hkm := (mem_Icc.mp (mem_filter.mp hk).1).2
  apply Real.rpow_nonneg
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hkm))

/-- P0082 page 363 case ii b. For beta at most one and P at least one,
the exceptional correction is at most m. -/
theorem exceptionalJ_le (P β : ℝ) (m : ℕ) (hP : 1 ≤ P) (hβ : β ≤ 1) :
    exceptionalJ P β m ≤ m := by
  let s := (Icc 1 m).filter (fun k : ℕ => P < (k : ℝ) ∧ (k : ℝ) < m - P)
  have hf : ∀ k ∈ s, ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1) ≤ 1 := by
    intro k hk
    obtain ⟨_, hkP, hkm⟩ := mem_filter.mp hk
    apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
    nlinarith
  have hs := Finset.sum_le_card_nsmul s _ 1 hf
  have hcard : s.card ≤ m := by
    calc
      _ ≤ (Icc 1 m).card := card_le_card (filter_subset _ _)
      _ = m := by simp
  have hcast : (s.card : ℝ) ≤ m := by exact_mod_cast hcard
  simpa [exceptionalJ, s] using hs.trans (by simpa using hcast)

/-- P0082 page 364 case ii d. The exceptional correction is at most m
to beta for positive m, beta at most one and P at least one. -/
theorem exceptionalJ_le_rpow (P β : ℝ) (m : ℕ) (hP : 1 ≤ P)
    (hβ : β ≤ 1) (hm : 1 ≤ m) : exceptionalJ P β m ≤ (m : ℝ) ^ β := by
  let s := (Icc 1 m).filter (fun k : ℕ => P < (k : ℝ) ∧ (k : ℝ) < m - P)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hf : ∀ k ∈ s, ((k : ℝ) * ((m : ℝ) - k)) ^ (β - 1) ≤ (m : ℝ) ^ (β - 1) := by
    intro k hk
    obtain ⟨hki, hkP, hkm⟩ := mem_filter.mp hk
    have hk2 : 2 ≤ k := by
      have h : (1 : ℝ) < k := hP.trans_lt hkP
      exact_mod_cast (show (2 : ℕ) ≤ k by exact_mod_cast h)
    have hmk : k + 2 ≤ m := by
      have h : (k : ℝ) + 1 < m := by linarith
      have h' : k + 1 < m := by exact_mod_cast h
      omega
    have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hmkR : (k : ℝ) + 2 ≤ m := by exact_mod_cast hmk
    have hbase : (m : ℝ) ≤ k * ((m : ℝ) - k) := by
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - 2 by linarith)
        (show 0 ≤ (m : ℝ) - k - 2 by linarith)]
    exact Real.rpow_le_rpow_of_nonpos hmpos hbase (by linarith)
  have hs := Finset.sum_le_card_nsmul s _ ((m : ℝ) ^ (β - 1)) hf
  have hcard : s.card ≤ m := by
    calc
      _ ≤ (Icc 1 m).card := card_le_card (filter_subset _ _)
      _ = m := by simp
  have hbound := mul_le_mul_of_nonneg_right (show (s.card : ℝ) ≤ m by exact_mod_cast hcard)
    (Real.rpow_nonneg hmpos.le (β - 1))
  have heq : (m : ℝ) * (m : ℝ) ^ (β - 1) = (m : ℝ) ^ β := by
    rw [Real.rpow_sub_one hmpos.ne']
    field_simp
  calc
    _ ≤ (s.card : ℝ) * (m : ℝ) ^ (β - 1) := by simpa [exceptionalJ, s] using hs
    _ ≤ (m : ℝ) * (m : ℝ) ^ (β - 1) := hbound
    _ = _ := heq
/-- P0082 page 364 case ii d and page 358 display 10. A fixed cap a on
the zero gap times log P gives deficit at least that gap times m times
log P divided by one plus a. The constant is uniform in m and beta. -/
theorem exceptionalJ_gap_lower_of_cap (P β a : ℝ) (m : ℕ) (hP : 1 ≤ P) (hPm : P ≤ m)
    (hβ : β ≤ 1) (ha : 0 ≤ a) (hcap : (1 - β) * Real.log P ≤ a) :
    (1 - β) * m * Real.log P / (1 + a) ≤ (m : ℝ) - exceptionalJ P β m := by
  have hPpos : 0 < P := by linarith
  have hmpos : (0 : ℝ) < m := hPpos.trans_le hPm
  have hm : 1 ≤ m := by exact_mod_cast hP.trans hPm
  let t := (1 - β) * Real.log P
  have ht0 : 0 ≤ t := mul_nonneg (by linarith) (Real.log_nonneg hP)
  have hta : t ≤ a := hcap
  have hden : 0 < 1 + t := by linarith
  have hfrac : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le hden
    linarith [Real.add_one_le_exp t]
  have hcapfrac : t / (1 + a) ≤ 1 - 1 / (1 + t) := by
    have hid : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
    rw [hid]
    exact div_le_div_of_nonneg_left ht0 hden (by linarith)
  have hlower : t / (1 + a) ≤ 1 - Real.exp (-t) :=
    hcapfrac.trans (sub_le_sub_left hfrac 1)
  have hpow := Real.rpow_le_rpow_of_nonpos hPpos hPm (show β - 1 ≤ 0 by linarith)
  have hJ := exceptionalJ_le_rpow P β m hP hβ hm
  have hJ' : exceptionalJ P β m ≤ (m : ℝ) * P ^ (β - 1) := by
    calc
      _ ≤ (m : ℝ) ^ β := hJ
      _ = (m : ℝ) * (m : ℝ) ^ (β - 1) := by rw [Real.rpow_sub_one hmpos.ne']; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
  have hPe : P ^ (β - 1) = Real.exp (-t) := by
    rw [Real.rpow_def_of_pos hPpos]
    congr 1
    dsimp [t]
    ring
  rw [hPe] at hJ'
  have hmul := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m)
  dsimp [t] at hmul
  have ha1 : 1 + a ≠ 0 := by positivity
  have hident : (m : ℝ) * ((1 - β) * Real.log P / (1 + a)) =
      (1 - β) * m * Real.log P / (1 + a) := by ring
  rw [hident] at hmul
  nlinarith only [hJ', hmul]

/-- P0082 page 364 case ii d. If the zero gap times log P is at most one,
the deficit m minus the exceptional correction is at least half of
one minus beta times m times log P. -/
theorem exceptionalJ_gap_lower (P β : ℝ) (m : ℕ) (hP : 1 ≤ P) (hPm : P ≤ m)
    (hβ : β ≤ 1) (hsmall : (1 - β) * Real.log P ≤ 1) :
    (1 - β) * m * Real.log P / 2 ≤ (m : ℝ) - exceptionalJ P β m := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    exceptionalJ_gap_lower_of_cap P β 1 m hP hPm hβ (by norm_num) hsmall

end LeanLab.ExceptionalSet.UpJ200.Decomp559d
