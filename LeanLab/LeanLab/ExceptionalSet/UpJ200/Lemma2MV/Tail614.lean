/-
P0015, Montgomery and Vaughan 1975, display (6.14) on page 363, in gm form:
the tail of the singular series beyond q > X^{6 delta}, weighted by n ≤ X, is
O of X^{1 + delta} / X^{6 delta}.

AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.HeathBrown1985.SingularSeries
import LeanLab.HeathBrown1985.DivisorEps

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MV

open Finset

/-- Tail of the singular series in the form used for P0015 display (6.14) on page 363:
for F at least 1 and F ≤ P < F + 1, the sum of |gm n q| over q > P is at most
4 times (6 + 2 log F) d(n)^2 / F. -/
theorem tail614_tsum_le (n F : ℕ) (hn : 1 ≤ n) (hF : 1 ≤ F) (P : ℝ)
    (hFP : (F : ℝ) ≤ P) :
    ∑' q : ℕ, (if P < (q : ℝ) then |LeanLab.HeathBrown1985.gm n q| else 0) ≤
      4 * ((6 + 2 * Real.log F) * (n.divisors.card : ℝ) ^ 2 / F) := by
  apply Real.tsum_le_of_sum_range_le
  · intro q; split_ifs <;> positivity
  · intro N
    rw [← Finset.sum_filter]
    calc ∑ q ∈ (range N).filter (fun q : ℕ => P < (q : ℝ)), |LeanLab.HeathBrown1985.gm n q|
        ≤ ∑ q ∈ Ioc F N, |LeanLab.HeathBrown1985.gm n q| := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro q hq
            simp only [mem_filter, mem_range] at hq
            have : (F : ℝ) < q := lt_of_le_of_lt hFP hq.2
            have : F < q := by exact_mod_cast this
            simp only [mem_Ioc]; omega
          · intro _ _ _; positivity
      _ ≤ _ := LeanLab.HeathBrown1985.sum_abs_gm_Ioc_le n F N hn hF

/-- The main estimate of P0015 display (6.14) on page 363 in gm form: n times the
tail over q > X^{6 delta} is at most C X^{1 + delta} / X^{6 delta}. -/
theorem tail614_main : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (n : ℝ) * ∑' q : ℕ, (if X ^ (6 * δ) < (q : ℝ) then |LeanLab.HeathBrown1985.gm n q| else 0) ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  refine ⟨8, by norm_num, fun δ hδ hδ1 => ?_⟩
  set k : ℕ := ⌈8 / δ⌉₊ with hk_def
  have hk8 : 8 / δ ≤ (k : ℝ) := Nat.le_ceil _
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk8
  have hk : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by
    have : (1 : ℝ) ≤ 8 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith)
  have hkinv : (k : ℝ)⁻¹ ≤ δ / 8 := by
    rw [inv_le_comm₀ hkpos (by positivity), inv_div]; exact hk8
  obtain ⟨A, hA, hdiv⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  set B : ℝ := A ^ 2 * (6 + 8 / δ) with hB_def
  have hB : 0 < B := by positivity
  refine ⟨max 1 (B ^ (2 / δ)), fun X hX n hn hnX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXB : B ^ (2 / δ) ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  set P : ℝ := X ^ (6 * δ) with hP_def
  have hP1 : 1 ≤ P := Real.one_le_rpow hX1 (by positivity)
  set F : ℕ := ⌊P⌋₊ with hF_def
  have hF1 : 1 ≤ F := Nat.le_floor (by simpa using hP1)
  have hFP : (F : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hPF : P < (F : ℝ) + 1 := Nat.lt_floor_add_one P
  have hF1r : (1 : ℝ) ≤ F := by exact_mod_cast hF1
  have hFpos : (0 : ℝ) < F := by linarith
  have h2F : P ≤ 2 * F := by linarith
  have hT := tail614_tsum_le n F hn hF1 P hFP
  -- divisor bound
  set d : ℝ := (n.divisors.card : ℝ) with hd_def
  have hd0 : 0 ≤ d := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdX : d ≤ A * X ^ (δ / 8) := by
    calc d ≤ A * (n : ℝ) ^ ((k : ℝ)⁻¹) := hdiv n hn
      _ ≤ A * X ^ ((k : ℝ)⁻¹) := by
          gcongr
      _ ≤ A * X ^ (δ / 8) := by
          gcongr
  have hd2 : d ^ 2 ≤ A ^ 2 * X ^ (δ / 4) := by
    calc d ^ 2 ≤ (A * X ^ (δ / 8)) ^ 2 := by gcongr
      _ = A ^ 2 * X ^ (δ / 4) := by
          have : (X ^ (δ / 8)) ^ 2 = X ^ (δ / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
            congr 1; push_cast; ring
          rw [mul_pow, this]
  -- log bound
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogF : Real.log F ≤ Real.log X := by
    calc Real.log F ≤ Real.log P := Real.log_le_log hFpos hFP
      _ = 6 * δ * Real.log X := Real.log_rpow hX0 _
      _ ≤ 1 * Real.log X := by gcongr; linarith
      _ = Real.log X := one_mul _
  have hlogF0 : 0 ≤ Real.log F := Real.log_nonneg hF1r
  have hlogXle : Real.log X ≤ X ^ (δ / 4) / (δ / 4) :=
    Real.log_le_rpow_div hX0.le (by positivity)
  have hXq1 : 1 ≤ X ^ (δ / 4) := Real.one_le_rpow hX1 (by positivity)
  have hL : 6 + 2 * Real.log F ≤ (6 + 8 / δ) * X ^ (δ / 4) := by
    have : X ^ (δ / 4) / (δ / 4) = 4 / δ * X ^ (δ / 4) := by
      field_simp
    rw [this] at hlogXle
    have h8 : 2 * (4 / δ * X ^ (δ / 4)) = 8 / δ * X ^ (δ / 4) := by ring
    have h9 : (6 + 8 / δ) * X ^ (δ / 4) = 6 * X ^ (δ / 4) + 8 / δ * X ^ (δ / 4) := by ring
    linarith
  have hXh : X ^ (δ / 4) * X ^ (δ / 4) = X ^ (δ / 2) := by
    rw [← Real.rpow_add hX0]; ring_nf
  have hBX : B ≤ X ^ (δ / 2) := by
    calc B = (B ^ (2 / δ)) ^ (δ / 2) := by
            rw [← Real.rpow_mul hB.le]; field_simp; simp
      _ ≤ X ^ (δ / 2) := by gcongr
  have hXd : X ^ (δ / 2) * X ^ (δ / 2) = X ^ δ := by
    rw [← Real.rpow_add hX0]; ring_nf
  have hprod : (6 + 2 * Real.log F) * d ^ 2 ≤ X ^ δ := by
    have hL0 : 0 ≤ 6 + 2 * Real.log F := by linarith
    calc (6 + 2 * Real.log F) * d ^ 2
        ≤ ((6 + 8 / δ) * X ^ (δ / 4)) * (A ^ 2 * X ^ (δ / 4)) := by
          apply mul_le_mul hL hd2 (by positivity) (by positivity)
      _ = B * X ^ (δ / 2) := by rw [hB_def, ← hXh]; ring
      _ ≤ X ^ (δ / 2) * X ^ (δ / 2) := by gcongr
      _ = X ^ δ := hXd
  have hXδ0 : 0 < X ^ δ := Real.rpow_pos_of_pos hX0 _
  have hPpos : 0 < P := by linarith
  have hT0 : 0 ≤ ∑' q : ℕ, (if P < (q : ℝ) then |LeanLab.HeathBrown1985.gm n q| else 0) :=
    tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hTX : ∑' q : ℕ, (if P < (q : ℝ) then |LeanLab.HeathBrown1985.gm n q| else 0) ≤
      8 * X ^ δ / P := by
    refine le_trans hT ?_
    calc 4 * ((6 + 2 * Real.log F) * d ^ 2 / F) ≤ 4 * (X ^ δ / F) := by gcongr
      _ ≤ 8 * X ^ δ / P := by
          rw [show 4 * (X ^ δ / F) = 4 * X ^ δ / F by ring, div_le_div_iff₀ hFpos hPpos]
          nlinarith [mul_le_mul_of_nonneg_left h2F hXδ0.le]
  have hX1d : X ^ (1 + δ) = X * X ^ δ := by
    rw [Real.rpow_add hX0, Real.rpow_one]
  calc (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then |LeanLab.HeathBrown1985.gm n q| else 0)
      ≤ X * (8 * X ^ δ / P) := mul_le_mul hnX hTX hT0 hX0.le
    _ = 8 * (X ^ (1 + δ) / P) := by rw [hX1d]; ring

end LeanLab.ExceptionalSet.UpJ200.Lemma2MV

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MV.tail614_main
