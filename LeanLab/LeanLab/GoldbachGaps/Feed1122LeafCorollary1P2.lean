/-
Second split step for `LeanLab.GoldbachGaps.Feed1122LeafCorollary1`, P0030 D. A. Goldston,
Linnik's theorem on Goldbach numbers in short intervals, Glasgow Math. J. 32 (1990) 285-297,
Corollary 1, page 292.

`leaf_rg_of_Rg_interval_proved` has exactly the statement of `leaf_rg_of_Rg_interval` and proves
it in full from `Rg_le_rg` and `rg_le_Rg` of `Goldston1990Cor1`: the lower half from
`R(n) ≤ r(n) log² (N + K)`, the upper half from `r(n) ≤ R(n) / log² y + 2 (y + 1)` with
`y = N / log⁴ N`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.GoldbachGaps.Feed1122LeafCorollary1
import LeanLab.GoldbachGaps.Goldston1990Cor1

namespace LeanLab.GoldbachGaps.Feed1122Cor1
open Real Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

/-- `leaf_rg_of_Rg_interval` of `Feed1122LeafCorollary1`, statement identical, proved. -/
theorem leaf_rg_of_Rg_interval_proved (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hR : Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), Rg n) / ((K N : ℝ) * N)) atTop
      (nhds 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2))
      atTop (nhds 1) := by
  have tL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tinv : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tL
  have tll : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tL
    simpa [Function.comp_def] using this
  have t2 : Tendsto (fun N : ℕ => Real.log N ^ 2 / (N : ℝ)) atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have t4 : Tendsto (fun N : ℕ => Real.log N ^ 4 / (N : ℝ)) atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  -- the lower function
  set Lk : ℕ → ℝ := fun N => Real.log ((N + K N : ℕ) : ℝ) with hLk
  set fR : ℕ → ℝ := fun N => (∑ n ∈ Icc N (N + K N), Rg n) / ((K N : ℝ) * N) with hfR
  -- L / Lk → 1, squeezed between 1 / (1 + 1/L) and 1
  have tlow : Tendsto (fun N : ℕ => (1 + (Real.log N)⁻¹)⁻¹) atTop (nhds 1) := by
    have := (tinv.const_add 1).inv₀ (by norm_num)
    simpa using this
  have eL : ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log N := tL.eventually_ge_atTop 2
  have e4 : ∀ᶠ N : ℕ in atTop, Real.log N ^ 4 / (N : ℝ) < 1 := t4.eventually (Iio_mem_nhds one_pos)
  have eN : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have ev := hK.and (eL.and (e4.and eN))
  have hLLk : ∀ᶠ N : ℕ in atTop, (1 + (Real.log N)⁻¹)⁻¹ ≤ Real.log N / Lk N ∧
      Real.log N / Lk N ≤ 1 ∧ 0 < Lk N := by
    filter_upwards [ev] with N ⟨⟨hK1, hKN⟩, hL2, _, hN1⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hL0 : 0 < Real.log N := by linarith
    have hL3 : 1 ≤ Real.log N ^ 3 := one_le_pow₀ (by linarith)
    have hKleN : (K N : ℝ) ≤ N := le_trans hKN (div_le_self hNpos.le hL3)
    have hlo : Real.log N ≤ Lk N := by
      simp only [hLk]; push_cast
      exact Real.log_le_log hNpos (by have : (0:ℝ) ≤ K N := Nat.cast_nonneg _; linarith)
    have hhi : Lk N ≤ Real.log N + 1 := by
      simp only [hLk]; push_cast
      have h2N : (N : ℝ) + K N ≤ 2 * N := by linarith
      have := Real.log_le_log (by positivity) h2N
      rw [Real.log_mul (by norm_num) hNpos.ne'] at this
      have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hLk0 : 0 < Lk N := by linarith
    refine ⟨?_, (div_le_one hLk0).2 hlo, hLk0⟩
    rw [show 1 + (Real.log N)⁻¹ = (Real.log N + 1) / Real.log N by field_simp, inv_div]
    exact div_le_div_of_nonneg_left hL0.le hLk0 hhi
  have tLLk : Tendsto (fun N : ℕ => Real.log N / Lk N) atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tlow tendsto_const_nhds
      (hLLk.mono fun _ h => h.1) (hLLk.mono fun _ h => h.2.1)
  -- L / log y → 1 with y = N / L⁴
  have tly : Tendsto (fun N : ℕ => (1 - 4 * (Real.log (Real.log N) / Real.log N))⁻¹) atTop
      (nhds 1) := by
    have := ((tll.const_mul 4).const_sub 1).inv₀ (by norm_num)
    simpa using this
  have tlower : Tendsto (fun N : ℕ => fR N * (Real.log N / Lk N) ^ 2) atTop (nhds 1) := by
    simpa using hR.mul (tLLk.pow 2)
  have tupper : Tendsto (fun N : ℕ => fR N * (1 - 4 * (Real.log (Real.log N) / Real.log N))⁻¹ ^ 2
      + (4 * (Real.log N)⁻¹ ^ 2 + 4 * (Real.log N ^ 2 / (N : ℝ)))) atTop (nhds 1) := by
    have := (hR.mul (tly.pow 2)).add (((tinv.pow 2).const_mul 4).add (t2.const_mul 4))
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tlower tupper
  · filter_upwards [ev, hLLk] with N ⟨⟨hK1, hKN⟩, hL2, h4, hN1⟩ ⟨_, _, hLk0⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast hK1
    have hL0 : 0 < Real.log N := by linarith
    have hsum : (∑ n ∈ Icc N (N + K N), Rg n) ≤
        (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) * Lk N ^ 2 := by
      rw [sum_mul]
      exact sum_le_sum fun n hn => Rg_le_rg (mem_Icc.mp hn).2
    simp only [hfR]
    rw [div_pow, show (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) / ((K N : ℝ) * N / Real.log N ^ 2) =
      (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) * Real.log N ^ 2 / ((K N : ℝ) * N) by field_simp]
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (∑ n ∈ Icc N (N + K N), Rg n) * Real.log N ^ 2 ≤
        (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) * Lk N ^ 2 * Real.log N ^ 2 :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ (K N : ℝ) * N)]
  · filter_upwards [ev] with N ⟨⟨hK1, hKN⟩, hL2, h4, hN1⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast hK1
    have hK1r : (1 : ℝ) ≤ K N := by exact_mod_cast hK1
    set L := Real.log N with hL
    have hL0 : 0 < L := by linarith
    set y : ℝ := N / L ^ 4 with hy
    have hL4 : 0 < L ^ 4 := by positivity
    have hy1 : 1 < y := by
      rw [hy, lt_div_iff₀ hL4, one_mul]; rwa [div_lt_one hNpos] at h4
    have hly : Real.log y = L * (1 - 4 * (Real.log L / L)) := by
      rw [hy, Real.log_div hNpos.ne' hL4.ne', Real.log_pow]; field_simp; push_cast; ring
    have hlyp : 0 < Real.log y := Real.log_pos hy1
    have hsum : (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) ≤
        (∑ n ∈ Icc N (N + K N), Rg n) / Real.log y ^ 2 + (K N + 1) * (2 * (y + 1)) := by
      calc (∑ n ∈ Icc N (N + K N), (rg n : ℝ))
          ≤ ∑ n ∈ Icc N (N + K N), (Rg n / Real.log y ^ 2 + 2 * (y + 1)) :=
            sum_le_sum fun n _ => rg_le_Rg n hy1
        _ = _ := by
          rw [sum_add_distrib, ← sum_div, sum_const, Nat.card_Icc,
            show N + K N + 1 - N = K N + 1 by omega, nsmul_eq_mul]
          push_cast; ring
    have hfac : (1 - 4 * (Real.log L / L))⁻¹ = L / Real.log y := by
      rw [hly]; field_simp
    rw [hfac]
    simp only [hfR]
    set SR := ∑ n ∈ Icc N (N + K N), Rg n with hSR
    set Sr := ∑ n ∈ Icc N (N + K N), (rg n : ℝ) with hSr
    have hk2 : ((K N : ℝ) + 1) / K N ≤ 2 := by rw [div_le_iff₀ hKpos]; linarith
    have hyL : 0 ≤ 2 * (y + 1) * L ^ 2 / N := by positivity
    calc Sr / ((K N : ℝ) * N / L ^ 2) = Sr * L ^ 2 / ((K N : ℝ) * N) := by field_simp
      _ ≤ (SR / Real.log y ^ 2 + (K N + 1) * (2 * (y + 1))) * L ^ 2 / ((K N : ℝ) * N) := by
          gcongr
      _ = SR / ((K N : ℝ) * N) * (L / Real.log y) ^ 2 +
            ((K N : ℝ) + 1) / K N * (2 * (y + 1) * L ^ 2 / N) := by
          field_simp
      _ ≤ SR / ((K N : ℝ) * N) * (L / Real.log y) ^ 2 + 2 * (2 * (y + 1) * L ^ 2 / N) := by
          gcongr
      _ = SR / ((K N : ℝ) * N) * (L / Real.log y) ^ 2 + (4 * L⁻¹ ^ 2 + 4 * (L ^ 2 / N)) := by
          rw [hy]; field_simp; ring

/-- `leaf_corollary1` of `DecompJ610`, statement `Corollary1`, now CONDITIONAL ON the single
LEAF `leaf_sum_Rg_interval_asymp`, Goldston page 292 display 7, since the unweighting step is
proved above. -/
theorem corollary1_of_one_leaf : Corollary1 := by
  intro K hK hJ
  exact leaf_rg_of_Rg_interval_proved K hK (leaf_sum_Rg_interval_asymp K hK hJ)

end LeanLab.GoldbachGaps.Feed1122Cor1

#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.leaf_rg_of_Rg_interval_proved
#print axioms LeanLab.GoldbachGaps.Feed1122Cor1.corollary1_of_one_leaf
