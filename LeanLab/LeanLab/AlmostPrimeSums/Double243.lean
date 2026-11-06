import LeanLab.AlmostPrimeSums.Mass243
import LeanLab.AlmostPrimeSums.Abel243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Two unconditional Abel estimates evaluate the upper double prime kernel.
BJS https://arxiv.org/abs/2207.09452 pp. 57 to 58 equations 186 to 189.
-/

namespace LeanLab.AlmostPrimeSums.Double243

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.ChenExplicit.D1552
open LeanLab.AlmostPrimeSums.Decomp1527c LeanLab.AlmostPrimeSums.Decomp243a
open LeanLab.AlmostPrimeSums.Decomp243b
open LeanLab.AlmostPrimeSums.Prime243 LeanLab.AlmostPrimeSums.Abel243
open LeanLab.AlmostPrimeSums.Mass243

/-- A fixed large N domain supplies all elementary logarithm size conditions
used below. Derived size check for BJS pp. 57 to 58. -/
theorem large_log (N : ℕ) (hN : exp (exp 36) < N) : 144 < log (N : ℝ) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log (N : ℝ) := by simpa using log_lt_log (exp_pos _) hN
  have hh := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 36)
  norm_num at hh
  linarith

/-- The inner prime sum is at most H of the first prime plus 54 over log
squared N. This is a coarse unconditional form of BJS p. 58 equation 188. -/
theorem inner_kernel_upper (N : ℕ) (hN : exp (exp 36) < N) (p : ℕ)
    (hp : p ∈ middlePrimes N) :
    (∑ q ∈ primesIco (y3 N) (√((N : ℝ) / p)),
      1 / ((q : ℝ) * log ((N : ℝ) / (p * q)))) ≤ H N p + 54 / log N ^ 2 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hLbig := large_log N hN
  have hLp : 0 < log (N : ℝ) := by linarith
  have hpp : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1.pos
  have hpy : (p : ℝ) < y3 N := Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)
  have hy0 : 0 < y3 N := rpow_pos_of_pos hNp _
  have hly : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hlp : log (p : ℝ) < log N / 3 := by
    have hh := log_lt_log hpp hpy
    rwa [hly] at hh
  have hy2 : 2 ≤ y3 N := by
    have hh := add_one_le_exp (log (y3 N))
    rw [exp_log hy0, hly] at hh
    linarith
  have hq : 0 < (N : ℝ) / p := div_pos hNp hpp
  have hs0 : 0 < √((N : ℝ) / p) := sqrt_pos_of_pos hq
  have hls : log (√((N : ℝ) / p)) = (log N - log p) / 2 := by
    rw [log_sqrt hq.le, log_div hNp.ne' hpp.ne']
  have hys : y3 N ≤ √((N : ℝ) / p) := by
    apply (log_le_log_iff hy0 hs0).mp
    rw [hly, hls]
    linarith
  have hlog : 0 < log (N / (p * √(N / p))) := by
    rw [log_div hNp.ne' (mul_pos hpp hs0).ne', log_mul hpp.ne' hs0.ne', hls]
    linarith
  have hh := hP_prime_sum_coarse N p hNp hpp (y3 N) (√((N : ℝ) / p)) hy2 hys hlog
    (primesIco (y3 N) (√((N : ℝ) / p)))
    (by
      intro q hq
      exact ⟨(mem_filter.mp hq).2.1, (mem_filter.mp hq).2.2,
        Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hq).1)⟩)
  have hH : (∫ t in y3 N..√((N : ℝ) / p), 1 / (t * log t * log (N / (p * t)))) = H N p := by
    simp only [H, sqrt_eq_rpow]
  rw [hH] at hh
  have hweight : hP N p (√((N : ℝ) / p)) ≤ 3 / log N := by
    unfold hP
    have hg : log (N : ℝ) / 3 ≤ log (N / (p * √(N / p))) := by
      rw [log_div hNp.ne' (mul_pos hpp hs0).ne', log_mul hpp.ne' hs0.ne', hls]
      linarith
    have hr := one_div_le_one_div_of_le (by positivity : 0 < log (N : ℝ) / 3) hg
    convert hr using 1 <;> field_simp <;> ring
  have herr : 6 / log (y3 N) * hP N p (√((N : ℝ) / p)) ≤ 54 / log N ^ 2 := by
    calc
      _ ≤ 6 / log (y3 N) * (3 / log N) := mul_le_mul_of_nonneg_left hweight
        (by rw [hly]; positivity)
      _ = _ := by rw [hly]; field_simp; ring
  exact hh.trans (by linarith [herr])

/-- The outer H prime sum has coefficient cbar and a coarse logarithmic
error. This is the unconditional Abel step in BJS p. 58 equation 189. -/
theorem outer_kernel_upper (N : ℕ) (hN : exp (exp 36) < N) :
    (∑ p ∈ middlePrimes N, H N p / p) ≤ I73 / log N +
      (384 / 7 * log (13 / 8 : ℝ)) / log N ^ 2 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hLbig := large_log N hN
  have hLp : 0 < log (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) < N := (one_lt_exp_iff.mpr (exp_pos 36)).trans hN
  have hz : log (z8 N) = log N / 8 := by rw [log_rpow hNp]; ring
  have hy : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hz0 : 0 < z8 N := rpow_pos_of_pos hNp _
  have hzy : z8 N ≤ y3 N := rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  have hz2 : 2 ≤ z8 N := by
    have hh := add_one_le_exp (log (z8 N))
    rw [exp_log hz0, hz] at hh
    linarith
  have hs := chen_weight_sum_coarse (log N) (z8 N) (y3 N) hLp hz2 hzy hy.le
    (middlePrimes N)
    (by
      intro p hp
      exact ⟨(mem_filter.mp hp).2.1, (mem_filter.mp hp).2.2,
        Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)⟩) (H N)
    (by
      intro u hu
      have hu0 := hz0.trans_le hu.1
      have hlogu : log u / log N ≤ 1 / 3 := by
        apply (div_le_iff₀ hLp).2
        have hh := log_le_log hu0 hu.2
        rw [hy] at hh
        linarith
      have he : (N : ℝ) ^ (log u / log N) = u := by
        rw [rpow_def_of_pos hNp]
        have hh : log (N : ℝ) * (log u / log N) = log u := by field_simp
        rw [hh, exp_log hu0]
      have hh := H_rpow_eq N hN1 (log u / log N) hlogu
      rwa [he] at hh)
  rw [eq116_integral N hN, Hz_eq N hN, hz] at hs
  convert hs using 1 <;> field_simp <;> ring

/-- The reciprocal mass of the middle prime interval is at most two in the
large N domain. Derived coarse input for BJS p. 58 equation 188. -/
theorem middle_reciprocal_le_two (N : ℕ) (hN : exp (exp 36) < N) :
    (∑ p ∈ middlePrimes N, (1 : ℝ) / p) ≤ 2 := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hLbig := large_log N hN
  have hLp : 0 < log (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) < N := (one_lt_exp_iff.mpr (exp_pos 36)).trans hN
  have hz : log (z8 N) = log N / 8 := by rw [log_rpow hNp]; ring
  have hy : log (y3 N) = log N / 3 := by rw [log_rpow hNp]; ring
  have hz0 : 0 < z8 N := rpow_pos_of_pos hNp _
  have hzy : z8 N ≤ y3 N := rpow_le_rpow_of_exponent_le hN1.le (by norm_num)
  have hz2 : 2 ≤ z8 N := by
    have hh := add_one_le_exp (log (z8 N))
    rw [exp_log hz0, hz] at hh
    linarith
  have hsum := (le_abs_self _).trans (prime_interval_error (z8 N) (y3 N) hz2 hzy)
  have hmain : log (log (y3 N)) - log (log (z8 N)) = log (8 / 3 : ℝ) := by
    rw [hz, hy, log_div hLp.ne' (by norm_num), log_div hLp.ne' (by norm_num),
      log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num)]
    ring
  rw [hmain, hz] at hsum
  have he : 6 / (log (N : ℝ) / 8) = 48 / log N := by field_simp; ring
  rw [he] at hsum
  have h48 : 48 / log (N : ℝ) ≤ 1 / 3 := by
    rw [div_le_iff₀ hLp]
    linarith
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 3)
  change (∑ p ∈ primesIco (z8 N) (y3 N), (1 : ℝ) / p) ≤ 2
  linarith

/-- The actual double kernel is at most cbar divided by log N plus an explicit
constant over log squared N. BJS pp. 57 to 58 equations 186 to 189. -/
theorem double_kernel_upper (N : ℕ) (hN : exp (exp 36) < N) :
    doubleKernel N ≤ I73 / log N +
      (384 / 7 * log (13 / 8 : ℝ) + 108) / log N ^ 2 := by
  have houter := outer_kernel_upper N hN
  have hrecip := middle_reciprocal_le_two N hN
  have hstep : doubleKernel N ≤ (∑ p ∈ middlePrimes N, H N p / p) +
      (54 / log N ^ 2) * ∑ p ∈ middlePrimes N, (1 : ℝ) / p := by
    dsimp [doubleKernel]
    have hh := sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left
      (inner_kernel_upper N hN p hp) (by positivity : 0 ≤ 1 / (p : ℝ)))
    convert hh using 1
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  calc
    doubleKernel N ≤ _ := hstep
    _ ≤ (I73 / log N + (384 / 7 * log (13 / 8 : ℝ)) / log N ^ 2) +
        (54 / log N ^ 2) * 2 := add_le_add houter
          (mul_le_mul_of_nonneg_left hrecip (by positivity))
    _ = _ := by ring

/-- The upper normalized double kernel coefficient is cbar with arbitrary
positive error. This is the qualitative content of BJS p. 58 equation 189. -/
theorem double_kernel_upper_eventual (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, log N * doubleKernel N ≤ I73 + ε := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr := hlog.const_div_atTop (384 / 7 * log (13 / 8 : ℝ) + 108)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (exp (exp (36 : ℝ))),
    herr.eventually (gt_mem_nhds hε)] with N hN hsmall
  have hLp : 0 < log (N : ℝ) := by have := large_log N hN; linarith
  have hh := mul_le_mul_of_nonneg_left (double_kernel_upper N hN) hLp.le
  have he : log (N : ℝ) * (I73 / log N +
      (384 / 7 * log (13 / 8 : ℝ) + 108) / log N ^ 2) =
      I73 + (384 / 7 * log (13 / 8 : ℝ) + 108) / log N := by field_simp
  rw [he] at hh
  exact hh.trans (by linarith)

/-- The exact unsifted triple mass leaf, with the two Abel upper estimates
and qualitative prime counting supplied by proofs. BJS Lemma 52. -/
theorem triple_mass_upper :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (#(TSet N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3))) : ℝ)
        ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + ε) *
          ((N : ℝ) / log N) := by
  intro ε hε
  let δ := min 1 (ε / 4)
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hcb : I73 < 1 := by have hh := cbar_lt'; change I73 < 1; unfold I73; linarith
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hcb.le hδ.le
  have hcoeff : (1 + δ) * (I73 + δ) ≤ I73 + ε := by nlinarith [hprod]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((triple_count_le_double_kernel δ hδ).and
      ((double_kernel_upper_eventual δ hδ).and (eventually_ge_atTop (2 : ℕ))))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hcount, hker, hN2⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmain : (1 + δ) * N * doubleKernel N ≤ (1 + δ) * (I73 + δ) * (N / log N) := by
    have hh := mul_le_mul_of_nonneg_left hker (show 0 ≤ (1 + δ) * N / log N by positivity)
    convert hh using 1 <;> field_simp <;> ring
  exact hcount.trans (hmain.trans (mul_le_mul_of_nonneg_right hcoeff (div_nonneg hNp.le hLp.le)))

end LeanLab.AlmostPrimeSums.Double243
