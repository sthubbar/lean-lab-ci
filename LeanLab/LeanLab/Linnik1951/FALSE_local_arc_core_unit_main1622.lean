/-
FALSE. Refutation of two leaves of the local core split at the unit modulus.

The leaf local_arc_core_unit_scale1622 in SPLIT_local_arc_core_unit_main1622.lean asks, for
every positive C, for a positive c with C times N at most c times N times the thirteenth
power of the logarithm of N times the sum of the two scale errors at the unit modulus.
That sum is at most twice the reciprocal of N to the one fourteenth, and any fixed power of
the logarithm divided by a positive power of N tends to zero, so the right side is o of N
and the leaf fails already at C equal to one.

The leaf local_arc_core_unit_main1622 in SPLIT_local_arc_core_unit1622.lean bounds the
damped convolution at a residual between four and N by the same o of N quantity. At the
residual n equal to N the damping is the exponential of minus one, and every term of the
convolution is at least the reciprocal of the square of the logarithm of N, so the damped
convolution is at least the exponential of minus one times N minus three over the square
of the logarithm of N. That is far larger than the bound for large N, so the conclusion
body of that leaf is false; it is refuted below for every hypothesis, and the hypotheses
GRH and MellinBound280 play no role.

The source leaves are not imported: this file imports only Data491 for logConvolution1622
and Mathlib, and restates the conclusions character for character with a negation.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Data491
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.Linnik1951

open Filter Topology

/-- The fifteenth power of the logarithm of N over N to the one fourteenth tends to zero
along the naturals. -/
theorem false1622_tendsto :
    Tendsto (fun N : ℕ => Real.log N ^ 15 / (N : ℝ) ^ (1 / 14 : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (15 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 14)).tendsto_div_nhds_zero
  have h2 := h.comp tendsto_natCast_atTop_atTop
  refine h2.congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- For x at least one, the sum of the two scale errors at the unit modulus is at most
twice the reciprocal of x to the one fourteenth. -/
theorem false1622_scale_le (x : ℝ) (hx : 1 ≤ x) :
    1 / x ^ (1 / 7 : ℝ) + 1 / Real.sqrt (x ^ (1 / 7 : ℝ)) ≤ 2 / x ^ (1 / 14 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set t := x ^ (1 / 14 : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hx (by norm_num)
  have h7 : x ^ (1 / 7 : ℝ) = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  rw [h7, Real.sqrt_sq (by linarith)]
  have htp : 0 < t := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) htp]
  nlinarith

/-- For N at least three the logarithm of N is at least one. -/
theorem false1622_log_ge_one (x : ℝ) (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [← Real.log_exp 1]
  apply Real.log_le_log (Real.exp_pos 1)
  have := Real.exp_one_lt_d9
  linarith

/-- Eventually along the naturals the fifteenth power of the logarithm times the scale
sum at the unit modulus is below any given positive bound. -/
theorem false1622_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      Real.log N ^ 15 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)))
        < ε := by
  have h := (false1622_tendsto.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 2)))
  obtain ⟨M, hM⟩ := eventually_atTop.mp h
  refine ⟨max M 3, fun N hN => ?_⟩
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hlt := hM N hNM
  have hL : 0 ≤ Real.log N ^ 15 := by
    have := false1622_log_ge_one N hN3; positivity
  have hs := false1622_scale_le N (by linarith)
  have htp : 0 < (N : ℝ) ^ (1 / 14 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  calc Real.log N ^ 15 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)))
      ≤ Real.log N ^ 15 * (2 / (N : ℝ) ^ (1 / 14 : ℝ)) := mul_le_mul_of_nonneg_left hs hL
    _ = 2 * (Real.log N ^ 15 / (N : ℝ) ^ (1 / 14 : ℝ)) := by ring
    _ < 2 * (ε / 2) := by linarith
    _ = ε := by ring

/-- FALSE. The leaf local_arc_core_unit_scale1622 fails: its conclusion, quantified over every
positive C, is refuted at C equal to one, because the right side is o of N. -/
theorem not_local_arc_core_unit_scale1622 : ¬ (∀ C : ℝ, 0 < C →
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)))) := by
  intro h
  obtain ⟨c, hc, N0, hN0⟩ := h 1 one_pos
  obtain ⟨M, hM⟩ := false1622_eventually (1 / c) (by positivity)
  set N := max (N0 + 1) (max M 3) with hNdef
  have hN0' : N0 < N := by omega
  have hNM : M ≤ N := by omega
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
  have hle := hN0 N hN0'
  have hlt := hM N hNM
  have hL1 := false1622_log_ge_one N hN3
  set B := (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) with hB
  have hB0 : 0 ≤ B := by positivity
  have h1315 : Real.log N ^ 13 ≤ Real.log N ^ 15 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hNp : (0 : ℝ) < N := by linarith
  have hcB : c * (Real.log N ^ 13 * B) < 1 := by
    have : Real.log N ^ 13 * B < 1 / c :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1315 hB0) hlt
    calc c * (Real.log N ^ 13 * B) < c * (1 / c) := mul_lt_mul_of_pos_left this hc
      _ = 1 := by field_simp
  have : (N : ℝ) * 1 ≤ (N : ℝ) * (c * (Real.log N ^ 13 * B)) := by
    calc (N : ℝ) * 1 = 1 * (N : ℝ) := by ring
      _ ≤ c * (N : ℝ) * Real.log N ^ 13 * B := hle
      _ = (N : ℝ) * (c * (Real.log N ^ 13 * B)) := by ring
  have := le_of_mul_le_mul_left this hNp
  linarith

/-- Each term of the convolution at n at least four is at least the reciprocal of the
square of the logarithm of n, so the convolution is at least n minus three over that
square. -/
theorem false1622_conv_lower (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℝ) - 3) / Real.log n ^ 2 ≤ logConvolution1622 n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
      1 / (Real.log n * Real.log n) ≤
        1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
    intro m hm
    obtain ⟨hm2, hmn⟩ := Finset.mem_Icc.mp hm
    have hmge : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hnm : 2 ≤ n - m := by omega
    have hnmge : (2 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast hnm
    have hmle : (m : ℝ) ≤ n := by exact_mod_cast (by omega : m ≤ n)
    have hnmle : ((n - m : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n - m ≤ n)
    have h1 : Real.log (m : ℝ) ≤ Real.log n := Real.log_le_log (by linarith) hmle
    have h2 : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log n := Real.log_le_log (by linarith) hnmle
    have h1' : (0 : ℝ) < Real.log (m : ℝ) := Real.log_pos (by linarith)
    have h2' : (0 : ℝ) < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos (by linarith)
    exact one_div_le_one_div_of_le (mul_pos h1' h2') (mul_le_mul h1 h2 h2'.le hlogn.le)
  have hcard : (Finset.Icc 2 (n - 2)).card = n - 3 := by
    rw [Nat.card_Icc]
    omega
  rw [logConvolution1622]
  calc ((n : ℝ) - 3) / Real.log n ^ 2
      = ∑ _m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log n * Real.log n) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub (by omega)]
        push_cast
        ring
    _ ≤ _ := Finset.sum_le_sum hterm

/-- FALSE. The conclusion body of the leaf local_arc_core_unit_main1622, after its GRH and
MellinBound280 hypotheses, fails: at q equal to one and the residual n equal to N the damped
convolution is at least the exponential of minus one times N minus three over the square of
the logarithm of N, which beats the o of N bound. -/
theorem not_local_arc_core_unit_main1622_body : ¬ (
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
  rintro ⟨c, hc, N0, hN0⟩
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  obtain ⟨M, hM⟩ := false1622_eventually (Real.exp (-1) / (4 * c)) (by positivity)
  set N := max (N0 + 1) (max M 6) with hNdef
  have hN0' : N0 < N := by omega
  have hNM : M ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hN6 : (6 : ℝ) ≤ N := by exact_mod_cast (show 6 ≤ N by omega)
  have hNp : (0 : ℝ) < N := by linarith
  have hq : ((1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    rw [Nat.cast_one]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hle := hN0 N hN0' 1 le_rfl hq rfl (N : ℤ) (by exact_mod_cast hN4) le_rfl
  simp only [Int.toNat_natCast, Nat.cast_one, one_mul] at hle
  rw [Complex.norm_real, Real.norm_eq_abs, neg_div, div_self hNp.ne'] at hle
  have hconv := false1622_conv_lower N hN4
  have hL1 := false1622_log_ge_one N (by linarith)
  have hLp : 0 < Real.log N := by linarith
  have hconv0 : 0 ≤ logConvolution1622 N :=
    le_trans (div_nonneg (by linarith) (by positivity)) hconv
  rw [abs_of_nonneg (mul_nonneg he.le hconv0)] at hle
  have hlt := hM N hNM
  set B := (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) with hB
  have hB0 : 0 ≤ B := by positivity
  set L := Real.log N with hL
  -- e^-1 (N-3) ≤ e^-1 L^2 conv ≤ L^2 c N L^13 B = N c (L^15 B) < N c e^-1/(4c)
  have h2 : Real.exp (-1) * ((N : ℝ) - 3) ≤ L ^ 2 * (c * N * L ^ 13 * B) := by
    have hL2 : 0 < L ^ 2 := by positivity
    have : ((N : ℝ) - 3) ≤ L ^ 2 * logConvolution1622 N := by
      have := mul_le_mul_of_nonneg_left hconv hL2.le
      rwa [mul_div_cancel₀ _ hL2.ne'] at this
    calc Real.exp (-1) * ((N : ℝ) - 3) ≤ Real.exp (-1) * (L ^ 2 * logConvolution1622 N) :=
          mul_le_mul_of_nonneg_left this he.le
      _ = L ^ 2 * (Real.exp (-1) * logConvolution1622 N) := by ring
      _ ≤ L ^ 2 * (c * N * L ^ 13 * B) := mul_le_mul_of_nonneg_left hle hL2.le
  have h3 : L ^ 2 * (c * N * L ^ 13 * B) = (N : ℝ) * c * (L ^ 15 * B) := by ring
  have h4 : (N : ℝ) * c * (L ^ 15 * B) ≤ (N : ℝ) * c * (Real.exp (-1) / (4 * c)) :=
    mul_le_mul_of_nonneg_left hlt.le (by positivity)
  have h5 : (N : ℝ) * c * (Real.exp (-1) / (4 * c)) = Real.exp (-1) * N / 4 := by
    field_simp
  nlinarith

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.not_local_arc_core_unit_scale1622
#print axioms LeanLab.Linnik1951.not_local_arc_core_unit_main1622_body
