import LeanLab.PNTPort.ExplicitPsi1.PsiSchoenfeldLarge

/-!
# `|ψ(x) - x| ≤ √x log² x/(8π)` for `x ≥ 10^8`, under RH

I-5250, unit U-6734, CLOUD 20261020T2113Z-cloud51. AI wrote this file. Known mathematics:
Schoenfeld 1976 (6.3) has this bound for `x ≥ 73.2`; the lab had it for `x ≥ 10^11` in
`psi_schoenfeld_large`. Here the range `[10^8, 10^11]` is added with the same parameters
`h = √x log x/π`, `T = 2π √x/log x` in `psi_upper_gen` and `psi_lower_gen`; the only change is a
sharper treatment of the main terms: with `L = log x`, `l = log L`, the `L²/8` cancels and the
margin is `l (L - l)/2 - L + l - log 2π - 1.57 π`, which is positive for `L ≥ 18.4`, `l ≥ 2.91`.
CONDITIONAL ON RH, the Hasanalizade-Shen-Wong `N(T)` counts `HSWN70` and `HSWHead14`, and
`Ordinates14`. Binary Goldbach is OPEN.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14 S1 S2)

/-- `log 2π ≤ 1.84`. -/
lemma log_two_pi_le_184 : log (2 * π) ≤ 1.84 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hp := Real.pi_lt_d4
  have h1 := Real.exp_one_gt_d9
  have e : exp 1.84 = exp 1 * exp 0.84 := by rw [← Real.exp_add]; norm_num
  have h2 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.84) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  rw [e]
  nlinarith [Real.exp_pos 0.84]

/-- The numerical facts on `s = √x`, `L = log x`, `λ = log L` for `10^8 ≤ x ≤ 10^11`. -/
lemma mid_facts {x : ℝ} (hx : 10 ^ 8 ≤ x) (hx' : x ≤ 10 ^ 11) :
    10000 ≤ √x ∧ 18.4 ≤ log x ∧ log x ≤ 25.4 ∧ 2.91 ≤ log (log x) ∧ log (log x) ≤ 3.3 := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsx : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have hs1 : 10000 ≤ √x := by nlinarith
  have hL : 18.4 ≤ log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h1 := Real.exp_one_lt_d9
    have e : exp 18.4 = exp 1 ^ 18 * exp 0.4 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h2 : exp 0.4 ≤ 1.4919 := by
      have := Real.exp_bound' (x := 0.4) (by norm_num) (by norm_num) (n := 6) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    rw [e]
    have h3 : exp 1 ^ 18 ≤ (2.7182818286 : ℝ) ^ 18 := by gcongr
    have h4 : (2.7182818286 : ℝ) ^ 18 * 1.4919 ≤ 10 ^ 8 := by norm_num
    nlinarith [Real.exp_pos 0.4, pow_pos (Real.exp_pos 1) 18]
  have hL' : log x ≤ 25.4 := by
    rw [Real.log_le_iff_le_exp hx0]
    have h1 := Real.exp_one_gt_d9
    have e : exp 25.4 = exp 1 ^ 25 * exp 0.4 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h2 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.4)
    rw [e]
    have h3 : (2.7182818283 : ℝ) ^ 25 ≤ exp 1 ^ 25 := by gcongr
    have h4 : (10 : ℝ) ^ 11 ≤ (2.7182818283 : ℝ) ^ 25 * 1.48 := by norm_num
    nlinarith [Real.exp_pos 0.4, pow_pos (Real.exp_pos 1) 25]
  have hLpos : 0 < log x := by linarith
  have hl : 2.91 ≤ log (log x) := by
    rw [Real.le_log_iff_exp_le hLpos]
    have h1 := Real.exp_one_lt_d9
    have e : exp 2.91 = exp 1 ^ 2 * exp 0.91 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h2 : exp 0.91 ≤ 2.4844 := by
      have := Real.exp_bound' (x := 0.91) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    rw [e]
    have h3 : exp 1 ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr
    nlinarith [Real.exp_pos 0.91, pow_pos (Real.exp_pos 1) 2]
  have hl' : log (log x) ≤ 3.3 := by
    rw [Real.log_le_iff_le_exp hLpos]
    have h1 := Real.exp_one_gt_d9
    have e : exp 3.3 = exp 1 ^ 3 * exp 0.3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h2 := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.3)
    rw [e]
    have h3 : (2.7182818283 : ℝ) ^ 3 ≤ exp 1 ^ 3 := by gcongr
    nlinarith [Real.exp_pos 0.3, pow_pos (Real.exp_pos 1) 3]
  exact ⟨hs1, hL, hL', hl, hl'⟩

set_option maxHeartbeats 4000000 in
/-- The core inequality on `[10^8, 10^11]`, in plain real variables: `s = √x`, `L = log x`,
`l = log L`, `c = log 2π`, `p = π`, and `E` the extra `c` of the lower bound. -/
lemma core_mid {s L l c p E : ℝ} (hs : 10000 ≤ s) (hL : 18.4 ≤ L) (hL' : L ≤ 25.4)
    (hl : 2.91 ≤ l) (hl' : l ≤ 3.3) (hc1 : 1.8 ≤ c) (hc2 : c ≤ 1.84) (hp1 : 3.14 ≤ p)
    (hp2 : p ≤ 3.1416) (hE0 : 0 ≤ E) (hE : E ≤ 2) :
    s * L / p / 2 + E + 4.786 / (s * L / p) +
      (s + L / (2 * p)) * ((L / 2 - l) ^ 2 / (2 * p) + 1.57) +
      (s + L / (2 * p)) * (p * s + L) * ((c + L / 2 - l) / (p ^ 2 * s) +
        (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * p ^ 2 * s ^ 2)) ≤
    s * L ^ 2 / (8 * p) := by
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hp0 : 0 < p := by linarith
  set M := c + L / 2 - l with hM
  have hM0 : 0 ≤ M := by linarith
  have hM1 : M ≤ 11.63 := by linarith
  set u := L / (2 * p) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 4.05 := by
    rw [hu, div_le_iff₀ (by positivity)]; nlinarith
  set S1v := (L / 2 - l) ^ 2 / (2 * p) + 1.57 with hS1v
  have hS1v0 : 0 ≤ S1v := by positivity
  have hS1v1 : S1v ≤ 16.9 := by
    have a : (L / 2 - l) ^ 2 ≤ 95.86 := by nlinarith
    have b : (L / 2 - l) ^ 2 / (2 * p) ≤ 15.33 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have h1 : u * S1v ≤ 68.5 := by nlinarith
  set B := (c + L / 2 - l) / (p ^ 2 * s) + (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * p ^ 2 * s ^ 2)
    with hB
  have hKp : (s + u) * (p * s + L) = p * s ^ 2 + 1.5 * s * L + L ^ 2 / (2 * p) := by
    rw [hu]; field_simp; ring
  have hp2' : 9.85 ≤ p ^ 2 := by nlinarith
  have hp3' : 30.9 ≤ p ^ 3 := by nlinarith
  have h2 : (s + u) * (p * s + L) * B ≤ M * s / p + 260.1 := by
    rw [hKp, hB]
    have e : (p * s ^ 2 + 1.5 * s * L + L ^ 2 / (2 * p)) *
        ((c + L / 2 - l) / (p ^ 2 * s) + (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * p ^ 2 * s ^ 2)) =
        M * s / p + 1.5 * L * M / p ^ 2 + L ^ 2 * M / (2 * p ^ 3 * s) +
        (p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2)) * ((1.004 * M + 41.26) * L / (2 * p ^ 2)) := by
      rw [hM]; field_simp
    rw [e]
    have t1 : 1.5 * L * M / p ^ 2 ≤ 45.1 := by
      rw [div_le_iff₀ (by positivity)]
      have a : L * M ≤ 25.4 * 11.63 := mul_le_mul hL' hM1 hM0 (by norm_num)
      nlinarith
    have t2 : L ^ 2 * M / (2 * p ^ 3 * s) ≤ 0.1 := by
      rw [div_le_iff₀ (by positivity)]
      have a : L * M ≤ 25.4 * 11.63 := mul_le_mul hL' hM1 hM0 (by norm_num)
      have b : L ^ 2 * M ≤ 25.4 * (25.4 * 11.63) := by
        have : L ^ 2 * M = L * (L * M) := by ring
        rw [this]; exact mul_le_mul hL' a (by positivity) (by norm_num)
      have c' : 30.9 * 10000 ≤ p ^ 3 * s := mul_le_mul hp3' hs (by norm_num) (by positivity)
      nlinarith
    have t3a : p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2) ≤ 3.146 := by
      have a1 : 1.5 * L / s ≤ 0.004 := by rw [div_le_iff₀ hs0]; nlinarith
      have a2 : L ^ 2 / (2 * p * s ^ 2) ≤ 0.0004 := by
        rw [div_le_iff₀ (by positivity)]
        have : 10000 * 10000 ≤ s ^ 2 := by nlinarith
        have : 2 * 3.14 * (10000 * 10000) ≤ 2 * p * s ^ 2 := by nlinarith
        nlinarith
      linarith
    have t3b : (1.004 * M + 41.26) * L / (2 * p ^ 2) ≤ 68.3 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1.004 * M + 41.26) * L ≤ (1.004 * 11.63 + 41.26) * 25.4 :=
        mul_le_mul (by linarith) hL' hL0.le (by positivity)
      nlinarith
    have t3 : (p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2)) * ((1.004 * M + 41.26) * L / (2 * p ^ 2))
        ≤ 3.146 * 68.3 := by
      apply mul_le_mul t3a t3b (by positivity) (by norm_num)
    linarith
  have h4 : 4.786 / (s * L / p) ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have : s * L / p ≥ 10000 * 18.4 / 3.1416 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hp0]; nlinarith
    linarith
  -- the main terms: `L²/8` cancels, the margin is at least 0.27
  have key : L / 2 + ((L / 2 - l) ^ 2 / 2 + 1.57 * p) + (c + L / 2 - l) + 0.27 ≤ L ^ 2 / 8 := by
    have a : 0 ≤ (l - 2.91) * (L - 18.4) := mul_nonneg (by linarith) (by linarith)
    have b : 0 ≤ (l - 2.91) * (3.3 - l) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsp : 3183 ≤ s / p := by rw [le_div_iff₀ hp0]; nlinarith
  have hmain : s * L / p / 2 + s * S1v + M * s / p =
      s / p * (L / 2 + ((L / 2 - l) ^ 2 / 2 + 1.57 * p) + (c + L / 2 - l)) := by
    rw [hS1v, hM]; field_simp
  have e2 : s * L ^ 2 / (8 * p) = s / p * (L ^ 2 / 8) := by field_simp
  have hk : s / p * (L / 2 + ((L / 2 - l) ^ 2 / 2 + 1.57 * p) + (c + L / 2 - l)) + s / p * 0.27 ≤
      s / p * (L ^ 2 / 8) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left key (by positivity)
  have hA : (s + u) * S1v = s * S1v + u * S1v := by ring
  calc _ = s * L / p / 2 + E + 4.786 / (s * L / p) + (s + u) * S1v +
        (s + u) * (p * s + L) * B := by rw [hu, hS1v, hB]
    _ ≤ _ := by rw [e2]; linarith [hA]

set_option maxHeartbeats 4000000 in
/-- **`|ψ(x) - x| ≤ √x log² x/(8π)` for `10^8 ≤ x ≤ 10^11`**, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14` and `Ordinates14` for the zeros. -/
theorem psi_schoenfeld_mid (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 10 ^ 8 ≤ x) (hx' : x ≤ 10 ^ 11) :
    |psiF x - x| ≤ √x * log x ^ 2 / (8 * π) := by
  obtain ⟨hs1, hL, hL', hl, hl'⟩ := mid_facts hx hx'
  have hx0 : 0 < x := by linarith
  set s := √x with hsdef
  set L := log x with hLdef
  set l := log L with hldef
  set c := log (2 * π) with hcdef
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hsx : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hp0 := Real.pi_pos
  have hp1 : 3.14 ≤ π := Real.pi_gt_d2.le
  have hp2 : π ≤ 3.1416 := Real.pi_lt_d4.le
  have hc1 : 1.8 ≤ c := LeanLab.ChirreHagen2025.Lemma26H.c_lower
  have hc2 : c ≤ 1.84 := log_two_pi_le_184
  set h := s * L / π with hhdef
  have hh0 : 0 < h := by positivity
  set T := 2 * π * s / L with hTdef
  have hT : 70 ≤ T := by
    rw [hTdef, le_div_iff₀ hL0]; nlinarith
  have hlogT : log T = c + L / 2 - l := by
    rw [hTdef, Real.log_div (by positivity) hL0.ne', Real.log_mul (by positivity) hs0.ne']
    have hLs : L = 2 * log s := by
      rw [hLdef, ← hsx, Real.log_pow]; push_cast; ring
    linarith
  have hT0 : 0 < T := by linarith
  set M := c + L / 2 - l with hM
  have hM0 : 0 ≤ M := by linarith
  have hS1 : S1 T = (L / 2 - l) ^ 2 / (2 * π) + 1.57 := by
    unfold S1; rw [hlogT, hM, hcdef]; ring
  set B := (c + L / 2 - l) / (π ^ 2 * s) + (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * π ^ 2 * s ^ 2)
    with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hS2 : S2 T ≤ L / 2 * B := by
    unfold S2
    rw [hlogT]
    have a : (1.004 * M + 41.26 - 0.25 * T) / T ^ 2 ≤ (1.004 * M + 41.26) / T ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have e : M / (π * T) + (1.004 * M + 41.26) / T ^ 2 = L / 2 * B := by
      rw [hB, hTdef]; field_simp; ring
    linarith
  set K := s + L / (2 * π) with hK
  have hK0 : 0 < K := by positivity
  have hS1v0 : 0 ≤ (L / 2 - l) ^ 2 / (2 * π) + 1.57 := by positivity
  have hX1 : (x + h) ^ (1 / 2 : ℝ) ≤ K := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left hK0.le, hK, ← hsx, hhdef]
    have : 0 ≤ (L / (2 * π)) ^ 2 := sq_nonneg _
    have e : (s + L / (2 * π)) ^ 2 = s ^ 2 + s * L / π + (L / (2 * π)) ^ 2 := by field_simp; ring
    linarith
  have hX10 : 0 ≤ (x + h) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hX3 : (x + h) ^ (3 / 2 : ℝ) ≤ (x + h) * K := by
    rw [rpow_three_halves (by linarith)]
    exact mul_le_mul_of_nonneg_left hX1 (by linarith)
  have hx12 : x ^ (1 / 2 : ℝ) = s := by rw [hsdef, Real.sqrt_eq_rpow]
  have hx32 : x ^ (3 / 2 : ℝ) = s * s ^ 2 := by
    rw [rpow_three_halves hx0.le, hx12, hsx]; ring
  have hcore0 := core_mid (E := 0) hs1 hL hL' hl hl' hc1 hc2 hp1 hp2 le_rfl (by norm_num)
  have hcorec := core_mid (E := c) hs1 hL hL' hl hl' hc1 hc2 hp1 hp2 (by linarith) (by linarith)
  have hfac : 2 * ((x + h) * K) * (L / 2 * B) / h = K * (π * s + L) * B := by
    rw [hhdef, ← hsx]; field_simp
  set S1v := (L / 2 - l) ^ 2 / (2 * π) + 1.57 with hS1v
  have hc0 : h / 2 + 0 + 4.786 / h + K * S1v + K * (π * s + L) * B ≤
      s * L ^ 2 / (8 * π) := by
    rw [hhdef, hK, hS1v, hB]; exact hcore0
  have hcc : h / 2 + c + 4.786 / h + K * S1v + K * (π * s + L) * B ≤
      s * L ^ 2 / (8 * π) := by
    rw [hhdef, hK, hS1v, hB]; exact hcorec
  rw [abs_le]
  constructor
  · -- lower
    have hlow := psi_lower_gen hRH hN hH h14 (x := x) (h := h) (T := T)
      (by have : s * s = x := by rw [← hsx]; ring
          have : h ≤ 9 * s := by
            rw [hhdef, div_le_iff₀ hp0]; nlinarith
          nlinarith) hh0 hT
    rw [← hcdef] at hlow
    rw [hx12, hx32, hS1] at hlow
    have t1 : s * S1v ≤ K * S1v :=
      mul_le_mul_of_nonneg_right (by rw [hK]; have : 0 ≤ L / (2 * π) := by positivity
                                     linarith) hS1v0
    have t2 : 2 * (s * s ^ 2) * S2 T / h ≤ K * (π * s + L) * B := by
      have a : 2 * (s * s ^ 2) * S2 T / h ≤ 2 * (s * s ^ 2) * (L / 2 * B) / h := by
        apply div_le_div_of_nonneg_right _ hh0.le
        exact mul_le_mul_of_nonneg_left hS2 (by positivity)
      have b : 2 * (s * s ^ 2) * (L / 2 * B) / h = π * s ^ 2 * B := by
        rw [hhdef]; field_simp
      have c' : π * s ^ 2 * B ≤ K * (π * s + L) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        rw [hK]; have : 0 ≤ L / (2 * π) * (π * s + L) := by positivity
        nlinarith
      linarith
    linarith
  · -- upper
    have hup := psi_upper_gen hRH hN hH h14 (x := x) (h := h) (T := T) (by linarith) hh0 hT
    rw [hS1, ← hcdef] at hup
    have t1 : (x + h) ^ (1 / 2 : ℝ) * S1v ≤ K * S1v := mul_le_mul_of_nonneg_right hX1 hS1v0
    have t2 : 2 * (x + h) ^ (3 / 2 : ℝ) * S2 T / h ≤ K * (π * s + L) * B := by
      rw [← hfac]
      apply div_le_div_of_nonneg_right _ hh0.le
      rcases le_or_gt 0 (S2 T) with h0 | h0
      · apply mul_le_mul (by linarith) hS2 h0 (by positivity)
      · have : 2 * (x + h) ^ (3 / 2 : ℝ) * S2 T ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
        have : 0 ≤ 2 * ((x + h) * K) * (L / 2 * B) := by positivity
        linarith
    linarith

/-- **`|ψ(x) - x| ≤ √x log² x/(8π)` for every `x ≥ 10^8`**, under RH, CONDITIONAL ON `HSWN70`,
`HSWHead14` and `Ordinates14` for the zeros. Schoenfeld 1976 (6.3) on the range `x ≥ 10^8`. -/
theorem psi_schoenfeld_lower (hRH : RiemannHypothesis) (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 10 ^ 8 ≤ x) :
    |psiF x - x| ≤ √x * log x ^ 2 / (8 * π) := by
  rcases le_or_gt x (10 ^ 11) with h | h
  · exact psi_schoenfeld_mid hRH hN hH h14 hx h
  · exact psi_schoenfeld_large hRH hN hH h14 h.le

end LeanLab.PNTPort.ExplicitPsi1.Trivial
