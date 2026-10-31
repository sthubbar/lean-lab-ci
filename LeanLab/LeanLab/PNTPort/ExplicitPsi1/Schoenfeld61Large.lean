import LeanLab.PNTPort.ExplicitPsi1.ThetaSchoenfeldLarge

/-!
# Schoenfeld 1976 (6.1) for `θ`, `|θ(x) - x| < √x (log x - 2) log x/(8π)`, for `x ≥ 3.6 · 10^13`

I-5270, unit U-6708, CLOUD 20261020T1816Z-cloud48, T2. AI wrote the Lean code. Known
mathematics: Schoenfeld 1976 (6.1) states this bound for `x ≥ 2.3 · 10^9`, cited in the lab as
`LeanLab.DERZ1997.Schoenfeld61`; here it is proved only for `x ≥ X0 = 3.6 · 10^13`, the range
Kaniecki's Lemma 6 actually uses, see KanieckiGapHSW.lean.

CONDITIONAL ON RH and on the Hasanalizade-Shen-Wong `N(T)` counts `HSWN70`, `HSWHead14` and
`Ordinates14`, every ordinate `|γ| ≥ 14`, for the true ordinates `gZ`. No Schoenfeld citation.

Method: cloud47's `psi_upper_gen` and `psi_lower_gen` with the same `h = √x log x/π` and
`T = 2π √x/log x` as `psi_schoenfeld_large_slack`, plus `ψ - θ ≤ 1.2 √x`; the only change is
the closing arithmetic `core61`, which spends the margin `log log x ≥ 3.43` against the `- 2 log x`.
Numerically, error over target is 0.978 at `x = 3.6 · 10^13`, 0.93 at `10^20`, 0.92 at `10^30`,
0.97 at `10^200`; the same `h`, `T` fail below about `10^12.3`, so `2.3 · 10^9` is out of reach
of this method with these zero counts.

Binary Goldbach is OPEN.
-/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

open Real Chebyshev
open LeanLab.Dudek2014.Section22
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14 S1 S2)

/-- `log x ≥ 31` and `log log x ≥ 3.43` for `x ≥ 3.6 · 10^13`. -/
lemma x0_facts {x : ℝ} (hx : 36 * 10 ^ 12 ≤ x) : 31 ≤ log x ∧ 3.43 ≤ log (log x) := by
  have hx0 : 0 < x := by linarith
  have hL : 31 ≤ log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h1 := Real.exp_one_lt_d9
    have e : exp 31 = exp 1 ^ 31 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have h3 : exp 1 ^ 31 ≤ (2.7182818286 : ℝ) ^ 31 := by gcongr
    have h4 : (2.7182818286 : ℝ) ^ 31 ≤ 36 * 10 ^ 12 := by norm_num
    linarith
  refine ⟨hL, ?_⟩
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have e : exp 3.43 = exp 1 ^ 3 * exp 0.43 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h2 : exp 0.43 ≤ 1.5373 := by
    have := Real.exp_bound' (x := 0.43) (by norm_num) (by norm_num) (n := 6) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [e]
  have h3 : exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
  nlinarith [Real.exp_pos 0.43, pow_pos (Real.exp_pos 1) 3]

set_option maxHeartbeats 4000000 in
/-- The core inequality for the `(log x - 2) log x` form, `L ≥ 31`, `l ≥ 3.43`, in plain real variables: `s = √x`, `L = log x`, `l = log L`, `c = log 2π`,
`p = π`, `K = s + L/(2π)`, `M = log T = c + L/2 - l`, and `E` the extra `2c` of the lower bound. -/
lemma core61 {s L l c p E : ℝ} (hs : 316227 ≤ s) (hL : 25.3 ≤ L) (hL31 : 31 ≤ L) (hl343 : 3.43 ≤ l) (hL2 : L ^ 2 ≤ s / 100)
    (hl : 3.2 ≤ l) (hlL : l ≤ L / 7) (hc1 : 1.8 ≤ c) (hc2 : c ≤ 2) (hp1 : 3.14 ≤ p) (hp2 : p ≤ 3.15)
    (hE0 : 0 ≤ E) (hE : E ≤ 4) :
    s * L / p / 2 + E + 4.786 / (s * L / p) + 1.2 * s +
      (s + L / (2 * p)) * ((L / 2 - l) ^ 2 / (2 * p) + 1.57) +
      (s + L / (2 * p)) * (p * s + L) * ((c + L / 2 - l) / (p ^ 2 * s) +
        (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * p ^ 2 * s ^ 2)) ≤
    s * (L - 2) * L / (8 * p) := by
  have hs0 : 0 < s := by linarith
  have hL0 : 0 < L := by linarith
  have hp0 : 0 < p := by linarith
  have hLs : L ≤ s / 2530 := by nlinarith
  set M := c + L / 2 - l with hM
  have hM0 : 0 ≤ M := by linarith
  have hM1 : M ≤ L / 2 := by linarith
  set u := L / (2 * p) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ L / 6.28 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set S1v := (L / 2 - l) ^ 2 / (2 * p) + 1.57 with hS1v
  have hS1v0 : 0 ≤ S1v := by positivity
  -- the square: (L/2 - l)² = L²/4 - l L + l²
  have hsq : (L / 2 - l) ^ 2 ≤ L ^ 2 / 4 := by nlinarith
  -- (1): u S1v ≤ L³/(16 p²) + 1.57 u, and L³ ≤ L s/100
  have h1 : u * S1v ≤ L / 6.28 * (L ^ 2 / 25.12 + 1.57) := by
    have : S1v ≤ L ^ 2 / 25.12 + 1.57 := by
      rw [hS1v]
      have : (L / 2 - l) ^ 2 / (2 * p) ≤ L ^ 2 / 4 / 6.28 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have e : L ^ 2 / 4 / 6.28 = L ^ 2 / 25.12 := by ring
      linarith
    exact mul_le_mul hu1 this hS1v0 (by positivity)
  have h1' : L / 6.28 * (L ^ 2 / 25.12 + 1.57) ≤ 0.00007 * s * L + 0.0002 * s := by
    have e : L / 6.28 * (L ^ 2 / 25.12 + 1.57) = L * L ^ 2 / 157.7536 + 0.25 * L := by ring
    have a : L * L ^ 2 ≤ L * (s / 100) := mul_le_mul_of_nonneg_left hL2 hL0.le
    have e2 : L * (s / 100) = s * L / 100 := by ring
    have hsL : 0 ≤ s * L := by positivity
    rw [e]
    have b1 : L * L ^ 2 / 157.7536 ≤ s * L / 15775.36 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    have b2 : 0.25 * L ≤ 0.0002 * s := by linarith
    have b3 : s * L / 15775.36 ≤ 0.00007 * s * L := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  -- (2): the tail term
  set B := (c + L / 2 - l) / (p ^ 2 * s) + (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * p ^ 2 * s ^ 2)
    with hB
  have hKp : (s + u) * (p * s + L) = p * s ^ 2 + 1.5 * s * L + L ^ 2 / (2 * p) := by
    rw [hu]; field_simp; ring
  have h2 : (s + u) * (p * s + L) * B ≤ M * s / p + 0.012 * s := by
    rw [hKp, hB]
    have e : (p * s ^ 2 + 1.5 * s * L + L ^ 2 / (2 * p)) *
        ((c + L / 2 - l) / (p ^ 2 * s) + (1.004 * (c + L / 2 - l) + 41.26) * L / (2 * p ^ 2 * s ^ 2)) =
        M * s / p + 1.5 * L * M / p ^ 2 + L ^ 2 * M / (2 * p ^ 3 * s) +
        (p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2)) * ((1.004 * M + 41.26) * L / (2 * p ^ 2)) := by
      rw [hM]; field_simp
    rw [e]
    have hp2' : 9.85 ≤ p ^ 2 := by nlinarith
    have hp3' : 30.9 ≤ p ^ 3 := by nlinarith
    have t1 : 1.5 * L * M / p ^ 2 ≤ 0.0008 * s := by
      rw [div_le_iff₀ (by positivity)]
      have a : L * M ≤ L * (L / 2) := mul_le_mul_of_nonneg_left hM1 hL0.le
      have b : s * 9.85 ≤ s * p ^ 2 := mul_le_mul_of_nonneg_left hp2' hs0.le
      have e1 : 1.5 * L * M = 1.5 * (L * M) := by ring
      have e2 : 0.0008 * s * p ^ 2 = 0.0008 * (s * p ^ 2) := by ring
      have e3 : L * (L / 2) = L ^ 2 / 2 := by ring
      rw [e1, e2]; linarith
    have t2 : L ^ 2 * M / (2 * p ^ 3 * s) ≤ 0.0001 * s := by
      rw [div_le_iff₀ (by positivity)]
      have a : L ^ 2 * M ≤ s / 100 * (s / 5060) := by
        apply mul_le_mul hL2 (by linarith) hM0 (by positivity)
      have b : s ^ 2 * 30.9 ≤ s ^ 2 * p ^ 3 := mul_le_mul_of_nonneg_left hp3' (sq_nonneg s)
      have e1 : 0.0001 * s * (2 * p ^ 3 * s) = 0.0002 * (s ^ 2 * p ^ 3) := by ring
      have e2 : s / 100 * (s / 5060) = s ^ 2 / 506000 := by ring
      have c0 : 0 ≤ s ^ 2 := sq_nonneg s
      rw [e1]; linarith
    have t3a : p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2) ≤ 3.151 := by
      have a1 : 1.5 * L / s ≤ 0.0006 := by rw [div_le_iff₀ hs0]; nlinarith
      have a2 : L ^ 2 / (2 * p * s ^ 2) ≤ 0.0001 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have t3b : (1.004 * M + 41.26) * L / (2 * p ^ 2) ≤ 0.0035 * s := by
      rw [div_le_iff₀ (by positivity)]
      have : (1.004 * M + 41.26) * L ≤ 0.502 * L ^ 2 + 41.26 * L := by nlinarith
      nlinarith
    have t3 : (p + 1.5 * L / s + L ^ 2 / (2 * p * s ^ 2)) * ((1.004 * M + 41.26) * L / (2 * p ^ 2))
        ≤ 3.151 * (0.0035 * s) := by
      apply mul_le_mul t3a t3b (by positivity) (by norm_num)
    linarith
  -- the main terms
  have h4 : 4.786 / (s * L / p) ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have : s * L / p ≥ 316227 * 25.3 / 3.15 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hp0]; nlinarith
    linarith
  have hmain : s * L / p / 2 + s * S1v + M * s / p + E + 0.001 + 1.212 * s +
      (0.00007 * s * L + 0.0002 * s) ≤ s * (L - 2) * L / (8 * p) := by
    rw [hS1v, hM]
    have key : L / 2 + ((L / 2 - l) ^ 2 / 2 + 1.57 * p) + (c + L / 2 - l) +
        (1.2122 + 0.00007 * L) * p + 0.001 ≤ L ^ 2 / 8 - L / 4 := by
      have hx : (l - 3.43) * (L + 2 - l - 3.43) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      have hLp : L * p ≤ L * 3.15 := mul_le_mul_of_nonneg_left hp2 hL0.le
      nlinarith
    have e : s * L / p / 2 + s * ((L / 2 - l) ^ 2 / (2 * p) + 1.57) + (c + L / 2 - l) * s / p + E +
        0.001 + 1.212 * s + (0.00007 * s * L + 0.0002 * s) =
        s / p * (L / 2 + ((L / 2 - l) ^ 2 / 2 + 1.57 * p) + (c + L / 2 - l) +
          (1.2122 + 0.00007 * L) * p) + E + 0.001 := by
      field_simp; ring
    rw [e]
    have e2 : s * (L - 2) * L / (8 * p) = s / p * (L ^ 2 / 8 - L / 4) := by field_simp; ring
    rw [e2]
    have hsp : 100000 ≤ s / p := by rw [le_div_iff₀ hp0]; nlinarith
    have : s / p * (L / 2 + ((L / 2 - l) ^ 2 / 2 + 1.57 * p) + (c + L / 2 - l) +
        (1.2122 + 0.00007 * L) * p) + s / p * 0.001 ≤ s / p * (L ^ 2 / 8 - L / 4) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left key (by positivity)
    nlinarith
  have hA : (s + u) * S1v = s * S1v + u * S1v := by ring
  have h2' : (s + u) * (p * s + L) * B = (s + L / (2 * p)) * (p * s + L) * B := by rw [hu]
  rw [hA] at *
  calc _ = s * L / p / 2 + E + 4.786 / (s * L / p) + 1.2 * s + (s * S1v + u * S1v) +
        (s + u) * (p * s + L) * B := by rw [hu, hS1v, hB]
    _ ≤ _ := by linarith

set_option maxHeartbeats 4000000 in
/-- **`|ψ(x) - x| ≤ √x (log x - 2) log x/(8π) - 1.2 √x - 1` for `x ≥ 3.6 · 10^13`**, under RH,
CONDITIONAL ON `HSWN70`, `HSWHead14` and `Ordinates14` for the zeros. -/
theorem psi_schoenfeld61_slack (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ)
    (hH : HSWHead14 gZ) (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx36 : 36 * 10 ^ 12 ≤ x) :
    |psiF x - x| ≤ √x * (log x - 2) * log x / (8 * π) - 1.2 * √x - 1 := by
  have hx : (10 : ℝ) ^ 11 ≤ x := by linarith
  obtain ⟨hs1, hL, hL2, hl, hlL, hLs⟩ := large_facts hx
  obtain ⟨hL31, hl343⟩ := x0_facts hx36
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
  have hp2 : π ≤ 3.15 := Real.pi_lt_d2.le
  have hc1 : 1.8 ≤ c := LeanLab.ChirreHagen2025.Lemma26H.c_lower
  have hc2 : c ≤ 2 := LeanLab.ChirreHagen2025.Lemma26H.c_upper
  have hLs' : L ≤ s / 2530 := by nlinarith
  set h := s * L / π with hhdef
  have hh0 : 0 < h := by positivity
  set T := 2 * π * s / L with hTdef
  have hT : 70 ≤ T := by
    rw [hTdef, le_div_iff₀ hL0]; nlinarith
  have hlogT : log T = c + L / 2 - l := by
    rw [hTdef, Real.log_div (by positivity) hL0.ne', Real.log_mul (by positivity) hs0.ne']
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
  -- the square roots
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
  have hcore0 := core61 (E := 1) hs1 hL hL31 hl343 hL2 hl hlL hc1 hc2 hp1 hp2 (by norm_num)
    (by norm_num)
  have hcorec := core61 (E := c + 1) hs1 hL hL31 hl343 hL2 hl hlL hc1 hc2 hp1 hp2 (by linarith)
    (by linarith)
  have hfac : 2 * ((x + h) * K) * (L / 2 * B) / h = K * (π * s + L) * B := by
    rw [hhdef, ← hsx]; field_simp
  have hhs : h ≤ s * s / 7944 := by
    have a : s * L ≤ s * (s / 2530) := mul_le_mul_of_nonneg_left hLs' hs0.le
    have b : s * L / π ≤ s * L / 3.14 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hp1
    rw [hhdef]
    have e : s * (s / 2530) / 3.14 = s * s / 7944.2 := by ring
    have c' : s * L / 3.14 ≤ s * (s / 2530) / 3.14 := div_le_div_of_nonneg_right a (by norm_num)
    have d : s * s / 7944.2 ≤ s * s / 7944 := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    linarith
  set S1v := (L / 2 - l) ^ 2 / (2 * π) + 1.57 with hS1v
  have hc0 : h / 2 + 1 + 4.786 / h + 1.2 * s + K * S1v + K * (π * s + L) * B ≤
      s * (L - 2) * L / (8 * π) := by
    rw [hhdef, hK, hS1v, hB]; exact hcore0
  have hcc : h / 2 + (c + 1) + 4.786 / h + 1.2 * s + K * S1v + K * (π * s + L) * B ≤
      s * (L - 2) * L / (8 * π) := by
    rw [hhdef, hK, hS1v, hB]; exact hcorec
  rw [abs_le]
  constructor
  · -- lower
    have hlow := psi_lower_gen hRH hN hH h14 (x := x) (h := h) (T := T)
      (by have : s * s = x := by rw [← hsx]; ring
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
      have hS20 : 0 ≤ S2 T ∨ S2 T < 0 := le_or_gt 0 (S2 T)
      rcases hS20 with h0 | h0
      · apply mul_le_mul (by linarith) hS2 h0 (by positivity)
      · have : 2 * (x + h) ^ (3 / 2 : ℝ) * S2 T ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) h0.le
        have : 0 ≤ 2 * ((x + h) * K) * (L / 2 * B) := by positivity
        linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- **Schoenfeld (6.1) for `θ`, `x ≥ 3.6 · 10^13`**: `|θ(x) - x| < √x (log x - 2) log x/(8π)`,
under RH, CONDITIONAL ON `HSWN70`, `HSWHead14` and `Ordinates14` for the zeros. -/
theorem theta_schoenfeld61_large (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ)
    {x : ℝ} (hx : 36 * 10 ^ 12 ≤ x) :
    |θ x - x| < √x * (Real.log x - 2) * Real.log x / (8 * π) := by
  have h1 := psi_schoenfeld61_slack hRH hN hH h14 hx
  rw [psiF_eq_psi] at h1
  have h2 := psi_sub_theta_large (x := x) (by linarith)
  have h3 := theta_le_psi x
  rw [abs_le] at h1
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2]

/-- The body of `LeanLab.DERZ1997.Schoenfeld61` with threshold `3.6 · 10^13` in place of
`2.3 · 10^9`, under RH, CONDITIONAL ON `HSWN70`, `HSWHead14`, `Ordinates14`. -/
theorem schoenfeld61_large (hRH : RiemannHypothesis)
    (hN : LeanLab.Dudek2014.SigmaH.HSWN70 gZ) (hH : HSWHead14 gZ)
    (h14 : LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ) :
    ∀ x : ℝ, 36 * 10 ^ 12 ≤ x →
      |θ x - x| < √x * (Real.log x - 2) * Real.log x / (8 * π) :=
  fun _ hx => theta_schoenfeld61_large hRH hN hH h14 hx

end LeanLab.PNTPort.ExplicitPsi1.Trivial
