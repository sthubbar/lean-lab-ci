import LeanLab.ExceptionalSet.MVMajorCount
import LeanLab.PNTPort.Vinogradov.TernaryAsymp

/-!
# `MajorArcCount` PROVED: Estermann 1938 by his own circle method route

Lab proof, unit U-6250, CLOUD 20261020T0917Z-cloud39. AI wrote the Lean code. Known
mathematics: Estermann 1938, Vaughan's book Chapter 3. Binary Goldbach is OPEN.

* `errMV_le`: the error of `majorPart_explicit` is at most `Mx/16` under three numerical
  conditions on `x`, `Q`, `L = log x`.
* `majorArcCount_proved : MajorArcCount`, unconditional, ineffective through Siegel-Walfisz:
  for every `A > 0` and `B ≥ 2A + 2`, at most `e⁸ x/(log x)^A` even `n ∈ (x/2, x]` have major
  arc part at most `Mx/4` at `Q = (log x)^B`, for all large `x`. The exceptional `n` are among
  those with `∏_{p ∣ n} (1 + √p/(p - 1)) > (log x)^A`.
* `estermann_circle_method`: `LogPowerSaving`, Estermann 1938, from `vinogradovDFT_proved`'s
  `estermann_of_majorArcCount` and this; the lab's first route, through Heath-Brown, is
  `Estermann1938.main`.
-/

namespace LeanLab.ExceptionalSet.MVMajor

open Complex Finset Real ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

lemma aux_three {s L Q : ℝ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    2 * s * L + 35 * Q * s + 10 * Q ^ 2 * L ≤ 47 * (Q ^ 2 * L * s) := by
  have hs0 : 0 ≤ s := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hQ2 : Q ≤ Q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ Q by linarith)
    calc Q = Q * 1 := by ring
      _ ≤ Q * Q := this
      _ = Q ^ 2 := by ring
  have hQ2' : 1 ≤ Q ^ 2 := le_trans hQ hQ2
  have hQL : Q ^ 2 * s ≤ Q ^ 2 * L * s := by
    have := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ Q ^ 2 * s by positivity)
    calc Q ^ 2 * s = Q ^ 2 * s * 1 := by ring
      _ ≤ Q ^ 2 * s * L := this
      _ = Q ^ 2 * L * s := by ring
  have h1 : s * L ≤ Q ^ 2 * L * s := by
    have := mul_le_mul_of_nonneg_right hQ2' (show (0 : ℝ) ≤ L * s by positivity)
    calc s * L = 1 * (L * s) := by ring
      _ ≤ Q ^ 2 * (L * s) := this
      _ = Q ^ 2 * L * s := by ring
  have h2 : Q * s ≤ Q ^ 2 * L * s :=
    le_trans (mul_le_mul_of_nonneg_right hQ2 hs0) hQL
  have h3 : Q ^ 2 * L ≤ Q ^ 2 * L * s := by
    have := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ Q ^ 2 * L by positivity)
    calc Q ^ 2 * L = Q ^ 2 * L * 1 := by ring
      _ ≤ Q ^ 2 * L * s := this
  linarith

lemma aux_frac {Q : ℝ} (hQ : 1 ≤ Q) : 2 / Q + 1 / (2 * Q ^ 2) ≤ 3 / Q := by
  have hQ0 : 0 < Q := by linarith
  have h1 : 1 / (2 * Q ^ 2) ≤ 1 / Q := one_div_le_one_div_of_le hQ0 (by nlinarith)
  have h2 : 2 / Q + 1 / Q = 3 / Q := by ring
  linarith

lemma aux_sing {L A B Q : ℝ} (hL0 : 0 < L) (hL1 : 1 ≤ L) (hL6 : 6 * Real.exp 8 ≤ L)
    (hB : 2 * A + 2 ≤ B) (hQ : Q = L ^ B) (hQ1 : 1 ≤ Q) (hP1 : 1 ≤ ⌊Q⌋₊) :
    Real.exp 8 * L ^ A / Real.sqrt ⌊Q⌋₊ ≤ 1 / 4 := by
  have hP : Q / 2 ≤ (⌊Q⌋₊ : ℝ) := floor_ge_half hQ1
  have hsP : 0 < Real.sqrt ⌊Q⌋₊ := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < ⌊Q⌋₊))
  rw [div_le_iff₀ hsP]
  have hQA : L ^ (2 * A) * L ^ (2 : ℝ) ≤ Q := by
    rw [hQ, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hB
  rw [Real.rpow_two] at hQA
  have hsqA : (L ^ A) ^ 2 = L ^ (2 * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
  have h8 := Real.exp_pos 8
  have hL2 : 32 * Real.exp 8 ^ 2 ≤ L ^ 2 := by nlinarith
  have hLA : 0 ≤ L ^ (2 * A) := (Real.rpow_pos_of_pos hL0 _).le
  have h16 : (4 * Real.exp 8 * L ^ A) ^ 2 ≤ (⌊Q⌋₊ : ℝ) := by
    have e1 : (4 * Real.exp 8 * L ^ A) ^ 2 = 16 * Real.exp 8 ^ 2 * L ^ (2 * A) := by
      rw [mul_pow, mul_pow, hsqA]; ring
    rw [e1]
    have h3 : 16 * Real.exp 8 ^ 2 * L ^ (2 * A) ≤ (L ^ 2 / 2) * L ^ (2 * A) :=
      mul_le_mul_of_nonneg_right (by linarith) hLA
    have h4 : (L ^ 2 / 2) * L ^ (2 * A) = L ^ (2 * A) * L ^ 2 / 2 := by ring
    linarith
  have := Real.le_sqrt_of_sq_le h16
  linarith

/-- The error of `majorPart_explicit` is at most `Mx/16` under three numerical conditions. -/
theorem errMV_le {x : ℕ} {Q E L K ε Cφ : ℝ} (hx1 : (1 : ℝ) ≤ x) (hL : L = Real.log x)
    (hL1 : 1 ≤ L) (hQ1 : 1 ≤ Q) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hE0 : 0 ≤ E)
    (hE : E ≤ 7 * Real.sqrt x + Q * K * x * ε + 2 * Q * L)
    (hphi : ∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ) ≤ Cφ * (1 + Real.log Q))
    (S1 : 6768 * (Q ^ 5 * L ^ 2) ≤ Real.sqrt x)
    (S2 : 720 * (K * (Q ^ 5 * L * ε)) ≤ 1)
    (S3 : 648 * (Cφ * (1 + Real.log Q)) ≤ Q) :
    errMV x Q E ≤ (Mx x : ℝ) * x / 16 := by
  set s := Real.sqrt (x : ℝ) with hsdef
  have hs2 : s ^ 2 = x := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.2 hx1
  have hMe : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
  set M := (Mx x : ℝ) with hMdef
  have hM2 : 2 * (x : ℝ) ≤ M := by rw [hMe]; linarith
  have hM3 : M ≤ 3 * x := by rw [hMe]; linarith
  have hM0 : 0 < M := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hsum0 : 0 ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ) := sum_nonneg fun _ _ => by positivity
  -- the first part
  have hpsi : Chebyshev.psi (x : ℝ) - Chebyshev.theta x ≤ 2 * s * L := by
    rw [hL]; exact Chebyshev.psi_sub_theta_le hx1
  have hpsi0 : 0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta x := by
    have := Chebyshev.theta_le_psi (x : ℝ); linarith
  have hfac : 1 + 2 * π * x * Q / M ≤ 5 * Q := by
    have h1 : 2 * π * x * Q / M ≤ π * Q := by
      rw [div_le_iff₀ hM0]
      have h2 := mul_le_mul_of_nonneg_left hM2 (show 0 ≤ π * Q by positivity)
      calc 2 * π * x * Q = π * Q * (2 * x) := by ring
        _ ≤ π * Q * M := h2
    have h3 : π * Q ≤ 4 * Q := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hQ0.le
    linarith
  have hfac0 : 0 ≤ 1 + 2 * π * x * Q / M := by positivity
  have hD : (Chebyshev.psi (x : ℝ) - Chebyshev.theta x) + E * (1 + 2 * π * x * Q / M) ≤
      2 * s * L + 5 * Q * (7 * s + Q * K * x * ε + 2 * Q * L) := by
    have h1 : E * (1 + 2 * π * x * Q / M) ≤ E * (5 * Q) := mul_le_mul_of_nonneg_left hfac hE0
    have h2 : E * (5 * Q) ≤ (7 * s + Q * K * x * ε + 2 * Q * L) * (5 * Q) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    linarith
  have hxL : (x : ℝ) * Real.log x + x ≤ 2 * x * L := by
    rw [← hL]
    have := mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ x by positivity)
    linarith
  have hQQ : Q ^ 2 * (2 * Q + 1) ≤ 3 * Q ^ 3 := by
    have := mul_le_mul_of_nonneg_left hQ1 (show (0 : ℝ) ≤ Q ^ 2 by positivity)
    have e : Q ^ 2 * Q = Q ^ 3 := by ring
    linarith
  have hfirst : Q ^ 2 * ((2 * Q + 1) * (((Chebyshev.psi x - Chebyshev.theta x) +
      E * (1 + 2 * π * x * Q / M)) * (x * Real.log x + x))) ≤
      3 * Q ^ 3 * ((2 * s * L + 5 * Q * (7 * s + Q * K * x * ε + 2 * Q * L)) * (2 * x * L)) := by
    rw [← mul_assoc]
    apply mul_le_mul hQQ _ (by positivity) (by positivity)
    apply mul_le_mul hD hxL (by positivity) (by positivity)
  have hthree := aux_three hs1 hL1 hQ1
  have hfirst2 : 3 * Q ^ 3 * ((2 * s * L + 5 * Q * (7 * s + Q * K * x * ε + 2 * Q * L)) *
      (2 * x * L)) ≤ (x : ℝ) ^ 2 / 12 := by
    have e1 : 3 * Q ^ 3 * ((2 * s * L + 5 * Q * (7 * s + Q * K * x * ε + 2 * Q * L)) *
        (2 * x * L)) = 6 * Q ^ 3 * x * L * (2 * s * L + 35 * Q * s + 10 * Q ^ 2 * L) +
        30 * (K * (Q ^ 5 * L * ε)) * x ^ 2 := by ring
    rw [e1]
    have h1 : 6 * Q ^ 3 * x * L * (2 * s * L + 35 * Q * s + 10 * Q ^ 2 * L) ≤
        282 * (Q ^ 5 * L ^ 2) * (x * s) := by
      have := mul_le_mul_of_nonneg_left hthree (show 0 ≤ 6 * Q ^ 3 * x * L by positivity)
      calc 6 * Q ^ 3 * x * L * (2 * s * L + 35 * Q * s + 10 * Q ^ 2 * L)
          ≤ 6 * Q ^ 3 * x * L * (47 * (Q ^ 2 * L * s)) := this
        _ = 282 * (Q ^ 5 * L ^ 2) * (x * s) := by ring
    have h2 : 282 * (Q ^ 5 * L ^ 2) * (x * s) ≤ (x : ℝ) ^ 2 / 24 := by
      have := mul_le_mul_of_nonneg_left S1 (show 0 ≤ (x : ℝ) * s by positivity)
      calc 282 * (Q ^ 5 * L ^ 2) * ((x : ℝ) * s) =
            (1 / 24) * (((x : ℝ) * s) * (6768 * (Q ^ 5 * L ^ 2))) := by ring
        _ ≤ (1 / 24) * (((x : ℝ) * s) * s) := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = (1 / 24) * ((x : ℝ) * s ^ 2) := by ring
        _ = (x : ℝ) ^ 2 / 24 := by rw [hs2]; ring
    have h3 : 30 * (K * (Q ^ 5 * L * ε)) * x ^ 2 ≤ (x : ℝ) ^ 2 / 24 := by
      have := mul_le_mul_of_nonneg_left S2 (show 0 ≤ (x : ℝ) ^ 2 by positivity)
      calc 30 * (K * (Q ^ 5 * L * ε)) * (x : ℝ) ^ 2 =
            (1 / 24) * ((x : ℝ) ^ 2 * (720 * (K * (Q ^ 5 * L * ε)))) := by ring
        _ ≤ (1 / 24) * ((x : ℝ) ^ 2 * 1) := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = (x : ℝ) ^ 2 / 24 := by ring
    linarith
  -- the second part
  have hT0 : 2 * M / (Q / M) + 1 / (2 * (Q / M) ^ 2) ≤ 27 * x ^ 2 / Q := by
    have e1 : 2 * M / (Q / M) + 1 / (2 * (Q / M) ^ 2) = M ^ 2 * (2 / Q + 1 / (2 * Q ^ 2)) := by
      field_simp
    rw [e1]
    have h1 : 2 / Q + 1 / (2 * Q ^ 2) ≤ 3 / Q := aux_frac hQ1
    have h2 : M ^ 2 ≤ 9 * x ^ 2 := by
      have := pow_le_pow_left₀ hM0.le hM3 2
      calc M ^ 2 ≤ (3 * x) ^ 2 := this
        _ = 9 * x ^ 2 := by ring
    calc M ^ 2 * (2 / Q + 1 / (2 * Q ^ 2)) ≤ (9 * x ^ 2) * (3 / Q) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 27 * x ^ 2 / Q := by ring
  have hsecond : (∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ)) *
      (2 * M / (Q / M) + 1 / (2 * (Q / M) ^ 2)) ≤ (x : ℝ) ^ 2 / 24 := by
    have hT00 : 0 ≤ 2 * M / (Q / M) + 1 / (2 * (Q / M) ^ 2) := by positivity
    calc (∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ)) * (2 * M / (Q / M) + 1 / (2 * (Q / M) ^ 2))
        ≤ (Cφ * (1 + Real.log Q)) * (27 * x ^ 2 / Q) :=
          mul_le_mul hphi hT0 hT00 (le_trans hsum0 hphi)
      _ = 27 * (Cφ * (1 + Real.log Q)) * x ^ 2 / Q := by ring
      _ ≤ 27 * (Q / 648) * x ^ 2 / Q := by
          apply div_le_div_of_nonneg_right _ hQ0.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = (x : ℝ) ^ 2 / 24 := by field_simp; ring
  unfold errMV
  rw [← hMdef]
  have : (x : ℝ) ^ 2 / 12 + (x : ℝ) ^ 2 / 24 ≤ M * x / 16 := by
    have h1 := mul_le_mul_of_nonneg_right hM2 (show (0 : ℝ) ≤ x by positivity)
    have e : (x : ℝ) ^ 2 = x * x := by ring
    rw [e]
    linarith
  linarith [hfirst.trans hfirst2]

/-- **Estermann's major arc count, PROVED**, unconditional and ineffective. -/
theorem majorArcCount_proved : MajorArcCount := by
  intro A hA
  refine ⟨2 * A + 2, fun B hB => ?_⟩
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  obtain ⟨c, hc, K, hK, hmaj⟩ := major_arc B hB0
  obtain ⟨Cφ, hCφ, hphi⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  obtain ⟨K1, hK1, g1⟩ := LeanLab.PNTPort.BV.log_rpow_le_rpow (5 * B + 2) (1 / 4) (by norm_num)
  obtain ⟨K2, hK2, g2⟩ := LeanLab.PNTPort.BV.log_rpow_le_rpow (3 * B) (1 / 2) (by norm_num)
  obtain ⟨K3, hK3, g3⟩ := LeanLab.PNTPort.BV.exp_neg_sqrt_log_le (c / Real.sqrt 2)
    (by positivity) (5 * B + 2)
  set Lb : ℝ := 6 * Real.exp 8 + (1944 * Cφ) ^ 2 + 720 * K * K3 + 10 with hLb
  set Xr : ℝ := Real.exp Lb + (6768 * K1) ^ 4 + K2 ^ 2 + 10 with hXr
  refine ⟨Real.exp 8, ⌈Xr⌉₊, fun x hx => ?_⟩
  have hxX : Xr ≤ (x : ℝ) := le_trans (Nat.le_ceil Xr) (by exact_mod_cast hx)
  have hexpLb : Real.exp Lb ≤ x := by
    have : 0 ≤ (6768 * K1) ^ 4 + K2 ^ 2 := by positivity
    linarith
  have hx10 : (10 : ℝ) ≤ x := by
    have : 0 ≤ Real.exp Lb + (6768 * K1) ^ 4 + K2 ^ 2 := by positivity
    linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set L := Real.log x with hLdef
  have hLLb : Lb ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]; exact hexpLb
  have hLb1 : 10 ≤ Lb := by
    have : 0 ≤ 6 * Real.exp 8 + (1944 * Cφ) ^ 2 + 720 * K * K3 := by positivity
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  set Q := L ^ B with hQdef
  have hLQ : L ≤ Q := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 hB1
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  -- powers of `Q` as powers of `L`
  have hQ5 : Q ^ 5 * L ^ 2 = L ^ (5 * B + 2) := by
    rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      ← Real.rpow_add hL0]
    push_cast; ring_nf
  have hQ3 : Q ^ 3 = L ^ (3 * B) := by
    rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    push_cast; ring_nf
  -- the conditions of `card_major_small_le`
  have hx7 : 7 ≤ x := by exact_mod_cast (show (7 : ℝ) ≤ x by linarith)
  have hQM : 2 * Q ^ 3 < Mx x := by
    have h1 := g2 x hx2
    rw [← hLdef, ← hQ3] at h1
    have hsq : (x : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt x := by rw [Real.sqrt_eq_rpow]
    rw [hsq] at h1
    have hs2 : Real.sqrt (x : ℝ) ^ 2 = x := Real.sq_sqrt hx0.le
    have hK2s : K2 ≤ Real.sqrt x := by
      rw [show K2 = Real.sqrt (K2 ^ 2) by rw [Real.sqrt_sq hK2.le]]
      apply Real.sqrt_le_sqrt
      have : 0 ≤ Real.exp Lb + (6768 * K1) ^ 4 := by positivity
      linarith
    have : Q ^ 3 ≤ x := by
      calc Q ^ 3 ≤ K2 * Real.sqrt x := h1
        _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hK2s (Real.sqrt_nonneg _)
        _ = x := by rw [← pow_two, hs2]
    have hMe : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
    rw [hMe]; linarith
  have hP2 : 2 ≤ ⌊Q⌋₊ := Nat.le_floor (by push_cast; linarith)
  set ε := Real.exp (-c * Real.sqrt (L / 2)) with hεdef
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  set E := 7 * Real.sqrt x + Q * K * x * ε + Real.log Q / Real.log 2 * L with hEdef
  have hmaj' : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x) := by
    intro q hq a' ha' β
    rw [mem_Icc] at hq
    have hqQ : (q : ℝ) ≤ Q := le_trans (by exact_mod_cast hq.2) (Nat.floor_le hQ0.le)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.1
    have hx4 : Real.exp 4 ≤ (x : ℝ) := by
      have : Real.exp 4 ≤ Real.exp Lb := Real.exp_le_exp.2 (by linarith)
      linarith
    refine (hmaj x hx4 q hq.1 hqQ a' ha' β).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h1 : (q : ℝ) * K * x * Real.exp (-c * Real.sqrt (Real.log x / 2)) ≤ Q * K * x * ε := by
      rw [hεdef, hLdef]
      have : 0 ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x / 2)) := by positivity
      nlinarith
    have h2 : Real.log q / Real.log 2 * Real.log x ≤ Real.log Q / Real.log 2 * L := by
      rw [← hLdef]
      apply mul_le_mul_of_nonneg_right _ hL0.le
      apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
      exact Real.log_le_log (by linarith) hqQ
    rw [hEdef]; linarith
  -- the error
  have hErr : errMV x Q E ≤ (Mx x : ℝ) * x / 16 := by
    have hE0 : 0 ≤ E := by
      have : 0 ≤ Real.log Q / Real.log 2 * L :=
        mul_nonneg (div_nonneg (Real.log_nonneg hQ1) (Real.log_nonneg (by norm_num))) hL0.le
      rw [hEdef]; positivity
    have hE : E ≤ 7 * Real.sqrt x + Q * K * x * ε + 2 * Q * L := by
      have := lp_bound hQ1
      have : Real.log Q / Real.log 2 * L ≤ 2 * Q * L := mul_le_mul_of_nonneg_right this hL0.le
      rw [hEdef]; linarith
    have hphiQ : ∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ) ≤ Cφ * (1 + Real.log Q) := by
      refine (hphi ⌊Q⌋₊).trans ?_
      apply mul_le_mul_of_nonneg_left _ hCφ.le
      have hP1 : (1 : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast (show 1 ≤ ⌊Q⌋₊ by omega)
      have := Real.log_le_log (by linarith) (Nat.floor_le hQ0.le)
      linarith
    -- S1
    have S1 : 6768 * (Q ^ 5 * L ^ 2) ≤ Real.sqrt x := by
      have h1 := g1 x hx2
      rw [← hLdef, ← hQ5] at h1
      have hq4 : 6768 * K1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
        have h0 : (6768 * K1) ^ 4 ≤ (x : ℝ) := by
          have : 0 ≤ Real.exp Lb + K2 ^ 2 := by positivity
          linarith
        calc 6768 * K1 = ((6768 * K1) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
          _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) h0 (by norm_num)
      have hsq : Real.sqrt (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
      rw [hsq]
      have hx14 : 0 ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by positivity
      calc 6768 * (Q ^ 5 * L ^ 2) ≤ 6768 * (K1 * (x : ℝ) ^ ((1 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = (6768 * K1) * (x : ℝ) ^ ((1 : ℝ) / 4) := by ring
        _ ≤ (x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right hq4 hx14
    -- S2
    have S2 : 720 * (K * (Q ^ 5 * L * ε)) ≤ 1 := by
      have hex : ε = Real.exp (-(c / Real.sqrt 2) * Real.sqrt L) := by
        rw [hεdef]
        congr 1
        rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      have h3 := g3 x hx2
      rw [← hLdef, ← hex] at h3
      have hLp : 0 < L ^ (5 * B + 2) := Real.rpow_pos_of_pos hL0 _
      have h4 : Q ^ 5 * L * ε ≤ K3 / L := by
        have e1 : Q ^ 5 * L = L ^ (5 * B + 2) / L := by
          rw [← hQ5]; field_simp
        rw [e1]
        calc L ^ (5 * B + 2) / L * ε ≤ L ^ (5 * B + 2) / L * (K3 / L ^ (5 * B + 2)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = K3 / L := by field_simp
      have h5 : 720 * (K * (K3 / L)) ≤ 1 := by
        rw [show 720 * (K * (K3 / L)) = 720 * K * K3 / L by ring, div_le_one hL0]
        have : 0 ≤ 6 * Real.exp 8 + (1944 * Cφ) ^ 2 := by positivity
        linarith
      have := mul_le_mul_of_nonneg_left h4 hK
      nlinarith
    -- S3
    have S3 : 648 * (Cφ * (1 + Real.log Q)) ≤ Q := by
      have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ0
      have hsQ2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ0.le
      have hlog : Real.log Q ≤ 2 * Real.sqrt Q := by
        have h := Real.log_le_sub_one_of_pos hsQ
        rw [Real.log_sqrt hQ0.le] at h
        linarith
      have hs1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.2 hQ1
      have hbig : 1944 * Cφ ≤ Real.sqrt Q := by
        rw [show 1944 * Cφ = Real.sqrt ((1944 * Cφ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_le_sqrt
        have : 0 ≤ 6 * Real.exp 8 + 720 * K * K3 := by positivity
        linarith
      have h1 : 1 + Real.log Q ≤ 3 * Real.sqrt Q := by linarith
      calc 648 * (Cφ * (1 + Real.log Q)) ≤ 648 * (Cφ * (3 * Real.sqrt Q)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left h1 hCφ.le
        _ = (1944 * Cφ) * Real.sqrt Q := by ring
        _ ≤ Real.sqrt Q * Real.sqrt Q := mul_le_mul_of_nonneg_right hbig hsQ.le
        _ = Q := by rw [← pow_two, hsQ2]
    exact errMV_le hx1 hLdef hL1 hQ1 hK hε0 hE0 hE hphiQ S1 S2 S3
  -- the singular series condition at `T = L^A`
  have hT : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hsing : Real.exp 8 * L ^ A / Real.sqrt ⌊Q⌋₊ ≤ 1 / 4 := by
    have hL6 : 6 * Real.exp 8 ≤ L := by
      have : 0 ≤ (1944 * Cφ) ^ 2 + 720 * K * K3 := by positivity
      linarith
    exact aux_sing hL0 hL1 hL6 hB hQdef hQ1 (by omega)
  have hcount := card_major_small_le hQ1 hQM hx7 hmaj' hErr hP2 hT hsing
  exact hcount

/-- **Estermann 1938 by his own circle method route**: almost all even numbers are Goldbach
numbers, `E(X) ≪_A X/(log X)^A`, unconditional, from Vinogradov's minor arc bound and the major
arc count, both now PROVED in the lab. -/
theorem estermann_circle_method : LogPowerSaving :=
  estermann_of_majorArcCount majorArcCount_proved

end LeanLab.ExceptionalSet.MVMajor
