import LeanLab.PNTPort.Vinogradov.Final
import LeanLab.Zhan1991.SPLIT_theorem2_1122

/-!
P0068 Zhan 1991, page 263, lines 1 and 2: "As for `N L⁻¹ ≤ A ≤ N`, (1.3) follows immediately from
Vinogradov's classical result". PROVED by wiring to the lab's unconditional Vinogradov minor arc
bound `LeanLab.PNTPort.Vinogradov.vinogradov_minor`, Vaughan's form, PROVED in PNTPort. It closes
the LEAF `large_range_leaf` of SPLIT_theorem2_1122 by a separate proof, without editing that file.
burst-20261122, session S80. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real Filter Asymptotics
open scoped ArithmeticFunction.vonMangoldt

/-- The two phase functions agree, `e(x) = exp(2πix)`. -/
theorem ee_eq_vin (x : ℝ) : ee x = LeanLab.PNTPort.LargeSieve.e x := by
  unfold ee LeanLab.PNTPort.LargeSieve.e
  congr 1; push_cast; ring

/-- `|e(x)| = 1`. -/
theorem ee_norm_v (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Page 260, `S(α; N, A) = S(α; N) - S(α; ⌊N - A⌋)` with PNTPort's full sum. PROVED. -/
theorem sexp_eq_diff (N : ℕ) (A α : ℝ) (hA0 : 0 ≤ A) (hAN : A ≤ N) :
    Sexp α N A = LeanLab.PNTPort.Vinogradov.S N α -
      LeanLab.PNTPort.Vinogradov.S ⌊(N : ℝ) - A⌋₊ α := by
  unfold Sexp LeanLab.PNTPort.Vinogradov.S shortWin
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n : ℕ => (N : ℝ) - A < n)]
  have hset : (Finset.Icc 1 N).filter (fun n : ℕ => ¬ ((N : ℝ) - A < n)) =
      Finset.Icc 1 ⌊(N : ℝ) - A⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩
      have h3 : (n : ℝ) ≤ N - A := (Nat.le_floor_iff (by linarith)).mp h2
      refine ⟨⟨h1, ?_⟩, h3⟩
      have : (n : ℝ) ≤ N := by linarith
      exact_mod_cast this
  rw [hset]
  simp only [ee_eq_vin]
  ring

/-- The Chebyshev bound for PNTPort's full sum. PROVED. -/
theorem S_trivial (M : ℕ) (α : ℝ) :
    ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤ (Real.log 4 + 4) * M := by
  have hb : ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤ Chebyshev.psi M := by
    unfold LeanLab.PNTPort.Vinogradov.S
    calc _ ≤ ∑ n ∈ Finset.Icc 1 M, ‖(Λ n : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * α)‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 M, Λ n := by
          apply Finset.sum_congr rfl
          intro n _
          rw [norm_mul, ← ee_eq_vin, ee_norm_v, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ ∑ n ∈ Finset.Ioc 0 M, Λ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            have hh := Finset.mem_Icc.mp hn
            exact Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩
          · intro n _ _
            exact ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by simp [Chebyshev.psi]
  exact hb.trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _))

/-- Vinogradov's bound at any `M ≤ N`, with the trivial bound when `M < q`. PROVED. -/
theorem S_bound_M (N M q : ℕ) (a : ℤ) (α : ℝ) (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (hMN : M ≤ N) :
    ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤
      300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        (1 + Real.log N) ^ 4 + (Real.log 4 + 4) * q := by
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hl4 : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  by_cases hqM : q ≤ M
  · have hv := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq hcop hα hqM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans hq hqM
    have h1 : (M : ℝ) / Real.sqrt q ≤ N / Real.sqrt q :=
      div_le_div_of_nonneg_right hMN' (Real.sqrt_nonneg _)
    have h2 : (M : ℝ) ^ ((4 : ℝ) / 5) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) :=
      Real.rpow_le_rpow (by linarith) hMN' (by norm_num)
    have h3 : Real.sqrt (M * q) ≤ Real.sqrt (N * q) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hMN' hq0.le)
    have h4 : (1 + Real.log M) ^ 4 ≤ (1 + Real.log N) ^ 4 := by
      have := Real.log_le_log (by linarith) hMN'
      have := Real.log_nonneg hM1
      gcongr
    have h5 : 0 ≤ (M : ℝ) / Real.sqrt q + (M : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (M * q) := by
      have := Real.sqrt_nonneg ((M : ℝ) * q)
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ M) ((4 : ℝ) / 5)
      have := div_nonneg (by linarith : (0 : ℝ) ≤ M) (Real.sqrt_nonneg (q : ℝ))
      linarith
    have h6 : 0 ≤ (1 + Real.log M) ^ 4 := by have := Real.log_nonneg hM1; positivity
    calc ‖LeanLab.PNTPort.Vinogradov.S M α‖
        ≤ 300 * ((M : ℝ) / Real.sqrt q + (M : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (M * q)) *
          (1 + Real.log M) ^ 4 := hv
      _ ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
          (1 + Real.log N) ^ 4 := by
          apply mul_le_mul _ h4 h6 (by linarith)
          linarith
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hl4 hq0.le)
  · push Not at hqM
    have hMq : (M : ℝ) ≤ q := by exact_mod_cast hqM.le
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hfirst : 0 ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt (N * q)) * (1 + Real.log N) ^ 4 := by
      have := Real.sqrt_nonneg ((N : ℝ) * q)
      have := Real.rpow_nonneg hN0 ((4 : ℝ) / 5)
      have := div_nonneg hN0 (Real.sqrt_nonneg (q : ℝ))
      have h0 : 0 ≤ (1 + Real.log N) ^ 4 := by
        rcases Nat.eq_zero_or_pos N with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ N := by exact_mod_cast h
          have := Real.log_nonneg this; positivity
      positivity
    calc ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤ (Real.log 4 + 4) * M := S_trivial M α
      _ ≤ (Real.log 4 + 4) * q := mul_le_mul_of_nonneg_left hMq hl4
      _ ≤ _ := le_add_of_nonneg_left hfirst

set_option maxHeartbeats 1600000 in
/-- Page 263, (1.3) on `N L⁻¹ ≤ A ≤ N` from Vinogradov: with `c₁, c₂ ≥ 2B + 12`,
`‖S(α; N, A)‖ ≤ 2 · 300 (N q^{-1/2} + N^{4/5} + (Nq)^{1/2}) (1 + L)^4 + 2 (log 4 + 4) q ≪ N L^{-B-1}
≤ A L^{-B}`, using `L^{c₂} ≤ q ≤ τ ≤ N L^{-c₁}`. PROVED. -/
theorem largeRange_of_vinogradov : LargeRange := by
  intro B hB
  refine ⟨2 * B + 12, fun c1 hc1 => ⟨2 * B + 12, fun c2 hc2 => ?_⟩⟩
  have hasy := (isLittleO_log_rpow_rpow_atTop (B + 5) (by norm_num : (0 : ℝ) < 1 / 5)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hasy.and (eventually_ge_atTop (Real.exp 1)))
  refine ⟨2 * (300 * 16 * 3 + 8), X0, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  obtain ⟨hb, he⟩ := hX0 N hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 1) he
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hP15 : 0 < (N : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hN0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLpos.le _),
    abs_of_nonneg hP15.le, one_mul] at hb
  have hLp : ∀ u v : ℝ, u ≤ v → L ^ u ≤ L ^ v := fun u v h =>
    Real.rpow_le_rpow_of_exponent_le hL1 h
  have hA0 : 0 < A := lt_of_lt_of_le (div_pos hN0 hLpos) hlo
  have hNA : (N : ℝ) ≤ A * L := by rwa [div_le_iff₀ hLpos] at hlo
  obtain ⟨hαe, hgcd, hlam, hq1, hqτ⟩ := hcond
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hLc1 : 0 < L ^ (-c1) := Real.rpow_pos_of_pos hLpos _
  have hLc1le : L ^ (-c1) ≤ 1 := by
    have := hLp (-c1) 0 (by linarith); simpa using this
  set τ := A ^ 2 / N * L ^ (-c1) with hτ
  have hτN : τ ≤ N * L ^ (-c1) := by
    rw [hτ]
    apply mul_le_mul_of_nonneg_right _ hLc1.le
    rw [div_le_iff₀ hN0]; nlinarith
  have hqN : q ≤ N := by
    have : (q : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
    rw [hαe, add_sub_cancel_left]
    refine hlam.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_left hqτ hq0.le
  have hcop : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hdiff := sexp_eq_diff N A α hA0.le hhi
  have hbN := S_bound_M N N q a α hq1 hcop hα le_rfl
  have hbM := S_bound_M N ⌊(N : ℝ) - A⌋₊ q a α hq1 hcop hα (by
    apply Nat.floor_le_of_le; linarith)
  -- the pieces
  set P := (N : ℝ) * L ^ (-B - 1) with hP
  have hpow : ∀ u : ℝ, (N : ℝ) * L ^ (4 : ℝ) * L ^ u = N * L ^ (u + 4) := by
    intro u; rw [mul_assoc, ← Real.rpow_add hLpos]; ring_nf
  have hs1 : (N : ℝ) / Real.sqrt q ≤ N * L ^ (-(c2 / 2)) := by
    have hsq : L ^ (c2 / 2) ≤ Real.sqrt q := by
      rw [show L ^ (c2 / 2) = Real.sqrt (L ^ c2) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLpos.le]; ring_nf]
      exact Real.sqrt_le_sqrt hq
    rw [Real.rpow_neg hLpos.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hN0.le (Real.rpow_pos_of_pos hLpos _) hsq
  have hs2 : Real.sqrt (N * q) ≤ N * L ^ (-(c1 / 2)) := by
    have h1 : (N : ℝ) * q ≤ (N * L ^ (-(c1 / 2))) ^ 2 := by
      have hsq2 : (L ^ (-(c1 / 2))) ^ 2 = L ^ (-c1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
      have e : (N * L ^ (-(c1 / 2))) ^ 2 = N * (N * L ^ (-c1)) := by
        rw [mul_pow, hsq2]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (hqτ.trans hτN) hN0.le
    rw [Real.sqrt_le_left (by positivity)]
    exact h1
  have hs3 : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ N * L ^ (-(B + 5)) := by
    have e : (N : ℝ) = N ^ ((4 : ℝ) / 5) * N ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    rw [Real.rpow_neg hLpos.le]
    have hLB : 0 < L ^ (B + 5) := Real.rpow_pos_of_pos hLpos _
    rw [← div_eq_mul_inv, le_div_iff₀ hLB]
    calc (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (B + 5) ≤ N ^ ((4 : ℝ) / 5) * N ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hN0.le _)
      _ = N := e.symm
  have hs4 : (q : ℝ) ≤ N * L ^ (-c1) := hqτ.trans hτN
  have hlogs : (1 + L) ^ 4 ≤ 16 * L ^ (4 : ℝ) := by
    rw [show L ^ (4 : ℝ) = L ^ (4 : ℕ) by norm_cast]
    have : 1 + L ≤ 2 * L := by linarith
    calc (1 + L) ^ 4 ≤ (2 * L) ^ 4 := by gcongr
      _ = 16 * L ^ 4 := by ring
  have hL4 : 0 ≤ L ^ (4 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hbig : 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
      (1 + L) ^ 4 + (Real.log 4 + 4) * q ≤ (300 * 16 * 3 + 8) * P := by
    have hsum0 : 0 ≤ (N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q) := by
      have := Real.sqrt_nonneg ((N : ℝ) * q)
      have := Real.rpow_nonneg hN0.le ((4 : ℝ) / 5)
      have := div_nonneg hN0.le (Real.sqrt_nonneg (q : ℝ))
      linarith
    have hl4 : Real.log 4 + 4 ≤ 8 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have t1 : (N : ℝ) * L ^ (-(c2 / 2)) * L ^ (4 : ℝ) ≤ P := by
      rw [mul_assoc, ← Real.rpow_add hLpos, hP]
      exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have t2 : (N : ℝ) * L ^ (-(B + 5)) * L ^ (4 : ℝ) ≤ P := by
      rw [mul_assoc, ← Real.rpow_add hLpos, hP]
      exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have t3 : (N : ℝ) * L ^ (-(c1 / 2)) * L ^ (4 : ℝ) ≤ P := by
      rw [mul_assoc, ← Real.rpow_add hLpos, hP]
      exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have t4 : (N : ℝ) * L ^ (-c1) ≤ P := by
      rw [hP]; exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have hA1 : 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        (1 + L) ^ 4 ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt (N * q)) * (16 * L ^ (4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogs (by linarith)
    have hA2 : ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        L ^ (4 : ℝ) ≤ 3 * P := by
      have := mul_le_mul_of_nonneg_right (add_le_add (add_le_add hs1 hs3) hs2) hL4
      nlinarith
    have hA3 : (Real.log 4 + 4) * q ≤ 8 * P := by
      have hq0' : (0 : ℝ) ≤ q := hq0.le
      calc (Real.log 4 + 4) * q ≤ 8 * q := mul_le_mul_of_nonneg_right hl4 hq0'
        _ ≤ 8 * P := by linarith
    nlinarith
  have hPA : P ≤ A * L ^ (-B) := by
    rw [hP, show (-B - 1 : ℝ) = -B + (-1) by ring, Real.rpow_add hLpos, Real.rpow_neg_one]
    have hLB0 : 0 < L ^ (-B) := Real.rpow_pos_of_pos hLpos _
    calc (N : ℝ) * (L ^ (-B) * L⁻¹) = N / L * L ^ (-B) := by ring
      _ ≤ A * L ^ (-B) := mul_le_mul_of_nonneg_right hlo hLB0.le
  rw [hdiff]
  calc ‖LeanLab.PNTPort.Vinogradov.S N α - LeanLab.PNTPort.Vinogradov.S ⌊(N : ℝ) - A⌋₊ α‖
      ≤ ‖LeanLab.PNTPort.Vinogradov.S N α‖ +
        ‖LeanLab.PNTPort.Vinogradov.S ⌊(N : ℝ) - A⌋₊ α‖ := norm_sub_le _ _
    _ ≤ 2 * ((300 * 16 * 3 + 8) * P) := by linarith
    _ ≤ 2 * (300 * 16 * 3 + 8) * (A * L ^ (-B)) := by nlinarith
    _ = _ := by ring

end LeanLab.Zhan1991
