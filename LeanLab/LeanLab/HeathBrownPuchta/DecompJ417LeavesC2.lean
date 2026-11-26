import LeanLab.HeathBrownPuchta.SReduction

/-!
# Heath-Brown and Puchta 2002, display 41: the Liu, Liu and Wang input split

P0012 page 26 quotes Liu, Liu and Wang 1999, J. Theor. Nombres Bordeaux 11, display 3.9:
`2X/φ(2X) ≤ 2 e^γ log x` for `x ≥ 9`, `X = Π_{d ≤ x} (2^d - 1)`.  Their proof, page 142,
uses Rosser and Schoenfeld 1962 display 3.42, `d/φ(d) < u(d)` with
`u(d) = e^γ log log d + 2.5064/log log d`, the monotonicity of `u` for `d ≥ 30`, and
`2X ≤ 2^(x²+1)`.  This file states those pieces as leaves and proves
`SReduction.LLW` and the parent `c2_bound` from them.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real

namespace LeanLab.HeathBrownPuchta.DecompJ417LeavesC2

open LeanLab.HeathBrownPuchta.SReduction

/-- Liu, Liu and Wang 1999 page 142, the function `u(d)` defined after display 3.9 from
Rosser and Schoenfeld display 3.42. -/
noncomputable def uRS (t : ℝ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * Real.log (Real.log t) +
    25064 / 10000 / Real.log (Real.log t)

/-- LEAF: Rosser and Schoenfeld 1962 display 3.42, as used by Liu, Liu and Wang page 142.
Class CITED-LEFT. P0012 page 26, reference 13. For every integer `d ≥ 3`,
`d/φ(d) < u(d)`. The RS exception `d = 223092870` still satisfies the bound with 2.5064. -/
theorem rosser_schoenfeld_342 (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) / (Nat.totient d : ℝ) < uRS d := by
  sorry

/-- Helper for the leaves `uRS_mono` and `uRS_endpoint`, PROVED: the harmonic number
`H_127 ≥ 5.4253`, by exact rational arithmetic. -/
theorem harmonic_127_ge : (54253 / 10000 : ℚ) ≤ harmonic 127 := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Helper, PROVED: `γ > 0.573` from `γ > H_127 - log 128` and `log 2 < 0.6931471808`. -/
theorem gamma_gt : (573 / 1000 : ℝ) < eulerMascheroniConstant := by
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 127
  have hH : (54253 / 10000 : ℝ) ≤ (harmonic 127 : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 harmonic_127_ge
    push_cast at this
    exact this
  have hl : Real.log ((127 : ℕ) + 1) = 7 * Real.log 2 := by
    rw [show ((127 : ℕ) : ℝ) + 1 = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  unfold eulerMascheroniSeq at h1
  rw [hl] at h1
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

/-- Helper, PROVED: `e^γ ≥ 1.7735` from the degree 5 Taylor lower bound at `0.573`. -/
theorem exp_gamma_gt : (17735 / 10000 : ℝ) ≤ Real.exp eulerMascheroniConstant := by
  have h := Real.sum_le_exp_of_nonneg (x := (573 / 1000 : ℝ)) (by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := Real.exp_le_exp.2 gamma_gt.le
  linarith


/-- Helper, PROVED: `e^x ≤ 1/(1-x)` for `x < 1`. -/
theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos x
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Helper, PROVED: `log log 30 ≥ 1.19`. -/
theorem loglog30_ge : (119 / 100 : ℝ) ≤ Real.log (Real.log 30) := by
  have h2 := Real.log_two_gt_d9
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have hq : Real.log (32 / 30) ≤ 32 / 30 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at hq
  have h30 : (3399 / 1000 : ℝ) ≤ Real.log 30 := by norm_num at h2; linarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have he1 := Real.exp_one_lt_d9
  have he2 := exp_le_inv_one_sub (x := 19 / 100) (by norm_num)
  have : Real.exp (119 / 100) = Real.exp 1 * Real.exp (19 / 100) := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  have hp := Real.exp_pos (19 / 100)
  norm_num at he1 he2
  nlinarith

/-- LEAF: Liu, Liu and Wang 1999 page 142, after display 3.9: the function `u` increases
for `d ≥ 30`. Class MEDIUM. P0012 page 26, reference 13. Real calculus: `log log t ≥ 1.22`
on `t ≥ 30` and `e^γ s + 2.5064/s` increases for `s² ≥ 2.5064/e^γ`. -/
theorem uRS_mono (a b : ℝ) (ha : 30 ≤ a) (hab : a ≤ b) : uRS a ≤ uRS b := by
  unfold uRS
  have hla : Real.log 30 ≤ Real.log a := Real.log_le_log (by norm_num) ha
  have hl30 : 0 < Real.log 30 := Real.log_pos (by norm_num)
  have hs1 : 119 / 100 ≤ Real.log (Real.log a) :=
    loglog30_ge.trans (Real.log_le_log hl30 hla)
  have hs12 : Real.log (Real.log a) ≤ Real.log (Real.log b) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by linarith) hab)
  set s1 := Real.log (Real.log a)
  set s2 := Real.log (Real.log b)
  set c := Real.exp eulerMascheroniConstant
  have hc := exp_gamma_gt
  have hs1p : 0 < s1 := by linarith
  have hs2p : 0 < s2 := by linarith
  have key : 25064 / 10000 / s1 - 25064 / 10000 / s2 =
      25064 / 10000 * (s2 - s1) / (s1 * s2) := by
    field_simp
  have hprod : (119 / 100) * (119 / 100) ≤ s1 * s2 := by nlinarith
  have h3 : 25064 / 10000 * (s2 - s1) / (s1 * s2) ≤ c * (s2 - s1) := by
    rw [div_le_iff₀ (by positivity)]
    have hd : 0 ≤ s2 - s1 := by linarith
    nlinarith [mul_nonneg hd (by linarith : (0 : ℝ) ≤ s1 * s2 - 119 / 100 * (119 / 100)),
      mul_nonneg hd (by linarith : (0 : ℝ) ≤ c - 17735 / 10000)]
  linarith

/-- Liu, Liu and Wang 1999 page 142, last display: `2X ≤ 2^(x²+1)`, PROVED here.
P0012 page 26, reference 13. Each factor `2^e - 1` with `e ≤ n` is below
`2^n`, so the product of `n` factors is at most `2^(n²)`. -/
theorem two_mprod_le (n : ℕ) : 2 * (mprod n : ℝ) ≤ 2 ^ (n ^ 2 + 1) := by
  have h : mprod n ≤ 2 ^ (n ^ 2) := by
    unfold mprod
    calc ∏ e ∈ Finset.Icc 1 n, (2 ^ e - 1) ≤ ∏ _e ∈ Finset.Icc 1 n, 2 ^ n := by
          apply Finset.prod_le_prod'
          intro e he
          simp only [Finset.mem_Icc] at he
          exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) he.2)
      _ = 2 ^ (n ^ 2) := by
          rw [Finset.prod_const, Nat.card_Icc, ← pow_mul]; congr 1; simp [sq]
  have h' : (mprod n : ℝ) ≤ 2 ^ (n ^ 2) := by exact_mod_cast h
  rw [pow_succ]; linarith

/-- LEAF: Liu, Liu and Wang 1999 page 142, the scalar step closing display 3.9:
`u(2^(x²+1)) ≤ 2 e^γ log x` for integers `x ≥ 9`. Class MEDIUM. P0012 page 26, reference 13.
Needs a lower bound `e^γ ≥ 1.76` and explicit logarithms; at `x = 9` the margin is about
`0.01`. -/
theorem uRS_endpoint (n : ℕ) (hn : 9 ≤ n) :
    uRS (2 ^ (n ^ 2 + 1)) ≤ 2 * Real.exp Real.eulerMascheroniConstant * Real.log n := by
  unfold uRS
  have hy1 := Real.log_two_gt_d9
  have hy2 := Real.log_two_lt_d9
  norm_num at hy1 hy2
  set y := Real.log 2 with hy
  have hL : Real.log ((2 : ℝ) ^ (n ^ 2 + 1)) = ((n : ℝ) ^ 2 + 1) * y := by
    rw [Real.log_pow]; push_cast; ring
  rw [hL]
  have hn9 : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (81 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hypos : 0 < y := by linarith
  have hLpos : 0 < ((n : ℝ) ^ 2 + 1) * y := by positivity
  have hL82 : 82 * y ≤ ((n : ℝ) ^ 2 + 1) * y := by nlinarith
  -- s ≥ 4.03
  have hs : (403 / 100 : ℝ) ≤ Real.log (((n : ℝ) ^ 2 + 1) * y) := by
    have h64 : Real.log 64 = 6 * y := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow, hy]; norm_num
    have hq := Real.log_le_sub_one_of_pos (x := 64 / (((n : ℝ) ^ 2 + 1) * y)) (by positivity)
    rw [Real.log_div (by norm_num) hLpos.ne'] at hq
    have hq2 : 64 / (((n : ℝ) ^ 2 + 1) * y) ≤ 64 / (82 * y) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hL82
    have hq3 : 64 / (82 * y) ≤ 64 / (82 * (6931471803 / 10000000000)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    norm_num at hq3
    linarith
  -- -log y ≥ 0.3661
  have hly : Real.log y ≤ -(3661 / 10000) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 1 / (2 * y ^ 2)) (by positivity)
    rw [one_div, inv_inv, Real.log_inv, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h
    push_cast at h
    nlinarith
  -- log (n^2+1) ≤ 2 log n + 1/81
  have hln : Real.log ((n : ℝ) ^ 2 + 1) ≤ 2 * Real.log n + 1 / 81 := by
    have hq := Real.log_le_sub_one_of_pos (x := ((n : ℝ) ^ 2 + 1) / (n : ℝ) ^ 2) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hq
    have : ((n : ℝ) ^ 2 + 1) / (n : ℝ) ^ 2 - 1 = 1 / (n : ℝ) ^ 2 := by field_simp; ring
    rw [this] at hq
    have : 1 / (n : ℝ) ^ 2 ≤ 1 / 81 := one_div_le_one_div_of_le (by norm_num) hn2
    push_cast at hq
    linarith
  rw [Real.log_mul (by positivity) hypos.ne'] at hs ⊢
  set s := Real.log ((n : ℝ) ^ 2 + 1) + Real.log y
  set c := Real.exp eulerMascheroniConstant
  have hc := exp_gamma_gt
  have hd : (3537 / 10000 : ℝ) ≤ 2 * Real.log n - s := by linarith
  have hspos : 0 < s := by linarith
  have hK : 25064 / 10000 / s ≤ c * (2 * Real.log n - s) := by
    rw [div_le_iff₀ hspos]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - 17735 / 10000)
        (by linarith : (0:ℝ) ≤ 2 * Real.log n - s - 3537 / 10000),
      mul_nonneg (by linarith : (0:ℝ) ≤ s - 403 / 100)
        (by linarith : (0:ℝ) ≤ 2 * Real.log n - s - 3537 / 10000)]
  nlinarith

/-- Liu, Liu and Wang display 3.9 in the form `SReduction.LLW`, from the four leaves. -/
theorem llw_of_leaves : LLW := by
  intro n hn
  set X := mprod n with hX
  have hX0 : X ≠ 0 := mprod_ne_zero n
  have hodd : ¬ 2 ∣ X := mprod_odd n
  have h15 : 15 ∣ X := by
    have := dvd_mprod (n := n) (e := 4) (by norm_num) (by omega)
    simpa using this
  have hX15 : 15 ≤ X := Nat.le_of_dvd (Nat.pos_of_ne_zero hX0) h15
  have hcop : Nat.Coprime 2 X := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have htot : Nat.totient (2 * X) = Nat.totient X := by
    rw [Nat.totient_mul hcop]; simp
  have hphi0 : (0 : ℝ) < Nat.totient X := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hX0)
  have h1 := rosser_schoenfeld_342 (2 * X) (by omega)
  rw [htot] at h1
  have h2 : uRS ((2 * X : ℕ) : ℝ) ≤ uRS (2 ^ (n ^ 2 + 1)) := by
    apply uRS_mono
    · have : (30 : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by exact_mod_cast (by omega : 30 ≤ 2 * X)
      exact this
    · push_cast; exact two_mprod_le n
  have h3 := uRS_endpoint n hn
  have h4 : ((2 * X : ℕ) : ℝ) / (Nat.totient X : ℝ) =
      2 * ((X : ℝ) / (Nat.totient X : ℝ)) := by push_cast; ring
  rw [h4] at h1
  show (X : ℝ) / (Nat.totient X : ℝ) ≤ _
  linarith

/-- P0012 page 26, display 41, `C₂ ≤ 2.2141`, the exact parent statement
`DecompJ417.c2_bound`, from the leaves of this file through `SReduction.C2_le_at_20`. -/
theorem c2_bound_of_leaves : LeanLab.HeathBrownPuchta.Lemma8Const.C2 ≤ 22141 / 10000 :=
  C2_le_at_20 llw_of_leaves

end LeanLab.HeathBrownPuchta.DecompJ417LeavesC2
