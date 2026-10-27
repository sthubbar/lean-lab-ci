/-
Kaniecki 1995, P0022: the constants inside the proof of Lemma 4, pp. 364-367, and the
elementary computations of Section 3, pp. 371-373.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Kaniecki1995.ExpBounds
import LeanLab.Kaniecki1995.Statements
import LeanLab.Kaniecki1995.Numerics

namespace LeanLab.Kaniecki1995
open Real Finset MeasureTheory

/-! ### Constants inside the proofs of Lemmas 3 and 4 -/

/-- p. 364: `0 < (1-σ)/((1-σ)² + t²) < 1/392.125` for `1/2 ≤ σ ≤ 3/4`, `t ≥ 14`. -/
theorem c392 {σ t : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 4) (ht : 14 ≤ t) :
    0 < (1 - σ) / ((1 - σ) ^ 2 + t ^ 2) ∧ (1 - σ) / ((1 - σ) ^ 2 + t ^ 2) < 1 / 392.125 := by
  have hd : 0 < (1 - σ) ^ 2 + t ^ 2 := by nlinarith
  refine ⟨div_pos (by linarith) hd, ?_⟩
  rw [div_lt_div_iff₀ hd (by norm_num)]
  nlinarith

/-- p. 365: on `0 < t ≤ 14`, `σ ≤ 3/4`, one has `|σ + it|/2 < 7.02`, so `δ|σ+it|/2 < 7.02/T`. -/
theorem c702 {σ t : ℝ} (h0 : 0 ≤ σ) (h2 : σ ≤ 3 / 4) (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    √(σ ^ 2 + t ^ 2) / 2 < 7.02 := by
  have : √(σ ^ 2 + t ^ 2) < 14.04 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  linarith

/-- p. 365: `δ = log(1 + 1/T) ≤ 1/T`. -/
theorem delta_le {T : ℝ} (hT : 0 < T) : Real.log (1 + 1 / T) ≤ 1 / T := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / T by positivity)
  linarith

/-- p. 365: the first part of (8) uses `14 · 6² = 504`. -/
theorem c504 : (14 : ℝ) * 6 ^ 2 = 504 := by norm_num

/-- p. 368, (16): `∫_{14}^∞ t^{-4} dt = 1/8232`. -/
theorem c8232 : ∫ t in Set.Ioi (14 : ℝ), t ^ (-4 : ℝ) = 1 / 8232 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  rw [show (-4 : ℝ) + 1 = -3 by norm_num, Real.rpow_neg (by norm_num)]
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The series `Σ_{n ≥ 1} 1/(4 (3/4 + n)²)` of p. 367 is larger than `0.1909`. -/
theorem series_ge :
    (0.1909 : ℝ) ≤ ∑' n : ℕ, 1 / (4 * ((n : ℝ) + 1 + 3 / 4) ^ 2) := by
  set f : ℕ → ℝ := fun n => 1 / (4 * ((n : ℝ) + 1 + 3 / 4) ^ 2) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le hf0 (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2)
    · intro n; simp only [hf]
      apply one_div_le_one_div_of_le (by positivity)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    · exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two) |>.congr
        (fun n => by push_cast; ring)
  set g : ℕ → ℝ := fun n => 1 / (4 * ((n : ℝ) + 1 + 3 / 4)) with hg
  have tele : ∀ n, g n - g (n + 1) ≤ f n := by
    intro n; simp only [hf, hg]; push_cast
    have h1 : (0 : ℝ) < (n : ℝ) + 1 + 3 / 4 := by positivity
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((n : ℝ) + 1 + 3 / 4)]
  have hK : ∀ K : ℕ, (∑ n ∈ range 30, f n) + g 30 - g (30 + K) ≤ ∑ n ∈ range (30 + K), f n := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [show 30 + (K + 1) = (30 + K) + 1 by ring, Finset.sum_range_succ f (30 + K)]
      have := tele (30 + K)
      linarith
  have h30 : (∑ n ∈ range 30, f n) + g 30 - g (30 + 10 ^ 7) ≤ ∑' n, f n :=
    (hK (10 ^ 7)).trans (hsum.sum_le_tsum _ (fun i _ => hf0 i))
  have hval : (0.1909 : ℝ) ≤ (∑ n ∈ range 30, f n) + g 30 - g (30 + 10 ^ 7) := by
    simp only [hf, hg]
    norm_num [Finset.sum_range_succ]
  exact hval.trans h30

/-- p. 367: with `k₁ = Σ_γ (1/2)/(1/4+γ²) ≤ 0.0231` (Davenport p. 82; true value
`0.0230957...`), `2k₁ - 2z - Σ_{n≥1} 1/(4(3/4+n)²) < -0.144` for every `z ≥ 0`,
which is the constant `-0.144` of (11) and of `f₂`. -/
theorem c0144 {k1 z : ℝ} (hk : k1 ≤ 0.0231) (hz : 0 ≤ z) :
    2 * k1 - 2 * z - ∑' n : ℕ, 1 / (4 * ((n : ℝ) + 1 + 3 / 4) ^ 2) < -0.144 := by
  have := series_ge
  linarith

/-- p. 367: `1/(2σ-1)² = log² T / (4a²c²)` for `σ = 1/2 + ac/log T`. -/
theorem c_first_term {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < Real.log T) :
    1 / (2 * sig a c T - 1) ^ 2 = Real.log T ^ 2 / (4 * a ^ 2 * c ^ 2) := by
  unfold sig
  field_simp
  ring

/-! ### Exponential bounds used in Section 3 -/

/-- Upper bound `exp (n + r) ≤ B` via Taylor, packaged. -/
theorem expU {x B : ℝ} (n : ℕ) (r : ℝ) (hx : x = n + r) (hr : |r| ≤ 1)
    (h : (2.7182818286 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) +
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14))) ≤ B) : Real.exp x ≤ B := by
  rw [hx]; exact exp_add_nat_le hr h

/-- Lower bound `B ≤ exp (n + r)` via Taylor, packaged. -/
theorem expL {x B : ℝ} (n : ℕ) (r : ℝ) (hx : x = n + r) (hr : |r| ≤ 1)
    (hpos : 0 ≤ (∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))
    (h : B ≤ (2.7182818283 : ℝ) ^ n * ((∑ m ∈ range 14, r ^ m / m.factorial) -
      |r| ^ 14 * (((14 : ℕ).succ : ℝ) / ((14 : ℕ).factorial * 14)))) : B ≤ Real.exp x := by
  rw [hx]; exact le_exp_add_nat hr hpos h

theorem e2016 : (5.69e8 : ℝ) ≤ Real.exp 20.16 :=
  expL 20 0.16 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e1932 : (2.45e8 : ℝ) ≤ Real.exp 19.32 :=
  expL 19 0.32 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e69365 : Real.exp 6.9365 ≤ 1029.2 :=
  expU 6 0.9365 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e30 : (1.0686e13 : ℝ) ≤ Real.exp 30 :=
  expL 30 0 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e2900155 : (558 * 84000 ^ 2 : ℝ) ≤ Real.exp 29.00155 :=
  expL 29 0.00155 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e5201727 : Real.exp 5.20172694 ≤ 181.58558 :=
  expU 5 0.20172694 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e11503 : Real.exp 11.503 ≤ 99012.37 :=
  expU 11 0.503 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e279707 : Real.exp 27.9707 ≤ 1.4045e12 :=
  expU 27 0.9707 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e2727755 : Real.exp 27.27755 ≤ 7.0225e11 :=
  expU 27 0.27755 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e2727756 : (7.0225e11 : ℝ) ≤ Real.exp 27.27756 :=
  expL 27 0.27756 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e269539 : (72 * 84000 ^ 2 : ℝ) ≤ Real.exp 26.9539 :=
  expL 26 0.9539 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e52017 : Real.exp 5.2017 ≤ 181.6 :=
  expU 5 0.2017 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e104832 : Real.exp 10.4832 ≤ 35720 :=
  expU 10 0.4832 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e54128 : Real.exp 5.4128 ≤ 224.3 :=
  expU 5 0.4128 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e520505 : Real.exp 5.20505 ≤ 182.22 :=
  expU 5 0.20505 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e104 : Real.exp 10.4 ≤ 32900 :=
  expU 10 0.4 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e40 : (2.35e17 : ℝ) ≤ Real.exp 40 :=
  expL 40 0 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e3925 : Real.exp 39.25 ≤ 1.1119e17 :=
  expU 39 0.25 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e45447 : (5.46e19 : ℝ) ≤ Real.exp 45.447 :=
  expL 45 0.447 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e451825 : (4.1926e19 : ℝ) ≤ Real.exp 45.1825 :=
  expL 45 0.1825 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e796906 : Real.exp 7.96906 ≤ 2890.2 :=
  expU 7 0.96906 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e534576 : Real.exp 5.34576 ≤ 209.72 :=
  expU 5 0.34576 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e520348 : Real.exp 5.20348 ≤ 181.905 :=
  expU 5 0.20348 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
theorem e5201620 : Real.exp 5.2016202 ≤ 181.5662 :=
  expU 5 0.2016202 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-! ### Helpers -/

theorem sqrt_c_le : √(1 + 1 / 16597 : ℝ) ≤ 1.0000302 :=
  sqrt_le_of le_rfl (by norm_num) (by norm_num)

theorem inv4pi_le : 1 / (4 * π) ≤ 1 / (4 * 3.14159265) :=
  one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d20])

theorem gL6_exp (L : ℝ) :
    gL6 (Real.exp L) = 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * Real.exp (L / 2) * L ^ 2 := by
  unfold gL6
  rw [Real.log_exp, Real.sqrt_mul (by norm_num)]
  have : √(Real.exp L) = Real.exp (L / 2) := by
    rw [show Real.exp L = Real.exp (L / 2) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  rw [this]; ring

theorem gL6_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : gL6 x ≤ gL6 y := by
  unfold gL6
  have h1 : 0 ≤ Real.log x := Real.log_nonneg hx
  apply mul_le_mul _ (pow_le_pow_left₀ h1 (Real.log_le_log (by linarith) hxy) 2) (sq_nonneg _)
    (by have := Real.pi_pos; positivity)
  apply mul_le_mul_of_nonneg_left _ (by have := Real.pi_pos; positivity)
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem gL6_nonneg {x : ℝ} : 0 ≤ gL6 x := by
  unfold gL6; have := Real.pi_pos; positivity

/-- `L / M ≤ L₀ / (L₀ - k)` when `M ≥ L - k`, `L ≥ L₀ > k ≥ 0`. -/
theorem ratio_le {L L0 k M : ℝ} (hk : 0 ≤ k) (hL0 : k < L0) (hL : L0 ≤ L) (hM : L - k ≤ M) :
    L / M ≤ L0 / (L0 - k) := by
  have h1 : 0 < L0 - k := by linarith
  have h2 : 0 < L - k := by linarith
  calc L / M ≤ L / (L - k) := div_le_div_of_nonneg_left (by linarith) h2 hM
    _ ≤ L0 / (L0 - k) := by
        rw [div_le_div_iff₀ h2 h1]; nlinarith

/-- The right side of (25): `4K e^{2ac (log x)/(log T)} log² T`, with `L = log x`, `M = log T`. -/
noncomputable def rhs25 (K L M : ℝ) : ℝ := 4 * K * Real.exp (2 * (aK * cK) * (L / M)) * M ^ 2

theorem ac2 : 2 * (aK * cK) = 5.199931001 := by rw [acK_eq]; norm_num

/-- Bound `rhs25` from a bound on `L / M` and on `M`. -/
theorem rhs25_le {K L M q B Mhi : ℝ} (hK : 0 ≤ K) (hM0 : 0 ≤ M) (hMhi : M ≤ Mhi) (hq : L / M ≤ q)
    (hB : Real.exp (5.199931001 * q) ≤ B) : rhs25 K L M ≤ 4 * K * B * Mhi ^ 2 := by
  unfold rhs25
  rw [ac2]
  have hE : Real.exp (5.199931001 * (L / M)) ≤ B :=
    (Real.exp_le_exp.2 (by nlinarith)).trans hB
  have hB0 : 0 ≤ B := (Real.exp_pos _).le.trans hE
  apply mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity))
    (pow_le_pow_left₀ hM0 hMhi 2) (sq_nonneg _) (by positivity)

/-! ### (25) from (23) and (24), p. 372: pure algebra -/

/-- From `x^{2(1-σ)}/(2T²) ≤ U < K log² T / T` with `T = 2x/h`, `σ = 1/2 + ac/log T`,
one gets `h < 4K e^{2ac log x / log T} log² T`, which is (25). -/
theorem eq25 {x h K U : ℝ} (hx : 1 < x) (hh : 0 < h) (hT : 1 < 2 * x / h)
    (hlow : x ^ (2 * (1 - sig aK cK (2 * x / h))) / (2 * (2 * x / h) ^ 2) ≤ U)
    (hup : U < K * Real.log (2 * x / h) ^ 2 / (2 * x / h)) :
    h < rhs25 K (Real.log x) (Real.log (2 * x / h)) := by
  set T := 2 * x / h with hTdef
  set M := Real.log T with hMdef
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := Real.log_pos hT
  have hTh : T * h = 2 * x := by rw [hTdef]; field_simp
  set E := 2 * (aK * cK) * (Real.log x / M) with hE
  have hpow : x ^ (2 * (1 - sig aK cK T)) = x * Real.exp (-E) := by
    rw [Real.rpow_def_of_pos hx0, sig, hE, ← Real.exp_log hx0]
    rw [Real.log_exp, ← Real.exp_add]
    congr 1
    rw [← hMdef]
    field_simp
    ring
  rw [hpow] at hlow
  have key : x * Real.exp (-E) / (2 * T ^ 2) < K * M ^ 2 / T := lt_of_le_of_lt hlow hup
  rw [div_lt_div_iff₀ (by positivity) hT0] at key
  -- x e^{-E} T < K M² 2T², so x e^{-E} < 2 K M² T
  have k2 : x * Real.exp (-E) < 2 * K * M ^ 2 * T := by
    have : x * Real.exp (-E) * T < (2 * K * M ^ 2 * T) * T := by nlinarith
    exact lt_of_mul_lt_mul_right this hT0.le
  have k3 : x * Real.exp (-E) * h < 4 * K * M ^ 2 * x := by
    have := mul_lt_mul_of_pos_right k2 hh
    calc x * Real.exp (-E) * h < 2 * K * M ^ 2 * T * h := this
      _ = 4 * K * M ^ 2 * x := by rw [mul_assoc (2 * K * M ^ 2), hTh]; ring
  have k4 : Real.exp (-E) * h < 4 * K * M ^ 2 := by
    have : x * (Real.exp (-E) * h) < x * (4 * K * M ^ 2) := by linarith
    exact lt_of_mul_lt_mul_left this hx0.le
  have hEE : Real.exp E * Real.exp (-E) = 1 := by rw [← Real.exp_add]; simp
  unfold rhs25
  rw [← hE]
  calc h = Real.exp E * (Real.exp (-E) * h) := by rw [← mul_assoc, hEE, one_mul]
    _ < Real.exp E * (4 * K * M ^ 2) := mul_lt_mul_of_pos_left k4 (Real.exp_pos _)
    _ = 4 * K * Real.exp E * M ^ 2 := by ring


/-! ### The printed computations of Section 3, pp. 371-373 -/

theorem kappa_le : 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) ≤ 1 / (4 * 3.14159265) * 1.0000302 :=
  mul_le_mul inv4pi_le sqrt_c_le (Real.sqrt_nonneg _) (by norm_num)

/-- p. 371: for `x ≤ e^{78}`, Lemma 6 gives `λ(x) < 4.1926 · 10^{19}`. -/
theorem p371_lam_e78 : gL6 (Real.exp 78) < 4.1926e19 := by
  rw [gL6_exp]
  have h39 : Real.exp (78 / 2) ≤ (2.7182818286 : ℝ) ^ 39 := by
    rw [show (78 : ℝ) / 2 = ((39 : ℕ) : ℝ) by norm_num]; exact exp_nat_le 39
  calc 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * Real.exp (78 / 2) * 78 ^ 2
      ≤ 1 / (4 * 3.14159265) * 1.0000302 * (2.7182818286 : ℝ) ^ 39 * 78 ^ 2 := by
        gcongr
        all_goals first | linarith [Real.pi_gt_d20] | exact sqrt_c_le
    _ < 4.1926e19 := by norm_num

/-- p. 371: `h = λ(4.1926 · 10^{19}) < 1.052 · 10^{12}`, via Lemma 6. -/
theorem p371_lam_lam : gL6 4.1926e19 < 1.052e12 := by
  unfold gL6
  have hlog : Real.log 4.1926e19 ≤ 45.1825 := (Real.log_le_iff_le_exp (by norm_num)).2 e451825
  have hlog0 : 0 ≤ Real.log 4.1926e19 := Real.log_nonneg (by norm_num)
  have hs : √((1 + 1 / 16597) * 4.1926e19 : ℝ) ≤ 6475225000 :=
    sqrt_le_of le_rfl (by norm_num) (by norm_num)
  calc 1 / (4 * π) * √((1 + 1 / 16597) * 4.1926e19 : ℝ) * Real.log 4.1926e19 ^ 2
      ≤ 1 / (4 * 3.14159265) * 6475225000 * 45.1825 ^ 2 := by
        gcongr
        linarith [Real.pi_gt_d20]
    _ < 1.052e12 := by norm_num

/-- p. 372: at `x = e^{78}`, `h < 1.052 · 10^{12}` gives `T = 2x/h ≥ e^{51}`. -/
theorem p372_T51 : Real.exp 51 ≤ 2 * Real.exp 78 / 1.052e12 := by
  rw [le_div_iff₀ (by norm_num)]
  have h27 := nat_le_exp 27
  push_cast at h27
  have : Real.exp 78 = Real.exp 51 * Real.exp 27 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have : (1.052e12 : ℝ) ≤ 2 * Real.exp 27 := by nlinarith
  nlinarith [Real.exp_pos 51]

/-- p. 372: for `x = e^L > e^{84000}`, Lemma 6's bound is below `x^{0.50024}`. -/
theorem p372_x050024 {L : ℝ} (hL : 84000 ≤ L) : gL6 (Real.exp L) < Real.exp (0.50024 * L) := by
  rw [gL6_exp]
  set e := L - 84000 with he
  have he0 : 0 ≤ e := by linarith
  have hsplit : Real.exp (0.50024 * L) = Real.exp (L / 2) * (Real.exp 20.16 * Real.exp (0.00024 * e)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [he]; ring
  have hq := Real.quadratic_le_exp_of_nonneg (x := 0.00024 * e) (by positivity)
  have hk := kappa_le
  have hin : 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * L ^ 2 < Real.exp 20.16 * Real.exp (0.00024 * e) := by
    have hL2 : L = 84000 + e := by rw [he]; ring
    have h1 : 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * L ^ 2 ≤ 1 / (4 * 3.14159265) * 1.0000302 * L ^ 2 :=
      mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    have h2 : 1 / (4 * 3.14159265) * 1.0000302 * L ^ 2 < 5.69e8 * (1 + 0.00024 * e + (0.00024 * e) ^ 2 / 2) := by
      rw [hL2]; nlinarith [mul_nonneg he0 he0]
    have h3 : 5.69e8 * (1 + 0.00024 * e + (0.00024 * e) ^ 2 / 2) ≤ Real.exp 20.16 * Real.exp (0.00024 * e) :=
      mul_le_mul e2016 hq (by positivity) (Real.exp_pos _).le
    linarith
  rw [hsplit]
  have := mul_lt_mul_of_pos_left hin (Real.exp_pos (L / 2))
  calc 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * Real.exp (L / 2) * L ^ 2
      = Real.exp (L / 2) * (1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * L ^ 2) := by ring
    _ < _ := this

/-- p. 372: `λ(λ(x)) < x^{0.25035}`: Lemma 6's bound at `x^{0.50024}` is below `x^{0.25035}`. -/
theorem p372_x025035 {L : ℝ} (hL : 84000 ≤ L) :
    gL6 (Real.exp (0.50024 * L)) < Real.exp (0.25035 * L) := by
  rw [gL6_exp]
  set e := L - 84000 with he
  have he0 : 0 ≤ e := by linarith
  have hsplit : Real.exp (0.25035 * L) =
      Real.exp (0.50024 * L / 2) * (Real.exp 19.32 * Real.exp (0.00023 * e)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [he]; ring
  have hq := Real.quadratic_le_exp_of_nonneg (x := 0.00023 * e) (by positivity)
  have hk := kappa_le
  have hin : 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * (0.50024 * L) ^ 2 <
      Real.exp 19.32 * Real.exp (0.00023 * e) := by
    have hL2 : L = 84000 + e := by rw [he]; ring
    have h1 : 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * (0.50024 * L) ^ 2 ≤
        1 / (4 * 3.14159265) * 1.0000302 * (0.50024 * L) ^ 2 :=
      mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    have h2 : 1 / (4 * 3.14159265) * 1.0000302 * (0.50024 * L) ^ 2 <
        2.45e8 * (1 + 0.00023 * e + (0.00023 * e) ^ 2 / 2) := by
      rw [hL2]; nlinarith [mul_nonneg he0 he0]
    have h3 : 2.45e8 * (1 + 0.00023 * e + (0.00023 * e) ^ 2 / 2) ≤
        Real.exp 19.32 * Real.exp (0.00023 * e) :=
      mul_le_mul e1932 hq (by positivity) (Real.exp_pos _).le
    linarith
  rw [hsplit]
  have := mul_lt_mul_of_pos_left hin (Real.exp_pos (0.50024 * L / 2))
  calc 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * Real.exp (0.50024 * L / 2) * (0.50024 * L) ^ 2
      = Real.exp (0.50024 * L / 2) * (1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * (0.50024 * L) ^ 2) := by
        ring
    _ < _ := this

/-- (26), p. 372: from (25) with `0.271` and `h < x^{0.25035}`, `h < 1116 log² x`. -/
theorem p372_eq26 {L h : ℝ} (hL : 84000 ≤ L) (h2 : 2 ≤ h) (hu : Real.log h ≤ 0.25035 * L)
    (h25 : h < rhs25 0.271 L (L + Real.log 2 - Real.log h)) : h < 1116 * L ^ 2 := by
  set M := L + Real.log 2 - Real.log h with hM
  have hl2 : Real.log 2 ≤ Real.log h := Real.log_le_log (by norm_num) h2
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMlo : 0.74965 * L ≤ M := by rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  have hMhi : M ≤ L := by rw [hM]; linarith
  have hq : L / M ≤ 1 / 0.74965 := by
    rw [div_le_iff₀ hM0]; nlinarith
  have hB : Real.exp (5.199931001 * (1 / 0.74965)) ≤ 1029.2 :=
    (Real.exp_le_exp.2 (by norm_num)).trans e69365
  have := rhs25_le (K := 0.271) (by norm_num) hM0.le hMhi hq hB
  have : 4 * 0.271 * 1029.2 * L ^ 2 < 1116 * L ^ 2 := by nlinarith
  linarith

/-- p. 372: if `h < 1116 log² x` and `log x ≥ 84000`, then `log T = log(2x/h) ≥ 83970`. -/
theorem p372_T83970 {L h : ℝ} (hL : 84000 ≤ L) (hh : 0 < h) (h26 : h < 1116 * L ^ 2) :
    83970 ≤ L + Real.log 2 - Real.log h := by
  set e := L - 84000 with he
  have he0 : 0 ≤ e := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg he0
  have hbig : 1116 * L ^ 2 ≤ 2 * Real.exp (L - 83970) := by
    have : Real.exp (L - 83970) = Real.exp 30 * Real.exp e := by rw [← Real.exp_add]; congr 1; rw [he]; ring
    rw [this]
    have hL2 : L = 84000 + e := by rw [he]; ring
    have h3 : 1.0686e13 * (1 + e + e ^ 2 / 2) ≤ Real.exp 30 * Real.exp e :=
      mul_le_mul e30 hq (by positivity) (Real.exp_pos _).le
    rw [hL2]; nlinarith [mul_nonneg he0 he0]
  have : Real.log h < Real.log (2 * Real.exp (L - 83970)) :=
    Real.log_lt_log hh (lt_of_lt_of_le h26 hbig)
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  linarith

theorem log_L_le {L : ℝ} (hL : 84000 ≤ L) : Real.log L ≤ Real.log 84000 + (L / 84000 - 1) := by
  have := Real.log_le_sub_one_of_pos (show 0 < L / 84000 by positivity)
  rw [Real.log_div (by linarith) (by norm_num)] at this
  linarith

/-- (27), p. 373: from (25) with `0.1973261` and `h < 1116 log² x`, `h < 143.3263 log²(2x/h)`. -/
theorem p373_eq27 {L h : ℝ} (hL : 84000 ≤ L) (hh : 0 < h) (h26 : h < 1116 * L ^ 2)
    (h25 : h < rhs25 0.1973261 L (L + Real.log 2 - Real.log h)) :
    h < 143.3263 * (L + Real.log 2 - Real.log h) ^ 2 := by
  set M := L + Real.log 2 - Real.log h with hM
  have hLp : 0 < L := by linarith
  have hlh : Real.log h < Real.log 1116 + 2 * Real.log L := by
    have := Real.log_lt_log hh h26
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
  have hK : Real.log 558 + 2 * Real.log 84000 ≤ 29.00155 := by
    have := (Real.log_le_iff_le_exp (by norm_num)).2 e2900155
    rwa [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at this
  have h1116 : Real.log 1116 = Real.log 2 + Real.log 558 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hlL := log_L_le hL
  have hMlo : L * (84000 - 29.00155) / 84000 ≤ M := by
    rw [hM, div_le_iff₀ (by norm_num)]; nlinarith
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hMlo
  have hq : L / M ≤ 84000 / (84000 - 29.00155) := by
    rw [div_le_div_iff₀ hM0 (by norm_num)]
    rw [div_le_iff₀ (by norm_num)] at hMlo; nlinarith
  have hB : Real.exp (5.199931001 * (84000 / (84000 - 29.00155))) ≤ 181.58558 :=
    (Real.exp_le_exp.2 (by norm_num)).trans e5201727
  have := rhs25_le (K := 0.1973261) (Mhi := M) (by norm_num) hM0.le le_rfl hq hB
  have : 4 * 0.1973261 * 181.58558 * M ^ 2 ≤ 143.3263 * M ^ 2 := by nlinarith [sq_nonneg M]
  linarith

/-- p. 373: from (27) and `log x ≤ log n₀ = e^{11.503}`, `h < 1.4045 · 10^{12}`. -/
theorem p373_h14045 {L h : ℝ} (hLhi : L ≤ Real.exp 11.503) (hh : 0 < h)
    (hM0 : 0 ≤ L + Real.log 2 - Real.log h)
    (h27 : h < 143.3263 * (L + Real.log 2 - Real.log h) ^ 2) : h < 1.4045e12 := by
  by_contra hc
  push Not at hc
  have hlh : 27.9707 ≤ Real.log h := (Real.le_log_iff_exp_le hh).2 (e279707.trans hc)
  have hl2 := Real.log_two_lt_d9
  have hMhi : L + Real.log 2 - Real.log h ≤ 99012.37 + 0.6931471808 - 27.9707 := by
    linarith [e11503]
  have : 143.3263 * (L + Real.log 2 - Real.log h) ^ 2 ≤
      143.3263 * (99012.37 + 0.6931471808 - 27.9707 : ℝ) ^ 2 := by
    gcongr
  have : 143.3263 * (99012.37 + 0.6931471808 - 27.9707 : ℝ) ^ 2 < 1.4045e12 := by norm_num
  linarith

/-- The Remark, p. 373, numerical part: with `h = 144 log² x`, `log x ≥ 84000`, one has
`log T ≥ 83970` and (25) with `0.1973261` fails. -/
theorem p373_remark_num {L : ℝ} (hL : 84000 ≤ L) :
    83970 ≤ L + Real.log 2 - Real.log (144 * L ^ 2) ∧
      rhs25 0.1973261 L (L + Real.log 2 - Real.log (144 * L ^ 2)) < 144 * L ^ 2 := by
  set M := L + Real.log 2 - Real.log (144 * L ^ 2) with hM
  have hLp : 0 < L := by linarith
  have e1 : Real.log (144 * L ^ 2) = Real.log 2 + Real.log 72 + 2 * Real.log L := by
    rw [show (144 : ℝ) * L ^ 2 = 2 * 72 * L ^ 2 by ring, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have hK : Real.log 72 + 2 * Real.log 84000 ≤ 26.9539 := by
    have := (Real.log_le_iff_le_exp (by norm_num)).2 e269539
    rwa [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at this
  have hlL := log_L_le hL
  have hlL0 : Real.log 84000 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have h72 : 0 ≤ Real.log 72 := Real.log_nonneg (by norm_num)
  have h84 : 0 ≤ Real.log 84000 := Real.log_nonneg (by norm_num)
  have hMlo : L * (84000 - 26.9539) / 84000 ≤ M := by
    rw [hM, e1, div_le_iff₀ (by norm_num)]; nlinarith
  have hMhi : M ≤ L := by rw [hM, e1]; linarith
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hMlo
  refine ⟨by rw [div_le_iff₀ (by norm_num)] at hMlo; nlinarith, ?_⟩
  have hq : L / M ≤ 84000 / (84000 - 26.9539) := by
    rw [div_le_div_iff₀ hM0 (by norm_num)]
    rw [div_le_iff₀ (by norm_num)] at hMlo; nlinarith
  have hB : Real.exp (5.199931001 * (84000 / (84000 - 26.9539))) ≤ 181.6 :=
    (Real.exp_le_exp.2 (by norm_num)).trans e52017
  have := rhs25_le (K := 0.1973261) (by norm_num) hM0.le hMhi hq hB
  have : 4 * 0.1973261 * 181.6 * L ^ 2 < 144 * L ^ 2 := by nlinarith
  linarith

/-- p. 372, "after some elementary computations yields `h < 1.4 · 10^{12}`": for
`78 ≤ log x ≤ 84000`, every `h ≥ 1.4 · 10^{12}` with `h ≤ x^{1/2}` violates (25). The bound
`h ≤ x^{1/2}` follows from `h ≤ λ(λ(x))` and Lemma 6. -/
theorem p372_claim_14e12 {L h : ℝ} (hL1 : 78 ≤ L) (hL2 : L ≤ 84000) (hh : 1.4e12 ≤ h)
    (hu : Real.log h ≤ L / 2) : rhs25 0.271 L (L + Real.log 2 - Real.log h) < h := by
  set M := L + Real.log 2 - Real.log h with hM
  have hh0 : 0 < h := by linarith
  have hl2 : Real.log 2 ≤ Real.log h := Real.log_le_log (by norm_num) (by linarith)
  have hl2a := Real.log_two_gt_d9
  have hMhi : M ≤ L := by rw [hM]; linarith
  rcases le_or_gt (Real.log h) 40 with hA | hC
  · have hMlo : L - 39.31 ≤ M := by rw [hM]; linarith
    have hM0 : 0 < M := by linarith
    rcases le_or_gt L 1000 with h1 | h1
    · have hq := ratio_le (k := 39.31) (L0 := 78) (by norm_num) (by norm_num) hL1 hMlo
      have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (78 / (78 - 39.31)) ≤ 10.4832)).trans e104832
      have := rhs25_le (K := 0.271) (by norm_num) hM0.le (hMhi.trans h1) hq hB
      have : 4 * 0.271 * 35720 * (1000 : ℝ) ^ 2 < 1.4e12 := by norm_num
      linarith
    rcases le_or_gt L 40000 with h2 | h2
    · have hq := ratio_le (k := 39.31) (L0 := 1000) (by norm_num) (by norm_num) h1.le hMlo
      have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (1000 / (1000 - 39.31)) ≤ 5.4128)).trans e54128
      have := rhs25_le (K := 0.271) (by norm_num) hM0.le (hMhi.trans h2) hq hB
      have : 4 * 0.271 * 224.3 * (40000 : ℝ) ^ 2 < 1.4e12 := by norm_num
      linarith
    · have hq := ratio_le (k := 39.31) (L0 := 40000) (by norm_num) (by norm_num) h2.le hMlo
      have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (40000 / (40000 - 39.31)) ≤ 5.20505)).trans e520505
      have := rhs25_le (K := 0.271) (by norm_num) hM0.le (hMhi.trans hL2) hq hB
      have : 4 * 0.271 * 182.22 * (84000 : ℝ) ^ 2 < 1.4e12 := by norm_num
      linarith
  · have hMlo : L / 2 ≤ M := by rw [hM]; linarith
    have hM0 : 0 < M := by linarith
    have hq : L / M ≤ 2 := by rw [div_le_iff₀ hM0]; linarith
    have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * 2 ≤ 10.4)).trans e104
    have := rhs25_le (K := 0.271) (by norm_num) hM0.le (hMhi.trans hL2) hq hB
    have hh40 : (2.35e17 : ℝ) ≤ h := by
      have : Real.exp 40 ≤ h := by rw [← Real.exp_log hh0]; exact Real.exp_le_exp.2 hC.le
      linarith [e40]
    have : 4 * 0.271 * 32900 * (84000 : ℝ) ^ 2 < 2.35e17 := by norm_num
    linarith

/-! ### Numerics for the assembled proof with `h = 1.4045 · 10^{12}` -/

theorem kk_bounds : 27.27755 ≤ Real.log (1.4045e12 / 2) ∧ Real.log (1.4045e12 / 2) ≤ 27.27756 := by
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 (e2727755.trans (by norm_num))
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 ((by norm_num : (1.4045e12 / 2 : ℝ) ≤ 7.0225e11).trans e2727756)

/-- Range 2 numerics: Lemma 6's bound at `e^{78.5}` is below `5.4599 · 10^{19}`. -/
theorem a1_gL6_e785 : gL6 (Real.exp 78.5) ≤ 5.4599e19 := by
  rw [gL6_exp]
  calc 1 / (4 * π) * √(1 + 1 / 16597 : ℝ) * Real.exp (78.5 / 2) * 78.5 ^ 2
      ≤ 1 / (4 * 3.14159265) * 1.0000302 * 1.1119e17 * 78.5 ^ 2 := by
        gcongr
        all_goals first | linarith [Real.pi_gt_d20] | exact sqrt_c_le |
          exact (Real.exp_le_exp.2 (by norm_num : (78.5 : ℝ) / 2 ≤ 39.25)).trans e3925
    _ ≤ 5.4599e19 := by norm_num

/-- Range 2 numerics: Lemma 6's bound at `5.46 · 10^{19}` is below `1.22 · 10^{12}`. -/
theorem a1_gL6_546 : gL6 5.46e19 ≤ 1.22e12 := by
  unfold gL6
  have hlog : Real.log 5.46e19 ≤ 45.447 := (Real.log_le_iff_le_exp (by norm_num)).2 e45447
  have hlog0 : 0 ≤ Real.log 5.46e19 := Real.log_nonneg (by norm_num)
  have hs : √((1 + 1 / 16597) * 5.46e19 : ℝ) ≤ 7.3895e9 :=
    sqrt_le_of le_rfl (by norm_num) (by norm_num)
  calc 1 / (4 * π) * √((1 + 1 / 16597) * 5.46e19 : ℝ) * Real.log 5.46e19 ^ 2
      ≤ 1 / (4 * 3.14159265) * 7.3895e9 * 45.447 ^ 2 := by
        gcongr
        linarith [Real.pi_gt_d20]
    _ ≤ 1.22e12 := by norm_num

/-- Range 3 numerics: with `h = 1.4045 · 10^{12}`, `78.5 ≤ log x ≤ 84000`, (25) with `0.271` fails. -/
theorem a2_range3 {L kk : ℝ} (hk1 : 27.27755 ≤ kk) (hk2 : kk ≤ 27.27756) (hL1 : 78.5 ≤ L)
    (hL2 : L ≤ 84000) : rhs25 0.271 L (L - kk) < 1.4045e12 := by
  have hMlo : L - 27.27756 ≤ L - kk := by linarith
  have hM0 : 0 < L - kk := by linarith
  rcases le_or_gt L 1000 with h1 | h1
  · have hq := ratio_le (k := 27.27756) (L0 := 78.5) (by norm_num) (by norm_num) hL1 hMlo
    have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (78.5 / (78.5 - 27.27756)) ≤ 7.96906)).trans e796906
    have := rhs25_le (K := 0.271) (Mhi := 1000 - 27.27755) (by norm_num) hM0.le (by linarith) hq hB
    have : 4 * 0.271 * 2890.2 * (1000 - 27.27755 : ℝ) ^ 2 < 1.4045e12 := by norm_num
    linarith
  rcases le_or_gt L 40000 with h2 | h2
  · have hq := ratio_le (k := 27.27756) (L0 := 1000) (by norm_num) (by norm_num) h1.le hMlo
    have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (1000 / (1000 - 27.27756)) ≤ 5.34576)).trans e534576
    have := rhs25_le (K := 0.271) (Mhi := 40000 - 27.27755) (by norm_num) hM0.le (by linarith) hq hB
    have : 4 * 0.271 * 209.72 * (40000 - 27.27755 : ℝ) ^ 2 < 1.4045e12 := by norm_num
    linarith
  · have hq := ratio_le (k := 27.27756) (L0 := 40000) (by norm_num) (by norm_num) h2.le hMlo
    have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (40000 / (40000 - 27.27756)) ≤ 5.20348)).trans e520348
    have := rhs25_le (K := 0.271) (Mhi := 84000 - 27.27755) (by norm_num) hM0.le (by linarith) hq hB
    have : 4 * 0.271 * 181.905 * (84000 - 27.27755 : ℝ) ^ 2 < 1.4045e12 := by norm_num
    linarith

/-- Range 4 numerics: with `h = 1.4045 · 10^{12}`, `84000 ≤ log x ≤ e^{11.503}`, (25) with
`0.1973261` fails. -/
theorem a3_range4 {L kk : ℝ} (hk1 : 27.27755 ≤ kk) (hk2 : kk ≤ 27.27756) (hL1 : 84000 ≤ L)
    (hL2 : L ≤ Real.exp 11.503) : rhs25 0.1973261 L (L - kk) < 1.4045e12 := by
  have hMlo : L - 27.27756 ≤ L - kk := by linarith
  have hM0 : 0 < L - kk := by linarith
  have hq := ratio_le (k := 27.27756) (L0 := 84000) (by norm_num) (by norm_num) hL1 hMlo
  have hB := (Real.exp_le_exp.2 (by norm_num : (5.199931001 : ℝ) * (84000 / (84000 - 27.27756)) ≤ 5.2016202)).trans e5201620
  have := rhs25_le (K := 0.1973261) (Mhi := 99012.37 - 27.27755) (by norm_num) hM0.le
    (by linarith [e11503]) hq hB
  have : 4 * 0.1973261 * 181.5662 * (99012.37 - 27.27755 : ℝ) ^ 2 < 1.4045e12 := by norm_num
  linarith


end LeanLab.Kaniecki1995

#print axioms LeanLab.Kaniecki1995.c392
#print axioms LeanLab.Kaniecki1995.c702
#print axioms LeanLab.Kaniecki1995.delta_le
#print axioms LeanLab.Kaniecki1995.c504
#print axioms LeanLab.Kaniecki1995.c8232
#print axioms LeanLab.Kaniecki1995.series_ge
#print axioms LeanLab.Kaniecki1995.c0144
#print axioms LeanLab.Kaniecki1995.c_first_term
#print axioms LeanLab.Kaniecki1995.gL6_exp
#print axioms LeanLab.Kaniecki1995.gL6_mono
#print axioms LeanLab.Kaniecki1995.eq25
#print axioms LeanLab.Kaniecki1995.p371_lam_e78
#print axioms LeanLab.Kaniecki1995.p371_lam_lam
#print axioms LeanLab.Kaniecki1995.p372_T51
#print axioms LeanLab.Kaniecki1995.p372_x050024
#print axioms LeanLab.Kaniecki1995.p372_x025035
#print axioms LeanLab.Kaniecki1995.p372_eq26
#print axioms LeanLab.Kaniecki1995.p372_T83970
#print axioms LeanLab.Kaniecki1995.p373_eq27
#print axioms LeanLab.Kaniecki1995.p373_h14045
#print axioms LeanLab.Kaniecki1995.p373_remark_num
#print axioms LeanLab.Kaniecki1995.p372_claim_14e12
#print axioms LeanLab.Kaniecki1995.kk_bounds
#print axioms LeanLab.Kaniecki1995.a1_gL6_e785
#print axioms LeanLab.Kaniecki1995.a1_gL6_546
#print axioms LeanLab.Kaniecki1995.a2_range3
#print axioms LeanLab.Kaniecki1995.a3_range4
