/-
AI-written Lean code, Claude, Lean Lab run 20261022T1302Z-31860, unit U-1483, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, Lemma 32's m of X3 at log log X2 = 32.15,
delta2 = 1.47115, the lab's frontier point of BJSm3215.lean, with the Siegel term nu of eq (91)
replaced by the q-dependent nuN of U1483SiegelQ.lean:
nuN = min(4 log(K/4)/(sqrt K log^2 K), 1/(2 R1 10 log l)), K = l^delta2, l = log x2 of X3.

BJSmX3.lean and BJSm3215.lean fix nu as a def, so their m bounds do not take nu as a parameter;
mX3 itself depends only on v, an upper bound for v'0 of (72), and phi carries nu.  This file
therefore re-proves the bracket bound with nuN and a new m bound, importing the definitions.

PROVED, numeric: nuNl_ge, nuN l >= 245, against the old Lean 144.9; phiN_le, the bracket of (72)
with beta0 = 1 - nuN is at most 5e-40 for every Y >= l; mN_le, m of X3 <= 1.03e-11 for
0 <= v <= 5e-40, against the old Lean 8.34e-10.  The floor is now 39 times 3/Lambda3.
CONDITIONAL, m_new_conditional: under the four cited Props of U1483SiegelQ, Thm11C being the
unprinted c-form, every real zero of an even primitive real L mod q with 4e5 < q <= K is at
most 1 - nuN, so nuN is a legitimate even-character Siegel input at this point.
The odd-character and Kadiri branch of (91) is untouched.  This is not a Chen threshold: the
X2-only chains were not redone.  Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.BJSm3215
import LeanLab.ChenExplicit.U1483SiegelQ

open Real

noncomputable section
namespace LeanLab.ChenExplicit.U1483MX3

open LeanLab.ChenExplicit.BJSm3215

/-- the new `ν(x₂)` with the q-dependent even-character constant. -/
def νN : ℝ := min (4 * log (K / 4) / (sqrt K * log K ^ 2)) (1 / (2 * 2.0452 * (10 * log ℓ)))
/-- `β₀ = 1 - νN`. -/
def β0N : ℝ := 1 - νN

/-- the bracket of (72) with `β₀ = 1 - νN`. -/
def φN (Y : ℝ) : ℝ :=
  3.2e-8 / Y ^ 4 + Y ^ 4 * (exp ((β0N - 1) * Y) / β0N + 1.02 * Y ^ 10 / exp (Y / 2) +
    3 * Y ^ 10 / exp (2 * Y / 3))

lemma logK_eq : log K = 1.47115 * log ℓ := by
  unfold K; rw [log_rpow ℓ_pos]

lemma logK_bounds : 44.238 ≤ log K ∧ log K ≤ 44.2384 := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  rw [logK_eq]; constructor <;> nlinarith

lemma K_pos : 0 < K := by unfold K; exact rpow_pos_of_pos ℓ_pos _

lemma logK4 : log (K / 4) = log K - log 4 := log_div K_pos.ne' (by norm_num)

/-- **`νN ℓ ≥ 245`.** -/
lemma νNℓ_ge : 245 ≤ νN * ℓ := by
  obtain ⟨u1, u2⟩ := logℓ_bounds
  have hℓ := ℓ_pos
  have c4 := LeanLab.ChenExplicit.U1483.log4_le
  set u := log ℓ with hu
  have hK : K = exp (u * 1.47115) := by unfold K; rw [rpow_def_of_pos hℓ]
  have hlogK : log K = 1.47115 * u := by rw [hK, log_exp]; ring
  have hsK : sqrt K = exp (0.735575 * u) := by
    rw [hK, sqrt_eq_rpow, ← exp_mul]; ring_nf
  have hℓe : ℓ = exp u := (exp_log hℓ).symm
  unfold νN
  rw [logK4, hsK, hlogK]
  have br1 : 245 ≤ 4 * (1.47115 * u - log 4) / (exp (0.735575 * u) * (1.47115 * u) ^ 2) * ℓ := by
    have hE : 2839 ≤ exp (0.264425 * u) := by
      have h0 : exp (7.9513 : ℝ) ≤ exp (0.264425 * u) := exp_le_exp.mpr (by linarith)
      have h := sum_le_exp_of_nonneg (x := (7.9513 : ℝ)) (by norm_num) 24
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
      norm_num at h; linarith
    have e : ℓ = exp (0.735575 * u) * exp (0.264425 * u) := by
      rw [hℓe, ← exp_add]; ring_nf
    have hp := exp_pos (0.735575 * u)
    have hD : 0 < (1.47115 * u) ^ 2 := by positivity
    have e2 : 4 * (1.47115 * u - log 4) / (exp (0.735575 * u) * (1.47115 * u) ^ 2) * ℓ =
        4 * (1.47115 * u - log 4) * exp (0.264425 * u) / (1.47115 * u) ^ 2 := by
      rw [e]; field_simp
    rw [e2, le_div_iff₀ hD]
    have hu2 : (1.47115 * u) ^ 2 ≤ 1957.1 := by nlinarith
    have hN : 171.4 ≤ 4 * (1.47115 * u - log 4) := by nlinarith
    nlinarith
  have br2 : 245 ≤ 1 / (2 * 2.0452 * (10 * u)) * ℓ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have := ℓ_bounds.1; have := Λ3_ge; nlinarith
  rcases min_choice (4 * (1.47115 * u - log 4) / (exp (0.735575 * u) * (1.47115 * u) ^ 2))
    (1 / (2 * 2.0452 * (10 * u))) with h | h
  · rw [h]; exact br1
  · rw [h]; exact br2

lemma νN_pos : 0 < νN := by
  have := νNℓ_ge; have := ℓ_pos; nlinarith

lemma νN_le : νN ≤ 1 / 1000 := by
  obtain ⟨u1, _⟩ := logℓ_bounds
  unfold νN
  refine (min_le_right _ _).trans ?_
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith

/-- `Y⁴ e^{-νN Y}` decreases for `Y ≥ ℓ`. -/
lemma decayN (Y : ℝ) (hY : ℓ ≤ Y) : Y ^ 4 * exp (-νN * Y) ≤ ℓ ^ 4 * exp (-νN * ℓ) := by
  have hℓ := ℓ_pos
  have hν := νNℓ_ge
  have hd : 0 ≤ Y - ℓ := by linarith
  have h1 : Y / ℓ ≤ exp ((Y - ℓ) / ℓ) := by
    have := add_one_le_exp ((Y - ℓ) / ℓ)
    have e : (Y - ℓ) / ℓ + 1 = Y / ℓ := by field_simp; ring
    linarith
  have h2 : (Y / ℓ) ^ 4 ≤ exp (4 * ((Y - ℓ) / ℓ)) := by
    have := pow_le_pow_left₀ (div_nonneg (by linarith) hℓ.le) h1 4
    rw [← exp_nat_mul] at this; push_cast at this; exact this
  have h3 : 4 * ((Y - ℓ) / ℓ) ≤ νN * (Y - ℓ) := by
    rw [← mul_div_assoc, div_le_iff₀ hℓ]; nlinarith
  have h4 : (Y / ℓ) ^ 4 ≤ exp (νN * (Y - ℓ)) := h2.trans (exp_le_exp.mpr h3)
  have e1 : Y ^ 4 = ℓ ^ 4 * (Y / ℓ) ^ 4 := by field_simp
  have e2 : exp (-νN * ℓ) = exp (νN * (Y - ℓ)) * exp (-νN * Y) := by rw [← exp_add]; ring_nf
  rw [e1, e2]
  have := exp_pos (-νN * Y)
  have : 0 ≤ ℓ ^ 4 := by positivity
  calc ℓ ^ 4 * (Y / ℓ) ^ 4 * exp (-νN * Y) ≤ ℓ ^ 4 * exp (νN * (Y - ℓ)) * exp (-νN * Y) := by
        gcongr
    _ = _ := by ring

/-- **`φN(Y) ≤ 5·10⁻⁴⁰` for every `Y ≥ log x₂(X₃)`.** -/
theorem phiN_le (Y : ℝ) (hY : ℓ ≤ Y) : φN Y ≤ 5 / 10 ^ 40 := by
  have hℓ := ℓ_pos
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; have := Λ3_ge; nlinarith
  have hY13 : (9 * 10 ^ 12 : ℝ) ≤ Y := by norm_num at hℓ13; linarith
  have hYp : 0 < Y := by linarith
  have hν1 := νN_le
  have hν0 := νN_pos
  have hb : 0.999 ≤ β0N := by unfold β0N; norm_num at hν1 ⊢; linarith
  unfold φN
  have t1 : 3.2e-8 / Y ^ 4 ≤ 1 / 10 ^ 50 := by
    rw [div_le_iff₀ (by positivity)]
    have : (9 * 10 ^ 12 : ℝ) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (by norm_num) hY13 4
    norm_num at this ⊢; nlinarith
  have e2 : (β0N - 1) * Y = -νN * Y := by unfold β0N; ring
  rw [e2]
  have d := decayN Y hY
  have hu := logℓ_bounds.2
  have hℓ4 : ℓ ^ 4 ≤ exp (4 * 30.0706) := by
    have : ℓ = exp (log ℓ) := (exp_log hℓ).symm
    rw [this, ← exp_nat_mul]; push_cast; exact exp_le_exp.mpr (by linarith)
  have hνℓ : exp (-νN * ℓ) ≤ exp (-245) := exp_le_exp.mpr (by have := νNℓ_ge; nlinarith)
  have hcomb : ℓ ^ 4 * exp (-νN * ℓ) ≤ exp (4 * 30.0706) * exp (-245) :=
    mul_le_mul hℓ4 hνℓ (exp_pos _).le (exp_pos _).le
  have hx : exp (4 * 30.0706) * exp (-245) ≤ 1 / 10 ^ 50 := by
    rw [← exp_add]
    have hle : exp (4 * 30.0706 + -245 : ℝ) ≤ exp (-((124 : ℕ) : ℝ)) :=
      exp_le_exp.mpr (by norm_num)
    rw [exp_neg] at hle
    have a := exp_nat_ge 124
    have c : (exp ((124 : ℕ) : ℝ))⁻¹ ≤ (2.7182818283 ^ 124)⁻¹ := by
      rw [inv_le_inv₀ (exp_pos _) (by positivity)]; exact a
    have h5 : ((2.7182818283 : ℝ) ^ 124)⁻¹ ≤ 1 / 10 ^ 50 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; norm_num
    linarith
  have t2 : Y ^ 4 * (exp (-νN * Y) / β0N) ≤ 2 / 10 ^ 50 := by
    have : Y ^ 4 * (exp (-νN * Y) / β0N) = (Y ^ 4 * exp (-νN * Y)) / β0N := by ring
    rw [this, div_le_iff₀ (by linarith)]
    have : Y ^ 4 * exp (-νN * Y) ≤ 1 / 10 ^ 50 := by linarith
    nlinarith
  have t3 : Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) ≤ 1.02 / 10 ^ 40 := by
    have := big_poly Y (by linarith)
    have e : Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) = 1.02 * (Y ^ 14 / exp (Y / 2)) := by ring
    rw [e]; nlinarith
  have t4 : Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) ≤ 3 / 10 ^ 40 := by
    have h := big_poly Y (by linarith)
    have hle : exp (Y / 2) ≤ exp (2 * Y / 3) := exp_le_exp.mpr (by linarith)
    have : Y ^ 14 / exp (2 * Y / 3) ≤ Y ^ 14 / exp (Y / 2) :=
      div_le_div_of_nonneg_left (by positivity) (exp_pos _) hle
    have e : Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) = 3 * (Y ^ 14 / exp (2 * Y / 3)) := by ring
    rw [e]; nlinarith
  have e : Y ^ 4 * (exp (-νN * Y) / β0N + 1.02 * Y ^ 10 / exp (Y / 2) +
      3 * Y ^ 10 / exp (2 * Y / 3)) =
      Y ^ 4 * (exp (-νN * Y) / β0N) + Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) +
        Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) := by ring
  rw [e]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

theorem mN_le (v : ℝ) (_hv0 : 0 ≤ v) (hv : v ≤ 5 / 10 ^ 40) : mX3 v ≤ 103 / 10 ^ 13 := by
  have hΛ := Λ3_ge
  have hΛ' : (1.14 * 10 ^ 13 : ℝ) ≤ Λ3 := by unfold Λ3; have := exp3215_ge; linarith
  have hℓ13 : (10 ^ 13 : ℝ) * (1 - 1 / 10 ^ 10) ≤ ℓ := by
    have := ℓ_bounds.1; nlinarith
  have hℓ := ℓ_pos
  unfold mX3 v0
  have a1 : 1 / (Λ3 ^ 10 * ℓ ^ 5) ≤ 1 / 10 ^ 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ Λ3 ^ 10 := one_le_pow₀ (by linarith)
    have : (10 ^ 12 : ℝ) ≤ ℓ ^ 5 := by
      have := pow_le_pow_left₀ (by norm_num) hℓ13 5; norm_num at this ⊢; linarith
    nlinarith
  have a2 : 1 / ((1 - 6 / ℓ) * Λ3) ≤ 1 / 10 ^ 12 := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; norm_num at hℓ13; linarith
    have h6p : 0 < 1 - 6 / ℓ := by linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have a3 : 3 / Λ3 ≤ 3 / (1.14 * 10 ^ 13) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ'
  have b1 : 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) ≤ 1 / 10 ^ 20 := by
    have hlog : 1 ≤ log Λ3 := by rw [log_Λ3]; have := log_two_lt_d9; norm_num at this ⊢; linarith
    have hE2 := pow_div_factorial_le_exp (x := Λ3) (by positivity) 20
    have hf : ((Nat.factorial 20 : ℕ) : ℝ) ≤ 10 ^ 19 := by norm_num [Nat.factorial]
    have h20 : Λ3 ^ 20 / 10 ^ 19 ≤ exp Λ3 :=
      le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hf) hE2
    rw [div_le_iff₀ (by have := exp_pos Λ3; positivity)]
    have hΛ4 : (10 ^ 52 : ℝ) ≤ Λ3 ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hΛ 4; norm_num at this ⊢; linarith
    have hΛ16 : 0 ≤ Λ3 ^ 16 := by positivity
    have : 108 * Λ3 ^ 16 ≤ 1 / 10 ^ 20 * (Λ3 ^ 20 / 10 ^ 19) := by
      have : Λ3 ^ 20 = Λ3 ^ 16 * Λ3 ^ 4 := by ring
      rw [this]; nlinarith [mul_le_mul_of_nonneg_left hΛ4 hΛ16]
    have : Λ3 ^ 20 / 10 ^ 19 ≤ exp Λ3 * log Λ3 := by
      have := exp_pos Λ3; nlinarith
    nlinarith
  have b2 : 26 * Λ3 ^ 5 / ℓ ^ 10 ≤ 1 / 10 ^ 20 := by
    have hℓΛ : Λ3 * (1 - 1 / 10 ^ 10) ≤ ℓ := ℓ_bounds.1
    have : (Λ3 / 2) ^ 10 ≤ ℓ ^ 10 := pow_le_pow_left₀ (by positivity) (by nlinarith) 10
    rw [div_le_iff₀ (by positivity)]
    have hΛ5 : (10 ^ 65 : ℝ) ≤ Λ3 ^ 5 := by
      have := pow_le_pow_left₀ (by norm_num) hΛ 5; norm_num at this ⊢; linarith
    have e : (Λ3 / 2) ^ 10 = Λ3 ^ 5 * Λ3 ^ 5 / 1024 := by ring
    rw [e] at this
    have h0 : 0 ≤ Λ3 ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hΛ5 h0]
  have b3 : 88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) ≤ 1 / 10 ^ 20 := by
    have hE := big_poly Λ3 (by linarith)
    have h1 : exp (-(8 / 3 * Λ3)) ≤ exp (-(Λ3 / 2)) := exp_le_exp.mpr (by linarith)
    have h2 : Λ3 ^ 5 * exp (-(Λ3 / 2)) ≤ 1 / 10 ^ 40 := by
      rw [exp_neg, ← div_eq_mul_inv]
      have : Λ3 ^ 5 / exp (Λ3 / 2) ≤ Λ3 ^ 14 / exp (Λ3 / 2) := by
        apply div_le_div_of_nonneg_right _ (exp_pos _).le
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h0 : 0 ≤ Λ3 ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left h1 h0
    nlinarith
  have b4 : 106 / Λ3 ^ 6 ≤ 1 / 10 ^ 20 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ (by norm_num) hΛ 6; norm_num at this ⊢; linarith
  have hv' : v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) ≤
      5 / 10 ^ 40 * (1 + 2 / 10 ^ 12) := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; norm_num at hℓ13; linarith
    have q1 : 0 ≤ 1 / (Λ3 ^ 10 * ℓ ^ 5) := by positivity
    have q2 : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) :=
      div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
    apply mul_le_mul hv (by linarith) (by linarith) (by norm_num)
  norm_num at hv' a3 b1 b2 b3 b4 ⊢
  linarith

/-- `v'₀(X₃)` with `νN`, the sup of (72) over `y ≥ x₂(X₃)`. -/
def vSN : ℝ := ⨆ Y : Set.Ici ℓ, φN Y

lemma phiN_nonneg {Y : ℝ} (hY : ℓ ≤ Y) : 0 ≤ φN Y := by
  have hY0 : 0 < Y := ℓ_pos.trans_le hY
  have hb : 0 < β0N := by unfold β0N; have := νN_le; linarith
  unfold φN
  positivity

lemma vSN_bounds : 0 ≤ vSN ∧ vSN ≤ 5 / 10 ^ 40 := by
  have : Nonempty (Set.Ici ℓ) := ⟨⟨ℓ, Set.mem_Ici.mpr le_rfl⟩⟩
  have hb : BddAbove (Set.range fun Y : Set.Ici ℓ => φN Y) :=
    ⟨5 / 10 ^ 40, by rintro _ ⟨Y, rfl⟩; exact phiN_le Y Y.2⟩
  exact ⟨(phiN_nonneg le_rfl).trans (le_ciSup hb ⟨ℓ, Set.mem_Ici.mpr le_rfl⟩),
    ciSup_le fun Y => phiN_le Y Y.2⟩

/-- **`0 ≤ m(X₃) ≤ 1.03·10⁻¹¹`** at log log X₂ = 32.15, δ₂ = 1.47115, with `νN`. -/
theorem mX3_vSN_bounds : 0 ≤ mX3 vSN ∧ mX3 vSN ≤ 103 / 10 ^ 13 := by
  obtain ⟨v0, v1⟩ := vSN_bounds
  exact ⟨mX3_nonneg v0, mN_le _ v0 v1⟩

/-- the side conditions of `siegel_even_upto_K` hold at this `K`. -/
lemma K_side : 100 ≤ 4 * log (K / 4) ∧ log (K / 4) ≤ 250 := by
  have c4 := LeanLab.ChenExplicit.U1483.log4_le
  have c4' : 0 ≤ log 4 := log_nonneg (by norm_num)
  obtain ⟨k1, k2⟩ := logK_bounds
  rw [logK4]; constructor <;> linarith

/-- **CONDITIONAL** on `ClassNumberH1`, `MeanValueStep`, `Thm11C`, `BordignonThm13`: every real
zero of an even primitive real `L(s, χ)` mod `q`, `4·10⁵ < q ≤ K`, is at most `β0N = 1 - νN`;
and, unconditionally, `m(X₃)` with `νN` is at most `1.03·10⁻¹¹`. -/
theorem m_new_conditional (hC : LeanLab.ChenExplicit.U1483.ClassNumberH1)
    (hM : LeanLab.ChenExplicit.U1483.MeanValueStep) (h11 : LeanLab.ChenExplicit.U1483.Thm11C)
    (h13 : LeanLab.ChenExplicit.U1483.BordignonThm13) :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), LeanLab.ChenExplicit.U1483.EvenRealPrim χ →
      (4e5 : ℝ) < q → (q : ℝ) ≤ K → ∀ β : ℝ, LeanLab.ChenExplicit.U1483.RealZero χ β → β ≤ β0N) ∧
    0 ≤ mX3 vSN ∧ mX3 vSN ≤ 103 / 10 ^ 13 := by
  refine ⟨?_, mX3_vSN_bounds⟩
  intro q _ χ hχ hq hqK β hβ
  have h := LeanLab.ChenExplicit.U1483.siegel_even_upto_K hC hM h11 h13 K_side.1 K_side.2 q χ hχ
    hq hqK β hβ
  have : νN ≤ 4 * log (K / 4) / (sqrt K * log K ^ 2) := min_le_left _ _
  unfold β0N; linarith

/-- the gain over the lab's old Lean figure, BJSm3215.mX3_vS_bounds, 8.34·10⁻¹⁰. -/
theorem gain_vs_old : (103 / 10 ^ 13 : ℝ) * 80 ≤ 834 / 10 ^ 12 := by norm_num

/-- Vacuity: `φN` is evaluated on a nonempty range, at `Y = ℓ` itself. -/
example : 0 ≤ φN ℓ ∧ φN ℓ ≤ 5 / 10 ^ 40 := ⟨phiN_nonneg le_rfl, phiN_le ℓ le_rfl⟩

end LeanLab.ChenExplicit.U1483MX3

#print axioms LeanLab.ChenExplicit.U1483MX3.νNℓ_ge
#print axioms LeanLab.ChenExplicit.U1483MX3.phiN_le
#print axioms LeanLab.ChenExplicit.U1483MX3.mN_le
#print axioms LeanLab.ChenExplicit.U1483MX3.mX3_vSN_bounds
#print axioms LeanLab.ChenExplicit.U1483MX3.K_side
#print axioms LeanLab.ChenExplicit.U1483MX3.m_new_conditional
#print axioms LeanLab.ChenExplicit.U1483MX3.gain_vs_old
