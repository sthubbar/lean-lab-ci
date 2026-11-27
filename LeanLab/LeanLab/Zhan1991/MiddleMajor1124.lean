/-
P0068 Zhan 1991, Theorem 2, page 262 last display: the case of the middle range reduction that the
blockwise step does not cover, split one step. burst-20261124, worker D, unit D-extra-2.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

When (1.2) holds with `τ = A² N⁻¹ L^{-c₁}` and `q ≥ L^{c₂}`, while the fresh approximation
`a₁/q₁` with `τ₁ = N^{1/3} L^{-c₁} / 4` has `q₁ < L^{c₂}`, the two fractions differ and
`|λ₁| ≥ 1/(q q₁) - 1/(q τ)`; this separation is PROVED as `cond12_sep`. What is left is the
analytic estimate of a major arc sum with that lower bound on the phase, LEAF
`middle_major_est_leaf`. `middle_major_of_est` gives the old LEAF `middle_major_leaf` of
MiddleSplit1124.lean, which now uses it.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122
import LeanLab.Zhan1991.WellKnownProof1122d

namespace LeanLab.Zhan1991

noncomputable section

/-- Page 262 last display, the two approximations differ: if (1.2) holds for `α` with `a/q` and
with `a₁/q₁`, `q₁ < q`, then `|λ₁| ≥ 1/(q q₁) - 1/(q τ)`, since `a/q ≠ a₁/q₁` as `(a, q) = 1`.
PROVED, burst-20261124 D-extra-2. -/
theorem cond12_sep (α τ τ1 lam lam1 : ℝ) (a a1 : ℤ) (q q1 : ℕ)
    (h : Cond12 α τ a q lam) (h1 : Cond12 α τ1 a1 q1 lam1) (hlt : q1 < q) :
    1 / ((q : ℝ) * q1) - 1 / ((q : ℝ) * τ) ≤ |lam1| := by
  obtain ⟨hα, hg, hl, hq1, -⟩ := h
  obtain ⟨hα1, -, -, hq11, -⟩ := h1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1pos : (0 : ℝ) < q1 := by exact_mod_cast hq11
  have hint : (1 : ℤ) ≤ |a * q1 - a1 * q| := by
    apply Int.one_le_abs
    intro h0
    have hdvd : (q : ℤ) ∣ a * q1 := ⟨a1, by linarith⟩
    have hcop : IsCoprime (q : ℤ) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hg
    have := Int.le_of_dvd (by exact_mod_cast hq11) (hcop.dvd_of_dvd_mul_left hdvd)
    have : q ≤ q1 := by exact_mod_cast this
    omega
  have hintR : (1 : ℝ) ≤ |(a : ℝ) * q1 - a1 * q| := by exact_mod_cast hint
  have hdiff : |(a : ℝ) / q - a1 / q1| ≥ 1 / ((q : ℝ) * q1) := by
    rw [show (a : ℝ) / q - a1 / q1 = ((a : ℝ) * q1 - a1 * q) / (q * q1) by field_simp,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q1)]
    exact div_le_div_of_nonneg_right hintR (by positivity)
  have hlam1 : lam1 = ((a : ℝ) / q - a1 / q1) + lam := by linarith
  have := abs_sub_abs_le_abs_sub ((a : ℝ) / q - a1 / q1) (-lam)
  rw [abs_neg, sub_neg_eq_add, ← hlam1] at this
  linarith

/-- Arithmetic for the middle range of page 262: the fresh approximation width is at most
one quarter of the original width. -/
theorem middle_major_tau1_le (N : ℕ) (A c1 : ℝ) (hN : (0 : ℝ) < N)
    (hA : (N : ℝ) ^ (2 / 3 : ℝ) ≤ A) :
    4 * ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) ≤
      A ^ 2 / N * Real.log N ^ (-c1) := by
  have hr : (N : ℝ) ^ (1 / 3 : ℝ) * N = ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by
    calc
      (N : ℝ) ^ (1 / 3 : ℝ) * N = (N : ℝ) ^ ((1 / 3 : ℝ) + 1) :=
        (Real.rpow_add_one hN.ne' _).symm
      _ = (N : ℝ) ^ ((2 / 3 : ℝ) * 2) := by norm_num
      _ = ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by
        rw [Real.rpow_mul hN.le, Real.rpow_two]
  have hAsq : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 ≤ A ^ 2 := by
    nlinarith [Real.rpow_nonneg hN.le (2 / 3 : ℝ)]
  have hdiv : (N : ℝ) ^ (1 / 3 : ℝ) ≤ A ^ 2 / N := by
    rw [le_div_iff₀ hN, hr]
    exact hAsq
  nlinarith [mul_le_mul_of_nonneg_right hdiv
    (Real.rpow_nonneg (Real.log_natCast_nonneg N) (-c1))]

/-- The separation bound of page 262 controls the reciprocal phase after the smaller
denominator is at most half the original approximation width. -/
theorem middle_major_reciprocal (q q1 τ lam : ℝ) (hq : 0 < q) (hq1 : 0 < q1)
    (hwidth : 2 * q1 ≤ τ)
    (hsep : 1 / (q * q1) - 1 / (q * τ) ≤ |lam|) :
    0 < |lam| ∧ 1 / (q1 * |lam|) ≤ 2 * q := by
  have hτ : 0 < τ := by linarith
  have hsmall : 1 / (q * τ) ≤ 1 / (2 * q * q1) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hhalf : 1 / (2 * q * q1) ≤ |lam| := by
    have hid : 1 / (q * q1) - 1 / (2 * q * q1) = 1 / (2 * q * q1) := by
      field_simp
      norm_num
    linarith
  have hlam : 0 < |lam| := lt_of_lt_of_le (by positivity) hhalf
  refine ⟨hlam, ?_⟩
  have hinv : 1 / |lam| ≤ 2 * q * q1 := by
    have := one_div_le_one_div_of_le (by positivity) hhalf
    simpa using this
  calc
    1 / (q1 * |lam|) = (1 / |lam|) / q1 := by rw [div_div, mul_comm q1]
    _ ≤ (2 * q * q1) / q1 := div_le_div_of_nonneg_right hinv hq1.le
    _ = 2 * q := mul_div_cancel_right₀ _ hq1.ne'

/-- The reciprocal phase in the page 262 middle major case is on the scale
`A L^{-c1-1}` after division by the smaller denominator. This is arithmetic only,
not the required estimate for the prime sum. -/
theorem middle_major_phase_scale (N : ℕ) (A α c1 : ℝ) (q : ℕ) (a1 : ℤ)
    (q1 : ℕ) (lam1 : ℝ) (hN : (1 : ℝ) < N)
    (hlo : (N : ℝ) ^ (2 / 3 : ℝ) ≤ A) (hhi : A ≤ (N : ℝ) / Real.log N)
    (hq : 0 < q) (hqτ : (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1))
    (hcond : Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1)
    (hsep : 1 / ((q : ℝ) * q1) -
      1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) ≤ |lam1|) :
    0 < |lam1| ∧ 1 / ((q1 : ℝ) * |lam1|) ≤ 2 * A * Real.log N ^ (-c1 - 1) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hLpos : 0 < Real.log N := Real.log_pos hN
  have hApos : 0 < A := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hlo
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1pos : (0 : ℝ) < q1 := by exact_mod_cast hcond.2.2.2.1
  have hfour := middle_major_tau1_le N A c1 hNpos hlo
  have hwidth : 2 * (q1 : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) := by
    linarith [hcond.2.2.2.2]
  obtain ⟨hlam, hinv⟩ := middle_major_reciprocal _ _ _ _ hqpos hq1pos hwidth hsep
  refine ⟨hlam, hinv.trans ?_⟩
  have hAN : A / N ≤ 1 / Real.log N := by
    rw [div_le_div_iff₀ hNpos hLpos]
    simpa using (le_div_iff₀ hLpos).mp hhi
  have hτ : A ^ 2 / N * Real.log N ^ (-c1) ≤ A * Real.log N ^ (-c1 - 1) := by
    calc
      A ^ 2 / N * Real.log N ^ (-c1) = A * (A / N) * Real.log N ^ (-c1) := by ring
      _ ≤ A * (1 / Real.log N) * Real.log N ^ (-c1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAN hApos.le)
          (Real.rpow_nonneg hLpos.le _)
      _ = A * Real.log N ^ (-c1 - 1) := by
        rw [Real.rpow_sub hLpos, Real.rpow_one]
        ring
  nlinarith

/-- The oscillatory integral in the middle major main term of page 262 is bounded by the
reciprocal of its nonzero frequency, uniformly in both endpoints. -/
theorem middle_major_integral_bound (a b lam : ℝ) (hlam : lam ≠ 0) :
    ‖∫ u in a..b, ee (lam * u)‖ ≤ 1 / |lam| := by
  let z : ℂ := 2 * Real.pi * Complex.I * lam
  have hz : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      (by exact_mod_cast hlam)
  have hee : (fun u : ℝ => ee (lam * u)) = fun u : ℝ => Complex.exp (z * u) := by
    funext u
    dsimp [ee, z]
    push_cast
    congr 1
    ring
  rw [hee, integral_exp_mul_complex hz, norm_div]
  have hnorm (x : ℝ) : ‖Complex.exp (z * x)‖ = 1 := by
    simp [z, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hz_norm : ‖z‖ = 2 * Real.pi * |lam| := by
    simp [z, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    ‖Complex.exp (z * b) - Complex.exp (z * a)‖ / ‖z‖ ≤ 2 / ‖z‖ :=
      div_le_div_of_nonneg_right
        ((norm_sub_le _ _).trans_eq (by rw [hnorm, hnorm]; norm_num)) (norm_nonneg _)
    _ = 2 / (2 * Real.pi * |lam|) := by rw [hz_norm]
    _ ≤ 1 / |lam| := by
      rw [div_le_div_iff₀ (by positivity) (abs_pos.mpr hlam)]
      nlinarith [Real.pi_gt_three, abs_pos.mpr hlam]

/-- The middle major main term of page 262 has size at most
`2 (log q1 + 1) D` when the reciprocal phase divided by `q1` is at most `D`.
This does not assert an approximation to the prime sum. -/
theorem middle_major_main_term_bound (q1 : ℕ) (a b lam D : ℝ) (hq1 : 1 ≤ q1)
    (hlam : lam ≠ 0) (hphase : 1 / ((q1 : ℝ) * |lam|) ≤ D) :
    ‖((((ArithmeticFunction.moebius q1 : ℝ) / (q1.totient : ℝ)) : ℂ) *
      ∫ u in a..b, ee (lam * u))‖ ≤ 2 * (Real.log q1 + 1) * D := by
  have hqpos : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have hφ : (0 : ℝ) < q1.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q1)
  have hμ : |(ArithmeticFunction.moebius q1 : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q1)
  have hcoeff :
      ‖((((ArithmeticFunction.moebius q1 : ℝ) / (q1.totient : ℝ)) : ℂ))‖ ≤
        1 / (q1.totient : ℝ) := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hφ]
    exact div_le_div_of_nonneg_right hμ hφ.le
  have hratio : (q1 : ℝ) / q1.totient ≤ 2 * (Real.log q1 + 1) :=
    (div_le_iff₀ hφ).mpr (le_log_mul_totient_wk q1 hq1)
  have hD : 0 ≤ D := le_trans (by positivity) hphase
  rw [norm_mul]
  calc
    _ ≤ (1 / (q1.totient : ℝ)) * (1 / |lam|) :=
      mul_le_mul hcoeff (middle_major_integral_bound a b lam hlam)
        (norm_nonneg _) (by positivity)
    _ = ((q1 : ℝ) / q1.totient) * (1 / ((q1 : ℝ) * |lam|)) := by
      field_simp
    _ ≤ ((q1 : ℝ) / q1.totient) * D :=
      mul_le_mul_of_nonneg_left hphase (by positivity)
    _ ≤ 2 * (Real.log q1 + 1) * D := mul_le_mul_of_nonneg_right hratio hD

/-- The continuous main term has the required logarithmic saving for `q1 ≤ L^c2`.
The lower threshold `c1 ≥ B` does not depend on `c2`; only the multiplicative constant does.
This still does not estimate the error in approximating the prime sum. -/
theorem middle_major_main_term_log_bound (q1 : ℕ) (a b lam L A B c1 c2 : ℝ)
    (hq1 : 1 ≤ q1) (hlam : lam ≠ 0) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hc1 : B ≤ c1) (hc2 : 0 < c2) (hqL : (q1 : ℝ) ≤ L ^ c2)
    (hphase : 1 / ((q1 : ℝ) * |lam|) ≤ 2 * A * L ^ (-c1 - 1)) :
    ‖((((ArithmeticFunction.moebius q1 : ℝ) / (q1.totient : ℝ)) : ℂ) *
      ∫ u in a..b, ee (lam * u))‖ ≤ 4 * (c2 + 1) * A * L ^ (-B) := by
  have hLpos : 0 < L := by linarith
  have hqpos : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have hlogq : Real.log q1 ≤ c2 * Real.log L := by
    calc
      Real.log q1 ≤ Real.log (L ^ c2) := Real.log_le_log hqpos hqL
      _ = c2 * Real.log L := Real.log_rpow hLpos c2
  have hlog : Real.log q1 + 1 ≤ (c2 + 1) * L := by
    nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hLpos) hc2.le]
  have hscale : L * L ^ (-c1 - 1) = L ^ (-c1) := by
    rw [Real.rpow_sub hLpos, Real.rpow_one]
    field_simp
  have hpow : L ^ (-c1) ≤ L ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  refine (middle_major_main_term_bound q1 a b lam _ hq1 hlam hphase).trans ?_
  calc
    2 * (Real.log q1 + 1) * (2 * A * L ^ (-c1 - 1)) =
        4 * A * (Real.log q1 + 1) * L ^ (-c1 - 1) := by ring
    _ ≤ 4 * A * ((c2 + 1) * L) * L ^ (-c1 - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity))
        (Real.rpow_nonneg hLpos.le _)
    _ = 4 * (c2 + 1) * A * (L * L ^ (-c1 - 1)) := by ring
    _ = 4 * (c2 + 1) * A * L ^ (-c1) := by rw [hscale]
    _ ≤ 4 * (c2 + 1) * A * L ^ (-B) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)

/-- LEAF: page 262 last display, the major arc case of the middle range, not argued in the paper:
`α = a₁/q₁ + λ₁` with `q₁ < L^{c₂}`, `|λ₁| ≤ 1/(q₁ τ₁)` and `|λ₁| ≥ 1/(q q₁) - 1/(q τ)` for some
`L^{c₂} ≤ q ≤ τ`, so `|λ₁| ≫ 1/(q₁ τ)`. Cut into blocks of length about `N^{2/3}`; on each block
use the Siegel and Walfisz theorem in short intervals when `|λ₁| N^{2/3} ≤ L^{B+1}`, and Theorem 3
of the paper otherwise; the main terms sum to `(μ(q₁)/φ(q₁)) ∫ e(λ₁ u) du ≪ (q₁/φ(q₁)) τ`, which
is `≪ A L^{-c₁-1} log L`. Needs `c₁` large in terms of `B`. Class HARD. -/
theorem middle_major_est_leaf : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∀ c2 : ℝ, 0 < c2 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α : ℝ) (q : ℕ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ),
      N₀ ≤ N → (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
      Real.log N ^ c2 ≤ q → (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) →
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 → (q1 : ℝ) < Real.log N ^ c2 →
      1 / ((q : ℝ) * q1) - 1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) ≤ |lam1| →
      ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B) := by
  intro B hB
  suffices herr : ∃ c1e : ℝ, ∀ c1 ≥ c1e, ∀ c2 : ℝ, 0 < c2 → ∃ E N₁ : ℝ,
      ∀ (N : ℕ) (A α : ℝ) (q : ℕ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ),
        N₁ ≤ N → (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
        Real.log N ^ c2 ≤ q → (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) →
        Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 →
        (q1 : ℝ) < Real.log N ^ c2 →
        1 / ((q : ℝ) * q1) -
          1 / ((q : ℝ) * (A ^ 2 / N * Real.log N ^ (-c1))) ≤ |lam1| →
        ‖Sexp α N A -
          (((ArithmeticFunction.moebius q1 : ℝ) / (q1.totient : ℝ) : ℂ) *
            ∫ u in ((N : ℝ) - A)..(N : ℝ), ee (lam1 * u))‖ ≤
          E * A * Real.log N ^ (-B) by
    obtain ⟨c1e, herr⟩ := herr
    refine ⟨max c1e B, ?_⟩
    intro c1 hc1 c2 hc2
    obtain ⟨E, N₁, herr⟩ := herr c1 ((le_max_left _ _).trans hc1) c2 hc2
    refine ⟨E + 4 * (c2 + 1), max N₁ 3, ?_⟩
    intro N A α q a1 q1 lam1 hN hlo hhi hq hqτ hcond hq1 hsep
    have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
    have hL1 : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hNpos]
      linarith [Real.exp_one_lt_d9]
    have hApos : 0 < A := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hlo
    have hqpos : (0 : ℝ) < q :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hq
    have hqn : 0 < q := by exact_mod_cast hqpos
    obtain ⟨hlam, hphase⟩ :=
      middle_major_phase_scale N A α c1 q a1 q1 lam1 (by linarith)
        hlo hhi hqn hqτ hcond hsep
    have hmain := middle_major_main_term_log_bound q1 ((N : ℝ) - A) N lam1
      (Real.log N) A B c1 c2 hcond.2.2.2.1 (abs_pos.mp hlam) hL1 hApos.le
      ((le_max_right _ _).trans hc1) hc2 hq1.le hphase
    have herror := herr N A α q a1 q1 lam1 ((le_max_left _ _).trans hN)
      hlo hhi hq hqτ hcond hq1 hsep
    let M : ℂ := ((ArithmeticFunction.moebius q1 : ℝ) / (q1.totient : ℝ) : ℂ) *
      ∫ u in ((N : ℝ) - A)..(N : ℝ), ee (lam1 * u)
    calc
      ‖Sexp α N A‖ ≤ ‖Sexp α N A - M‖ + ‖M‖ := by
        simpa using norm_add_le (Sexp α N A - M) M
      _ ≤ E * A * Real.log N ^ (-B) +
          4 * (c2 + 1) * A * Real.log N ^ (-B) := add_le_add herror hmain
      _ = (E + 4 * (c2 + 1)) * A * Real.log N ^ (-B) := by ring
  -- The remaining input is the uniform short interval prime sum error estimate.
  sorry

/-- Page 262 last display, the major arc case of the middle range from the separation
`cond12_sep` and the LEAF `middle_major_est_leaf`. PROVED; same statement as
`middle_major_leaf` of MiddleSplit1124.lean. -/
theorem middle_major_of_est : ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∀ c2 : ℝ, 0 < c2 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) (a1 : ℤ) (q1 : ℕ) (lam1 : ℝ),
      N₀ ≤ N → (N : ℝ) ^ (2 / 3 : ℝ) ≤ A → A ≤ (N : ℝ) / Real.log N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam → Real.log N ^ c2 ≤ q →
      Cond12 α ((N : ℝ) ^ (1 / 3 : ℝ) / 4 * Real.log N ^ (-c1)) a1 q1 lam1 →
      (q1 : ℝ) < Real.log N ^ c2 → ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B) := by
  intro B hB
  obtain ⟨c1m, h⟩ := middle_major_est_leaf B hB
  refine ⟨c1m, fun c1 hc1 c2 hc2 => ?_⟩
  obtain ⟨K, N₀, h'⟩ := h c1 hc1 c2 hc2
  refine ⟨K, N₀, fun N A α lam a q a1 q1 lam1 hN hlo hhi hc hq hc' hq1 => ?_⟩
  have hlt : q1 < q := by
    have : (q1 : ℝ) < q := lt_of_lt_of_le hq1 hq
    exact_mod_cast this
  exact h' N A α q a1 q1 lam1 hN hlo hhi hq hc.2.2.2.2 hc' hq1
    (cond12_sep α _ _ lam lam1 a a1 q q1 hc hc' hlt)

end

end LeanLab.Zhan1991
