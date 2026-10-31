/-
AI-written Lean code, Claude, 2026-10-21, session 20261021T0117Z-cloud55, unit U-6787.
P0072 Togashi and Uchiyama 1964, On the Representation of Large Even Integers as Sums of Two
Almost Primes. I, J. Fac. Sci. Hokkaido Univ. 18, pp. 60 to 68, lab copy papers/P0072.pdf.

This file closes the explicit real-variable steps of Sections 1, 3 and 4 that the earlier
files TogashiUchiyama.lean and TogashiUchiyamaBrun.lean left open.

PROVED here:
* p. 62, Lemma 2 proof: the finite product identity
  ∏_{2<p≤x} (1 - 2/p) = 4 ∏_{2<p≤x} p(p-2)/(p-1)² · ∏_{p≤x} (1 - 1/p)², `lemma2_prod_identity`,
  and the constant bookkeeping A_N = (2 e^{2C} C_N)⁻¹, `lemma2_constant`.
* p. 64: 2/(p-2) · C_{pN} = 2/p · C_N, `CpN_identity`; the main term of W_q for a > 1,
  a² - 2∫_1^a (a-w)²/w dw = (2a-1)² - 2a² log a, `integral_identity`, `Wq_main_identity`;
  and 2/(q W_q) turns into A_N C_ε(t)/q, `Ceps_from_Wq`.
* p. 65: the denominator of C_ε(t) is positive for 0 < a ≤ 3, `D_pos`, the two branches agree
  at a = 1, `D_one`, and D is strictly increasing on (0, 3], `D_strictMonoOn`; hence C_ε(t)
  is positive and strictly decreasing for t > (1-2ε)⁻¹, `Ceps_pos`, `Ceps_strictAntiOn`.
* p. 66, Lemma 6 in full: the expansion of h₁ = 1/h, its three derivative formulas,
  h₁'(2) = -1, h₁'' < 0 and h₁ > 0 on [2, 2.5], and h positive and convex on [2, 2.5],
  `lemma6_pos`, `lemma6_convex`.

Not proved here: Buhštab's constants 196.0022, 144.1328, 98.0, 101.6 and 26.4612 of Section 2,
whose method, reference [1], is not printed; the sieve inequalities and Mertens type sums,
which stay cited. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimeSums.TogashiUchiyama

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex

open LeanLab.AlmostPrimeSums.TogashiUchiyama (q h)

/-! ### Elementary logarithm bounds -/

lemma log_le_div_e {a : ℝ} (ha : 0 < a) : log a ≤ a / exp 1 := by
  have he : 0 < exp 1 := exp_pos 1
  have := log_le_sub_one_of_pos (div_pos ha he)
  rw [log_div ha.ne' he.ne', log_exp] at this
  linarith

lemma e_gt : (2.718 : ℝ) < exp 1 := by have := exp_one_gt_d9; norm_num at this ⊢; linarith

/-! ### p. 65: the denominator of C_ε -/

/-- q is positive on [1, 3]. -/
theorem q_pos {a : ℝ} (h1 : 1 ≤ a) (h3 : a ≤ 3) : 0 < q a := by
  have he := e_gt
  have hep : 0 < exp 1 := exp_pos 1
  have hl := log_le_div_e (show 0 < a by linarith)
  have hl' : 2 * a ^ 2 * log a ≤ 2 * a ^ 2 * (a / exp 1) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have key : 2 * a ^ 3 < exp 1 * (2 * a - 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3)) (sub_nonneg.2 h1),
      mul_pos (sub_pos.2 he) (show (0 : ℝ) < (2 * a - 1) ^ 2 by nlinarith)]
  have : 2 * a ^ 2 * (a / exp 1) < (2 * a - 1) ^ 2 := by
    rw [show 2 * a ^ 2 * (a / exp 1) = 2 * a ^ 3 / exp 1 by ring, div_lt_iff₀ hep]; linarith
  unfold q; linarith

/-- The derivative of q, (2a-1)² - 2a² log a, is 6a - 4 - 4a log a. -/
lemma hasDerivAt_q {a : ℝ} (ha : 0 < a) :
    HasDerivAt q (6 * a - 4 - 4 * a * log a) a := by
  have hl := hasDerivAt_log ha.ne'
  have h1 : HasDerivAt (fun s : ℝ => (2 * s - 1) ^ 2) (2 * (2 * a - 1) * 2) a := by
    have := (((hasDerivAt_id a).const_mul 2).sub_const 1).pow 2
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun s : ℝ => 2 * s ^ 2 * log s) (2 * (2 * a) * log a + 2 * a ^ 2 * a⁻¹) a := by
    have := ((hasDerivAt_pow 2 a).const_mul 2).mul hl
    refine this.congr_deriv ?_
    simp
  have h3 : HasDerivAt (fun s : ℝ => (2 * s - 1) ^ 2 - 2 * s ^ 2 * log s)
      (2 * (2 * a - 1) * 2 - (2 * (2 * a) * log a + 2 * a ^ 2 * a⁻¹)) a := h1.sub h2
  refine h3.congr_deriv ?_
  field_simp; ring

/-- q' > 0 on [1, 3]. -/
theorem q_deriv_pos {a : ℝ} (h1 : 1 ≤ a) (h3 : a ≤ 3) : 0 < 6 * a - 4 - 4 * a * log a := by
  have he := e_gt
  have hep : 0 < exp 1 := exp_pos 1
  have hl := log_le_div_e (show 0 < a by linarith)
  have hl' : 4 * a * log a ≤ 4 * a * (a / exp 1) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have key : 4 * a ^ 2 < exp 1 * (6 * a - 4) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3)]
  have : 4 * a * (a / exp 1) < 6 * a - 4 := by
    rw [show 4 * a * (a / exp 1) = 4 * a ^ 2 / exp 1 by ring, div_lt_iff₀ hep]; linarith
  linarith

theorem q_strictMonoOn : StrictMonoOn q (Set.Icc (1 : ℝ) 3) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 1 3)
  · intro x hx
    exact (hasDerivAt_q (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_q (by linarith [hx.1])).deriv]
    exact q_deriv_pos hx.1.le hx.2.le

/-- The paper's denominator: a² for 0 < a ≤ 1, (2a-1)² - 2a² log a for 1 < a ≤ 3. -/
def D (a : ℝ) : ℝ := if a ≤ 1 then a ^ 2 else q a

/-- The two branches agree at a = 1, so D is continuous there. -/
theorem D_one : q 1 = (1 : ℝ) ^ 2 := by norm_num [q]

theorem D_pos {a : ℝ} (h0 : 0 < a) (h3 : a ≤ 3) : 0 < D a := by
  unfold D; split_ifs with h
  · positivity
  · exact q_pos (by linarith) h3

theorem D_strictMonoOn : StrictMonoOn D (Set.Ioc (0 : ℝ) 3) := by
  intro x hx y hy hxy
  unfold D
  split_ifs with h1 h2 h2
  · nlinarith [hx.1]
  · have : q 1 < q y := q_strictMonoOn ⟨le_rfl, by norm_num⟩ ⟨by linarith, hy.2⟩ (by linarith)
    rw [D_one] at this; nlinarith [hx.1]
  · linarith
  · exact q_strictMonoOn ⟨by linarith, hx.2⟩ ⟨by linarith, hy.2⟩ hxy

/-- The paper's C_ε(t) = 144 e^{2C} / D(a), a = 3(1 - 2ε - 1/t). -/
def Ceps (ε t : ℝ) : ℝ :=
  144 * exp (2 * eulerMascheroniConstant) / D (3 * (1 - 2 * ε - 1 / t))

lemma a_mem {ε t : ℝ} (hε : 0 ≤ ε) (hε1 : 2 * ε < 1) (ht : 1 / (1 - 2 * ε) < t) :
    3 * (1 - 2 * ε - 1 / t) ∈ Set.Ioc (0 : ℝ) 3 := by
  have h12 : 0 < 1 - 2 * ε := by linarith
  have h1t : 0 < 1 / (1 - 2 * ε) := by positivity
  have ht0 : 0 < t := lt_trans h1t ht
  have : 1 / t < 1 - 2 * ε := by
    rw [div_lt_iff₀ ht0]; rw [div_lt_iff₀ h12] at ht; linarith
  have : 0 < 1 / t := by positivity
  constructor <;> linarith

/-- p. 65: C_ε(t) is positive for t > (1-2ε)⁻¹. -/
theorem Ceps_pos {ε t : ℝ} (hε : 0 ≤ ε) (hε1 : 2 * ε < 1) (ht : 1 / (1 - 2 * ε) < t) :
    0 < Ceps ε t := by
  have := a_mem hε hε1 ht
  unfold Ceps; exact div_pos (by positivity) (D_pos this.1 this.2)

/-- p. 65: C_ε(t) is strictly decreasing for t > (1-2ε)⁻¹. -/
theorem Ceps_strictAntiOn {ε : ℝ} (hε : 0 ≤ ε) (hε1 : 2 * ε < 1) :
    StrictAntiOn (Ceps ε) (Set.Ioi (1 / (1 - 2 * ε))) := by
  intro s hs t ht hst
  have h12 : 0 < 1 - 2 * ε := by linarith
  have hs0 : 0 < s := lt_trans (by positivity) (show 1 / (1 - 2 * ε) < s from hs)
  have hmem_s := a_mem hε hε1 hs
  have hmem_t := a_mem hε hε1 ht
  have hlt : 3 * (1 - 2 * ε - 1 / s) < 3 * (1 - 2 * ε - 1 / t) := by
    have : 1 / t < 1 / s := one_div_lt_one_div_of_lt hs0 hst
    linarith
  have hD := D_strictMonoOn hmem_s hmem_t hlt
  have hDs := D_pos hmem_s.1 hmem_s.2
  unfold Ceps
  exact div_lt_div_of_pos_left (by positivity) hDs hD

/-! ### p. 64: the main term of W_q -/

/-- ∫_1^a (a-w)²/w dw = a² log a - 2a(a-1) + (a²-1)/2, the continuous form of
Σ_{z<p≤z^a} 2/p · log²(z^a/p) / log² z that the paper evaluates by Mertens type sums. -/
theorem integral_identity {a : ℝ} (ha : 1 ≤ a) :
    ∫ w in (1 : ℝ)..a, (a - w) ^ 2 / w = a ^ 2 * log a - 2 * a * (a - 1) + (a ^ 2 - 1) / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) a,
      HasDerivAt (fun w => a ^ 2 * log w - 2 * a * w + w ^ 2 / 2) ((a - x) ^ 2 / x) x := by
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h' : HasDerivAt (fun w => a ^ 2 * log w - 2 * a * w + w ^ 2 / 2)
        (a ^ 2 * x⁻¹ - 2 * a * 1 + ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 2) x :=
      (((hasDerivAt_log hx0).const_mul (a ^ 2)).sub
        ((hasDerivAt_id x).const_mul (2 * a))).add ((hasDerivAt_pow 2 x).div_const 2)
    refine h'.congr_deriv ?_
    field_simp; ring
  have hint : IntervalIntegrable (fun w => (a - w) ^ 2 / w) MeasureTheory.volume 1 a := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) continuousOn_id
    intro x hx; rw [Set.uIcc_of_le ha] at hx; simp; linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp; ring

/-- p. 64: a² - 2 (a² log a - 2a(a-1) + (a²-1)/2) = (2a-1)² - 2a² log a. -/
theorem Wq_main_identity (a : ℝ) :
    a ^ 2 - 2 * (a ^ 2 * log a - 2 * a * (a - 1) + (a ^ 2 - 1) / 2) = q a := by
  unfold q; ring

/-- p. 64: with C_{pN} = C_N (p-2)/p for p ∤ N, 2/(p-2) · C_{pN} = 2/p · C_N. -/
theorem CpN_identity {p C : ℝ} (hp : 2 < p) :
    2 / (p - 2) * (C * ((p - 2) / p)) = 2 / p * C := by
  have : p - 2 ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  field_simp

/-- pp. 64 to 65: with W_q = D/36 · C_N L², L = log N, and A_N = (2 e^{2C} C_N)⁻¹,
2/(q W_q) = A_N · (144 e^{2C} / D) / (q L²), the paper's A_N C_ε(t_q)/q · 1/log² N. -/
theorem Ceps_from_Wq {Dv CN L qq : ℝ} (hD : 0 < Dv) (hC : 0 < CN) (hL : 0 < L) (hq : 0 < qq) :
    2 / (qq * (Dv / 36 * CN * L ^ 2)) =
      (2 * exp (2 * eulerMascheroniConstant) * CN)⁻¹ *
        (144 * exp (2 * eulerMascheroniConstant) / Dv) / qq / L ^ 2 := by
  have : exp (2 * eulerMascheroniConstant) ≠ 0 := (exp_pos _).ne'
  field_simp; ring

/-! ### p. 62: Lemma 2 bookkeeping -/

/-- The constant: 4 · T⁻¹ · e^{-2C} · Q⁻¹ = (2 e^{2C} C_N)⁻¹ with C_N = T Q / 8, where
T = ∏_{p>2} (p-1)²/(p(p-2)) and Q = ∏_{p|N, p>2} (p-2)/p. -/
theorem lemma2_constant {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) :
    4 * T⁻¹ * exp (-(2 * eulerMascheroniConstant)) * Q⁻¹ =
      (2 * exp (2 * eulerMascheroniConstant) * (T * Q / 8))⁻¹ := by
  rw [exp_neg]
  have : exp (2 * eulerMascheroniConstant) ≠ 0 := (exp_pos _).ne'
  field_simp; ring

/-- Primes p ≤ x with p > 2. -/
def oddPr (x : ℕ) : Finset ℕ := (range (x + 1)).filter (fun p => p.Prime ∧ 2 < p)

/-- Primes p ≤ x. -/
def pr (x : ℕ) : Finset ℕ := (range (x + 1)).filter Nat.Prime

lemma pr_eq_insert {x : ℕ} (hx : 2 ≤ x) : pr x = insert 2 (oddPr x) := by
  ext p
  simp only [pr, oddPr, mem_filter, mem_range, mem_insert]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h2.eq_two_or_odd' with rfl | ho
    · left; rfl
    · right; refine ⟨h1, h2, ?_⟩
      have := h2.two_le
      rcases Nat.lt_or_ge 2 p with h | h
      · exact h
      · have : p = 2 := by omega
        subst this; exact absurd ho (by decide)
  · rintro (rfl | ⟨h1, h2, _⟩)
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨h1, h2⟩

/-- p. 62, Lemma 2 proof: for x ≥ 2,
∏_{2<p≤x} (1 - 2/p) = 4 ∏_{2<p≤x} p(p-2)/(p-1)² · ∏_{p≤x} (1 - 1/p)². -/
theorem lemma2_prod_identity {x : ℕ} (hx : 2 ≤ x) :
    ∏ p ∈ oddPr x, (1 - 2 / (p : ℝ)) =
      4 * (∏ p ∈ oddPr x, ((p : ℝ) * (p - 2) / (p - 1) ^ 2)) *
        ∏ p ∈ pr x, (1 - 1 / (p : ℝ)) ^ 2 := by
  have h2 : (2 : ℕ) ∉ oddPr x := by simp [oddPr]
  rw [pr_eq_insert hx, prod_insert h2]
  have hterm : ∀ p ∈ oddPr x, (1 - 2 / (p : ℝ)) =
      ((p : ℝ) * (p - 2) / (p - 1) ^ 2) * (1 - 1 / (p : ℝ)) ^ 2 := by
    intro p hp
    simp only [oddPr, mem_filter] at hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast hp.2.2
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [prod_congr rfl hterm, prod_mul_distrib]
  push_cast; ring

/-! ### p. 66: Lemma 6 in full -/

/-- h₁ = 1/h = (3 - s) q(s). -/
def h1 (s : ℝ) : ℝ := (3 - s) * q s

/-- The paper's expansion of h₁. -/
theorem h1_expand (s : ℝ) :
    h1 s = -4 * s ^ 3 + 16 * s ^ 2 - 13 * s + 3 + 2 * s ^ 3 * log s - 6 * s ^ 2 * log s := by
  unfold h1 q; ring

def h1d (s : ℝ) : ℝ := -10 * s ^ 2 + 26 * s - 13 + 6 * s ^ 2 * log s - 12 * s * log s
def h1dd (s : ℝ) : ℝ := -14 * s + 14 + 12 * s * log s - 12 * log s
def h1ddd (s : ℝ) : ℝ := -2 + 12 * log s - 12 / s

theorem hasDerivAt_h1 {s : ℝ} (hs : 0 < s) : HasDerivAt h1 (h1d s) s := by
  have hl := hasDerivAt_log hs.ne'
  have e : h1 = fun s => -4 * s ^ 3 + 16 * s ^ 2 - 13 * s + 3 + 2 * s ^ 3 * log s
      - 6 * s ^ 2 * log s := funext h1_expand
  rw [e]
  have h' : HasDerivAt (fun s : ℝ => -4 * s ^ 3 + 16 * s ^ 2 - 13 * s + 3 + 2 * s ^ 3 * log s
      - 6 * s ^ 2 * log s)
      (-4 * (((3 : ℕ) : ℝ) * s ^ (3 - 1)) + 16 * (((2 : ℕ) : ℝ) * s ^ (2 - 1)) - 13 * 1
        + (2 * (((3 : ℕ) : ℝ) * s ^ (3 - 1)) * log s + 2 * s ^ 3 * s⁻¹)
        - (6 * (((2 : ℕ) : ℝ) * s ^ (2 - 1)) * log s + 6 * s ^ 2 * s⁻¹)) s :=
    (((((((hasDerivAt_pow 3 s).const_mul (-4)).add ((hasDerivAt_pow 2 s).const_mul 16)).sub
      ((hasDerivAt_id s).const_mul 13)).add_const 3).add
        (((hasDerivAt_pow 3 s).const_mul 2).mul hl)).sub (((hasDerivAt_pow 2 s).const_mul 6).mul hl))
  refine h'.congr_deriv ?_
  unfold h1d; field_simp; ring

theorem hasDerivAt_h1d {s : ℝ} (hs : 0 < s) : HasDerivAt h1d (h1dd s) s := by
  have hl := hasDerivAt_log hs.ne'
  have h' : HasDerivAt (fun s : ℝ => -10 * s ^ 2 + 26 * s - 13 + 6 * s ^ 2 * log s
      - 12 * s * log s)
      (-10 * (((2 : ℕ) : ℝ) * s ^ (2 - 1)) + 26 * 1
        + (6 * (((2 : ℕ) : ℝ) * s ^ (2 - 1)) * log s + 6 * s ^ 2 * s⁻¹)
        - (12 * 1 * log s + 12 * s * s⁻¹)) s :=
    ((((((hasDerivAt_pow 2 s).const_mul (-10)).add ((hasDerivAt_id s).const_mul 26)).sub_const
      13).add (((hasDerivAt_pow 2 s).const_mul 6).mul hl)).sub
        (((hasDerivAt_id s).const_mul 12).mul hl))
  refine h'.congr_deriv ?_
  unfold h1dd; field_simp; ring

theorem hasDerivAt_h1dd {s : ℝ} (hs : 0 < s) : HasDerivAt h1dd (h1ddd s) s := by
  have hl := hasDerivAt_log hs.ne'
  have h' : HasDerivAt (fun s : ℝ => -14 * s + 14 + 12 * s * log s - 12 * log s)
      (-14 * 1 + (12 * 1 * log s + 12 * s * s⁻¹) - 12 * s⁻¹) s :=
    ((((hasDerivAt_id s).const_mul (-14)).add_const 14).add
      (((hasDerivAt_id s).const_mul 12).mul hl)).sub (hl.const_mul 12)
  refine h'.congr_deriv ?_
  unfold h1ddd; field_simp; ring

/-- p. 66: h₁'(2) = -1. -/
theorem h1d_two : h1d 2 = -1 := by unfold h1d; ring

lemma log_le_one_of {s : ℝ} (h0 : 0 < s) (hs : s ≤ 2.5) : log s < 1 := by
  have := log_le_div_e h0
  have he := e_gt
  have : s / exp 1 < 1 := by rw [div_lt_one (exp_pos 1)]; linarith
  linarith

/-- p. 66: h₁'' < 0 on [2, 2.5], from h₁''(s) = (s - 1)(12 log s - 14). -/
theorem h1dd_neg {s : ℝ} (h2 : 2 ≤ s) (h25 : s ≤ 2.5) : h1dd s < 0 := by
  have hl := log_le_one_of (by linarith) h25
  have : h1dd s = (s - 1) * (12 * log s - 14) := by unfold h1dd; ring
  rw [this]; nlinarith

/-- p. 66: h₁ > 0 on [2, 2.5]. -/
theorem h1_pos {s : ℝ} (h2 : 2 ≤ s) (h25 : s ≤ 2.5) : 0 < h1 s :=
  mul_pos (by linarith) (q_pos (by linarith) (by linarith))

theorem h1_concaveOn : ConcaveOn ℝ (Set.Icc (2 : ℝ) 2.5) h1 := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) (f' := h1d) (f'' := h1dd)
  · intro x hx; exact (hasDerivAt_h1 (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (hasDerivAt_h1 (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (hasDerivAt_h1d (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (h1dd_neg hx.1.le hx.2.le).le

lemma h_eq (s : ℝ) : h s = 1 / h1 s := rfl

/-- **Lemma 6, positivity**, p. 66. -/
theorem lemma6_pos {s : ℝ} (h2 : 2 ≤ s) (h25 : s ≤ 2.5) : 0 < h s := by
  rw [h_eq]; exact one_div_pos.2 (h1_pos h2 h25)

/-- **Lemma 6, convexity**, p. 66: h is convex on [2, 2.5]. -/
theorem lemma6_convex : ConvexOn ℝ (Set.Icc (2 : ℝ) 2.5) h := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy θ μ hθ hμ hθμ
  have hA := h1_pos hx.1 hx.2
  have hB := h1_pos hy.1 hy.2
  have hc := h1_concaveOn.2 hx hy hθ hμ hθμ
  simp only [smul_eq_mul] at hc ⊢
  rw [h_eq, h_eq, h_eq]
  set A := h1 x
  set B := h1 y
  have hm : 0 < θ * A + μ * B := by
    rcases eq_or_lt_of_le hθ with h0 | h0
    · subst h0; simp at hθμ; subst hθμ; simpa using hB
    · nlinarith [mul_nonneg hμ hB.le]
  have step1 : 1 / h1 (θ * x + μ * y) ≤ 1 / (θ * A + μ * B) :=
    one_div_le_one_div_of_le hm hc
  have step2 : 1 / (θ * A + μ * B) ≤ θ * (1 / A) + μ * (1 / B) := by
    rw [div_le_iff₀ hm]
    have hμ' : μ = 1 - θ := by linarith
    subst hμ'
    have : θ * (1 / A) + (1 - θ) * (1 / B) = (θ * B + (1 - θ) * A) / (A * B) := by
      field_simp
    rw [this, div_mul_eq_mul_div, le_div_iff₀ (mul_pos hA hB)]
    nlinarith [sq_nonneg (A - B), mul_nonneg hθ hμ]
  linarith

/-! ### p. 67: Section 5 assembly, CONDITIONAL ON Lemmas 4 and 5 -/

/-- **Section 5**, p. 67, with the cited sieve results as named hypotheses. Unit M stands for
A_N φ(N)/log² N and E for the error terms. CONDITIONAL ON `lemma4`, Buhštab's lower bound
S₁ > 26.4612 M - E, and on `lemma5`, Lemma 5 with r = 2, S₂ ≤ I/3 · M + E; the inputs I < 79.3026
and S ≥ S₁ - S₂ - S₃ with S₃ ≤ E are the paper's. Conclusion S > 0.027 M - 3E, so S > 0.0269 M
once 3E ≤ 0.0001 M. -/
theorem section5_assembly {S S1 S2 S3 M E I : ℝ} (hM : 0 < M)
    (lemma4 : 26.4612 * M - E < S1) (lemma5 : S2 ≤ I / 3 * M + E) (hI : I < 79.3026)
    (hS3 : S3 ≤ E) (hS : S1 - S2 - S3 ≤ S) : 0.027 * M - 3 * E < S := by
  have : I / 3 * M < 26.4342 * M := by
    have : I / 3 < 26.4342 := by linarith
    exact mul_lt_mul_of_pos_right this hM
  linarith

theorem section5_assembly_0269 {S S1 S2 S3 M E I : ℝ} (hM : 0 < M)
    (lemma4 : 26.4612 * M - E < S1) (lemma5 : S2 ≤ I / 3 * M + E) (hI : I < 79.3026)
    (hS3 : S3 ≤ E) (hS : S1 - S2 - S3 ≤ S) (hE : 3 * E ≤ 0.0001 * M) : 0.0269 * M < S := by
  have := section5_assembly hM lemma4 lemma5 hI hS3 hS
  linarith

end LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex

#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.q_pos
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.D_pos
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.D_strictMonoOn
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.Ceps_pos
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.Ceps_strictAntiOn
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.integral_identity
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.Wq_main_identity
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.CpN_identity
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.Ceps_from_Wq
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.lemma2_constant
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.lemma2_prod_identity
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.hasDerivAt_h1
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.hasDerivAt_h1d
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.hasDerivAt_h1dd
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.h1d_two
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.h1dd_neg
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.lemma6_pos
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.lemma6_convex
#print axioms LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.section5_assembly_0269

/-- Vacuity check: the hypotheses of `section5_assembly_0269` are jointly satisfiable. -/
example : (0.0269 : ℝ) * 1 < 1 :=
  LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex.section5_assembly_0269 (S := 1) (S1 := 27)
    (S2 := 26) (S3 := 0) (M := 1) (E := 0) (I := 78) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
