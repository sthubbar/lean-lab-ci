/-
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Copy: papers/P0099.pdf, Ramaré's own typeset copy,
https://ramare-olivier.github.io/Maths/gap.pdf. Formulas read from rendered page images,
pp. 12, 13, 21, 22 and Sections 7 and 8.

Unit U-6731, session 20261020T1914Z-cloud49. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Contents.
* `theorem3_of_chain`: Theorem 3, the 1/28 314 000 interval for real x > 10 726 905 041,
  CONDITIONAL ON two named inputs: Theorem 2 for x ≥ 10^20 with the Table 1 value
  Δ = 81 353 847, and the Section 7 prime chain certificate below 10^20 with Δ = 28 314 000.
  The chain to real-interval step is proved here.
* `lemma7`: Lemma 7, PROVED.
* `prime_of_theorem4_conclusion`: the last step from Theorem 4's conclusion θ(Y) - θ(Y0) > 0
  to a prime in ]Y(1 - 1/Δ), Y], via Lemma 7, PROVED.
* `norm_fm`, `v_recurrence`: Lemma 6, the first identity of (20) and the recurrence (22) for
  f_m(t) = (4 t (1 - t))^m, PROVED.
-/
import Mathlib
import LeanLab.Common.ThetaWindow

namespace LeanLab.RamareSaouter2003.Smooth
open Real

/-! ### Theorem 3 from Theorem 2 at 10^20 and the Section 7 chain -/

/-- Theorem 2 at x0 = 10^20, Table 1 first row, Δ = 81 353 847. The table row is labelled
`log x0 = 46`, while Theorem 2 asks x0 ≥ 10^20 and log 10^20 = 46.051...; the lab states the
conservative reading, valid for x ≥ 10^20. Cited input, not proved here. -/
def Theorem2At1e20 : Prop :=
  ∀ x : ℝ, (10 : ℝ) ^ 20 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 81353847) < p ∧ (p : ℝ) ≤ x

/-- The Section 7 certificate, in the paper's words: a sequence of primes p_0, ..., p_N with
p_0 above the top U, p_N at or below the bottom L, decreasing, each step
p_{k+1} > p_k (1 - 1/Δ). Sections 7 and 8 report about 400 million such primes, certified by
Pocklington, Brillhart-Lehmer-Selfridge and Jaeschke tests. Cited computation. -/
def ChainCert (L U Δ : ℝ) : Prop :=
  ∃ (N : ℕ) (p : ℕ → ℕ), (∀ k ≤ N, (p k).Prime) ∧ U ≤ (p 0 : ℝ) ∧ (p N : ℝ) ≤ L ∧
    ∀ k < N, (p k : ℝ) * (1 - 1 / Δ) < p (k + 1) ∧ p (k + 1) < p k

/-- A chain certificate gives the real-variable interval statement on ]L, U[. PROVED. -/
theorem interval_of_chain {L U Δ : ℝ} (hΔ : 1 < Δ) (h : ChainCert L U Δ) :
    ∀ x : ℝ, L < x → x < U → ∃ q : ℕ, q.Prime ∧ x * (1 - 1 / Δ) < q ∧ (q : ℝ) ≤ x := by
  intro x hLx hxU
  obtain ⟨N, p, hpr, hU, hL, hstep⟩ := h
  have hex : ∃ k, (p k : ℝ) ≤ x := ⟨N, by linarith⟩
  classical
  let k := Nat.find hex
  have hk : (p k : ℝ) ≤ x := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    have : (p 0 : ℝ) ≤ x := by rw [← h0]; exact hk
    linarith
  have hkN : k ≤ N := Nat.find_min' hex (by linarith)
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjx : x < (p j : ℝ) := by
    have := Nat.find_min hex (show j < k by omega)
    push Not at this
    exact this
  have hjN : j < N := by omega
  have hs := (hstep j hjN).1
  have hpos : 0 < 1 - 1 / Δ := by
    have : 1 / Δ < 1 := by rw [div_lt_one (by linarith)]; exact hΔ
    linarith
  refine ⟨p k, hpr k hkN, ?_, hk⟩
  rw [hj]
  calc x * (1 - 1 / Δ) < (p j : ℝ) * (1 - 1 / Δ) := mul_lt_mul_of_pos_right hjx hpos
    _ < p (j + 1) := hs

/-- Theorem 3 CONDITIONAL ON Theorem 2 at 10^20 and the Section 7 chain from 10^20 down to
10 726 905 041 with Δ = 28 314 000. -/
theorem theorem3_of_chain (h2 : Theorem2At1e20)
    (hc : ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000) :
    ∀ x : ℝ, 10726905041 < x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x := by
  intro x hx
  rcases lt_or_ge x ((10 : ℝ) ^ 20) with hlt | hge
  · exact interval_of_chain (by norm_num) hc x hx hlt
  · obtain ⟨p, hp, hl, hu⟩ := h2 x hge
    refine ⟨p, hp, ?_, hu⟩
    have hx0 : 0 ≤ x := by linarith
    have : x * (1 - 1 / 28314000) ≤ x * (1 - 1 / 81353847) :=
      mul_le_mul_of_nonneg_left (by norm_num) hx0
    linarith

/-! ### Lemma 7 and the last step of Theorem 4 -/

/-- Lemma 7: for a ∈ [0, 1/2], 1 - (1 + m u a)/(1 + m u (1 - a)) e^{-u} ≤ u (1 + (1 - 2a) m).
The paper leaves m ≥ 1 and u ≥ 0 implicit; the lab assumes m ≥ 0 and u ≥ 0. PROVED. -/
theorem lemma7 {m u a : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    1 - (1 + m * u * a) / (1 + m * u * (1 - a)) * Real.exp (-u) ≤ u * (1 + (1 - 2 * a) * m) := by
  have hmu : 0 ≤ m * u := mul_nonneg hm hu
  have hD : 0 < 1 + m * u * (1 - a) := by nlinarith
  have hE : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have hE1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hN : 0 ≤ 1 + m * u * a := by nlinarith
  rw [div_mul_eq_mul_div, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hD]
  -- (1 + m u a) e^{-u} ≥ (1 + m u a)(1 - u), and the rest is polynomial
  have h1 : (1 + m * u * a) * (1 - u) ≤ (1 + m * u * a) * Real.exp (-u) :=
    mul_le_mul_of_nonneg_left hE hN
  nlinarith [mul_nonneg hmu hu, mul_nonneg (mul_nonneg hmu hu) ha0,
    mul_nonneg hmu (show 0 ≤ 1 - 2 * a by linarith),
    mul_nonneg (mul_nonneg hmu (show 0 ≤ 1 - 2 * a by linarith)) (mul_nonneg hmu (show 0 ≤ 1 - a by linarith)),
    mul_nonneg (mul_nonneg hmu hu) (mul_nonneg hmu (show 0 ≤ 1 - a by linarith))]

/-- The last step of Theorem 4 and Theorem 2: if θ(Y) - θ(Y0) > 0 with
Y0 = Y (1 + m u a)/(1 + m u (1 - a)) e^{-u}, the paper's (9), and u (1 + (1 - 2a) m) ≤ 1/Δ,
then ]Y (1 - 1/Δ), Y] holds a prime. PROVED. -/
theorem prime_of_theorem4_conclusion {Y m u a Δ : ℝ} (hY : 0 ≤ Y) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hθ : 0 < Chebyshev.theta Y -
      Chebyshev.theta (Y * ((1 + m * u * a) / (1 + m * u * (1 - a))) * Real.exp (-u)))
    (hΔ : u * (1 + (1 - 2 * a) * m) ≤ 1 / Δ) :
    ∃ p : ℕ, p.Prime ∧ Y * (1 - 1 / Δ) < p ∧ (p : ℝ) ≤ Y := by
  set Y0 := Y * ((1 + m * u * a) / (1 + m * u * (1 - a))) * Real.exp (-u) with hY0
  have hmu : 0 ≤ m * u := mul_nonneg hm hu
  have hD : 0 < 1 + m * u * (1 - a) := by nlinarith
  have hN : 0 ≤ 1 + m * u * a := by nlinarith
  have hY0nn : 0 ≤ Y0 := mul_nonneg (mul_nonneg hY (div_nonneg hN hD.le)) (Real.exp_pos _).le
  obtain ⟨p, hp, hl, hu'⟩ :=
    LeanLab.Common.ThetaWindow.exists_prime_of_theta_lt (y := Y) hY0nn (by linarith)
  refine ⟨p, hp, ?_, hu'⟩
  have h7 := lemma7 hm hu ha0 ha1
  have : Y * (1 - 1 / Δ) ≤ Y0 := by
    have e : Y0 = Y * ((1 + m * u * a) / (1 + m * u * (1 - a)) * Real.exp (-u)) := by
      rw [hY0]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hY
    linarith
  linarith

/-! ### Lemma 6, the test function f_m(t) = (4 t (1 - t))^m -/

/-- The test function (19). -/
noncomputable def fm (m : ℕ) (t : ℝ) : ℝ := (4 * t * (1 - t)) ^ m

/-- The relation behind (22): ((t - 1/2) f_{m+1})' = (2m+3) f_{m+1} - (2m+2) f_m. -/
theorem hasDerivAt_key (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s => (s - 1 / 2) * fm (m + 1) s)
      ((2 * m + 3) * fm (m + 1) t - (2 * m + 2) * fm m t) t := by
  have hq : HasDerivAt (fun s : ℝ => 4 * s * (1 - s)) (4 * (1 - t) + 4 * t * (-1)) t := by
    have h1 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    exact h1.mul h2
  have hp := hq.pow (m + 1)
  have hl : HasDerivAt (fun s : ℝ => s - 1 / 2) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  have h := hl.mul hp
  unfold fm
  convert h using 1
  simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  ring

theorem continuous_fm (m : ℕ) : Continuous (fm m) := by
  unfold fm; fun_prop

/-- The integral form of the key relation over any [α, β]. -/
theorem integral_key (m : ℕ) (α β : ℝ) :
    (2 * m + 3) * (∫ t in α..β, fm (m + 1) t) - (2 * m + 2) * (∫ t in α..β, fm m t) =
      (β - 1 / 2) * fm (m + 1) β - (α - 1 / 2) * fm (m + 1) α := by
  have hc1 := (continuous_fm (m + 1)).intervalIntegrable (μ := MeasureTheory.volume) α β
  have hc0 := (continuous_fm m).intervalIntegrable (μ := MeasureTheory.volume) α β
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hc1.const_mul _) (hc0.const_mul _)]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_key m t)
  exact ((continuous_fm (m + 1)).const_mul _ |>.sub ((continuous_fm m).const_mul _)).intervalIntegrable _ _

theorem fm_zero_left (m : ℕ) : fm (m + 1) 0 = 0 := by simp [fm]
theorem fm_zero_right (m : ℕ) : fm (m + 1) 1 = 0 := by simp [fm]
theorem fm_symm (m : ℕ) (a : ℝ) : fm m (1 - a) = fm m a := by
  unfold fm; ring

/-- Recurrence for ||f_m||_1: (2m+3) ||f_{m+1}||_1 = (2m+2) ||f_m||_1. -/
theorem norm_fm_succ (m : ℕ) :
    (2 * m + 3) * (∫ t in (0 : ℝ)..1, fm (m + 1) t) = (2 * m + 2) * (∫ t in (0 : ℝ)..1, fm m t) := by
  have := integral_key m 0 1
  rw [fm_zero_left, fm_zero_right] at this
  linarith

/-- Lemma 6, first identity of (20): ||f_m||_1 = 2^{2m} m!^2 / (2m+1)!, here written with
∫_0^1 f_m, equal to the L1 norm since f_m ≥ 0 on [0, 1]. PROVED. -/
theorem norm_fm (m : ℕ) :
    (∫ t in (0 : ℝ)..1, fm m t) = 2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 / (2 * m + 1).factorial := by
  induction m with
  | zero => simp [fm]
  | succ m ih =>
    have h := norm_fm_succ m
    have hpos : (0 : ℝ) < 2 * m + 3 := by positivity
    have e : (∫ t in (0 : ℝ)..1, fm (m + 1) t) =
        (2 * m + 2) / (2 * m + 3) * (∫ t in (0 : ℝ)..1, fm m t) := by
      field_simp; linarith
    rw [e, ih]
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring, Nat.factorial_succ (2 * m + 1 + 1),
      Nat.factorial_succ (2 * m + 1), Nat.factorial_succ m]
    push_cast
    have hf : (0 : ℝ) < (2 * m + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    field_simp
    ring

/-- v(f, a) = ∫_0^a f + ∫_{1-a}^1 f, the paper's v. -/
noncomputable def v (f : ℝ → ℝ) (a : ℝ) : ℝ := (∫ t in (0 : ℝ)..a, f t) + ∫ t in (1 - a)..1, f t

/-- Lemma 6, recurrence (22), with m + 1 for the paper's m:
(2m+3) v(f_{m+1}, a) = (2m+2) v(f_m, a) + (2a - 1) f_{m+1}(a). PROVED, for every real a. -/
theorem v_recurrence (m : ℕ) (a : ℝ) :
    (2 * m + 3) * v (fm (m + 1)) a = (2 * m + 2) * v (fm m) a + (2 * a - 1) * fm (m + 1) a := by
  have h1 := integral_key m 0 a
  have h2 := integral_key m (1 - a) 1
  rw [fm_zero_left] at h1
  rw [fm_zero_right, fm_symm] at h2
  unfold v
  linarith

theorem v_fm_zero (a : ℝ) : v (fm 0) a = 2 * a := by
  simp [v, fm]; ring

/-- Section 6, p. 24: w(f_2, a) = v(f_2, a)/||f_2||_1 = 2 a^3 (10 - 15 a + 6 a^2). PROVED from (22)
and (20); this checks the printed formula. -/
theorem w_f2 (a : ℝ) :
    v (fm 2) a / (∫ t in (0 : ℝ)..1, fm 2 t) = 2 * a ^ 3 * (10 - 15 * a + 6 * a ^ 2) := by
  have h0 := v_fm_zero a
  have h1 := v_recurrence 0 a
  have h2 := v_recurrence 1 a
  have hn := norm_fm 2
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, zero_add] at h1 h2
  rw [hn]
  norm_num [Nat.factorial]
  simp only [fm] at h1 h2
  rw [h0] at h1
  norm_num at h2
  rw [div_eq_iff (by norm_num)]
  linear_combination (1 / 5 : ℝ) * h2 + (4 / 15 : ℝ) * h1

/-! ### Theorem 4 as a named input, for f = f_m, and its prime consequence -/

/-- (4), p. 15: s_m(T) = {(1/(m π))(log(T/2π) + 1/m) + (1.34/T)(2 log(T/2π) + 1)}{1 + 10^-5}. -/
noncomputable def sm (m : ℕ) (T : ℝ) : ℝ :=
  ((1 / (m * π)) * (Real.log (T / (2 * π)) + 1 / m) +
    1.34 / T * (2 * Real.log (T / (2 * π)) + 1)) * (1 + 1 / 10 ^ 5)

/-- (8): w(f_m, a) = v(f_m, a)/||f_m||_1. -/
noncomputable def w (m : ℕ) (a : ℝ) : ℝ := v (fm m) a / ∫ t in (0 : ℝ)..1, fm m t

/-- (6): μ*_m(f_m) = ||f_m^(m)||_1/||f_m||_1. -/
noncomputable def muStar (m : ℕ) : ℝ :=
  (∫ t in (0 : ℝ)..1, |iteratedDeriv m (fm m) t|) / ∫ t in (0 : ℝ)..1, fm m t

/-- Theorem 4, p. 17: α3^-1 = (0.99 - 1.0007 α1 - (2.001/α4) w(f, a) - 0.0326/α2)/2.0012. -/
noncomputable def alpha3inv (m : ℕ) (α1 α2 α4 a : ℝ) : ℝ :=
  (0.99 - 1.0007 * α1 - 2.001 / α4 * w m a - 0.0326 / α2) / 2.0012

/-- Theorem 4, p. 18: u = (1.0001/T)(α3 μ*_m(f_m)/m^m · T (s_m(T)/√Y + (s_m(T0)/2)(T/T0)^m))^(1/(m+1)). -/
noncomputable def uRS (m : ℕ) (α1 α2 α4 a Y T T0 : ℝ) : ℝ :=
  1.0001 / T * ((1 / alpha3inv m α1 α2 α4 a) * muStar m / (m : ℝ) ^ m * T *
    (sm m T / √Y + sm m T0 / 2 * (T / T0) ^ m)) ^ ((1 : ℝ) / (m + 1))

/-- Theorem 4 of the paper for the test function f = f_m of (19), as a named input. `NT` is the
zero counting function N(T) of (3) and `T0` the height to which RH is assumed verified; the paper's
proof uses RH to T0, Lemma 1 from Rosser, Brun-Titchmarsh by Montgomery-Vaughan and Schoenfeld's
ψ - θ bounds (11). Not proved here. -/
def Theorem4Fm (NT : ℝ → ℝ) (T0 : ℝ) : Prop :=
  ∀ (m : ℕ) (α1 α2 α4 a Y T : ℝ), 2 ≤ m → 0 < α1 → 1 ≤ α2 → 1 / 2 ≤ α4 → α4 ≤ 1 →
    0 ≤ a → a ≤ 1 / 2 → 0 < alpha3inv m α1 α2 α4 a → 2 * 10 ^ 12 ≤ Y → 1000 ≤ T →
    2 * NT T ≤ α1 * √Y →
    m * uRS m α1 α2 α4 a Y T T0 ≤ 0.0001 →
    α2 ≤ uRS m α1 α2 α4 a Y T T0 * √Y →
    Y ^ α4 ≤ uRS m α1 α2 α4 a Y T T0 * Y → T ≤ T0 →
    uRS m α1 α2 α4 a Y T T0 * Y / (101 * (1 - w m a)) ≤
      Chebyshev.theta Y - Chebyshev.theta (Y * ((1 + m * uRS m α1 α2 α4 a Y T T0 * a) /
        (1 + m * uRS m α1 α2 α4 a Y T T0 * (1 - a))) * Real.exp (-uRS m α1 α2 α4 a Y T T0))

/-- Theorem 4 gives a prime in ]Y(1 - 1/Δ), Y] once u (1 + (1 - 2a) m) ≤ 1/Δ. The positivity
of the right side uses 1 - w(f, a) > 0, which the paper derives from α3 > 0; PROVED here.
CONDITIONAL ON `Theorem4Fm`. -/
theorem prime_of_theorem4 {NT : ℝ → ℝ} {T0 : ℝ} (h4 : Theorem4Fm NT T0)
    {m : ℕ} {α1 α2 α4 a Y T Δ : ℝ} (hm : 2 ≤ m) (hα1 : 0 < α1) (hα2 : 1 ≤ α2)
    (hα4 : 1 / 2 ≤ α4) (hα4' : α4 ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (h3 : 0 < alpha3inv m α1 α2 α4 a) (hY : 2 * 10 ^ 12 ≤ Y) (hT : 1000 ≤ T)
    (hN : 2 * NT T ≤ α1 * √Y)
    (hmu : m * uRS m α1 α2 α4 a Y T T0 ≤ 0.0001)
    (h2 : α2 ≤ uRS m α1 α2 α4 a Y T T0 * √Y)
    (hY4 : Y ^ α4 ≤ uRS m α1 α2 α4 a Y T T0 * Y) (hTT : T ≤ T0)
    (hΔ : uRS m α1 α2 α4 a Y T T0 * (1 + (1 - 2 * a) * m) ≤ 1 / Δ) :
    ∃ p : ℕ, p.Prime ∧ Y * (1 - 1 / Δ) < p ∧ (p : ℝ) ≤ Y := by
  have key := h4 m α1 α2 α4 a Y T hm hα1 hα2 hα4 hα4' ha0 ha1 h3 hY hT hN hmu h2 hY4 hTT
  set u := uRS m α1 α2 α4 a Y T T0
  have hYpos : 0 < Y := by linarith
  have hsq : 0 < √Y := Real.sqrt_pos.mpr hYpos
  have hu : 0 < u := by
    by_contra hneg
    push Not at hneg
    have : u * √Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hsq.le
    linarith
  have hw : w m a < 1 := by
    unfold alpha3inv at h3
    have hα4pos : 0 < α4 := by linarith
    have hq : 0 < 0.0326 / α2 := div_pos (by norm_num) (by linarith)
    by_contra hge
    push Not at hge
    have : (2.001 : ℝ) ≤ 2.001 / α4 * w m a := by
      have h1 : (2.001 : ℝ) ≤ 2.001 / α4 := by
        rw [le_div_iff₀ hα4pos]; nlinarith
      nlinarith
    have : (0.99 - 1.0007 * α1 - 2.001 / α4 * w m a - 0.0326 / α2) / 2.0012 < 0 := by
      apply div_neg_of_neg_of_pos _ (by norm_num); linarith
    linarith
  have hpos : 0 < u * Y / (101 * (1 - w m a)) := by
    apply div_pos (mul_pos hu hYpos); nlinarith
  exact prime_of_theorem4_conclusion hYpos.le (by positivity) hu.le ha0 ha1
    (by linarith) hΔ

end LeanLab.RamareSaouter2003.Smooth
