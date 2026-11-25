/-
Helpers for `leaf_large_exponent` in SPLIT_lemma10_large_L, P0069 page 24, the exponent count of
Lemma 10 in the case L > qT. Two proved pieces:
`p3_eventually`, the asymptotic input: for x large, L >= 1 and a fixed power of L is at most
x^delta and at most T0 = exp(L^(1/3)).
`p3_alg`, the pure algebra: with those size bounds the product
(L^B + 2 Ll^(1/2)/T) L^B' (qT+M)^(1/2) (qT+N)^(1/2) is at most C x^(1/2) / L^A.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Real Filter Asymptotics

/-- Proved helper: for x large, 1 <= L x, 1 <= x, and (L^h)^2 is at most x^delta and at most
T0 x = exp(L^(1/3)). -/
theorem p3_eventually (h δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, 1 ≤ L x ∧ 1 ≤ x ∧ (L x ^ h) ^ 2 ≤ x ^ δ ∧ (L x ^ h) ^ 2 ≤ T0 x := by
  have e1 : ∀ᶠ x in atTop, Real.exp 1 ≤ x := eventually_ge_atTop _
  have e2 := (isLittleO_log_rpow_rpow_atTop (2 * h) hδ).bound one_pos
  have e3 := ((isLittleO_rpow_exp_atTop (6 * h)).comp_tendsto
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp Real.tendsto_log_atTop)).bound
    one_pos
  filter_upwards [e1, e2, e3] with x hx h2 h3
  have hex : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx1 : 1 ≤ x := hex.trans hx
  have hl : 1 ≤ L x := by
    unfold L
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hx
  have hl0 : 0 ≤ L x := by linarith
  have key : L x ^ (2 * h) = (L x ^ h) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hl0, Real.rpow_two]
  refine ⟨hl, hx1, ?_, ?_⟩
  · rw [← key]
    have hn1 : ‖Real.log x ^ (2 * h)‖ = Real.log x ^ (2 * h) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (show 0 ≤ Real.log x from hl0) _)
    have hn2 : ‖x ^ δ‖ = x ^ δ := Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)
    rw [hn1, hn2, one_mul] at h2
    exact h2
  · rw [← key]
    simp only [Function.comp_apply] at h3
    have hlg : 0 ≤ Real.log x := hl0
    have hk : (Real.log x ^ (1 / 3 : ℝ)) ^ (6 * h) = Real.log x ^ (2 * h) := by
      rw [← Real.rpow_mul hlg]
      congr 1
      ring
    have hn1 : ‖(Real.log x ^ (1 / 3 : ℝ)) ^ (6 * h)‖ = Real.log x ^ (2 * h) := by
      rw [hk]; exact Real.norm_of_nonneg (Real.rpow_nonneg hlg _)
    have hn2 : ‖Real.exp (Real.log x ^ (1 / 3 : ℝ))‖ = Real.exp (Real.log x ^ (1 / 3 : ℝ)) :=
      Real.norm_of_nonneg (Real.exp_pos _).le
    rw [hn1, hn2, one_mul] at h3
    exact h3

/-- Proved helper: a nonnegative a with a^2 at most b^2, b nonnegative, has a at most b. -/
theorem p3_le_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  calc a = √(a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ √(b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

/-- Proved helper: for 1 <= x, x^a x^b x^c <= x^d when a + b + c <= d. -/
theorem p3_xpow3 {x a b c d : ℝ} (hx : 1 ≤ x) (h : a + b + c ≤ d) :
    x ^ a * x ^ b * x ^ c ≤ x ^ d := by
  have hx0 : 0 < x := by linarith
  rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- Proved helper, the algebra of page 24 in the case L > qT. Here beta, beta', gamma, alpha
stand for L^abs B, L^abs B', L^A, L^abs A0, and T0' for T0. -/
theorem p3_alg {x q T M N Λ c2 T0' lB lB' β β' γ α : ℝ}
    (hq : 1 ≤ q) (hqα : q ≤ α) (hT : 2 < T) (hc2 : 0 < c2) (hM : 1 ≤ c2 * M)
    (hN : 1 ≤ c2 * N) (hprod : M * N * Λ = x) (hlarge : q * T < Λ) (hMN : T0' ≤ M * N)
    (hT0 : T0' ≤ T) (hlB0 : 0 ≤ lB) (hlB : lB ≤ β) (hlB'0 : 0 ≤ lB') (hlB' : lB' ≤ β')
    (hβ : 1 ≤ β) (hβ' : 1 ≤ β') (hγ : 0 < γ)
    (hG : (α * (β * β' * γ)) ^ 2 ≤ T0')
    (hP2 : (q * T) ^ 2 * (β * β' * γ) ^ 2 ≤ x) (hPM : q * T * M * (β * β' * γ) ^ 2 ≤ x)
    (hPN : q * T * N * (β * β' * γ) ^ 2 ≤ x) :
    (lB + 2 * √Λ / T) * (lB' * (√(q * T + M) * √(q * T + N))) ≤
      (2 + 2 * √(2 + 2 * c2)) * √x / γ := by
  generalize hDdef' : β * β' * γ = D at hG hP2 hPM hPN
  have hDdef : D = β * β' * γ := hDdef'.symm
  have hββ : 1 ≤ β * β' := one_le_mul_of_one_le_of_one_le hβ hβ'
  have hD : γ ≤ D := by rw [hDdef]; nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le hγ hD
  have hα1 : 1 ≤ α := hq.trans hqα
  have hMpos : 0 < M := pos_of_mul_pos_right (by linarith : 0 < c2 * M) hc2.le
  have hNpos : 0 < N := pos_of_mul_pos_right (by linarith : 0 < c2 * N) hc2.le
  have hqT : 2 < q * T := by nlinarith
  have hΛ : 0 < Λ := by linarith
  have hx : 0 < x := by rw [← hprod]; positivity
  have hT0' : 0 ≤ T := by linarith
  have hD2α : D ^ 2 ≤ (α * D) ^ 2 := by
    rw [mul_pow]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hα1)
  have hD2T : D ^ 2 ≤ T := (hD2α.trans hG).trans hT0
  have hTqT : T ≤ q * T := le_mul_of_one_le_left hT0' hq
  have hMN2 : M * N * D ^ 2 ≤ x := by
    have h1 : M * N * D ^ 2 ≤ M * N * (q * T) :=
      mul_le_mul_of_nonneg_left (hD2T.trans hTqT) (by positivity)
    have h2 : M * N * (q * T) < M * N * Λ := mul_lt_mul_of_pos_left hlarge (by positivity)
    linarith
  have h4 : (q * T + M) * (q * T + N) * D ^ 2 ≤ 4 * x := by
    have e : (q * T + M) * (q * T + N) * D ^ 2 = (q * T) ^ 2 * D ^ 2 + q * T * M * D ^ 2 +
        q * T * N * D ^ 2 + M * N * D ^ 2 := by ring
    rw [e]; linarith
  generalize hSdef' : √(q * T + M) * √(q * T + N) = S
  have hSdef : S = √(q * T + M) * √(q * T + N) := hSdef'.symm
  have hβ0 : 0 ≤ β := by linarith
  have hβ'0 : 0 ≤ β' := by linarith
  have hPM0 : 0 ≤ q * T + M := by positivity
  have hPN0 : 0 ≤ q * T + N := by positivity
  have hSnn : 0 ≤ S := by rw [hSdef]; positivity
  have hsq4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hS1 : S * D ≤ 2 * √x := by
    apply p3_le_of_sq_le (by positivity) (by positivity)
    have hl : (S * D) ^ 2 = (q * T + M) * (q * T + N) * D ^ 2 := by
      rw [hSdef, mul_pow, mul_pow, Real.sq_sqrt hPM0, Real.sq_sqrt hPN0]
    have hr : (2 * √x) ^ 2 = 4 * x := by
      rw [mul_pow, Real.sq_sqrt hx.le]; norm_num
    rw [hl, hr]; exact h4
  -- second factor
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (β' * γ) ^ 2 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; exact sq_nonneg _
  have hED : E ≤ D ^ 2 := by
    rw [hEdef, hDdef]
    have hb : β' * γ ≤ β * β' * γ := by nlinarith
    exact pow_le_pow_left₀ (by positivity) hb 2
  have hΛM : Λ * M ≤ c2 * x := by
    calc Λ * M = Λ * M * 1 := by ring
      _ ≤ Λ * M * (c2 * N) := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = c2 * x := by rw [← hprod]; ring
  have hΛN : Λ * N ≤ c2 * x := by
    calc Λ * N = Λ * N * 1 := by ring
      _ ≤ Λ * N * (c2 * M) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = c2 * x := by rw [← hprod]; ring
  have hαD : α * D ^ 2 ≤ (α * D) ^ 2 := by
    rw [mul_pow, sq α]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hα1) (sq_nonneg _)
  have hqE : q * E ≤ T := by
    have h1 : q * E ≤ α * D ^ 2 := mul_le_mul hqα hED hE0 (by linarith)
    linarith
  have hq2E : q ^ 2 * E ≤ T0' := by
    have h1 : q ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (by linarith) hqα 2
    have h2 : q ^ 2 * E ≤ α ^ 2 * D ^ 2 := mul_le_mul h1 hED hE0 (by positivity)
    rw [mul_pow] at hG
    linarith
  have hΛT0 : Λ * T0' ≤ x := by
    rw [← hprod, mul_comm (M * N) Λ]
    exact mul_le_mul_of_nonneg_left hMN hΛ.le
  have hT1 : T ≤ T ^ 2 := by nlinarith
  have t1 : Λ * (q * T) ^ 2 * E ≤ x * T ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hq2E hΛ.le
    calc Λ * (q * T) ^ 2 * E = (Λ * (q ^ 2 * E)) * T ^ 2 := by ring
      _ ≤ x * T ^ 2 := mul_le_mul_of_nonneg_right (h.trans hΛT0) (sq_nonneg _)
  have t2 : Λ * (q * T) * M * E ≤ c2 * x * T ^ 2 := by
    calc Λ * (q * T) * M * E = (q * E) * T * (Λ * M) := by ring
      _ ≤ T * T * (c2 * x) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hqE hT0') hΛM (by positivity) (by positivity)
      _ = c2 * x * T ^ 2 := by ring
  have t3 : Λ * (q * T) * N * E ≤ c2 * x * T ^ 2 := by
    calc Λ * (q * T) * N * E = (q * E) * T * (Λ * N) := by ring
      _ ≤ T * T * (c2 * x) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hqE hT0') hΛN (by positivity) (by positivity)
      _ = c2 * x * T ^ 2 := by ring
  have t4 : Λ * M * N * E ≤ x * T ^ 2 := by
    have hET : E ≤ T := hED.trans hD2T
    calc Λ * M * N * E = x * E := by rw [← hprod]; ring
      _ ≤ x * T := mul_le_mul_of_nonneg_left hET hx.le
      _ ≤ x * T ^ 2 := mul_le_mul_of_nonneg_left hT1 hx.le
  have key : Λ * ((q * T + M) * (q * T + N)) * E ≤ (2 + 2 * c2) * T ^ 2 * x := by
    have e : Λ * ((q * T + M) * (q * T + N)) * E = Λ * (q * T) ^ 2 * E +
        Λ * (q * T) * M * E + Λ * (q * T) * N * E + Λ * M * N * E := by ring
    rw [e]; linarith [t1, t2, t3, t4]
  have hS2 : √Λ * S * (β' * γ) ≤ √(2 + 2 * c2) * T * √x := by
    apply p3_le_of_sq_le (by positivity) (by positivity)
    have hl : (√Λ * S * (β' * γ)) ^ 2 = Λ * ((q * T + M) * (q * T + N)) * E := by
      rw [hEdef, hSdef]
      simp only [mul_pow]
      rw [Real.sq_sqrt hΛ.le, Real.sq_sqrt hPM0, Real.sq_sqrt hPN0]
    have hr : (√(2 + 2 * c2) * T * √x) ^ 2 = (2 + 2 * c2) * T ^ 2 * x := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 + 2 * c2 by positivity), Real.sq_sqrt hx.le]
    rw [hl, hr]; exact key
  have hTpos : 0 < T := by linarith
  have e1 : lB * (lB' * S) ≤ β * (β' * S) :=
    mul_le_mul hlB (mul_le_mul_of_nonneg_right hlB' hSnn) (by positivity) (by linarith)
  have e2 : 2 * √Λ / T * (lB' * S) ≤ 2 * √Λ / T * (β' * S) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlB' hSnn) (by positivity)
  rw [le_div_iff₀ hγ]
  have f1 : β * (β' * S) * γ = S * D := by rw [hDdef]; ring
  have f2 : 2 * √Λ / T * (β' * S) * γ = 2 / T * (√Λ * S * (β' * γ)) := by ring
  have f3 : 2 / T * (√Λ * S * (β' * γ)) ≤ 2 / T * (√(2 + 2 * c2) * T * √x) :=
    mul_le_mul_of_nonneg_left hS2 (by positivity)
  have f4 : 2 / T * (√(2 + 2 * c2) * T * √x) = 2 * √(2 + 2 * c2) * √x := by
    field_simp
  calc (lB + 2 * √Λ / T) * (lB' * S) * γ
      = lB * (lB' * S) * γ + 2 * √Λ / T * (lB' * S) * γ := by ring
    _ ≤ β * (β' * S) * γ + 2 * √Λ / T * (β' * S) * γ :=
        add_le_add (mul_le_mul_of_nonneg_right e1 hγ.le) (mul_le_mul_of_nonneg_right e2 hγ.le)
    _ ≤ 2 * √x + 2 * √(2 + 2 * c2) * √x := by rw [f1, f2]; linarith
    _ = (2 + 2 * √(2 + 2 * c2)) * √x := by ring

#print axioms p3_eventually
#print axioms p3_le_of_sq_le
#print axioms p3_xpow3
#print axioms p3_alg

end LeanLab.BakerHarmanPintz1997
