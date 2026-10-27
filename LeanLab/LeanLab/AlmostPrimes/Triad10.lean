import Mathlib
import LeanLab.AlmostPrimes.DudekLarge
import LeanLab.ChebyshevExplicit.Psi30

open Real Finset LeanLab.ChebyshevExplicit LeanLab.AlmostPrimes.DudekLarge

namespace LeanLab.AlmostPrimes.Triad10

theorem poly_le_exp_11999 {L : ℝ} (hL : 11999 ≤ L) : 10000 * (L + 1) ^ 5 ≤ exp (L / 20) := by
  set t := L / 20 with ht
  have ht600 : 599 ≤ t := by rw [ht]; linarith
  have h1 : L + 1 ≤ 21 * t := by rw [ht]; linarith
  have h5 : (L + 1) ^ 5 ≤ (21 * t) ^ 5 := pow_le_pow_left₀ (by linarith) h1 5
  have hexp := Real.pow_div_factorial_le_exp t (by linarith : 0 ≤ t) 12
  have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  have h7 : (599 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht600 7
  have ht5 : 0 ≤ t ^ 5 := by positivity
  have hprod : (599 : ℝ) ^ 7 * t ^ 5 ≤ t ^ 7 * t ^ 5 := mul_le_mul_of_nonneg_right h7 ht5
  have h12 : t ^ 12 = t ^ 7 * t ^ 5 := by ring
  have h21 : (21 * t) ^ 5 = 4084101 * t ^ 5 := by ring
  have hdiv : t ^ 12 / 479001600 = t ^ 12 * (1 / 479001600) := by ring
  rw [hdiv] at hexp
  nlinarith

theorem triad10_main (N : ℕ) (hE : Even N) (hN : exp 11999 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  by_contra hno
  have he : (12000 : ℝ) ≤ exp 11999 := by
    have := Real.add_one_le_exp (11999 : ℝ); linarith
  have hNr : (12000 : ℝ) ≤ N := he.trans hN
  have h4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN0 : 0 < N := by omega
  have hN30 : 30 ≤ N := by
    have : (30 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set L := Real.log N with hLdef
  have hL : 11999 ≤ L := by
    have := Real.log_le_log (exp_pos 11999) hN
    rwa [Real.log_exp] at this
  have hLpos : 0 < L := by linarith
  have hexpL : exp L = N := Real.exp_log hNpos
  -- the parameters
  set Q : ℕ := 100 * ⌈L⌉₊ with hQdef
  have hQr : (Q : ℝ) = 100 * (⌈L⌉₊ : ℝ) := by rw [hQdef]; push_cast; ring
  have hceil1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hceil2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hQlo : 100 * L ≤ (Q : ℝ) := by rw [hQr]; linarith
  have hQhi : (Q : ℝ) ≤ 100 * (L + 1) := by rw [hQr]; linarith
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  set z := exp (19 / 20 * L) with hz
  have hlogz : Real.log z = 19 / 20 * L := Real.log_exp _
  have hz1 : 1 < z := by rw [hz]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have hzpos : 0 < z := by linarith
  have hzN : z * exp (L / 20) = N := by
    rw [hz, ← Real.exp_add, ← hexpL]; congr 1; ring
  -- the three estimates
  have hc := card_le_of_no_rep Q hE h4 hno
  have hhead := head_le (Q := Q) hN0 hz1
  have htail := tail_le (N := N) hQ1
  have hpi := pi_ge_chebyshev30 N hN30
  rw [hlogz] at hhead
  rw [← hLdef] at hpi
  -- multiply the head and tail by L
  have hhead1 : 2 * N / (19 / 20 * L) * (3 / 10) * L = 12 / 19 * N := by
    field_simp; ring
  have hE1 : 1 + 19 / 20 * L ≤ L + 1 := by linarith
  have hE3 : (1 + 19 / 20 * L) ^ 3 ≤ (L + 1) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hE1 3
  have hpoly := poly_le_exp_11999 hL
  have hE2 : (Q : ℝ) * (4 * z * (1 + 19 / 20 * L) ^ 3) * L ≤ 4 / 100 * N := by
    have hA : (Q : ℝ) * L ≤ 100 * (L + 1) * (L + 1) :=
      mul_le_mul hQhi (by linarith) hLpos.le (by positivity)
    have hB : (Q : ℝ) * (4 * z * (1 + 19 / 20 * L) ^ 3) * L
        = 4 * z * ((Q : ℝ) * L) * (1 + 19 / 20 * L) ^ 3 := by ring
    rw [hB]
    calc 4 * z * ((Q : ℝ) * L) * (1 + 19 / 20 * L) ^ 3
        ≤ 4 * z * (100 * (L + 1) * (L + 1)) * (L + 1) ^ 3 := by
          apply mul_le_mul _ hE3 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 4 / 100 * (z * (10000 * (L + 1) ^ 5)) := by ring
      _ ≤ 4 / 100 * (z * exp (L / 20)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hpoly hzpos.le
      _ = 4 / 100 * N := by rw [hzN]
  have htail1 : (N : ℝ) / Q * L ≤ 1 / 100 * N := by
    have hQpos : (0 : ℝ) < Q := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hQpos]
    nlinarith
  -- log (N + 1) + L is tiny next to N
  have hlog1 : Real.log (N + 1) ≤ L + 1 := by
    have h2N : (N : ℝ) + 1 ≤ N * exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith
    calc Real.log (N + 1) ≤ Real.log (N * exp 1) := Real.log_le_log (by linarith) h2N
      _ = L + 1 := by rw [Real.log_mul hNpos.ne' (exp_pos 1).ne', Real.log_exp]
  have hsmall : 2 * L + 1 ≤ 1 / 100 * N := by
    have := Real.quadratic_le_exp_of_nonneg hLpos.le
    rw [hexpL] at this
    nlinarith
  have hlog2 := Real.log_two_gt_d9
  -- combine: π N L ≤ (head + tail + 1) L
  have hcL : (Nat.primeCounting N : ℝ) * L ≤
      (2 * N / (19 / 20 * L) * (3 / 10) + Q * (4 * z * (1 + 19 / 20 * L) ^ 3) + N / Q + 1) * L := by
    apply mul_le_mul_of_nonneg_right _ hLpos.le
    linarith
  have hexp : (2 * N / (19 / 20 * L) * (3 / 10) + Q * (4 * z * (1 + 19 / 20 * L) ^ 3) + N / Q + 1) * L
      = 2 * N / (19 / 20 * L) * (3 / 10) * L + Q * (4 * z * (1 + 19 / 20 * L) ^ 3) * L
        + N / Q * L + L := by ring
  rw [hexp, hhead1] at hcL
  have hcL2 : 0.9212 * N - 5 * L ≤ (Nat.primeCounting N : ℝ) * L := by
    have : (0.9212 * N - 5 * L) / L * L ≤ (Nat.primeCounting N : ℝ) * L := by
      apply mul_le_mul_of_nonneg_right hpi hLpos.le
    rwa [div_mul_cancel₀ _ hLpos.ne'] at this
  nlinarith

-- To avoid normalization issues with large exponents, we define a custom N.
def large_N : ℕ := 40000

end LeanLab.AlmostPrimes.Triad10
