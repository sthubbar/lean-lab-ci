/-
Split of the damped convolution estimate at the unit modulus, at one residual and one
modulus.

The target bounds the size of the exponentially damped convolution of the residual by a
constant times N times the thirteenth power of the logarithm of N times the sum of the
two scale errors. The damping is the exponential of minus the residual over N, and the
residual lies between four and N.

The estimate of the convolution itself is elementary. The convolution is a sum of
reciprocals of products of two logarithms, taken over the integers from two up to the
residual minus two. Every term of that sum is nonnegative, because both logarithms in
its denominator are logarithms of integers which are at least two. Every such product is
at least the square of the logarithm of two, and the sum has fewer than the residual
many terms, so the whole convolution is at most the residual divided by the square of
the logarithm of two. Those two facts are the first two leaves.

The exponential damping is at most one, since the residual is nonnegative. That step is
proved outright below, together with the product of the two estimates, so no leaf states
it, and the size of the damped convolution is at most N divided by the square of the
logarithm of two.

What is left is the scale comparison: for large N the thirteenth power of the logarithm
of N outgrows every fixed power of N, so N times the sum of the two scale errors at the
unit modulus is at least a fixed positive multiple of N. That comparison mentions N
alone, neither the convolution nor the residual, and it is the third leaf.

The assembly multiplies nothing analytically: it reads the modulus of the real number as
the number itself, applies the estimate of the damped convolution, and then the scale
comparison with the reciprocal of the square of the logarithm of two.
-/
import LeanLab.Linnik1951.SPLIT_local_arc_core_unit1622

namespace LeanLab.Linnik1951

/-- LEAF. Nonnegativity of the convolution. Each summand is a reciprocal of a product of
two logarithms of integers which are both at least two, hence is nonnegative, and a sum
of nonnegative summands is nonnegative, so the convolution at a residual of at least four
is nonnegative. This is the step which turns the modulus of the real number into the
number itself, and it carries no damping, no modulus and no scale error. -/
theorem local_arc_core_unit_conv_nonneg1622 (n : ℕ) (hn : 4 ≤ n) :
    0 ≤ logConvolution1622 n := by
  rw [logConvolution1622]
  refine Finset.sum_nonneg ?_
  intro m hm
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm2, hmn⟩ := hm
  have hnm : 2 ≤ n - m := by omega
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
  have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
  have hpos : 0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := mul_pos hmpos hnmpos
  exact div_nonneg zero_le_one hpos.le

/-- LEAF. Size of the convolution. Every denominator in the sum is the product of two
logarithms of integers which are at least two, hence is at least the square of the
logarithm of two, so every summand is at most the reciprocal of that square, and the sum
has fewer than the residual many summands, so the convolution at a residual of at least
four is at most the residual divided by the square of the logarithm of two. This is a
counting estimate on one finite sum, with no damping and no scale error in it. -/
theorem local_arc_core_unit_conv_size1622 (n : ℕ) (hn : 4 ≤ n) :
    logConvolution1622 n ≤ (n : ℝ) / Real.log 2 ^ 2 := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2sq : 0 < Real.log 2 ^ 2 := by positivity
  rw [logConvolution1622]
  have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
      1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / Real.log 2 ^ 2 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm2, hmn⟩ := hm
    have hnm : 2 ≤ n - m := by omega
    have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
    have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
    have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
    have h2le : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have h2le' : Real.log 2 ≤ Real.log ((n - m : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hnm)
    have hprod : Real.log 2 * Real.log 2 ≤ Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) :=
      mul_le_mul h2le h2le' h2pos.le hmpos.le
    have hpos : 0 < Real.log 2 * Real.log 2 := mul_pos h2pos h2pos
    exact one_div_le_one_div_of_le hpos hprod
  have hsum := Finset.sum_le_sum hterm
  have hcard : (Finset.Icc 2 (n - 2)).card = n - 3 := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
  have hcast : ((n - 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : (n - 3 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hpos' : 0 ≤ 1 / Real.log 2 ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_right hcast hpos'
  rw [div_eq_mul_inv]
  linarith

/-- LEAF. The scale comparison. For every positive constant there are a positive constant
and a threshold so that, past the threshold, the first constant times N is at most the
second constant times N times the thirteenth power of the logarithm of N times the sum of
the two scale errors at the unit modulus. This is a statement about N alone: no
convolution, no residual and no exponential damping occurs in it. -/
theorem local_arc_core_unit_scale1622 (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      C * (N : ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by
  refine ⟨C, hC, 3, ?_⟩
  intro N hN
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 3 ≤ N from by omega)
  have hlog : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := by
        have h := Real.exp_one_lt_d9
        linarith
      have h := Real.log_lt_log (Real.exp_pos 1) hexp
      simpa [Real.log_exp] using h
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hN3
    linarith
  have hsum : 0 ≤ 1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) := by
    positivity
  have hlogpow : (1 : ℝ) ≤ Real.log (N : ℝ) ^ 13 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 13
    simpa [pow_one] using this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N from by omega)
  calc C * (N : ℝ) = C * (N : ℝ) * 1 := by ring
    _ ≤ C * (N : ℝ) * (Real.log (N : ℝ) ^ 13) := by
        apply mul_le_mul_of_nonneg_left hlogpow (by positivity)
    _ ≤ C * (N : ℝ) * Real.log (N : ℝ) ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity

/-- The exponential damping is at most one at a nonnegative residual over a positive N, so
the damped convolution at a residual between four and N is at most N divided by the
square of the logarithm of two. -/
private theorem local_arc_core_unit_damped1622 (N n : ℕ) (hN : 0 < N) (hn4 : 4 ≤ n)
    (hnN : n ≤ N) :
    Real.exp (-(n : ℝ) / N) * logConvolution1622 n ≤ (N : ℝ) * (1 / Real.log 2 ^ 2) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hexp : Real.exp (-(n : ℝ) / N) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hNr)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
  have hnle : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hstep : Real.exp (-(n : ℝ) / N) * logConvolution1622 n ≤
      1 * ((n : ℝ) / Real.log 2 ^ 2) :=
    mul_le_mul hexp (local_arc_core_unit_conv_size1622 n hn4)
      (local_arc_core_unit_conv_nonneg1622 n hn4) (by norm_num)
  have hdiv : (n : ℝ) / Real.log 2 ^ 2 ≤ (N : ℝ) / Real.log 2 ^ 2 :=
    div_le_div_of_nonneg_right hnle (le_of_lt hsq)
  calc Real.exp (-(n : ℝ) / N) * logConvolution1622 n
      ≤ 1 * ((n : ℝ) / Real.log 2 ^ 2) := hstep
    _ = (n : ℝ) / Real.log 2 ^ 2 := by ring
    _ ≤ (N : ℝ) / Real.log 2 ^ 2 := hdiv
    _ = (N : ℝ) * (1 / Real.log 2 ^ 2) := by rw [mul_one_div]

/-- The damped convolution estimate at the unit modulus, from the size of the convolution
and the scale comparison. The target statement is unchanged. -/
theorem local_arc_core_unit_main1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall : (0 : ℝ) < 1 / Real.log 2 ^ 2 := by
    have hsq : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
    positivity
  obtain ⟨c, hc, N0, hscale⟩ := local_arc_core_unit_scale1622 (1 / Real.log 2 ^ 2) hsmall
  refine ⟨c, hc, max N0 3, ?_⟩
  intro N hN q hq hqQ hq1 n hn4 hnN
  have hN0' : N0 < N := lt_of_le_of_lt (le_max_left N0 3) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right N0 3) hN
  have hNpos : 0 < N := by omega
  have hn4n : 4 ≤ n.toNat := by omega
  have hntN : n.toNat ≤ N := by omega
  have hdamp := local_arc_core_unit_damped1622 N n.toNat hNpos hn4n hntN
  have hconv : (0 : ℝ) ≤ logConvolution1622 n.toNat :=
    local_arc_core_unit_conv_nonneg1622 n.toNat hn4n
  have hnorm : ‖((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖
      = Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat := by
    rw [Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hconv)]
  rw [hnorm]
  subst hq1
  have hnormR : c * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
      = c * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by
    rw [Nat.cast_one, one_mul]
  rw [hnormR]
  calc Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat
      ≤ (N : ℝ) * (1 / Real.log 2 ^ 2) := hdamp
    _ = (1 / Real.log 2 ^ 2) * (N : ℝ) := by ring
    _ ≤ c * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) :=
        hscale N hN0'

end LeanLab.Linnik1951
