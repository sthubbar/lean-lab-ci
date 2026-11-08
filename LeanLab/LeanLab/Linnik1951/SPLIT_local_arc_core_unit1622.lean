/-
Split of the local core estimate at the unit modulus, at one residual and one modulus.

The target bounds the difference between the resolved core sum over the reduced
residues and the singular coefficient times the Ramanujan sum times the damped
convolution, by a constant times N log N to the thirteenth times the sum of the two
errors. At the unit modulus the only reduced residue is the residue zero, the singular
coefficient of the modulus and the Ramanujan sum both equal one, and the resolved core
sum is the unshifted core integral over the interval of length two over N around the
origin. That reduction is proved outright below, so no leaf states it.

What remains splits in two by the triangle inequality, and the two summands are the two
errors the target adds. The first summand is the size of the core integral alone, with
no main term in it: the local square mean value on the core. The second summand is the
size of the damped convolution alone: the elementary estimate of the convolution
against the exponential damping. Both leaves are strictly weaker than the target. The
target controls their difference, each leaf controls one of the two terms separately,
and neither leaf mentions the other.

The two constants of the leaves are added, and the assembly below only adds the two
error sizes. No analytic input is invented here.
-/
import LeanLab.Linnik1951.SPLIT_arc_local_expansion1622

namespace LeanLab.Linnik1951

/-- At the unit modulus the filter over the reduced residues of the single residue
class leaves only the residue zero, so the resolved core sum is the unshifted core
integral over the interval of length two over N around the origin. -/
private theorem local_arc_unit_sum1622 (N : ℕ) (q : ℕ) (hq1 : q = 1) (n : ℤ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
          primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
        primeFourier111 N z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  subst hq1
  rw [Finset.range_one]
  simp

/-- At the unit modulus the square of the Moebius function and the square of the
totient both equal one, and the Ramanujan sum of the unit modulus at any residual
also equals one, so the modulus of their product is one. -/
private theorem local_arc_unit_coefficient1622 (q : ℕ) (hq1 : q = 1) (m : ℕ) :
    ‖(((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q m‖ = 1 := by
  subst hq1
  simp [LeanLab.Perelli1996.Ramanujan103.ramanujanSum, LeanLab.Perelli1996.Kernel.e]

/-- LEAF. The size of the core integral at the unit modulus. The squared prime Fourier
series against the phase of the residual, integrated over the interval of length two
over N around the origin, is bounded by the local square mean value alone, which is N
log N to the thirteenth times the sum of the two errors. There is no main term, no
damped convolution and no Ramanujan sum in this step; the residual enters only through
the phase. -/
theorem local_arc_core_unit_integral1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
            primeFourier111 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The elementary lower bound for the convolution at the unit modulus.  Every
summand with `2 <= m <= n - 2` is at least `1 / (Real.log n)^2`, and there are
`n - 3` such summands. -/
private theorem logConvolution_unit_lower1622 (n : ℕ) (hn : 4 ≤ n) :
    ((n - 3 : ℕ) : ℝ) / Real.log n ^ 2 ≤ logConvolution1622 n := by
  have hn2 : 2 ≤ n := by omega
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
      (1 : ℝ) / Real.log n ^ 2 ≤
        1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmn : m ≤ n - 2 := hm.2
    have hnm2 : (2 : ℝ) ≤ (n - m : ℕ) := by
      have hmn2 : (2 : ℕ) ≤ n - m := by omega
      exact_mod_cast hmn2
    have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hnmlog : 0 < Real.log ((n - m : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n - m))
    have hmm : (m : ℝ) ≤ n := by
      exact_mod_cast (by omega)
    have hnm : ((n - m : ℕ) : ℝ) ≤ n := by
      exact_mod_cast (by omega)
    have hmlog_le : Real.log (m : ℝ) ≤ Real.log n :=
      Real.log_le_log hL hmm
    have hnmlog_le : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log n :=
      Real.log_le_log hL hnm
    have hprod : Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) ≤ Real.log n ^ 2 := by
      nlinarith [mul_le_mul hmlog_le hnmlog_le (le_of_lt hnmlog) (le_of_lt hL)]
    have hprodpos : 0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) :=
      mul_pos hmlog hnmlog
    have hsqpos : 0 < Real.log n ^ 2 := sq_pos_of_pos hL
    exact (div_le_div₀ hprod hprodpos hsqpos (by rfl)).2 hprod
  have hcard : ((Finset.Icc 2 (n - 2)).card : ℝ) = (n : ℝ) - 3 := by
    have h1 : (Finset.Icc 2 (n - 2)).card = n - 3 := by
      rw [Nat.card_Icc]
      omega
    rw [h1, Nat.cast_sub (show 3 ≤ n by omega)]
    norm_num
  calc
    ((n - 3 : ℕ) : ℝ) / Real.log n ^ 2 =
        ((Finset.Icc 2 (n - 2)).card : ℝ) * ((1 : ℝ) / Real.log n ^ 2) := by
      rw [hcard]
      ring
    _ ≤ ∑ m ∈ Finset.Icc 2 (n - 2), ((1 : ℝ) / Real.log n ^ 2) :=
      Finset.sum_le_sum (fun m hm => le_rfl)
    _ ≤ ∑ m ∈ Finset.Icc 2 (n - 2),
        1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = logConvolution1622 n := by
      rfl

/-- LEAF. The size of the target main term at the unit modulus. The exponentially
damped convolution of the residual, with the damping of minus the residual over N, is
at most a constant times N log N to the thirteenth times the sum of the two errors.
This is the elementary estimate of the convolution, and it carries no prime Fourier
series, no integral and no Ramanujan sum. -/
theorem local_arc_core_unit_main1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The local core estimate at the unit modulus, from the size of the core integral and
the size of the damped convolution. The target statement is unchanged. -/
theorem local_arc_core_unit1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c1, hc1, N1, h1⟩ := local_arc_core_unit_integral1622 hG hM
  obtain ⟨c2, hc2, N2, h2⟩ := local_arc_core_unit_main1622 hG hM
  refine ⟨c1 + c2, by linarith, max N1 N2, ?_⟩
  intro N hN q hq hqQ hq1 n hn4 hnN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hA := h1 N hN1 q hq hqQ hq1 n hn4 hnN
  have hB := h2 N hN2 q hq hqQ hq1 n hn4 hnN
  have hsum := local_arc_unit_sum1622 N q hq1 n
  have hcoef := local_arc_unit_coefficient1622 q hq1 n.toNat
  have hsplit : ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat *
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)) =
      ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) *
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) := by
    ring
  have hMn : ‖((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) *
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ =
      ‖((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ := by
    rw [norm_mul, hcoef, one_mul]
  rw [hsum, hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  rw [hMn]
  calc ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
            primeFourier111 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ +
        ‖((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖
      ≤ c1 * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          c2 * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
        add_le_add hA hB
    _ = (c1 + c2) * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
        ring

end LeanLab.Linnik1951
