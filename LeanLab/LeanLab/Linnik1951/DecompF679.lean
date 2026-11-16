/-
Split of the unit core integral into a finite signed kernel and a damping tail.
The exact window expansion keeps every frequency and its sinc factor.
The finite kernel estimate below is a separate open arithmetic input.
It is not supplied by an estimate for the nonprincipal character errors.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_local_arc_core_unit1622
import LeanLab.Linnik1951.Decomp552b

namespace LeanLab.Linnik1951

open Finset

/-- LEAF. Count the possible first coordinates of an ordered prime pair.
This elementary coefficient bound is the input to the damping tail estimate. -/
theorem prime_pair_bound_F679 (k : ℕ) :
    primePairCount552 k ≤ k + 1 := by
  unfold primePairCount552
  exact (card_filter_le _ _).trans_eq (card_range _)

/-- LEAF. Expand the unit core integral as a real signed sinc series.
This exact identity retains the contribution of every prime pair frequency. -/
theorem unit_core_kernel_F679 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
      primeFourier111 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ((∑' k : ℕ, (primePairCount552 k : ℝ) * Real.exp (-(k : ℝ) / N) *
        (2 * (1 / (N : ℝ)) *
          Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ))))) : ℂ) := by
  simpa only [zero_add, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one, Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_div,
    Complex.ofReal_one] using
    prime_square_window552 N hN (1 / (N : ℝ)) (by positivity) 0 n

/-- LEAF. Remove frequencies at least N squared from the signed kernel.
Absolute convergence and exponential damping bound this tail uniformly in
the residual, without a prime distribution estimate. -/
theorem unit_kernel_truncation_F679 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    |(∑' k : ℕ, (primePairCount552 k : ℝ) * Real.exp (-(k : ℝ) / N) *
        (2 * (1 / (N : ℝ)) *
          Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ))))) -
      (∑ k ∈ range (N ^ 2), (primePairCount552 k : ℝ) * Real.exp (-(k : ℝ) / N) *
        (2 * (1 / (N : ℝ)) *
          Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ)))))| ≤
      32 * (N : ℝ) * Real.exp (-(N : ℝ) / 2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let a : ℕ → ℝ := fun k => primePairCount552 k
  let b : ℕ → ℝ := fun k =>
    Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ)))
  let g : ℕ → ℝ := fun k => Real.exp (-(k : ℝ) / (2 * N))
  let f : ℕ → ℝ := fun k =>
    a k * Real.exp (-(k : ℝ) / N) * (2 * (1 / (N : ℝ)) * b k)
  have ha (k : ℕ) : 0 ≤ a k := Nat.cast_nonneg _
  have ha' (k : ℕ) : a k ≤ (k : ℝ) + 1 := by
    change (primePairCount552 k : ℝ) ≤ (k : ℝ) + 1
    exact_mod_cast prime_pair_bound_F679 k
  have hb (k : ℕ) : |b k| ≤ 1 := Real.abs_sinc_le_one _
  have hr : Real.exp (-1 / (2 * (N : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by positivity))
  have hgeq (k : ℕ) :
      g k = Real.exp (-1 / (2 * (N : ℝ))) ^ k := by
    rw [← Real.exp_nat_mul]
    dsimp [g]
    congr 1
    ring
  have hgs : Summable g :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr).congr (fun k => (hgeq k).symm)
  have hden : (1 - Real.exp (-1 / (2 * (N : ℝ))))⁻¹ ≤ 8 * N := by
    have hd := exponential_denominator111 (4 * (N : ℝ)) (by linarith)
    have he : -2 / (4 * (N : ℝ)) = -1 / (2 * (N : ℝ)) := by
      field_simp
      <;> ring
    calc
      _ ≤ 2 * (4 * (N : ℝ)) := by simpa only [he, one_div] using hd
      _ = _ := by ring
  have hgt : (∑' k, g k) ≤ 8 * N := by
    simpa only [hgeq, tsum_geometric_of_lt_one (Real.exp_pos _).le hr] using hden
  have hterm (k : ℕ) : |f k| ≤ 4 * g k := by
    have hcount : a k ≤ 2 * (N : ℝ) * Real.exp ((k : ℝ) / (2 * N)) := by
      calc
        a k ≤ (k : ℝ) + 1 := ha' k
        _ ≤ (k : ℝ) + 2 * N := by linarith
        _ = 2 * (N : ℝ) * ((k : ℝ) / (2 * N) + 1) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
    have hexp : Real.exp ((k : ℝ) / (2 * N)) * Real.exp (-(k : ℝ) / N) =
        g k := by
      rw [← Real.exp_add]
      dsimp [g]
      congr 1
      ring
    calc
      |f k| = a k * Real.exp (-(k : ℝ) / N) *
          (2 * (1 / (N : ℝ)) * |b k|) := by
        dsimp [f]
        rw [abs_mul, abs_mul, abs_of_nonneg (ha k), abs_of_pos (Real.exp_pos _),
          abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (2 * (N : ℝ) * Real.exp ((k : ℝ) / (2 * N))) *
          Real.exp (-(k : ℝ) / N) * (2 * (1 / (N : ℝ)) * 1) := by
        gcongr
        exact hb k
      _ = 4 * (Real.exp ((k : ℝ) / (2 * N)) *
          Real.exp (-(k : ℝ) / N)) := by field_simp; ring
      _ = 4 * g k := by rw [hexp]
  have hfs : Summable f := Summable.of_norm_bounded (hgs.mul_left 4)
    (fun k => by simpa only [Real.norm_eq_abs] using hterm k)
  have hsplit : (∑' k, f k) - ∑ k ∈ range (N ^ 2), f k =
      ∑' k, f (k + N ^ 2) := by
    linarith [hfs.sum_add_tsum_nat_add (N ^ 2)]
  have hshift (k : ℕ) :
      |f (k + N ^ 2)| ≤ (4 * Real.exp (-(N : ℝ) / 2)) * g k := by
    calc
      _ ≤ 4 * g (k + N ^ 2) := hterm _
      _ = _ := by
        dsimp [g]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        field_simp
        ring
  change |(∑' k, f k) - ∑ k ∈ range (N ^ 2), f k| ≤ _
  rw [hsplit]
  calc
    _ ≤ (∑' k, (4 * Real.exp (-(N : ℝ) / 2)) * g k) := by
      simpa only [Real.norm_eq_abs] using
        (tsum_of_norm_bounded (f := fun k : ℕ => f (k + N ^ 2))
          ((hgs.mul_left (4 * Real.exp (-(N : ℝ) / 2))).hasSum)
          (fun k => by simpa only [Real.norm_eq_abs] using hshift k))
    _ = (4 * Real.exp (-(N : ℝ) / 2)) * (∑' k, g k) := tsum_mul_left
    _ ≤ (4 * Real.exp (-(N : ℝ) / 2)) * (8 * N) :=
      mul_le_mul_of_nonneg_left hgt (by positivity)
    _ = _ := by ring

/-- LEAF. Estimate the finite signed prime pair kernel below N squared.
This is the arithmetic cancellation step. The absolute value is outside
the sum, so the sinc factors keep their signs. No integral or infinite
Fourier series occurs in this step. -/
theorem unit_kernel_finite_F679 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ n : ℤ, (4 : ℤ) ≤ n → n ≤ N →
        |∑ k ∈ range (N ^ 2), (primePairCount552 k : ℝ) * Real.exp (-(k : ℝ) / N) *
          (2 * (1 / (N : ℝ)) *
            Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ))))| ≤
          c * (N : ℝ) * Real.log N ^ 13 *
            (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. Absorb the exponentially small truncation error into the
square root error scale once N is at least sixty four. This step uses
only inequalities for real exponential, logarithm and powers. -/
theorem unit_tail_absorption_F679 (N : ℕ) (hN : 64 ≤ N) :
    32 * (N : ℝ) * Real.exp (-(N : ℝ) / 2) ≤
      (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have he := Real.pow_div_factorial_le_exp ((N : ℝ) / 2) (by positivity) 3
  norm_num at he
  have hsq : (1536 : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNr) (by linarith : 0 ≤ (N : ℝ) + 64)]
  have hlarge : 32 * (N : ℝ) ≤ Real.exp ((N : ℝ) / 2) := by
    nlinarith [mul_nonneg hNp.le (sub_nonneg.mpr hsq)]
  have hsmall : 32 * (N : ℝ) * Real.exp (-(N : ℝ) / 2) ≤ 1 := by
    rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr hlarge
  have hlog : 1 ≤ Real.log N :=
    (Real.le_log_iff_exp_le hNp).mpr (by linarith [Real.exp_one_lt_three])
  have hsqrt : Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) ≤ N := by
    calc
      _ ≤ Real.sqrt ((N : ℝ) ^ (2 : ℝ)) :=
        Real.sqrt_le_sqrt (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
      _ = N := by rw [Real.rpow_two, Real.sqrt_sq hNp.le]
  have hsqrtpos : 0 < Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) :=
    Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hNp _)
  have hratio : 1 ≤ (N : ℝ) / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) :=
    (le_div_iff₀ hsqrtpos).mpr (by simpa using hsqrt)
  calc
    _ ≤ 1 := hsmall
    _ ≤ ((N : ℝ) / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log N ^ 13 := by
      have hp : 1 ≤ Real.log N ^ 13 := one_le_pow₀ hlog
      nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hp)]
    _ = _ := by ring

/-- Assemble the exact kernel identity, finite cancellation estimate and
exponential tail bound at the unit modulus. -/
theorem local_arc_core_unit_integral1622_F679 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ, (4 : ℤ) ≤ n → n ≤ N → ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ ≤ c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c, hc, N0, hfinite⟩ := unit_kernel_finite_F679 hG hM
  refine ⟨c + 1, by linarith, max N0 64, ?_⟩
  intro N hN q _ _ hq1 n hn4 hnN
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN64 : 64 ≤ N := le_trans (le_max_right _ _) hN.le
  have hN1 : 1 ≤ N := by omega
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  let S : ℝ := ∑' k : ℕ, (primePairCount552 k : ℝ) * Real.exp (-(k : ℝ) / N) *
    (2 * (1 / (N : ℝ)) *
      Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ))))
  let T : ℝ := ∑ k ∈ range (N ^ 2),
    (primePairCount552 k : ℝ) * Real.exp (-(k : ℝ) / N) *
      (2 * (1 / (N : ℝ)) *
        Real.sinc (2 * Real.pi * ((n : ℝ) - k) * (1 / (N : ℝ))))
  have htrunc : |S - T| ≤ 32 * (N : ℝ) * Real.exp (-(N : ℝ) / 2) :=
    unit_kernel_truncation_F679 N hN1 n
  have hfin : |T| ≤ c * (N : ℝ) * Real.log N ^ 13 *
      (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) :=
    hfinite N hN0 n hn4 hnN
  have htail := unit_tail_absorption_F679 N hN64
  rw [unit_core_kernel_F679 N hN1 n, Complex.norm_real, Real.norm_eq_abs]
  change |S| ≤ _
  calc
    |S| = |(S - T) + T| := by congr 1; ring
    _ ≤ |S - T| + |T| := abs_add_le _ _
    _ ≤ 32 * (N : ℝ) * Real.exp (-(N : ℝ) / 2) +
        c * (N : ℝ) * Real.log N ^ 13 *
          (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add htrunc hfin
    _ ≤ (N : ℝ) * Real.log N ^ 13 *
          (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) +
        c * (N : ℝ) * Real.log N ^ 13 *
          (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add htail le_rfl
    _ = (c + 1) * (N : ℝ) * Real.log N ^ 13 *
        (1 / Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ))) := by ring
    _ ≤ (c + 1) * (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      rw [hq1, Nat.cast_one, one_mul]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (by positivity)

end LeanLab.Linnik1951
