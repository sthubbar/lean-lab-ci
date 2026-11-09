/-
Split unit of Linnik1951/SPLIT_log_convolution_estimate1622.
Sub-leaves for the elementary excess estimate logConv_excess1622, plus the assembly
theorem logConv_excess1622_split. No statement of the parent file is changed and no
definition is added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write u = log m, v = log (n - m) and L = log n, so that the summand is
1 / (u * v) and the shift is 2L - u - v, the logarithm of n^2 / (m (n - m)). The
summand is at most 1/L^2 + 2 (2L - u - v)/L^3 wherever the shift is at most L/2,
and the shift has total at most a constant times n over the whole range. The two
ends of the range, where the shift is large, hold only about the square root of n
terms of size at most a constant over L, which is again at most a constant times
n / L^3. Adding the three pieces gives the excess with one constant.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. Positivity of the shift: for every index of the convolution the logarithm
of m (n - m) is at most twice the logarithm of n, that is the shift 2 log n minus
log m minus log (n - m) is nonnegative. This is the step that lets the shift be
weight summed over the range without a sign condition. -/
theorem logConv_shift_nonneg1622 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    0 ≤ 2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)) := by
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm2, hmn⟩ := hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hnm_pos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by
    have : 0 < n - m := by omega
    exact_mod_cast this
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hprod_le : (m : ℝ) * ((n - m : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : m ≤ n)
    have h2 : ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : n - m ≤ n)
    nlinarith
  have hlog_prod : Real.log ((m : ℝ) * ((n - m : ℕ) : ℝ)) ≤ Real.log ((n : ℝ) ^ 2) :=
    Real.log_le_log (mul_pos hm_pos hnm_pos) hprod_le
  rw [Real.log_mul hm_pos.ne' hnm_pos.ne', Real.log_pow, Nat.cast_ofNat] at hlog_prod
  linarith

/-- LEAF. Total of the shift: summed over the whole range 2 <= m <= n - 2 the shift
2 log n - log m - log (n - m) is at most a constant times n. The shift is the
logarithm of n^2 / (m (n - m)), and the sum of the logarithms is read off a lower
bound for the logarithm of the factorial (n - 2)!, so the constant is absolute. -/
theorem logConv_shift_sum1622 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1000 ≤ n →
      (∑ m ∈ Finset.Icc 2 (n - 2),
          (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ K * (n : ℝ) := by
  sorry

/-- LEAF. Termwise majorant: for positive u, v and L with u + v at most 2 L and with
the shift 2 L - u - v at most L / 2, the reciprocal product 1 / (u v) is at most
1 / L^2 plus twice the shift over L^3. This is the elementary inequality
4 u v <= (u + v)^2 together with a quadratic estimate for the reciprocal of
1 - shift / L. -/
theorem logConv_term_majorant1622 (u v L : ℝ) (hu : 0 < u) (hv : 0 < v) (hL : 0 < L)
    (hsum : u + v ≤ 2 * L) (hshift : 2 * L - (u + v) ≤ L / 2) :
    1 / (u * v) ≤ 1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v)) := by
  set s := 2 * L - (u + v) with hs
  have hs_nonneg : 0 ≤ s := by rw [hs]; linarith
  have hs_le : s ≤ L / 2 := hshift
  have huv : u + v = 2 * L - s := by rw [hs]; ring
  have h_amgm : 4 * (u * v) ≤ (u + v) ^ 2 := by
    have h := sq_nonneg (u - v)
    nlinarith
  have hpos_uv : 0 < u * v := mul_pos hu hv
  have hpos_sq : 0 < (2 * L - s) ^ 2 := by
    have hpos : 0 < 2 * L - s := by rw [← huv]; linarith
    positivity
  have h1 : 1 / (u * v) ≤ 4 / ((2 * L - s) ^ 2) := by
    rw [div_le_div_iff₀ hpos_uv hpos_sq]
    nlinarith
  have h2 : 4 / ((2 * L - s) ^ 2) ≤ 1 / L ^ 2 + (2 / L ^ 3) * s := by
    have hLpos : 0 < L := hL
    have h_denom : 0 < L ^ 3 * (2 * L - s) ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos_sq (by positivity : 0 < L ^ 2 * L + 2 * L * s)]
    -- after cross-multiplying: 4 * (L^2 * L + 2 * L * s) ≤ (L^2 + 2*s*L) * (2L-s)^2 ... let me use a cleaner approach
    have hkey : 4 * L ^ 3 ≤ (L + 2 * s) * (2 * L - s) ^ 2 := by
      have ht : s / L ≤ 1 / 2 := by
        rw [div_le_iff₀ hL]
        linarith
      have ht_nonneg : 0 ≤ s / L := div_nonneg hs_nonneg hL.le
      have h_poly : 0 ≤ (s / L) * (4 - 7 * (s / L) + 2 * (s / L) ^ 2) := by
        have h_quad : 0 ≤ 4 - 7 * (s / L) + 2 * (s / L) ^ 2 := by
          nlinarith
        exact mul_nonneg ht_nonneg h_quad
      have h_eq : (L + 2 * s) * (2 * L - s) ^ 2 - 4 * L ^ 3 = L ^ 3 * ((s / L) * (4 - 7 * (s / L) + 2 * (s / L) ^ 2)) := by
        field_simp
        ring
      nlinarith
    have h_eq1 : 1 / L ^ 2 + (2 / L ^ 3) * s = (L + 2 * s) / L ^ 3 := by
      field_simp
      ring
    have h_eq2 : 4 / ((2 * L - s) ^ 2) = (4 * L ^ 3) / (L ^ 3 * (2 * L - s) ^ 2) := by
      field_simp
      ring
    rw [h_eq1, h_eq2]
    rw [div_le_div_iff₀ (by positivity : 0 < L ^ 3) h_denom]
    nlinarith
  rw [hs] at h1
  linarith [h1, h2]

/-- LEAF. Small shift in the middle of the range: for n at least 10^3 and for an
index m with 2 sqrt n <= m <= n - 2 sqrt n the product m (n - m) is at least
n^(3/2), so the shift 2 log n - log m - log (n - m) is at most half of log n. This
is the step that makes the termwise majorant applicable away from the two ends. -/
theorem logConv_middle_shift1622 (n m : ℕ) (hn : 1000 ≤ n)
    (hm1 : 2 * Nat.sqrt n ≤ m) (hm2 : m ≤ n - 2 * Nat.sqrt n) :
    2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)) ≤ Real.log (n : ℝ) / 2 := by
  sorry

/-- LEAF. Mass of the two ends: summed over the indices m of the range which fail
2 sqrt n <= m <= n - 2 sqrt n, that is over the two ends of the range, the summand
1 / (log m log (n - m)) is at most a constant times n / (log n)^3. Each such index
has both logarithms at least half of log n, and there are at most 4 sqrt n of them. -/
theorem logConv_end_mass1622 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1000 ≤ n →
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
  sorry

/-- The excess estimate of the parent file, assembled from the leaves above with no
remaining gap: the range of the convolution is cut at 2 sqrt n, the middle carries the
main term n / (log n)^2 plus twice the total shift over log n cubed, and the two ends
carry a constant times n / (log n)^3. -/
theorem logConv_excess1622_split :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1000 ≤ n →
      logConvolution1622 n - (n : ℝ) / Real.log n ^ 2 ≤ C * ((n : ℝ) / Real.log n ^ 3) := by
  classical
  obtain ⟨K, hKpos, hK⟩ := logConv_shift_sum1622
  obtain ⟨Ke, hKepos, hKe⟩ := logConv_end_mass1622
  refine ⟨2 * K + Ke, by linarith, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hLne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hL
  have hT : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 (n - 2))
    (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)
    (fun m => 1 / (Real.log m * Real.log (n - m : ℕ)))
  -- the middle range
  have hmid :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 + 2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
    have hpoint : ∀ m ∈ (Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
        1 / (Real.log m * Real.log (n - m : ℕ))
          ≤ 1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))) := by
      intro m hmf
      obtain ⟨hmem, hm1, hm2⟩ := Finset.mem_filter.mp hmf
      have hu : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hv : 0 < Real.log ((n - m : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n - m by omega))
      have hsum : Real.log m + Real.log (n - m : ℕ) ≤ 2 * Real.log (n : ℝ) := by
        linarith [logConv_shift_nonneg1622 n m hmem]
      have hshift := logConv_middle_shift1622 n m hn hm1 hm2
      exact logConv_term_majorant1622 (Real.log m) (Real.log (n - m : ℕ)) (Real.log (n : ℝ))
        hu hv hL hsum (by linarith)
    have hcard : (((Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) ≤ (n : ℝ) := by
      have h1 : ((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card ≤ n := by
        have h2 := Finset.card_le_card (Finset.filter_subset
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n) (Finset.Icc 2 (n - 2)))
        have h3 : (Finset.Icc 2 (n - 2)).card = n - 2 + 1 - 2 := Nat.card_Icc 2 (n - 2)
        omega
      exact_mod_cast h1
    have hsums :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
          ≤ K * (n : ℝ) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans (hK n hn)
      intro x hx _
      exact logConv_shift_nonneg1622 n x hx
    have hE :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))))
          = (((Finset.Icc 2 (n - 2)).filter
              (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
                (1 / Real.log (n : ℝ) ^ 2) +
              (2 / Real.log (n : ℝ) ^ 3) *
                (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
                  (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
                  (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hcast : (0 : ℝ) ≤ 1 / Real.log (n : ℝ) ^ 2 := by positivity
    have hfac : (0 : ℝ) ≤ 2 / Real.log (n : ℝ) ^ 3 := by positivity
    have hle1 : (((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
            (1 / Real.log (n : ℝ) ^ 2) ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hcast
    have hle2 : (2 / Real.log (n : ℝ) ^ 3) *
          (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsums hfac
    calc (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ ∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) :=
          Finset.sum_le_sum hpoint
      _ = _ := hE
      _ ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) +
            (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) := add_le_add hle1 hle2
      _ = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
            2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
          field_simp
  -- the two ends
  have hends :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hKe n hn
  have hcomb : (n : ℝ) / Real.log (n : ℝ) ^ 2 +
        2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) +
          Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3)
      = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
          (2 * K + Ke) * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by ring
  have hunfold : logConvolution1622 n =
      ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ)) := rfl
  rw [hunfold]
  linarith [hsplit, hmid, hends, hcomb]

end LeanLab.Linnik1951
