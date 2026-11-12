/-
Unit Linnik1951/SPLIT-outer_finite_square487.
Split of outer_finite_square487 of Decomp487b into the square-to-kernel reduction,
the region split of the frequency square at the sign of t + u, and the two region estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp487b

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. First conjunct of the target: the square of the finite signed contour is continuous in
alpha, so it is interval integrable over the outer range. No estimate is involved. -/
theorem outer_finite_square_integrable487 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, ∀ M : ℝ → ℂ, Continuous M →
      IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2) volume
        (4 / (N : ℝ)) (1 / R) := by
  sorry

/-- LEAF. Square and Fubini step. The squared finite contour is bounded by two over pi squared
times the double frequency integral of the coefficient moduli times the modulus of the alpha
integral of the kernel product. Only the signed square identity, the exchange of the alpha
integral with the two frequency integrals and the triangle inequality are used here. -/
theorem outer_finite_modulus_reduction487 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (M : ℝ → ℂ)
    (hM : Continuous M) :
    (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
      (1 / (2 * Real.pi)) ^ 2 *
        ∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ := by
  sorry

/-- LEAF. Region split of the frequency square. The double modulus integral over the square of
radius N over R times log cubed N is the sum of its part with t + u nonnegative and its part with
t + u negative. The two parts are the positive frequency difference case and the negative
frequency sum case of the outer contour. -/
theorem outer_finite_region_split487 (N : ℕ) (R : ℝ) (M : ℝ → ℂ) (hM : Continuous M) :
    (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
        ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ‖M t‖ * ‖M u‖ *
            ‖∫ α in (4 / (N : ℝ))..(1 / R),
              mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
      (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            if 0 ≤ t + u then
              ‖M t‖ * ‖M u‖ *
                ‖∫ α in (4 / (N : ℝ))..(1 / R),
                  mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
            else 0) +
        (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
          ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
            if 0 ≤ t + u then 0
            else
              ‖M t‖ * ‖M u‖ *
                ‖∫ α in (4 / (N : ℝ))..(1 / R),
                  mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) := by
  sorry

/-- LEAF. Positive frequency difference region, t + u nonnegative. The second mean value theorem in
alpha applied to the monotone arctangent factor bounds the alpha integral of the kernel product by
a constant over one plus the frequency difference, so the region costs the reciprocal difference
kernel at the radius N over R times log cubed N. -/
theorem outer_finite_difference_region487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
              ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
                if 0 ≤ t + u then
                  ‖M t‖ * ‖M u‖ *
                    ‖∫ α in (4 / (N : ℝ))..(1 / R),
                      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
                else 0) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  sorry

/-- LEAF. Negative frequency sum region, t + u negative. There the Gamma asymptotics on the line
supply exponential decay in the sum of the frequencies, which dominates the polynomial weight of
the coefficient bound, so the region costs log N to the seventh times the exponential sum kernel at
the radius N over R times log cubed N. -/
theorem outer_finite_sum_region487 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          (∫ t in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
              ∫ u in -((N : ℝ) / R * Real.log N ^ 3)..((N : ℝ) / R * Real.log N ^ 3),
                if 0 ≤ t + u then 0
                else
                  ‖M t‖ * ‖M u‖ *
                    ‖∫ α in (4 / (N : ℝ))..(1 / R),
                      mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖) ≤
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  sorry

/-- The finite signed outer square of the contour truncated at radius N over R times log cubed N.
This is proved from the integrability leaf, the square and Fubini reduction, the region split and
the two region estimates; the two region constants are added. -/
theorem outer_finite_square487_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          IntervalIntegrable (fun α : ℝ => ‖truncatedMellin487 N R M α‖ ^ 2)
            volume (4 / (N : ℝ)) (1 / R) ∧
          (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2) ≤
            C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) := by
  obtain ⟨Cd, hCd, Nd, hd⟩ := outer_finite_difference_region487 B0 hB0
  obtain ⟨Cs, hCs, Ns, hs⟩ := outer_finite_sum_region487 B0 hB0
  obtain ⟨Ni, hi⟩ := outer_finite_square_integrable487
  refine ⟨Cd + Cs, by positivity, max 8 (max Ni (max Nd Ns)), ?_⟩
  intro N hN R hR1 hR M hM
  have hN8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNd : Nd < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNs : Ns < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hl0 : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (pow_nonneg hl0 3)
  have hd0 : 0 ≤ differenceKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun u => by positivity)
  have hs0 : 0 ≤ sumKernel376 T := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith)
    intro t
    exact intervalIntegral.integral_nonneg_of_forall (by linarith)
      (fun u => (Real.exp_pos _).le)
  have hk0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) ^ 2 := by positivity
  have hk1 : (1 / (2 * Real.pi)) ^ 2 ≤ 1 := by
    have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hle : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc (1 / (2 * Real.pi)) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = 1 := one_pow 2
  have hl6d : 0 ≤ Real.log N ^ 6 * differenceKernel376 T :=
    mul_nonneg (pow_nonneg hl0 6) hd0
  have hl7s : 0 ≤ Real.log N ^ 7 * sumKernel376 T :=
    mul_nonneg (pow_nonneg hl0 7) hs0
  have e1 : (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T) ≤
      Cd * Real.log N ^ 6 * differenceKernel376 T := by
    calc (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T)
        ≤ 1 * (Cd * Real.log N ^ 6 * differenceKernel376 T) :=
          mul_le_mul_of_nonneg_right hk1
            (mul_nonneg (mul_nonneg hCd.le (pow_nonneg hl0 6)) hd0)
      _ = Cd * Real.log N ^ 6 * differenceKernel376 T := one_mul _
  have e2 : (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T) ≤
      Cs * Real.log N ^ 7 * sumKernel376 T := by
    calc (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T)
        ≤ 1 * (Cs * Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_right hk1
            (mul_nonneg (mul_nonneg hCs.le (pow_nonneg hl0 7)) hs0)
      _ = Cs * Real.log N ^ 7 * sumKernel376 T := one_mul _
  have e3 : Cd * Real.log N ^ 6 * differenceKernel376 T ≤
      (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T := by
    calc Cd * Real.log N ^ 6 * differenceKernel376 T
        = Cd * (Real.log N ^ 6 * differenceKernel376 T) := by ring
      _ ≤ (Cd + Cs) * (Real.log N ^ 6 * differenceKernel376 T) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCs.le) hl6d
      _ = (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T := by ring
  have e4 : Cs * Real.log N ^ 7 * sumKernel376 T ≤
      (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := by
    calc Cs * Real.log N ^ 7 * sumKernel376 T
        = Cs * (Real.log N ^ 7 * sumKernel376 T) := by ring
      _ ≤ (Cd + Cs) * (Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCd.le) hl7s
      _ = (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := by ring
  refine ⟨hi N hNi R M hM.1, ?_⟩
  calc
    (∫ α in (4 / (N : ℝ))..(1 / R), ‖truncatedMellin487 N R M α‖ ^ 2)
        ≤ (1 / (2 * Real.pi)) ^ 2 *
          ∫ t in -T..T, ∫ u in -T..T,
            ‖M t‖ * ‖M u‖ *
              ‖∫ α in (4 / (N : ℝ))..(1 / R),
                mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖ :=
          outer_finite_modulus_reduction487 N (by omega) R M hM.1
    _ ≤ (1 / (2 * Real.pi)) ^ 2 *
          ((∫ t in -T..T, ∫ u in -T..T,
              if 0 ≤ t + u then
                ‖M t‖ * ‖M u‖ *
                  ‖∫ α in (4 / (N : ℝ))..(1 / R),
                    mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖
              else 0) +
            (∫ t in -T..T, ∫ u in -T..T,
              if 0 ≤ t + u then 0
              else
                ‖M t‖ * ‖M u‖ *
                  ‖∫ α in (4 / (N : ℝ))..(1 / R),
                    mellinKernel442 N α t * (starRingEnd ℂ) (mellinKernel442 N α u)‖)) :=
          mul_le_mul_of_nonneg_left (outer_finite_region_split487 N R M hM.1) hk0
    _ ≤ (1 / (2 * Real.pi)) ^ 2 *
          (Cd * Real.log N ^ 6 * differenceKernel376 T +
            Cs * Real.log N ^ 7 * sumKernel376 T) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (hd N hNd R hR1 hR M hM) (hs N hNs R hR1 hR M hM)) hk0
    _ = (1 / (2 * Real.pi)) ^ 2 * (Cd * Real.log N ^ 6 * differenceKernel376 T) +
          (1 / (2 * Real.pi)) ^ 2 * (Cs * Real.log N ^ 7 * sumKernel376 T) := by ring
    _ ≤ Cd * Real.log N ^ 6 * differenceKernel376 T +
          Cs * Real.log N ^ 7 * sumKernel376 T := add_le_add e1 e2
    _ ≤ (Cd + Cs) * Real.log N ^ 6 * differenceKernel376 T +
          (Cd + Cs) * Real.log N ^ 7 * sumKernel376 T := add_le_add e3 e4

end LeanLab.Linnik1951
