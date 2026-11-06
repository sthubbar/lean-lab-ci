/-
P0093 pages 156 through 158. Absolute central Mellin kernel mass.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT1622_mellin

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 156 equation 4.1. The Mellin kernel before its coefficient M.
The factor one over two pi remains outside this kernel. -/
noncomputable def mellinKernel442 (N : ℕ) (α t : ℝ) : ℂ :=
  (((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
    (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)

/-- LEAF. P0093 page 156 equation 4.1 and page 158 central estimate
before equation 4.8. On the central interval absolute Gamma decay gives
an integrable logarithm weighted kernel with mass at most a constant
times square root N times log cubed N. This retains only the absolute
kernel calculation. There is no coefficient M, character, GRH or radius R. -/
theorem central_kernel_mass442 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
        Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
            C * Real.sqrt N * Real.log N ^ 3 := by
  sorry

/-- LEAF. P0093 page 156 equation 4.1. A line bound on M bounds the
Mellin integral by B0 over two pi times its absolute weighted kernel
mass. This is the norm integral inequality alone. -/
theorem mellin_kernel_domination442 (N : ℕ) (α B0 : ℝ) (hB0 : 0 ≤ B0)
    (M : ℝ → ℂ) (hM : LineBound1622 N B0 M)
    (hI : Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :
    ‖mellinU1622 N M α‖ ≤ (1 / (2 * Real.pi)) * B0 *
      (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  have hb (t : ℝ) : ‖mellinKernel442 N α t * M t‖ ≤
      B0 * (‖mellinKernel442 N α t‖ *
        Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left (hM.2 t) (norm_nonneg (mellinKernel442 N α t))
    nlinarith
  have hnorm := norm_integral_le_of_norm_le (hI.const_mul B0) (Filter.Eventually.of_forall hb)
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, mellinKernel442 N α t * M t)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ, B0 * (‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- LEAF. P0093 page 158 before equation 4.8. Square root N is at
most N over square root R when one is at most R at most N. -/
theorem sqrt_scale442 (N R : ℝ) (hN : 0 < N) (hR : 0 < R) (hRN : R ≤ N) :
    Real.sqrt N ≤ N / Real.sqrt R := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    Real.sqrt N * Real.sqrt R ≤ Real.sqrt N * Real.sqrt N := by
      gcongr
    _ = N := Real.mul_self_sqrt hN.le

/-- P0093 page 158 central estimate before equation 4.8. Exact
lemma2_central1622 statement. CONDITIONAL only on central_kernel_mass442.
The coefficient domination and the radius scaling have clean proofs. -/
theorem lemma2_central_decomposed442 (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
        ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
          ‖mellinU1622 N M α‖ ≤ B * (N : ℝ) / Real.sqrt R * Real.log N ^ 3 := by
  obtain ⟨C, hC, N0, hc⟩ := central_kernel_mass442
  refine ⟨(1 / (2 * Real.pi)) * B0 * C, by positivity, max 1 N0, ?_⟩
  intro N hN R hR1 hR M hM α hα
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have hRp : 0 < R := by linarith
  have hRN : R ≤ N := by
    calc R ≤ (N : ℝ) ^ (2 / 7 : ℝ) := hR
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = N := Real.rpow_one _
  obtain ⟨hI, hm⟩ := hc N (by omega) α hα
  have hl : 0 ≤ Real.log N ^ 3 := pow_nonneg (Real.log_nonneg hNr) 3
  calc
    _ ≤ (1 / (2 * Real.pi)) * B0 *
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mellin_kernel_domination442 N α B0 hB0.le M hM hI
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * Real.sqrt N * Real.log N ^ 3) := by
      gcongr
    _ ≤ (1 / (2 * Real.pi)) * B0 * (C * ((N : ℝ) / Real.sqrt R) * Real.log N ^ 3) := by
      gcongr
      exact sqrt_scale442 N R hNp hRp hRN
    _ = _ := by ring

/-- P0093 page 156 equation 4.1. A nonzero concrete coefficient on
the line at N equal to four and B0 equal to one. -/
theorem lineBound_one442 : LineBound1622 4 1 (fun _ => 1) := by
  refine ⟨continuous_const, fun t => ?_⟩
  have hx : Real.exp 1 ≤ (4 : ℝ) * (|t| + 2) := by
    nlinarith [abs_nonneg t, Real.exp_one_lt_three]
  have hl := Real.log_le_log (Real.exp_pos 1) hx
  rw [Real.log_exp] at hl
  simpa using one_le_pow₀ hl (n := 3)

/-- P0093 page 158 central estimate and page 159 equation 5.1.
Exact central_pointwise376 statement. CONDITIONAL on the absolute
kernel mass and the existing corrected Mellin transfer. -/
theorem central_pointwise_decomposed442 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
          |α| ≤ 4 / (N : ℝ) →
            ‖characterPrime280 χ N α‖ ^ 2 ≤
              B * (N : ℝ) ^ 2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 := by
  obtain ⟨B0, hB0, D, hD, Nt, ht⟩ := mellin_transfer1622 hG
  obtain ⟨C, hC, Nc, hc⟩ := lemma2_central_decomposed442 B0 hB0
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨2 * C ^ 2 + 2 * D ^ 2, by positivity, max 8 (max L (max Nt Nc)), ?_⟩
  intro N hN q hq hqt χ hχ α hα
  have h8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hLN : L < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNt : Nt < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNc : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hl : 1 ≤ Real.log N := by
    have hLR : (L : ℝ) < N := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hLR).le
  set R := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  obtain ⟨hR1, hR2⟩ := qtau_range1622 N q (by omega) hq hqt
  have hRp : 0 < R := by dsimp [R]; positivity
  have hRN : R ≤ N := by
    have := four_rpow1622 N (by omega)
    change R ≤ (N : ℝ) ^ (2 / 7 : ℝ) at hR2
    have : 0 ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by positivity
    linarith
  obtain ⟨M, hM, hm⟩ := ht N hNt q hq hqt χ hχ
  have hU := hc N hNc R hR1 hR2 M hM α hα
  have hsq : ‖mellinU1622 N M α‖ ^ 2 ≤ C ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) := by
    calc
      _ ≤ (C * (N : ℝ) / Real.sqrt R * Real.log N ^ 3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hU 2
      _ = _ := by
        rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hRp.le]
        ring
  have herror : (D * Real.sqrt N) ^ 2 ≤ D ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6) := by
    rw [mul_pow, Real.sq_sqrt hNr.le]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
    have hn : (N : ℝ) ≤ (N : ℝ) ^ 2 / R := by
      rw [le_div_iff₀ hRp]
      nlinarith
    exact hn.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl))
  have hh := norm_sq_le_of_near1622 (hm α)
  change _ ≤ (2 * C ^ 2 + 2 * D ^ 2) * (N : ℝ) ^ 2 / R * Real.log N ^ 6
  calc
    _ ≤ 2 * ‖mellinU1622 N M α‖ ^ 2 + 2 * (D * Real.sqrt N) ^ 2 := hh
    _ ≤ 2 * (C ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6)) +
        2 * (D ^ 2 * ((N : ℝ) ^ 2 / R * Real.log N ^ 6)) :=
      add_le_add (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (mul_le_mul_of_nonneg_left herror (by norm_num))
    _ = _ := by ring

end LeanLab.Linnik1951
