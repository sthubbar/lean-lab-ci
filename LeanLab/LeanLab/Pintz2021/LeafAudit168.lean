import LeanLab.Pintz2021.DecompJ281
import LeanLab.ChenExplicit.TwinCNumeric

/-!
Audit of the existing decomposition against P0054 page 8 display 2.22.
The supplied series in the existing tail leaf is unrestricted.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.LeafAudit168

open State1581 DecompJ281 Finset Filter Topology

attribute [local instance] Classical.propDecidable

/-- Supplied series values supported on the pair of poles. -/
noncomputable def poleSeries (z w : ExcPair) (_m : ℕ) : ℂ :=
  if z = pole ∧ w = pole then 1 else 0

/-- The pole supported main term is the exact discrete difference kernel. -/
theorem main_poleSeries (H P X ε : ℝ) (m : ℕ) :
    mainTermPrime (excSet H (Real.sqrt X) P X) poleSeries ε X m =
      WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 m true := by
  unfold mainTermPrime poleSeries
  simp_rw [finsum_eq_if]
  rw [finsum_eq_single _ pole (by intro z hz; simp [hz])]
  simp only [pole_mem_excSet, ↓reduceIte]
  rw [finsum_eq_single _ pole (by intro w hw; simp [hw])]
  simp [pole_mem_excSet, mult_pole, Asign_pole, show pole.ρ = 1 from rfl]

/-- A zero cutoff removes the supplied pole term. -/
theorem truncated_poleSeries_zero (H P X ε : ℝ) (m : ℕ) :
    mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) poleSeries ε X 0 m = 0 := by
  have hcut : ¬ UCutoff pole pole m ≤ (0 : ℝ) := by
    norm_num [UCutoff, pole]
  unfold mainTermTruncatedPrime poleSeries
  simp_rw [finsum_eq_if]
  rw [finsum_eq_single _ pole (by intro z hz; simp [hz])]
  simp only [pole_mem_excSet, show pole.ρ.im = 0 from rfl, abs_zero, le_refl,
    and_self, ↓reduceIte]
  rw [finsum_eq_single _ pole (by intro w hw; simp [hw])]
  simp [hcut]

/-- A concrete nonempty discrete difference kernel with the paper cutoff. -/
theorem kernel_instance :
    WeightedKernelsTask08.weightedKernel 1 3 1 1 1 true = 1 := by
  rw [WeightedKernelsTask08.weightedKernel_poles]
  have hp : WeightedKernelsTask08.kernelPairs 1 3 1 true = {(3, 2)} := by
    ext ⟨k, l⟩
    norm_num [WeightedKernelsTask08.kernelPairs]
    omega
  rw [hp]
  norm_num

/-- The existing tail leaf cannot hold for unrestricted U and supplied series. -/
theorem unrestricted_tail_false :
    ¬ (∃ C' : ℝ, 0 < C' ∧ ∀ H X P U ε : ℝ,
      ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
        ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
          mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X U m‖ ≤
            C' * (Sing m * X * Real.log U / Real.sqrt U)) := by
  rintro ⟨C, _, h⟩
  have ht := h 0 3 1 0 1 poleSeries 1
  rw [main_poleSeries, truncated_poleSeries_zero] at ht
  norm_num [X1, kernel_instance] at ht

/-- The prime convention has the same divergent pole series at zero frequency. -/
theorem prime_zero_no_limit (s : ℂ) :
    ¬ Tendsto (singPartialPrime pole pole 0) atTop (𝓝 s) := by
  have heq : singPartialPrime pole pole 0 = singPartial pole pole 0 := by
    funext Q
    simp only [singPartialPrime, singPartial, cCoefPrime_pole]
  rw [heq]
  exact Audit168.zero_no_limit s

/-- The major arc prime coefficient vanishes at the negative scale used in the audit. -/
theorem negative_scale_major_zero : R1majPrime 1 (-1) 1 2 = 0 := by
  have hf : ⌊(-1 : ℝ)⌋₊ = 0 := Nat.floor_of_nonpos (by norm_num)
  simp [R1majPrime, X1, DifferenceTask53.differenceR1, MinorArcs.coef,
    MinorArcs.S, MinorArcs.aS, hf]

/-- The triangle leaf needs sign and scale hypotheses that its sealed statement omits. -/
theorem triangle_leaf_false :
    ¬ (∀ {H X P U ε ε0 c C C' : ℝ} {m : ℕ}
      {Sg' : ExcPair → ExcPair → ℕ → ℂ},
      ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
        C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X U m‖ ≤
          C' * (Sing m * X * Real.log U / Real.sqrt U) →
      U = Real.sqrt X →
      ‖R1majPrime ε X P m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X U m‖ ≤
          max C C' * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0) +
            Sing m * X * Real.log U / X ^ (1 / 4 : ℝ))) := by
  intro h
  have hs : 1 < Sing 2 := by
    have hc := LeanLab.ChenExplicit.twinC_ge_065
    have he : Sing 2 = 2 * LeanLab.ChenExplicit.twinC := by
      simpa [Applications.C0_eq_twinC] using Sing_two_pow 1
    rw [he]
    linarith
  have h1 : ‖R1majPrime 1 (-1) 1 2 -
      mainTermPrime (excSet 0 (Real.sqrt (-1)) 1 (-1)) (fun _ _ _ => 0) 1 (-1) 2‖ ≤
      (-1 : ℝ) * (Sing 2 * (-1) * Real.exp (-(0 * 0)) + (-1 : ℝ) ^ (1 - 1 : ℝ)) := by
    simp only [negative_scale_major_zero, mainTermPrime, mul_zero, zero_mul, finsum_zero,
      sub_zero, norm_zero]
    norm_num
    linarith
  have h2 : ‖mainTermPrime (excSet 0 (Real.sqrt (-1)) 1 (-1))
        (fun _ _ _ => 0) 1 (-1) 2 -
      mainTermTruncatedPrime (excSet 0 (Real.sqrt (-1)) 1 (-1))
        (fun _ _ _ => 0) 1 (-1) 0 2‖ ≤
      (1 : ℝ) * (Sing 2 * (-1) * Real.log 0 / Real.sqrt 0) := by
    simp [mainTermPrime, mainTermTruncatedPrime]
  have ht := h (H := 0) (X := -1) (P := 1) (U := 0) (ε := 1) (ε0 := 1)
    (c := 0) (C := -1) (C' := 1) (m := 2) (Sg' := fun _ _ _ => 0) h1 h2 (by norm_num)
  simp [negative_scale_major_zero, mainTermTruncatedPrime] at ht
  linarith

/-- The exact existing untruncated prime leaf is false at zero frequency. -/
theorem untruncated_leaf_false :
    ¬ (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0))) := by
  rintro ⟨ε0, hε0, h⟩
  let ε := min (ε0 / 2) (1 / 9)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε0' : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε < 4 / 9 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c, H0, C, X0, hc, hdata⟩ := h ε hε hε0'
  obtain ⟨H, X, P0, hHyp, _⟩ := thm1Hyp_inhabited hε hε4 H0 X0
  obtain ⟨P, _, _, _, Sg, hconv, _⟩ := hdata H X P0 hHyp
  exact prime_zero_no_limit (Sg pole pole 0)
    (hconv pole (pole_mem_excSet _ _ _ _) pole (pole_mem_excSet _ _ _ _) 0)

end LeanLab.Pintz2021.LeafAudit168

#print axioms LeanLab.Pintz2021.LeafAudit168.main_poleSeries
#print axioms LeanLab.Pintz2021.LeafAudit168.truncated_poleSeries_zero
#print axioms LeanLab.Pintz2021.LeafAudit168.kernel_instance
#print axioms LeanLab.Pintz2021.LeafAudit168.unrestricted_tail_false
#print axioms LeanLab.Pintz2021.LeafAudit168.prime_zero_no_limit

#print axioms LeanLab.Pintz2021.LeafAudit168.negative_scale_major_zero
#print axioms LeanLab.Pintz2021.LeafAudit168.triangle_leaf_false

#print axioms LeanLab.Pintz2021.LeafAudit168.untruncated_leaf_false
