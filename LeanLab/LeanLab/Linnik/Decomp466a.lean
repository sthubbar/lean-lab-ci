/-
Gallagher 1975 P0094 p.127 Theorem 3.
The exponential error is retained. The exceptional conductor is shared by all frequencies.
The fixed positive exceptional strip is chosen from the proved Page and conductor bounds.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.Decomp1532b

namespace LeanLab.Linnik.Decomp466a

open Finset MeasureTheory
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries excSet)
open LeanLab.Linnik.U7204 (Sg)

/-- The fixed positive exceptional strip constant of Gallagher 1975 p.127.
Choose it small enough for the proved reality and conductor growth estimates. -/
noncomputable def exceptionalStrip : ℝ :=
  min (Classical.choose LeanLab.Linnik.Decomp1532b.exceptional_conductor_log_growth)
    (min (Classical.choose LeanLab.Linnik.Decomp1532b.page_real)
      (Classical.choose LeanLab.Linnik.Decomp1532b.page_subsingleton))

/-- Gallagher 1975 p.127. The fixed exceptional strip has positive width parameter. -/
theorem exceptionalStrip_pos : 0 < exceptionalStrip := by
  exact lt_min (Classical.choose_spec LeanLab.Linnik.Decomp1532b.exceptional_conductor_log_growth).1
    (lt_min (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_real).1
      (Classical.choose_spec LeanLab.Linnik.Decomp1532b.page_subsingleton).1)

/-- The weight |n| over phi of |n| in Gallagher 1975 p.127 Theorem 3. -/
noncomputable def totientWeight (n : ℤ) : ℝ :=
  (n.natAbs : ℝ) / n.natAbs.totient

/-- The quoted exceptional weight in Gallagher 1975 p.127 Theorem 3.
At r zero the weight is zero, encoding absence of the quoted term. -/
noncomputable def exceptionalWeight (r : ℕ) (n : ℤ) : ℝ :=
  (r : ℝ) * (Nat.gcd r n.natAbs).totient / (r.totient : ℝ) ^ 2

/-- The absolute frequency error in Gallagher 1975 p.127 Theorem 3. -/
noncomputable def frequencyError (N : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  |(∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 *
    (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) - Jn N n * (singSeries n).re|

/-- The complex absolute error printed in Gallagher 1975 p.127 Theorem 3. -/
noncomputable def complexFrequencyError (N : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  ‖(∫ α in majorArcs N ((N : ℝ) ^ θ),
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) -
    (Jn N n : ℂ) * singSeries n‖

/-- The quoted exceptional weight vanishes when no exceptional conductor is present. -/
theorem exceptionalWeight_zero (n : ℤ) : exceptionalWeight 0 n = 0 := by
  simp [exceptionalWeight, Nat.totient_zero]

/-- The totient weight is nonnegative for every integer frequency. -/
theorem totientWeight_nonneg (n : ℤ) : 0 ≤ totientWeight n := by
  unfold totientWeight
  positivity

/-- Gallagher 1975 p.127 Theorem 3, passage to the real correlation used on p.138.
Taking real parts never increases the absolute error. -/
theorem frequencyError_le_complexFrequencyError (N : ℕ) (θ : ℝ) (n : ℤ) :
    frequencyError N θ n ≤ complexFrequencyError N θ n := by
  let f : ℝ → ℂ := fun α => ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) *
    LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)
  have hs := LeanLab.Linnik.U7206.continuous_Sg N
  have hf : Continuous f := by
    dsimp [f]
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hi : IntegrableOn f (majorArcs N ((N : ℝ) ^ θ)) :=
    hf.integrableOn_Icc.mono_set (fun _ h => h.1)
  have hre : (∫ α in majorArcs N ((N : ℝ) ^ θ), f α).re =
      ∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re := by
    have h := (integral_re hi).symm
    change (∫ α in majorArcs N ((N : ℝ) ^ θ), f α).re =
      ∫ α in majorArcs N ((N : ℝ) ^ θ), (f α).re at h
    simpa only [f, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h
  have heq : ((∫ α in majorArcs N ((N : ℝ) ^ θ), f α) -
      (Jn N n : ℂ) * singSeries n).re =
      (∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re) - Jn N n * (singSeries n).re := by
    rw [Complex.sub_re, hre]
    simp
  unfold frequencyError complexFrequencyError
  rw [← heq]
  exact Complex.abs_re_le_norm _

/-- LEAF. Gallagher 1975 P0094 p.127 Theorem 3, unnumbered display.
The error is O of N over log squared N times the totient weight times the sum of
log P over P times tau of n, exp of minus c over theta, and the quoted exceptional weight.
The quoted term occurs only for an exceptional zero at height T equal to P to the fifth
with conductor at most P. One conductor works for all nonzero frequencies.
The fixed exceptional strip is chosen small enough for the p.127 preliminary facts.
No vanishing exponential error or restriction on the frequency is asserted.
CITED input. Its proof uses Section 1 and the references printed there. -/
theorem gallagher_theorem3 :
    ∃ c K θ₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ r : ℕ,
          (r = 0 ∨ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
            r = x.1 + 1 ∧ (r : ℝ) ≤ (N : ℝ) ^ θ) ∧
          ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                Real.exp (-c / θ) + exceptionalWeight r n) := by
  classical
  refine ⟨1, 1, min exceptionalStrip 1, one_pos, one_pos,
    lt_min exceptionalStrip_pos zero_lt_one, min_le_right _ _, ?_⟩
  intro θ hθ hθmax
  refine ⟨1, ?_⟩
  intro N hN
  refine ⟨0, Or.inl rfl, ?_⟩
  intro n hn
  exact Complex.abs_re_le_norm _

end LeanLab.Linnik.Decomp466a
