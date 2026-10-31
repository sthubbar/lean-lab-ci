/-
P0070, p. 367, the conductor blocks in equations 36 to 38.
These are finite reductions with actual zero multiplicities.
No density estimate or zero free assertion is assumed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.GaussReduction97
import LeanLab.PerelliPintz1992.ConductorWindow

namespace LeanLab.PerelliPintz1992.Section6
open Real Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Equation 38, p. 367: in a conductor block r at least B, the weight
X divided by square root r is bounded by X divided by square root B. -/
theorem weighted_conductor_block (R : Finset ℕ+) (B X U σ T : ℝ) (K : ENNReal)
    (hB : 0 < B) (hX : 0 ≤ X)
    (hR : ∀ r ∈ R, B ≤ (r : ℝ) ∧ (r : ℝ) ≤ U)
    (hK : ∀ r ∈ R, allCharacterCount r σ T ≤ K) :
    (∑ r ∈ R, ENNReal.ofReal (X / sqrt (r : ℝ)) *
      ∑ ψ : DirichletCharacter ℂ (r : ℕ), if ψ.IsPrimitive then zeroCount ψ σ T else 0) ≤
      ENNReal.ofReal (X / sqrt B) *
        min (primitiveCount U σ T) ((R.card : ENNReal) * K) := by
  calc
    _ ≤ ∑ r ∈ R, ENNReal.ofReal (X / sqrt B) *
        ∑ ψ : DirichletCharacter ℂ (r : ℕ), if ψ.IsPrimitive then zeroCount ψ σ T else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul' ?_ le_rfl
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_left hX (Real.sqrt_pos.mpr hB)
        (Real.sqrt_le_sqrt (hR r hr).1)
    _ = ENNReal.ofReal (X / sqrt B) *
        (∑ r ∈ R, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
          if ψ.IsPrimitive then zeroCount ψ σ T else 0) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul' le_rfl (primitive_count_min_bound R U σ T K
      (fun r hr => (hR r hr).2) hK)

/-- LEAF. Equations 37 and 38, p. 367: every selected conductor subfamily has
both the global primitive count bound and the uniform Farey conductor count bound. -/
theorem farey_conductor_subfamily_min_bound (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : Finset ℚ, ∀ M : ℕ, 1 ≤ M → ∀ Q H ξ : ℝ,
      (M : ℝ) ≤ Q → 0 < H →
      (∀ x ∈ F, M ≤ x.den ∧ x.den ≤ 2 * M) →
      (∀ x ∈ F, ∃ α : ℝ,
        |(x : ℝ) - α| ≤ 1 / ((x.den : ℝ) * Q) ∧ |α - ξ| ≤ 1 / H) →
      ∀ R : Finset ℕ+, R ⊆ positiveConductors (fareyWindowModuli F) →
      ∀ U σ T : ℝ, (∀ r ∈ R, (r : ℝ) ≤ U) → ∀ K : ENNReal,
      (∀ r ∈ R, allCharacterCount r σ T ≤ K) →
      (∑ r ∈ R, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then zeroCount ψ σ T else 0) ≤
        min (primitiveCount U σ T)
          (ENNReal.ofReal (C * ((M : ℝ) ^ 2 / H + 1) * (M : ℝ) ^ ν) * K) := by
  obtain ⟨C, hC, hbound⟩ := farey_window_conductors ν hν
  refine ⟨C, hC, ?_⟩
  intro F M hM Q H ξ hMQ hH hden hmeet R hR U σ T hU K hK
  have hc : (R.card : ℝ) ≤ C * ((M : ℝ) ^ 2 / H + 1) * (M : ℝ) ^ ν := by
    calc
      _ ≤ ((positiveConductors (fareyWindowModuli F)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hR
      _ = ((characterConductors (fareyWindowModuli F)).card : ℝ) := by
        rw [positiveConductors_card]
      _ ≤ _ := hbound F M hM Q H ξ hMQ hH hden hmeet
  have hce : (R.card : ENNReal) ≤
      ENNReal.ofReal (C * ((M : ℝ) ^ 2 / H + 1) * (M : ℝ) ^ ν) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hc
  exact (primitive_count_min_bound R U σ T K hU hK).trans
    (min_le_min le_rfl (mul_le_mul' hce le_rfl))


/-- Actual conductors in the dyadic block with binary logarithm j, p. 367. -/
def conductorBlock (Q : Finset ℕ+) (j : ℕ) : Finset ℕ+ :=
  (positiveConductors Q).filter (fun r => Nat.log 2 (r : ℕ) = j)

/-- Each actual conductor is at most the upper bound for its inducing moduli. -/
theorem positiveConductors_le (Q : Finset ℕ+) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    ∀ r ∈ positiveConductors Q, (r : ℕ) ≤ X := by
  intro r hr
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hr
  exact (Nat.le_of_dvd c.1.val.property c.2.conductor_dvd_level).trans (hQ c.1.val c.1.property)

/-- The actual conductor block lies between 2 to j and 2 to j plus one. -/
theorem conductorBlock_range (Q : Finset ℕ+) (j : ℕ) {r : ℕ+}
    (hr : r ∈ conductorBlock Q j) :
    2 ^ j ≤ (r : ℕ) ∧ (r : ℕ) < 2 ^ (j + 1) := by
  have hj := (Finset.mem_filter.mp hr).2
  rw [← hj]
  exact ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt r.property),
    Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- LEAF. Equation 36, p. 367, with an explicit logarithmic factor and a finite supremum.
The dyadic blocks contain only actual primitive conductors. -/
theorem weighted_primitive_dyadic_reduction (Q : Finset ℕ+) (σ T : ℝ) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    (∑ c : Σ q : Q, DirichletCharacter ℂ (q.val : ℕ),
      ENNReal.ofReal ‖gaussSum c.2 ZMod.stdAddChar‖ * zeroCount c.2 σ T) ≤
    ((Nat.log 2 X + 1 : ℕ) : ENNReal) *
      (Finset.range (Nat.log 2 X + 1)).sup (fun j =>
        ENNReal.ofReal ((X : ℝ) / sqrt ((2 : ℝ) ^ j)) *
          ∑ r ∈ conductorBlock Q j, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
            if ψ.IsPrimitive then zeroCount ψ σ T else 0) := by
  let f : ℕ+ → ENNReal := fun r => ENNReal.ofReal ((X : ℝ) / sqrt (r : ℝ)) *
    ∑ ψ : DirichletCharacter ℂ (r : ℕ), if ψ.IsPrimitive then zeroCount ψ σ T else 0
  let g : ℕ → ENNReal := fun j => ENNReal.ofReal ((X : ℝ) / sqrt ((2 : ℝ) ^ j)) *
    ∑ r ∈ conductorBlock Q j, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
      if ψ.IsPrimitive then zeroCount ψ σ T else 0
  let J := Finset.range (Nat.log 2 X + 1)
  have hmap : ∀ r ∈ positiveConductors Q, Nat.log 2 (r : ℕ) ∈ J := by
    intro r hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.log_mono_right (positiveConductors_le Q X hQ r hr)))
  have hgroup : ∑ r ∈ positiveConductors Q, f r = ∑ j ∈ J, ∑ r ∈ conductorBlock Q j, f r := by
    exact (Finset.sum_fiberwise_of_maps_to hmap f).symm
  calc
    _ ≤ ∑ r ∈ positiveConductors Q, f r := weighted_primitive_reduction Q σ T X hQ
    _ = ∑ j ∈ J, ∑ r ∈ conductorBlock Q j, f r := hgroup
    _ ≤ ∑ j ∈ J, g j := by
      apply Finset.sum_le_sum
      intro j hj
      dsimp only [g]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul' ?_ le_rfl
      apply ENNReal.ofReal_le_ofReal
      have hlow : (2 : ℝ) ^ j ≤ (r : ℝ) := by exact_mod_cast (conductorBlock_range Q j hr).1
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg X)
        (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hlow)
    _ ≤ ∑ _j ∈ J, J.sup g := Finset.sum_le_sum (fun j hj => Finset.le_sup hj)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

end
end LeanLab.PerelliPintz1992.Section6
