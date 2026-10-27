/-
P0070, p. 367, the Gauss weight in equation 36.
Reuse the existing induced Gauss bound from ExceptionalSet.Lu2010GaussBound.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.InducedZeros
import LeanLab.PerelliPintz1992.ConductorCount
import LeanLab.ExceptionalSet.Lu2010GaussBound

namespace LeanLab.PerelliPintz1992.Section6
open Real Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 367, equation 36: induction bounds the Gauss weight by square root r. -/
theorem induced_gauss_le_sqrt {r q : ℕ+} (h : (r : ℕ) ∣ (q : ℕ))
    (ψ : DirichletCharacter ℂ (r : ℕ)) (hψ : ψ.IsPrimitive) :
    ‖gaussSum (ψ.changeLevel h) ZMod.stdAddChar‖ ≤ sqrt (r : ℝ) := by
  have hb := LeanLab.ExceptionalSet.Lu2010GaussBound.induced_gauss_norm_sq_le ψ hψ h
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 hb

/-- LEAF. Page 367, equation 36: for each primitive ψ, all induced Gauss weighted
zero counts are at most X divided by square root r times the zero count of ψ.
This includes infinite ENNReal zero counts and needs no density hypothesis. -/
theorem weighted_induced_zeroCount_le (Q : Finset ℕ+) {r : ℕ+}
    (ψ : DirichletCharacter ℂ (r : ℕ)) (hψ : ψ.IsPrimitive) (σ T : ℝ) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    (∑ c ∈ inducedFamily Q ψ,
      ENNReal.ofReal ‖gaussSum c.2 ZMod.stdAddChar‖ * zeroCount c.2 σ T) ≤
      ENNReal.ofReal ((X : ℝ) / sqrt (r : ℝ)) * zeroCount ψ σ T := by
  have hr : 0 < (r : ℝ) := by exact_mod_cast r.property
  have hs : 0 < sqrt (r : ℝ) := Real.sqrt_pos.mpr hr
  calc
    _ ≤ ∑ _c ∈ inducedFamily Q ψ, ENNReal.ofReal (sqrt (r : ℝ)) * zeroCount ψ σ T := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨h, hh⟩ := (Finset.mem_filter.mp hc).2
      rw [← hh, zeroCount_changeLevel]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (induced_gauss_le_sqrt h ψ hψ)) le_rfl
    _ = ENNReal.ofReal ((inducedFamily Q ψ).card * sqrt (r : ℝ)) * zeroCount ψ σ T := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((X : ℝ) / sqrt (r : ℝ)) * zeroCount ψ σ T := by
      apply mul_le_mul' ?_ le_rfl
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((X : ℝ) / r) * sqrt (r : ℝ) :=
          mul_le_mul_of_nonneg_right (inducedFamily_card_le Q ψ X hQ) hs.le
        _ = (X : ℝ) / sqrt (r : ℝ) := by
          have he := Real.sq_sqrt hr.le
          field_simp
          nlinarith


/-- The positive conductors of the actual characters at moduli in Q, p. 367. -/
def positiveConductors (Q : Finset ℕ+) : Finset ℕ+ :=
  Finset.univ.image (fun c : Σ q : Q, DirichletCharacter ℂ (q.val : ℕ) =>
    (⟨c.2.conductor, Nat.pos_of_ne_zero c.2.conductor_ne_zero⟩ : ℕ+))

/-- LEAF. Equation 36, p. 367, before dyadic grouping: sum over the actual primitive
conductors with the factor X divided by square root r. No density bound is assumed. -/
theorem weighted_primitive_reduction (Q : Finset ℕ+) (σ T : ℝ) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    (∑ c : Σ q : Q, DirichletCharacter ℂ (q.val : ℕ),
      ENNReal.ofReal ‖gaussSum c.2 ZMod.stdAddChar‖ * zeroCount c.2 σ T) ≤
    ∑ r ∈ positiveConductors Q,
      ENNReal.ofReal ((X : ℝ) / sqrt (r : ℝ)) *
        ∑ ψ : DirichletCharacter ℂ (r : ℕ), if ψ.IsPrimitive then zeroCount ψ σ T else 0 := by
  let f : (Σ q : Q, DirichletCharacter ℂ (q.val : ℕ)) → ENNReal :=
    fun c => ENNReal.ofReal ‖gaussSum c.2 ZMod.stdAddChar‖ * zeroCount c.2 σ T
  have hcover : ∀ c, f c ≤ ∑ r ∈ positiveConductors Q,
      ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then if c ∈ inducedFamily Q ψ then f c else 0 else 0 := by
    intro c
    let r : ℕ+ := ⟨c.2.conductor, Nat.pos_of_ne_zero c.2.conductor_ne_zero⟩
    have hr : r ∈ positiveConductors Q := Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
    have hp : c.2.primitiveCharacter.IsPrimitive := c.2.primitiveCharacter_isPrimitive
    have hi : c ∈ inducedFamily Q (r := r) c.2.primitiveCharacter := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, c.2.conductor_dvd_level, c.2.changeLevel_primitiveCharacter⟩
    have hinner : f c ≤ ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then if c ∈ inducedFamily Q ψ then f c else 0 else 0 := by
      have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun ψ : DirichletCharacter ℂ (r : ℕ) =>
          if ψ.IsPrimitive then if c ∈ inducedFamily Q ψ then f c else 0 else 0)
        (fun _ _ => bot_le) (Finset.mem_univ c.2.primitiveCharacter)
      dsimp only [r] at hh hi ⊢
      split_ifs at hh with hp'
      · exact hh
      · exact False.elim (hp' hp)
    apply hinner.trans
    exact Finset.single_le_sum (f := fun r : ℕ+ =>
      ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then if c ∈ inducedFamily Q ψ then f c else 0 else 0)
      (fun _ _ => bot_le) hr
  calc
    _ ≤ ∑ c, ∑ r ∈ positiveConductors Q, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then if c ∈ inducedFamily Q ψ then f c else 0 else 0 :=
      Finset.sum_le_sum (fun c _ => hcover c)
    _ = ∑ r ∈ positiveConductors Q, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then ∑ c ∈ inducedFamily Q ψ, f c else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ψ hψ
      by_cases hp : ψ.IsPrimitive
      · simp only [ite_eq_left hp]
        rw [← Finset.sum_filter]
        congr 1
        ext c
        simp
      · simp only [ite_eq_right hp, Finset.sum_const_zero]
    _ ≤ ∑ r ∈ positiveConductors Q, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
        if ψ.IsPrimitive then
          ENNReal.ofReal ((X : ℝ) / sqrt (r : ℝ)) * zeroCount ψ σ T else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro ψ hψ
      by_cases hp : ψ.IsPrimitive
      · simp only [ite_eq_left hp]
        exact weighted_induced_zeroCount_le Q ψ hp σ T X hQ
      · simp only [ite_eq_right hp, le_refl]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ hψ
      by_cases hp : ψ.IsPrimitive <;> simp [hp]


/-- The positive conductor encoding has exactly the previously defined conductor count. -/
theorem positiveConductors_card (Q : Finset ℕ+) :
    (positiveConductors Q).card = (characterConductors Q).card := by
  apply Finset.card_nbij (fun r : ℕ+ => (r : ℕ))
  · intro r hr
    obtain ⟨c, _, he⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, congrArg (fun r : ℕ+ => (r : ℕ)) he⟩
  · intro r hr s hs he
    exact Subtype.ext he
  · intro r hr
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨⟨c.2.conductor, Nat.pos_of_ne_zero c.2.conductor_ne_zero⟩,
      Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, rfl⟩

/-- The two count bounds used in the first minimum of 38, p. 367.
The finite primitive sum is bounded by both the global primitive count and the number
of selected conductors times any bound on each fixed modulus count. -/
theorem primitive_count_min_bound (R : Finset ℕ+) (U σ T : ℝ) (K : ENNReal)
    (hR : ∀ r ∈ R, (r : ℝ) ≤ U) (hK : ∀ r ∈ R, allCharacterCount r σ T ≤ K) :
    (∑ r ∈ R, ∑ ψ : DirichletCharacter ℂ (r : ℕ),
      if ψ.IsPrimitive then zeroCount ψ σ T else 0) ≤
      min (primitiveCount U σ T) ((R.card : ENNReal) * K) := by
  apply le_min
  · have hh := ENNReal.sum_le_tsum (f := fun r : ℕ+ =>
        if (r : ℝ) ≤ U then ∑' ψ : DirichletCharacter ℂ (r : ℕ),
          if ψ.IsPrimitive then zeroCount ψ σ T else 0 else 0) R
    apply le_trans ?_ hh
    apply Finset.sum_le_sum
    intro r hr
    rw [ite_eq_left (hR r hr), tsum_fintype]
  · calc
      _ ≤ ∑ r ∈ R, K := by
        apply Finset.sum_le_sum
        intro r hr
        apply le_trans ?_ (hK r hr)
        unfold allCharacterCount
        rw [tsum_fintype]
        apply Finset.sum_le_sum
        intro ψ hψ
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end
end LeanLab.PerelliPintz1992.Section6
