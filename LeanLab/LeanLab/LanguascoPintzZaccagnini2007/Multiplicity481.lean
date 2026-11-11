import LeanLab.LanguascoPintzZaccagnini2007.ZeroFacts481
import LeanLab.LanguascoPintzZaccagnini2007.Instances481

/-!
Positive analytic multiplicities for the zero family in P0045 page 5.
This supplies a nonempty instance of the indexed count hypotheses.
It does not assert a zero density estimate.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Complex Real Set Filter Finset
open LeanLab.PNTPort.DirichletZF.U1482
open scoped Classical Topology

/-- P0045 page 5, multiplicity sentence before Lemma 4.1.
A zero of a nonzero entire function has finite positive analytic multiplicity. -/
theorem entire_zero_multiplicity_pos481 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h2 : f 2 ≠ 0) {ρ : ℂ} (hz : f ρ = 0) : 0 < analyticOrderNatAt f ρ := by
  have hfinite : analyticOrderAt f ρ ≠ ⊤ := by
    intro h
    have hev : f =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp h
    have heq : EqOn f 0 Set.univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => hf.analyticAt z) isPreconnected_univ (Set.mem_univ ρ) hev
    exact h2 (heq (Set.mem_univ 2))
  have hne : analyticOrderAt f ρ ≠ 0 := (hf.analyticAt ρ).analyticOrderAt_ne_zero.mpr hz
  apply Nat.pos_of_ne_zero
  intro h
  apply hne
  rw [← Nat.cast_analyticOrderNatAt hfinite, h, Nat.cast_zero]

/-- P0045 pages 4 and 5, display 8 and the multiplicity convention in Lemma 4.1.
Every actual member of the zero box has a positive natural analytic multiplicity. -/
theorem zeroBox_multiplicity_pos481 {X : ℕ} {H T P : ℝ}
    {z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ} (hz : z ∈ zeroBox481 X H T P) :
    0 < analyticOrderNatAt (Lfun481 z.2.1) z.2.2 := by
  rcases z with ⟨r, χ, ρ⟩
  have hr : 1 ≤ r := hz.1
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  by_cases hχ : χ = 1
  · have hprim := hz.2.2.1
    have hr1 : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hρ : ρ ≠ 1 := by
      intro he
      have hlt := hz.2.2.2.2.2.1
      rw [he] at hlt
      norm_num at hlt
    have h2 : gZ 2 ≠ 0 := by
      rw [gZ_of_ne (by norm_num)]
      exact mul_ne_zero (by norm_num)
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))
    have heq : Lfun481 χ = riemannZeta := by
      funext s
      simp [Lfun481, hχ, DirichletCharacter.LFunction_modOne_eq]
    have hzζ : riemannZeta ρ = 0 := by simpa only [heq] using hz.2.2.2.1
    have hzG : gZ ρ = 0 := by rw [gZ_of_ne hρ, hzζ, mul_zero]
    have hp := entire_zero_multiplicity_pos481 gZ
      (fun s => (gZ_analyticAt s).differentiableAt) h2 hzG
    rw [ord_gZ hρ] at hp
    simpa only [heq] using hp
  · have heq : Lfun481 χ = DirichletCharacter.LFunction χ := by
      funext s
      simp [Lfun481, hr0]
    have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    rw [heq]
    exact entire_zero_multiplicity_pos481 _ (DirichletCharacter.differentiable_LFunction hχ)
      h2 (by simpa only [heq] using hz.2.2.2.1)

/-- P0045 page 5, multiplicity convention: a genuine singleton zero family satisfies the count input.
The chosen character is the principal character modulo one and the zero is minus two. -/
theorem indexed_zero_singleton_instance481 :
    ∃ z : Fin 1 → Σ r : ℕ, DirichletCharacter ℂ r × ℂ,
      (∀ i, z i ∈ zeroBox481 2 (3 * Real.log 2) 1 2) ∧
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) ∧
      (1 : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ) := by
  let w : Σ r : ℕ, DirichletCharacter ℂ r × ℂ := ⟨1, 1, -2⟩
  let z : Fin 1 → Σ r : ℕ, DirichletCharacter ℂ r × ℂ := fun _ => w
  have hw : w ∈ zeroBox481 2 (3 * Real.log 2) 1 2 := zeroBox_nonempty_instance481
  have hp : 1 ≤ analyticOrderNatAt (Lfun481 w.2.1) w.2.2 := zeroBox_multiplicity_pos481 hw
  have hmult : ∀ v, (univ.filter (fun i => z i = v)).card ≤
      analyticOrderNatAt (Lfun481 v.2.1) v.2.2 := by
    intro v
    by_cases hv : v = w
    · subst v
      simpa [z] using hp
    · simp [z, Ne.symm hv]
  exact ⟨z, fun _ => hw, hmult, by simpa using indexed_zero_count481 z hmult⟩

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.entire_zero_multiplicity_pos481
#print axioms LeanLab.LPZ2007.zeroBox_multiplicity_pos481
#print axioms LeanLab.LPZ2007.indexed_zero_singleton_instance481
