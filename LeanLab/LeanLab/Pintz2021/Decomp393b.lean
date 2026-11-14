import LeanLab.Pintz2021.Decomp393a

/-!
Explicit stabilization thresholds for the DecompJ803 cutoff audit.
Source: arXiv:1804.05561v1 page 5 display 1.22 and page 9 display 2.12.
These are derived arithmetic bounds. They do not supply a zero density estimate.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Decomp393b

open Filter Topology Finset State1581 DecompJ281 Truncation168

attribute [local instance] Classical.propDecidable

/-- Moduli at most P give character cutoff at most P squared when P is at least one. -/
theorem UCutoff_le_sq_level (z w : ExcPair) (m : ℕ) {P : ℝ}
    (hP : 1 ≤ P) (hz : (z.r : ℝ) ≤ P) (hw : (w.r : ℝ) ≤ P) :
    UCutoff z w m ≤ P ^ 2 := by
  letI : NeZero z.r := z.hr
  letI : NeZero w.r := w.hr
  have hzr : 0 ≤ (z.r : ℝ) := Nat.cast_nonneg _
  have hwr : 0 ≤ (w.r : ℝ) := Nat.cast_nonneg _
  have hg : (1 : ℝ) ≤ Nat.gcd z.r w.r := by
    exact_mod_cast Nat.gcd_pos_of_pos_left w.r (NeZero.pos z.r)
  have hgmz : (1 : ℝ) ≤ Nat.gcd m z.r := by
    exact_mod_cast Nat.gcd_pos_of_pos_right m (NeZero.pos z.r)
  have hgmw : (1 : ℝ) ≤ Nat.gcd m w.r := by
    exact_mod_cast Nat.gcd_pos_of_pos_right m (NeZero.pos w.r)
  have hPsq : P ≤ P ^ 2 := by nlinarith
  have hLpos : 0 < Nat.lcm z.r w.r := Nat.lcm_pos (NeZero.pos z.r) (NeZero.pos w.r)
  letI : NeZero (Nat.lcm z.r w.r) := ⟨hLpos.ne'⟩
  have hcond : ((lift z (Nat.lcm z.r w.r) *
      (lift w (Nat.lcm z.r w.r))⁻¹).conductor : ℝ) ≤ P ^ 2 := by
    have hcle : (lift z (Nat.lcm z.r w.r) *
        (lift w (Nat.lcm z.r w.r))⁻¹).conductor ≤ Nat.lcm z.r w.r :=
      Nat.le_of_dvd hLpos (DirichletCharacter.conductor_dvd_level _)
    calc
      _ ≤ (Nat.lcm z.r w.r : ℝ) := by exact_mod_cast hcle
      _ ≤ (z.r : ℝ) * w.r := by exact_mod_cast Nat.lcm_le_mul (NeZero.pos z.r) (NeZero.pos w.r)
      _ ≤ P * P := mul_le_mul hz hw hwr (by linarith)
      _ = P ^ 2 := (pow_two P).symm
  simp only [UCutoff, max_le_iff]
  exact ⟨⟨(div_le_self (sq_nonneg _) (by nlinarith : (1 : ℝ) ≤
      (Nat.gcd z.r w.r : ℝ) ^ 2)).trans (pow_le_pow_left₀ hzr hz 2),
    (div_le_self (sq_nonneg _) (by nlinarith : (1 : ℝ) ≤
      (Nat.gcd z.r w.r : ℝ) ^ 2)).trans (pow_le_pow_left₀ hwr hw 2)⟩,
    ⟨⟨(div_le_self hzr hgmz).trans (hz.trans hPsq),
      (div_le_self hwr hgmw).trans (hw.trans hPsq)⟩, hcond⟩⟩

/-- Height and squared level bounds remove every restriction except the lcm condition. -/
theorem retainedPairs_eq_lcm_of_bounds (E : Finset ExcPair) {P U : ℝ} (m : ℕ)
    (hP : 1 ≤ P) (hU : P ^ 2 ≤ U)
    (hr : ∀ z ∈ E, (z.r : ℝ) ≤ P) (hγ : ∀ z ∈ E, |z.ρ.im| ≤ U) :
    retainedPairs E P U m =
      (E ×ˢ E).filter (fun p => (Nat.lcm p.1.r p.2.r : ℝ) ≤ P) := by
  ext p
  simp only [retainedPairs, mem_filter, mem_product]
  constructor
  · rintro ⟨hp, _, _, hl, _⟩
    exact ⟨hp, hl⟩
  · rintro ⟨⟨hz, hw⟩, hl⟩
    exact ⟨⟨hz, hw⟩, hγ _ hz, hγ _ hw, hl,
      (UCutoff_le_sq_level _ _ m hP (hr _ hz) (hr _ hw)).trans hU⟩

/-- For the actual exceptional set, max of square root X and P squared suffices. -/
theorem actual_truncated_eq_lcm_sum (E : Finset ExcPair) (H X ε P U : ℝ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (m : ℕ)
    (hE : (E : Set ExcPair) = excSet H (Real.sqrt X) P X)
    (hP : 1 ≤ P) (hγ : Real.sqrt X ≤ U) (hU : P ^ 2 ≤ U) :
    mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg ε X P U m =
      ∑ p ∈ (E ×ˢ E).filter (fun p => (Nat.lcm p.1.r p.2.r : ℝ) ≤ P),
        pairTerm Sg ε X m p := by
  have he : ∀ z ∈ E, z ∈ excSet H (Real.sqrt X) P X := by
    intro z hz
    rw [← hE]
    exact hz
  have hr : ∀ z ∈ E, (z.r : ℝ) ≤ P := by
    intro z hz
    rcases Set.mem_insert_iff.mp (he z hz) with hz | hz
    · simpa [hz, pole] using hP
    · exact hz.1
  have hi : ∀ z ∈ E, |z.ρ.im| ≤ U := by
    intro z hz
    rcases Set.mem_insert_iff.mp (he z hz) with hz | hz
    · simpa [hz, pole] using (Real.sqrt_nonneg X).trans hγ
    · exact hz.2.2.2.2.trans hγ
  rw [← hE, DecompJ665.truncatedPrime_eq_finite, truncatedPrime,
    retainedPairs_eq_lcm_of_bounds E m hP hU hr hi]

/-- The sealed leaf's bound at fixed actual data forces the discarded lcm sum to vanish. -/
theorem actual_bound_forces_discarded_lcm_sum_eq_zero (E : Finset ExcPair)
    (H X ε P C : ℝ) (Sg : ExcPair → ExcPair → ℕ → ℂ) (m : ℕ)
    (hE : (E : Set ExcPair) = excSet H (Real.sqrt X) P X)
    (hb : ∀ U : ℝ, 2 ≤ U →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg ε X P U m‖ ≤
          C * (Sing m * X * Real.log U / Real.sqrt U)) :
    ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
      pairTerm Sg ε X m p = 0 := by
  apply Decomp393a.discarded_lcm_sum_eq_zero_of_eventual_bound E Sg ε X P
    (C * (Sing m * X)) m
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with U hU
  rw [hE]
  convert hb U hU using 1 <;> ring

/-- At level one the actual truncation is exact above the height bound and one. -/
theorem level_one_truncation_exact (H X ε U : ℝ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (m : ℕ)
    (hγ : Real.sqrt X ≤ U) (hU : 1 ≤ U) :
    mainTermPrime (excSet H (Real.sqrt X) 1 X) Sg ε X m =
      mainTermTruncatedPrime (excSet H (Real.sqrt X) 1 X) Sg ε X 1 U m := by
  classical
  let E := (DecompJ665.excSet_finite H (Real.sqrt X) 1 X).toFinset
  have hE : (E : Set ExcPair) = excSet H (Real.sqrt X) 1 X := Set.Finite.coe_toFinset _
  rw [actual_truncated_eq_lcm_sum E H X ε 1 U Sg m hE le_rfl hγ (by simpa using hU),
    ← hE, mainTermPrime_eq_sum]
  apply congrArg (fun F : Finset (ExcPair × ExcPair) => ∑ p ∈ F, pairTerm Sg ε X m p)
  symm
  apply filter_eq_self.mpr
  intro p hp
  have hz : p.1 ∈ excSet H (Real.sqrt X) 1 X := by
    rw [← hE]
    exact (mem_product.mp hp).1
  have hw : p.2 ∈ excSet H (Real.sqrt X) 1 X := by
    rw [← hE]
    exact (mem_product.mp hp).2
  rw [DecompJ665.modulus_one_of_mem le_rfl hz, DecompJ665.modulus_one_of_mem le_rfl hw]
  norm_num

end LeanLab.Pintz2021.Decomp393b

#print axioms LeanLab.Pintz2021.Decomp393b.UCutoff_le_sq_level
#print axioms LeanLab.Pintz2021.Decomp393b.retainedPairs_eq_lcm_of_bounds
#print axioms LeanLab.Pintz2021.Decomp393b.actual_truncated_eq_lcm_sum

#print axioms LeanLab.Pintz2021.Decomp393b.actual_bound_forces_discarded_lcm_sum_eq_zero

#print axioms LeanLab.Pintz2021.Decomp393b.level_one_truncation_exact
