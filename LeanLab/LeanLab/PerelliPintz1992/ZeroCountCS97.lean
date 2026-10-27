/-
P0070, p. 366, the finite count Cauchy-Schwarz step in equation 34.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.PerelliPintz1992.Section6
open Real Finset

/-- LEAF. Equation 34, p. 366: a finite sum of square roots of natural multiplicity
counts is bounded by both their sum and square root of the family size times their sum.
Applying this to actual zero counts still requires their finite natural count realization. -/
theorem finite_zero_sqrt_min {ι : Type*} (Z : Finset ι) (m : ι → ℕ) :
    (∑ i ∈ Z, sqrt (m i : ℝ)) ≤
      min (∑ i ∈ Z, (m i : ℝ)) (sqrt ((Z.card : ℝ) * ∑ i ∈ Z, (m i : ℝ))) := by
  apply le_min
  · apply Finset.sum_le_sum
    intro i hi
    apply Real.sqrt_le_self_iff.mpr
    rcases Nat.eq_zero_or_pos (m i) with hm | hm
    · exact Or.inl (by exact_mod_cast hm)
    · exact Or.inr (by exact_mod_cast hm)
  · apply Real.le_sqrt_of_sq_le
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Z (fun _ => (1 : ℝ))
      (fun i => sqrt (m i : ℝ))
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      Real.sq_sqrt (Nat.cast_nonneg _)] using hh


/-- A finite actual zero multiplicity count is a natural number. This is the count
interpretation needed when applying the finite form of 34 on p. 366. -/
theorem zeroCount_eq_nat_of_ne_top {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ)
    (hfinite : zeroCount χ σ T ≠ ⊤) : ∃ n : ℕ, zeroCount χ σ T = (n : ENNReal) := by
  classical
  let f : ℂ → ENat := fun ρ =>
    if ρ ∈ zeroRegion σ T then analyticOrderAt χ.LFunction ρ else 0
  have he : (∑' ρ : ℂ, f ρ).toENNReal = zeroCount χ σ T := by
    calc
      _ = ∑' ρ : ℂ, (f ρ).toENNReal :=
        Topology.IsClosedEmbedding.map_tsum f (g := ENat.toENNRealRingHom)
          ENat.isClosedEmbedding_toENNReal
      _ = _ := by
        unfold zeroCount
        apply tsum_congr
        intro ρ
        by_cases hρ : ρ ∈ zeroRegion σ T <;> simp [f, hρ]
  have hf : (∑' ρ : ℂ, f ρ) ≠ ⊤ := by
    intro hh
    apply hfinite
    rw [← he, hh]
    rfl
  refine ⟨(∑' ρ : ℂ, f ρ).toNat, ?_⟩
  rw [← he]
  have hh := congrArg ENat.toENNReal (ENat.natCast_toNat hf)
  simpa only [ENat.toENNReal_coe] using hh.symm

/-- LEAF. Equation 34, p. 366: the actual character zero counts satisfy both
count envelopes once every count is finite. No density estimate is assumed. -/
theorem character_zero_sqrt_min (q : ℕ+) (σ T : ℝ)
    (hfinite : ∀ χ : DirichletCharacter ℂ (q : ℕ), zeroCount χ σ T ≠ ⊤) :
    (∑ χ : DirichletCharacter ℂ (q : ℕ), sqrt ((zeroCount χ σ T).toReal)) ≤
      min (allCharacterCount q σ T).toReal
        (sqrt ((q : ℝ) * (allCharacterCount q σ T).toReal)) := by
  classical
  choose n hn using fun χ => zeroCount_eq_nat_of_ne_top χ σ T (hfinite χ)
  have hto : ∀ χ : DirichletCharacter ℂ (q : ℕ), (zeroCount χ σ T).toReal = (n χ : ℝ) := by
    intro χ
    rw [hn χ]
    simp
  have hsum : (allCharacterCount q σ T).toReal =
      ∑ χ : DirichletCharacter ℂ (q : ℕ), (n χ : ℝ) := by
    unfold allCharacterCount
    rw [tsum_fintype, ENNReal.toReal_sum (fun χ _ => hfinite χ)]
    apply Finset.sum_congr rfl
    intro χ hχ
    exact hto χ
  have hcard : Fintype.card (DirichletCharacter ℂ (q : ℕ)) ≤ (q : ℕ) := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q : ℕ)]
    exact Nat.totient_le _
  simp_rw [hto]
  rw [hsum]
  apply (finite_zero_sqrt_min (Finset.univ : Finset (DirichletCharacter ℂ (q : ℕ))) n).trans
  apply min_le_min le_rfl
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun χ _ => Nat.cast_nonneg (n χ)))
  simpa only [Finset.card_univ] using (show
    (Fintype.card (DirichletCharacter ℂ (q : ℕ)) : ℝ) ≤ (q : ℝ) by exact_mod_cast hcard)

end LeanLab.PerelliPintz1992.Section6
