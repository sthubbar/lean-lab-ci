/-
P0093 page 160 equation 5.5. Finite coefficient energy for the mixed term.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp491b
import LeanLab.PNTPort.LargeSieve.Multiplicative

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- P0093 page 156 equation 3.4. The single character reduced residue phase. -/
noncomputable def residuePhase555 (q : ℕ) (n : ℤ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
    χ a * Complex.exp
      (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)

/-- LEAF. P0093 page 160 equation 5.5. Character Parseval gives the exact
energy of the residue phases at every signed frequency. -/
theorem residuePhase_energy555 (q : ℕ) [NeZero q] (n : ℤ) :
    (∑ χ : DirichletCharacter ℂ q, ‖residuePhase555 q n χ‖ ^ 2) =
      (q.totient : ℝ) ^ 2 := by
  classical
  let S : ZMod q → ℂ := fun a => Complex.exp
    (((2 * Real.pi * (n : ℝ) * ((a.val : ℝ) / q) : ℝ) : ℂ) * Complex.I)
  have hc (χ : DirichletCharacter ℂ q) :
      (∑ a : ZMod q, χ a * S a) = residuePhase555 q n χ := by
    rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range]
    unfold residuePhase555
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : Nat.Coprime a q
    · rw [ite_eq_left hcop]
      dsimp only [S]
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)]
    · have hz : χ (a : ZMod q) = 0 :=
        MulChar.map_nonunit χ (by simpa only [ZMod.isUnit_iff_coprime] using hcop)
      simp [hz, hcop]
  have he := LeanLab.PNTPort.LargeSieve.sum_chars_normSq S
  simp_rw [hc] at he
  have hs : (∑ a : ZMod q, if IsUnit a then ‖S a‖ ^ 2 else 0) =
      (q.totient : ℝ) := by
    rw [LeanLab.PNTPort.LargeSieve.sum_zmod_eq_sum_range]
    simp only [S, Complex.norm_exp_ofReal_mul_I, one_pow, ZMod.isUnit_iff_coprime]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext a
    simp [Nat.coprime_comm]
  rw [hs] at he
  simpa only [pow_two] using he

/-- LEAF. P0093 page 160 equation 5.5. The conjugate Gauss coefficients have
exact total squared norm equal to the square of the totient. -/
theorem conjugateGauss_energy555 (q : ℕ) [NeZero q] :
    (∑ χ : DirichletCharacter ℂ q, ‖conjugateGauss491 q χ‖ ^ 2) =
      (q.totient : ℝ) ^ 2 := by
  have he (χ : DirichletCharacter ℂ q) :
      conjugateGauss491 q χ = star (residuePhase555 q 1 χ) := by
    simp [conjugateGauss491, residuePhase555]
  simp_rw [he, norm_star]
  exact residuePhase_energy555 q 1

/-- LEAF. P0093 page 156 equation 3.4. Exchanging the two characters leaves
an ordered character contribution unchanged. -/
theorem characterPair_comm555 (N q : ℕ) (n : ℤ)
    (χ ψ : DirichletCharacter ℂ q) :
    characterPair491 N q n χ ψ = characterPair491 N q n ψ χ := by
  unfold characterPair491
  have hm (a : ℕ) : χ a * ψ a = ψ a * χ a := mul_comm _ _
  have hi (z : ℝ) : characterPrime280 χ N z * characterPrime280 ψ N z =
      characterPrime280 ψ N z * characterPrime280 χ N z := mul_comm _ _
  simp_rw [hm, hi]
  ring

/-- LEAF. P0093 page 160 equation 5.5. Cauchy Schwarz controls the sum of
Gauss and frequency phase products by the square of the totient. -/
theorem mixed_coefficient_sum555 (q : ℕ) [NeZero q] (n : ℤ) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖) ≤
        (q.totient : ℝ) ^ 2 := by
  classical
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
        ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun χ _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ Real.sqrt (∑ χ : DirichletCharacter ℂ q, ‖conjugateGauss491 q χ‖ ^ 2) *
        Real.sqrt (∑ χ : DirichletCharacter ℂ q, ‖residuePhase555 q n χ‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [conjugateGauss_energy555, residuePhase_energy555]
      simp only [Real.sqrt_sq (Nat.cast_nonneg _)]
      ring

/-- LEAF. P0093 page 160 equation 5.5. Removing the oscillatory phase bounds
one mixed ordered pair by its finite coefficient times the unsigned mixed mass. -/
theorem characterPair_principal_le555 (N q : ℕ) (n : ℤ)
    (χ : DirichletCharacter ℂ q) (hq : 1 ≤ q) (hN : 1 ≤ N)
    (hG : ‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ ≤ 1) :
    ‖characterPair491 N q n 1 χ‖ ≤
      (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
        (q.totient : ℝ) ^ 2) *
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
          ‖characterPrime280 χ N z‖) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set r : ℝ := 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hS : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (1 : DirichletCharacter ℂ q) a * χ a * Complex.exp
        (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      residuePhase555 q n χ := by
    unfold residuePhase555
    apply Finset.sum_congr rfl
    intro a ha
    rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr (mem_filter.mp ha).2),
      one_mul]
  have hI : ‖∫ z in -r..r,
      characterPrime280 (1 : DirichletCharacter ℂ q) N z * characterPrime280 χ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖ := by
    have h := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun z => characterPrime280 (1 : DirichletCharacter ℂ q) N z *
        characterPrime280 χ N z *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))
      (show -r ≤ r by linarith)
    simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using h
  have hmass : 0 ≤ ∫ z in -r..r,
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
        ‖characterPrime280 χ N z‖ :=
    intervalIntegral.integral_nonneg (by linarith) (fun z _ => by positivity)
  unfold characterPair491
  rw [hS]
  simp only [norm_mul, norm_div, norm_pow, norm_one, Complex.norm_natCast]
  change 1 / (q.totient : ℝ) ^ 2 * _ * _ * _ * _ ≤ _
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 2 * 1 * ‖conjugateGauss491 q χ‖ *
        ‖residuePhase555 q n χ‖) *
        (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
          ‖characterPrime280 χ N z‖) := by
      apply mul_le_mul _ hI (norm_nonneg _) (by positivity)
      gcongr
    _ = _ := by ring

/-- LEAF. P0093 page 160 equation 5.5. A common unsigned mixed mass bound
controls the whole mixed term by twice that bound through total finite energy. -/
theorem mixedTerm_of_mass555 (N q : ℕ) [NeZero q] (n : ℤ) (M : ℝ)
    (hq : 1 ≤ q) (hN : 1 ≤ N) (hM : 0 ≤ M)
    (hG : ‖conjugateGauss491 q (1 : DirichletCharacter ℂ q)‖ ≤ 1)
    (hmass : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ *
          ‖characterPrime280 χ N z‖) ≤ M) :
    ‖mixedTerm491 N q n‖ ≤ 2 * M := by
  classical
  let s := univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)
  have hp : ∀ χ ∈ s,
      ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ ≤
        2 * M / (q.totient : ℝ) ^ 2 *
          (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖) := by
    intro χ hχ
    have hb := (characterPair_principal_le555 N q n χ hq hN hG).trans
      (mul_le_mul_of_nonneg_left (hmass χ (by simpa [s] using hχ)) (by positivity))
    rw [characterPair_comm555 N q n χ 1]
    calc
      _ ≤ ‖characterPair491 N q n 1 χ‖ + ‖characterPair491 N q n 1 χ‖ := norm_add_le _ _
      _ ≤ 2 * (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ /
          (q.totient : ℝ) ^ 2 * M) := by linarith
      _ = _ := by ring
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  calc
    ‖mixedTerm491 N q n‖ ≤ ∑ χ ∈ s,
        ‖characterPair491 N q n 1 χ + characterPair491 N q n χ 1‖ := norm_sum_le _ _
    _ ≤ ∑ χ ∈ s, 2 * M / (q.totient : ℝ) ^ 2 *
        (‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖) := Finset.sum_le_sum hp
    _ = 2 * M / (q.totient : ℝ) ^ 2 *
        ∑ χ ∈ s, ‖conjugateGauss491 q χ‖ * ‖residuePhase555 q n χ‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * M / (q.totient : ℝ) ^ 2 * (q.totient : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (mixed_coefficient_sum555 q n) (by positivity)
    _ = 2 * M := by field_simp [hφ]

end LeanLab.Linnik1951
