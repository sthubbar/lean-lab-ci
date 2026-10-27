import LeanLab.PNTPort.LargeSieve.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
P0054 author copy page 6 displays 2.5 to 2.9.
Character values are supplied as functions on the natural numbers.
These are algebraic templates. Actual character data, convergence and
the analytic singular series estimates remain conditional.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.CharacterSumsTask53

open Finset
open LeanLab.PNTPort.LargeSieve

/-- The finite character Fourier sum in display 2.7. -/
noncomputable def characterSum (χ : ℕ → ℂ) (q : ℕ) (m : ℤ) : ℂ :=
  ∑ h ∈ Icc 1 q, χ h * e ((h : ℝ) * m / q)

/-- The Gauss sum is the character sum at frequency one. -/
noncomputable def gaussSum (χ : ℕ → ℂ) (q : ℕ) : ℂ := characterSum χ q 1

/-- The principal character values at the supplied modulus. -/
def principalValue (q h : ℕ) : ℂ := if Nat.Coprime h q then 1 else 0

/-- The coefficient in display 2.6 or 2.9 with the exact conjugations. -/
noncomputable def generalizedCoeff (χ ψ : ℕ → ℂ) (q : ℕ) (m : ℤ)
    (difference : Bool) : ℂ :=
  let c := characterSum (fun h => χ h *
    (if difference then (starRingEnd ℂ) (ψ h) else ψ h) * principalValue q h) q (-m)
  let tχ := gaussSum (fun h => (starRingEnd ℂ) (χ h) * principalValue q h) q
  let tψ := gaussSum (fun h => (starRingEnd ℂ) (ψ h) * principalValue q h) q
  c * tχ * (if difference then (starRingEnd ℂ) tψ else tψ) / (Nat.totient q : ℂ) ^ 2

/-- The series template in display 2.5 or 2.8. Convergence is a separate input. -/
noncomputable def generalizedSeries (r s : ℕ) (χ ψ : ℕ → ℂ) (m : ℤ)
    (difference : Bool) : ℂ :=
  ∑' q : ℕ, if 0 < q ∧ Nat.lcm r s ∣ q then generalizedCoeff χ ψ q m difference else 0

/-- Conjugating the character values negates the Fourier frequency. -/
theorem characterSum_conj (χ : ℕ → ℂ) (q : ℕ) (m : ℤ) :
    characterSum (fun h => (starRingEnd ℂ) (χ h)) q (-m) =
      (starRingEnd ℂ) (characterSum χ q m) := by
  unfold characterSum
  rw [map_sum]
  apply sum_congr rfl
  intro h _
  rw [map_mul, Int.cast_neg, mul_neg, neg_div, e_neg]

/-- The trivial finite bound applies to all supplied values of norm at most one. -/
theorem norm_characterSum_le (χ : ℕ → ℂ) (q : ℕ) (m : ℤ)
    (hχ : ∀ h ∈ Icc 1 q, ‖χ h‖ ≤ 1) : ‖characterSum χ q m‖ ≤ q := by
  unfold characterSum
  calc
    _ ≤ ∑ h ∈ Icc 1 q, ‖χ h * e ((h : ℝ) * m / q)‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ Icc 1 q, (1 : ℝ) := by
      apply sum_le_sum
      intro h hh
      simpa only [norm_mul, norm_e, mul_one] using hχ h hh
    _ = q := by simp

/-- The finite character sum is periodic in the integer frequency. -/
theorem characterSum_periodic (χ : ℕ → ℂ) (q : ℕ) (hq : 0 < q) :
    Function.Periodic (characterSum χ q) (q : ℤ) := by
  intro m
  unfold characterSum
  apply sum_congr rfl
  intro h _
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hphase : (h : ℝ) * ((m + (q : ℤ) : ℤ) : ℝ) / q =
      (h : ℝ) * m / q + h := by
    push_cast
    field_simp <;> ring
  have he : e (h : ℝ) = 1 := by simpa using e_int (h : ℤ)
  rw [hphase, e_add, he, mul_one]

/-- The principal character at zero frequency counts the units. -/
theorem principal_zero (q : ℕ) :
    characterSum (principalValue q) q 0 = (Nat.totient q : ℂ) := by
  have hset : Icc 1 q = Ico 1 (1 + q) := by
    ext h
    simp only [mem_Icc, mem_Ico]
    omega
  have hc : ((Icc 1 q).filter (fun h => Nat.Coprime h q)).card = Nat.totient q := by
    rw [hset]
    simpa only [Nat.coprime_comm] using Nat.filter_coprime_Ico_eq_totient q 1
  unfold characterSum principalValue
  simp only [Int.cast_zero, mul_zero, zero_div, e_zero, mul_one]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hc

/-- The finite bound for a supplied complex Dirichlet character. -/
theorem norm_characterSum_dirichlet {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℤ) :
    ‖characterSum (fun h => χ (h : ZMod q)) q m‖ ≤ q :=
  norm_characterSum_le _ q m (fun h _ => χ.norm_le_one (h : ZMod q))

/-- Both coefficient templates have the correct nonzero modulus one model. -/
theorem generalizedCoeff_one (m : ℤ) (difference : Bool) :
    generalizedCoeff (fun _ => 1) (fun _ => 1) 1 m difference = 1 := by
  have hem : e (-(m : ℝ)) = 1 := by
    simpa only [Int.cast_neg] using e_int (-m)
  have he1 : e (1 : ℝ) = 1 := by simpa using e_int (1 : ℤ)
  cases difference <;>
    simp [generalizedCoeff, gaussSum, characterSum, principalValue, Int.cast_neg, hem, he1]

/-- The trivial coefficient majorant uses three finite character sum bounds. -/
theorem norm_generalizedCoeff_le (χ ψ : ℕ → ℂ) (q : ℕ) (m : ℤ) (difference : Bool)
    (hχ : ∀ h ∈ Icc 1 q, ‖χ h‖ ≤ 1) (hψ : ∀ h ∈ Icc 1 q, ‖ψ h‖ ≤ 1) :
    ‖generalizedCoeff χ ψ q m difference‖ ≤
      (q : ℝ) ^ 3 / (Nat.totient q : ℝ) ^ 2 := by
  have hp : ∀ h, ‖principalValue q h‖ ≤ 1 := by
    intro h
    unfold principalValue
    split_ifs <;> norm_num
  have htχ : ‖gaussSum (fun h => (starRingEnd ℂ) (χ h) * principalValue q h) q‖ ≤ q := by
    apply norm_characterSum_le
    intro h hh
    rw [norm_mul, Complex.norm_conj]
    simpa using mul_le_mul (hχ h hh) (hp h) (norm_nonneg _) zero_le_one
  have htψ : ‖gaussSum (fun h => (starRingEnd ℂ) (ψ h) * principalValue q h) q‖ ≤ q := by
    apply norm_characterSum_le
    intro h hh
    rw [norm_mul, Complex.norm_conj]
    simpa using mul_le_mul (hψ h hh) (hp h) (norm_nonneg _) zero_le_one
  have hc : ‖characterSum (fun h => χ h *
      (if difference then (starRingEnd ℂ) (ψ h) else ψ h) * principalValue q h) q (-m)‖ ≤ q := by
    apply norm_characterSum_le
    intro h hh
    have hψ' : ‖if difference then (starRingEnd ℂ) (ψ h) else ψ h‖ ≤ 1 := by
      cases difference <;> simpa using hψ h hh
    rw [norm_mul, norm_mul]
    have hpair : ‖χ h‖ * ‖if difference then (starRingEnd ℂ) (ψ h) else ψ h‖ ≤ 1 := by
      simpa using mul_le_mul (hχ h hh) hψ' (norm_nonneg _) zero_le_one
    simpa using mul_le_mul hpair (hp h) (norm_nonneg _) zero_le_one
  unfold generalizedCoeff
  rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have htψ' : ‖if difference then
      (starRingEnd ℂ) (gaussSum (fun h => (starRingEnd ℂ) (ψ h) * principalValue q h) q)
      else gaussSum (fun h => (starRingEnd ℂ) (ψ h) * principalValue q h) q‖ ≤ q := by
    cases difference <;> simpa using htψ
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ (q : ℝ) * q * q :=
      mul_le_mul (mul_le_mul hc htχ (norm_nonneg _) (Nat.cast_nonneg _)) htψ'
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by ring

/-- The trivial coefficient majorant is not a convergence argument. -/
theorem coefficient_majorant_not_summable :
    ¬ Summable (fun q : ℕ => (q : ℝ) ^ 3 / (Nat.totient q : ℝ) ^ 2) := by
  intro hs
  have hsmall : ∀ᶠ q : ℕ in Filter.atTop,
      (q : ℝ) ^ 3 / (Nat.totient q : ℝ) ^ 2 < 1 :=
    hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  set q := N + 1
  have hq : 0 < q := by omega
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφle : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφsq : (Nat.totient q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.totient q)) hφle 2
    have h3 := mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hq1)
    nlinarith
  have hge : (1 : ℝ) ≤ (q : ℝ) ^ 3 / (Nat.totient q : ℝ) ^ 2 :=
    (one_le_div (by positivity)).mpr hφsq
  have hlt := hN q (by dsimp [q]; omega)
  linarith

end LeanLab.Pintz2021.CharacterSumsTask53

#print axioms LeanLab.Pintz2021.CharacterSumsTask53.characterSum_conj
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.norm_characterSum_le
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.characterSum_periodic
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.principal_zero
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.norm_characterSum_dirichlet
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.generalizedCoeff_one
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.norm_generalizedCoeff_le
#print axioms LeanLab.Pintz2021.CharacterSumsTask53.coefficient_majorant_not_summable
