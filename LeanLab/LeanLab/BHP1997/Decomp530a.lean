/-
P0069 page 22, Lemma 8 and Rademacher reference 28.
Rademacher pages 195, 198 and 199 give the strip and Gamma inputs.
This module does not import the contour target.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Repair499Euler

namespace LeanLab.BHP1997.DecompC165a.Contour230

/-- Pages 22 and 23, auxiliary regular contour and Perron step. -/
theorem principal_residue_factor_le (q : ℕ) : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)‖ ≤ 1 := by
  calc
    _ ≤ ∏ p ∈ q.primeFactors, ‖(1 - (p : ℂ)⁻¹)‖ := Finset.norm_prod_le _ _
    _ ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        have hp1 : (1 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
        have hreal : (1 - (p : ℂ)⁻¹) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        · have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
          linarith
        · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)


end LeanLab.BHP1997.DecompC165a.Contour230

namespace LeanLab.BHP1997.Decomp530a
open Classical Complex Set Filter ZMod
open scoped Topology

/-- Page 22, the residue of the principal character and zero for other characters. -/
noncomputable def poleResidue {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ = 1 then ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) else 0

/-- Page 22, subtract the principal pole and fill its removable value. -/
noncomputable def regularPart {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ := by
  classical
  exact if χ = 1 then dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 else χ.LFunction

/-- Page 22, the pole-subtracted L-function extends to an entire function. -/
theorem regularPart_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (regularPart χ) := by
  classical
  unfold regularPart
  split_ifs with h
  · rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  · exact DirichletCharacter.differentiable_LFunction h

/-- Rademacher page 199, the root number in the functional equation has norm one.
The finite Fourier inversion formula supplies the Gauss sum norm. -/
theorem rootNumber_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  have hgs : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
    have hi : χ⁻¹.IsPrimitive := by
      simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
    have he : 𝓕 (χ : ZMod q → ℂ) =
        fun k => χ⁻¹ (-k) * gaussSum χ stdAddChar := funext hχ.fourierTransform_eq_inv_mul_gaussSum
    have hh := congrFun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
    rw [he, ZMod.dft_mul_const, ZMod.dft_comp_neg] at hh
    simp only [neg_neg, hi.fourierTransform_eq_inv_mul_gaussSum, inv_inv, map_one,
      smul_eq_mul, mul_one] at hh
    have hstar : star (gaussSum χ stdAddChar) = χ (-1) * gaussSum χ⁻¹ stdAddChar := by
      rw [star_gaussSum_eq, AddChar.inv_mulShift]
      change gaussSum χ⁻¹ (stdAddChar.mulShift ((-1 : (ZMod q)ˣ) : ZMod q)) = _
      rw [gaussSum_mulShift_eq]
      simp
    have hs := Complex.mul_conj (gaussSum χ stdAddChar)
    change gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = _ at hs
    rw [hstar] at hs
    have ht : (‖gaussSum χ stdAddChar‖ ^ 2 : ℂ) = q := by
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← hs]
      linear_combination hh
    exact_mod_cast ht
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I,
    one_pow, div_one, Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
  have hn : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
    rw [← hgs, Real.sqrt_sq (norm_nonneg _)]
  simpa [hn, Real.sqrt_eq_rpow] using
    div_self (ne_of_gt (Real.rpow_pos_of_pos (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q) (1 / 2)))

/-- Page 22, split the L-function into its entire regular part and its principal pole. -/
theorem LFunction_eq_regularPart_add_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    χ.LFunction s = regularPart χ s + poleResidue χ / (s - 1) := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    simp only [regularPart, poleResidue, ↓reduceIte]
    rw [dslope_of_ne _ hs, slope_def_field]
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
      Function.update_self, DirichletCharacter.LFunctionTrivChar]
    field_simp
    ring
  · simp [regularPart, poleResidue, hχ]

/-- Page 22, the norm of the residue is at most one. -/
theorem poleResidue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖poleResidue χ‖ ≤ 1 := by
  classical
  unfold poleResidue
  split_ifs
  · exact LeanLab.BHP1997.DecompC165a.Contour230.principal_residue_factor_le q
  · simp

/-- Page 22, subtracting or restoring the pole costs its reciprocal distance. -/
theorem pole_norm_bounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s ≠ 1) :
    ‖regularPart χ s‖ ≤ ‖χ.LFunction s‖ + 1 / ‖s - 1‖ ∧
    ‖χ.LFunction s‖ ≤ ‖regularPart χ s‖ + 1 / ‖s - 1‖ := by
  have hp : ‖poleResidue χ / (s - 1)‖ ≤ 1 / ‖s - 1‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right (poleResidue_norm_le χ) (norm_nonneg _)
  have hi := LFunction_eq_regularPart_add_pole χ hs
  constructor
  · have hr : regularPart χ s = χ.LFunction s - poleResidue χ / (s - 1) :=
      eq_sub_iff_add_eq.mpr hi.symm
    rw [hr]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hp)
  · calc ‖χ.LFunction s‖ = ‖regularPart χ s + poleResidue χ / (s - 1)‖ := congrArg norm hi
         _ ≤ ‖regularPart χ s‖ + 1 / ‖s - 1‖ :=
           (norm_add_le _ _).trans (add_le_add le_rfl hp)

/-- Rademacher page 198, display 6.1, with the principal pole subtracted.
The constant is independent of the modulus and the character. -/
theorem regularPart_right_bound {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖regularPart χ (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ 1 + 2 / δ := by
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + t * I
  have hsre : s.re = 1 + δ := by simp [s]
  have hs : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, one_re] at this
    linarith
  have hd : δ ≤ ‖s - 1‖ := by
    have hh := Complex.abs_re_le_norm (s - 1)
    simpa [hsre, abs_of_pos hδ] using hh
  have hb := Repair499Euler.LFunction_norm_le χ (s := s) (by rw [hsre]; linarith)
  have hi := (pole_norm_bounds χ hs).1
  have hp : 1 / ‖s - 1‖ ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ hd
  change ‖regularPart χ s‖ ≤ _
  rw [hsre] at hb
  norm_num only [add_sub_cancel_left] at hb
  rw [show 2 / δ = 1 / δ + 1 / δ by ring]
  linarith

/-- Rademacher pages 198 and 199, expose the Gamma quotient in the primitive functional equation. -/
theorem primitive_functional_equation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : 1 < (1 - s).re) :
    χ.LFunction s = (q : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
      (χ⁻¹.gammaFactor (1 - s) / χ.gammaFactor s) * χ⁻¹.LFunction (1 - s) := by
  have hg : χ⁻¹.gammaFactor (1 - s) ≠ 0 := by
    classical
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  have hs' : 1 - s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have he := hχ.completedLFunction_one_sub (1 - s)
  simp only [sub_sub_cancel] at he
  have hright : χ⁻¹.completedLFunction (1 - s) =
      χ⁻¹.LFunction (1 - s) * χ⁻¹.gammaFactor (1 - s) := by
    exact ((eq_div_iff hg).mp
      (χ⁻¹.LFunction_eq_completed_div_gammaFactor (1 - s) (Or.inl hs'))).symm
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0), he, hright]
  rw [show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring]
  ring

/-- Rademacher page 199, auxiliary Euler factor estimate for induced characters. -/
theorem left_euler_factor_bound {p : ℕ} (hp : p.Prime) {δ t : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - z * (p : ℂ) ^ (-((-δ : ℝ) : ℂ) - (t : ℂ) * I)‖ ≤
      (if p = 2 ∨ p = 3 then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 2 + δ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn : ‖(p : ℂ) ^ (-((-δ : ℝ) : ℂ) - (t : ℂ) * I)‖ = (p : ℝ) ^ δ := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp
  have h1 : 1 ≤ (p : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hp.one_le) hδ
  have hr : 1 ≤ Real.sqrt (p : ℝ) := (Real.le_sqrt (by norm_num) hpR.le).mpr (by exact_mod_cast hp.one_le)
  have he : (p : ℝ) ^ (1 / 2 + δ) = Real.sqrt p * (p : ℝ) ^ δ := by
    rw [Real.rpow_add hpR, Real.sqrt_eq_rpow]
  have hb : ‖1 - z * (p : ℂ) ^ (-((-δ : ℝ) : ℂ) - (t : ℂ) * I)‖ ≤ 2 * (p : ℝ) ^ δ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, hn]
    nlinarith [Real.rpow_nonneg hpR.le δ]
  rw [he]
  split_ifs with h
  · nlinarith [Real.rpow_nonneg hpR.le δ]
  · have hp5 : 4 ≤ p := by have := hp.two_le; omega
    have hr2 : 2 ≤ Real.sqrt (p : ℝ) := (Real.le_sqrt (by norm_num) hpR.le).mpr (by exact_mod_cast hp5)
    nlinarith [Real.rpow_nonneg hpR.le δ]

/-- Rademacher page 199, auxiliary finite prime product for the induced left edge. -/
theorem weighted_prime_product_le (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ m.primeFactors)
    {a : ℝ} (ha : 0 ≤ a) :
    (∏ p ∈ S, (if p = 2 ∨ p = 3 then (2 : ℝ) else 1) * (p : ℝ) ^ a) ≤
      4 * (m : ℝ) ^ a := by
  have hcoef : (∏ p ∈ S, if p = 2 ∨ p = 3 then (2 : ℝ) else 1) ≤ 4 := by
    have he (p : ℕ) : (if p = 2 ∨ p = 3 then (2 : ℝ) else 1) =
        (if p = 2 then (2 : ℝ) else 1) * (if p = 3 then (2 : ℝ) else 1) := by
      split_ifs <;> simp_all
    simp_rw [he]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    split_ifs <;> norm_num
  have hprod : (∏ p ∈ S, p) ≤ m := by
    exact Nat.le_of_dvd hm ((Finset.prod_dvd_prod_of_subset S m.primeFactors id hS).trans (Nat.prod_primeFactors_dvd m))
  have hpow : (∏ p ∈ S, (p : ℝ) ^ a) ≤ (m : ℝ) ^ a := by
    rw [Real.finsetProd_rpow S (fun p : ℕ => (p : ℝ)) (by intro p hp; positivity) a]
    apply Real.rpow_le_rpow (by positivity) _ ha
    simpa only [Nat.cast_prod] using (show ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (m : ℝ) from by exact_mod_cast hprod)
  rw [Finset.prod_mul_distrib]
  exact mul_le_mul hcoef hpow (by positivity) (by norm_num)

/-- Rademacher page 199, display 6.2. CONDITIONAL ON the explicit Gamma quotient estimate. -/
theorem primitive_left_bound {δ G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : s.re = -δ)
    (hgamma : ‖χ⁻¹.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤
      G * (|s.im| + 2) ^ (1 / 2 + δ)) :
    ‖χ.LFunction s‖ ≤ G * (1 + 1 / δ) *
      ((q : ℝ) * (|s.im| + 2)) ^ (1 / 2 + δ) := by
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp only [hs, zero_re] at this; linarith
  have hs1 : 1 < (1 - s).re := by simp only [sub_re, one_re, hs]; linarith
  have hb := Repair499Euler.LFunction_norm_le χ⁻¹ hs1
  have hbr : ‖χ⁻¹.LFunction (1 - s)‖ ≤ 1 + 1 / δ := by
    simpa only [sub_re, one_re, hs, sub_neg_eq_add, add_sub_cancel_left] using hb
  rw [primitive_functional_equation χ hχ hs0 hs1, norm_mul, norm_mul, norm_mul,
    rootNumber_norm χ hχ, mul_one, Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
  have hre : (1 / 2 - s).re = 1 / 2 + δ := by simp [hs]
  rw [hre]
  calc _ ≤ (q : ℝ) ^ (1 / 2 + δ) * (G * (|s.im| + 2) ^ (1 / 2 + δ)) * (1 + 1 / δ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hgamma (Real.rpow_nonneg (Nat.cast_nonneg q) _))
        hbr (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.mul_rpow (Nat.cast_nonneg q) (by positivity : 0 ≤ |s.im| + 2)]; ring

/-- Rademacher page 199, elementary Euler product transfer from a divisor modulus. -/
theorem induced_euler_product_bound {d q : ℕ} [NeZero d] (hdq : d ∣ q) (hq : 0 < q)
    (χ : DirichletCharacter ℂ d) {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    ‖∏ p ∈ q.primeFactors,
      (1 - χ (p : ZMod d) * (p : ℂ) ^ (-(((-δ : ℝ) : ℂ) + t * I)))‖ ≤
      4 * ((q / d : ℕ) : ℝ) ^ (1 / 2 + δ) := by
  classical
  let S := q.primeFactors.filter fun p => ¬p ∣ d
  have hS : S ⊆ (q / d).primeFactors := by
    intro p hp
    obtain ⟨hpq, hpd⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hpq
    apply Nat.mem_primeFactors.mpr
    refine ⟨hprime, ?_, Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hq hdq) (Nat.pos_of_dvd_of_pos hdq hq))⟩
    have hpq' := Nat.dvd_of_mem_primeFactors hpq
    have he : q = d * (q / d) := (Nat.mul_div_cancel' hdq).symm
    rw [he] at hpq'
    exact (hprime.dvd_mul.mp hpq').resolve_left hpd
  have he : (∏ p ∈ q.primeFactors,
      (1 - χ (p : ZMod d) * (p : ℂ) ^ (-(((-δ : ℝ) : ℂ) + t * I)))) =
      ∏ p ∈ S, (1 - χ (p : ZMod d) * (p : ℂ) ^ (-(((-δ : ℝ) : ℂ) + t * I))) := by
    classical
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hd : p ∣ d := by simpa only [Finset.mem_filter, hp, true_and, not_not] using hnot
    have hz : χ (p : ZMod d) = 0 := by
      apply χ.map_nonunit
      intro hu
      have hc := (ZMod.isUnit_iff_coprime p d).mp hu
      exact ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hc) hd
    simp [hz]
  rw [he, norm_prod]
  calc
    _ ≤ ∏ p ∈ S, (if p = 2 ∨ p = 3 then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 2 + δ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      simpa only [neg_add, sub_eq_add_neg] using
        left_euler_factor_bound hprime hδ (t := t) (χ.norm_le_one (p : ZMod d))
    _ ≤ _ := weighted_prime_product_le (q / d)
      (Nat.div_pos (Nat.le_of_dvd hq hdq) (NeZero.pos d)) S hS (by linarith)

/-- Rademacher page 199 display 6.2 extended by the proved finite Euler transfer.
CONDITIONAL ON the uniform Gamma quotient estimate. -/
theorem all_character_left_bound {δ G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G)
    (hgamma : ∀ (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d)
      (s : ℂ), s.re = -δ →
      ‖ψ⁻¹.gammaFactor (1 - s) / ψ.gammaFactor s‖ ≤
        G * (|s.im| + 2) ^ (1 / 2 + δ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖χ.LFunction (((-δ : ℝ) : ℂ) + t * I)‖ ≤
      (4 * G * (1 + 1 / δ)) * ((q : ℝ) * (|t| + 2)) ^ (1 / 2 + δ) := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let s : ℂ := ((-δ : ℝ) : ℂ) + t * I
  have hs : s.re = -δ := by simp [s]
  have hs1 : s ≠ 1 := by intro he; have := congrArg Complex.re he; simp only [hs, one_re] at this; linarith
  have hi := primitive_left_bound hδ hG χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs
    (hgamma _ χ.primitiveCharacter s hs)
  have hp := induced_euler_product_bound χ.conductor_dvd_level (NeZero.pos q)
    χ.primitiveCharacter hδ.le t
  have he := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (s := s) (Or.inr hs1)
  rw [χ.changeLevel_primitiveCharacter] at he
  have hcast : (χ.conductor : ℝ) * ((q / χ.conductor : ℕ) : ℝ) = q := by
    exact_mod_cast Nat.mul_div_cancel' χ.conductor_dvd_level
  have hbase : ((χ.conductor : ℝ) * (|t| + 2)) * ((q / χ.conductor : ℕ) : ℝ) =
      (q : ℝ) * (|t| + 2) := by rw [mul_right_comm, hcast]
  have hi' : ‖χ.primitiveCharacter.LFunction s‖ ≤ G * (1 + 1 / δ) *
      ((χ.conductor : ℝ) * (|t| + 2)) ^ (1 / 2 + δ) := by simpa [s] using hi
  change ‖χ.LFunction s‖ ≤ _
  rw [he, norm_mul]
  calc
    _ ≤ (G * (1 + 1 / δ) * ((χ.conductor : ℝ) * (|t| + 2)) ^ (1 / 2 + δ)) *
        (4 * ((q / χ.conductor : ℕ) : ℝ) ^ (1 / 2 + δ)) :=
      mul_le_mul hi' hp (norm_nonneg _) (by positivity)
    _ = (4 * G * (1 + 1 / δ)) *
        (((χ.conductor : ℝ) * (|t| + 2)) * ((q / χ.conductor : ℕ) : ℝ)) ^ (1 / 2 + δ) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (χ.conductor : ℝ) * (|t| + 2)) (Nat.cast_nonneg _)]
      ring
    _ = _ := by rw [hbase]

/-- Rademacher page 195 display 3.4, auxiliary Gaussian localization estimate. -/
theorem gaussian_linear_decay (u : ℝ) : (|u| + 2) * Real.exp (-(u ^ 2)) ≤ 3 := by
  have h1 : 1 ≤ Real.exp (u ^ 2) := Real.one_le_exp (sq_nonneg u)
  have hu : |u| ≤ Real.exp (u ^ 2) := by
    have he := Real.add_one_le_exp (u ^ 2)
    nlinarith [sq_nonneg (|u| - 1 / 2), sq_abs u]
  have hh := mul_le_mul_of_nonneg_right (by linarith : |u| + 2 ≤ 3 * Real.exp (u ^ 2))
    (Real.exp_pos (-(u ^ 2))).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hh

/-- Rademacher page 195 display 3.4, the exact Gaussian localization norm. -/
theorem localized_norm (f : ℂ → ℂ) (t σ : ℝ) (z : ℂ) :
    ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ =
      ‖f (z + t * I)‖ * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [pow_two, Complex.mul_re]

/-- Rademacher page 195 display 3.4, Gaussian localization bounds the whole strip.
CONDITIONAL ON the explicit exponential strip growth premise. -/
theorem localized_bddAbove (f : ℂ → ℂ) {δ σ t C B : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 < C) (hB : 0 < B)
    (hg : ∀ s : ℂ, -δ ≤ s.re → s.re ≤ 1 + δ →
      ‖f s‖ ≤ C * Real.exp (B * |s.im|)) :
    BddAbove ((norm ∘ (fun z : ℂ => f (z + t * I) * Complex.exp ((z - σ) ^ 2))) ''
      Complex.HadamardThreeLines.verticalClosedStrip (-δ) (1 + δ)) := by
  use C * Real.exp (B * |t| + 4 + B ^ 2 / 4)
  rintro y ⟨z, hz, rfl⟩
  have hzr : -δ ≤ z.re ∧ z.re ≤ 1 + δ := hz
  have hr : (z.re - σ) ^ 2 ≤ 4 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 2 - (z.re - σ))
      (by linarith : 0 ≤ 2 + (z.re - σ))
    nlinarith
  have hc : B * (|z.im| + |t|) + ((z.re - σ) ^ 2 - z.im ^ 2) ≤
      B * |t| + 4 + B ^ 2 / 4 := by
    nlinarith [sq_nonneg (|z.im| - B / 2), sq_abs z.im]
  have hb := hg (z + t * I) (by simpa using hzr.1) (by simpa using hzr.2)
  simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at hb
  have hnorm : ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ =
      ‖f (z + t * I)‖ * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) := by
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [pow_two, Complex.mul_re]
  change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ (C * Real.exp (B * |z.im + t|)) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ ≤ (C * Real.exp (B * (|z.im| + |t|))) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) := by
      gcongr
      exact abs_add_le _ _
    _ = C * Real.exp (B * (|z.im| + |t|) + ((z.re - σ) ^ 2 - z.im ^ 2)) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc) hC.le

/-- Rademacher page 195 display 3.4, auxiliary weighted strip interpolation.
CONDITIONAL ON explicit strip growth and the two boundary estimates.
Gaussian localization reduces this to Mathlib HadamardThreeLines. -/
theorem weighted_strip_interpolation {δ : ℝ} (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q A : ℝ, 1 ≤ Q → 0 < A →
      ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ,
        -δ ≤ s.re → s.re ≤ 1 + δ → ‖f s‖ ≤ C * Real.exp (B * |s.im|)) →
      (∀ t : ℝ, ‖f (((-δ : ℝ) : ℂ) + t * I)‖ ≤
        A * (Q * (|t| + 2)) ^ (1 / 2 + δ)) →
      (∀ t : ℝ, ‖f (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ A) →
      ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
        ‖f ((σ : ℂ) + t * I)‖ ≤
          K * A * (Q * (|t| + 1)) ^ ((1 + δ - σ) / 2) := by
  refine ⟨3 * Real.exp 4, by positivity, ?_⟩
  intro Q A hQ hA f hf hg hleft hright σ t hσ0 hσ1
  obtain ⟨C, B, hC, hB, hg⟩ := hg
  let K : ℝ := 3 * Real.exp 4
  let P : ℝ := Q * (|t| + 1)
  let a : ℝ := 1 / 2 + δ
  let g : ℂ → ℂ := fun z => f (z + t * I) * Complex.exp ((z - σ) ^ 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have h4 (z : ℂ) (hz : -δ ≤ z.re ∧ z.re ≤ 1 + δ) : (z.re - σ) ^ 2 ≤ 4 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 2 - (z.re - σ))
      (by linarith : 0 ≤ 2 + (z.re - σ))
    nlinarith
  have hdamp (z : ℂ) (hz : -δ ≤ z.re ∧ z.re ≤ 1 + δ) :
      (|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) ≤ K := by
    calc
      _ ≤ (|z.im| + 2) * Real.exp (4 - z.im ^ 2) := by
        gcongr
        exact h4 z hz
      _ = Real.exp 4 * ((|z.im| + 2) * Real.exp (-(z.im ^ 2))) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ Real.exp 4 * 3 := mul_le_mul_of_nonneg_left (gaussian_linear_decay z.im) (Real.exp_pos _).le
      _ = K := by dsimp [K]; ring
  have hgl (z : ℂ) (hz : z.re = -δ) : ‖g z‖ ≤ K * A * P ^ a := by
    have he : z + t * I = (((-δ : ℝ) : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [hz]
    have hl := hleft (z.im + t)
    have hheight : |z.im + t| + 2 ≤ (|t| + 1) * (|z.im| + 2) := by
      have hh := abs_add_le z.im t
      nlinarith [abs_nonneg z.im, abs_nonneg t]
    have hp : (Q * (|z.im + t| + 2)) ^ a ≤ P ^ a * (|z.im| + 2) := by
      calc
        _ ≤ (P * (|z.im| + 2)) ^ a := by
          apply Real.rpow_le_rpow (by positivity) _ ha
          dsimp [P]
          nlinarith
        _ = P ^ a * (|z.im| + 2) ^ a := Real.mul_rpow hP.le (by positivity)
        _ ≤ P ^ a * (|z.im| + 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg z.im]) ha1)
            (Real.rpow_nonneg hP.le _)
    have hn : ‖f (z + t * I)‖ ≤ (A * P ^ a) * (|z.im| + 2) := by
      rw [he]
      calc
        _ ≤ A * (P ^ a * (|z.im| + 2)) := hl.trans (mul_le_mul_of_nonneg_left hp hA.le)
        _ = _ := by ring
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ ((A * P ^ a) * (|z.im| + 2)) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = (A * P ^ a) * ((|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2)) := by ring
      _ ≤ (A * P ^ a) * K := mul_le_mul_of_nonneg_left
        (hdamp z (by constructor <;> rw [hz] <;> linarith)) (by positivity)
      _ = _ := by ring
  have hgr (z : ℂ) (hz : z.re = 1 + δ) : ‖g z‖ ≤ K * A := by
    have he : z + t * I = (((1 + δ : ℝ) : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [hz]
    have hr : ‖f (z + t * I)‖ ≤ A := by rw [he]; exact hright (z.im + t)
    have hr4 := h4 z (by constructor <;> rw [hz] <;> linarith)
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ A * Real.exp 4 := mul_le_mul hr (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.im]))
        (Real.exp_pos _).le hA.le
      _ ≤ K * A := by dsimp [K]; nlinarith [Real.exp_pos 4]
  have hgd : Differentiable ℂ g := by
    dsimp [g]
    exact (hf.comp (by fun_prop)).mul (by fun_prop)
  have hgb := localized_bddAbove f hδ hδhalf hσ0 hσ1 hC hB hg (t := t)
  have hi := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := g) (z := (σ : ℂ)) (l := -δ) (u := 1 + δ)
    (by linarith) (by constructor <;> simp only [ofReal_re] <;> linarith)
    hgd.diffContOnCl hgb
    (fun z hz => hgl z (by simpa using hz)) (fun z hz => hgr z (by simpa using hz))
  simp only [g, sub_self, zero_pow (by norm_num : 2 ≠ 0), Complex.exp_zero, mul_one,
    ofReal_re, sub_neg_eq_add] at hi
  let w : ℝ := (σ + δ) / (1 + 2 * δ)
  have hden : 1 + δ + δ = 1 + 2 * δ := by ring
  rw [hden] at hi
  change ‖f ((σ : ℂ) + t * I)‖ ≤ (K * A * P ^ a) ^ (1 - w) * (K * A) ^ w at hi
  have hex : a * (1 - w) = (1 + δ - σ) / 2 := by
    dsimp [a, w]
    field_simp [show 1 + 2 * δ ≠ 0 by linarith]
    ring
  have hKA : 0 < K * A := mul_pos hK hA
  have halg : (K * A * P ^ a) ^ (1 - w) * (K * A) ^ w =
      K * A * P ^ ((1 + δ - σ) / 2) := by
    rw [Real.mul_rpow hKA.le (Real.rpow_nonneg hP.le a), ← Real.rpow_mul hP.le, hex]
    calc
      _ = ((K * A) ^ (1 - w) * (K * A) ^ w) * P ^ ((1 + δ - σ) / 2) := by ring
      _ = _ := by rw [← Real.rpow_add hKA, sub_add_cancel, Real.rpow_one]
  exact hi.trans_eq halg


/-- Rademacher pages 197 and 198, normalize the printed Gamma ratio for both parities.
CONDITIONAL ON the explicit ordinary Gamma quotient estimate. -/
theorem gamma_quotient_normalization {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hgamma : ∀ (Q : ℝ), 0 ≤ Q → ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
        Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤
        (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : s.re = -δ) :
    ‖χ⁻¹.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤
      (|s.im| + 2) ^ (1 / 2 + δ) := by
  have haux (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
      ‖Complex.Gammaℝ ((Q : ℂ) + 1 - s) / Complex.Gammaℝ ((Q : ℂ) + s)‖ ≤
        (|s.im| + 2) ^ (1 / 2 + δ) := by
    have hr := hgamma Q hQ0 s (by rw [hs]; linarith) (by rw [hs]; linarith)
    have hn : ‖(Q : ℂ) + 1 + s‖ ≤ |s.im| + 2 := by
      have hh := Complex.norm_le_abs_re_add_abs_im ((Q : ℂ) + 1 + s)
      simp only [add_re, ofReal_re, one_re, add_im, ofReal_im, one_im, zero_add, hs] at hh
      rw [abs_of_nonneg (by linarith : 0 ≤ Q + 1 + -δ)] at hh
      linarith
    have hb : (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 + δ) ≤
        (|s.im| + 2) ^ (1 / 2 + δ) :=
      Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg ((Q : ℂ) + 1 + s), abs_nonneg s.im]) (by linarith)
    have hpi : Real.pi ^ (-δ - 1 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, mul_div_mul_comm,
      ← Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    rw [show -((Q : ℂ) + 1 - s) / 2 - (-((Q : ℂ) + s) / 2) = s - 1 / 2 by ring]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    rw [show (s - 1 / 2).re = -δ - 1 / 2 by simp [hs]]
    rw [show ((Q : ℂ) + 1 - s) / 2 = (Q : ℂ) / 2 + (1 - s) / 2 by ring,
      show ((Q : ℂ) + s) / 2 = (Q : ℂ) / 2 + s / 2 by ring]
    have hr' : ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
        Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤ (|s.im| + 2) ^ (1 / 2 + δ) := by
      simpa only [hs, sub_neg_eq_add] using hr.trans (by simpa only [hs, sub_neg_eq_add] using hb)
    simpa only [one_mul] using mul_le_mul hpi hr' (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hi : χ⁻¹.Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one]
  by_cases he : χ.Even
  · simpa only [DirichletCharacter.gammaFactor, ite_eq_left he, ite_eq_left (hi.mpr he), ofReal_zero, zero_add]
      using haux 0 (by norm_num) (by norm_num)
  · have hin : ¬χ⁻¹.Even := fun h => he (hi.mp h)
    simp only [DirichletCharacter.gammaFactor, ite_eq_right he, ite_eq_right hin]
    rw [show (1 - s) + 1 = (1 : ℂ) + 1 - s by ring,
      show s + 1 = (1 : ℂ) + s by ring]
    exact haux 1 (by norm_num) (by norm_num)

/-- LEAF. P0069 page 22, Lemma 8, Rademacher reference 28.
Rademacher page 197, Lemma 1, display 5.1. This is the printed ordinary
Gamma quotient estimate with its exact constant. It covers both character
parities through Q equal to zero or one. OPEN. -/
theorem leaf_rademacher_gamma_ratio :
    ∀ Q : ℝ, 0 ≤ Q → ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 1 / 2 →
      ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
        Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤
        (‖(Q : ℂ) + 1 + s‖ / 2) ^ (1 / 2 - s.re) := by
  sorry

/-- Rademacher pages 197 to 199, the conductor-uniform Gamma input has constant one.
CONDITIONAL ON the exact printed ordinary Gamma ratio leaf. -/
theorem gamma_quotient_uniform {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ G : ℝ, 0 < G ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℂ), s.re = -δ →
      ‖χ⁻¹.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤
        G * (|s.im| + 2) ^ (1 / 2 + δ) := by
  refine ⟨1, by norm_num, ?_⟩
  intro q _ χ s hs
  simpa only [one_mul] using
    gamma_quotient_normalization hδ hδhalf leaf_rademacher_gamma_ratio χ s hs

/-- Rademacher page 197, Lemma 1, the right boundary equality follows from conjugation. -/
theorem gamma_ratio_right_edge {Q : ℝ} (hQ : 0 ≤ Q) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
      Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ = 1 := by
  let w : ℂ := (Q : ℂ) / 2 + s / 2
  have hw : 0 < w.re := by simp [w, hs]; linarith
  have he : (Q : ℂ) / 2 + (1 - s) / 2 = (starRingEnd ℂ) w := by
    apply Complex.ext <;> simp [w, Complex.div_re, Complex.div_im, hs] <;> ring
  rw [he, Complex.Gamma_conj, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hw))

/-- Rademacher page 197 display 5.2, the left boundary follows from Gamma recurrence. -/
theorem gamma_ratio_left_edge {Q : ℝ} (hQ : 0 ≤ Q) {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) /
      Complex.Gamma ((Q : ℂ) / 2 + s / 2)‖ ≤ ‖(Q : ℂ) + 1 + s‖ / 2 := by
  let w : ℂ := (Q : ℂ) / 2 + s / 2
  by_cases hG : Complex.Gamma w = 0
  · change ‖_ / Complex.Gamma w‖ ≤ _
    rw [hG, div_zero, norm_zero]
    positivity
  have hw : w ≠ 0 := by intro h; apply hG; rw [h, Complex.Gamma_zero]
  have he : (Q : ℂ) / 2 + (1 - s) / 2 = (starRingEnd ℂ) (w + 1) := by
    apply Complex.ext <;> simp [w, Complex.div_re, Complex.div_im, hs] <;> ring
  have hn : ‖Complex.Gamma ((Q : ℂ) / 2 + (1 - s) / 2) / Complex.Gamma w‖ = ‖w‖ := by
    rw [he, Complex.Gamma_conj, Complex.norm_div, Complex.norm_conj,
      Complex.Gamma_add_one w hw, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hG)]
  change ‖_ / Complex.Gamma w‖ ≤ _
  rw [hn]
  have hw2 : ‖w‖ ^ 2 = (Q / 2 - 1 / 4) ^ 2 + (s.im / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [w, hs]
    ring
  have hv2 : (‖(Q : ℂ) + 1 + s‖ / 2) ^ 2 = (Q / 2 + 1 / 4) ^ 2 + (s.im / 2) ^ 2 := by
    rw [div_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hs]
    ring
  nlinarith [norm_nonneg w, norm_nonneg ((Q : ℂ) + 1 + s)]

open Asymptotics

/-- Rademacher page 195 display 3.1, the strip maximum principle under finite-order growth.
CONDITIONAL ON the explicit growth and constant boundary premises. -/
theorem finite_order_strip_maximum {l u M C c t₀ : ℝ} (hlu : l < u) (hC : 0 < C) (hc : 0 < c)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : ∀ z : ℂ, l ≤ z.re → z.re ≤ u → ‖f z‖ ≤ C * Real.exp (|z.im + t₀| ^ c))
    (ha : ∀ z : ℂ, z.re = l → ‖f z‖ ≤ M)
    (hb : ∀ z : ℂ, z.re = u → ‖f z‖ ≤ M)
    {z : ℂ} (hzl : l ≤ z.re) (hzu : z.re ≤ u) : ‖f z‖ ≤ M := by
  let η : ℝ := (Real.pi / (u - l)) / 2
  have hd : 0 < u - l := sub_pos.mpr hlu
  have hη : 0 < η := by dsimp [η]; positivity
  have hηlt : η < Real.pi / (u - l) := by
    dsimp [η]
    have hh := div_pos Real.pi_pos hd
    linarith
  have htwo : 0 < (2 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) _
  have he : ∀ᶠ x : ℝ in atTop, (2 * x) ^ c ≤ Real.exp (η * x) := by
    have hh := (isLittleO_rpow_exp_pos_mul_atTop c hη).bound (one_div_pos.mpr htwo)
    filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs, Real.abs_exp, abs_of_nonneg (Real.rpow_nonneg hx0 c)] at hx
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0]
    calc
      _ ≤ (2 : ℝ) ^ c * (1 / (2 : ℝ) ^ c * Real.exp (η * x)) := mul_le_mul_of_nonneg_left hx htwo.le
      _ = _ := by field_simp
  have hbound : ∃ d < Real.pi / (u - l), ∃ B : ℝ,
      f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo l u)]
        fun z => Real.exp (B * Real.exp (d * |z.im|)) := by
    refine ⟨η, hηlt, 1, Asymptotics.IsBigO.of_bound C ?_⟩
    have he' : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop,
        (2 * |z.im|) ^ c ≤ Real.exp (η * |z.im|) := tendsto_comap.eventually he
    have ht' : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop,
        |t₀| ≤ |z.im| := tendsto_comap.eventually (eventually_ge_atTop |t₀|)
    have hs' : ∀ᶠ z : ℂ in 𝓟 (Complex.re ⁻¹' Ioo l u), z.re ∈ Ioo l u :=
      Filter.eventually_principal.mpr (by intro z hz; exact hz)
    filter_upwards [he'.filter_mono inf_le_left, ht'.filter_mono inf_le_left,
      hs'.filter_mono inf_le_right] with w hw ht hs
    simp only [Real.norm_eq_abs, Real.abs_exp, one_mul]
    have hp : |w.im + t₀| ^ c ≤ Real.exp (η * |w.im|) := by
      refine (Real.rpow_le_rpow (abs_nonneg _) ?_ hc.le).trans hw
      have hh := abs_add_le w.im t₀
      linarith
    exact (hg w hs.1.le hs.2.le).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) hC.le)
  exact PhragmenLindelof.vertical_strip hf.diffContOnCl hbound ha hb hzl hzu

/-- Rademacher page 195 display 3.4, three-lines interpolation under finite-order growth.
CONDITIONAL ON the explicit growth and boundary premises. -/
theorem finite_order_three_lines {l u a b C c t₀ : ℝ} (hlu : l < u)
    (ha0 : 0 < a) (hb0 : 0 < b) (hC : 0 < C) (hc : 0 < c)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : ∀ z : ℂ, l ≤ z.re → z.re ≤ u → ‖f z‖ ≤ C * Real.exp (|z.im + t₀| ^ c))
    (ha : ∀ z : ℂ, z.re = l → ‖f z‖ ≤ a)
    (hb : ∀ z : ℂ, z.re = u → ‖f z‖ ≤ b)
    {z : ℂ} (hzl : l ≤ z.re) (hzu : z.re ≤ u) :
    ‖f z‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) := by
  let α : ℝ := Real.log a / (u - l)
  let β : ℝ := Real.log b / (u - l)
  let E : ℂ → ℝ := fun w => (w.re - u) * α + (l - w.re) * β
  let F : ℂ → ℂ := fun w => f w * Complex.exp ((w - u) * α + (l - w) * β)
  have hd : 0 < u - l := sub_pos.mpr hlu
  have hn (w : ℂ) : ‖F w‖ = ‖f w‖ * Real.exp (E w) := by
    dsimp [F, E]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hE (w : ℂ) (hwl : l ≤ w.re) (hwu : w.re ≤ u) :
      E w ≤ (u - l) * (|α| + |β|) := by
    have h1 : (w.re - u) * α ≤ (u - l) * |α| := by
      calc
        _ ≤ |(w.re - u) * α| := le_abs_self _
        _ = |w.re - u| * |α| := abs_mul _ _
        _ ≤ (u - l) * |α| := by rw [abs_of_nonpos (by linarith)]; gcongr; linarith
    have h2 : (l - w.re) * β ≤ (u - l) * |β| := by
      calc
        _ ≤ |(l - w.re) * β| := le_abs_self _
        _ = |l - w.re| * |β| := abs_mul _ _
        _ ≤ (u - l) * |β| := by rw [abs_of_nonpos (by linarith)]; gcongr; linarith
    dsimp [E]
    nlinarith
  have hFd : Differentiable ℂ F := by dsimp [F]; exact hf.mul (by fun_prop)
  have hFg (w : ℂ) (hwl : l ≤ w.re) (hwu : w.re ≤ u) :
      ‖F w‖ ≤ (C * Real.exp ((u - l) * (|α| + |β|))) * Real.exp (|w.im + t₀| ^ c) := by
    rw [hn]
    calc
      _ ≤ (C * Real.exp (|w.im + t₀| ^ c)) * Real.exp ((u - l) * (|α| + |β|)) :=
        mul_le_mul (hg w hwl hwu) (Real.exp_le_exp.mpr (hE w hwl hwu)) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hFa (w : ℂ) (hw : w.re = l) : ‖F w‖ ≤ 1 := by
    have hEval : E w = -Real.log a := by
      dsimp [E, α, β]
      rw [hw]
      field_simp [ne_of_gt hd]
      ring
    rw [hn, hEval]
    calc
      _ ≤ a * Real.exp (-Real.log a) := mul_le_mul_of_nonneg_right (ha w hw) (Real.exp_pos _).le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log ha0]; field_simp
  have hFb (w : ℂ) (hw : w.re = u) : ‖F w‖ ≤ 1 := by
    have hEval : E w = -Real.log b := by
      dsimp [E, α, β]
      rw [hw]
      field_simp [ne_of_gt hd]
      ring
    rw [hn, hEval]
    calc
      _ ≤ b * Real.exp (-Real.log b) := mul_le_mul_of_nonneg_right (hb w hw) (Real.exp_pos _).le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log hb0]; field_simp
  have hF := finite_order_strip_maximum hlu (by positivity : 0 < C * Real.exp ((u - l) * (|α| + |β|)))
    hc F hFd hFg hFa hFb hzl hzu
  rw [hn] at hF
  have hp : Real.exp (-(E z)) = a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) := by
    rw [Real.rpow_def_of_pos ha0, Real.rpow_def_of_pos hb0, ← Real.exp_add]
    congr 1
    dsimp [E, α, β]
    field_simp [ne_of_gt hd]
    ring
  calc
    ‖f z‖ ≤ 1 / Real.exp (E z) := (le_div_iff₀ (Real.exp_pos _)).mpr hF
    _ = _ := by rw [one_div, ← Real.exp_neg, hp]


/-- Rademacher page 195 display 3.4, weighted interpolation on the whole closed strip.
CONDITIONAL ON the exact finite-order growth and boundary premises. -/
theorem weighted_strip_interpolation_finite_order {δ : ℝ} (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q A : ℝ, 1 ≤ Q → 0 < A →
      ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s : ℂ,
        -δ ≤ s.re → s.re ≤ 1 + δ → ‖f s‖ ≤ C * Real.exp (|s.im| ^ c)) →
      (∀ t : ℝ, ‖f (((-δ : ℝ) : ℂ) + t * I)‖ ≤
        A * (Q * (|t| + 2)) ^ (1 / 2 + δ)) →
      (∀ t : ℝ, ‖f (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ A) →
      ∀ σ t : ℝ, -δ ≤ σ → σ ≤ 1 + δ →
        ‖f ((σ : ℂ) + t * I)‖ ≤
          K * A * (Q * (|t| + 1)) ^ ((1 + δ - σ) / 2) := by
  refine ⟨3 * Real.exp 4, by positivity, ?_⟩
  intro Q A hQ hA f hf hg hleft hright σ t hσ0 hσ1
  obtain ⟨C, c, hC, hc, hg⟩ := hg
  let K : ℝ := 3 * Real.exp 4
  let P : ℝ := Q * (|t| + 1)
  let a : ℝ := 1 / 2 + δ
  let g : ℂ → ℂ := fun z => f (z + t * I) * Complex.exp ((z - σ) ^ 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have h4 (z : ℂ) (hz : -δ ≤ z.re ∧ z.re ≤ 1 + δ) : (z.re - σ) ^ 2 ≤ 4 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 2 - (z.re - σ))
      (by linarith : 0 ≤ 2 + (z.re - σ))
    nlinarith
  have hdamp (z : ℂ) (hz : -δ ≤ z.re ∧ z.re ≤ 1 + δ) :
      (|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) ≤ K := by
    calc
      _ ≤ (|z.im| + 2) * Real.exp (4 - z.im ^ 2) := by
        gcongr
        exact h4 z hz
      _ = Real.exp 4 * ((|z.im| + 2) * Real.exp (-(z.im ^ 2))) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ Real.exp 4 * 3 := mul_le_mul_of_nonneg_left (gaussian_linear_decay z.im) (Real.exp_pos _).le
      _ = K := by dsimp [K]; ring
  have hgl (z : ℂ) (hz : z.re = -δ) : ‖g z‖ ≤ K * A * P ^ a := by
    have he : z + t * I = (((-δ : ℝ) : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [hz]
    have hl := hleft (z.im + t)
    have hheight : |z.im + t| + 2 ≤ (|t| + 1) * (|z.im| + 2) := by
      have hh := abs_add_le z.im t
      nlinarith [abs_nonneg z.im, abs_nonneg t]
    have hp : (Q * (|z.im + t| + 2)) ^ a ≤ P ^ a * (|z.im| + 2) := by
      calc
        _ ≤ (P * (|z.im| + 2)) ^ a := by
          apply Real.rpow_le_rpow (by positivity) _ ha
          dsimp [P]
          nlinarith
        _ = P ^ a * (|z.im| + 2) ^ a := Real.mul_rpow hP.le (by positivity)
        _ ≤ P ^ a * (|z.im| + 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg z.im]) ha1)
            (Real.rpow_nonneg hP.le _)
    have hn : ‖f (z + t * I)‖ ≤ (A * P ^ a) * (|z.im| + 2) := by
      rw [he]
      calc
        _ ≤ A * (P ^ a * (|z.im| + 2)) := hl.trans (mul_le_mul_of_nonneg_left hp hA.le)
        _ = _ := by ring
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ ((A * P ^ a) * (|z.im| + 2)) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = (A * P ^ a) * ((|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2)) := by ring
      _ ≤ (A * P ^ a) * K := mul_le_mul_of_nonneg_left
        (hdamp z (by constructor <;> rw [hz] <;> linarith)) (by positivity)
      _ = _ := by ring
  have hgr (z : ℂ) (hz : z.re = 1 + δ) : ‖g z‖ ≤ K * A := by
    have he : z + t * I = (((1 + δ : ℝ) : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [hz]
    have hr : ‖f (z + t * I)‖ ≤ A := by rw [he]; exact hright (z.im + t)
    have hr4 := h4 z (by constructor <;> rw [hz] <;> linarith)
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ A * Real.exp 4 := mul_le_mul hr (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.im]))
        (Real.exp_pos _).le hA.le
      _ ≤ K * A := by dsimp [K]; nlinarith [Real.exp_pos 4]
  have hgd : Differentiable ℂ g := by
    dsimp [g]
    exact (hf.comp (by fun_prop)).mul (by fun_prop)
  have hgg (z : ℂ) (hzl : -δ ≤ z.re) (hzu : z.re ≤ 1 + δ) :
      ‖g z‖ ≤ (C * Real.exp 4) * Real.exp (|z.im + t| ^ c) := by
    have hh := hg (z + t * I) (by simpa using hzl) (by simpa using hzu)
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at hh
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ (C * Real.exp (|z.im + t| ^ c)) * Real.exp 4 :=
        mul_le_mul hh (Real.exp_le_exp.mpr (by nlinarith [h4 z ⟨hzl, hzu⟩, sq_nonneg z.im]))
          (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hi := finite_order_three_lines (l := -δ) (u := 1 + δ) (a := K * A * P ^ a)
    (b := K * A) (C := C * Real.exp 4) (c := c) (t₀ := t)
    (by linarith) (by positivity) (by positivity) (by positivity) hc g hgd hgg hgl hgr
    (z := (σ : ℂ)) (by simpa using hσ0) (by simpa using hσ1)
  simp only [g, sub_self, zero_pow (by norm_num : 2 ≠ 0), Complex.exp_zero, mul_one,
    ofReal_re, sub_neg_eq_add] at hi
  let w : ℝ := (σ + δ) / (1 + 2 * δ)
  have hden : 1 + δ + δ = 1 + 2 * δ := by ring
  rw [hden] at hi
  change ‖f ((σ : ℂ) + t * I)‖ ≤ (K * A * P ^ a) ^ (1 - w) * (K * A) ^ w at hi
  have hex : a * (1 - w) = (1 + δ - σ) / 2 := by
    dsimp [a, w]
    field_simp [show 1 + 2 * δ ≠ 0 by linarith]
    ring
  have hKA : 0 < K * A := mul_pos hK hA
  have halg : (K * A * P ^ a) ^ (1 - w) * (K * A) ^ w =
      K * A * P ^ ((1 + δ - σ) / 2) := by
    rw [Real.mul_rpow hKA.le (Real.rpow_nonneg hP.le a), ← Real.rpow_mul hP.le, hex]
    calc
      _ = ((K * A) ^ (1 - w) * (K * A) ^ w) * P ^ ((1 + δ - σ) / 2) := by ring
      _ = _ := by rw [← Real.rpow_add hKA, sub_add_cancel, Real.rpow_one]
  exact hi.trans_eq halg


/-- LEAF. P0069 page 22, Lemma 8, Rademacher reference 28.
Rademacher page 195 display 3.1 is finite-order growth, used for the
L-functions in Section 6 on pages 198 and 199. The principal pole is
subtracted. The two growth constants can depend on the character. OPEN. -/
theorem leaf_regularPart_finite_order_growth {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ →
      ‖regularPart χ s‖ ≤ C * Real.exp (|s.im| ^ c) := by
  sorry

/-- P0069 page 22 and Rademacher page 195 display 3.1.
The stronger linear-exponential growth statement follows from the printed
finite-order premise and the proved edge bounds. CONDITIONAL ON the exact
finite-order growth input and the ordinary Gamma quotient leaf. -/
theorem leaf_regularPart_growth {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ →
      ‖regularPart χ s‖ ≤ C * Real.exp (B * |s.im|) := by
  have hfinite := leaf_regularPart_finite_order_growth hδ hδhalf χ
  obtain ⟨G, hG, hgamma⟩ := gamma_quotient_uniform hδ hδhalf
  obtain ⟨K, hK, hinterp⟩ := weighted_strip_interpolation_finite_order hδ hδhalf
  let B : ℝ := 4 * G * (1 + 1 / δ)
  let A : ℝ := B + 2 + 2 / δ
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hleft (u : ℝ) : ‖regularPart χ (((-δ : ℝ) : ℂ) + u * I)‖ ≤
      A * ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) := by
    let s : ℂ := ((-δ : ℝ) : ℂ) + u * I
    have hsre : s.re = -δ := by simp [s]
    have hs : s ≠ 1 := by intro he; have := congrArg Complex.re he; simp only [hsre, one_re] at this; linarith
    have hd : 1 ≤ ‖s - 1‖ := by
      have hh := Complex.abs_re_le_norm (s - 1)
      simp only [sub_re, one_re, hsre, abs_of_nonpos (by linarith : -δ - 1 ≤ 0)] at hh
      linarith
    have hp : 1 / ‖s - 1‖ ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
    have hbase : 1 ≤ (q : ℝ) * (|u| + 2) := by nlinarith [abs_nonneg u]
    have hpow : 1 ≤ ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) :=
      Real.one_le_rpow hbase (by linarith)
    have hl := all_character_left_bound hδ hG.le hgamma χ u
    have hr := (pole_norm_bounds χ hs).1
    change ‖regularPart χ s‖ ≤ _
    change ‖χ.LFunction s‖ ≤ B * ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) at hl
    have hBA : B + 1 ≤ A := by
      have hd0 : 0 < 2 / δ := by positivity
      dsimp [A]
      linarith
    have hmul := mul_le_mul_of_nonneg_right hBA
      (Real.rpow_nonneg (by positivity : 0 ≤ (q : ℝ) * (|u| + 2)) (1 / 2 + δ))
    nlinarith
  have hright (u : ℝ) : ‖regularPart χ (((1 + δ : ℝ) : ℂ) + u * I)‖ ≤ A := by
    refine (regularPart_right_bound hδ χ u).trans ?_
    dsimp [A]
    linarith
  let C : ℝ := K * A * q
  refine ⟨C, 1, by dsimp [C]; positivity, by norm_num, ?_⟩
  intro s hsl hsu
  have hi := hinterp (q : ℝ) A hqR hA (regularPart χ) (regularPart_entire χ)
    hfinite hleft hright s.re s.im hsl hsu
  rw [Complex.re_add_im] at hi
  have hbase : 1 ≤ (q : ℝ) * (|s.im| + 1) := by nlinarith [abs_nonneg s.im]
  have hpow : ((q : ℝ) * (|s.im| + 1)) ^ ((1 + δ - s.re) / 2) ≤
      (q : ℝ) * (|s.im| + 1) := by
    exact Real.rpow_le_self_of_one_le hbase (by linarith)
  calc
    ‖regularPart χ s‖ ≤ (K * A) * ((q : ℝ) * (|s.im| + 1)) :=
      hi.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = C * (|s.im| + 1) := by dsimp [C]; ring
    _ ≤ C * Real.exp |s.im| := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by dsimp [C]; positivity)
    _ = C * Real.exp (1 * |s.im|) := by rw [one_mul]

/-- P0069 page 22, Lemma 8, the stronger auxiliary convexity input.
CONDITIONAL ON the ordinary Gamma quotient and regular-part growth leaves. -/
theorem convexity_from_edges :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
        (σ : ℂ) + t * Complex.I ≠ 1 →
        ‖χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤
          C * (((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε) +
            1 / ‖(σ : ℂ) + t * Complex.I - 1‖) := by
  intro ε hε
  let δ : ℝ := min ε (1 / 4)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδhalf : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  obtain ⟨G, hG, hgamma⟩ := gamma_quotient_uniform hδ hδhalf
  obtain ⟨K, hK, hinterp⟩ := weighted_strip_interpolation hδ hδhalf
  let B : ℝ := 4 * G * (1 + 1 / δ)
  let A : ℝ := B + 2 + 2 / δ
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let D : ℝ := K * A
  have hD : 0 < D := mul_pos hK hA
  refine ⟨D + 1, by positivity, ?_⟩
  intro q _ hq χ σ t hσ0 hσ1 hne
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hleft (u : ℝ) : ‖regularPart χ (((-δ : ℝ) : ℂ) + u * I)‖ ≤
      A * ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) := by
    let s : ℂ := ((-δ : ℝ) : ℂ) + u * I
    have hsre : s.re = -δ := by simp [s]
    have hs : s ≠ 1 := by intro he; have := congrArg Complex.re he; simp only [hsre, one_re] at this; linarith
    have hd : 1 ≤ ‖s - 1‖ := by
      have hh := Complex.abs_re_le_norm (s - 1)
      simp only [sub_re, one_re, hsre, abs_of_nonpos (by linarith : -δ - 1 ≤ 0)] at hh
      linarith
    have hp : 1 / ‖s - 1‖ ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
    have hbase : 1 ≤ (q : ℝ) * (|u| + 2) := by nlinarith [abs_nonneg u]
    have hpow : 1 ≤ ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) :=
      Real.one_le_rpow hbase (by linarith)
    have hl := all_character_left_bound hδ hG.le hgamma χ u
    have hr := (pole_norm_bounds χ hs).1
    change ‖regularPart χ s‖ ≤ _
    change ‖χ.LFunction s‖ ≤ B * ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) at hl
    have hBA : B + 1 ≤ A := by
      have hd0 : 0 < 2 / δ := by positivity
      dsimp [A]
      linarith
    have hmul := mul_le_mul_of_nonneg_right hBA
      (Real.rpow_nonneg (by positivity : 0 ≤ (q : ℝ) * (|u| + 2)) (1 / 2 + δ))
    nlinarith
  have hright (u : ℝ) : ‖regularPart χ (((1 + δ : ℝ) : ℂ) + u * I)‖ ≤ A := by
    refine (regularPart_right_bound hδ χ u).trans ?_
    dsimp [A]
    linarith
  have hi := hinterp (q : ℝ) A hqR hA (regularPart χ) (regularPart_entire χ)
    (leaf_regularPart_growth hδ hδhalf χ) hleft hright σ t hσ0 hσ1
  have hbase : 1 ≤ (q : ℝ) * (|t| + 1) := by nlinarith [abs_nonneg t]
  have hpow : ((q : ℝ) * (|t| + 1)) ^ ((1 + δ - σ) / 2) ≤
      ((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hreg : ‖regularPart χ ((σ : ℂ) + t * I)‖ ≤
      D * ((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε) :=
    hi.trans (mul_le_mul_of_nonneg_left hpow hD.le)
  have hL := (pole_norm_bounds χ hne).2
  have hp0 : 0 ≤ 1 / ‖(σ : ℂ) + t * I - 1‖ := by positivity
  have hpow0 : 0 ≤ ((q : ℝ) * (|t| + 1)) ^ ((1 - σ) / 2 + ε) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith [mul_nonneg hD.le hp0]


end LeanLab.BHP1997.Decomp530a
