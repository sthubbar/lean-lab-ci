/-
AI wrote this Lean code. Codex task575, 2026-11-15.
A supply split for Proposition 1.4 on pp. 339 to 341.
The original target remains open. Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Decomp575a
import LeanLab.Zinoviev1997.Decomp575c

namespace LeanLab.Zinoviev1997.Decomp575b
open MeasureTheory ArithmeticFunction
open LeanLab.Zinoviev1997.State1546

/-- The progression Mangoldt sum in display 1.10 on p. 340. -/
noncomputable def psiMod (x : ℝ) (q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊,
    if n % q = l % q then ArithmeticFunction.vonMangoldt n else 0

/-- The weighted progression sum before display 1.10 on p. 340. -/
noncomputable def weightedMod (x : ℝ) (q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊,
    if n % q = l % q then ArithmeticFunction.vonMangoldt n / Real.log n else 0

/-- Abel summation in display 1.10 on p. 340 before the prime power correction. -/
theorem weightedMod_abel {x : ℝ} (hx : 2 ≤ x) (q l : ℕ) :
    weightedMod x q l = psiMod x q l / Real.log x +
      ∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2) := by
  let c : ℕ → ℝ := fun n => if n % q = l % q then ArithmeticFunction.vonMangoldt n else 0
  have hlog : ∀ u ∈ Set.Icc (2 : ℝ) x, Real.log u ≠ 0 := by
    intro u hu
    exact ne_of_gt (Real.log_pos (by linarith [hu.1]))
  have hu0 : ∀ u ∈ Set.Icc (2 : ℝ) x, u ≠ 0 := by
    intro u hu
    linarith [hu.1]
  have hd : ∀ u ∈ Set.Icc (2 : ℝ) x,
      HasDerivAt (fun u : ℝ => 1 / Real.log u) (-(1 / (u * Real.log u ^ 2))) u := by
    intro u hu
    convert (hasDerivAt_const u (1 : ℝ)).div (Real.hasDerivAt_log (hu0 u hu)) (hlog u hu) using 1
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have hc : ContinuousOn (fun u : ℝ => -(1 / (u * Real.log u ^ 2))) (Set.Icc 2 x) := by
    apply ContinuousOn.neg
    apply continuousOn_const.div
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono (by
        intro u hu
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu0 u hu)).pow 2)
    · intro u hu
      exact mul_ne_zero (hu0 u hu) (pow_ne_zero 2 (hlog u hu))
  have hab := sum_mul_eq_sub_integral_mul₁ c
    (by simp [c]) (by simp [c]) x
    (fun u hu => (hd u hu).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun u hu => (hd u hu).deriv.symm) measurableSet_Icc)
  have hsum : ∀ y : ℝ, (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, c k) = psiMod y q l := by
    intro y
    rfl
  rw [hsum] at hab
  have he : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (1 / Real.log (k : ℝ)) * c k) = weightedMod x q l := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [c]
    split_ifs <;> ring
  rw [he] at hab
  rw [intervalIntegral.integral_of_le hx]
  have hint : (∫ u in Set.Ioc (2 : ℝ) x,
      deriv (fun u : ℝ => 1 / Real.log u) u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k) =
      -(∫ u in Set.Ioc (2 : ℝ) x, psiMod u q l / (u * Real.log u ^ 2)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [(hd u ⟨hu.1.le, hu.2⟩).deriv, hsum]
    ring
  rw [hint] at hab
  simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm, one_mul] using hab

/-- The modulus one reduction in the last paragraph on p. 341. -/
theorem piMod_one (x : ℝ) (l : ℕ) : piMod x 1 l = piMod x 1 0 := by
  simp [piMod, Nat.mod_one]
/-- The modulus two reduction on p. 341 retains the missing prime two. -/
theorem piMod_two {x : ℝ} (hx : 2 ≤ x) {l : ℕ} (hl : Nat.Coprime l 2) :
    piMod x 2 l + 1 = piMod x 1 0 := by
  have hl2 : l % 2 = 1 := by
    exact Nat.odd_iff.mp (Nat.coprime_two_right.mp hl)
  have hset : (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 1 = 0 % 1) =
      insert 2 ((Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 2 = l % 2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mod_one, and_true,
      Finset.mem_insert, hl2]
    constructor
    · rintro ⟨hp, hprime⟩
      rcases hprime.eq_two_or_odd with rfl | ho
      · exact Or.inl rfl
      · exact Or.inr ⟨hp, hprime, ho⟩
    · rintro (rfl | ⟨hp, hprime, ho⟩)
      · exact ⟨Nat.le_floor hx, Nat.prime_two⟩
      · exact ⟨hp, hprime⟩
  unfold piMod
  rw [hset, Finset.card_insert_of_notMem]
  simp [hl2]

/-- Integrability of the smooth logarithmic kernels used on pp. 340 to 341. -/
theorem logarithmic_kernels {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun u : ℝ => 1 / Real.log u ^ 2) volume 2 x ∧
    IntervalIntegrable (fun u : ℝ => 1 / (u * Real.log u ^ 2)) volume 2 x := by
  have hu : ∀ u ∈ Set.uIcc (2 : ℝ) x, u ≠ 0 ∧ Real.log u ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le hx] at hu
    exact ⟨by linarith [hu.1], (Real.log_pos (by linarith [hu.1])).ne'⟩
  have hlog : ContinuousOn Real.log (Set.uIcc (2 : ℝ) x) :=
    Real.continuousOn_log.mono (by
      intro u h
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (hu u h).1)
  constructor
  · exact (continuousOn_const.div (hlog.pow 2)
      (fun u h => pow_ne_zero 2 (hu u h).2)).intervalIntegrable
  · exact (continuousOn_const.div (continuousOn_id.mul (hlog.pow 2))
      (fun u h => mul_ne_zero (hu u h).1 (pow_ne_zero 2 (hu u h).2))).intervalIntegrable

/-- The progression kernel in Abel summation on p. 340 is integrable. -/
theorem psiMod_kernel_integrable {x : ℝ} (hx : 2 ≤ x) (q l : ℕ) :
    IntervalIntegrable (fun u : ℝ => psiMod u q l / (u * Real.log u ^ 2)) volume 2 x := by
  let c : ℕ → ℝ := fun n => if n % q = l % q then ArithmeticFunction.vonMangoldt n else 0
  have hg := (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp
    (logarithmic_kernels hx).2
  have hi := integrableOn_mul_sum_Icc c (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hg
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  convert hi using 1
  ext u
  change psiMod u q l / (u * Real.log u ^ 2) =
    1 / (u * Real.log u ^ 2) * psiMod u q l
  ring

/-- Subtract the Li main term using the existing zinLi_by_parts on p. 341. -/
theorem centered_abel {x : ℝ} (hx : 2 ≤ x) {q : ℕ} (hq : 1 ≤ q) (l : ℕ) :
    weightedMod x q l - zinLi x / (Nat.totient q : ℝ) =
      (psiMod x q l - x / (Nat.totient q : ℝ)) / Real.log x +
      (∫ u in (2 : ℝ)..x,
        (psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2)) +
      2 / ((Nat.totient q : ℝ) * Real.log 2) := by
  have hp : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
  have hlog : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hi : (∫ u in (2 : ℝ)..x,
      (psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2)) =
      (∫ u in (2 : ℝ)..x, psiMod u q l / (u * Real.log u ^ 2)) -
      (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) / (Nat.totient q : ℝ) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      (psiMod_kernel_integrable hx q l) ((logarithmic_kernels hx).1.div_const _)]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [Set.uIcc_of_le hx] at hu
      linarith [hu.1]
    field_simp
  rw [hi, weightedMod_abel hx, zinLi_by_parts hx]
  field_simp
  ring

/-- The absolute integral form needed in the last remainder display on p. 341. -/
theorem centered_integral_abs {x : ℝ} (hx : 2 ≤ x) (q l : ℕ) :
    |∫ u in (2 : ℝ)..x,
      (psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2)| ≤
      ∫ u in (2 : ℝ)..x,
      |psiMod u q l - u / (Nat.totient q : ℝ)| / (u * Real.log u ^ 2) := by
  calc
    _ ≤ ∫ u in (2 : ℝ)..x,
        |(psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2)| :=
      intervalIntegral.abs_integral_le_integral_abs hx
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := by
        rw [Set.uIcc_of_le hx] at hu
        linarith [hu.1]
      dsimp only
      rw [abs_div, abs_of_nonneg (mul_nonneg hu0 (sq_nonneg _))]

/-- Finite character orthogonality for the progression sum on p. 340. -/
theorem progression_orthogonality {q l : ℕ} [NeZero q] (hl : Nat.Coprime l q) (x : ℝ) :
    (Nat.totient q : ℂ) * (psiMod x q l : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((l : ZMod q)⁻¹) * psiChi χ x := by
  have hlunit : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  simp only [psiChi, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [psiMod, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hlunit]
  by_cases h : n % q = l % q
  · have hz : (l : ZMod q) = (n : ZMod q) := (ZMod.natCast_eq_natCast_iff' l n q).mpr h.symm
    simp [h, hz]
  · have hz : (l : ZMod q) ≠ (n : ZMod q) := by
      intro hz
      exact h ((ZMod.natCast_eq_natCast_iff' l n q).mp hz).symm
    simp [h, hz]

/-- Uniform character errors imply the progression error by the p. 340 average.
The character bounds are explicit hypotheses and are not discharged here. -/
theorem character_average_bound {q l : ℕ} [NeZero q] (hl : Nat.Coprime l q)
    (x B : ℝ)
    (hB : ∀ χ : DirichletCharacter ℂ q,
      ‖psiChi χ x - if χ = 1 then (x : ℂ) else 0‖ ≤ B) :
    |psiMod x q l - x / (Nat.totient q : ℝ)| ≤ B := by
  have hp : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hlunit : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  have hlinv : IsUnit ((l : ZMod q)⁻¹) := by
    rcases hlunit with ⟨u, hu⟩
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      χ ((l : ZMod q)⁻¹) * (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
    simp [MulChar.one_apply (hlinv)]
  have he : (Nat.totient q : ℂ) * (psiMod x q l : ℂ) - (x : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((l : ZMod q)⁻¹) *
        (psiChi χ x - if χ = 1 then (x : ℂ) else 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hmain, progression_orthogonality hl x]
  have hnorm : ‖(Nat.totient q : ℂ) * (psiMod x q l : ℂ) - (x : ℂ)‖ ≤
      (Nat.totient q : ℝ) * B := by
    rw [he]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ ((l : ZMod q)⁻¹) *
          (psiChi χ x - if χ = 1 then (x : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ q, B := by
        apply Finset.sum_le_sum
        intro χ hχ
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans (by simpa using hB χ)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have he' : (Nat.totient q : ℂ) * (psiMod x q l : ℂ) - (x : ℂ) =
      ((Nat.totient q : ℝ) * (psiMod x q l - x / (Nat.totient q : ℝ)) : ℝ) := by
    have hpC : (Nat.totient q : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    push_cast
    field_simp [hpC]
  rw [he', Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hp] at hnorm
  exact (mul_le_mul_iff_right₀ hp).mp hnorm

/-- Proposition 1.4, p. 341, second display.
CONDITIONAL ON the Schoenfeld psi supply in Decomp575c and lemma13.
This is only the endpoint progression psi estimate. Its proof uses the unchanged
Lemma 1.3 and its explicit budget, character orthogonality on p. 340,
induction from primitive characters and the Schoenfeld psi estimate quoted on p. 341.
No assertion about the interior modulus range is hidden in this endpoint leaf. -/
theorem progression_endpoint (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 3 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |psiMod x q l - x / (Nat.totient q : ℝ)| ≤
      0.85 * Real.sqrt x * Real.log x ^ 2 := by
  have : NeZero q := ⟨by omega⟩
  exact character_average_bound hl x _
    (fun χ => LeanLab.Zinoviev1997.Decomp575c.character_error hG χ hx hqx)

/-- LEAF. Proposition 1.4, p. 341, the last remainder display.
Supporting absolute integral form with the lower endpoint term reserved explicitly.
The endpoint condition q at most x to the power 0.37 is not a uniform condition
on the integration variable. A proof must split the interval or establish a
uniform explicit formula before applying the estimate inside this integral. -/
theorem integrated_progression_error (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 3 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    (∫ u in (2 : ℝ)..x,
      |psiMod u q l - u / (Nat.totient q : ℝ)| / (u * Real.log u ^ 2)) ≤
      0.1 * Real.sqrt x * Real.log x + 10 ^ 8 -
        2 / ((Nat.totient q : ℝ) * Real.log 2) := by
  sorry

/-- Each normalized Mangoldt weight lies between zero and one, supporting p. 340. -/
theorem mangoldt_log_ratio (n : ℕ) :
    0 ≤ vonMangoldt n / Real.log n ∧ vonMangoldt n / Real.log n ≤ 1 := by
  constructor
  · exact div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)
  · rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
    · simp
    · simp
    · exact (div_le_one (Real.log_pos (by exact_mod_cast hn))).mpr vonMangoldt_le_log

/-- Only nonprime terms remain in the weighted count correction on p. 340. -/
theorem correction_eq (x : ℝ) (q l : ℕ) :
    weightedMod x q l - (piMod x q l : ℝ) =
      ∑ n ∈ Finset.Iic ⌊x⌋₊,
        if ¬n.Prime ∧ n % q = l % q then vonMangoldt n / Real.log n else 0 := by
  unfold weightedMod piMod
  rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp [hp, vonMangoldt_apply_prime hp, hlog]
  · simp [hp]

/-- The prime power correction before display 1.10 on p. 340 is nonnegative. -/
theorem correction_nonneg (x : ℝ) (q l : ℕ) :
    0 ≤ weightedMod x q l - (piMod x q l : ℝ) := by
  rw [correction_eq]
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact (mangoldt_log_ratio n).1
  · rfl

/-- Mathlib identifies the nonprime Mangoldt mass used for the p. 340 correction. -/
theorem mangoldt_nonprime_sum (x : ℝ) :
    (∑ n ∈ Finset.Iic ⌊x⌋₊, if ¬n.Prime then vonMangoldt n else 0) =
      Chebyshev.psi x - Chebyshev.theta x := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
  have he : Finset.Iic ⌊x⌋₊ = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [he, Finset.sum_insert (by simp)]
  simp

/-- A supporting global prime power bound for p. 340, split at square root x. -/
theorem correction_le {x : ℝ} (hx : 2 ≤ x) (q l : ℕ) :
    weightedMod x q l - (piMod x q l : ℝ) ≤ 5 * Real.sqrt x + 1 := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hterm : ∀ n : ℕ,
      (if ¬n.Prime ∧ n % q = l % q then vonMangoldt n / Real.log n else 0) ≤
      (if (n : ℝ) ≤ Real.sqrt x then 1 else 0) +
        2 / Real.log x * (if ¬n.Prime then vonMangoldt n else 0) := by
    intro n
    by_cases hn : (n : ℝ) ≤ Real.sqrt x
    · have hpos : 0 ≤ 2 / Real.log x * (if ¬n.Prime then vonMangoldt n else 0) := by
        positivity
      rw [ite_eq_left hn]
      have ha : (if ¬n.Prime ∧ n % q = l % q then vonMangoldt n / Real.log n else 0) ≤ 1 := by
        split_ifs
        · exact (mangoldt_log_ratio n).2
        · norm_num
      exact ha.trans (le_add_of_nonneg_right hpos)
    · have hn0 : 0 < (n : ℝ) := lt_trans hsqrt (lt_of_not_ge hn)
      have hln : Real.log x / 2 ≤ Real.log n := by
        rw [← Real.log_sqrt hx0.le]
        exact Real.log_le_log hsqrt (le_of_lt (lt_of_not_ge hn))
      have hln0 : 0 < Real.log (n : ℝ) := by linarith
      rw [ite_eq_right hn]
      by_cases hp : ¬n.Prime ∧ n % q = l % q
      · simp only [ite_eq_left hp, ite_eq_left hp.1, zero_add]
        have hv : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
        have he : vonMangoldt n / Real.log n ≤ 2 / Real.log x * vonMangoldt n := by
          rw [div_le_iff₀ hln0]
          have hh := mul_le_mul_of_nonneg_left hln hv
          field_simp
          nlinarith
        exact he
      · rw [ite_eq_right hp]
        positivity
  rw [correction_eq]
  calc
    _ ≤ ∑ n ∈ Finset.Iic ⌊x⌋₊,
        ((if (n : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) +
          2 / Real.log x * (if ¬n.Prime then vonMangoldt n else 0)) :=
      Finset.sum_le_sum (fun n hn => hterm n)
    _ = (∑ n ∈ Finset.Iic ⌊x⌋₊, if (n : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) +
        2 / Real.log x * (Chebyshev.psi x - Chebyshev.theta x) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, mangoldt_nonprime_sum]
    _ ≤ Real.sqrt x + 1 + 2 / Real.log x * (2 * Real.sqrt x * Real.log x) := by
      apply add_le_add
      · have hh : ((Finset.Iic ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt x)).card ≤
            (Finset.Iic ⌊Real.sqrt x⌋₊).card := by
          apply Finset.card_le_card
          intro n hn
          exact Finset.mem_Iic.mpr (Nat.le_floor (Finset.mem_filter.mp hn).2)
        simp only [Nat.card_Iic] at hh
        have hh' : (∑ n ∈ Finset.Iic ⌊x⌋₊, if (n : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) ≤
            (⌊Real.sqrt x⌋₊ : ℝ) + 1 := by
          have hcast : (((Finset.Iic ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt x)).card : ℝ) ≤
              (⌊Real.sqrt x⌋₊ : ℝ) + 1 := by exact_mod_cast hh
          simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hcast
        exact hh'.trans (by linarith [Nat.floor_le hsqrt.le])
      · exact mul_le_mul_of_nonneg_left (Chebyshev.psi_sub_theta_le (by linarith)) (by positivity)
    _ = _ := by field_simp; ring


/-- The supporting global prime power budget for pp. 340 to 341.
The bound is derived from Mathlib Chebyshev estimates and uses no progression estimate. -/
theorem weighted_prime_power_error {q l : ℕ} {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |weightedMod x q l - (piMod x q l : ℝ)| ≤
      0.35 * Real.sqrt x * Real.log x := by
  have hx2 : 2 ≤ x := by linarith
  have hL : 20 ≤ Real.log x := by
    have hh : Real.log ((10 : ℝ) ^ 9) ≤ Real.log x := Real.log_le_log (by positivity) hx
    rw [Real.log_pow, Real.log_ten_eq] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hs : 1 ≤ Real.sqrt x := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
    simpa using hh
  rw [abs_of_nonneg (correction_nonneg x q l)]
  have hb := correction_le hx2 q l
  nlinarith [mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg x)]

/-! ### Explicit estimates for the modulus one prime count -/

private theorem log_two_ge_0693 : (0.693 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

private theorem log_four_le_14 : Real.log 4 ≤ 1.4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h]
  linarith [Real.log_two_lt_d9]

private theorem sqrt_ge_31622 {x : ℝ} (hx : (10 : ℝ) ^ 9 ≤ x) :
    (31622 : ℝ) ≤ Real.sqrt x := by
  have h9 : ((10 : ℝ) ^ 9) = 1000000000 := by norm_num
  have hxx : (31622 : ℝ) ^ 2 ≤ x := by
    have hsq : (31622 : ℝ) ^ 2 = 999950884 := by norm_num
    rw [hsq, h9] at *
    linarith
  calc (31622 : ℝ) = Real.sqrt ((31622 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hxx

private theorem log_ge_207 {x : ℝ} (hx : (10 : ℝ) ^ 9 ≤ x) : (20.7 : ℝ) ≤ Real.log x := by
  have h0 : (0 : ℝ) < (10 : ℝ) ^ 9 := by norm_num
  have h10 : (2.302 : ℝ) ≤ Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have h : (20.7 : ℝ) ≤ Real.log ((10 : ℝ) ^ 9) := by
    rw [Real.log_pow]
    push_cast
    linarith
  exact h.trans (Real.log_le_log h0 hx)

private theorem log_ge_693 {u : ℝ} (hu : (1024 : ℝ) ≤ u) : (6.93 : ℝ) ≤ Real.log u := by
  have h0 : (0 : ℝ) < 1024 := by norm_num
  have h : (6.93 : ℝ) ≤ Real.log (1024 : ℝ) := by
    have e : (1024 : ℝ) = 2 ^ (10 : ℕ) := by norm_num
    rw [e, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  exact h.trans (Real.log_le_log h0 hu)

/-- `c ≤ u^(1/n)` from `c^n ≤ u`. -/
private theorem le_rpow_recip {u : ℝ} (hu : (0 : ℝ) ≤ u) {n : ℕ} (hn : 0 < n) {c : ℝ}
    (hc : (0 : ℝ) ≤ c) (h : c ^ n ≤ u) : c ≤ u ^ ((n : ℝ)⁻¹) := by
  have h1 : (c ^ n : ℝ) ^ ((n : ℝ)⁻¹) ≤ u ^ ((n : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  have e : (c ^ n : ℝ) ^ ((n : ℝ)⁻¹) = c := by
    rw [← Real.rpow_natCast c n, ← Real.rpow_mul hc,
      mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
    exact Real.rpow_one c
  rwa [e] at h1

private theorem rpow_small {u : ℝ} (hu : (1024 : ℝ) ≤ u) {k : ℕ} (hk : 3 ≤ k) :
    u ^ ((k : ℝ)⁻¹) ≤ Real.sqrt u / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hk1 : (1 : ℝ) ≤ u := by linarith
  have htwo : (2 : ℝ) ≤ u ^ ((6 : ℝ)⁻¹) := by
    refine le_rpow_recip hu0 (by norm_num : (0:ℕ) < 6) (by norm_num : (0:ℝ) ≤ 2) ?_
    have h64 : ((2 : ℝ) ^ 6) = 64 := by norm_num
    rw [h64]
    linarith
  have hexp : ((k : ℝ)⁻¹) ≤ ((3 : ℝ)⁻¹) := by
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h := one_div_le_one_div_of_le (a := (3 : ℝ)) (b := (k : ℝ)) (by norm_num) hk3
    simpa [one_div] using h
  have h1 : u ^ ((k : ℝ)⁻¹) ≤ u ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hk1 hexp
  have h2 : u ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt u / 2 := by
    have hpos : (0 : ℝ) < u ^ ((3 : ℝ)⁻¹) := Real.rpow_pos_of_pos (by linarith) _
    have hs2 : Real.sqrt u = u ^ ((6 : ℝ)⁻¹) * u ^ ((3 : ℝ)⁻¹) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < u), Real.sqrt_eq_rpow]
      norm_num
    rw [hs2, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [htwo, hpos]
  exact h1.trans h2

private theorem rpow_small_big {u : ℝ} (hu : (10 : ℝ) ^ 9 ≤ u) {k : ℕ} (hk : 3 ≤ k) :
    u ^ ((k : ℝ)⁻¹) ≤ Real.sqrt u / 30 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hk1 : (1 : ℝ) ≤ u := by linarith
  have hthirty : (30 : ℝ) ≤ u ^ ((6 : ℝ)⁻¹) := by
    refine le_rpow_recip hu0 (by norm_num : (0:ℕ) < 6) (by norm_num : (0:ℝ) ≤ 30) ?_
    have h9 : ((10 : ℝ) ^ 9) = 1000000000 := by norm_num
    rw [h9] at hu
    nlinarith
  have hexp : ((k : ℝ)⁻¹) ≤ ((3 : ℝ)⁻¹) := by
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h := one_div_le_one_div_of_le (a := (3 : ℝ)) (b := (k : ℝ)) (by norm_num) hk3
    simpa [one_div] using h
  have h1 : u ^ ((k : ℝ)⁻¹) ≤ u ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hk1 hexp
  have h2 : u ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt u / 30 := by
    have hpos : (0 : ℝ) < u ^ ((3 : ℝ)⁻¹) := Real.rpow_pos_of_pos (by linarith) _
    have hs2 : Real.sqrt u = u ^ ((6 : ℝ)⁻¹) * u ^ ((3 : ℝ)⁻¹) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < u), Real.sqrt_eq_rpow]
      norm_num
    rw [hs2, le_div_iff₀ (by norm_num : (0 : ℝ) < 30)]
    nlinarith [hthirty, hpos]
  exact h1.trans h2

/-- `ψ - θ` at the three Costa-Pereira levels, with the Chebyshev bound on each `ψ`. -/
private theorem psi_sub_theta_explicit {u : ℝ} (hu : 2 ≤ u) :
    Chebyshev.psi u - Chebyshev.theta u ≤
      Real.log 4 * (Real.sqrt u + u ^ ((3 : ℝ)⁻¹) + u ^ ((5 : ℝ)⁻¹)) +
        u ^ ((4 : ℝ)⁻¹) * Real.log u + (2 / 3) * u ^ ((6 : ℝ)⁻¹) * Real.log u +
          (2 / 5) * u ^ ((10 : ℝ)⁻¹) * Real.log u := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi u
  have h1 : Chebyshev.psi (Real.sqrt u) ≤
      Real.log 4 * Real.sqrt u + u ^ ((4 : ℝ)⁻¹) * Real.log u := by
    have hp := Chebyshev.psi_le (x := Real.sqrt u) (Real.one_le_sqrt.mpr hu1)
    have hl : Real.log (Real.sqrt u) = Real.log u / 2 := Real.log_sqrt hu0
    have hs : Real.sqrt (Real.sqrt u) = u ^ ((4 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hu0]
      norm_num
    rw [hs, hl] at hp
    linarith
  have h2 : Chebyshev.psi (u ^ ((3 : ℝ)⁻¹)) ≤
      Real.log 4 * u ^ ((3 : ℝ)⁻¹) + (2 / 3) * u ^ ((6 : ℝ)⁻¹) * Real.log u := by
    have hpos : (0 : ℝ) < u := by linarith
    have hone : (1 : ℝ) ≤ u ^ ((3 : ℝ)⁻¹) := Real.one_le_rpow hu1 (by norm_num)
    have hp := Chebyshev.psi_le (x := u ^ ((3 : ℝ)⁻¹)) hone
    have hl : Real.log (u ^ ((3 : ℝ)⁻¹)) = Real.log u / 3 := by
      rw [Real.log_rpow hpos]
      ring
    have hs : Real.sqrt (u ^ ((3 : ℝ)⁻¹)) = u ^ ((6 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu0]
      norm_num
    rw [hs, hl] at hp
    linarith
  have h3 : Chebyshev.psi (u ^ ((5 : ℝ)⁻¹)) ≤
      Real.log 4 * u ^ ((5 : ℝ)⁻¹) + (2 / 5) * u ^ ((10 : ℝ)⁻¹) * Real.log u := by
    have hpos : (0 : ℝ) < u := by linarith
    have hone : (1 : ℝ) ≤ u ^ ((5 : ℝ)⁻¹) := Real.one_le_rpow hu1 (by norm_num)
    have hp := Chebyshev.psi_le (x := u ^ ((5 : ℝ)⁻¹)) hone
    have hl : Real.log (u ^ ((5 : ℝ)⁻¹)) = Real.log u / 5 := by
      rw [Real.log_rpow hpos]
      ring
    have hs : Real.sqrt (u ^ ((5 : ℝ)⁻¹)) = u ^ ((10 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu0]
      norm_num
    rw [hs, hl] at hp
    linarith
  have e2 : u ^ ((2 : ℝ)⁻¹) = Real.sqrt u := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [e2] at hcp
  linarith [h1, h2, h3]

/-- The `ψ` error of reference 4 in the shape used below. -/
private theorem psi_error_le (hG : LeanLab.DERZ1997.GRH) {u : ℝ} (hu : 75 < u) :
    |Chebyshev.psi u - u| ≤ 0.04 * (Real.sqrt u * Real.log u ^ 2) := by
  have hp := LeanLab.Zinoviev1997.Decomp575c.schoenfeld_psi hG hu
  have hpi : 1 / (8 * Real.pi) ≤ 0.04 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d20]
  have h0 : (0 : ℝ) ≤ Real.sqrt u * Real.log u ^ 2 := by positivity
  have h2 : (1 / (8 * Real.pi)) * Real.sqrt u * Real.log u ^ 2 ≤
      0.04 * (Real.sqrt u * Real.log u ^ 2) := by
    nlinarith [hpi, h0]
  exact hp.trans h2

/-- The kernel of the `θ` remainder is at most `5.012` on `[2, 1024]`. -/
private theorem theta_error_pointwise_small {u : ℝ} (hu : (2 : ℝ) ≤ u) :
    |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)| ≤ 5.012 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : (0.693 : ℝ) ≤ Real.log u :=
    (log_two_ge_0693).trans (Real.log_le_log (by norm_num) hu)
  have hsq : (0.48 : ℝ) ≤ Real.log u ^ 2 := by nlinarith
  have ht : Chebyshev.theta u ≤ 1.4 * u := by
    refine (Chebyshev.theta_le_log4_mul_x (le_of_lt hu0)).trans ?_
    nlinarith [hu0, log_four_le_14]
  have habs : |Chebyshev.theta u - u| ≤ 2.4 * u := by
    rw [abs_le]
    constructor
    · nlinarith [Chebyshev.theta_nonneg u]
    · nlinarith [ht]
  have hden : (0 : ℝ) < u * Real.log u ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h2 : (2.4 : ℝ) * u ≤ 5.012 * (u * Real.log u ^ 2) := by nlinarith [hsq, hu0]
  linarith [habs, h2]

/-- The same kernel decays like `0.3 / √u` from `1024` on, under GRH. -/
private theorem theta_error_pointwise_decay (hG : LeanLab.DERZ1997.GRH) {u : ℝ}
    (hu : (1024 : ℝ) ≤ u) :
    |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)| ≤ 0.3 / Real.sqrt u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlog : (6.93 : ℝ) ≤ Real.log u := log_ge_693 hu
  have hsq : (48 : ℝ) ≤ Real.log u ^ 2 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hden : (0 : ℝ) < u * Real.log u ^ 2 := by positivity
  have hpsi := psi_error_le hG (u := u) (by linarith : 75 < u)
  have hpt := psi_sub_theta_explicit (by linarith : 2 ≤ u)
  have h3 := rpow_small hu (k := 3) (by norm_num)
  have h4 := rpow_small hu (k := 4) (by norm_num)
  have h5 := rpow_small hu (k := 5) (by norm_num)
  have h6 := rpow_small hu (k := 6) (by norm_num)
  have h10 := rpow_small hu (k := 10) (by norm_num)
  have hpd : Chebyshev.psi u - Chebyshev.theta u ≤ 0.26 * (Real.sqrt u * Real.log u ^ 2) := by
    have hl0 : (0 : ℝ) ≤ Real.log u := by linarith
    have hl4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hsum : Real.sqrt u + u ^ ((3 : ℝ)⁻¹) + u ^ ((5 : ℝ)⁻¹) ≤ 2 * Real.sqrt u := by
      linarith
    have e1 : Real.log 4 * (Real.sqrt u + u ^ ((3 : ℝ)⁻¹) + u ^ ((5 : ℝ)⁻¹)) ≤
        2.8 * Real.sqrt u := by
      have h := mul_le_mul log_four_le_14 hsum (by positivity) (by positivity)
      linarith [h]
    have e2 : u ^ ((4 : ℝ)⁻¹) * Real.log u ≤ 0.5 * (Real.sqrt u * Real.log u) := by
      have h := mul_le_mul_of_nonneg_right h4 hl0
      linarith [h]
    have e3 : (2 / 3) * u ^ ((6 : ℝ)⁻¹) * Real.log u ≤
        (1 / 3) * (Real.sqrt u * Real.log u) := by
      have h := mul_le_mul_of_nonneg_right h6 hl0
      linarith [h]
    have e4 : (2 / 5) * u ^ ((10 : ℝ)⁻¹) * Real.log u ≤
        (1 / 5) * (Real.sqrt u * Real.log u) := by
      have h := mul_le_mul_of_nonneg_right h10 hl0
      linarith [h]
    have hquad : 2.8 * Real.sqrt u + (0.5 + 1 / 3 + 1 / 5) * (Real.sqrt u * Real.log u) ≤
        0.26 * (Real.sqrt u * Real.log u ^ 2) := by
      have hbr : (0 : ℝ) < 0.26 * Real.log u ^ 2 - (0.5 + 1/3 + 1/5) * Real.log u - 2.8 := by
        nlinarith [hlog, hsq]
      nlinarith [mul_pos hs hbr]
    linarith [hpt, e1, e2, e3, e4, hquad]
  have habs : |Chebyshev.theta u - u| ≤
      0.04 * (Real.sqrt u * Real.log u ^ 2) + (Chebyshev.psi u - Chebyshev.theta u) := by
    have hlow : u - Chebyshev.theta u ≤
        0.04 * (Real.sqrt u * Real.log u ^ 2) + (Chebyshev.psi u - Chebyshev.theta u) := by
      have h1 : u - Chebyshev.theta u =
          (u - Chebyshev.psi u) + (Chebyshev.psi u - Chebyshev.theta u) := by ring
      have h2 : u - Chebyshev.psi u ≤ |Chebyshev.psi u - u| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    have hup : Chebyshev.theta u - u ≤
        0.04 * (Real.sqrt u * Real.log u ^ 2) + (Chebyshev.psi u - Chebyshev.theta u) := by
      have h1 : Chebyshev.theta u - u ≤ Chebyshev.psi u - u := by
        linarith [Chebyshev.theta_le_psi u]
      linarith [h1, le_abs_self (Chebyshev.psi u - u), hpsi]
    exact abs_le.mpr ⟨by linarith, hup⟩
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hcore : (0.3 / Real.sqrt u) * u = 0.3 * Real.sqrt u := by
    have hsne : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu0).ne'
    field_simp
    nlinarith [Real.sq_sqrt hu0.le]
  have he : (0.3 / Real.sqrt u) * (u * Real.log u ^ 2) =
      0.3 * (Real.sqrt u * Real.log u ^ 2) := by
    calc (0.3 / Real.sqrt u) * (u * Real.log u ^ 2)
        = ((0.3 / Real.sqrt u) * u) * Real.log u ^ 2 := by ring
      _ = (0.3 * Real.sqrt u) * Real.log u ^ 2 := by rw [hcore]
      _ = 0.3 * (Real.sqrt u * Real.log u ^ 2) := by ring
  rw [he]
  linarith [habs, hpd]

/-- The `θ` kernel is integrable on any interval inside the positive reals. -/
private theorem theta_kernel_integrable' {a x : ℝ} (ha : (2 : ℝ) ≤ a) (hax : a ≤ x) :
    IntervalIntegrable
      (fun u : ℝ => (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) volume a x := by
  have hx2 : (2 : ℝ) ≤ x := ha.trans hax
  have h1 : IntegrableOn (fun u : ℝ => Chebyshev.theta u / (u * Real.log u ^ 2))
      (Set.Icc a x) volume :=
    (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (fun u hu => ⟨ha.trans hu.1, hu.2⟩)
  have h2 : IntegrableOn (fun u : ℝ => 1 / Real.log u ^ 2) (Set.Icc a x) volume :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hx2).mp (logarithmic_kernels hx2).1).mono_set
      (fun u hu => ⟨ha.trans hu.1, hu.2⟩)
  have hi : IntervalIntegrable
      (fun u : ℝ => Chebyshev.theta u / (u * Real.log u ^ 2) - 1 / Real.log u ^ 2)
      volume a x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hax).mpr (h1.sub h2)
  apply hi.congr
  intro u hu
  have hu0 : u ≠ 0 := by
    rw [Set.uIoc_of_le hax] at hu
    linarith [hu.1]
  field_simp

/-- The modulus one count as `Nat.primeCounting`. -/
private theorem piMod_one_card (x : ℝ) (l : ℕ) : piMod x 1 l = Nat.primeCounting ⌊x⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  unfold piMod
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mod_one, and_true, Nat.mem_primesLE]

/-- Abel summation for the ordinary prime count against `zinLi`. -/
private theorem prime_count_abel {x : ℝ} (hx : 2 ≤ x) (l : ℕ) :
    (piMod x 1 l : ℝ) - zinLi x =
      (Chebyshev.theta x - x) / Real.log x +
        (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) +
          2 / Real.log 2 := by
  have h1 : (piMod x 1 l : ℝ) = Chebyshev.theta x / Real.log x +
      ∫ u in (2 : ℝ)..x, Chebyshev.theta u / (u * Real.log u ^ 2) := by
    rw [piMod_one_card]
    exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have h2 : zinLi x = x / Real.log x - 2 / Real.log 2 +
      ∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2 := zinLi_by_parts hx
  have hI1 : IntervalIntegrable
      (fun u : ℝ => Chebyshev.theta u / (u * Real.log u ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hI2 : IntervalIntegrable (fun u : ℝ => 1 / Real.log u ^ 2) volume 2 x :=
    (logarithmic_kernels hx).1
  have hi : (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) =
      (∫ u in (2 : ℝ)..x, Chebyshev.theta u / (u * Real.log u ^ 2)) -
        (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [Set.uIcc_of_le hx] at hu
      linarith [hu.1]
    field_simp
  rw [hi, h1, h2]
  ring

/-- The `θ` remainder integral is bounded by `0.6 √x + 5130`. -/
private theorem theta_error_integral (hG : LeanLab.DERZ1997.GRH) {x : ℝ}
    (hx : (10 : ℝ) ^ 9 ≤ x) :
    |∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)| ≤
      0.6 * Real.sqrt x + 5130 := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hax : (1024 : ℝ) ≤ x := by linarith
  have hf1 : IntervalIntegrable
      (fun u : ℝ => (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) volume 2 1024 :=
    theta_kernel_integrable' (by norm_num) (by norm_num)
  have hf2 : IntervalIntegrable
      (fun u : ℝ => (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) volume 1024 x :=
    theta_kernel_integrable' (by norm_num) hax
  have hg : IntervalIntegrable (fun u : ℝ => 0.3 / Real.sqrt u) volume 1024 x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
    intro u hu
    rw [Set.uIcc_of_le hax] at hu
    exact (Real.sqrt_pos.mpr (by linarith [hu.1])).ne'
  have hL : (∫ u in (2 : ℝ)..1024,
      |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)|) ≤ 5123 := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (2:ℝ) ≤ 1024)
      hf1.abs intervalIntegrable_const
      (fun u hu => theta_error_pointwise_small hu.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    nlinarith
  have hR : (∫ u in (1024 : ℝ)..x,
      |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)|) ≤ 0.6 * Real.sqrt x := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) hax hf2.abs hg
      (fun u hu => theta_error_pointwise_decay hG hu.1)
    have hv : (∫ u in (1024 : ℝ)..x, 0.3 / Real.sqrt u) = 0.6 * (Real.sqrt x - 32) := by
      have hcongr : (∫ u in (1024 : ℝ)..x, 0.3 / Real.sqrt u) =
          ∫ u in (1024 : ℝ)..x, 0.3 * u ^ ((-1 : ℝ)/2) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hax] at hu
        have hu0 : (0 : ℝ) < u := by linarith [hu.1]
        change 0.3 / Real.sqrt u = 0.3 * u ^ ((-1 : ℝ)/2)
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hu0)]
        norm_num
      rw [hcongr, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -1/2))]
      have hx' : x ^ ((-1 : ℝ)/2 + 1) = Real.sqrt x := by
        rw [show (-1 : ℝ)/2 + 1 = (1 : ℝ)/2 by norm_num, ← Real.sqrt_eq_rpow]
      have h32 : (1024 : ℝ) ^ ((-1 : ℝ)/2 + 1) = 32 := by
        rw [show (-1 : ℝ)/2 + 1 = (1 : ℝ)/2 by norm_num,
          show (1024 : ℝ) = 32 ^ 2 by norm_num,
          ← Real.rpow_natCast (32 : ℝ) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 32)]
        norm_num
      rw [hx', h32, show (-1 : ℝ)/2 + 1 = (1 : ℝ)/2 by norm_num]
      ring
    have hs : (32 : ℝ) ≤ Real.sqrt x := by
      have h1 : (32 : ℝ) = Real.sqrt ((32 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      rw [h1]
      apply Real.sqrt_le_sqrt
      linarith
    nlinarith [hm, hv]
  have hsplit : (∫ u in (2 : ℝ)..x,
      |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)|) =
      (∫ u in (2 : ℝ)..1024, |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)|) +
        (∫ u in (1024 : ℝ)..x, |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)|) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hf1.abs hf2.abs]
  calc |∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)|
      ≤ ∫ u in (2 : ℝ)..x, |(Chebyshev.theta u - u) / (u * Real.log u ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hx2
    _ = _ := hsplit
    _ ≤ 0.6 * Real.sqrt x + 5130 := by linarith [hL, hR]

/-- The endpoint `θ` remainder. -/
private theorem theta_error_endpoint (hG : LeanLab.DERZ1997.GRH) {x : ℝ}
    (hx : (10 : ℝ) ^ 9 ≤ x) :
    |(Chebyshev.theta x - x) / Real.log x| ≤
      0.04 * Real.sqrt x * Real.log x + 0.15 * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hL : (20.7 : ℝ) ≤ Real.log x := log_ge_207 hx
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hpsi := psi_error_le hG (u := x) (by linarith : 75 < x)
  have hpt := psi_sub_theta_explicit (by linarith : 2 ≤ x)
  have h3 := rpow_small_big hx (k := 3) (by norm_num)
  have h4 := rpow_small_big hx (k := 4) (by norm_num)
  have h5 := rpow_small_big hx (k := 5) (by norm_num)
  have h6 := rpow_small_big hx (k := 6) (by norm_num)
  have h10 := rpow_small_big hx (k := 10) (by norm_num)
  have hpd : Chebyshev.psi x - Chebyshev.theta x ≤ 0.15 * Real.sqrt x * Real.log x := by
    have hl4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hsum : Real.sqrt x + x ^ ((3 : ℝ)⁻¹) + x ^ ((5 : ℝ)⁻¹) ≤ 1.07 * Real.sqrt x := by
      linarith
    have e1 : Real.log 4 * (Real.sqrt x + x ^ ((3 : ℝ)⁻¹) + x ^ ((5 : ℝ)⁻¹)) ≤
        1.5 * Real.sqrt x := by
      have h := mul_le_mul log_four_le_14 hsum (by positivity) (by positivity)
      linarith [h]
    have e2 : x ^ ((4 : ℝ)⁻¹) * Real.log x ≤ (1/30) * (Real.sqrt x * Real.log x) := by
      have h := mul_le_mul_of_nonneg_right h4 hL0.le
      linarith [h]
    have e3 : (2 / 3) * x ^ ((6 : ℝ)⁻¹) * Real.log x ≤
        (2/90) * (Real.sqrt x * Real.log x) := by
      have h := mul_le_mul_of_nonneg_right h6 hL0.le
      linarith [h]
    have e4 : (2 / 5) * x ^ ((10 : ℝ)⁻¹) * Real.log x ≤
        (2/150) * (Real.sqrt x * Real.log x) := by
      have h := mul_le_mul_of_nonneg_right h10 hL0.le
      linarith [h]
    have hprod : (0 : ℝ) ≤ Real.sqrt x * Real.log x := by positivity
    nlinarith [hpt, e1, e2, e3, e4, hL, hs]
  have habs : |Chebyshev.theta x - x| ≤
      0.04 * (Real.sqrt x * Real.log x ^ 2) + (Chebyshev.psi x - Chebyshev.theta x) := by
    have hlow : x - Chebyshev.theta x ≤
        0.04 * (Real.sqrt x * Real.log x ^ 2) + (Chebyshev.psi x - Chebyshev.theta x) := by
      have h1 : x - Chebyshev.theta x =
          (x - Chebyshev.psi x) + (Chebyshev.psi x - Chebyshev.theta x) := by ring
      have h2 : x - Chebyshev.psi x ≤ |Chebyshev.psi x - x| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    have hup : Chebyshev.theta x - x ≤
        0.04 * (Real.sqrt x * Real.log x ^ 2) + (Chebyshev.psi x - Chebyshev.theta x) := by
      have h1 : Chebyshev.theta x - x ≤ Chebyshev.psi x - x := by
        linarith [Chebyshev.theta_le_psi x]
      linarith [h1, le_abs_self (Chebyshev.psi x - x), hpsi]
    exact abs_le.mpr ⟨by linarith, hup⟩
  rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
  nlinarith [habs, hpd]

/-- The lower endpoint constant of the Abel formula. -/
private theorem two_div_log_two_le : |2 / Real.log 2| ≤ 2.9 := by
  have h : (0.693 : ℝ) ≤ Real.log 2 := log_two_ge_0693
  have h0 : (0 : ℝ) < Real.log 2 := by linarith
  rw [abs_of_pos (by positivity)]
  rw [div_le_iff₀ h0]
  nlinarith

/-- LEAF. Proposition 1.4, p. 341, last paragraph, reference 4.
Supporting relaxed Schoenfeld prime counting bound for the ordinary prime count.
The additive two covers the normalization from the classical li to the integral
from two used here. This leaf is restricted to modulus one. -/
theorem schoenfeld_prime_counting (hG : LeanLab.DERZ1997.GRH)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |(piMod x 1 0 : ℝ) - zinLi x| ≤
      0.1 * Real.sqrt x * Real.log x + 2 := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hs := sqrt_ge_31622 hx
  have hL := log_ge_207 hx
  have hab := prime_count_abel hx2 0
  have hA := theta_error_endpoint hG hx
  have hI := theta_error_integral hG hx
  have hC := two_div_log_two_le
  have h1 : |(Chebyshev.theta x - x) / Real.log x +
      (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) +
        2 / Real.log 2| ≤
      (0.04 * Real.sqrt x * Real.log x + 0.15 * Real.sqrt x) +
        (0.6 * Real.sqrt x + 5130) + 2.9 := by
    calc |(Chebyshev.theta x - x) / Real.log x +
        (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) +
          2 / Real.log 2|
        ≤ |(Chebyshev.theta x - x) / Real.log x +
            (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2))| +
            |2 / Real.log 2| := abs_add_le _ _
      _ ≤ (|(Chebyshev.theta x - x) / Real.log x| +
            |∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)|) +
            |2 / Real.log 2| := by
          have h := abs_add_le ((Chebyshev.theta x - x) / Real.log x)
            (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2))
          linarith
      _ ≤ _ := by linarith [hA, hI, hC]
  have hprod : (0 : ℝ) ≤ Real.sqrt x * Real.log x := by positivity
  calc |(piMod x 1 0 : ℝ) - zinLi x|
      = |(Chebyshev.theta x - x) / Real.log x +
          (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) +
            2 / Real.log 2| := by rw [hab]
    _ ≤ 0.04 * Real.sqrt x * Real.log x + 0.15 * Real.sqrt x +
        (0.6 * Real.sqrt x + 5130) + 2.9 := h1
    _ ≤ 0.1 * Real.sqrt x * Real.log x + 2 := by nlinarith [hs, hL, hprod]


/-- Scalar assembly of the three separate budgets from pp. 340 to 341.
This implication proves no analytic estimate assumed in its hypotheses. -/
theorem error_bound_of_budgets {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 2 ≤ x)
    (hendpoint : |psiMod x q l - x / (Nat.totient q : ℝ)| ≤
      0.85 * Real.sqrt x * Real.log x ^ 2)
    (hintegral : (∫ u in (2 : ℝ)..x,
      |psiMod u q l - u / (Nat.totient q : ℝ)| / (u * Real.log u ^ 2)) ≤
      0.1 * Real.sqrt x * Real.log x + 10 ^ 8 -
        2 / ((Nat.totient q : ℝ) * Real.log 2))
    (hpowers : |weightedMod x q l - (piMod x q l : ℝ)| ≤
      0.35 * Real.sqrt x * Real.log x) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hphi : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have he : |(psiMod x q l - x / (Nat.totient q : ℝ)) / Real.log x| ≤
      0.85 * Real.sqrt x * Real.log x := by
    rw [abs_div, abs_of_pos hlog, div_le_iff₀ hlog]
    nlinarith only [hendpoint]
  have hc : |2 / ((Nat.totient q : ℝ) * Real.log 2)| =
      2 / ((Nat.totient q : ℝ) * Real.log 2) := abs_of_pos (by positivity)
  have hw : |weightedMod x q l - zinLi x / (Nat.totient q : ℝ)| ≤
      0.95 * Real.sqrt x * Real.log x + 10 ^ 8 := by
    rw [centered_abel hx hq l]
    have hi := (centered_integral_abs hx q l).trans hintegral
    have ht := abs_add_le
      ((psiMod x q l - x / (Nat.totient q : ℝ)) / Real.log x)
      (∫ u in (2 : ℝ)..x,
        (psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2))
    have ht' := abs_add_le
      ((psiMod x q l - x / (Nat.totient q : ℝ)) / Real.log x +
        ∫ u in (2 : ℝ)..x,
          (psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2))
      (2 / ((Nat.totient q : ℝ) * Real.log 2))
    rw [hc] at ht'
    linarith
  calc
    _ = |((piMod x q l : ℝ) - weightedMod x q l) +
        (weightedMod x q l - zinLi x / (Nat.totient q : ℝ))| := by congr 1; ring
    _ ≤ |(piMod x q l : ℝ) - weightedMod x q l| +
        |weightedMod x q l - zinLi x / (Nat.totient q : ℝ)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_sub_comm (piMod x q l : ℝ)]; linarith

/-- Exact supply statement for prop14_error_bound on pp. 339 to 341.
CONDITIONAL ON integrated_progression_error, schoenfeld_prime_counting,
schoenfeld_psi and the unchanged lemma13_explicit_budget. -/
theorem prop14_error_bound (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 1 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  have hx2 : 2 ≤ x := by linarith
  have hS : 0 ≤ Real.sqrt x * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg (by linarith))
  rcases (by omega : q = 1 ∨ q = 2 ∨ 3 ≤ q) with rfl | rfl | hq3
  · have hs := schoenfeld_prime_counting hG hx
    rw [piMod_one]
    simp only [Nat.totient_one, Nat.cast_one, div_one]
    nlinarith only [hs, hS]
  · have hs := schoenfeld_prime_counting hG hx
    have hc : (piMod x 2 l : ℝ) + 1 = (piMod x 1 0 : ℝ) := by
      exact_mod_cast piMod_two hx2 hl
    have he : |(piMod x 2 l : ℝ) - zinLi x| ≤
        |(piMod x 1 0 : ℝ) - zinLi x| + 1 := by
      calc
        _ = |((piMod x 1 0 : ℝ) - zinLi x) - 1| := by rw [← hc]; congr 1; ring
        _ ≤ _ := by simpa using abs_sub ((piMod x 1 0 : ℝ) - zinLi x) 1
    simp only [show Nat.totient 2 = 1 by decide, Nat.cast_one, div_one]
    nlinarith only [hs, he, hS]
  · exact error_bound_of_budgets hq hx2
      (progression_endpoint hG hq3 hl hx hqx)
      (integrated_progression_error hG hq3 hl hx hqx)
      (weighted_prime_power_error hx)

/-- A nonempty arithmetic domain for Proposition 1.4 on p. 339. -/
theorem arithmetic_domain_instance :
    (10 ^ 9 : ℝ) ≥ 10 ^ 9 ∧ Nat.Coprime 1 3 ∧
      (3 : ℝ) ≤ (10 ^ 9 : ℝ) ^ (0.37 : ℝ) := by
  refine ⟨le_rfl, by norm_num, ?_⟩
  have hL : 20 ≤ Real.log ((10 : ℝ) ^ 9) := by
    rw [Real.log_pow, Real.log_ten_eq]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 3) (by positivity)).mp
  rw [Real.log_rpow (by positivity : (0 : ℝ) < 10 ^ 9)]
  norm_num at hL ⊢
  linarith [Real.log_three_lt_d9]

/-- The endpoint range in Proposition 1.4 is not a uniform interior range.
This diagnostic concerns the range condition alone and asserts no paper error. -/
theorem endpoint_modulus_range_not_uniform :
    ∃ x : ℝ, 10 ^ 9 ≤ x ∧ (3 : ℝ) ≤ x ^ (0.37 : ℝ) ∧
      ∃ u ∈ Set.Icc (2 : ℝ) x, ¬ (3 : ℝ) ≤ u ^ (0.37 : ℝ) := by
  refine ⟨10 ^ 9, le_rfl, arithmetic_domain_instance.2.2, 2, by norm_num, ?_⟩
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (0.37 : ℝ) ≤ 1)
  norm_num only [Real.rpow_one] at h
  linarith

/-- A lower bound for the positive kernel used in the p. 341 remainder. -/
theorem logarithmic_integral_lower {a x : ℝ} (ha : 1 < a) (hax : a ≤ x) :
    (x - a) / Real.log x ^ 2 ≤ ∫ u in a..x, 1 / Real.log u ^ 2 := by
  have hlog : ∀ u ∈ Set.uIcc a x, 0 < Real.log u := by
    intro u hu
    rw [Set.uIcc_of_le hax] at hu
    exact Real.log_pos (ha.trans_le hu.1)
  have hc : ContinuousOn (fun u : ℝ => 1 / Real.log u ^ 2) (Set.uIcc a x) := by
    apply continuousOn_const.div
    · exact (Real.continuousOn_log.mono (by
        intro u hu
        rw [Set.uIcc_of_le hax] at hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [hu.1])).pow 2
    · intro u hu
      exact pow_ne_zero 2 (hlog u hu).ne'
  have hm := intervalIntegral.integral_mono_on (μ := volume) hax
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / Real.log x ^ 2) volume a x)
    hc.intervalIntegrable (show ∀ u ∈ Set.Icc a x, 1 / Real.log x ^ 2 ≤ 1 / Real.log u ^ 2 by
      intro u hu
      have hl := Real.log_le_log (show 0 < u by linarith [hu.1]) hu.2
      apply one_div_le_one_div_of_le (sq_pos_of_pos (Real.log_pos (by linarith [hu.1])))
      exact pow_le_pow_left₀ (Real.log_nonneg (by linarith [hu.1])) hl 2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hm

/-- A trivial full interval estimate exceeds the p. 341 remainder budget.
This is a diagnostic of an estimate, not a counterexample to Proposition 1.4. -/
theorem trivial_integral_budget_too_large :
    0.1 * Real.sqrt ((10 : ℝ) ^ 40) * Real.log ((10 : ℝ) ^ 40) + 10 ^ 8 <
      ∫ u in ((10 : ℝ) ^ 20)..((10 : ℝ) ^ 40), 1 / Real.log u ^ 2 := by
  have hs : Real.sqrt ((10 : ℝ) ^ 40) = (10 : ℝ) ^ 20 := by
    rw [show (10 : ℝ) ^ 40 = ((10 : ℝ) ^ 20) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hl0 : 0 < Real.log ((10 : ℝ) ^ 40) := Real.log_pos (by norm_num)
  have hl : Real.log ((10 : ℝ) ^ 40) ≤ 100 := by
    rw [Real.log_pow, Real.log_ten_eq]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlo := logarithmic_integral_lower
    (by norm_num : (1 : ℝ) < 10 ^ 20) (by norm_num : (10 : ℝ) ^ 20 ≤ 10 ^ 40)
  rw [hs]
  apply lt_of_lt_of_le _ hlo
  rw [lt_div_iff₀ (sq_pos_of_pos hl0)]
  have hsqu : Real.log ((10 : ℝ) ^ 40) ^ 2 ≤ 10000 := by nlinarith
  have hm := mul_le_mul (show 0.1 * (10 : ℝ) ^ 20 * Real.log ((10 : ℝ) ^ 40) + 10 ^ 8 ≤
      0.1 * (10 : ℝ) ^ 20 * 100 + 10 ^ 8 by gcongr)
    hsqu (sq_nonneg _) (by positivity : 0 ≤ 0.1 * (10 : ℝ) ^ 20 * 100 + 10 ^ 8)
  norm_num at hm ⊢
  linarith

/-- The correct interior modulus range above its threshold, supporting pp. 340 to 341. -/
theorem modulus_range_above_threshold {q u : ℝ} (hq : 0 ≤ q)
    (hu : q ^ ((100 : ℝ) / 37) ≤ u) : q ≤ u ^ (0.37 : ℝ) := by
  calc
    q = (q ^ ((100 : ℝ) / 37)) ^ (0.37 : ℝ) := by
      rw [← Real.rpow_mul hq]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hq _) hu (by norm_num)

/-- The endpoint range puts the threshold below the endpoint, pp. 340 to 341. -/
theorem threshold_le_endpoint {q x : ℝ} (hx : 0 ≤ x)
    (hqx : q ≤ x ^ (0.37 : ℝ)) (hq : 0 ≤ q) :
    q ^ ((100 : ℝ) / 37) ≤ x := by
  calc
    _ ≤ (x ^ (0.37 : ℝ)) ^ ((100 : ℝ) / 37) :=
      Real.rpow_le_rpow hq hqx (by norm_num)
    _ = x := by rw [← Real.rpow_mul hx]; norm_num

/-- The range threshold can equal the endpoint, supporting the p. 341 range diagnostic. -/
theorem threshold_can_equal_endpoint :
    ∃ q : ℕ, ∃ x : ℝ, 10 ^ 9 ≤ x ∧ 1 ≤ q ∧
      (q : ℝ) ≤ x ^ (0.37 : ℝ) ∧ (q : ℝ) ^ ((100 : ℝ) / 37) = x := by
  refine ⟨10 ^ 37, (10 : ℝ) ^ 100, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  · norm_num only [Nat.cast_pow, Nat.cast_ofNat]

/-- The modulus one count is Mathlib primeCounting, supporting p. 341. -/
theorem piMod_one_eq_primeCounting (x : ℝ) (l : ℕ) :
    piMod x 1 l = Nat.primeCounting ⌊x⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  unfold piMod
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Iic, Nat.mod_one, and_true, Nat.mem_primesLE]

/-- The ordinary prime count Abel formula used for the p. 341 small modulus cases. -/
theorem ordinary_count_abel {x : ℝ} (hx : 2 ≤ x) (l : ℕ) :
    (piMod x 1 l : ℝ) = Chebyshev.theta x / Real.log x +
      ∫ u in (2 : ℝ)..x, Chebyshev.theta u / (u * Real.log u ^ 2) := by
  rw [piMod_one_eq_primeCounting]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-- Integrability of the ordinary theta error kernel used on p. 341. -/
theorem theta_error_kernel_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun u : ℝ => (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) volume 2 x := by
  have hi : IntervalIntegrable (fun u : ℝ => Chebyshev.theta u / (u * Real.log u ^ 2) -
      1 / Real.log u ^ 2) volume 2 x := by
    apply IntervalIntegrable.sub
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
    · exact (logarithmic_kernels hx).1
  apply hi.congr
  intro u hu
  have hu0 : u ≠ 0 := by
    rw [Set.uIoc_of_le hx] at hu
    linarith [hu.1]
  field_simp

/-- The ordinary prime count error after the p. 341 Li integration by parts. -/
theorem ordinary_centered_abel {x : ℝ} (hx : 2 ≤ x) (l : ℕ) :
    (piMod x 1 l : ℝ) - zinLi x = (Chebyshev.theta x - x) / Real.log x +
      (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) +
      2 / Real.log 2 := by
  have hi : (∫ u in (2 : ℝ)..x, (Chebyshev.theta u - u) / (u * Real.log u ^ 2)) =
      (∫ u in (2 : ℝ)..x, Chebyshev.theta u / (u * Real.log u ^ 2)) -
      (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) := by
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : u ≠ 0 := by
        rw [Set.uIcc_of_le hx] at hu
        linarith [hu.1]
      field_simp
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
      exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
    · exact (logarithmic_kernels hx).1
  rw [hi, ordinary_count_abel hx, zinLi_by_parts hx]
  ring

/-- A supporting elementary lower interval estimate for the p. 341 small modulus proof. -/
theorem theta_error_integral_trivial {x : ℝ} (hx : 2 ≤ x) :
    (∫ u in (2 : ℝ)..x, |Chebyshev.theta u - u| / (u * Real.log u ^ 2)) ≤ 3 * (x - 2) := by
  have hden : ∀ u ∈ Set.uIcc (2 : ℝ) x, 0 < u * Real.log u ^ 2 := by
    intro u hu
    rw [Set.uIcc_of_le hx] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hlog : 0 < Real.log u := Real.log_pos (by linarith [hu.1])
    positivity
  have hi : IntervalIntegrable
      (fun u : ℝ => |Chebyshev.theta u - u| / (u * Real.log u ^ 2)) volume 2 x := by
    have hh := (theta_error_kernel_integrable hx).norm
    apply hh.congr
    intro u hu
    dsimp only
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hden u (by
      rw [Set.uIcc_of_le hx]
      rw [Set.uIoc_of_le hx] at hu
      exact ⟨hu.1.le, hu.2⟩))]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hx hi intervalIntegrable_const
    (show ∀ u ∈ Set.Icc (2 : ℝ) x,
      |Chebyshev.theta u - u| / (u * Real.log u ^ 2) ≤ (3 : ℝ) by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hlog : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu.1
      have hlog0 : 0 < Real.log u := by linarith [Real.log_two_gt_d9]
      have ht : Chebyshev.theta u ≤ 2 * u := by
        apply (Chebyshev.theta_le_log4_mul_x hu0.le).trans
        have hl4 : Real.log (4 : ℝ) ≤ 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
          norm_num only [Nat.cast_ofNat]
          linarith [Real.log_two_lt_d9]
        exact mul_le_mul_of_nonneg_right hl4 hu0.le
      have he : |Chebyshev.theta u - u| ≤ u := by
        rw [abs_le]
        constructor <;> linarith [Chebyshev.theta_nonneg u]
      calc
        _ ≤ u / (u * Real.log u ^ 2) :=
          div_le_div_of_nonneg_right he (hden u (by rwa [Set.uIcc_of_le hx])).le
        _ = 1 / Real.log u ^ 2 := by field_simp
        _ ≤ 3 := by
          rw [div_le_iff₀ (sq_pos_of_pos hlog0)]
          nlinarith [Real.log_two_gt_d9])
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hm

end LeanLab.Zinoviev1997.Decomp575b
