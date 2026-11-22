/-
DQ4 decisions for BhowmikGrimmelt2026, design queue item DQ4, run 20261118T0802Z-4078.
Source: P0029 pages 11, 12, 15, 18 and 20.

Part A. The two cited route steps `primitive_psi_zero_expansion508` and
`oscillatory_zero_modes508` of Decomp508a are accepted as NAMED HYPOTHESES.
The route conclusion, the major arc estimate of `major_arc_partial_summation504`,
is proved below from them as explicit hypothesis arguments, together with the
proved Hardy critical line zero. CONDITIONAL, never PROVED.
Two match theorems check that the named hypotheses are exactly the sealed statements.

Part B. `Prop52`, the lab transcription of Proposition 5.2 on P0029 page 18, is FALSE.
At R equal to N the normalisation N over R is one, and the one point interval at a
large prime p gives the modulus one character the value log p minus at most two, while
the right side is at most the absolute value of C. `not_prop52_dq4` proves this with
no unproved step. Every theorem that takes `h52 : Prop52` is therefore vacuous.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SharpArc673

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-! ## Part A. Named hypotheses for the two cited route steps -/

/-- Named hypothesis, the conclusion of `primitive_psi_zero_expansion508`, P0029 page 11
display 3.5, the sharp primitive character explicit formula. CITED. -/
def PrimitivePsiZeroExpansionDQ4 : Prop :=
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2

/-- Named hypothesis, the conclusion of `oscillatory_zero_modes508` at the exponent Θ,
P0029 pages 11, 12 and 15 display 4.6, uniform control of the finite sharp zero modes. CITED. -/
def OscillatoryZeroModesDQ4 (Θ : ℝ) : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ (q : ℕ) [NeZero q], q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
          ‖zeroTwist508 χ Z X β‖ ≤
            C * (X : ℝ) ^ (Θ + ε) * Real.sqrt (1 + |β| * X)

/-- Match check: the named hypothesis is exactly the sealed statement of
`primitive_psi_zero_expansion508`. Depends on the sealed open leaf and only checks the match. -/
theorem primitive_named_match_dq4 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    PrimitivePsiZeroExpansionDQ4 :=
  primitive_psi_zero_expansion508 Θ hΘ hZ

/-- Match check: the named hypothesis is exactly the sealed statement of
`oscillatory_zero_modes508`. Depends on the sealed open leaf and only checks the match. -/
theorem oscillatory_named_match_dq4 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    OscillatoryZeroModesDQ4 Θ :=
  oscillatory_zero_modes508 Θ hΘ hZ

/-- P0029 page 11 display 3.5 for every character, CONDITIONAL on the named hypothesis
`PrimitivePsiZeroExpansionDQ4`. Same proof as `psi_zero_expansion504`. -/
theorem psi_zero_expansion_of_named_dq4 (hprim : PrimitivePsiZeroExpansionDQ4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, hC, hprimitive⟩ := hprim
  refine ⟨C + 1 / Real.log 2, by positivity, ?_⟩
  intro X hX q _ hq χ
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hd := χ.conductor_dvd_level
  have hr : χ.conductor ≤ Nat.sqrt X :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hd).trans hq
  obtain ⟨T, hT, Z, hmem, hbound⟩ := hprimitive X hX χ.conductor hr
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  have hz (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
      DirichletCharacter.LFunction χ ρ = 0 ↔
        DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      character_zero_changeLevel508 hd χ.primitiveCharacter h0 h1
  have hm (ρ : ℂ) (hρ : ρ ∈ Z) : mult χ ρ = mult χ.primitiveCharacter ρ := by
    have hh := (hmem ρ).mp hρ
    simpa only [χ.changeLevel_primitiveCharacter] using
      character_mult_changeLevel508 hd χ.primitiveCharacter hh.2.1 hh.2.2.1
  have hmain : χ = 1 ↔ χ.primitiveCharacter = 1 := by
    simpa only [χ.changeLevel_primitiveCharacter] using
      (DirichletCharacter.changeLevel_eq_one_iff (χ := χ.primitiveCharacter) hd)
  refine ⟨T, hT, Z, ?_, ?_⟩
  · intro ρ
    rw [hmem]
    constructor
    · rintro ⟨hL, h0, h1, hT'⟩
      exact ⟨(hz ρ h0 h1).mpr hL, h0, h1, hT'⟩
    · rintro ⟨hL, h0, h1, hT'⟩
      exact ⟨(hz ρ h0 h1).mp hL, h0, h1, hT'⟩
  · intro n hn hnX
    have hmode : (∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ) =
        ∑ ρ ∈ Z, (mult χ.primitiveCharacter ρ : ℂ) * (n : ℂ) ^ ρ / ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hm ρ hρ]
    have he :
        (∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
        (if χ = 1 then (n : ℂ) else 0) +
        ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ =
        ((∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
          ∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor)) +
        ((∑ m ∈ Finset.range (n + 1),
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ.primitiveCharacter (m : ZMod χ.conductor)) -
        (if χ.primitiveCharacter = 1 then (n : ℂ) else 0) +
        ∑ ρ ∈ Z, (mult χ.primitiveCharacter ρ : ℂ) * (n : ℂ) ^ ρ / ρ) := by
      rw [hmode]
      have hmainval : (if χ = 1 then (n : ℂ) else 0) =
          (if χ.primitiveCharacter = 1 then (n : ℂ) else 0) := by
        by_cases hc : χ = 1
        · simp only [hc, hmain.mp hc, ite_true]
        · simp only [hc, hmain.not.mp hc, ite_false]
      rw [hmainval]
      ring
    have hdiff := psi_changeLevel_bound508 hd χ.primitiveCharacter n X
      (Nat.pos_of_ne_zero (NeZero.ne q)) hn hnX (hq.trans (Nat.sqrt_le_self X))
    rw [χ.changeLevel_primitiveCharacter] at hdiff
    rw [he]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ Real.log X ^ 2 / Real.log 2 + C * Real.log X ^ 2 :=
        add_le_add hdiff (hbound n hn hnX)
      _ = _ := by ring

/-- P0029 pages 11 and 12, the rational arc estimate, CONDITIONAL on the named hypothesis
`OscillatoryZeroModesDQ4 Θ`, on one half at most Θ and on the all character explicit formula.
Same proof as `sharp_rational_arc508` with the cited inputs made explicit. -/
theorem sharp_rational_arc_of_named_dq4 (Θ : ℝ) (hhalf : 1 / 2 ≤ Θ)
    (hosc : OscillatoryZeroModesDQ4 Θ)
    (hpsi : ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q,
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt X → ∀ a : ℕ, Nat.Coprime a q →
      ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) →
        ‖Ssum X ((a : ℝ) / q + β) -
          ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β‖ ≤
        C * (X : ℝ) ^ (Θ + ε) *
          (Real.sqrt q * Real.sqrt (1 + |β| * X)) := by
  classical
  intro ε hε
  obtain ⟨Cψ, hCψ, hψ⟩ := hpsi
  obtain ⟨Cz, hCz, hz⟩ := hosc ε hε
  let K : ℝ := (2 / ε) ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 10 * Real.pi * Cψ * K
  let E : ℝ := K / Real.log 2
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCψ) hK
  have hE : 0 ≤ E := div_nonneg hK hL.le
  refine ⟨Cz + A + E, by positivity, ?_⟩
  intro X hX q hq hqQ a ha β hβ
  haveI : NeZero q := ⟨by omega⟩
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hxp : 0 < (X : ℝ) := lt_of_lt_of_le zero_lt_one hx
  let W : ℝ := (X : ℝ) ^ (Θ + ε)
  let F : ℝ := Real.sqrt q * Real.sqrt (1 + |β| * X)
  have hW : 0 ≤ W := Real.rpow_nonneg hxp.le _
  have hF : 1 ≤ F := by
    have hsq : (1 : ℝ) ≤ Real.sqrt q := Real.le_sqrt_of_sq_le (by
      norm_num
      exact_mod_cast hq)
    have hsf : (1 : ℝ) ≤ Real.sqrt (1 + |β| * X) :=
      Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (abs_nonneg β) (Nat.cast_nonneg X)])
    dsimp [F]
    nlinarith
  have hWF : W ≤ W * F := by nlinarith
  have hrem : Real.sqrt X * Real.log X ^ 2 ≤ K * W :=
    sqrt_log_power_budget508 hx hhalf hε
  have hlog : Real.log X ^ 2 ≤ K * W :=
    (log_sq_power_budget508 hx hε).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hK)
  have hunit : IsUnit ((a : ℤ) : ZMod q) := by
    simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime a q).mpr ha
  have hb := sharp_rational_mode_reduction508 (a : ℤ) hunit
    (by omega : 1 ≤ X) hq hqQ hβ (mul_nonneg hCψ (sq_nonneg (Real.log X)))
    (mul_nonneg (mul_nonneg hCz hW) (Real.sqrt_nonneg (1 + |β| * X))) (by
      intro χ
      obtain ⟨T, hT, Z, hspec, hr⟩ := hψ X hX q hqQ χ
      refine ⟨Z, ?_, hz X hX q hqQ χ T hT Z hspec β hβ⟩
      intro n hnX
      by_cases hn : n = 0
      · rw [hn, sharp_remainder_zero508 χ Z (fun ρ hρ => ((hspec ρ).mp hρ).2.1)]
        simpa only [norm_zero] using mul_nonneg hCψ (sq_nonneg (Real.log X))
      · simpa only [sharpRemainder508, psiCharacter502, zeroPartial508, mul_div_assoc] using
          hr n (by omega) hnX)
  have hrb : 10 * Real.pi * (Cψ * Real.log X ^ 2) * Real.sqrt X ≤ A * (W * F) := by
    calc
      _ = (10 * Real.pi * Cψ) * (Real.sqrt X * Real.log X ^ 2) := by ring
      _ ≤ (10 * Real.pi * Cψ) * (K * W) := mul_le_mul_of_nonneg_left hrem
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hCψ)
      _ = A * W := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWF hA
  have hlb : Real.log X ^ 2 / Real.log 2 ≤ E * (W * F) := by
    calc
      _ ≤ (K * W) / Real.log 2 := div_le_div_of_nonneg_right hlog hL.le
      _ = E * W := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWF hE
  have hc : Real.sqrt q * (Cz * W * Real.sqrt (1 + |β| * X)) = Cz * (W * F) := by
    dsimp [F]
    ring
  change _ ≤ (Cz + A + E) * W * F
  convert hb.trans (add_le_add (add_le_add (le_of_eq hc) hrb) hlb) using 1
  ring

/-- DQ4 route conclusion. P0029 pages 11 and 12, the major arc estimate of
`major_arc_partial_summation504`: for every positive ε there is C with
the norm of S minus V at most C times X to the Θ plus one quarter plus ε, uniformly in α.
CONDITIONAL on the two named cited hypotheses `PrimitivePsiZeroExpansionDQ4`
and `OscillatoryZeroModesDQ4 Θ`, and on `ZeroBound Θ`. The bound one half at most Θ comes from
the proved `zeroBound_lower150`, whose Hardy input is now proved in Decomp515a.
Same assembly as `major_arc_partial_summation504`. -/
theorem major_arc_route_of_named_dq4 (Θ : ℝ) (hZ : ZeroBound Θ)
    (hprim : PrimitivePsiZeroExpansionDQ4)
    (hosc : OscillatoryZeroModesDQ4 Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖Ssum X α - VX150 X α‖ ≤ C * (X : ℝ) ^ (Θ + 1 / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC, hlocal⟩ := sharp_rational_arc_of_named_dq4 Θ
    (zeroBound_lower150 hZ) hosc
    (psi_zero_expansion_of_named_dq4 hprim) ε hε
  refine ⟨C * Real.sqrt 5, ?_⟩
  intro X hX α hα
  obtain ⟨q, hq, hαq⟩ := exists_arc502 (by omega : 1 ≤ X) α
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hqQ := (Finset.mem_Icc.mp hq).2
  haveI : NeZero q := ⟨by omega⟩
  let a : ℕ := (nint150 ((q : ℝ) * α)).toNat
  let β : ℝ := α - (a : ℝ) / q
  have haZ : (a : ℤ) = nint150 ((q : ℝ) * α) :=
    Int.toNat_of_nonneg (nint_mem150 (q := q) hα).1
  have har : (a : ℝ) = (nint150 ((q : ℝ) * α) : ℝ) := by exact_mod_cast haZ
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq1
  have hβq : (q : ℝ) * |β| = |(q : ℝ) * α - nint150 ((q : ℝ) * α)| := by
    calc
      _ = |(q : ℝ) * β| := by rw [abs_mul, abs_of_pos hqp]
      _ = _ := by
        congr 1
        dsimp [β]
        rw [har]
        field_simp
  have hb1 : |β| ≤ (1 / (Nat.sqrt X : ℝ)) / q :=
    (le_div_iff₀ hqp).mpr (by rw [mul_comm, hβq]; exact hαq.1)
  have hβ : |β| ≤ 1 / ((q : ℝ) * Nat.sqrt X) := by
    simpa only [div_div, mul_comm] using hb1
  have hcop : Nat.Coprime a q := assigned_coprime504 hq1 hα hαq
  have hV : VX150 X α =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) * TX150 X β := by
    rw [VX_eq_arcTerm502 hq hαq]
    change ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ) *
      TX150 X (α - (nint150 ((q : ℝ) * α) : ℝ) / q) = _
    rw [← har]
  have hh := hlocal X hX q hq1 hqQ a hcop β hβ
  have hαeq : (a : ℝ) / q + β = α := by dsimp [β]; ring
  rw [hαeq] at hh
  rw [hV]
  calc
    _ ≤ C * (X : ℝ) ^ (Θ + ε) *
        (Real.sqrt q * Real.sqrt (1 + |β| * X)) := hh
    _ ≤ C * (X : ℝ) ^ (Θ + ε) *
        (Real.sqrt 5 * (X : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (gauss_arc_scale508 (by omega) hq1 hqQ hβ) (by positivity)
    _ = _ := by
      have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
      have he : (X : ℝ) ^ (Θ + 1 / 4 + ε) =
          (X : ℝ) ^ (Θ + ε) * (X : ℝ) ^ (1 / 4 : ℝ) := by
        rw [show Θ + 1 / 4 + ε = (Θ + ε) + 1 / 4 by ring, Real.rpow_add hxp]
      rw [he]
      ring

/-! ## Part B. Prop52 is false at R equal to N -/

section PartB

attribute [local instance] Classical.propDecidable

/-- The interval maximum is nonnegative for a nonnegative level. -/
theorem intervalMax_nonneg_dq4 (N : ℕ) {R : ℝ} (hR : 0 ≤ R) (f : ℕ → ℂ) :
    0 ≤ intervalMax N R f := by
  unfold intervalMax
  exact Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => Real.iSup_nonneg fun h =>
    div_nonneg (norm_nonneg _)
      (add_nonneg (by linarith [h.2.1]) (div_nonneg (Nat.cast_nonneg _) hR))

/-- At level R equal to N the one point interval at p gives the norm of f at p. -/
theorem intervalMax_ge_point_dq4 {N p : ℕ} (hp1 : 1 ≤ p) (hpN : p ≤ N) (f : ℕ → ℂ) :
    ‖f p‖ ≤ intervalMax N (N : ℝ) f := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNR : (N : ℝ) / (N : ℝ) = 1 := div_self hN.ne'
  set S : ℝ := ∑ n ∈ Finset.range (N + 1), ‖f n‖ with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hg : ∀ x y : ℝ, (1 ≤ x ∧ x ≤ y ∧ y ≤ N) →
      ‖∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, f n‖ / ((y - x) + (N : ℝ) / N) ≤ S := by
    rintro x y ⟨hx, hxy, hy⟩
    rw [hNR]
    have hden : 1 ≤ (y - x) + 1 := by linarith
    have hfl : ⌊y⌋₊ ≤ N := Nat.floor_le_of_le hy
    calc _ ≤ ‖∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, f n‖ := div_le_self (norm_nonneg _) hden
      _ ≤ ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊y⌋₊, ‖f n‖ := norm_sum_le _ _
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega) (fun _ _ _ => norm_nonneg _)
  have hval : ‖f p‖ = ‖∑ n ∈ Finset.Icc ⌈(p : ℝ)⌉₊ ⌊(p : ℝ)⌋₊, f n‖ /
      (((p : ℝ) - p) + (N : ℝ) / N) := by
    rw [Nat.ceil_natCast, Nat.floor_natCast, Finset.Icc_self, Finset.sum_singleton, hNR,
      sub_self, zero_add, div_one]
  have hP : (1 ≤ (p : ℝ) ∧ (p : ℝ) ≤ p ∧ (p : ℝ) ≤ N) :=
    ⟨by exact_mod_cast hp1, le_rfl, by exact_mod_cast hpN⟩
  rw [hval]
  unfold intervalMax
  refine le_ciSup_of_le ?_ (p : ℝ) ?_
  · exact ⟨S, Set.forall_mem_range.2 fun x =>
      Real.iSup_le (fun y => Real.iSup_le (fun h => hg _ _ h) hS) hS⟩
  refine le_ciSup_of_le ?_ (p : ℝ) ?_
  · exact ⟨S, Set.forall_mem_range.2 fun y => Real.iSup_le (fun h => hg _ _ h) hS⟩
  refine le_ciSup_of_le ?_ hP le_rfl
  exact ⟨_, Set.forall_mem_range.2 fun _ => le_rfl⟩

/-- The primitive character sum dominates its modulus one term when the summands are
nonnegative and the level is at least one. -/
theorem primSum_ge_modOne_dq4 {R : ℝ} (hR : 1 ≤ R)
    (F : ∀ r : ℕ, [NeZero r] → DirichletCharacter ℂ r → ℝ)
    (hF : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), 0 ≤ F r χ) :
    F (0 + 1) (1 : DirichletCharacter ℂ (0 + 1)) ≤ primSum R F := by
  unfold primSum
  have h0 : 0 ∈ Finset.range ⌊R⌋₊ := Finset.mem_range.mpr (Nat.floor_pos.mpr hR)
  have hterm : ∀ (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)),
      0 ≤ (if χ.IsPrimitive then F (r + 1) χ else 0) := by
    intro r χ
    split_ifs
    · exact hF _ _
    · exact le_rfl
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun r => ∑ χ : DirichletCharacter ℂ (r + 1),
      if χ.IsPrimitive then F (r + 1) χ else 0)
    (fun r _ => Finset.sum_nonneg fun χ _ => hterm r χ) h0)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun χ : DirichletCharacter ℂ (0 + 1) => if χ.IsPrimitive then F (0 + 1) χ else 0)
    (fun χ _ => hterm 0 χ) (Finset.mem_univ (1 : DirichletCharacter ℂ (0 + 1))))
  rw [ite_eq_left DirichletCharacter.isPrimitive_one_level_one]

/-- The modulus one character takes the value one at every natural number. -/
theorem modOne_char_apply_dq4 (χ : DirichletCharacter ℂ (0 + 1)) (n : ℕ) :
    χ (n : ZMod (0 + 1)) = 1 := by
  have : Subsingleton (ZMod (0 + 1)) := (inferInstance : Subsingleton (Fin 1))
  have h : (n : ZMod (0 + 1)) = 1 := Subsingleton.elim _ _
  rw [h, map_one]

/-- The one point value at a prime p is at least log p minus two after two unit size
perturbations, when the character value u is one. -/
theorem point_value_ge_dq4 {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : u = 1) (a b : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    Real.log p - 2 ≤ ‖(vonMangoldt p : ℂ) * u - a + b‖ := by
  subst hu
  have hΛ : ‖(vonMangoldt p : ℂ) * 1‖ = Real.log p := by
    rw [mul_one, vonMangoldt_apply_prime hp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
  have htri : ‖(vonMangoldt p : ℂ) * 1‖ ≤ ‖(vonMangoldt p : ℂ) * 1 - a + b‖ + ‖a‖ + ‖b‖ := by
    have he : (vonMangoldt p : ℂ) * 1 = ((vonMangoldt p : ℂ) * 1 - a + b) + a - b := by ring
    calc ‖(vonMangoldt p : ℂ) * 1‖ = ‖((vonMangoldt p : ℂ) * 1 - a + b) + a - b‖ := by
          rw [← he]
      _ ≤ ‖((vonMangoldt p : ℂ) * 1 - a + b) + a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [norm_add_le ((vonMangoldt p : ℂ) * 1 - a + b) a]
  linarith

/-- The same bound with only the principal perturbation. -/
theorem point_value_ge'_dq4 {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : u = 1) (a : ℂ)
    (ha : ‖a‖ ≤ 1) :
    Real.log p - 2 ≤ ‖(vonMangoldt p : ℂ) * u - a‖ := by
  have h := point_value_ge_dq4 hp hu a 0 ha (by simp)
  rwa [add_zero] at h

/-- FALSE: `Prop52`, the lab transcription of Proposition 5.2 on P0029 page 18, is refuted.
At R equal to N the term N over R in the denominator is one, so the one point interval at a
prime p already gives the modulus one character the value log p minus at most two, while
both parts of Prop52 bound the whole sum by the absolute value of C. PROVED, no open step. -/
theorem not_prop52_dq4 : ¬ Prop52 := by
  rintro ⟨c, hc, C, hC⟩
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (⌈Real.exp (|C| + 3)⌉₊)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR : Real.exp (|C| + 3) ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpge)
  have hlogp : |C| + 3 ≤ Real.log p := by
    have h := Real.log_le_log (Real.exp_pos _) hpR
    rwa [Real.log_exp] at h
  have hC0 := abs_nonneg C
  have hlog1 : 1 ≤ Real.log p := by linarith
  have hlogpos : 0 < Real.log p := by linarith
  have hsq1 : 1 ≤ Real.sqrt (Real.log p) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqle : Real.sqrt (Real.log p) ≤ Real.log p :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hcond1 : 2 ≤ Real.exp (Real.sqrt (Real.log p)) := by
    have h1 := Real.add_one_le_exp (1 : ℝ)
    have h2 := Real.exp_le_exp.mpr hsq1
    linarith
  have hcond2 : Real.exp (Real.sqrt (Real.log p)) ≤ (p : ℝ) := by
    calc Real.exp (Real.sqrt (Real.log p)) ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr hsqle
      _ = p := Real.exp_log hp0
  obtain ⟨h1, h2⟩ := hC p (p : ℝ) hcond1 hcond2 le_rfl
  have hR1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hexp : Real.exp (-c * Real.log p / Real.log p) ≤ 1 := by
    rw [mul_div_assoc, div_self hlogpos.ne', mul_one, Real.exp_le_one_iff]
    linarith
  have hexp0 := Real.exp_pos (-c * Real.log p / Real.log p)
  by_cases hs : ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      SiegelZero (p : ℝ) r χ β
  · obtain ⟨r₀, hr₀, χ₀, β, hsz⟩ := hs
    have hup := h2 r₀ χ₀ β hsz
    obtain ⟨_, _, _, hβlo, hβhi, _⟩ := hsz
    have hb1 : (1 - β) * Real.log p ≤ 1 := by
      have h := mul_lt_mul_of_pos_right (show 1 - β < 1 / Real.log p by linarith) hlogpos
      rw [one_div_mul_cancel hlogpos.ne'] at h
      linarith
    have hb0 : 0 ≤ (1 - β) * Real.log p := mul_nonneg (by linarith) hlogpos.le
    have hrhs : C * (1 - β) * Real.log p * Real.exp (-c * Real.log p / Real.log p) ≤ |C| := by
      have hk0 : 0 ≤ (1 - β) * Real.log p * Real.exp (-c * Real.log p / Real.log p) :=
        mul_nonneg hb0 hexp0.le
      have hk1 : (1 - β) * Real.log p * Real.exp (-c * Real.log p / Real.log p) ≤ 1 := by
        nlinarith
      calc C * (1 - β) * Real.log p * Real.exp (-c * Real.log p / Real.log p)
          = C * ((1 - β) * Real.log p * Real.exp (-c * Real.log p / Real.log p)) := by ring
        _ ≤ |C| * ((1 - β) * Real.log p * Real.exp (-c * Real.log p / Real.log p)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hk0
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hk1 hC0
        _ = |C| := mul_one _
    have hlow := primSum_ge_modOne_dq4 hR1 (hF := fun r _ χ => intervalMax_nonneg_dq4 p hp0.le _)
      (F := fun r _ χ => intervalMax p (p : ℝ)
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0)))
    have hpt := intervalMax_ge_point_dq4 (N := p) (p := p) hp.one_lt.le le_rfl
      (fun n => (vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ (0 + 1)) n -
        (if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then 1 else 0) +
          (if 0 + 1 = r₀ ∧ HEq (1 : DirichletCharacter ℂ (0 + 1)) χ₀ then
            (n : ℂ) ^ ((β : ℂ) - 1) else 0))
    have hval := point_value_ge_dq4 hp (modOne_char_apply_dq4 1 p)
      (if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then (1 : ℂ) else 0)
      (if 0 + 1 = r₀ ∧ HEq (1 : DirichletCharacter ℂ (0 + 1)) χ₀ then
        (p : ℂ) ^ ((β : ℂ) - 1) else 0)
      (by split_ifs <;> simp)
      (by
        split_ifs
        · rw [Complex.norm_natCast_cpow_of_pos hp.pos]
          apply Real.rpow_le_one_of_one_le_of_nonpos hR1
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
          linarith
        · simp)
    have hchain := hval.trans (hpt.trans (hlow.trans hup))
    linarith
  · have hup := h1 hs
    have hrhs : C * Real.exp (-c * Real.log p / Real.log p) ≤ |C| := by
      calc C * Real.exp (-c * Real.log p / Real.log p)
          ≤ |C| * Real.exp (-c * Real.log p / Real.log p) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) hexp0.le
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hexp hC0
        _ = |C| := mul_one _
    have hlow := primSum_ge_modOne_dq4 hR1 (hF := fun r _ χ => intervalMax_nonneg_dq4 p hp0.le _)
      (F := fun _ _ χ => intervalMax p (p : ℝ)
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0))
    have hpt := intervalMax_ge_point_dq4 (N := p) (p := p) hp.one_lt.le le_rfl
      (fun n => (vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ (0 + 1)) n -
        if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then 1 else 0)
    have hval := point_value_ge'_dq4 hp (modOne_char_apply_dq4 1 p)
      (if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then (1 : ℂ) else 0)
      (by split_ifs <;> simp)
    have hchain := hval.trans (hpt.trans (hlow.trans hup))
    linarith

/-- Consequence: every theorem with a hypothesis `h52 : Prop52` is vacuous. Example:
the hypotheses of `mv_no_siegel150` can never all hold. -/
theorem h52_vacuous_dq4 (h52 : Prop52) : False := not_prop52_dq4 h52

end PartB

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.primitive_named_match_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.oscillatory_named_match_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.zeroBound_lower150
#print axioms LeanLab.BhowmikGrimmelt2026.psi_zero_expansion_of_named_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.sharp_rational_arc_of_named_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.major_arc_route_of_named_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.intervalMax_nonneg_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.intervalMax_ge_point_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.primSum_ge_modOne_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.modOne_char_apply_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.point_value_ge_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.point_value_ge'_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.not_prop52_dq4
#print axioms LeanLab.BhowmikGrimmelt2026.h52_vacuous_dq4
