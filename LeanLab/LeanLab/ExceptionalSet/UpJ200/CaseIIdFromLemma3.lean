/-
ROUTE for burst-20261122 unit caseIId_lemma3, session S67.
P0082, Bruedern and Perelli 1998, Ann. Inst. Fourier 48, pages 353 to 378,
https://doi.org/10.5802/aif.1621. Lemma 3 on page 358, displays 12 and 13 on
page 359, case ii b and ii d on pages 363 and 364.

`DQCaseIIdSplit.caseIIdMajorLowerHyp_of_leaves` proves the named hypothesis
`DQLeafNearZeroSelected.CaseIIdMajorLowerHyp` from the LEAF
`DQCaseIIdSplit.leaf_bp_lemma3_shared`. This file derives that leaf's exact
statement from the named citation wall `DQCaseIIbP0082.BPLemma3Hyp`:
* `tildeS_eq_twistedSing`: the two formalizations of display 12 are equal; both take
  the real part of `χ~(-1)`, and they differ only in the order of the gcd arguments.
* `tildeI_eq_Itilde`: the two formalizations of display 13 are equal.
* the middle error term of display 20 vanishes since `χ~(m) = 0` when
  `(m, r~) > 1`, `DQCaseIIbP0082.char_vanishes`, page 363 case ii b.
Then `caseIIdMajorLowerHyp_of_lemma3` is the proof of
`caseIIdMajorLowerHyp_of_leaves` copied word for word with the leaf replaced.
CONDITIONAL ON `BPLemma3Hyp`; no sorry.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit
import LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082

namespace LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected (CaseIIdMajorLowerHyp)
open LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082 (BPLemma3Hyp char_vanishes)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde)
open LeanLab.ExceptionalSet.UpJ200.DQCaseIIdSplit

/-- P0082 page 359 display 12: the two formalizations `DQCaseIIdSplit.tildeS` and
`DQDisplay21P0082.twistedSing` of the modified singular series agree for every
character and every `m`. PROVED. -/
theorem tildeS_eq_twistedSing {r : ℕ} (χ : DirichletCharacter ℂ r) (m : ℤ) :
    tildeS χ m = twistedSing χ m := by
  have hg : Nat.gcd r m.natAbs = Int.gcd m r := by
    show Nat.gcd r m.natAbs = Nat.gcd m.natAbs (r : ℤ).natAbs
    rw [Int.natAbs_natCast, Nat.gcd_comm]
  unfold tildeS twistedSing DQDisplay21P0082.singFactor
  rw [hg]

/-- P0082 page 359 display 13: the two formalizations `DQCaseIIdSplit.tildeI` and
`DQDisplay21P0082.Itilde` of the sum `I~(m)` agree. PROVED. -/
theorem tildeI_eq_Itilde (β P : ℝ) (m : ℤ) : tildeI β P m = Itilde β P m := by
  unfold tildeI Itilde
  congr 1

/-- P0082 page 358 Lemma 3, display 20 on page 363, for even `m` with `(m, r~) > 1`:
the exact statement of the LEAF `DQCaseIIdSplit.leaf_bp_lemma3_shared`, derived from
`BPLemma3Hyp`. The middle error term vanishes by `char_vanishes`, page 363 case ii b.
CONDITIONAL ON `BPLemma3Hyp`. -/
theorem bp_lemma3_shared_of_lemma3 (hL3 : BPLemma3Hyp) :
    ∀ a : ℝ, 0 < a → ∃ C c₂ : ℝ, 0 < C ∧ 0 < c₂ ∧
      ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
      ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
      ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
        χ.LFunction β = 0 →
        ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m → 1 < Int.gcd m r →
          |(R1 (X ^ θ) X m).re - ((m : ℝ) * singSeries m + tildeI β (X ^ θ) m * tildeS χ m)| ≤
            C * X * divisorError r (X ^ θ) m +
            C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
              Real.exp (-(c₂ / θ)) * Real.log (X ^ θ) := by
  intro a ha
  obtain ⟨C, c₂, hC, hc₂, hL⟩ := hL3 a ha
  refine ⟨C, c₂, hC, hc₂, ?_⟩
  intro θ hθ hθ1
  obtain ⟨P₀, hP⟩ := hL θ hθ hθ1
  refine ⟨P₀, ?_⟩
  intro X hX hPX r hr hr1 hrX hsel hnz χ β hp hsq hne hβlo hβ1 hz m hm hmX hev hgcd
  have hb := hP X hX hPX r hr hr1 hrX hsel hnz χ β hp hsq hne hβlo hβ1 hz m hm hmX hev
  have hχm : χ (m : ZMod r) = 0 := char_vanishes χ m (by omega) hgcd
  rw [hχm, norm_zero] at hb
  rw [tildeI_eq_Itilde, tildeS_eq_twistedSing]
  have hz0 : C * X * (0 : ℝ) ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
      ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) = 0 := by ring
  rw [hz0, add_zero] at hb
  exact hb

/-- P0082 page 364 case ii d. The exact named hypothesis
`DQLeafNearZeroSelected.CaseIIdMajorLowerHyp`, CONDITIONAL ON `BPLemma3Hyp`. The proof of
`DQCaseIIdSplit.caseIIdMajorLowerHyp_of_leaves` copied word for word, with the LEAF
`leaf_bp_lemma3_shared` replaced by `bp_lemma3_shared_of_lemma3 hL3`. -/
theorem caseIIdMajorLowerHyp_of_lemma3 (hL3 : BPLemma3Hyp) : CaseIIdMajorLowerHyp := by
  intro γ h1 h2 a ha
  obtain ⟨C, c₂, hC, hc₂, hL3θ⟩ := bp_lemma3_shared_of_lemma3 hL3 a ha
  obtain ⟨c₀, hc₀, hS⟩ := LeanLab.ExceptionalSet.Task672.singSeriesLowerHyp_proved672
  set K : ℝ := 4 * C * Real.exp a / c₀ with hK
  have hKpos : 0 < K := by positivity
  refine ⟨min (1 / 100) (c₂ / (6 * (|Real.log K| + 1))), lt_min (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδlt
  have hδ1 : δ < 1 / 100 := (lt_min_iff.mp hδlt).1
  have hδ2 : δ < c₂ / (6 * (|Real.log K| + 1)) := (lt_min_iff.mp hδlt).2
  have hθ : (6 * δ : ℝ) < 6 / 100 := by linarith
  obtain ⟨P₀, hL3⟩ := hL3θ (6 * δ) (by positivity) hθ
  refine ⟨c₀ * Real.exp (-a) / 4, C, by positivity, hC, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  have hQ : Tendsto (fun N : ℕ => F γ N ^ (1 - 6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - 6 * δ)).comp hF
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hP.eventually_ge_atTop (max P₀ 2)).and (hQ.eventually_ge_atTop 2))
  refine ⟨N₀, ?_⟩
  intro N hN r hr hrP hsel m hev hlow hle hgcd hprod hrz χ β hp hreal hne hβ0 hβlo hβ1 hz
  obtain ⟨hPN, hQN⟩ := hN₀ N hN
  have hX : 0 < F γ N := Real.exp_pos _
  have hP2 : 2 ≤ F γ N ^ (6 * δ) := le_trans (le_max_right _ _) hPN
  have hPP₀ : P₀ ≤ F γ N ^ (6 * δ) := le_trans (le_max_left _ _) hPN
  have hsplit : F γ N = F γ N ^ (6 * δ) * F γ N ^ (1 - 6 * δ) := by
    rw [← Real.rpow_add hX]; simp
  have hPX : F γ N ^ (6 * δ) ≤ F γ N / 2 := by
    have hPpos : 0 ≤ F γ N ^ (6 * δ) := by linarith
    have := mul_le_mul_of_nonneg_left hQN hPpos
    rw [← hsplit] at this; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hm1 : 1 ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hmpos
    omega
  have hr1 : r ≠ 1 := by
    rintro rfl; simp at hgcd
  have hbound := hL3 (F γ N) hX hPP₀ r hr hr1 hrP hsel hrz χ β hp
    hreal hne hβlo hβ1 hz m hm1 hle hev hgcd
  have := hrz
  set X := F γ N with hXdef
  set P := X ^ (6 * δ) with hPdef
  set M : ℝ := (m.toNat : ℝ) / (m.toNat.totient : ℝ) with hMdef
  have hmnat : 1 ≤ m.toNat := by omega
  have hφpos : (0 : ℝ) < (m.toNat.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hM : 1 ≤ M := by
    rw [hMdef, le_div_iff₀ hφpos, one_mul]; exact_mod_cast Nat.totient_le _
  have hSm : c₀ * M ≤ singSeries m := hS m hm1 hev
  have hS0 : 0 ≤ singSeries m := le_trans (by positivity) hSm
  have hSt := leaf_tildeS_le_of_empty r χ m hm1 hev hprod
  obtain ⟨hI0, hI⟩ := tildeI_bounds β P m hβ0 hβ1.le hm1
  have hL : 0 < Real.log P := Real.log_pos (by linarith)
  have hLm : Real.log P ≤ Real.log m := Real.log_le_log (by linarith) (by linarith)
  have hβa : (1 - β) * Real.log P ≤ a := by
    have h' : 1 - β ≤ a / Real.log P := by linarith
    calc (1 - β) * Real.log P ≤ a / Real.log P * Real.log P :=
          mul_le_mul_of_nonneg_right h' hL.le
      _ = a := div_mul_cancel₀ a hL.ne'
  have hgap := gap_lower m β (Real.log P) a hmpos hL hLm hβ1 hβa
  have hmain := main_term_lower m (singSeries m) (tildeI β P m) (tildeS χ m) ((m : ℝ) ^ β)
    hS0 hI0 hI hSt
  set y := (1 - β) * Real.log P with hydef
  have hy0 : 0 ≤ y := by
    have : 0 < 1 - β := by linarith
    positivity
  have hea : 0 < Real.exp (-a) := Real.exp_pos _
  have hT : c₀ * Real.exp (-a) * M * y * X / 2 ≤
      (m : ℝ) * singSeries m + tildeI β P m * tildeS χ m := by
    have e1 : singSeries m * ((m : ℝ) * y * Real.exp (-a)) ≤ singSeries m * ((m : ℝ) - (m : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left hgap hS0
    have e2 : c₀ * M * ((m : ℝ) * y * Real.exp (-a)) ≤ singSeries m * ((m : ℝ) * y * Real.exp (-a)) :=
      mul_le_mul_of_nonneg_right hSm (by positivity)
    have e3 : c₀ * M * (X / 2 * y * Real.exp (-a)) ≤ c₀ * M * ((m : ℝ) * y * Real.exp (-a)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlow.le hy0) hea.le
    have e4 : c₀ * Real.exp (-a) * M * y * X / 2 = c₀ * M * (X / 2 * y * Real.exp (-a)) := by ring
    linarith
  have hR := (abs_le.mp hbound).1
  have hcmp : |Real.log K| + 1 < c₂ / (6 * δ) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hδ2
    linarith
  have hexpK : Real.exp (-(c₂ / (6 * δ))) ≤ K⁻¹ := by
    rw [← Real.exp_log hKpos, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have := le_abs_self (Real.log K)
    linarith
  have hCE : C * Real.exp (-(c₂ / (6 * δ))) ≤ c₀ * Real.exp (-a) / 4 := by
    have hKinv : C * K⁻¹ = c₀ * Real.exp (-a) / 4 := by
      rw [hK, Real.exp_neg]
      field_simp
    calc C * Real.exp (-(c₂ / (6 * δ))) ≤ C * K⁻¹ := mul_le_mul_of_nonneg_left hexpK hC.le
      _ = _ := hKinv
  have hR' : (m : ℝ) * singSeries m + tildeI β P m * tildeS χ m - C * X * divisorError r P m -
      C * Real.exp (-(c₂ / (6 * δ))) * X * M * y ≤ (R1 P X m).re := by
    have e : C * X * M * (1 - β) * Real.exp (-(c₂ / (6 * δ))) * Real.log P =
        C * Real.exp (-(c₂ / (6 * δ))) * X * M * y := by rw [hydef]; ring
    linarith
  have hfin := combine_ii_d (R1 P X m).re ((m : ℝ) * singSeries m + tildeI β P m * tildeS χ m)
    (C * X * divisorError r P m) (C * Real.exp (-(c₂ / (6 * δ)))) c₀ (Real.exp (-a)) M X y
    hR' hT hCE hM hX.le hy0 hc₀ hea
  have e : c₀ * Real.exp (-a) / 4 * (1 - β) * Real.log P * X =
      c₀ * Real.exp (-a) / 4 * y * X := by rw [hydef]; ring
  linarith

end LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3

#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3.tildeS_eq_twistedSing
#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3.tildeI_eq_Itilde
#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3.bp_lemma3_shared_of_lemma3
#print axioms LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3.caseIIdMajorLowerHyp_of_lemma3
