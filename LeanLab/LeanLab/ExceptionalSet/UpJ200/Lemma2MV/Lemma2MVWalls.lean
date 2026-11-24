import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Remainder66Split

/-!
# `Lemma2NoExcSmallDelta` with its two walls as explicit hypotheses

A copy of the proofs of `Lemma2MVSplit.mv_617`, `Lemma2MVSplit.mv_71` and
`Lemma2MVSplit.lemma2NoExcSmallDelta_of_leaves`, with the leaf `mv_remainder_66_68` supplied by
`rem66_of_lemma55` from P0015 Lemma 5.5, display (5.4) page 360, and the leaf
`mv_gallagher_lemma43`, P0015 Lemma 4.3, passed as a hypothesis. So
`lemma2NoExcSmallDelta_of_walls` is PROVED sorry free CONDITIONAL ON `rem66_lemma55` and
`mv_gallagher_lemma43` alone.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 eC nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected
  (singularSeries NoExceptionalReal Lemma2NoExcBP SingularSeriesEvenLowerBP exp_neg_le_inv
    noExceptionalReal_of_selected_one)

/-- P0015 display (6.17), the statement of `mv_617`, PROVED as there with the leaf
`mv_remainder_66_68` passed as the hypothesis `hR`. -/
theorem mv_617_of_walls (hR : type_of% @mv_remainder_66_68) : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ)‖ ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) + C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) := by
  obtain ⟨C1, hC1, h1⟩ := hR
  obtain ⟨C2, hC2, h2⟩ := mv_arc_main_611
  obtain ⟨C3, hC3, h3⟩ := mv_truncation_613
  obtain ⟨C4, hC4, h4⟩ := mv_tail_614
  refine ⟨C1 + C2 * C3 + C4, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨X1, hX1⟩ := h1 δ hδ hδ1
  obtain ⟨X2, hX2⟩ := h2 δ hδ hδ1
  obtain ⟨X3, hX3⟩ := h3 δ hδ hδ1
  obtain ⟨X4, hX4⟩ := h4 δ hδ hδ1
  refine ⟨max (max X1 X2) (max X3 (max X4 1)), ?_⟩
  intro X hX n hn hnX
  have hXa : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXd : X4 ≤ X := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  have hX1' : (1 : ℝ) ≤ X := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  set s := Icc 1 ⌊P⌋₊ with hs
  set W := mvW P X
  set ρ := (n : ℝ) / (n.totient : ℝ)
  have hφ : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le n
  have hW0 : 0 ≤ W := by
    refine sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  set E := X ^ (1 + δ) / P
  have hE0 : 0 ≤ E := div_nonneg (Real.rpow_nonneg (by linarith) _) hP0
  -- the three pieces
  have hA := hX1 X hXa n hn hnX
  have hB : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ ≤ C2 * C3 * E := by
    calc ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖
        ≤ ∑ q ∈ s, ‖mainWeight q n‖ * (C2 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
          have hqP : (q : ℝ) ≤ P := by
            have := (mem_Icc.mp hq).2
            exact le_trans (by exact_mod_cast this) (Nat.floor_le hP0)
          exact mul_le_mul_of_nonneg_left (hX2 X hXb q hq1 hqP n hn hnX) (norm_nonneg _)
      _ = C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
      _ ≤ C2 * (C3 * E) := mul_le_mul_of_nonneg_left (hX3 X hXc n hn hnX) hC2.le
      _ = C2 * C3 * E := by ring
  have hC : ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤ C4 * E := by
    obtain ⟨hsum, hhas⟩ := mv_singular_series_616 n hn
    have ht := norm_sum_sub_tsum_le hsum hhas s
    have hcongr : ∑' q : ℕ, (if q ∈ s then 0 else ‖mainWeight q n‖) =
        ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) := by
      refine tsum_congr (fun q => ?_)
      by_cases hq0 : q = 0
      · subst hq0; simp [mainWeight_zero]
      · have hiff : q ∈ s ↔ ¬ P < (q : ℝ) := by
          rw [hs, mem_Icc, not_lt]
          constructor
          · rintro ⟨_, h⟩; exact le_trans (by exact_mod_cast h) (Nat.floor_le hP0)
          · intro h; exact ⟨by omega, Nat.le_floor h⟩
        by_cases hq : q ∈ s
        · simp [hq, hiff.mp hq]
        · have : P < (q : ℝ) := by by_contra h; exact hq (hiff.mpr h)
          simp [hq, this]
    rw [hcongr] at ht
    rw [norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ‖(∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)‖
        ≤ (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ C4 * E := hX4 X hXd n hn hnX
  -- assemble
  have hsplit : R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) =
      (R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n) +
        ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) +
        (n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    push_cast
    have : ∑ q ∈ s, mainWeight q n * (n : ℂ) = ∑ q ∈ s, (n : ℂ) * mainWeight q n :=
      sum_congr rfl (fun q _ => mul_comm _ _)
    rw [this]; ring
  rw [hsplit]
  have hrem : 0 ≤ ρ * (W * Real.sqrt X + W ^ 2) := by positivity
  calc _ ≤ ‖R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n‖ +
          ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ +
          ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ :=
        norm_add₃_le
    _ ≤ C1 * ρ * (W * Real.sqrt X + W ^ 2) + C2 * C3 * E + C4 * E := by
        gcongr
    _ ≤ (C1 + C2 * C3 + C4) * E + (C1 + C2 * C3 + C4) * ρ * (W * Real.sqrt X + W ^ 2) := by
        have h23 : 0 ≤ C2 * C3 := by positivity
        nlinarith [mul_nonneg h23 hrem, mul_nonneg hC4.le hrem, mul_nonneg hC1.le hE0]

/-- P0015 display (7.1), the statement of `mv_71`, PROVED as there with the leaf
`mv_gallagher_lemma43` passed as the hypothesis `hG43`. -/
theorem mv_71_of_walls (hG43 : type_of% @mv_gallagher_lemma43) : ∀ a : ℝ, 0 < a → ∃ c₆ B δ₁ : ℝ, 0 < c₆ ∧ 0 < B ∧ 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      mvW (X ^ (6 * δ)) X ≤
        B * Real.sqrt X * Real.exp (-(c₆ * Real.log X / Real.log (X ^ (6 * δ)))) := by
  intro a ha
  obtain ⟨C, hC, hG⟩ := mv_gallagher_lemma42_step
  obtain ⟨c₃, B, δ₁, hc₃, hB, hδ₁, hL⟩ := hG43 a ha
  refine ⟨c₃, C * B, min δ₁ (1 / 100), hc₃, by positivity, lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδm
  obtain ⟨X1, hX1⟩ := hG δ hδ (lt_of_lt_of_le hδm (min_le_right _ _))
  obtain ⟨X2, hX2⟩ := hL δ hδ (lt_of_lt_of_le hδm (min_le_left _ _))
  refine ⟨max X1 (max X2 0), ?_⟩
  intro X hX hno
  have hXa : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hXb : X2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX0 : 0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨M, hM, hsum⟩ := hX2 X hXb hno
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX0 _
  have hstep : ∀ r ∈ Icc 1 ⌊P⌋₊,
      ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, Wnorm P X χ.1 ≤
        C * Real.sqrt X * ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := by
    intro r hr
    have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
    have hrP : (r : ℝ) ≤ P := le_trans (by exact_mod_cast (mem_Icc.mp hr).2) (Nat.floor_le hP0)
    have : NeZero r := ⟨by omega⟩
    rw [mul_finsum]
    refine finsum_le_finsum (Set.toFinite _) (Set.toFinite _) (fun χ => ?_)
    exact hX1 X hXa r hr1 hrP χ.1 χ.2 (M r χ.1) (hM r hr1 hrP χ.1 χ.2)
  calc mvW P X ≤ ∑ r ∈ Icc 1 ⌊P⌋₊, C * Real.sqrt X *
          ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := sum_le_sum hstep
    _ = C * Real.sqrt X * ∑ r ∈ Icc 1 ⌊P⌋₊,
          ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := by rw [mul_sum]
    _ ≤ C * Real.sqrt X * (B * Real.exp (-(c₃ * Real.log X / Real.log P))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * B * Real.sqrt X * Real.exp (-(c₃ * Real.log X / Real.log P)) := by ring

/-- P0082 Lemma 2 for small `δ`, the statement of `lemma2NoExcSmallDelta_of_leaves`, PROVED as
there, CONDITIONAL ON P0015 Lemma 5.5 `rem66_lemma55` and Lemma 4.3 `mv_gallagher_lemma43`. -/
theorem lemma2NoExcSmallDelta_of_walls (hL55 : type_of% @rem66_lemma55)
    (hG43 : type_of% @mv_gallagher_lemma43) : Lemma2NoExcSmallDelta := by
  intro a ha
  obtain ⟨CA, hCA, hA⟩ := mv_617_of_walls (rem66_of_lemma55 hL55)
  obtain ⟨c₆, B, δ₁, hc₆, hB, hδ₁, hW⟩ := mv_71_of_walls hG43 a ha
  refine ⟨c₆, CA * (1 + B + B ^ 2), hc₆, by positivity, min δ₁ (1 / 100),
    lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδm
  obtain ⟨XA, hXA⟩ := hA δ hδ (lt_of_lt_of_le hδm (min_le_right _ _))
  obtain ⟨XB, hXB⟩ := hW δ hδ (lt_of_lt_of_le hδm (min_le_left _ _))
  refine ⟨max (max XA XB) (max 2 (Real.exp (c₆ / (30 * δ ^ 2)))), ?_⟩
  intro X hX hno m hm hmX
  have hXa : XA ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp (c₆ / (30 * δ ^ 2)) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := Real.log_rpow hX0 _
  have hratio : c₆ * Real.log X / Real.log (X ^ (6 * δ)) = c₆ / (6 * δ) := by
    rw [hlogP]; field_simp
  have hbA := hXA X hXa m hm hmX
  have hbW := hXB X hXb hno
  rw [hratio] at hbW ⊢
  set e := Real.exp (-(c₆ / (6 * δ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; have : 0 < c₆ / (6 * δ) := by positivity
    linarith
  set W := mvW (X ^ (6 * δ)) X
  have hW0 : 0 ≤ W := sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  set ρ := (m : ℝ) / (m.totient : ℝ)
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le m
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  -- the first error term
  have hE : X ^ (1 + δ) / X ^ (6 * δ) ≤ X * e := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0, ← Real.exp_sub, he]
    have hsplit : Real.log X * (1 + δ) - Real.log X * (6 * δ) =
        Real.log X + -(5 * δ * Real.log X) := by ring
    rw [hsplit, Real.exp_add, Real.exp_log hX0]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hX0.le
    have hl : c₆ / (30 * δ ^ 2) ≤ Real.log X := by
      rw [← Real.log_exp (c₆ / (30 * δ ^ 2))]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have h30 : c₆ / (6 * δ) = 5 * δ * (c₆ / (30 * δ ^ 2)) := by field_simp; ring
    rw [h30]
    have : 5 * δ * (c₆ / (30 * δ ^ 2)) ≤ 5 * δ * Real.log X :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    linarith
  -- the W terms
  have hW1 : W * Real.sqrt X ≤ B * X * e := by
    calc W * Real.sqrt X ≤ B * Real.sqrt X * e * Real.sqrt X :=
          mul_le_mul_of_nonneg_right hbW hsq0
      _ = B * X * e := by linear_combination (B * e) * hsq
  have hW2 : W ^ 2 ≤ B ^ 2 * X * e := by
    have h1 : W ^ 2 ≤ (B * Real.sqrt X * e) ^ 2 := pow_le_pow_left₀ hW0 hbW 2
    have h2 : (B * Real.sqrt X * e) ^ 2 = B ^ 2 * X * (e * e) := by
      linear_combination (B ^ 2 * e ^ 2) * hsq
    have h3 : B ^ 2 * X * (e * e) ≤ B ^ 2 * X * e := by
      have : e * e ≤ e := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  calc _ ≤ CA * (X ^ (1 + δ) / X ^ (6 * δ)) + CA * ρ * (W * Real.sqrt X + W ^ 2) := hbA
    _ ≤ CA * (ρ * (X * e)) + CA * ρ * (B * X * e + B ^ 2 * X * e) := by
        have hXe0 : 0 ≤ X * e := by positivity
        gcongr
        calc X ^ (1 + δ) / X ^ (6 * δ) ≤ X * e := hE
          _ ≤ ρ * (X * e) := by nlinarith
    _ = CA * (1 + B + B ^ 2) * ρ * X * e := by ring

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_617_of_walls
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_71_of_walls
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lemma2NoExcSmallDelta_of_walls
