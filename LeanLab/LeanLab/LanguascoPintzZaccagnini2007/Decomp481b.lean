import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
The real and nonreal character cases of P0045 preprint page 6.
External results stay cited. Their consequences proved in P0045 stay open.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- P0045 page 6: Davenport Chapter 5, the real primitive conductor classification. -/
def RealPrimitiveStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∀ a, (χ a).im = 0) →
      r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r

/-- P0045 page 5: Pintz and Goldfeld and Schinzel, the real zero lower bound. -/
def RealZeroStatement481 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ →
      Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ

/-- P0045 page 6: the denominator in the quoted Iwaniec region. -/
def iwaniecDenom481 (r : ℕ) (t : ℝ) : ℝ :=
  let ℓ := Real.log ((r : ℝ) * (|t| + 2))
  4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
    (ℓ * Real.log (2 * ℓ)) ^ (3 / 4 : ℝ))

/-- P0045 page 6: Iwaniec's zero free region for nonreal primitive characters. -/
def IwaniecStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
      1 - 1 / iwaniecDenom481 r s.im < s.re → Lfun481 χ s ≠ 0

/-- LEAF. CITED. P0045 page 6, first proof paragraph following display 10.
Davenport Chapter 5 supplies the classification of real primitive conductors. -/
theorem davenport_classification481 : RealPrimitiveStatement481 := by
  sorry

/-- LEAF. CITED. P0045 page 5, the paragraph before Lemma 4.1.
Pintz 1976 and Goldfeld and Schinzel 1975 supply the real zero bound. -/
theorem real_zero_bound481 : RealZeroStatement481 := by
  sorry

/-- LEAF. CITED. P0045 page 6, second proof paragraph following display 10.
Iwaniec 1974 supplies the nonreal character zero free region. -/
theorem iwaniec_zero_free481 : IwaniecStatement481 := by
  sorry

/-- LEAF. OPEN. P0045 page 5 before Lemma 4.1 and page 6, first proof paragraph.
The real zero bound gives the quadratic conductor bound.
Nonreal zeros of real characters also require the classical zero free region.
The primitive principal character is excluded for large X at bounded height. -/
theorem real_exceptional_conductor481 (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  sorry

/-! Inlined proof of `nonreal_exceptional_radical481`. These private lemmas are copies of the
proved lemmas of `SPLIT_nonreal_exceptional_radical481`, which imports this file and so cannot be
called from here. No statement is changed and nothing is assumed. -/

private theorem lpz481_oddRad_pos (r : ℕ) : 0 < oddRad131 r := by
  rw [oddRad131]
  refine Finset.prod_pos ?_
  intro p hp
  have h2 : 2 < p := (Finset.mem_filter.mp hp).2
  omega

/-- The Iwaniec denominator is positive at conductor at least one. -/
private theorem lpz481_denom_pos {r : ℕ} {t : ℝ} (hr : 1 ≤ r) :
    0 < iwaniecDenom481 r t := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by linarith
  have habs : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hprod : (2 : ℝ) ≤ (r : ℝ) * (|t| + 2) := by
    have h := mul_le_mul hr1 habs (by norm_num : (0 : ℝ) ≤ 2) hr0
    simpa using h
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLpos : 0 < Real.log ((r : ℝ) * (|t| + 2)) := Real.log_pos (by linarith)
  have hLge : Real.log 2 ≤ Real.log ((r : ℝ) * (|t| + 2)) :=
    Real.log_le_log (by norm_num) hprod
  have h2L : 0 < Real.log (2 * Real.log ((r : ℝ) * (|t| + 2))) := by
    apply Real.log_pos
    linarith
  have hterm : 0 ≤ (Real.log ((r : ℝ) * (|t| + 2)) *
      Real.log (2 * Real.log ((r : ℝ) * (|t| + 2)))) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (le_of_lt (mul_pos hLpos h2L)) _
  have hodd1 : (1 : ℝ) ≤ (oddRad131 r : ℝ) := by
    have h1 : 1 ≤ oddRad131 r := by have := lpz481_oddRad_pos r; omega
    exact_mod_cast h1
  have hodd : 0 < Real.log (2 * (oddRad131 r : ℝ)) := by
    apply Real.log_pos
    linarith
  have hrw : iwaniecDenom481 r t
      = 4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
          (Real.log ((r : ℝ) * (|t| + 2)) *
            Real.log (2 * Real.log ((r : ℝ) * (|t| + 2)))) ^ ((3 : ℝ) / 4)) := rfl
  rw [hrw]
  exact mul_pos (by norm_num) (by linarith)

/-- The zero free region in the shape the box uses. -/
private theorem leaf_iwaniec_bound481_inl481b (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ X : ℕ, 2 ≤ X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
      (∃ a, (z.2.1 a).im ≠ 0) →
        Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im := by
  intro X hX P z hz him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  have hHpos : 0 < H := by linarith
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hD : 0 < iwaniecDenom481 z.1 z.2.2.im := lpz481_denom_pos h1
  have hnot : ¬ (1 - 1 / iwaniecDenom481 z.1 z.2.2.im < z.2.2.re) := by
    intro hlt
    exact (hiw z.1 h1 z.2.1 h3 him z.2.2 hlt) h4
  have hle : z.2.2.re ≤ 1 - 1 / iwaniecDenom481 z.1 z.2.2.im := not_lt.mp hnot
  have hstep : (1 : ℝ) / iwaniecDenom481 z.1 z.2.2.im ≤ H / Real.log X := by linarith
  have hmul : Real.log X ≤ H * iwaniecDenom481 z.1 z.2.2.im := by
    have h := (div_le_div_iff₀ hD hlogX).mp hstep
    linarith
  rw [div_le_iff₀ hHpos]
  linarith [mul_comm H (iwaniecDenom481 z.1 z.2.2.im)]

/-- `log y ≤ 6 * y ^ (1/6)` for `y ≥ 0`. -/
private theorem lpz481_log_le_six_rpow {y : ℝ} (hy : 0 ≤ y) :
    Real.log y ≤ 6 * y ^ ((1 : ℝ) / 6) := by
  have h := Real.log_le_rpow_div hy (show (0 : ℝ) < 1 / 6 by norm_num)
  have h6 : y ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) = 6 * y ^ ((1 : ℝ) / 6) := by
    rw [div_eq_mul_inv, show ((1 : ℝ) / 6)⁻¹ = 6 by norm_num]
    ring
  linarith [h, h6]

/-- The size of the second summand of the denominator only. -/
private theorem leaf_denom_upper_bound481_inl481b (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → ∀ P H : ℝ, AdmissibleP131 X P →
      ∀ z ∈ zeroBox481 X H T P,
        (Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) *
          Real.log (2 * Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)))) ^ (3 / 4 : ℝ)
          ≤ C * (Real.log X) ^ (7 / 8 : ℝ) := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hT2 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  set A : ℝ := (41 : ℝ) / 100 + Real.log (T + 2) / Real.log 2 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have h : 0 ≤ Real.log (T + 2) / Real.log 2 := div_nonneg hT2 hlog2pos.le
    linarith
  have hDpos : 0 < 6 * (2 : ℝ) ^ ((1 : ℝ) / 6) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) ((1 : ℝ) / 6))
  refine ⟨(6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * A ^ ((7 : ℝ) / 8), ?_, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos hDpos ((3 : ℝ) / 4))
      (Real.rpow_pos_of_pos hApos ((7 : ℝ) / 8))
  · intro X hX P H hP z hz
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
    obtain ⟨hPa, hPb⟩ := hP
    have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
    have hlogXge : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
    have hR1 : (1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast h1
    have hR0 : (0 : ℝ) < (z.1 : ℝ) := by linarith
    have ha2 : (2 : ℝ) ≤ |z.2.2.im| + 2 := by linarith [abs_nonneg z.2.2.im]
    have hapos : (0 : ℝ) < |z.2.2.im| + 2 := by linarith
    have hra : 0 < (z.1 : ℝ) * (|z.2.2.im| + 2) := mul_pos hR0 hapos
    have hge2 : (2 : ℝ) ≤ (z.1 : ℝ) * (|z.2.2.im| + 2) := by
      have h := mul_le_mul hR1 ha2 (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ (z.1 : ℝ))
      simpa using h
    have hPle : (z.1 : ℝ) ≤ (X : ℝ) ^ ((41 : ℝ) / 100) := h2.trans hPb
    have him : |z.2.2.im| + 2 ≤ T + 2 := by linarith
    have hmul : (z.1 : ℝ) * (|z.2.2.im| + 2) ≤ (X : ℝ) ^ ((41 : ℝ) / 100) * (T + 2) :=
      mul_le_mul hPle him (by linarith) (Real.rpow_pos_of_pos hXpos _).le
    have hlogmul : Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2))
        ≤ Real.log ((X : ℝ) ^ ((41 : ℝ) / 100) * (T + 2)) := Real.log_le_log hra hmul
    have hlogsplit : Real.log ((X : ℝ) ^ ((41 : ℝ) / 100) * (T + 2))
        = (41 : ℝ) / 100 * Real.log X + Real.log (T + 2) := by
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hXpos _)) (by linarith : (T + 2 : ℝ) ≠ 0),
        Real.log_rpow hXpos]
    have hl : Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ A * Real.log X := by
      have hge1 : (1 : ℝ) ≤ Real.log X / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        linarith
      have hTstep : Real.log (T + 2) ≤ Real.log (T + 2) / Real.log 2 * Real.log X := by
        have h := mul_le_mul_of_nonneg_left hge1 hT2
        rw [mul_one] at h
        calc Real.log (T + 2) ≤ Real.log (T + 2) * (Real.log X / Real.log 2) := h
          _ = Real.log (T + 2) / Real.log 2 * Real.log X := by ring
      have hAexp : A * Real.log X
          = (41 : ℝ) / 100 * Real.log X + Real.log (T + 2) / Real.log 2 * Real.log X := by
        rw [hAdef]
        ring
      linarith
    have hlpos : 0 < Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) := Real.log_pos (by linarith)
    set l : ℝ := Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) with hldef
    have hl0 : 0 < l := hlpos
    have hlog2le : Real.log 2 ≤ l := Real.log_le_log (by norm_num) hge2
    have h2l1 : 1 < 2 * l := by linarith [Real.log_two_gt_d9]
    have hlog2l : 0 < Real.log (2 * l) := Real.log_pos h2l1
    have hbasepos : 0 ≤ l * Real.log (2 * l) := (mul_pos hl0 hlog2l).le
    have hbase : l * Real.log (2 * l) ≤ 6 * (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((7 : ℝ) / 6) := by
      have hlog : Real.log (2 * l) ≤ 6 * (2 * l) ^ ((1 : ℝ) / 6) :=
        lpz481_log_le_six_rpow (by linarith)
      have hmr : (2 * l) ^ ((1 : ℝ) / 6) = (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((1 : ℝ) / 6) :=
        Real.mul_rpow (by norm_num) hl0.le
      have hl76 : l ^ ((7 : ℝ) / 6) = l * l ^ ((1 : ℝ) / 6) := by
        have h : (7 : ℝ) / 6 = 1 + 1 / 6 := by norm_num
        rw [h, Real.rpow_add hl0, Real.rpow_one]
      have hstep : l * Real.log (2 * l) ≤ l * (6 * ((2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((1 : ℝ) / 6))) := by
        have h := mul_le_mul_of_nonneg_left hlog hl0.le
        rwa [hmr] at h
      rw [hl76]
      nlinarith [hstep, Real.rpow_pos_of_pos hl0 ((1 : ℝ) / 6)]
    have hpow : (l * Real.log (2 * l)) ^ ((3 : ℝ) / 4)
        ≤ (6 * (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((7 : ℝ) / 6)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow hbasepos hbase (by norm_num)
    have hpow2 : (6 * (2 : ℝ) ^ ((1 : ℝ) / 6) * l ^ ((7 : ℝ) / 6)) ^ ((3 : ℝ) / 4)
        = (6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * l ^ ((7 : ℝ) / 8) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hl0.le _),
        ← Real.rpow_mul hl0.le]
      norm_num
    have hlA : l ^ ((7 : ℝ) / 8) ≤ A ^ ((7 : ℝ) / 8) * (Real.log X) ^ ((7 : ℝ) / 8) := by
      have h1' : l ^ ((7 : ℝ) / 8) ≤ (A * Real.log X) ^ ((7 : ℝ) / 8) :=
        Real.rpow_le_rpow hl0.le hl (by norm_num)
      rwa [Real.mul_rpow hApos.le hlogX.le] at h1'
    calc (l * Real.log (2 * l)) ^ ((3 : ℝ) / 4)
        ≤ (6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * l ^ ((7 : ℝ) / 8) := hpow.trans_eq hpow2
      _ ≤ (6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) *
            (A ^ ((7 : ℝ) / 8) * (Real.log X) ^ ((7 : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left hlA (le_of_lt (Real.rpow_pos_of_pos hDpos _))
      _ = ((6 * (2 : ℝ) ^ ((1 : ℝ) / 6)) ^ ((3 : ℝ) / 4) * A ^ ((7 : ℝ) / 8)) *
            (Real.log X) ^ ((7 : ℝ) / 8) := by ring

private theorem lpz481_rpow_eighth_pow {x : ℝ} (hx : 0 < x) :
    (x ^ ((1 : ℝ) / 8)) ^ 8 = x := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ 8 = (x ^ ((1 : ℝ) / 8)) ^ (8 : ℝ) :=
    (Real.rpow_natCast _ 8).symm
  rw [h1, ← Real.rpow_mul hx.le]
  norm_num

/-- Helper: `C * H < L ^ (1/8)` once `(C H) ^ 8 + 1 ≤ L`. -/
private theorem lpz481_ch_lt_eighth {C H L : ℝ} (hCH : 0 < C * H)
    (hL : (C * H) ^ 8 + 1 ≤ L) : C * H < L ^ ((1 : ℝ) / 8) := by
  have hLpos : 0 < L := by
    have h0 : (0 : ℝ) ≤ (C * H) ^ 8 := by positivity
    linarith
  have hDpos : 0 < L ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hLpos _
  have hD8 : (L ^ ((1 : ℝ) / 8)) ^ 8 = L := lpz481_rpow_eighth_pow hLpos
  have hlt : (C * H) ^ 8 < (L ^ ((1 : ℝ) / 8)) ^ 8 := by
    rw [hD8]
    nlinarith [pow_pos hCH 8]
  by_contra hcon
  push_neg at hcon
  have := pow_le_pow_left₀ (le_of_lt hDpos) hcon 8
  linarith

/-- The growth comparison. -/
private theorem leaf_log_growth_excludes481_inl481b (C : ℝ) (hC : 0 < C) (H : ℝ) (hH : 1 ≤ H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      C * (Real.log X) ^ (7 / 8 : ℝ) < Real.log X / H := by
  have hHpos : 0 < H := by linarith
  have hCH : 0 < C * H := mul_pos hC hHpos
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp ((C * H) ^ 8 + 1))
  have hN1 : (0 : ℝ) < (N : ℝ) := by
    have hpos : (0 : ℝ) < Real.exp ((C * H) ^ 8 + 1) := Real.exp_pos _
    linarith
  refine ⟨N, fun X hX => ?_⟩
  have hL : (C * H) ^ 8 + 1 ≤ Real.log X := by
    have h1 : (C * H) ^ 8 + 1 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos ((C * H) ^ 8 + 1)) (le_of_lt hN)
      rwa [Real.log_exp] at h
    have h2 : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hN1 (by exact_mod_cast hX)
    linarith
  have hLpos : 0 < Real.log X := by
    have h0 : (0 : ℝ) ≤ (C * H) ^ 8 := by positivity
    linarith
  set D : ℝ := (Real.log X) ^ ((1 : ℝ) / 8) with hDdef
  have hDpos : 0 < D := Real.rpow_pos_of_pos hLpos _
  have hCHltD : C * H < D := lpz481_ch_lt_eighth hCH hL
  have hsplit : (Real.log X) ^ (7 / 8 : ℝ) = Real.log X / D := by
    have h78 : (7 : ℝ) / 8 = 1 - 1 / 8 := by norm_num
    rw [h78, Real.rpow_sub hLpos, Real.rpow_one, hDdef]
  have hkey : C * (Real.log X / D) = (C * Real.log X) / D := by ring
  rw [hsplit, hkey, div_lt_div_iff₀ hDpos hHpos]
  nlinarith [mul_pos hLpos (sub_pos.mpr hCHltD)]

/-- `Lg X = log X / log 2`. -/
private theorem lpz481_Lg_eq (X : ℕ) : Lg X = Real.log X / Real.log 2 := by
  rw [Lg, Real.log_div_log]

/-- Growth helper for the assembly. -/
private theorem lpz481_growth_helper (D H : ℝ) (hD : 0 < D) (hH : 1 ≤ H) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      Real.log 2 + 2 * Real.log (Lg X) + D * (Real.log X) ^ (7 / 8 : ℝ)
        ≤ Real.log X / (4 * 10 ^ 4 * H) := by
  set K : ℝ := 4 * 10 ^ 4 * H with hKdef
  have hKpos : 0 < K := by positivity
  set E : ℝ := (15 + D) * K with hEdef
  have hEpos : 0 < E := by
    rw [hEdef]
    have : 0 < 15 + D := by linarith
    exact mul_pos this hKpos
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (E ^ 8 + 1))
  refine ⟨max N 3, fun X hX => ?_⟩
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have := Real.exp_pos (E ^ 8 + 1)
    linarith
  have hLbig : E ^ 8 + 1 ≤ Real.log X := by
    have h1 : E ^ 8 + 1 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos (E ^ 8 + 1)) (le_of_lt hN)
      rwa [Real.log_exp] at h
    have h2 : Real.log (N : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hNpos (by exact_mod_cast hXN)
    linarith
  have hLpos : 0 < Real.log X := by
    have h1 : (1 : ℝ) < (X : ℝ) := by
      have h : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
      linarith
    exact Real.log_pos h1
  have hLone : 1 ≤ Real.log X := by
    have h3X : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
    have h13 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    have h3 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) h3X
    linarith
  set L : ℝ := Real.log X with hLdef
  have hLpos' : 0 < L := hLpos
  have hLone' : 1 ≤ L := hLone
  have h78one : (1 : ℝ) ≤ L ^ ((7 : ℝ) / 8) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hLone' (by norm_num : (0 : ℝ) ≤ 7 / 8)
    rwa [Real.one_rpow] at h
  have hlog2 : Real.log 2 ≤ L ^ ((7 : ℝ) / 8) := by
    have h := Real.log_two_lt_d9
    linarith
  have hLgbound : Real.log (Lg X) ≤ 1 + 6 * L ^ ((1 : ℝ) / 6) := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hLgpos : 0 < Lg X := by
      rw [lpz481_Lg_eq]
      exact div_pos hLpos' hlog2pos
    have hLgle : Lg X ≤ 2 * L := by
      rw [lpz481_Lg_eq, div_le_iff₀ hlog2pos]
      nlinarith [Real.log_two_gt_d9, hLpos']
    have hstep1 : Real.log (Lg X) ≤ Real.log (2 * L) := Real.log_le_log hLgpos hLgle
    have hstep2 : Real.log (2 * L) = Real.log 2 + Real.log L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hLpos')]
    have hstep3 : Real.log L ≤ 6 * L ^ ((1 : ℝ) / 6) := lpz481_log_le_six_rpow hLpos'.le
    have hstep4 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have h16le : L ^ ((1 : ℝ) / 6) ≤ L ^ ((7 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hLone' (by norm_num)
  have hMain : (15 + D) * L ^ ((7 : ℝ) / 8) ≤ L / K := by
    have hKE : E ≤ L ^ ((1 : ℝ) / 8) := le_of_lt (lpz481_ch_lt_eighth hEpos hLbig)
    have hsplit : L ^ ((7 : ℝ) / 8) * L ^ ((1 : ℝ) / 8) = L := by
      rw [← Real.rpow_add hLpos', show (7 : ℝ) / 8 + 1 / 8 = 1 by norm_num, Real.rpow_one]
    rw [le_div_iff₀ hKpos]
    calc (15 + D) * L ^ ((7 : ℝ) / 8) * K
        = L ^ ((7 : ℝ) / 8) * E := by rw [hEdef]; ring
      _ ≤ L ^ ((7 : ℝ) / 8) * L ^ ((1 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left hKE (le_of_lt (Real.rpow_pos_of_pos hLpos' _))
      _ = L := hsplit
  have hExp : Real.log 2 + 2 * Real.log (Lg X) + D * L ^ ((7 : ℝ) / 8)
      ≤ (15 + D) * L ^ ((7 : ℝ) / 8) := by
    have h16pos : 0 < L ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hLpos' _
    nlinarith [hlog2, hLgbound, h16le, h78one]
  have hfin := hExp.trans hMain
  rwa [hKdef] at hfin

/-- The split target: the statement of `nonreal_exceptional_radical481`, proved from the three
leaves through `oddRad131`, with constant one. -/
private theorem nonreal_exceptional_radical481_split_inl481b (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨C, hC, hden⟩ := leaf_denom_upper_bound481_inl481b T hT
  obtain ⟨X₁, hX₁⟩ := lpz481_growth_helper C H hC hH
  refine ⟨1, one_pos, max X₁ 3, ?_⟩
  intro X hX P hP z hz him
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have h2 : 2 ≤ X := by omega
  have hHpos : 0 < H := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast h2)
  have hlow : Real.log X / H ≤ iwaniecDenom481 z.1 z.2.2.im :=
    leaf_iwaniec_bound481_inl481b hiw H T hH hT X h2 P z hz him
  have hup : (Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) *
      Real.log (2 * Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)))) ^ (3 / 4 : ℝ)
      ≤ C * (Real.log X) ^ (7 / 8 : ℝ) := hden X h2 P H hP z hz
  have hgro : Real.log 2 + 2 * Real.log (Lg X) + C * (Real.log X) ^ (7 / 8 : ℝ)
      ≤ Real.log X / (4 * 10 ^ 4 * H) := hX₁ X hX1
  have hdenom : iwaniecDenom481 z.1 z.2.2.im
      = 4 * 10 ^ 4 * (Real.log (2 * (oddRad131 z.1 : ℝ)) +
          (Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) *
            Real.log (2 * Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)))) ^ (3 / 4 : ℝ)) := rfl
  rw [hdenom] at hlow
  have hstep : Real.log X / H ≤
      4 * 10 ^ 4 * (Real.log (2 * (oddRad131 z.1 : ℝ)) + C * (Real.log X) ^ (7 / 8 : ℝ)) := by
    nlinarith [hlow, hup]
  have hmain : Real.log X / (4 * 10 ^ 4 * H) - C * (Real.log X) ^ (7 / 8 : ℝ)
      ≤ Real.log (2 * (oddRad131 z.1 : ℝ)) := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 10 ^ 4 * H)]
    rw [div_le_iff₀ hHpos] at hstep
    nlinarith [hstep]
  have hLgpos : 0 < Lg X := by
    rw [lpz481_Lg_eq]
    exact div_pos hlogX (by linarith [Real.log_two_gt_d9])
  have hexpand : Real.log (2 * Lg X ^ 2) = Real.log 2 + 2 * Real.log (Lg X) := by
    rw [Real.log_mul (x := (2 : ℝ)) (y := Lg X ^ 2) (by norm_num)
      (pow_ne_zero 2 (ne_of_gt hLgpos)), Real.log_pow]
    push_cast
    ring
  have hkey : Real.log (2 * Lg X ^ 2) ≤ Real.log (2 * (oddRad131 z.1 : ℝ)) := by
    rw [hexpand]
    linarith [hgro, hmain]
  have hoddpos : (0 : ℝ) < (oddRad131 z.1 : ℝ) := by
    have h := lpz481_oddRad_pos z.1
    exact_mod_cast h
  have := (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2 * Lg X ^ 2) (by positivity)).mp hkey
  have hfin : Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by linarith
  simpa using hfin

/-- PROVED. P0045 page 6, last proof paragraph and display 10.
The Iwaniec region gives odd radical growth for nonreal exceptional characters.
This states the weaker quadratic conclusion actually used by the corollary. -/
theorem nonreal_exceptional_radical481 (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) :=
  nonreal_exceptional_radical481_split_inl481b hiw H T hH hT

/-- LEAF. P0045 page 6, first proof paragraph following display 10.
Transfer the conductor lower bound through the three classified possibilities. -/
theorem real_radical_transfer481 {r : ℕ} {Y : ℝ}
    (hclass : r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r)
    (hY : Y ≤ (r : ℝ)) : Y / 8 ≤ (oddRad131 r : ℝ) := by
  have hr : r ≤ 8 * oddRad131 r := by rcases hclass with h | h | h <;> omega
  have hc : (r : ℝ) ≤ 8 * (oddRad131 r : ℝ) := by exact_mod_cast hr
  linarith

end
end LeanLab.LPZ2007
