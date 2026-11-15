/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 5 hypothesis A1.2 and
page 15 first paragraph of Section 4, as transcribed in
`Task556a.prime_short_interval_character`.

RESULT OF THIS FILE. The exact statement of
`Task556a.prime_short_interval_character` is refuted for every B > 1/5 and
every 0 < ε ≤ 11/36, see `prime_short_interval_character_statement_fails`,
and so the statement quantified over all B and ε is refuted as well, see
`prime_short_interval_character_universal_fails`.

REASON. Hypothesis A1.2 of page 5 is printed with the character multiplying
the smooth main weight, (λ(m) - D(χ) f(m)) χ(m). Take the principal character
modulo 1 and modulo 2 on the whole of I1 = [X - Y, X). The prime indicator
vanishes on the even integers of I1, so the difference of the two defects is
exactly minus the sum of 1 / log m over the even m of I1, which is at least
(Y / 2 - 1) / log X. The claimed bound gives 2 C Y (log X)^(-5B) for that
difference, impossible for large X when 5B > 1. No prime number theory is used.

Every declaration below is proved in full. No definition is added.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a

namespace LeanLab.KumchevLiu2007.Eq33RouteE

open Real Complex LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology

/-- P0088 page 5 hypothesis A1.2 with page 2 display 5: on the whole interval
I1 the defect of the principal character modulo 1 minus the defect of the
principal character modulo 2 is minus the sum of f1(m) = 1 / log m over the
even integers of I1. -/
theorem primeCharacterDefect_principal_diff (X Y : ℝ) (h : 2 < X - Y) :
    primeCharacterDefect (1 : DirichletCharacter ℂ 1) X Y (X - Y) X -
        primeCharacterDefect (1 : DirichletCharacter ℂ 2) X Y (X - Y) X =
      -∑ m ∈ primeWindow X Y,
        (((if Even m then 1 / Real.log (m : ℝ) else 0 : ℝ)) : ℂ) := by
  unfold primeCharacterDefect
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    have h2 := hm
    simp only [primeWindow, Finset.mem_filter] at h2
    exact h2.2
  have h1 : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  rw [ite_eq_left hm', ite_eq_left hm', h1, mul_one]
  simp only [ite_true]
  rcases Nat.even_or_odd m with he | ho
  · have h0 : ((m : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff m 2).mpr he.two_dvd
    have hnp : ¬ m.Prime := by
      intro hp
      have h2 : m = 2 := (hp.even_iff).mp he
      rw [h2] at hm'
      norm_num at hm'
      linarith [hm'.1]
    rw [h0, MulChar.map_zero, mul_zero, sub_zero, ite_eq_right hnp, ite_eq_left he]
    simp
  · have h1' : ((m : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr ho
    rw [h1', map_one, mul_one, sub_self, ite_eq_right (Nat.not_even_iff_odd.mpr ho)]
    simp

/-- P0088 page 2 display 5 and page 15 f1: the sum of f1(m) = 1 / log m over
the even integers of I1 = [X - Y, X) is at least (Y / 2 - 1) / log X. -/
theorem even_weight_sum_ge (X Y : ℝ) (hY : 0 ≤ Y) (h : 2 < X - Y) :
    (Y / 2 - 1) / Real.log X ≤
      ∑ m ∈ primeWindow X Y, (if Even m then 1 / Real.log (m : ℝ) else 0 : ℝ) := by
  have hX : 2 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hmem : ∀ k ∈ Finset.Ico ⌈(X - Y) / 2⌉₊ ⌈X / 2⌉₊,
      X - Y ≤ ((2 * k : ℕ) : ℝ) ∧ ((2 * k : ℕ) : ℝ) < X := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have h1 : (X - Y) / 2 ≤ (k : ℝ) := Nat.ceil_le.mp hk1
    have h2 : (k : ℝ) < X / 2 := Nat.lt_ceil.mp hk2
    push_cast
    constructor <;> linarith
  have hsub : (Finset.Ico ⌈(X - Y) / 2⌉₊ ⌈X / 2⌉₊).image (fun k : ℕ => 2 * k) ⊆
      primeWindow X Y := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨h1, h2⟩ := hmem k hk
    simp only [primeWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2.le), h1, h2⟩
  have hcard : Y / 2 - 1 ≤ ((⌈X / 2⌉₊ - ⌈(X - Y) / 2⌉₊ : ℕ) : ℝ) := by
    have hb : X / 2 ≤ (⌈X / 2⌉₊ : ℝ) := Nat.le_ceil _
    have ha : (⌈(X - Y) / 2⌉₊ : ℝ) < (X - Y) / 2 + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have hn : ⌈X / 2⌉₊ ≤ (⌈X / 2⌉₊ - ⌈(X - Y) / 2⌉₊) + ⌈(X - Y) / 2⌉₊ := by omega
    have hn' : (⌈X / 2⌉₊ : ℝ) ≤
        ((⌈X / 2⌉₊ - ⌈(X - Y) / 2⌉₊ : ℕ) : ℝ) + (⌈(X - Y) / 2⌉₊ : ℝ) := by
      exact_mod_cast hn
    linarith
  calc
    (Y / 2 - 1) / Real.log X ≤
        ∑ _k ∈ Finset.Ico ⌈(X - Y) / 2⌉₊ ⌈X / 2⌉₊, 1 / Real.log X := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one_div]
      exact div_le_div_of_nonneg_right hcard hL.le
    _ ≤ ∑ k ∈ Finset.Ico ⌈(X - Y) / 2⌉₊ ⌈X / 2⌉₊,
        (if Even (2 * k) then 1 / Real.log ((2 * k : ℕ) : ℝ) else 0 : ℝ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      obtain ⟨h1, h2⟩ := hmem k hk
      rw [ite_eq_left (even_two_mul k)]
      have hpos : 0 < Real.log ((2 * k : ℕ) : ℝ) := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le hpos
        (Real.log_le_log (by linarith) h2.le)
    _ = ∑ m ∈ (Finset.Ico ⌈(X - Y) / 2⌉₊ ⌈X / 2⌉₊).image (fun k : ℕ => 2 * k),
        (if Even m then 1 / Real.log (m : ℝ) else 0 : ℝ) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) hxy
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
      split_ifs
      · have h2 := hm
        simp only [primeWindow, Finset.mem_filter] at h2
        have hpos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith [h2.2.1])
        positivity
      · exact le_rfl

/-- P0088 page 5 hypothesis A1.2 as transcribed in
`Task556a.prime_short_interval_character`, page 15 first paragraph of Section 4:
the exact statement fails for every B > 1/5 and every 0 < ε ≤ 11/36. The
principal characters modulo 1 and modulo 2 on the whole of I1 give the
contradiction. -/
theorem prime_short_interval_character_statement_fails (B ε : ℝ) (hB : 1 / 5 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 36) :
    ¬ (∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeCharacterDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)) := by
  rintro ⟨C, X0, hC, -, hst⟩
  have hT1 : Filter.Tendsto (fun X : ℝ => Real.log X ^ (5 * B - 1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  have hT2 : Filter.Tendsto (fun X : ℝ => Real.log X ^ B) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  have hT3 : Filter.Tendsto (fun X : ℝ => X ^ (7 / 12 + ε / 2)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by positivity)
  have hT4 : Filter.Tendsto (fun X : ℝ => X ^ (1 - (7 / 12 + ε / 2))) Filter.atTop
      Filter.atTop := tendsto_rpow_atTop (by linarith)
  obtain ⟨X, h1, h2, h3, h4, h5, h6⟩ :=
    ((hT1.eventually_gt_atTop (8 * C)).and ((hT2.eventually_ge_atTop 2).and
      ((hT3.eventually_ge_atTop 4).and ((hT4.eventually_ge_atTop 2).and
        ((Filter.eventually_ge_atTop X0).and (Filter.eventually_ge_atTop (6 : ℝ))))))).exists
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hY4 : 4 ≤ windowY X ε := h3
  have hXY : X = windowY X ε * X ^ (1 - (7 / 12 + ε / 2)) := by
    rw [windowY, ← Real.rpow_add hX0]
    ring_nf
    rw [Real.rpow_one]
  have hYX : 2 < X - windowY X ε := by nlinarith
  have hq1 : ((1 : ℕ) : ℝ) ≤ Real.log X ^ B := by push_cast; linarith
  have hq2 : ((2 : ℕ) : ℝ) ≤ Real.log X ^ B := by push_cast; linarith
  have hd1 := hst X h5 1 le_rfl hq1 1 (X - windowY X ε) X le_rfl (by linarith) le_rfl
  have hd2 := hst X h5 2 (by norm_num) hq2 1 (X - windowY X ε) X le_rfl (by linarith) le_rfl
  have hdiff := primeCharacterDefect_principal_diff X (windowY X ε) hYX
  have hlow := even_weight_sum_ge X (windowY X ε) (by linarith) hYX
  have hnorm : (windowY X ε / 2 - 1) / Real.log X ≤
      2 * (C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)) := by
    calc
      _ ≤ ∑ m ∈ primeWindow X (windowY X ε),
          (if Even m then 1 / Real.log (m : ℝ) else 0 : ℝ) := hlow
      _ ≤ ‖primeCharacterDefect (1 : DirichletCharacter ℂ 1) X (windowY X ε)
            (X - windowY X ε) X -
          primeCharacterDefect (1 : DirichletCharacter ℂ 2) X (windowY X ε)
            (X - windowY X ε) X‖ := by
        rw [hdiff, norm_neg, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ _ := by
        refine (norm_sub_le _ _).trans ?_
        linarith
  have hTL : Real.log X ^ (5 * B - 1) * Real.log X = (Real.log X ^ B) ^ (5 : ℕ) := by
    calc
      _ = Real.log X ^ (5 * B - 1) * Real.log X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = Real.log X ^ (5 * B - 1 + 1) := (Real.rpow_add hL _ _).symm
      _ = Real.log X ^ (B * ((5 : ℕ) : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = _ := by rw [Real.rpow_mul hL.le, Real.rpow_natCast]
  have hT : 0 < Real.log X ^ (5 * B - 1) := Real.rpow_pos_of_pos hL _
  rw [zpow_neg, zpow_ofNat, ← hTL, div_le_iff₀ hL] at hnorm
  have hfin : 2 * (C * windowY X ε * (Real.log X ^ (5 * B - 1) * Real.log X)⁻¹) *
      Real.log X = 2 * C * windowY X ε / Real.log X ^ (5 * B - 1) := by
    field_simp
  rw [hfin, le_div_iff₀ hT] at hnorm
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ windowY X ε / 4 - 1 by linarith) hT.le,
    mul_pos (show (0 : ℝ) < windowY X ε by linarith)
      (show (0 : ℝ) < Real.log X ^ (5 * B - 1) - 8 * C by linarith)]

/-- P0088 page 5 hypothesis A1.2 as transcribed in
`Task556a.prime_short_interval_character`, page 15 first paragraph of Section 4:
the statement quantified over all B > 0 and 0 < ε ≤ 11/36, exactly as on main,
is false. The instance B = 1 and ε = 1/10 fails. -/
theorem prime_short_interval_character_universal_fails :
    ¬ (∀ (B ε : ℝ) (_ : 0 < B) (_ : 0 < ε) (_ : ε ≤ 11 / 36),
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeCharacterDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)) := by
  intro h
  exact prime_short_interval_character_statement_fails 1 (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) (h 1 (1 / 10) (by norm_num) (by norm_num) (by norm_num))

end LeanLab.KumchevLiu2007.Eq33RouteE
