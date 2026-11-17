/-
Kumchev and Liu 2007, page 5 hypothesis A1.2, supplied on page 15 in the
first paragraph of Section 4.

The file `SPLIT_prime_short_interval_character` cuts the sealed statement into
three leaves. This file proves that the statement of the third leaf,
`leaf_principal_prime_count_level_exceeding_one`, is false for every
`B > 1/5` and every `0 < ε ≤ 11/36`, with no leaf and no prime number theory.

The moduli two and six on the whole window are enough. The integers coprime
to six are among the integers coprime to two, and the ones left over are the
odd multiples of three, the residue class three modulo six. None of them is
prime inside the window, so the two centres differ by minus the sum of the
reciprocal logarithm over that class, which is at least
`(windowY / 6 - 1) / log X`. The two bounds of the leaf give twice a fixed
constant times `windowY` over a positive power of `log X`.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_prime_short_interval_character

namespace LeanLab.KumchevLiu2007.Task556a

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 5 hypothesis A1.2 with page 2 display 5: on the whole interval I1 the
centre of the level two sum minus the centre of the level six sum is minus the
sum of f1(m) = 1 / log m over the integers of I1 congruent to 3 modulo 6. -/
theorem principal_coprime_two_six_diff (X Y : ℝ) (h : 3 < X - Y) :
    (∑ m ∈ (primeWindow X Y).filter
          (fun m : ℕ => (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 2),
          ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))) -
        (∑ m ∈ (primeWindow X Y).filter
          (fun m : ℕ => (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 6),
          ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))) =
      -∑ m ∈ primeWindow X Y,
        (((if m % 6 = 3 then 1 / Real.log (m : ℝ) else 0 : ℝ)) : ℂ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    have h2 := hm
    simp only [primeWindow, Finset.mem_filter] at h2
    exact h2.2
  have hc2 : m.Coprime 2 ↔ Odd m := Nat.coprime_two_right
  have hc3 : m.Coprime 3 ↔ ¬ 3 ∣ m := by
    rw [Nat.coprime_comm]
    exact Nat.prime_three.coprime_iff_not_dvd
  have hc6 : m.Coprime 6 ↔ (Odd m ∧ ¬ 3 ∣ m) := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right, hc2, hc3]
  by_cases h3 : m % 6 = 3
  · have ho : Odd m := by
      rw [Nat.odd_iff]; omega
    have hd : 3 ∣ m := by omega
    have hnp : ¬ m.Prime := by
      intro hp
      have h3m : 3 = m := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
      have hlt : (3 : ℝ) < (m : ℝ) := by linarith [hm'.1]
      rw [← h3m] at hlt
      norm_num at hlt
    have hn6 : ¬ m.Coprime 6 := fun hc => (hc6.mp hc).2 hd
    rw [if_pos (⟨hm', hc2.mpr ho⟩ : (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 2),
      if_neg (fun hc : (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 6 => hn6 hc.2),
      if_neg hnp, if_pos h3]
    simp
  · have hiff : m.Coprime 2 ↔ m.Coprime 6 := by
      rw [hc2, hc6, Nat.odd_iff]
      constructor
      · intro ho
        exact ⟨ho, by omega⟩
      · exact fun hc => hc.1
    rw [if_neg h3]
    by_cases hc : m.Coprime 2
    · rw [if_pos (⟨hm', hc⟩ : (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 2),
        if_pos (⟨hm', hiff.mp hc⟩ : (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 6)]
      simp
    · rw [if_neg (fun hx : (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 2 => hc hx.2),
        if_neg (fun hx : (X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 6 =>
          hc (hiff.mpr hx.2))]
      simp

/-- Page 2 display 5 and page 15 f1: the sum of f1(m) = 1 / log m over the
integers of I1 = [X - Y, X) congruent to 3 modulo 6 is at least
(Y / 6 - 1) / log X. -/
theorem three_mod_six_weight_sum_ge (X Y : ℝ) (hY : 0 ≤ Y) (h : 3 < X - Y) :
    (Y / 6 - 1) / Real.log X ≤
      ∑ m ∈ primeWindow X Y, (if m % 6 = 3 then 1 / Real.log (m : ℝ) else 0 : ℝ) := by
  have hX : 3 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hmem : ∀ k ∈ Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊,
      X - Y ≤ ((6 * k + 3 : ℕ) : ℝ) ∧ ((6 * k + 3 : ℕ) : ℝ) < X := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have h1 : (X - Y - 3) / 6 ≤ (k : ℝ) := Nat.ceil_le.mp hk1
    have h2 : (k : ℝ) < (X - 3) / 6 := Nat.lt_ceil.mp hk2
    push_cast
    constructor <;> linarith
  have hsub : (Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊).image
      (fun k : ℕ => 6 * k + 3) ⊆ primeWindow X Y := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨h1, h2⟩ := hmem k hk
    simp only [primeWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2.le), h1, h2⟩
  have hcard : Y / 6 - 1 ≤ ((⌈(X - 3) / 6⌉₊ - ⌈(X - Y - 3) / 6⌉₊ : ℕ) : ℝ) := by
    have hb : (X - 3) / 6 ≤ (⌈(X - 3) / 6⌉₊ : ℝ) := Nat.le_ceil _
    have ha : (⌈(X - Y - 3) / 6⌉₊ : ℝ) < (X - Y - 3) / 6 + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have hn : ⌈(X - 3) / 6⌉₊ ≤
        (⌈(X - 3) / 6⌉₊ - ⌈(X - Y - 3) / 6⌉₊) + ⌈(X - Y - 3) / 6⌉₊ := by omega
    have hn' : (⌈(X - 3) / 6⌉₊ : ℝ) ≤
        ((⌈(X - 3) / 6⌉₊ - ⌈(X - Y - 3) / 6⌉₊ : ℕ) : ℝ) +
          (⌈(X - Y - 3) / 6⌉₊ : ℝ) := by
      exact_mod_cast hn
    linarith
  calc
    (Y / 6 - 1) / Real.log X ≤
        ∑ _k ∈ Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊, 1 / Real.log X := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one_div]
      exact div_le_div_of_nonneg_right hcard hL.le
    _ ≤ ∑ k ∈ Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊,
        (if (6 * k + 3) % 6 = 3 then 1 / Real.log ((6 * k + 3 : ℕ) : ℝ) else 0 : ℝ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      obtain ⟨h1, h2⟩ := hmem k hk
      rw [if_pos (by omega : (6 * k + 3) % 6 = 3)]
      have hpos : 0 < Real.log ((6 * k + 3 : ℕ) : ℝ) := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le hpos
        (Real.log_le_log (by linarith) h2.le)
    _ = ∑ m ∈ (Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊).image
          (fun k : ℕ => 6 * k + 3),
        (if m % 6 = 3 then 1 / Real.log (m : ℝ) else 0 : ℝ) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      have hxy' : 6 * x + 3 = 6 * y + 3 := hxy
      omega
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
      split_ifs
      · have h2 := hm
        simp only [primeWindow, Finset.mem_filter] at h2
        have hpos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith [h2.2.1])
        positivity
      · exact le_rfl

/-- Page 5 hypothesis A1.2 at the trivial character and level above one, as cut
in `leaf_principal_prime_count_level_exceeding_one`: the exact statement of
that leaf fails for every B > 1/5 and every 0 < ε ≤ 11/36. The levels two and
six on the whole of I1 give the contradiction. -/
theorem leaf_principal_prime_count_level_exceeding_one_statement_fails (B ε : ℝ)
    (hB : 1 / 5 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 36) :
    ¬ (∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => (u ≤ (m : ℝ) ∧ (m : ℝ) < v) ∧ m.Coprime q),
            ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖ ≤
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
    ((hT1.eventually_gt_atTop (24 * C)).and ((hT2.eventually_ge_atTop 6).and
      ((hT3.eventually_ge_atTop 12).and ((hT4.eventually_ge_atTop 2).and
        ((Filter.eventually_ge_atTop X0).and (Filter.eventually_ge_atTop (6 : ℝ))))))).exists
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hY12 : 12 ≤ windowY X ε := h3
  have hXY : X = windowY X ε * X ^ (1 - (7 / 12 + ε / 2)) := by
    rw [windowY, ← Real.rpow_add hX0]
    ring_nf
    rw [Real.rpow_one]
  have hYX : 3 < X - windowY X ε := by nlinarith
  have hq2 : ((2 : ℕ) : ℝ) ≤ Real.log X ^ B := by push_cast; linarith
  have hq6 : ((6 : ℕ) : ℝ) ≤ Real.log X ^ B := by push_cast; linarith
  have hd2 := hst X h5 2 le_rfl hq2 (X - windowY X ε) X le_rfl (by linarith) le_rfl
  have hd6 := hst X h5 6 (by norm_num) hq6 (X - windowY X ε) X le_rfl (by linarith) le_rfl
  have hdiff := principal_coprime_two_six_diff X (windowY X ε) hYX
  have hlow := three_mod_six_weight_sum_ge X (windowY X ε) (by linarith) hYX
  have hnorm : (windowY X ε / 6 - 1) / Real.log X ≤
      2 * (C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)) := by
    calc
      _ ≤ ∑ m ∈ primeWindow X (windowY X ε),
          (if m % 6 = 3 then 1 / Real.log (m : ℝ) else 0 : ℝ) := hlow
      _ ≤ ‖(∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => (X - windowY X ε ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 2),
              ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))) -
            (∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => (X - windowY X ε ≤ (m : ℝ) ∧ (m : ℝ) < X) ∧ m.Coprime 6),
              ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ)))‖ := by
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
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ windowY X ε / 12 - 1 by linarith) hT.le,
    mul_pos (show (0 : ℝ) < windowY X ε by linarith)
      (show (0 : ℝ) < Real.log X ^ (5 * B - 1) - 24 * C by linarith)]

/-- Page 5 hypothesis A1.2 at the trivial character and level above one, as cut
in `leaf_principal_prime_count_level_exceeding_one`: the statement quantified
over all B > 0 and 0 < ε ≤ 11/36, exactly as the leaf, is false. The instance
B = 1 and ε = 1/10 fails. -/
theorem leaf_principal_prime_count_level_exceeding_one_universal_fails :
    ¬ (∀ (B ε : ℝ) (_ : 0 < B) (_ : 0 < ε) (_ : ε ≤ 11 / 36),
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => (u ≤ (m : ℝ) ∧ (m : ℝ) < v) ∧ m.Coprime q),
            ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)) := by
  intro h
  exact leaf_principal_prime_count_level_exceeding_one_statement_fails 1 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
    (h 1 (1 / 10) (by norm_num) (by norm_num) (by norm_num))

end LeanLab.KumchevLiu2007.Task556a
