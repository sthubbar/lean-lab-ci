/-
Kumchev and Liu 2007, page 5 hypothesis A1.2, supplied on page 15 in the
first paragraph of Section 4, as sealed in
`Task556a.prime_short_interval_character`.

This file splits that one statement into three leaves and proves it from them
with no sorry of its own. The split is the case analysis on the character and
on the level that the shape of `primeCharacterDefect` forces. The defect is a
sum of the prime indicator minus the reciprocal logarithm, the whole bracket
multiplied by the character. Once the character is not the trivial one the
smooth weight leaves with it, and the summand is the prime indicator times the
character: a short interval character sum over the primes. Once the character
is the trivial one the character keeps exactly the integers coprime to the
level, all integers at level one and only the coprime ones above, and the
summand is the prime indicator minus the reciprocal logarithm over those.

The third leaf is where the sealed statement goes wrong. At level two the
centre of that leaf is the prime count of the window minus the sum of the
reciprocal logarithm over the odd integers of the window, because the even ones
carry no character. The level one leaf and the level two leaf cannot both hold:
their centres differ by the sum of the reciprocal logarithm over the even
integers of the window, which is at least `(windowY / 2 - 1) / log X`, while
the two bounds give twice a fixed constant times `windowY` over a positive
power of `log X`. The theorem at the end of this file proves that reading of
the sealed statement outright, with no leaf, so the third leaf is recorded as
false as cut rather than as work still to do.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a
import LeanLab.KumchevLiu2007.PrimeShortIntervalCharacter_Leaves

namespace LeanLab.KumchevLiu2007.Task556a

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. Step one of the split, the nontrivial character case of hypothesis
A1.2. With the character not trivial the smooth weight leaves the defect, so
the whole estimate is the sum of the character over the primes of the window
`I1` intersected with the subinterval `[u, v)`. This is the short interval
Siegel Walfisz step of page 15. -/
theorem leaf_nonprincipal_prime_character_sum (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            (if m.Prime then χ m else 0)‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) :=
  leaf_nonprincipal_prime_character_sum_from_leaves B ε hB hε hε1

/-- LEAF. Step two of the split, the trivial character at level one. Here the
character is one on every integer, so the defect is the number of primes of
the subinterval minus the sum of the reciprocal logarithm over all integers of
it. This is the short interval prime count step of page 15. -/
theorem leaf_principal_prime_count_level_one (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) :=
  leaf_principal_prime_count_level_one_from_leaves B ε hB hε hε1

/-- LEAF. Step three of the split, the trivial character at level above one.
Here the character is one exactly on the integers coprime to the level and
zero on the others, so the defect runs over the coprime integers only, which
is the prime count of those minus the sum of the reciprocal logarithm over
them. This is the step the sealed statement reads into hypothesis A1.2 at
every level, and it is false as cut: at level two the even integers of the
window give `-1/log m` and no prime, so the centre is of size
`windowY X ε / log X` where the right side is `windowY X ε` over a positive
power of `log X`. -/
theorem leaf_principal_prime_count_level_exceeding_one (B ε : ℝ) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => (u ≤ (m : ℝ) ∧ (m : ℝ) < v) ∧ m.Coprime q),
            ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  sorry

/-- The three leaves above, assembled into the sealed statement. No sorry. -/
theorem prime_short_interval_character_split (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖primeCharacterDefect χ X (windowY X ε) u v‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  obtain ⟨C1, X1, hC1, hX1, h1⟩ := leaf_nonprincipal_prime_character_sum B ε hB hε hε1
  obtain ⟨C2, X2, hC2, hX2, h2⟩ := leaf_principal_prime_count_level_one B ε hB hε hε1
  obtain ⟨C3, X3, hC3, hX3, h3⟩ :=
    leaf_principal_prime_count_level_exceeding_one B ε hB hε hε1
  refine ⟨C1 + C2 + C3, max X1 (max X2 X3), by positivity,
    le_trans hX1 (le_max_left _ _), ?_⟩
  intro X hX q hq hqB χ u v hu huv hv
  have hX1' : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hX2' : X2 ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hX3' : X3 ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos hX0 _
  have hZ : 0 < (Real.log X ^ B) ^ (-5 : ℤ) := zpow_pos (Real.rpow_pos_of_pos hL B) _
  have hbig : ∀ a : ℝ, a ≤ C1 + C2 + C3 →
      a * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) ≤
        (C1 + C2 + C3) * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
    intro a ha
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hY.le) hZ.le
  have hone_one : ∀ m : ℕ, (1 : DirichletCharacter ℂ 1) ((m : ℕ) : ZMod 1) = 1 := by
    intro m
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime m 1).mpr (Nat.coprime_one_right m))
  have hone_above : ∀ (m : ℕ) {q : ℕ},
      (1 : DirichletCharacter ℂ q) ((m : ℕ) : ZMod q) = if m.Coprime q then 1 else 0 := by
    intro m q
    by_cases hu' : IsUnit ((m : ZMod q))
    · rw [if_pos ((ZMod.isUnit_iff_coprime m q).mp hu'), MulChar.one_apply hu']
    · rw [if_neg (fun hc => hu' ((ZMod.isUnit_iff_coprime m q).mpr hc)), MulChar.map_nonunit _ hu']
  by_cases hχ : χ = 1
  · subst hχ
    rcases Nat.eq_or_lt_of_le hq with hq1 | hq2
    · subst hq1
      have hd : primeCharacterDefect (1 : DirichletCharacter ℂ 1) X (windowY X ε) u v =
          ∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
              ((if m.Prime then (1 : ℂ) else 0) -
                ((1 / Real.log (m : ℝ) : ℝ) : ℂ)) := by
        unfold primeCharacterDefect
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [if_pos rfl, hone_one m, mul_one]
      rw [hd]
      exact (h2 X hX2' u v hu huv hv).trans (hbig C2 (by linarith))
    · have hterm : ∀ m : ℕ,
          ((if m.Prime then (1 : ℂ) else 0) -
              (if (1 : DirichletCharacter ℂ q) = 1 then
                ((1 / Real.log (m : ℝ) : ℝ) : ℂ) else 0)) *
            (1 : DirichletCharacter ℂ q) ((m : ℕ) : ZMod q) =
          (if m.Coprime q then
            ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))
            else 0) := by
        intro m
        rw [if_pos rfl, hone_above m (q := q)]
        by_cases hc : m.Coprime q
        · rw [if_pos hc]; rw [if_pos hc]
          ring
        · rw [if_neg hc]; rw [if_neg hc]
          ring
      have hd : primeCharacterDefect (1 : DirichletCharacter ℂ q) X (windowY X ε) u v =
          ∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => (u ≤ (m : ℝ) ∧ (m : ℝ) < v) ∧ m.Coprime q),
              ((if m.Prime then (1 : ℂ) else 0) -
                ((1 / Real.log (m : ℝ) : ℝ) : ℂ)) := by
        unfold primeCharacterDefect
        refine (Finset.sum_congr rfl (fun m _ => hterm m)).trans ?_
        rw [← Finset.sum_filter, Finset.filter_filter]
      rw [hd]
      exact (h3 X hX3' q (by omega) hqB u v hu huv hv).trans (hbig C3 (by linarith))
  · have hd : primeCharacterDefect χ X (windowY X ε) u v =
        ∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            (if m.Prime then χ m else 0) := by
      unfold primeCharacterDefect
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [if_neg hχ, sub_zero]
      by_cases hmp : m.Prime <;> simp [hmp]
    rw [hd]
    exact (h1 X hX1' q hq hqB χ hχ u v hu huv hv).trans (hbig C1 (by linarith))

/-! ### The reading of the sealed statement is refuted

The sealed statement of this unit, at any `B > 1/5`, is false. The whole
window is enough: the defects of the trivial character at levels one and two
differ by minus the sum of the reciprocal logarithm over the even integers of
the window, and that sum is at least `(windowY / 2 - 1) / log X`, while the
two bounds of the sealed statement give twice a fixed constant times
`windowY` over a positive power of `log X`. No prime number theory enters.
-/

/-- Page 5 hypothesis A1.2 with page 2 display 5: on the whole interval
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

/-- page 2 display 5 and page 15 f1: the sum of f1(m) = 1 / log m over
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

/-- Page 5 hypothesis A1.2 as transcribed in
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

/-- Page 5 hypothesis A1.2 as transcribed in
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

/-- The residue class 3 modulo 6 supplies at least Y/6 - 1 reciprocal
logarithm weights. This is an elementary check on page 5 hypothesis A1.2,
with the page 15 choice of f1. -/
theorem odd_multiple_three_weight_sum_ge (X Y : ℝ) (hY : 0 ≤ Y) (h : 3 < X - Y) :
    (Y / 6 - 1) / Real.log X ≤
      ∑ m ∈ primeWindow X Y,
        (if m.Coprime 2 ∧ ¬m.Coprime 6 then 1 / Real.log (m : ℝ) else 0 : ℝ) := by
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hmem : ∀ k ∈ Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊,
      X - Y ≤ ((6 * k + 3 : ℕ) : ℝ) ∧ ((6 * k + 3 : ℕ) : ℝ) < X := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have h1 : (X - Y - 3) / 6 ≤ (k : ℝ) := Nat.ceil_le.mp hk1
    have h2 : (k : ℝ) < (X - 3) / 6 := Nat.lt_ceil.mp hk2
    push_cast
    constructor <;> linarith
  have hclass : ∀ k : ℕ, (6 * k + 3).Coprime 2 ∧ ¬(6 * k + 3).Coprime 6 := by
    intro k
    constructor
    · exact Nat.coprime_two_right.mpr ⟨3 * k + 1, by omega⟩
    · intro hc
      have hc3 := ((Nat.coprime_mul_iff_right (m := 2) (n := 3)).mp hc).2
      have hd : 3 ∣ 6 * k + 3 := ⟨2 * k + 1, by omega⟩
      exact (Nat.prime_three.coprime_iff_not_dvd.mp hc3.symm) hd
  have hsub :
      (Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊).image
          (fun k : ℕ => 6 * k + 3) ⊆ primeWindow X Y := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨h1, h2⟩ := hmem k hk
    simp only [primeWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2.le), h1, h2⟩
  have hcard : Y / 6 - 1 ≤
      ((⌈(X - 3) / 6⌉₊ - ⌈(X - Y - 3) / 6⌉₊ : ℕ) : ℝ) := by
    have hb : (X - 3) / 6 ≤ (⌈(X - 3) / 6⌉₊ : ℝ) := Nat.le_ceil _
    have ha : (⌈(X - Y - 3) / 6⌉₊ : ℝ) < (X - Y - 3) / 6 + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have hn : ⌈(X - 3) / 6⌉₊ ≤
        (⌈(X - 3) / 6⌉₊ - ⌈(X - Y - 3) / 6⌉₊) + ⌈(X - Y - 3) / 6⌉₊ := by omega
    have hn' : (⌈(X - 3) / 6⌉₊ : ℝ) ≤
        ((⌈(X - 3) / 6⌉₊ - ⌈(X - Y - 3) / 6⌉₊ : ℕ) : ℝ) +
          (⌈(X - Y - 3) / 6⌉₊ : ℝ) := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∑ _k ∈ Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊,
        1 / Real.log X := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one_div]
      exact div_le_div_of_nonneg_right hcard hL.le
    _ ≤ ∑ k ∈ Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊,
        (if (6 * k + 3).Coprime 2 ∧ ¬(6 * k + 3).Coprime 6 then
          1 / Real.log ((6 * k + 3 : ℕ) : ℝ) else 0 : ℝ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      obtain ⟨h1, h2⟩ := hmem k hk
      rw [ite_eq_left (hclass k)]
      exact one_div_le_one_div_of_le (Real.log_pos (by linarith))
        (Real.log_le_log (by linarith) h2.le)
    _ = ∑ m ∈ (Finset.Ico ⌈(X - Y - 3) / 6⌉₊ ⌈(X - 3) / 6⌉₊).image
        (fun k : ℕ => 6 * k + 3),
        (if m.Coprime 2 ∧ ¬m.Coprime 6 then 1 / Real.log (m : ℝ) else 0 : ℝ) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      dsimp only at hxy
      omega
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => ?_
      split_ifs
      · have hm' := (Finset.mem_filter.mp hm).2
        exact le_of_lt (one_div_pos.mpr (Real.log_pos (by linarith [hm'.1])))
      · exact le_rfl

/-- For the whole window above 3, subtracting the coprime-level-six sum
from the coprime-level-two sum cancels every prime. Only the negative
reciprocal logarithms on the residue class 3 modulo 6 remain. -/
theorem principal_two_six_sum_diff (X Y : ℝ) (h : 3 < X - Y) :
    (∑ m ∈ (primeWindow X Y).filter
        (fun m : ℕ => ((X - Y ≤ (m : ℝ)) ∧ (m : ℝ) < X) ∧ m.Coprime 2),
        ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))) -
      (∑ m ∈ (primeWindow X Y).filter
        (fun m : ℕ => ((X - Y ≤ (m : ℝ)) ∧ (m : ℝ) < X) ∧ m.Coprime 6),
        ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))) =
      -∑ m ∈ primeWindow X Y,
        ((if m.Coprime 2 ∧ ¬m.Coprime 6 then
          1 / Real.log (m : ℝ) else 0 : ℝ) : ℂ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := (Finset.mem_filter.mp hm).2
  have hm3 : 3 < m := by exact_mod_cast (show (3 : ℝ) < (m : ℝ) by linarith [hm'.1])
  have hc : m.Coprime 6 → m.Coprime 2 := fun hc =>
    ((Nat.coprime_mul_iff_right (m := 2) (n := 3)).mp hc).1
  simp only [hm', true_and]
  by_cases hp : m.Prime
  · have hc2 : m.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
      omega)
    have hc3 : m.Coprime 3 := hp.coprime_iff_not_dvd.mpr (by
      intro hd
      have := Nat.le_of_dvd (by norm_num : 0 < 3) hd
      omega)
    have hc6 : m.Coprime 6 := Nat.coprime_mul_iff_right.mpr ⟨hc2, hc3⟩
    rw [ite_eq_left hc2, ite_eq_left hc6,
      ite_eq_right (show ¬(m.Coprime 2 ∧ ¬m.Coprime 6) from fun h => h.2 hc6)]
    simp only [sub_self, Complex.ofReal_zero, neg_zero]
  · by_cases hc2 : m.Coprime 2
    · by_cases hc6 : m.Coprime 6
      · rw [ite_eq_left hc2, ite_eq_left hc6,
          ite_eq_right (show ¬(m.Coprime 2 ∧ ¬m.Coprime 6) from fun h => h.2 hc6)]
        simp only [sub_self, Complex.ofReal_zero, neg_zero]
      · rw [ite_eq_left hc2, ite_eq_right hc6, ite_eq_right hp,
          ite_eq_left (show m.Coprime 2 ∧ ¬m.Coprime 6 from ⟨hc2, hc6⟩)]
        simp only [zero_sub, sub_zero]
    · have hc6 : ¬m.Coprime 6 := fun h6 => hc2 (hc h6)
      rw [ite_eq_right hc2, ite_eq_right hc6,
        ite_eq_right (show ¬(m.Coprime 2 ∧ ¬m.Coprime 6) from fun h => hc2 h.1)]
      simp only [sub_self, Complex.ofReal_zero, neg_zero]

/-- A standalone refutation of the third leaf for every B > 1/5.
Levels 2 and 6 alone contradict its bound, without a prime number theorem
or either of the other leaves. The concrete instance is B = 1, epsilon =
1/10 and the full window at one of these two levels. -/
theorem principal_prime_count_level_exceeding_one_fails (B ε : ℝ) (hB : 1 / 5 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 36) :
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
        ((Filter.eventually_ge_atTop X0).and (Filter.eventually_ge_atTop (8 : ℝ))))))).exists
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
  have hdiff := principal_two_six_sum_diff X (windowY X ε) hYX
  have hlow := odd_multiple_three_weight_sum_ge X (windowY X ε) (by linarith) hYX
  have hnorm : (windowY X ε / 6 - 1) / Real.log X ≤
      2 * (C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ)) := by
    have habs : (∑ m ∈ primeWindow X (windowY X ε),
        (if m.Coprime 2 ∧ ¬m.Coprime 6 then 1 / Real.log (m : ℝ) else 0 : ℝ)) ≤
        ‖-∑ m ∈ primeWindow X (windowY X ε),
          ((if m.Coprime 2 ∧ ¬m.Coprime 6 then
            1 / Real.log (m : ℝ) else 0 : ℝ) : ℂ)‖ := by
      rw [norm_neg, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    rw [← hdiff] at habs
    exact hlow.trans (habs.trans ((norm_sub_le _ _).trans (by linarith)))
  have hTL : Real.log X ^ (5 * B - 1) * Real.log X = (Real.log X ^ B) ^ (5 : ℕ) := by
    calc
      _ = Real.log X ^ (5 * B - 1) * Real.log X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = Real.log X ^ (5 * B - 1 + 1) := (Real.rpow_add hL _ _).symm
      _ = Real.log X ^ (B * ((5 : ℕ) : ℝ)) := by congr 1; push_cast; ring
      _ = _ := by rw [Real.rpow_mul hL.le, Real.rpow_natCast]
  have hT : 0 < Real.log X ^ (5 * B - 1) := Real.rpow_pos_of_pos hL _
  rw [zpow_neg, zpow_ofNat, ← hTL, div_le_iff₀ hL] at hnorm
  have hfin : 2 * (C * windowY X ε * (Real.log X ^ (5 * B - 1) * Real.log X)⁻¹) *
      Real.log X = 2 * C * windowY X ε / Real.log X ^ (5 * B - 1) := by field_simp
  rw [hfin, le_div_iff₀ hT] at hnorm
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ windowY X ε / 12 - 1 by linarith) hT.le,
    mul_pos (show (0 : ℝ) < windowY X ε by linarith)
      (show (0 : ℝ) < Real.log X ^ (5 * B - 1) - 24 * C by linarith)]

end LeanLab.KumchevLiu2007.Task556a
