/-
Unit U-1610, run 20261103T0803Z-22341. Refutations of the old statements of `DecompJ200`,
spelled here as Props since the file now holds the repaired forms, and vacuity instances.

* `old_split_false`: gamma 0, M 1, the old `Eγ_minor_dyadic` and `Eγ_major_dyadic` were `0`.
* `old_sum_false`: gamma = log log 6 / log log 2, N 1: `n = 1` has no solution, it lies in no
  block `(i, 2i]`, and `n = 2` has `F = 6 = 3 + 3`.
* `old_sum_exp_false`: gamma 5/4, c = C = 1 refutes every c', C'.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.DecompJ200

namespace LeanLab.ExceptionalSet.Audit1610

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998
open LeanLab.ExceptionalSet.DecompJ200

attribute [local instance] Classical.propDecidable

/-- The old block `(M, 2M]`. -/
noncomputable def oldDyadic (γ : ℝ) (M : ℕ) : ℕ :=
  ((Finset.Ioc M (2 * M)).filter (fun n => ¬ Solvable γ n)).card

/-- The old `leaf_dyadic_split`, with its two definitions unfolded to `0`. -/
def OldSplit : Prop := ∀ (γ : ℝ) (M : ℕ), (oldDyadic γ M : ℝ) ≤ 0 + 0

/-- The old `leaf_dyadic_sum`. -/
def OldSum : Prop := ∀ (γ : ℝ) (N : ℕ),
  (Eγ γ N : ℝ) ≤ ∑ i ∈ Finset.Ioc 0 N, (oldDyadic γ i : ℝ)

/-- The old `leaf_dyadic_sum_exp`. -/
def OldSumExp : Prop := ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ c C : ℝ, 0 < c → 0 < C →
  ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
    (∑ M ∈ Finset.Ioc 0 N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ)
      ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ))

/-- Two odd primes sum to at least `6`, so a target below `3` has no solution. -/
theorem not_solvable_of_lt {γ : ℝ} {n : ℕ} (h : F γ n < 3) : ¬ Solvable γ n := by
  rintro ⟨p₁, p₂, hp₁, hp₂, ho₁, ho₂, habs⟩
  have h3 : ∀ p : ℕ, p.Prime → Odd p → 3 ≤ p := by
    intro p hp ho
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · have : p = 2 := by omega
      subst this
      exact absurd ho (by decide)
    · exact hge
  have h6 : (6 : ℝ) ≤ ((p₁ + p₂ : ℕ) : ℝ) := by
    have := h3 p₁ hp₁ ho₁
    have := h3 p₂ hp₂ ho₂
    exact_mod_cast (by omega : 6 ≤ p₁ + p₂)
  have := (abs_lt.mp habs).2
  linarith

theorem old_split_false : ¬ OldSplit := by
  intro h
  have hcard := h 0 1
  have hmem : (2 : ℕ) ∈ (Finset.Ioc 1 (2 * 1)).filter (fun n => ¬ Solvable 0 n) := by
    refine Finset.mem_filter.mpr ⟨by simp, not_solvable_of_lt ?_⟩
    simp only [F, Real.rpow_zero]
    have := Real.exp_one_lt_d9
    linarith
  have hpos : 0 < oldDyadic 0 1 := Finset.card_pos.mpr ⟨2, hmem⟩
  have : (0 : ℝ) < oldDyadic 0 1 := by exact_mod_cast hpos
  linarith

theorem old_sum_false : ¬ OldSum := by
  intro h
  set γ : ℝ := Real.log (Real.log 6) / Real.log (Real.log 2) with hγ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog21 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hll2 : Real.log (Real.log 2) ≠ 0 := (Real.log_neg hlog2 hlog21).ne
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hF2 : F γ (2 : ℕ) = 6 := by
    simp only [F]
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this, Real.rpow_def_of_pos hlog2, hγ, mul_div_cancel₀ _ hll2, Real.exp_log hlog6,
      Real.exp_log (by norm_num)]
  have hsolv : Solvable γ 2 := by
    refine ⟨3, 3, by norm_num, by norm_num, by decide, by decide, ?_⟩
    rw [hF2]
    norm_num
  have hdy : oldDyadic γ 1 = 0 := by
    unfold oldDyadic
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn hb
    have hn' := Finset.mem_Ioc.mp hn
    have : n = 2 := by omega
    subst this
    exact hb hsolv
  have hE : 1 ≤ Eγ γ 1 := by
    refine Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨by simp, not_solvable_of_lt ?_⟩⟩
    have hle : F γ (1 : ℕ) ≤ Real.exp 1 := by
      simp only [F, Nat.cast_one, Real.log_one]
      apply Real.exp_le_exp.mpr
      rcases eq_or_ne γ 0 with h0 | h0
      · simp [h0]
      · simp [Real.zero_rpow h0]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := h γ 1
  have hset : Finset.Ioc 0 1 = {1} := by decide
  rw [hset, Finset.sum_singleton, hdy] at h1
  have : (1 : ℝ) ≤ Eγ γ 1 := by exact_mod_cast hE
  norm_num at h1
  linarith

lemma two_sum_Ioc (N : ℕ) : 2 * ∑ M ∈ Finset.Ioc 0 N, (M : ℝ) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), mul_add, ih]
    push_cast
    ring

theorem old_sum_exp_false : ¬ OldSumExp := by
  intro h
  obtain ⟨c', hc', C', hC', hb⟩ := h (5 / 4) (by norm_num) (by norm_num) 1 1 one_pos one_pos
  have hexp : (3 - 2 * (5 / 4) : ℝ) = 1 / 2 := by norm_num
  rw [hexp] at hb
  set A : ℝ := |1 - c'| + 1 with hA
  set E : ℝ := Real.exp (A ^ 2 / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  obtain ⟨N, hN⟩ := exists_nat_gt (max 2 (4 * C' ^ 2 * E ^ 2))
  have hN2 : (2 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 4 * C' ^ 2 * E ^ 2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNnat : 2 ≤ N := by
    have : (2 : ℕ) < N := by exact_mod_cast hN2
    omega
  have hNpos : (0 : ℝ) < N := by linarith
  set L : ℝ := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  set a : ℝ := L ^ (1 / 2 : ℝ) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hL0 _
  have ha2 : a ^ 2 = L := by
    rw [ha, ← Real.sqrt_eq_rpow, Real.sq_sqrt hL0]
  have hterm : ∀ M ∈ Finset.Ioc 0 N, (M : ℝ) * Real.exp (-a) ≤
      1 * M * Real.exp (-1 * Real.log M ^ (1 / 2 : ℝ)) := by
    intro M hM
    obtain ⟨hM0, hMN⟩ := Finset.mem_Ioc.mp hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
    have hlog : Real.log M ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hMN)
    have hrp : Real.log M ^ (1 / 2 : ℝ) ≤ a :=
      Real.rpow_le_rpow (Real.log_nonneg hM1) hlog (by norm_num)
    have : Real.exp (-a) ≤ Real.exp (-1 * Real.log M ^ (1 / 2 : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [one_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hmain := hsum.trans (hb N hNnat)
  have hsumval : (N : ℝ) ^ 2 / 2 ≤ ∑ M ∈ Finset.Ioc 0 N, (M : ℝ) := by
    have := two_sum_Ioc N
    nlinarith
  have h1 : (N : ℝ) ^ 2 / 2 * Real.exp (-a) ≤ C' * N * Real.exp (-c' * a) :=
    (mul_le_mul_of_nonneg_right hsumval (Real.exp_pos _).le).trans hmain
  -- divide by `N exp(-a)`
  have h2 : (N : ℝ) / 2 ≤ C' * Real.exp ((1 - c') * a) := by
    have hexp : Real.exp (-c' * a) = Real.exp (-a) * Real.exp ((1 - c') * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at h1
    have hpos : 0 < (N : ℝ) * Real.exp (-a) := mul_pos hNpos (Real.exp_pos _)
    have : (N : ℝ) * Real.exp (-a) * ((N : ℝ) / 2) ≤
        (N : ℝ) * Real.exp (-a) * (C' * Real.exp ((1 - c') * a)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hpos
  set s : ℝ := Real.exp (L / 2) with hs
  have hspos : 0 < s := Real.exp_pos _
  have hs2 : s ^ 2 = N := by
    rw [hs, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (L / 2) = L := by push_cast; ring
    rw [this, hL, Real.exp_log hNpos]
  have h3 : Real.exp ((1 - c') * a) ≤ s * E := by
    rw [hs, hE, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hle : (1 - c') * a ≤ A * a :=
      mul_le_mul_of_nonneg_right (by rw [hA]; linarith [le_abs_self (1 - c')]) ha0
    nlinarith [sq_nonneg (a - A)]
  have h4 : s ^ 2 / 2 ≤ C' * (s * E) := by
    rw [hs2]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hC'.le)
  have h5 : s ≤ 2 * C' * E := by
    have : s * s ≤ s * (2 * C' * E) := by nlinarith
    exact le_of_mul_le_mul_left this hspos
  have h6 : s ^ 2 ≤ (2 * C' * E) ^ 2 := pow_le_pow_left₀ hspos.le h5 2
  rw [hs2] at h6
  nlinarith

/-! ### Vacuity instances -/

/-- The hypotheses of `leaf_dyadic_split` hold at gamma 5/4, delta 1/200, kappa 1, c₀ 1. -/
theorem split_hypotheses : (1 : ℝ) < 5 / 4 ∧ (5 / 4 : ℝ) < 3 / 2 ∧ (0 : ℝ) < 1 / 200 ∧
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 := by norm_num

/-- The hypothesis of `leaf_block_dissection` holds for the empty set of integers. -/
theorem dissection_hypothesis_empty (γ : ℝ) :
    ∀ N : ℕ, 0 ≤ N → (blockCount γ (fun _ => False) N : ℝ) ≤
      1 * N * U1539.calE γ 1 N ^ (-(1 / 12 : ℝ)) := by
  intro N _
  have h0 : blockCount γ (fun _ => False) N = 0 := by simp [blockCount]
  rw [h0]
  have : 0 ≤ U1539.calE γ 1 N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  push_cast
  positivity

/-- The window is not empty for large arguments at gamma 5/4: `N` itself lies in it. -/
theorem self_mem_window (N : ℕ) (hF : 2 ≤ F (5 / 4) N) : N ∈ window (5 / 4) N := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
  · have := Int.lt_floor_add_one (F (5 / 4) N)
    show F (5 / 4) N / 2 < (⌊F (5 / 4) N⌋ : ℝ)
    linarith
  · exact Int.floor_le _

end LeanLab.ExceptionalSet.Audit1610
