import Mathlib
import LeanLab.Zhao2025.Zhao2025U6901Grid
import LeanLab.Zhao2025.Zhao2025U6904Wide

/-!
# Zhao 2025, certified (3.27) with any top `Λ_M` and step count `M`, tail from (3.16)

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6904, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

As `T_of_326` of U-6901, but the grid runs from `Λ₀` to any `top ≥ 5.2` in `M` steps, and the tail
is `T(top) ≤ 100 e^{-2.22 top}`, Zhao's (3.16), taken as the hypothesis `h316`.  The exact tail
`100 e^{-2.22 · 5.2} ≈ 0.00096` replaces the rounded `0.001`, and `top = 5.68` is the fix of F-5011
that Zhao confirmed by email.

* `T_of_326_316`, CONDITIONAL ON (3.26) as `h326` with `0 ≤ ε ≤ 10⁻⁸` and (3.16) as `h316`.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6841

/-- Grid data for one (3.27) evaluation with its own top and step count. -/
structure GridData2 where
  l0 : ℚ
  L0 : ℚ
  h : ℚ
  M : ℕ
  top : ℚ
  n0 : ℕ
  jumps : List ℕ
  wx : List (ℕ × ℚ)
  q : ℚ
  r : ℚ
  target : ℚ

/-- Every count is certified at its witness grid point. -/
def gridChk2 (d : GridData2) : Bool :=
  decide (d.L0 + (d.M : ℚ) * d.h = d.top) && decide (0 < d.h) && decide (26 / 5 ≤ d.top) &&
  decide (1 ≤ d.M) && (List.range (d.M + 1)).all (fun k =>
    decide (k ≤ (d.wx.getD k (0, 1)).1) && decide ((d.wx.getD k (0, 1)).1 ≤ d.M) &&
    chkW d.l0 (d.L0 + ((d.wx.getD k (0, 1)).1 : ℚ) * d.h) (d.wx.getD k (0, 1)).2
      (cntOf d.n0 d.jumps k))

/-- The (3.27) sum with `r`, `q` is at most the target. -/
def sumChk2 (d : GridData2) : Bool :=
  decide (0 ≤ d.L0) && decide (0 ≤ d.q) && decide (eupq (10 / 3 * d.h) ≤ d.q) &&
  decide (eupq (10 / 3 * d.L0) ≤ d.r) &&
  decide (0 ≤ d.top) && decide (d.r * ((d.n0 : ℚ) + ∑ k ∈ Finset.range d.M, (d.jumps.getD k 0 : ℚ) * d.q ^ k) +
    100 * eupq (111 / 50 * d.top) ≤ d.target)

/-- CONDITIONAL ON Zhao (3.26) as `h326` with `0 ≤ ε ≤ 10⁻⁸` and on (3.16) at `top` as `h316`:
for grid data passing both kernel checks, `T(Λ₀) ≤ target`. -/
theorem T_of_326_316 (d : GridData2) (hg : gridChk2 d = true) (hs : sumChk2 d = true)
    {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 8)
    (h326 : ∀ L x : ℝ, (d.L0 : ℝ) ≤ L → L ≤ d.top → 4 * (d.l0 : ℝ) / 5 ≤ x →
      0 < Delta x L d.l0 → ε < Delta x L d.l0 ^ 2 →
      (((s.filter (fun j => lam j ≤ L)).card : ℕ) : ℝ) ≤ 1 / (Delta x L d.l0 ^ 2 - ε))
    (h316 : Tsum s lam d.top ≤ 100 * Real.exp (-(2.22 * (d.top : ℝ)))) :
    Tsum s lam d.L0 ≤ d.target := by
  simp only [gridChk2, sumChk2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hg hs
  obtain ⟨⟨⟨⟨hsumM, hh⟩, htop⟩, hM1⟩, hall⟩ := hg
  obtain ⟨⟨⟨⟨⟨hL0, hq0⟩, hq⟩, hr⟩, htop0⟩, hfin⟩ := hs
  obtain ⟨m, hm⟩ : ∃ m, d.M = m + 1 := ⟨d.M - 1, by omega⟩
  have hhR : (0 : ℝ) < d.h := by exact_mod_cast hh
  have hMR : (d.L0 : ℝ) + (m + 1 : ℕ) * d.h = d.top := by
    have : ((d.L0 + (d.M : ℚ) * d.h : ℚ) : ℝ) = ((d.top : ℚ) : ℝ) := by rw [hsumM]
    rw [hm] at this; push_cast at this ⊢; linarith
  set f : ℝ → ℝ := fun y => Real.exp (-(10 / 3 * y)) with hfdef
  have hf : Antitone f := by
    intro a b hab; simp only [hfdef]; apply Real.exp_le_exp.mpr; linarith
  have hf0 : ∀ y, 0 ≤ f y := fun y => (Real.exp_pos _).le
  set Λ : ℕ → ℝ := fun i => (d.L0 : ℝ) + i * d.h with hΛdef
  have hΛ : Monotone Λ := by
    intro a b hab; simp only [hΛdef]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hΛM : Λ (m + 1) = d.top := by simp only [hΛdef]; exact hMR
  have hΛ0 : Λ 0 = d.L0 := by simp only [hΛdef]; simp
  set Ncount : ℝ → ℕ := fun L => (s.filter (fun j => lam j ≤ L)).card with hNdef
  have hNmono : ∀ a b : ℝ, a ≤ b → Ncount a ≤ Ncount b := by
    intro a b hab
    exact Finset.card_le_card (fun j hj => by
      simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.trans hab⟩)
  have hcount : ∀ i, 1 ≤ i → i ≤ m + 1 →
      (((s.filter (fun j => lam j ≤ Λ i)).card : ℕ) : ℝ) ≤ ((cntOf d.n0 d.jumps i : ℕ) : ℝ) := by
    intro i _ hi
    obtain ⟨⟨hji, hjM⟩, hc⟩ := hall i (by omega)
    set j := (d.wx.getD i (0, 1)).1
    set x := (d.wx.getD i (0, 1)).2
    obtain ⟨hx, hD, hε', hlt⟩ := chkW_sound _ _ _ _ hc ε hε
    have eL : (((d.L0 + (j : ℚ) * d.h) : ℚ) : ℝ) = Λ j := by simp only [hΛdef]; push_cast; ring
    rw [eL] at hε' hlt hD
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hlo : (d.L0 : ℝ) ≤ Λ j := by simp only [hΛdef]; nlinarith
    have hhi : Λ j ≤ d.top := by rw [← hΛM]; exact hΛ (by omega)
    have h1 := h326 (Λ j) x hlo hhi hx hD hε'
    have h2 : (Ncount (Λ j) : ℝ) < cntOf d.n0 d.jumps i + 1 := lt_of_le_of_lt h1 hlt
    have h3 : Ncount (Λ j) ≤ cntOf d.n0 d.jumps i := by
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h2)
    have h4 := hNmono (Λ i) (Λ j) (hΛ hji)
    exact_mod_cast h4.trans h3
  have hmain := sum_bound s lam f hf hf0 Λ hΛ m (fun i => ((cntOf d.n0 d.jumps i : ℕ) : ℝ)) hcount
  rw [abel_identity (fun i => f (Λ i)) (fun i => ((cntOf d.n0 d.jumps i : ℕ) : ℝ)) m] at hmain
  simp only [cntOf_succ] at hmain
  have hr' : f (Λ 0) ≤ (d.r : ℝ) := by
    rw [hΛ0]; simp only [hfdef]
    have := eupq_ge (10 / 3 * d.L0) (by positivity)
    have hr2 : ((eupq (10 / 3 * d.L0) : ℚ) : ℝ) ≤ (d.r : ℝ) := by exact_mod_cast hr
    push_cast at this; linarith
  have hqR : Real.exp (-(10 / 3 * (d.h : ℝ))) ≤ (d.q : ℝ) := by
    have := eupq_ge (10 / 3 * d.h) (by positivity)
    have hq2 : ((eupq (10 / 3 * d.h) : ℚ) : ℝ) ≤ (d.q : ℝ) := by exact_mod_cast hq
    push_cast at this; linarith
  have hfΛ : ∀ i : ℕ, f (Λ i) = f (Λ 0) * Real.exp (-(10 / 3 * (d.h : ℝ))) ^ i := by
    intro i; simp only [hfdef, hΛdef]
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hfΛle : ∀ i : ℕ, f (Λ i) ≤ (d.r : ℝ) * (d.q : ℝ) ^ i := by
    intro i; rw [hfΛ i]
    exact mul_le_mul hr' (pow_le_pow_left₀ (Real.exp_pos _).le hqR i) (by positivity)
      (le_trans (hf0 _) hr')
  have htailR : 100 * Real.exp (-(2.22 * (d.top : ℝ))) ≤ 100 * ((eupq (111 / 50 * d.top) : ℚ) : ℝ) := by
    have := eupq_ge (111 / 50 * d.top) (by positivity)
    push_cast at this
    have e : (111 / 50 : ℝ) * d.top = 2.22 * d.top := by norm_num
    rw [e] at this; linarith
  have hbound : ((d.n0 : ℕ) : ℝ) * f (Λ 0) + ∑ i ∈ Finset.range (m + 1),
      (d.jumps.getD i 0 : ℝ) * f (Λ i) ≤
        (d.target : ℝ) - 100 * ((eupq (111 / 50 * d.top) : ℚ) : ℝ) := by
    have hfin' : ((d.r * ((d.n0 : ℚ) + ∑ k ∈ Finset.range d.M, (d.jumps.getD k 0 : ℚ) * d.q ^ k)
        + 100 * eupq (111 / 50 * d.top) : ℚ) : ℝ) ≤ (d.target : ℝ) := by exact_mod_cast hfin
    rw [hm] at hfin'
    push_cast at hfin'
    have e1 : ((d.n0 : ℕ) : ℝ) * f (Λ 0) ≤ (d.n0 : ℝ) * (d.r : ℝ) :=
      mul_le_mul_of_nonneg_left hr' (Nat.cast_nonneg _)
    have e2 : ∑ i ∈ Finset.range (m + 1), (d.jumps.getD i 0 : ℝ) * f (Λ i) ≤
        ∑ i ∈ Finset.range (m + 1), (d.jumps.getD i 0 : ℝ) * ((d.r : ℝ) * (d.q : ℝ) ^ i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfΛle i) (Nat.cast_nonneg _))
    have e3 : ∑ i ∈ Finset.range (m + 1), (d.jumps.getD i 0 : ℝ) * ((d.r : ℝ) * (d.q : ℝ) ^ i) =
        (d.r : ℝ) * ∑ i ∈ Finset.range (m + 1), (d.jumps.getD i 0 : ℝ) * (d.q : ℝ) ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e3] at e2
    have : (d.r : ℝ) * ((d.n0 : ℝ) + ∑ k ∈ Finset.range (m + 1), (d.jumps.getD k 0 : ℝ) * (d.q : ℝ) ^ k)
        = (d.n0 : ℝ) * d.r + (d.r : ℝ) * ∑ i ∈ Finset.range (m + 1), (d.jumps.getD i 0 : ℝ) * (d.q : ℝ) ^ i := by
      ring
    linarith
  have hcnt0 : ((cntOf d.n0 d.jumps 0 : ℕ) : ℝ) = (d.n0 : ℝ) := by simp [cntOf]
  rw [hcnt0] at hmain
  have htail : ∑ j ∈ s.filter (fun j => ¬ lam j ≤ Λ (m + 1)), f (max (lam j) (Λ 0)) ≤
      100 * Real.exp (-(2.22 * (d.top : ℝ))) := by
    calc _ = ∑ j ∈ s.filter (fun j => ¬ lam j ≤ Λ (m + 1)), f (max (lam j) d.top) := by
          apply Finset.sum_congr rfl
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          push Not at h
          rw [hΛM] at h
          have : Λ 0 ≤ d.top := by rw [← hΛM]; exact hΛ (Nat.zero_le _)
          rw [max_eq_left (by linarith), max_eq_left h.le]
      _ ≤ ∑ j ∈ s, f (max (lam j) d.top) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hf0 _)
      _ ≤ _ := h316
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun j => lam j ≤ Λ (m + 1))
    (fun j => f (max (lam j) (Λ 0)))
  unfold Tsum
  rw [hΛ0] at hsplit
  simp only [hfdef] at hsplit htail hmain hbound
  rw [hΛ0] at hmain htail hbound
  linarith

end LeanLab.Zhao2025.U6900
