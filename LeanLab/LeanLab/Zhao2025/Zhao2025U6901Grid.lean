import Mathlib
import LeanLab.Zhao2025.Zhao2025U6900Abel

/-!
# Zhao 2025, a generic certified (3.27): `T(Λ₀) ≤ target` from (3.26) and (3.20) for any grid data

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2,
a preprint.  Unit U-6901, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.  Binary Goldbach is open.

A `GridData` holds `λ₀`, `Λ₀`, the step `h` with `Λ₀ + 200 h = 5.2`, the integer counts as `n₀` and
their jumps, for each `k ≤ 200` a witness index `jₖ ≥ k` and a rational `xₖ`, rational upper
bounds `r ≥ e^{-(10/3)Λ₀}`, `q ≥ e^{-(10/3)h}`, and the target.  `gridChk` and `sumChk` are kernel
computations over `ℚ`.

* `T_of_326`, CONDITIONAL ON Zhao (3.26), Pintz's Theorem I, as `h326` with `0 ≤ ε ≤ 10⁻⁸`, and on
  (3.20) as `h320`: if both checks pass, `T(Λ₀) ≤ target` for any finite family of `λⱼ`.
  The counts use the right minimum: `N(Λₖ) ≤ N(Λ_{jₖ}) ≤ nₖ`.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6841

/-- Grid data for one (3.27) evaluation. -/
structure GridData where
  l0 : ℚ
  L0 : ℚ
  h : ℚ
  n0 : ℕ
  jumps : List ℕ
  wx : List (ℕ × ℚ)
  q : ℚ
  r : ℚ
  target : ℚ

/-- The counts `n₀`, `n_{k+1} = nₖ + jumpsₖ`. -/
def cntOf (n0 : ℕ) (js : List ℕ) : ℕ → ℕ
  | 0 => n0
  | k + 1 => cntOf n0 js k + js.getD k 0

/-- The upper Taylor enclosure of `e^{-a}` over `ℚ`, valid for `0 ≤ a`. -/
def eupq (a : ℚ) : ℚ := ((T15q (a / 8)) ^ 8)⁻¹

/-- Every count is certified at its witness grid point. -/
def gridChk (d : GridData) : Bool :=
  decide (d.L0 + 200 * d.h = 26 / 5) && decide (0 < d.h) &&
  (List.range 201).all (fun k =>
    decide (k ≤ (d.wx.getD k (0, 1)).1) && decide ((d.wx.getD k (0, 1)).1 ≤ 200) &&
    chk d.l0 (d.L0 + ((d.wx.getD k (0, 1)).1 : ℚ) * d.h) (d.wx.getD k (0, 1)).2
      (cntOf d.n0 d.jumps k))

/-- The (3.27) sum with `r`, `q` is at most the target. -/
def sumChk (d : GridData) : Bool :=
  decide (0 ≤ d.L0) && decide (0 ≤ d.q) && decide (eupq (10 / 3 * d.h) ≤ d.q) &&
  decide (eupq (10 / 3 * d.L0) ≤ d.r) &&
  decide (d.r * ((d.n0 : ℚ) + ∑ k ∈ Finset.range 200, (d.jumps.getD k 0 : ℚ) * d.q ^ k) + 1 / 1000
    ≤ d.target)

theorem eupq_ge (a : ℚ) (h0 : 0 ≤ a) : Real.exp (-(a : ℝ)) ≤ ((eupq a : ℚ) : ℝ) := by
  have := expneg_upper (a : ℝ) (by exact_mod_cast h0)
  unfold eupq; push_cast; rw [T15q_cast]; push_cast; exact this

theorem cntOf_succ (n0 : ℕ) (js : List ℕ) (k : ℕ) :
    ((cntOf n0 js (k + 1) : ℕ) : ℝ) - (cntOf n0 js k : ℝ) = (js.getD k 0 : ℝ) := by
  simp [cntOf]

/-- CONDITIONAL ON Zhao (3.26) as `h326` with `0 ≤ ε ≤ 10⁻⁸` and on (3.20) as `h320`: for grid
data passing both kernel checks, `T(Λ₀) ≤ target`. -/
theorem T_of_326 (d : GridData) (hg : gridChk d = true) (hs : sumChk d = true)
    {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 8)
    (h326 : ∀ L x : ℝ, (d.L0 : ℝ) ≤ L → L ≤ 5.2 → 4 * (d.l0 : ℝ) / 5 ≤ x →
      0 < Delta x L d.l0 → ε < Delta x L d.l0 ^ 2 →
      (((s.filter (fun j => lam j ≤ L)).card : ℕ) : ℝ) ≤ 1 / (Delta x L d.l0 ^ 2 - ε))
    (h320 : Tsum s lam 5.2 ≤ 0.001) :
    Tsum s lam d.L0 ≤ d.target := by
  simp only [gridChk, sumChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hg hs
  obtain ⟨⟨hsum200, hh⟩, hall⟩ := hg
  obtain ⟨⟨⟨⟨hL0, hq0⟩, hq⟩, hr⟩, hfin⟩ := hs
  have hhR : (0 : ℝ) < d.h := by exact_mod_cast hh
  have h200R : (d.L0 : ℝ) + 200 * d.h = 5.2 := by
    have : ((d.L0 + 200 * d.h : ℚ) : ℝ) = ((26 / 5 : ℚ) : ℝ) := by rw [hsum200]
    push_cast at this; linarith
  set f : ℝ → ℝ := fun y => Real.exp (-(10 / 3 * y)) with hfdef
  have hf : Antitone f := by
    intro a b hab; simp only [hfdef]; apply Real.exp_le_exp.mpr; linarith
  have hf0 : ∀ y, 0 ≤ f y := fun y => (Real.exp_pos _).le
  set Λ : ℕ → ℝ := fun i => (d.L0 : ℝ) + i * d.h with hΛdef
  have hΛ : Monotone Λ := by
    intro a b hab; simp only [hΛdef]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have hΛ200 : Λ 200 = 5.2 := by simp only [hΛdef]; push_cast; linarith
  have hΛ0 : Λ 0 = d.L0 := by simp only [hΛdef]; simp
  set Ncount : ℝ → ℕ := fun L => (s.filter (fun j => lam j ≤ L)).card with hNdef
  have hNmono : ∀ a b : ℝ, a ≤ b → Ncount a ≤ Ncount b := by
    intro a b hab
    exact Finset.card_le_card (fun j hj => by
      simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.trans hab⟩)
  have hcount : ∀ i, 1 ≤ i → i ≤ 199 + 1 →
      (((s.filter (fun j => lam j ≤ Λ i)).card : ℕ) : ℝ) ≤ ((cntOf d.n0 d.jumps i : ℕ) : ℝ) := by
    intro i _ hi
    obtain ⟨⟨hji, hj200⟩, hc⟩ := hall i (by omega)
    set j := (d.wx.getD i (0, 1)).1
    set x := (d.wx.getD i (0, 1)).2
    obtain ⟨hx, hD, hε', hlt⟩ := chk_sound _ _ _ _ hc ε hε
    have eL : (((d.L0 + (j : ℚ) * d.h) : ℚ) : ℝ) = Λ j := by simp only [hΛdef]; push_cast; ring
    rw [eL] at hε' hlt hD
    have hjR : (j : ℝ) ≤ 200 := by exact_mod_cast hj200
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hlo : (d.L0 : ℝ) ≤ Λ j := by simp only [hΛdef]; nlinarith
    have hhi : Λ j ≤ 5.2 := by rw [← hΛ200]; exact hΛ hj200
    have h1 := h326 (Λ j) x hlo hhi hx hD hε'
    have h2 : (Ncount (Λ j) : ℝ) < cntOf d.n0 d.jumps i + 1 := lt_of_le_of_lt h1 hlt
    have h3 : Ncount (Λ j) ≤ cntOf d.n0 d.jumps i := by
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h2)
    have h4 := hNmono (Λ i) (Λ j) (hΛ hji)
    exact_mod_cast h4.trans h3
  have hmain := sum_bound s lam f hf hf0 Λ hΛ 199 (fun i => ((cntOf d.n0 d.jumps i : ℕ) : ℝ)) hcount
  rw [abel_identity (fun i => f (Λ i)) (fun i => ((cntOf d.n0 d.jumps i : ℕ) : ℝ)) 199] at hmain
  simp only [cntOf_succ] at hmain
  -- the weights
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
  have hbound : ((d.n0 : ℕ) : ℝ) * f (Λ 0) + ∑ i ∈ Finset.range (199 + 1),
      (d.jumps.getD i 0 : ℝ) * f (Λ i) ≤ (d.target : ℝ) - 1 / 1000 := by
    have hfin' : ((d.r * ((d.n0 : ℚ) + ∑ k ∈ Finset.range 200, (d.jumps.getD k 0 : ℚ) * d.q ^ k)
        + 1 / 1000 : ℚ) : ℝ) ≤ (d.target : ℝ) := by exact_mod_cast hfin
    push_cast at hfin'
    have e1 : ((d.n0 : ℕ) : ℝ) * f (Λ 0) ≤ (d.n0 : ℝ) * (d.r : ℝ) :=
      mul_le_mul_of_nonneg_left hr' (Nat.cast_nonneg _)
    have e2 : ∑ i ∈ Finset.range (199 + 1), (d.jumps.getD i 0 : ℝ) * f (Λ i) ≤
        ∑ i ∈ Finset.range 200, (d.jumps.getD i 0 : ℝ) * ((d.r : ℝ) * (d.q : ℝ) ^ i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfΛle i) (Nat.cast_nonneg _))
    have e3 : ∑ i ∈ Finset.range 200, (d.jumps.getD i 0 : ℝ) * ((d.r : ℝ) * (d.q : ℝ) ^ i) =
        (d.r : ℝ) * ∑ i ∈ Finset.range 200, (d.jumps.getD i 0 : ℝ) * (d.q : ℝ) ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e3] at e2
    have : (d.r : ℝ) * ((d.n0 : ℝ) + ∑ k ∈ Finset.range 200, (d.jumps.getD k 0 : ℝ) * (d.q : ℝ) ^ k)
        = (d.n0 : ℝ) * d.r + (d.r : ℝ) * ∑ i ∈ Finset.range 200, (d.jumps.getD i 0 : ℝ) * (d.q : ℝ) ^ i := by
      ring
    linarith
  have hcnt0 : ((cntOf d.n0 d.jumps 0 : ℕ) : ℝ) = (d.n0 : ℝ) := by simp [cntOf]
  rw [hcnt0] at hmain
  -- the tail above 5.2
  have htail : ∑ j ∈ s.filter (fun j => ¬ lam j ≤ Λ (199 + 1)), f (max (lam j) (Λ 0)) ≤ 0.001 := by
    calc _ = ∑ j ∈ s.filter (fun j => ¬ lam j ≤ Λ (199 + 1)), f (max (lam j) 5.2) := by
          apply Finset.sum_congr rfl
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          push Not at h
          rw [hΛ200] at h
          have : Λ 0 ≤ 5.2 := by rw [← hΛ200]; exact hΛ (Nat.zero_le _)
          rw [max_eq_left (by linarith), max_eq_left h.le]
      _ ≤ ∑ j ∈ s, f (max (lam j) 5.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hf0 _)
      _ ≤ 0.001 := h320
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun j => lam j ≤ Λ (199 + 1))
    (fun j => f (max (lam j) (Λ 0)))
  unfold Tsum
  rw [hΛ0] at hsplit
  simp only [hfdef] at hsplit htail hmain hbound
  rw [hΛ0] at hmain htail hbound
  linarith

end LeanLab.Zhao2025.U6900
