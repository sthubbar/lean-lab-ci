import Mathlib
import LeanLab.Zhao2025.Zhao2025U6900Cert

/-!
# Zhao 2025, (3.27) from (3.26): the `t₅` input of layout C with every count certified

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2,
a preprint.  Unit U-6900, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.  Binary Goldbach is open.

`T(Λ) = Σⱼ e^{-(10/3) max{λⱼ, Λ}}` is Zhao's (3.14), `N(Λ) = #{j : λⱼ ≤ Λ}` his count of (2.30),
(2.31).  Here (3.27) is proved as a theorem about any finite family of reals `λⱼ`:

* `step_bound`, `sum_bound`, `abel_identity`, PROVED: the Stieltjes step on a monotone grid, for any
  antitone nonnegative weight, and the summation by parts that turns the bound into Zhao's form.
* `t5_of_326`, CONDITIONAL ON Zhao (3.26), Pintz's Theorem I, as `h326` with `0 ≤ ε ≤ 10⁻⁸`, and on
  (3.20), `T(5.2) ≤ 0.001` from Corollary 3.2, as `h320`: `T(1.363) ≤ 0.09063` for the zero
  family, which is the layout C input `t₅` at `λ₀ = 0.857`.  This replaces U-6841's
  `t5_conditional`, whose hypothesis carried 200 uncertified float counts.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Zhao2025.U6841

/-- PROVED: for an antitone `f` and a monotone grid `Λ`, if `l ≤ Λ (m+1)` then
`f (max l (Λ 0)) ≤ f (Λ m) + Σ_{i<m} (f (Λ i) - f (Λ (i+1))) [l ≤ Λ (i+1)]`. -/
theorem step_bound (f : ℝ → ℝ) (hf : Antitone f) (Λ : ℕ → ℝ) (hΛ : Monotone Λ) :
    ∀ (m : ℕ) (l : ℝ), l ≤ Λ (m + 1) → f (max l (Λ 0)) ≤ f (Λ m) +
      ∑ i ∈ Finset.range m, (f (Λ i) - f (Λ (i + 1))) * (if l ≤ Λ (i + 1) then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro l _
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    exact hf (le_max_right _ _)
  | succ m ih =>
    intro l hl
    rw [Finset.sum_range_succ]
    by_cases h : l ≤ Λ (m + 1)
    · have := ih l h
      rw [if_pos h]; linarith
    · push Not at h
      have hz : ∑ i ∈ Finset.range m, (f (Λ i) - f (Λ (i + 1))) *
          (if l ≤ Λ (i + 1) then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi' : i + 1 ≤ m + 1 := by simp at hi; omega
        have : ¬ l ≤ Λ (i + 1) := fun h' => absurd (h'.trans (hΛ hi')) (not_le.mpr h)
        rw [if_neg this, mul_zero]
      rw [hz, if_neg (not_le.mpr h), mul_zero, zero_add, add_zero]
      exact hf (h.le.trans (le_max_left _ _))

/-- PROVED: summing `step_bound` over a finite family and bounding each count by `n`. -/
theorem sum_bound {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (f : ℝ → ℝ) (hf : Antitone f)
    (hf0 : ∀ y, 0 ≤ f y) (Λ : ℕ → ℝ) (hΛ : Monotone Λ) (m : ℕ) (n : ℕ → ℝ)
    (hN : ∀ i, 1 ≤ i → i ≤ m + 1 → (((s.filter (fun j => lam j ≤ Λ i)).card : ℕ) : ℝ) ≤ n i) :
    ∑ j ∈ s.filter (fun j => lam j ≤ Λ (m + 1)), f (max (lam j) (Λ 0)) ≤
      f (Λ m) * n (m + 1) + ∑ i ∈ Finset.range m, (f (Λ i) - f (Λ (i + 1))) * n (i + 1) := by
  set t := s.filter (fun j => lam j ≤ Λ (m + 1))
  calc ∑ j ∈ t, f (max (lam j) (Λ 0))
      ≤ ∑ j ∈ t, (f (Λ m) + ∑ i ∈ Finset.range m,
          (f (Λ i) - f (Λ (i + 1))) * (if lam j ≤ Λ (i + 1) then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact step_bound f hf Λ hΛ m (lam j) (Finset.mem_filter.mp hj).2
    _ = f (Λ m) * (t.card : ℝ) + ∑ i ∈ Finset.range m, (f (Λ i) - f (Λ (i + 1))) *
          ((t.filter (fun j => lam j ≤ Λ (i + 1))).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · simp [mul_comm]
        · apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.mul_sum, Finset.sum_boole]
    _ = f (Λ m) * ((s.filter (fun j => lam j ≤ Λ (m + 1))).card : ℝ) +
          ∑ i ∈ Finset.range m, (f (Λ i) - f (Λ (i + 1))) *
            ((s.filter (fun j => lam j ≤ Λ (i + 1))).card : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i + 1 ≤ m + 1 := by simp at hi; omega
        have hc : s.filter (fun j => lam j ≤ Λ (m + 1) ∧ lam j ≤ Λ (i + 1)) =
            s.filter (fun j => lam j ≤ Λ (i + 1)) :=
          Finset.filter_congr (fun j _ => ⟨fun h => h.2, fun h => ⟨h.trans (hΛ hi'), h⟩⟩)
        rw [Finset.filter_filter, hc]
    _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hN (m + 1) (by omega) le_rfl) (hf0 _)
        · apply Finset.sum_le_sum
          intro i hi
          have hi' : i + 1 ≤ m + 1 := by simp at hi; omega
          exact mul_le_mul_of_nonneg_left (hN (i + 1) (by omega) hi')
            (sub_nonneg.mpr (hf (hΛ (Nat.le_succ i))))

/-- PROVED: summation by parts, the by-parts form equals Zhao's form of (3.27). -/
theorem abel_identity (w n : ℕ → ℝ) : ∀ m : ℕ,
    w m * n (m + 1) + ∑ i ∈ Finset.range m, (w i - w (i + 1)) * n (i + 1) =
      n 0 * w 0 + ∑ i ∈ Finset.range (m + 1), (n (i + 1) - n i) * w i := by
  intro m
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun i => (n (i + 1) - n i) * w i)]
    linarith

/-- The (3.14) sum `T(Λ)` with weight `10/3`. -/
noncomputable def Tsum {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ j ∈ s, Real.exp (-(10 / 3 * max (lam j) L))

theorem cnt_succ (k : ℕ) : ((cnt (k + 1) : ℕ) : ℝ) - (cnt k : ℝ) = (jumps.getD k 0 : ℝ) := by
  simp [cnt]

/-- CONDITIONAL ON Zhao (3.26) as `h326`, `0 ≤ ε ≤ 10⁻⁸`, and (3.20) as `h320`:
`T(1.363) ≤ 0.09063` at `λ₀ = 0.857`, the layout C input `t₅`, for any finite zero family. -/
theorem t5_of_326 {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 8)
    (h326 : ∀ L x : ℝ, 1.363 ≤ L → L ≤ 5.2 → 4 * 0.857 / 5 ≤ x → 0 < Delta x L 0.857 →
      ε < Delta x L 0.857 ^ 2 →
      (((s.filter (fun j => lam j ≤ L)).card : ℕ) : ℝ) ≤ 1 / (Delta x L 0.857 ^ 2 - ε))
    (h320 : Tsum s lam 5.2 ≤ 0.001) :
    Tsum s lam 1.363 ≤ 0.09063 := by
  set f : ℝ → ℝ := fun y => Real.exp (-(10 / 3 * y)) with hfdef
  have hf : Antitone f := by
    intro a b hab; simp only [hfdef]; apply Real.exp_le_exp.mpr; linarith
  have hf0 : ∀ y, 0 ≤ f y := fun y => (Real.exp_pos _).le
  set Λ : ℕ → ℝ := fun i => 1.363 + i * (3.837 / 200) with hΛdef
  have hΛ : Monotone Λ := by
    intro a b hab; simp only [hΛdef]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  have h200 : Λ 200 = 5.2 := by simp only [hΛdef]; norm_num
  have hcount : ∀ i, 1 ≤ i → i ≤ 199 + 1 →
      (((s.filter (fun j => lam j ≤ Λ i)).card : ℕ) : ℝ) ≤ ((cnt i : ℕ) : ℝ) := by
    intro i _ hi
    have := count_le_of_326 ε hε (fun L => (s.filter (fun j => lam j ≤ L)).card) h326 i (by omega)
    exact_mod_cast this
  have hmain := sum_bound s lam f hf hf0 Λ hΛ 199 (fun i => ((cnt i : ℕ) : ℝ)) hcount
  rw [abel_identity (fun i => f (Λ i)) (fun i => ((cnt i : ℕ) : ℝ)) 199] at hmain
  have hsum : ((cnt 0 : ℕ) : ℝ) * f (Λ 0) + ∑ i ∈ Finset.range (199 + 1),
      (((cnt (i + 1) : ℕ) : ℝ) - (cnt i : ℝ)) * f (Λ i) = T327sum - 0.001 := by
    unfold T327sum
    simp only [cnt_succ, hfdef, hΛdef]
    norm_num
    simp [cnt]
  rw [hsum, h200] at hmain
  -- the tail above 5.2
  have htail : ∑ j ∈ s.filter (fun j => ¬ lam j ≤ 5.2), f (max (lam j) (Λ 0)) ≤ 0.001 := by
    calc _ = ∑ j ∈ s.filter (fun j => ¬ lam j ≤ 5.2), f (max (lam j) 5.2) := by
          apply Finset.sum_congr rfl
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          push Not at h
          have h0 : Λ 0 = 1.363 := by simp only [hΛdef]; norm_num
          rw [h0, max_eq_left (by linarith), max_eq_left h.le]
      _ ≤ ∑ j ∈ s, f (max (lam j) 5.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => hf0 _)
      _ ≤ 0.001 := h320
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun j => lam j ≤ 5.2)
    (fun j => f (max (lam j) (Λ 0)))
  have h0 : Λ 0 = 1.363 := by simp only [hΛdef]; norm_num
  have ht := t5_sum_le
  unfold Tsum
  rw [h0] at hsplit htail
  simp only [hfdef] at hsplit htail hmain
  rw [h0] at hmain
  linarith

/-- Vacuity: the empty family satisfies both hypotheses for any `ε`. -/
theorem t5_vacuity_empty (ε : ℝ) :
    (∀ L x : ℝ, 1.363 ≤ L → L ≤ 5.2 → 4 * 0.857 / 5 ≤ x → 0 < Delta x L 0.857 →
      ε < Delta x L 0.857 ^ 2 →
      ((((∅ : Finset ℕ).filter (fun j => (fun _ : ℕ => (0 : ℝ)) j ≤ L)).card : ℕ) : ℝ) ≤
        1 / (Delta x L 0.857 ^ 2 - ε)) ∧ Tsum (∅ : Finset ℕ) (fun _ => 0) 5.2 ≤ 0.001 := by
  refine ⟨?_, by simp [Tsum]; norm_num⟩
  intro L x _ _ _ _ h
  simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
  exact (one_div_pos.mpr (by linarith)).le

end LeanLab.Zhao2025.U6900
