import LeanLab.ChenDoubleSieve.BuchstabSharp

/-!
# A stronger Buchstab bound above three

Source: https://arxiv.org/pdf/0705.1652, page 9, Lemma 2.10.
This auxiliary bound is a new variant for rigorous integral domination.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Buchstab
open Wu04Functional (IsBuchstab)

theorem propagate_upper_from_three {ω : ℝ → ℝ} (hω : IsBuchstab ω) {c : ℝ}
    (hbase : ∀ u ∈ Icc (3 : ℝ) 4, ω u ≤ c) : ∀ u : ℝ, 3 ≤ u → ω u ≤ c := by
  have step : ∀ n : ℕ, ∀ u : ℝ, 3 ≤ u → u ≤ (n : ℝ) + 4 → ω u ≤ c := by
    intro n
    induction n with
    | zero =>
      intro u hu2 hu3
      exact hbase u ⟨hu2, by simpa using hu3⟩
    | succ n ih =>
      intro u hu2 huMax
      by_cases hsmall : u ≤ (n : ℝ) + 4
      · exact ih u hu2 hsmall
      let b : ℝ := n + 4
      have hb3 : 4 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : b ≤ u := (lt_of_not_ge hsmall).le
      have hwb : ω b ≤ c := ih b (by linarith) le_rfl
      have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc b u) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc b u) := by
        rw [uIcc_of_le hbu]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t - 1
        linarith [ht.1]
      have hFTC := integral_eq_sub_of_hasDerivAt_of_le hbu hcont
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hI : (∫ t in b..u, ω (t - 1)) ≤ (u - b) * c := by
        have hm := integral_mono_on (μ := volume) hbu hci.intervalIntegrable intervalIntegrable_const
          (fun t ht => ih (t - 1) (by linarith [ht.1]) (by
            dsimp [b] at hbu
            push_cast at huMax
            linarith [ht.2]))
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
      have hleft : b * ω b ≤ b * c := mul_le_mul_of_nonneg_left hwb (by linarith)
      have hmul : u * ω u ≤ u * c := by linarith
      by_contra hnot
      have hpos := mul_pos (show 0 < u by linarith) (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith
  intro u hu
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])


/-- A small rational logarithm certificate used at u equal three. -/
theorem log_two_le_694 : log (2 : ℝ) ≤ 694/1000 := by
  have h := (Wu04Integral.log_bounds 8 (y := 2) (by norm_num)).2
  apply h.trans
  norm_num [Wu04Integral.logUpper, Wu04Integral.logLower, Finset.sum_range_succ]

/-- The initial interval for the smaller tail constant. -/
theorem bound_three_four {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω)
    {u : ℝ} (hu : u ∈ Icc 3 4) : ω u ≤ (566/1000 : ℝ) := by
  have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc 3 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t-1)) (uIcc 3 u) := by
    rw [uIcc_of_le hu.1]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t-1
    linarith [ht.1]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1 hcont
    (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
  have hI : (∫ t in (3 : ℝ)..u, ω (t-1)) ≤ (u-3)*(5671433/10000000) := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) hu.1 hci.intervalIntegrable
      intervalIntegrable_const (fun t ht => buchstab_le_5671433 hω (by linarith [ht.1]))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have h3 := formula_two_three hω (u := 3) (by norm_num)
  norm_num at h3
  have hl := log_two_le_694
  have hmul : u*ω u ≤ u*(566/1000) := by nlinarith [hu.1, hu.2]
  exact (mul_le_mul_iff_right₀ (by linarith [hu.1] : 0 < u)).mp (by simpa [mul_comm] using hmul)

/-- A useful uniform tail bound, CONDITIONAL ON IsBuchstab only. -/
theorem buchstab_le_566 {ω : ℝ → ℝ} (hω : Wu04Functional.IsBuchstab ω)
    {u : ℝ} (hu : 3 ≤ u) : ω u ≤ (566/1000 : ℝ) :=
  propagate_upper_from_three hω (fun u hu => bound_three_four hω hu) u hu

end LeanLab.ChenDoubleSieve.Wu04Buchstab

#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.propagate_upper_from_three

#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.log_two_le_694

#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.bound_three_four

#print axioms LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_566
