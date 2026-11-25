import LeanLab.ChenDoubleSieve.Task587SharpTail
import LeanLab.ChenDoubleSieve.BuchstabBounds

/-!
Buchstab caps above three used by the window splits of Wu 2004 Lemma 5.2 page 26,
Table 1 page 30. They are the numerical values of omega from Lemma 2.10 page 9.
Source: https://arxiv.org/abs/0705.1652.
On 2 to 3 omega u = (1 + log (u - 1)) / u is at most (u - 1) / u, and the delay
equation u omega u = 3 omega 3 + integral from 3 to u of omega (t - 1) is stepped
with upper Riemann sums of that bound. No new definitions.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set
namespace LeanLab.ChenDoubleSieve.Task587.CapChain
open Wu04Functional

/-- On 2 to 3, omega u is at most (u - 1) / u, from the formula of Wu 2004 Lemma 2.10
page 9 on that interval and log y at most y - 1. -/
theorem omega_le_ratio {ω : ℝ → ℝ} (hω : IsBuchstab ω) {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    ω s ≤ (s - 1) / s := by
  rw [Wu04Buchstab.formula_two_three hω hs]
  have hl := log_le_sub_one_of_pos (show (0 : ℝ) < s - 1 by linarith [hs.1])
  exact div_le_div_of_nonneg_right (by linarith) (by linarith [hs.1])

/-- Three omega 3 = 1 + log 2 is at most 16932 / 10000, Wu 2004 Lemma 2.10 page 9. -/
theorem three_omega_three {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    3 * ω 3 ≤ (16932 / 10000 : ℝ) := by
  have h3 := Wu04Buchstab.formula_two_three hω (u := 3) (by norm_num)
  have hl := sharp_tail_log_certificates.1
  rw [h3]
  norm_num
  linarith

/-- One step of the delay equation of Wu 2004 Lemma 2.10 page 9 from a to b inside
3 to 4, with the delayed values bounded by (b - 2) / (b - 1). -/
theorem cap_step {ω : ℝ → ℝ} (hω : IsBuchstab ω) {a b P : ℝ} (h3a : 3 ≤ a) (hab : a ≤ b)
    (hb4 : b ≤ 4) (hP : a * ω a ≤ P) :
    b * ω b ≤ P + (b - a) * ((b - 2) / (b - 1)) := by
  have ha0 : 0 < a := by linarith
  have hbase : ω a ≤ P / a := by
    rw [le_div_iff₀ ha0]
    linarith
  have h := Task587.delay_affine_upper hω (a := a) (u := b) (B := P / a)
    (C := (b - 2) / (b - 1)) (by linarith) hab hbase (fun t ht => by
      have h1 := omega_le_ratio hω (s := t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : (t - 1 - 1) / (t - 1) ≤ (b - 2) / (b - 1) := by
        rw [div_le_div_iff₀ (by linarith [ht.1]) (by linarith)]
        nlinarith [ht.2]
      linarith)
  have hcancel : a * (P / a) = P := by field_simp
  linarith

/-- Omega is at most 5655 / 10000 from 3 on, Wu 2004 Lemma 2.10 page 9 values. -/
theorem cap_5655 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : (3 : ℝ) ≤ u) :
    ω u ≤ (5655 / 10000 : ℝ) :=
  (Task587.buchstab_le_5644 hω hu).trans (by norm_num)

/-- Omega is at most 564 / 1000 from 61 / 20 on, Wu 2004 Lemma 2.10 page 9 values. -/
theorem cap_564 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : (61 / 20 : ℝ) ≤ u) :
    ω u ≤ (564 / 1000 : ℝ) := by
  by_cases h35 : u ≤ (7 / 2 : ℝ)
  · have h1 := cap_step hω (a := 3) (b := 61 / 20) (by norm_num) (by norm_num) (by norm_num)
      (three_omega_three hω)
    have hB : ω (61 / 20) ≤ (5636 / 10000 : ℝ) := by norm_num at h1; linarith
    have h2 := Task587.delay_affine_upper hω (a := 61 / 20) (u := u) (B := 5636 / 10000)
      (C := 563 / 1000) (by norm_num) hu hB
      (fun t ht => Task587.buchstab_two_five_halves_le hω ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hu0 : 0 < u := by linarith
    have h3 : u * ω u ≤ u * (564 / 1000) := by nlinarith
    exact le_of_mul_le_mul_left h3 hu0
  · exact (Task587.buchstab_le_5618 hω (by linarith)).trans (by norm_num)

/-- Omega is at most 563 / 1000 from 31 / 10 on, Wu 2004 Lemma 2.10 page 9 values.
Five delay steps of width 1 / 50 from 3 reach 31 / 10. -/
theorem cap_563 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : (31 / 10 : ℝ) ≤ u) :
    ω u ≤ (563 / 1000 : ℝ) := by
  by_cases h35 : u ≤ (7 / 2 : ℝ)
  · have s1 := cap_step hω (a := 3) (b := 151 / 50) (by norm_num) (by norm_num) (by norm_num)
      (three_omega_three hω)
    have s2 := cap_step hω (a := 151 / 50) (b := 152 / 50) (by norm_num) (by norm_num)
      (by norm_num) s1
    have s3 := cap_step hω (a := 152 / 50) (b := 153 / 50) (by norm_num) (by norm_num)
      (by norm_num) s2
    have s4 := cap_step hω (a := 153 / 50) (b := 154 / 50) (by norm_num) (by norm_num)
      (by norm_num) s3
    have s5 := cap_step hω (a := 154 / 50) (b := 31 / 10) (by norm_num) (by norm_num)
      (by norm_num) s4
    have hB : ω (31 / 10) ≤ (563 / 1000 : ℝ) := by norm_num at s5; linarith
    have h2 := Task587.delay_affine_upper hω (a := 31 / 10) (u := u) (B := 563 / 1000)
      (C := 563 / 1000) (by norm_num) hu hB
      (fun t ht => Task587.buchstab_two_five_halves_le hω ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hu0 : 0 < u := by linarith
    have h3 : u * ω u ≤ u * (563 / 1000) := by nlinarith
    exact le_of_mul_le_mul_left h3 hu0
  · exact (Task587.buchstab_le_5618 hω (by linarith)).trans (by norm_num)

/-- Omega is at most 78 / 100 from 13 / 10 on: it is 1 / u on 13 / 10 to 2 and
at most 567144 / 1000000 above 2, Wu 2004 Lemma 2.10 page 9. -/
theorem cap_78 {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : (13 / 10 : ℝ) ≤ u) :
    ω u ≤ (78 / 100 : ℝ) := by
  rcases le_total u 2 with h2 | h2
  · rw [hω.2.1 u (by linarith) h2, div_le_iff₀ (by linarith)]
    linarith
  · exact (Wu04Buchstab.buchstab_le_567144 hω h2).trans (by norm_num)

end LeanLab.ChenDoubleSieve.Task587.CapChain
