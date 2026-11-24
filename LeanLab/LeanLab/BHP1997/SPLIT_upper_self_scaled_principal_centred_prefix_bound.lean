/-
Split of the OPEN leaf `upper_self_scaled_principal_centred_prefix_bound` of
SPLIT_upper_self_scaled_principal_distribution into two smaller leaves and one proved lemma, with
an assembly that carries that same statement, proved from them and using no sorry.

Source: P0069 Baker, Harman and Pintz 1997, Section 5, page 53. The raw coefficient is
b1(m) = g_m - h_m + j_m - kept part of k_m, and the displayed four term identity gives
psi(m, Y^c4) = g_m - h_m + j_m - k_m. Subtracting, b1(m) = psi(m, Y^c4) + the deleted part of k_m.
The density v1 of the page 53 display is accordingly the sum of the rough density
omega(1/c4)/c4 and the deleted Buchstab integral. The centred prefix bound therefore splits by
linearity into a rough part and a deleted part, each centred at its own density.

Lemma, PROVED here: b1 at the self scale Y = m is psi(m, m^c4) plus upperK minus upperKept.
Leaf 1, HARD: the centred prefix bound of the self scaled rough indicator at the density
omega(1/c4)/c4 over log Y.
Leaf 2, HARD: the centred prefix bound of the self scaled deleted part at the density
upperDeletedIntegral over log Y.

The defect found today in the sibling leaf upper_self_scaled_principal_trivial_character, Mathlib's
trivial character being zero on non units, does not touch this statement: no character and no
modulus occur in it. This file adds no definition, edits no existing file. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_principal_distribution

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- Proved step, page 53 of P0069: at the self scale Y = m the raw coefficient equals the rough
indicator psi(m, m^c4) plus the deleted part k_m minus its kept part. This is the subtraction of the
displayed four term identity `upper_rough_four_term` from the definition of `upperRawWeight`. -/
theorem upper_raw_weight_self_eq_rough_add_deleted (ε : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    upperRawWeight ε (m : ℝ) m =
      upperRough m ((m : ℝ) ^ (1/4+(2*(1/16-1/10^5))/8-ε)) +
        (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) := by
  have h := upper_rough_four_term ε (Y := (m : ℝ)) (by exact_mod_cast hm) m
  unfold upperC4 at h
  rw [h]
  unfold upperRawWeight
  ring

/-- LEAF: the rough part of the page 53 density of P0069, Buchstab asymptotic behind 5.17 to 5.23.
HARD, for Codex: the self scaled indicator psi(m, m^c4), weighted by log m over log Y, has on each
segment from Y to t, Y ≤ t ≤ 2Y, mass omega(1/c4)/c4 over log Y per element up to C Y (log x)^(-A).
A short interval prime number theorem iterated through Buchstab. Easier than the parent: no deleted
part. Non-vacuity: at t = 2Y the segment is the whole interval and the density is positive. -/
theorem upper_self_scaled_rough_centred_prefix_bound
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              upperRough m ((m : ℝ) ^ (1/4+(2*(1/16-1/10^5))/8-ε)) : ℝ) : ℂ) -
            ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) : ℝ) : ℂ) /
              Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the deleted part of the page 53 density of P0069, the set E not covered by Lemma 33.
HARD, for Codex: k_m minus its kept part at the self scale, weighted by log m over log Y, has on each
segment from Y to t, Y ≤ t ≤ 2Y, mass upperDeletedIntegral over log Y per element up to
C Y (log x)^(-A), by the prime number theorem and partial summation. Easier than the parent: no
rough indicator. Non-vacuity: at t = 2Y the segment is the whole interval. -/
theorem upper_self_scaled_deleted_centred_prefix_bound
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) : ℝ) : ℂ) -
            ((upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

set_option maxHeartbeats 800000 in
/-- The statement of `upper_self_scaled_principal_centred_prefix_bound` of the imported file,
verbatim, assembled from the two leaves and the proved lemma. For x at least 4 the level is at
least 2, so on the interval b1 is log m over log Y times the raw weight; the lemma splits the raw
weight into the rough part and the deleted part, the density splits the same way, and the triangle
inequality adds the two leaf bounds. -/
theorem upper_self_scaled_principal_centred_prefix_bound_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) - ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := upper_self_scaled_rough_centred_prefix_bound h4 h9 hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := upper_self_scaled_deleted_centred_prefix_bound h4 h9 hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) 4 + |C1| + |C2|, fun x hx t htl htu => ?_⟩
  have hab : 0 ≤ |C1| + |C2| := by positivity
  have hmx : max (max C1 C2) 4 ≤ x := by linarith [abs_nonneg C1, abs_nonneg C2]
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left C1 C2) (le_max_left _ 4)) hmx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right C1 C2) (le_max_left _ 4)) hmx
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ 4) hmx
  have hY2 : (2 : ℝ) ≤ x ^ (11 / 20 + ε) := by
    have hs : (2 : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    rw [Real.sqrt_eq_rpow] at hs
    exact le_trans hs (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  set L : ℝ := Real.log (x ^ (11 / 20 + ε)) with hL
  set a : ℝ := ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) with ha
  set d : ℝ := upperDeletedIntegral ω ε with hd
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) with hS
  have hsum : ∀ m ∈ S, ((b1 x m : ℂ) - ((a + d : ℝ) : ℂ) / (L : ℂ)) =
      ((((Real.log (m : ℝ) / L *
          upperRough m ((m : ℝ) ^ (1/4+(2*(1/16-1/10^5))/8-ε)) : ℝ) : ℂ) - ((a : ℝ) : ℂ) / (L : ℂ))
      + (((Real.log (m : ℝ) / L *
          (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) : ℝ) : ℂ) - ((d : ℝ) : ℂ) / (L : ℂ))) := by
    intro m hm
    have hmJ : m ∈ rightInterval ε x := (Finset.mem_filter.mp hm).1
    have hm1 : 1 ≤ m := by
      have := (Finset.mem_Ioc.mp (by simpa [rightInterval] using hmJ)).1
      omega
    rw [hb x m, if_pos ⟨hY2, hmJ⟩, upper_raw_weight_self_eq_rough_add_deleted ε hm1]
    push_cast
    ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
  have hYL : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
  refine le_trans (norm_add_le _ _) ?_
  have e1 := hC1 x hx1 t htl htu
  have e2 := hC2 x hx2 t htl htu
  have hc : C1 + C2 ≤ max (max C1 C2) 4 + |C1| + |C2| := by
    have : (0:ℝ) ≤ max (max C1 C2) 4 := le_trans (by norm_num) (le_max_right _ 4)
    linarith [le_abs_self C1, le_abs_self C2]
  calc _ ≤ C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := add_le_add e1 e2
    _ = (C1 + C2) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    _ ≤ (max (max C1 C2) 4 + |C1| + |C2|) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right hc hYL
    _ = _ := by ring

end LeanLab.BHP1997.Upper312Route
