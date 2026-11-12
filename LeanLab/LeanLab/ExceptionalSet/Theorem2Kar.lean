/-
Theorem 2 of J. Brudern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst.
Fourier 48 (1998), p. 354, proved on p. 377, from `KaracubaCore.Lemma10Kar`, Lemma 10 with
`S ⊆ [2, k-1]` as in Karacuba's Theorem 1, instead of the lab `Lemma10`, whose class allows
`s = 1`. Coordinator decisions 1 and 5, 2026-11-12.

`theorem2_of_leaves_kar` copies the proof of `Decomp1539a.theorem2_of_leaves` line for line
and supplies one more fact: P0082 p. 377 takes `k = [9 (log N)^{γ-1}] + 1`, which tends to
infinity, so `δ k ≥ 2` for large `N`, `kN_large`, and then dropping `s = 1` from the set `S`
of p. 377 leaves a set of size at least `(δ/2) k`, `KaracubaCore.kclassKar_of_kclass`.
In fact every `s` in the `S` of p. 377 is at least the lower end of display (56), which
grows like `(1-c)/(1-θ/2) (log N)^{γ-1}`, so for large `N` that `S` has no `s = 1` at all;
the Lean route uses only the weaker count above.

`theorem2_via_karacuba_kar` then gives Theorem 2 from the Karacuba leaves of KaracubaCore
WITHOUT the QUESTION leaf `leaf_s1_case`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaCore

namespace LeanLab.ExceptionalSet.U1539

open Real Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- PROVED. P. 377: `k = [9 (log N)^{γ-1}] + 1` tends to infinity, so for every `δ > 0`,
`δ k ≥ 2` for all large `N`. -/
theorem kN_large (γ : ℝ) (h1 : 1 < γ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N → 2 ≤ δ * (kN γ N : ℝ) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (γ - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < γ - 1)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop (2 / (9 * δ))))
  refine ⟨N₃, fun N hN => ?_⟩
  have hx := hN₃ N hN
  have hfl : 9 * Real.log (N : ℝ) ^ (γ - 1) < (kN γ N : ℝ) := by
    simpa [kN, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (9 * Real.log (N : ℝ) ^ (γ - 1))
  have h9 : 2 / δ ≤ 9 * Real.log (N : ℝ) ^ (γ - 1) := by
    have : 2 / (9 * δ) * 9 = 2 / δ := by field_simp
    nlinarith
  have : 2 / δ ≤ (kN γ N : ℝ) := by linarith
  rw [div_le_iff₀ hδ] at this
  linarith

/-- ASSEMBLY. Theorem 2 from `Lemma10Kar`, CONDITIONAL ON `KaracubaCore.Lemma10Kar`, on
Lemma 16 (a), (b) and on the leaves `leaf_T2_*` of Decomp1539a. A copy of
`theorem2_of_leaves` with `δ/2` in place of `δ` and the class fact of `kclassKar_of_kclass`. -/
theorem theorem2_of_leaves_kar (h10 : KaracubaCore.Lemma10Kar) (h16a : Lemma16a) (h16b : Lemma16b) : Theorem2 := by
  intro γ h1 h2 c C hc0 hc1 hC0 hC1
  set θ := min (1 / 4 : ℝ) ((γ - 1 - C) / (2 * γ)) with hθdef
  have hθ0 : 0 < θ := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have hθ1 : θ < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθC : 1 + C < γ * (1 - θ) := by
    have hm := min_le_right (1 / 4 : ℝ) ((γ - 1 - C) / (2 * γ))
    have hγθ : γ * θ ≤ (γ - 1 - C) / 2 := by
      calc γ * θ ≤ γ * ((γ - 1 - C) / (2 * γ)) := mul_le_mul_of_nonneg_left hm (by linarith)
        _ = (γ - 1 - C) / 2 := by field_simp
    nlinarith
  have hd1 : 1 / (1 - θ / 2) < 1 / (1 - θ) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hd2 : 1 / (1 - θ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hd3 : 0 < 1 / (1 - θ / 2) := by apply div_pos one_pos; linarith
  have hδ0 : 0 < deltaK c θ := by
    unfold deltaK
    have : 0 < 1 / (1 - θ) - 1 / (1 - θ / 2) := by linarith
    have : 0 < 1 - c := by linarith
    positivity
  have hδ1 : deltaK c θ < 1 := by
    unfold deltaK
    have : (1 - c) * (1 / (1 - θ) - 1 / (1 - θ / 2)) < 2 := by nlinarith
    nlinarith
  obtain ⟨B, c', hB, hc', hK⟩ := h10 θ (θ / 2) (3 / 4) (deltaK c θ / 2) (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)
  obtain ⟨N3, hN3⟩ := kN_large γ h1 (deltaK c θ) hδ0
  obtain ⟨N0, hN0⟩ := classMembership_of_leaves h16a h16b γ c C θ h1 h2 hc0 hc1 hC0 hC1 hθ0 hθ1 hθC
  obtain ⟨N2, hN2⟩ := leaf_T2_large_one γ (c' / 100) h1 h2
  obtain ⟨B0, hB0⟩ := leaf_T2_small γ (c' / 100) (max (max N0 N3) (max N2 2))
  refine ⟨c' / 100, max B0 (B + 1), by positivity, fun N hN α hlo hhi => ?_⟩
  have hFpos : 0 < F γ (2 * N) ^ (-c) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hαabs : 0 < |α| := lt_of_lt_of_le hFpos hlo
  have hnorm : ‖expSumF γ α N‖ = ‖expSumF γ |α| N‖ := by
    rcases abs_cases α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, norm_expSumF_neg]
  rw [hnorm]
  have hE : 0 ≤ (N : ℝ) * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by positivity
  by_cases hbig : max (max N0 N3) (max N2 2) ≤ N
  · have hbig' := hbig
    simp only [max_le_iff] at hbig'
    obtain ⟨⟨hN0', hN3'⟩, hN2', hN2''⟩ := hbig'
    obtain ⟨hKC, hk1, hk10⟩ := hN0 N hN0' |α| hαabs hlo hhi
    have h1' := hK N hN (fun x => |α| * F γ x) (kN γ N)
      (KaracubaCore.kclassKar_of_kclass hKC (hN3 N hN3'))
    have h2' := leaf_T2_conv γ c' h1 hc' N hN2'' (kN γ N) hk1 hk10
    have h3' := norm_Icc_le γ |α| N
    have h4' := hN2 N hN2'
    calc ‖expSumF γ |α| N‖
        ≤ B * (N : ℝ) ^ (1 - c' / (kN γ N : ℝ) ^ 2) + 1 := by linarith
      _ ≤ B * ((N : ℝ) * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)))
          + (N : ℝ) * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
          have := mul_le_mul_of_nonneg_left h2' hB.le
          linarith
      _ = (B + 1) * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by ring
      _ ≤ max B0 (B + 1) * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE
  · have hsmall := hB0 N hN (by omega)
    calc ‖expSumF γ |α| N‖ ≤ N + 1 := norm_expSumF_le γ |α| N
      _ ≤ B0 * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := hsmall
      _ ≤ max B0 (B + 1) * N * Real.exp (-(c' / 100) * Real.log N ^ (3 - 2 * γ)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE

/-- ASSEMBLY. Theorem 2 CONDITIONAL ON `Lemma10Kar` and the leaves of Decomp1539a only. -/
theorem theorem2_of_all_leaves_kar (h10 : KaracubaCore.Lemma10Kar) : Theorem2 :=
  theorem2_of_leaves_kar h10
    (lemma16a_of_leaves lemma15_of_leaves)
    (lemma16b_of_leaves (lemma14_of_leaves (lemma13_of_leaves lemma11_of_leaves lemma12_of_leaves)))

/-- Theorem 2 by the Karacuba route without `leaf_s1_case`: CONDITIONAL ON the CITED
`KaracubaCore.leaf_karLemma1_mvt`, `KaracubaCore.leaf_karLemma2`, and the LEAF
`KaracubaCore.leaf_W_bound`, which reduces to `KaracubaWSplit.leafW1_bound`. The leaves of
Decomp1539a used here are all proved; `leaf_karLemma3` and `leaf_T_bound` are PROVED. -/
theorem theorem2_via_karacuba_kar : Theorem2 :=
  theorem2_of_all_leaves_kar KaracubaCore.lemma10Kar_of_karacuba

end LeanLab.ExceptionalSet.U1539
