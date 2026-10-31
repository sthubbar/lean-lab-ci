/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
P0021 journal Lemma 6, p. 1219, and display 9, p. 1222.
The analytic one-sided bounds are hypotheses, not proved inputs.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Decomp138
namespace LeanLab.BS2022GRH.Mertens138
open Real Finset Classical ChenThresholdGRH Decomp138

/-- LEAF. The exact interval split in display 9, p. 1222, for real endpoints. -/
theorem sum_band_eq_sub (u z : ℝ) (huz : u ≤ z) :
    ∑ p ∈ band u z, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesBelow ⌈z⌉₊, (1 : ℝ) / p) -
        ∑ p ∈ Nat.primesBelow ⌈u⌉₊, (1 : ℝ) / p := by
  have hband : band u z = Nat.primesBelow ⌈z⌉₊ \ Nat.primesBelow ⌈u⌉₊ := by
    ext p
    simp only [band, Nat.mem_primesBelow, mem_filter, mem_range, mem_sdiff, Nat.lt_ceil]
    constructor
    · rintro ⟨hpz, hprime, hpu, _⟩
      exact ⟨⟨hpz, hprime⟩, fun h => (not_lt_of_ge hpu) h.1⟩
    · rintro ⟨⟨hpz, hprime⟩, hnot⟩
      refine ⟨hpz, hprime, ?_, hpz⟩
      by_contra h
      exact hnot ⟨lt_of_not_ge h, hprime⟩
  have hsub : Nat.primesBelow ⌈u⌉₊ ⊆ Nat.primesBelow ⌈z⌉₊ := by
    intro p hp
    obtain ⟨hpu, hprime⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨hpu.trans_le (Nat.ceil_mono huz), hprime⟩
  rw [hband, sum_sdiff_eq_sub hsub]

/-- LEAF. Display 9, p. 1222, conditional on the one-sided bounds of Lemma 6. -/
theorem reciprocal_sum_lt_of_mertens (z u M : ℝ) (hz : exp 2753 < z) (_hu : 400 ≤ u)
    (huz : u < z)
    (hupper : (∑ p ∈ Nat.primesBelow ⌈z⌉₊, (1 : ℝ) / p) ≤
      log (log z) + M + 2.28975e-9 / log z)
    (hlower : log (log u) + M - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈u⌉₊, (1 : ℝ) / p) :
    ∑ p ∈ band u z, (1 : ℝ) / p < log (log z) - log (log u) + 1.131e-7 := by
  have hz0 : 0 < z := (exp_pos _).trans hz
  have hlog : (2753 : ℝ) < log z := (lt_log_iff_exp_lt hz0).2 hz
  have hc : 2.28975e-9 / log z < (1.131e-7 - 1.107533e-7 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < log z)).2
    nlinarith
  rw [sum_band_eq_sub u z huz.le]
  linarith

/-- The arXiv error at u = 400 exceeds the journal target in display 9, p. 1222. -/
theorem old_error_exceeds_journal : (1.131e-7 : ℝ) < 1.5e-4 / log 400 := by
  have hlog : 0 < log (400 : ℝ) := log_pos (by norm_num)
  rw [lt_div_iff₀ hlog]
  have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 400)
  nlinarith
/-- Exact Lemma 7, pp. 1221 and 1222, CONDITIONAL ON the journal Lemma 6 bounds. -/
theorem lemma7J_of_mertens (M : ℝ)
    (hupper : ∀ z : ℝ, exp 2753 < z →
      (∑ p ∈ Nat.primesBelow ⌈z⌉₊, (1 : ℝ) / p) ≤ log (log z) + M + 2.28975e-9 / log z)
    (hlower : ∀ u : ℝ, 400 ≤ u → log (log u) + M - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈u⌉₊, (1 : ℝ) / p) : Lemma7J := by
  apply Decomp138.lemma7J_of_reciprocal
  intro z u hz hu huz
  exact reciprocal_sum_lt_of_mertens z u M hz hu huz (hupper z hz) (hlower u hu)

end LeanLab.BS2022GRH.Mertens138

#print axioms LeanLab.BS2022GRH.Mertens138.sum_band_eq_sub

#print axioms LeanLab.BS2022GRH.Mertens138.reciprocal_sum_lt_of_mertens

#print axioms LeanLab.BS2022GRH.Mertens138.old_error_exceeds_journal

#print axioms LeanLab.BS2022GRH.Mertens138.lemma7J_of_mertens
