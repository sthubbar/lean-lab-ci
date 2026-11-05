/-
P0069, pages 25 to 27. CODEX task312.
Existing declarations moved intact from DecompC165b under the statement seal.
No statement or definition body is changed. No new analytic input is asserted.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165

namespace LeanLab.BHP1997.DecompC165b
open Classical

/-- Pages 25 to 27, psi at natural cutoff. This is the indicator of having no prime divisor below the cutoff. -/
noncomputable def siftedWeight (n z : ℕ) : ℝ :=
 if n = 1 ∨ z ≤ n.minFac then 1 else 0

/-- Pages 25 to 27, exact support of psi. Reuses Nat.le_minFac. -/
theorem sifted_weight_support (n z : ℕ) :
    siftedWeight n z = 1 ↔ ∀ p : ℕ, p.Prime → p < z → ¬p ∣ n := by
  by_cases h : n = 1 ∨ z ≤ n.minFac
  · simp only [siftedWeight, ite_eq_left h, true_iff]
    intro p hp hpz hpn
    rcases h with hn | hz
    · subst n
      exact hp.not_dvd_one hpn
    · have hm := Nat.minFac_le_of_dvd hp.two_le hpn
      omega
  · simp only [siftedWeight, ite_eq_right h, zero_ne_one, false_iff]
    intro hh
    apply h
    exact Nat.le_minFac.mpr (fun p hp hpn => le_of_not_gt (fun hlt => hh p hp hlt hpn))

/-- Pages 25 to 27, exact support at a real cutoff. Natural ceiling preserves the strict prime inequality. -/
theorem sifted_weight_support_real (n : ℕ) (z : ℝ) :
    siftedWeight n ⌈z⌉₊ = 1 ↔ ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬p ∣ n := by
  rw [sifted_weight_support]
  simp only [Nat.lt_ceil]

/-- Pages 25 to 27, definition 4.6 and the actual lab primorial. -/
theorem sifted_weight_primorial (n : ℕ) (z : ℝ) :
    siftedWeight n ⌈z⌉₊ = if Nat.gcd n (Thm2.primorialBelow z) = 1 then 1 else 0 := by
  have hi : siftedWeight n ⌈z⌉₊ = 1 ↔ Nat.gcd n (Thm2.primorialBelow z) = 1 := by
    rw [sifted_weight_support_real, ← Nat.coprime_iff_gcd_eq_one,
      Thm2.primorialBelow, Nat.coprime_prod_right_iff]
    constructor
    · intro h p hp
      have hp' := Finset.mem_filter.mp hp
      exact ((hp'.2.1.coprime_iff_not_dvd).mpr (h p hp'.2.1 hp'.2.2)).symm
    · intro h p hp hpz
      have hmem : p ∈ (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hpz), hp, hpz⟩
      exact hp.coprime_iff_not_dvd.mp (h p hmem).symm
  by_cases h : Nat.gcd n (Thm2.primorialBelow z) = 1
  · rw [ite_eq_left h]
    exact hi.mpr h
  · rw [ite_eq_right h]
    have hn := mt hi.mp h
    unfold siftedWeight at *
    split_ifs at * <;> norm_num at *

/-- Pages 25 to 27. A coefficient family multiplied by the basic sifted indicator.
This notation exposes the rough support used by the Section 4 construction. -/
noncomputable def section4SiftedFamily (c : ℝ → ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  c x k * siftedWeight k ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊

end LeanLab.BHP1997.DecompC165b
