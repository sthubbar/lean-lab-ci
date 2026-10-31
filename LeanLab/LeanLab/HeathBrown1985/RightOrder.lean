/-
I-0061, run 20261017T1103Z-22220, unit U-0290. AI-written Lean code, Claude. Checked only by
the Lean kernel.

The right order of magnitude for the Goldbach count r(m) for almost all even m, from
Siegel-Walfisz alone. r(m) is the number of primes p < m with m - p prime, the lab's
`SchnirelmannGoldbach.r`.

* Upper bound, every m ≥ 3, unconditional: r(m) ≤ C m / log² m · ∏_{p ∣ m} (1 + 1/p), the lab's
  Selberg sieve result `S1u_holds`.
* Lower bound, almost all m: for every C > 0, all but O(x (log x)^{-C}) even m in (2x, 3x]
  have r(m) ≥ e⁻⁶ x / log² (3x), from Heath-Brown 1985 Theorem 1 through `fewReps`, and the
  pointwise inequality N₂(x, m) ≤ log² m · r(m).

KNOWN mathematics: Hardy-Littlewood type order for almost all even m goes back to
Chudakov, van der Corput and Estermann 1937 to 1938. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HeathBrown1985.ManyReps
import LeanLab.SchnirelmannGoldbach.S1.Final

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Real

attribute [local instance] Classical.propDecidable

/-- Each weighted representation counted by `N₂(x, m)` weighs at most `log² m`, and the
primes counted by `N₂` are among those counted by `r(m)`. -/
theorem N2_le_log_sq_mul_r (x : ℝ) (m : ℕ) :
    N2 x m ≤ Real.log m ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) := by
  unfold N2 LeanLab.SchnirelmannGoldbach.r
  set S := (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ (p : ℝ) ≤ x)
  set R := (range m).filter (fun p => p.Prime ∧ (m - p).Prime)
  have hsub : S ⊆ R := by
    intro p hp
    simp only [S, R, mem_filter, mem_range] at hp ⊢
    obtain ⟨hp1, hp2, hp3, -⟩ := hp
    refine ⟨?_, hp2, hp3⟩
    by_contra hcon
    have : m - p = 0 := by omega
    rw [this] at hp3
    exact Nat.not_prime_zero hp3
  have hterm : ∀ p ∈ S, Real.log p * Real.log (m - p : ℕ) ≤ Real.log m ^ 2 := by
    intro p hp
    simp only [S, mem_filter, mem_range] at hp
    obtain ⟨hp1, hp2, hp3, -⟩ := hp
    have hpm : p ≤ m := by omega
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp2.one_lt.le
    have h2 : (1 : ℝ) ≤ ((m - p : ℕ) : ℝ) := by exact_mod_cast hp3.one_lt.le
    have hl1 : 0 ≤ Real.log p := Real.log_nonneg h1
    have hl2 : 0 ≤ Real.log ((m - p : ℕ) : ℝ) := Real.log_nonneg h2
    have hpm' : (p : ℝ) ≤ m := by exact_mod_cast hpm
    have hmp' : ((m - p : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m p
    have hb1 : Real.log p ≤ Real.log m := Real.log_le_log (by linarith) hpm'
    have hb2 : Real.log ((m - p : ℕ) : ℝ) ≤ Real.log m :=
      Real.log_le_log (by linarith) hmp'
    calc Real.log p * Real.log ((m - p : ℕ) : ℝ) ≤ Real.log m * Real.log m :=
          mul_le_mul hb1 hb2 hl2 (hl1.trans hb1)
      _ = Real.log m ^ 2 := by ring
  calc ∑ p ∈ S, Real.log p * Real.log ((m - p : ℕ) : ℝ) ≤ ∑ _p ∈ S, Real.log m ^ 2 :=
        sum_le_sum hterm
    _ = (S.card : ℝ) * Real.log m ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (R.card : ℝ) * Real.log m ^ 2 := by
        gcongr
    _ = Real.log m ^ 2 * (R.card : ℝ) := by ring

/-- The even `m ∈ (2x, 3x]` with fewer than `e⁻⁶ x / log² (3x)` Goldbach representations. -/
def lowReps (x : ℝ) : Finset ℕ :=
  ((range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))).filter
    (fun m => Even m ∧
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) < Real.exp (-6) * x / Real.log (3 * x) ^ 2)

theorem lowReps_subset_fewReps (x : ℝ) (hx : 2 ≤ x) : lowReps x ⊆ fewReps x := by
  intro m hm
  simp only [lowReps, fewReps, mem_filter, mem_range] at hm ⊢
  obtain ⟨⟨hm1, hm2⟩, hev, hlt⟩ := hm
  refine ⟨⟨hm1, hm2⟩, hev, ?_⟩
  have hm3 : (m : ℝ) ≤ 3 * x := by
    have : m ≤ ⌊3 * x⌋₊ := by omega
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
  have hm1' : (1 : ℝ) ≤ m := by linarith
  have hL : 0 < Real.log (3 * x) := Real.log_pos (by linarith)
  have hlm0 : 0 ≤ Real.log m := Real.log_nonneg hm1'
  have hlm : Real.log m ≤ Real.log (3 * x) := Real.log_le_log (by linarith) hm3
  have hsq : Real.log m ^ 2 ≤ Real.log (3 * x) ^ 2 := by gcongr
  have hr0 : (0 : ℝ) ≤ (LeanLab.SchnirelmannGoldbach.r m : ℝ) := Nat.cast_nonneg _
  have hmul : Real.log (3 * x) ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) <
      Real.exp (-6) * x := by
    rw [lt_div_iff₀ (by positivity)] at hlt
    linarith
  calc N2 x m ≤ Real.log m ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) :=
        N2_le_log_sq_mul_r x m
    _ ≤ Real.log (3 * x) ^ 2 * (LeanLab.SchnirelmannGoldbach.r m : ℝ) :=
        mul_le_mul_of_nonneg_right hsq hr0
    _ < Real.exp (-6) * x := hmul

/-- **Lower bound for almost all even m, from Theorem 1.** -/
theorem lowReps_card_of_theorem1 (h1 : Theorem1) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((lowReps x).card : ℝ) ≤ K * x * Real.log x ^ (-C) := by
  obtain ⟨K, hK⟩ := fewReps_card_of_theorem1 h1 C hC
  refine ⟨K, fun x hx => ?_⟩
  have := card_le_card (lowReps_subset_fewReps x hx)
  exact (Nat.cast_le.mpr this).trans (hK x hx)

/-- **I-0061, the right order of r(m) for almost all even m, from Siegel-Walfisz alone.**
There is one constant `C'` with `r(m) ≤ C' m / log² m · ∏_{p ∣ m}(1 + 1/p)` for every `m ≥ 3`,
and for every `C > 0` all but `O(x (log x)^{-C})` even `m ∈ (2x, 3x]` have
`r(m) ≥ e⁻⁶ x / log² (3x)`. Zero sorry. -/
theorem rightOrder_of_siegelWalfisz (hSW : SiegelWalfisz) :
    (∃ C' : ℝ, ∀ m : ℕ, 3 ≤ m →
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤
        C' * m / Real.log m ^ 2 * LeanLab.SchnirelmannGoldbach.singProd m) ∧
    (∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      ((lowReps x).card : ℝ) ≤ K * x * Real.log x ^ (-C)) := by
  refine ⟨?_, fun C hC => lowReps_card_of_theorem1 (theorem1_of_siegelWalfisz hSW) C hC⟩
  obtain ⟨C', hC'⟩ := LeanLab.SchnirelmannGoldbach.S1u_holds
  refine ⟨C', fun m hm => ?_⟩
  exact hC' m hm m (mem_Icc.mpr ⟨by omega, le_rfl⟩)

/-- The even `m ∈ (2x, 3x]` with `r(m) < e⁻⁶ m / (12 log² m)`, a threshold in `m` alone. -/
def lowRepsM (x : ℝ) : Finset ℕ :=
  ((range (⌊3 * x⌋₊ + 1)).filter (fun m : ℕ => 2 * x < (m : ℝ))).filter
    (fun m => Even m ∧
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) < Real.exp (-6) * m / (12 * Real.log m ^ 2))

theorem lowRepsM_subset (x : ℝ) (hx : 2 ≤ x) : lowRepsM x ⊆ lowReps x := by
  intro m hm
  simp only [lowRepsM, lowReps, mem_filter, mem_range] at hm ⊢
  obtain ⟨⟨hm1, hm2⟩, hev, hlt⟩ := hm
  refine ⟨⟨hm1, hm2⟩, hev, lt_of_lt_of_le hlt ?_⟩
  have hm3 : (m : ℝ) ≤ 3 * x := by
    have : m ≤ ⌊3 * x⌋₊ := by omega
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
  have hm4 : (4 : ℝ) ≤ m := by linarith
  have hlm : 0 < Real.log m := Real.log_pos (by linarith)
  have hL : 0 < Real.log (3 * x) := Real.log_pos (by linarith)
  -- log (3x) ≤ log (3m/2) ≤ log (m²) = 2 log m
  have h3x : 3 * x ≤ (m : ℝ) ^ 2 := by nlinarith
  have hlog : Real.log (3 * x) ≤ 2 * Real.log m := by
    have := Real.log_le_log (by linarith) h3x
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hsq : Real.log (3 * x) ^ 2 ≤ 4 * Real.log m ^ 2 := by nlinarith
  have he : 0 < Real.exp (-6) := Real.exp_pos _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hmx : (m : ℝ) ≤ 3 * x := hm3
  calc Real.exp (-6) * m * Real.log (3 * x) ^ 2
      ≤ Real.exp (-6) * (3 * x) * (4 * Real.log m ^ 2) := by gcongr
    _ = Real.exp (-6) * x * (12 * Real.log m ^ 2) := by ring

/-- **I-0061, threshold in m.** From Siegel-Walfisz: for every `C > 0`, all but
`O(x (log x)^{-C})` even `m ∈ (2x, 3x]` have `r(m) ≥ e⁻⁶ m / (12 log² m)`. Zero sorry. -/
theorem lowRepsM_card_of_siegelWalfisz (hSW : SiegelWalfisz) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((lowRepsM x).card : ℝ) ≤ K * x * Real.log x ^ (-C) := by
  obtain ⟨K, hK⟩ := lowReps_card_of_theorem1 (theorem1_of_siegelWalfisz hSW) C hC
  refine ⟨K, fun x hx => ?_⟩
  exact (Nat.cast_le.mpr (card_le_card (lowRepsM_subset x hx))).trans (hK x hx)

end LeanLab.HeathBrown1985
