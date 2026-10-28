/-
P0083 Perelli 1996, merge of the two encodings, PC run 20261020T0503Z-11094, unit U-1167.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Encoding A is `Perelli1996/Statements.lean`, namespace `LeanLab.Perelli1996`, imported by
Languasco2004. Encoding B is the repo copy, now `Perelli1996/B/*`, namespace
`LeanLab.Perelli1996.B`, which PROVED Corollary 1 second part from the first, U-5100.

* `sing_eq_B`, `R_eq_B`: A's `𝔖` and `R` are B's, definitionally or by `B.R_eq`.
* `corollary1b_of_corollary1a`: A's Corollary 1 second part from A's first part, by B's route:
  `F(n) ≥ N/2` on the window, `𝔖(m) ≥ 1` for even `m`, `R(m) ≤ m/4` for non-Goldbach
  `m ≥ 17408⁸`, so a non-Goldbach even `F(n)` has `|err| ≥ 3N/8 > N/L^A`.
* `corollary1b_of_theorem1`: A's `Corollary1b F` CONDITIONAL ON A's `Theorem1 F` only, so the
  cited `corollary1b` sorry of Statements.lean is no longer needed by any downstream use.
-/
import LeanLab.Perelli1996.StatementsA
import LeanLab.Perelli1996.B.Cor1b

namespace LeanLab.Perelli1996
-- 2026-10-28 architect: encoding A now lives in StatementsA, namespace EncA
open LeanLab.Perelli1996.EncA
open Finset Real Polynomial Filter Topology

attribute [local instance] Classical.propDecidable

/-- A's singular series is B's. -/
theorem sing_eq_B (n : ℕ) : Sing n = B.Sing n := rfl

/-- A's `R`, the lab's `PerelliPintz1992.r`, is B's `R`. -/
theorem R_eq_B (n : ℕ) : R n = B.R n := by
  rw [B.R_eq]; rfl

/-- `F(n)` in A's natural-number reading is B's integer value once it is nonnegative. -/
theorem Fn_eq (F : ℤ[X]) (n : ℕ) : Fn F n = (B.Fv F n).toNat := rfl

/-- **Corollary 1, second part, from the first part**, in encoding A. -/
theorem corollary1b_of_corollary1a {F : ℤ[X]} (h : Corollary1a F) : Corollary1b F := by
  intro hF _hrho A ε hA hε
  obtain ⟨C₂, N₁, hC⟩ := h hF A ε hA hε
  obtain ⟨X₀, hX₀, hX⟩ := B.poly_lower F hF
  set k := F.natDegree with hk
  have hk0 : k ≠ 0 := by have := hF.1; omega
  have hdeg : deg F = (k : ℝ) := rfl
  -- `L^{-A} < 3/8` for large `N`
  have htend : Tendsto (fun N : ℝ => Real.log N ^ (-A)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hA).comp Real.tendsto_log_atTop
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 3 / 8)))
  refine ⟨C₂, max (max N₁ N₂) (max (X₀ ^ k) (2 * 17408 ^ 8)), fun N H hN h1 h2 => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNX : X₀ ^ k ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNb : 2 * 17408 ^ 8 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hLA : Real.log N ^ (-A) < 3 / 8 := hN₂ N hN2
  have hLA' : N / Real.log N ^ A < 3 / 8 * N := by
    rw [Real.rpow_neg hL.le] at hLA
    rw [div_eq_mul_inv, mul_comm]
    exact mul_lt_mul_of_pos_right hLA hN0
  have hsub : (nRange (N ^ (1 / deg F)) H).filter
        (fun n : ℕ => (2 : ℤ) ∣ F.eval (n : ℤ) ∧ ¬ IsGoldbachSum (Fn F n)) ⊆
      (nRange (N ^ (1 / deg F)) H).filter (fun n => N / Real.log N ^ A < |err F n|) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨hnw, hev, hng⟩ := hn
    refine Finset.mem_filter.2 ⟨hnw, ?_⟩
    have hnlo : N ^ (1 / (k : ℝ)) ≤ n := by
      simp only [nRange, Finset.mem_Icc] at hnw
      rw [← hdeg]
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnw.1)
    have hXn : X₀ ≤ n := by
      have := Real.rpow_le_rpow (by positivity) hNX (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))
      rw [one_div, Real.pow_rpow_inv_natCast hX₀ hk0] at this
      rw [one_div] at hnlo
      linarith
    have hFn := hX n hXn
    have hnk : N ≤ (n : ℝ) ^ k := by
      have := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hnlo k
      rwa [B.rpow_k N hN0.le k hk0] at this
    have hFN : N / 2 ≤ (B.Fv F n : ℝ) := by linarith
    set m := Fn F n with hm
    have hFpos : 0 ≤ B.Fv F n := by
      have : (0 : ℝ) ≤ (B.Fv F n : ℝ) := by linarith
      exact_mod_cast this
    have hmc : (m : ℝ) = (B.Fv F n : ℝ) := by
      rw [hm, Fn_eq]; exact_mod_cast Int.toNat_of_nonneg hFpos
    have hmeven : Even m := by
      obtain ⟨r, hr⟩ := hev
      refine ⟨r.toNat, ?_⟩
      rw [hm, Fn_eq]
      have hv : B.Fv F n = 2 * r := hr
      omega
    have hmbig : (17408 : ℝ) ^ 8 ≤ m := by rw [hmc]; linarith
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0] at hmbig; norm_num at hmbig
    have hS : 1 ≤ Sing m := by rw [sing_eq_B]; exact B.one_le_sing hmeven hm0
    have hR : R m ≤ (m : ℝ) / 4 := by rw [R_eq_B]; exact B.R_le_quarter hmbig hng
    have hmpos : (0 : ℝ) < m := by rw [hmc]; linarith
    have hD : err F n ≤ -(3 / 4 * (m : ℝ)) := by
      unfold err
      rw [← hm]
      nlinarith
    have habs : 3 / 4 * (m : ℝ) ≤ |err F n| := by
      rw [abs_of_neg (by linarith)]; linarith
    calc N / Real.log N ^ A < 3 / 8 * N := hLA'
      _ ≤ 3 / 4 * (m : ℝ) := by rw [hmc]; linarith
      _ ≤ |err F n| := habs
  calc (goldExc F N H (N ^ (1 / deg F)) : ℝ)
      ≤ (excCount F N H A : ℝ) := by
        unfold goldExc excCount
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C₂ * H / Real.log N ^ A := hC N H hN1 h1 h2

/-- **Corollary 1, second part, CONDITIONAL ON Theorem 1 only**, in encoding A. -/
theorem corollary1b_of_theorem1 {F : ℤ[X]} (h : Theorem1 F) : Corollary1b F :=
  corollary1b_of_corollary1a (corollary1a_of_theorem1 h)

/-- Pintz 2021's (5.4), `E_k(N) ≪ N (log N)^{-A}` for every `k ≥ 1`, CONDITIONAL ON Perelli's
Theorem 1 for `2x^k` only; Statements.lean's `perelli54` took the separate Corollary 1 sorry. -/
theorem perelli54_of_theorem1 {k : ℕ} (hk : 1 ≤ k) (h : Theorem1 (F2 k)) :
    LeanLab.ExceptionalSet.Pintz2021.PolyLogPowerSaving k :=
  polyLog_of_corollary1b hk (corollary1b_of_theorem1 h)

/-- Vacuity: `F = X` is admissible with `ρ_F(2) = 1 ≠ 0`, so the hypotheses of
`corollary1b_of_theorem1` can hold. -/
theorem vacuity_merge : Admissible (X : ℤ[X]) ∧ rhoF (X : ℤ[X]) 2 ≠ 0 := by
  refine ⟨B.vacuity_X.1, ?_⟩
  have : (Finset.range 2).filter (fun m : ℕ => ((2 : ℕ) : ℤ) ∣ (X : ℤ[X]).eval (m : ℤ)) = {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, eval_X]
    constructor
    · rintro ⟨h1, h2⟩
      interval_cases m
      · rfl
      · norm_num at h2
    · rintro rfl; norm_num
  unfold rhoF
  rw [this]
  simp

end LeanLab.Perelli1996
