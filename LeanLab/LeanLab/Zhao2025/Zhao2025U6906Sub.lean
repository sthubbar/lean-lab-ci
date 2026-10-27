import Mathlib
import LeanLab.Zhao2025.Zhao2025U6904Grid
import LeanLab.Zhao2025.Zhao2025U6903ST

/-!
# Zhao 2025, the unshown subcases `λ₁,₁ ∈ [0.01, 0.10]` and `[0.10, 0.30]` of Section 4

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6906, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

Zhao treats `λ₁,₁ ∈ [0.30, 0.40]` in (4.7) to (4.9) and says the subcases `[0.01, 0.10]` and
`[0.10, 0.30]` "will be treated in a similar manner".  Here they are done in the (4.7) layout with
Lemma 2.4 (2), `N(3.08) ≤ 1`, and (3), `N(1.58) ≤ 1`: the sets `i ≥ 2` have all `λ ≥ Λ`, so
`Sᵢ = Tᵢ(Λ)`, and `S₁ ≤ e^{-(10/3)λ₁,₁} + T₁(Λ)` with `λ₀ = λ₁,₁ ≥` the left end.

* `layout47`, PROVED: `Σ Sᵢ² ≤ (a + t₁)² + t_m t_s` from `S₁ ≤ a + t₁`, `0 ≤ Sᵢ ≤ t_m`, `Σ_{i≥2} Sᵢ ≤ t_s`.
* `sub010_closes`, `sub001_closes`, PROVED: with the certified inputs of `Zhao2025U6906Data`
  (`T₁ ≤ 0.0690`, `Tᵢ ≤ 0.0464`, `Σ Tᵢ ≤ 4.951` at `Λ = 1.58`; `T₁ ≤ 0.0042`, `Tᵢ ≤ 0.0018`,
  `Σ Tᵢ ≤ 0.6150` at `Λ = 3.08`) as hypotheses, `Σ Sᵢ² < 0.85`, resp. `< 0.946`, for every
  `λ₁,₁` in the subcase.  Those inputs are CONDITIONAL ON (3.15), (3.16), (3.26) through
  `T_of_326_316` and `sT_of_315`.
-/

namespace LeanLab.Zhao2025.U6900

/-- PROVED: the (4.7) layout. -/
theorem layout47 (n : ℕ) (S : ℕ → ℝ) (a t1 tm ts : ℝ) (hS0 : 0 ≤ S 0) (h0 : S 0 ≤ a + t1)
    (hS : ∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ tm)
    (hsum : ∑ i ∈ Finset.range n, S (i + 1) ≤ ts) (htm : 0 ≤ tm) :
    ∑ i ∈ Finset.range (n + 1), S i ^ 2 ≤ (a + t1) ^ 2 + tm * ts := by
  rw [Finset.sum_range_succ']
  have h1 : S 0 ^ 2 ≤ (a + t1) ^ 2 := pow_le_pow_left₀ hS0 h0 2
  have h2 : ∑ i ∈ Finset.range n, S (i + 1) ^ 2 ≤ ∑ i ∈ Finset.range n, tm * S (i + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨p, q⟩ := hS i (Finset.mem_range.mp hi)
    nlinarith
  have h3 : ∑ i ∈ Finset.range n, tm * S (i + 1) ≤ tm * ts := by
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum htm
  linarith

theorem exp_third_le : Real.exp (-(1 / 3 : ℝ)) ≤ ((eupq (1 / 3) : ℚ) : ℝ) := by
  have := eupq_ge (1 / 3) (by norm_num); push_cast at this; exact this

theorem exp_thirtieth_le : Real.exp (-(1 / 30 : ℝ)) ≤ ((eupq (1 / 30) : ℚ) : ℝ) := by
  have := eupq_ge (1 / 30) (by norm_num); push_cast at this; exact this

set_option maxRecDepth 100000 in
theorem num010 : (eupq (1 / 3) + 69 / 1000) ^ 2 + 464 / 10000 * (4951 / 1000) < (85 / 100 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem num001 : (eupq (1 / 30) + 42 / 10000) ^ 2 + 18 / 10000 * (6150 / 10000) < (946 / 1000 : ℚ) := by
  decide +kernel

/-- PROVED: the subcase `λ₁,₁ ∈ [0.10, 0.30]` closes, `Σ Sᵢ² < 0.85`, given its inputs. -/
theorem sub010_closes (n : ℕ) (S : ℕ → ℝ) (l11 : ℝ) (hl : 0.10 ≤ l11) (hS0 : 0 ≤ S 0)
    (h0 : S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.0690)
    (hS : ∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0464)
    (hsum : ∑ i ∈ Finset.range n, S (i + 1) ≤ 4.951) :
    ∑ i ∈ Finset.range (n + 1), S i ^ 2 < 0.85 := by
  have he : Real.exp (-(10 / 3 * l11)) ≤ ((eupq (1 / 3) : ℚ) : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_third_le
  have h := layout47 n S (((eupq (1 / 3) : ℚ) : ℝ)) 0.0690 0.0464 4.951 hS0 (by linarith) hS hsum
    (by norm_num)
  have hn : (((eupq (1 / 3) + 69 / 1000) ^ 2 + 464 / 10000 * (4951 / 1000) : ℚ) : ℝ) <
      ((85 / 100 : ℚ) : ℝ) := by exact_mod_cast num010
  push_cast at hn
  norm_num at h hn ⊢
  linarith

/-- PROVED: the subcase `λ₁,₁ ∈ [0.01, 0.10]` closes, `Σ Sᵢ² < 0.946`, given its inputs. -/
theorem sub001_closes (n : ℕ) (S : ℕ → ℝ) (l11 : ℝ) (hl : 0.01 ≤ l11) (hS0 : 0 ≤ S 0)
    (h0 : S 0 ≤ Real.exp (-(10 / 3 * l11)) + 0.0042)
    (hS : ∀ i, i < n → 0 ≤ S (i + 1) ∧ S (i + 1) ≤ 0.0018)
    (hsum : ∑ i ∈ Finset.range n, S (i + 1) ≤ 0.6150) :
    ∑ i ∈ Finset.range (n + 1), S i ^ 2 < 0.946 := by
  have he : Real.exp (-(10 / 3 * l11)) ≤ ((eupq (1 / 30) : ℚ) : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans exp_thirtieth_le
  have h := layout47 n S (((eupq (1 / 30) : ℚ) : ℝ)) 0.0042 0.0018 0.6150 hS0 (by linarith) hS hsum
    (by norm_num)
  have hn : (((eupq (1 / 30) + 42 / 10000) ^ 2 + 18 / 10000 * (6150 / 10000) : ℚ) : ℝ) <
      ((946 / 1000 : ℚ) : ℝ) := by exact_mod_cast num001
  push_cast at hn
  norm_num at h hn ⊢
  linarith

end LeanLab.Zhao2025.U6900
