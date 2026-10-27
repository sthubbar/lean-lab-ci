/-
Route R-5010, T3 MOONSHOT: the bilateral sandwich of Brüdern-Fouvry, as used by
Baker-Harman-Pintz 1997, P0069, page 2, applied to one even N at a time.
CLOUD 20261019T0213Z-cloud14, unit U-5073.

PROVED: `sandwich`, if `0 ≤ a₀ ≤ ρ ≤ a₁` and `0 ≤ b₀ ≤ ρ' ≤ b₁` then
`ρρ' ≥ a₀b₁ + a₁b₀ - a₁b₁`; `sandwich_sum`, the same summed over any finite set of pairs, so the
sandwich count is a lower bound for the Goldbach count of N; `parity_limit`, if the minorant
densities are at most 1 and the majorant densities at least 2, the size Selberg's parity example
forces on pure Type I sieve weights, then `u₀v₁ + u₁v₀ - u₁v₁ ≤ 0` and the sandwich detects
nothing; `bhp_margin`, the BHP constants of (1.5) leave `u₀v₁ + u₁v₀ - u₁v₁ > 0.0055`.
KNOWN mathematics. Binary Goldbach is OPEN; nothing here is progress on it.
AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.Routes.R5010

/-- The Brüdern-Fouvry inequality, page 2 of P0069. -/
theorem sandwich {a₀ a₁ b₀ b₁ ρ ρ' : ℝ} (ha : a₀ ≤ ρ) (ha' : ρ ≤ a₁) (hb : b₀ ≤ ρ')
    (hb' : ρ' ≤ b₁) (ha1 : 0 ≤ a₁) (hb1 : 0 ≤ b₁) :
    a₀ * b₁ + a₁ * b₀ - a₁ * b₁ ≤ ρ * ρ' := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb'),
    mul_le_mul_of_nonneg_right ha hb1, mul_le_mul_of_nonneg_left hb ha1]

/-- Summed over the pairs `k + m = N`, or any finite index set: the sandwich count is at most
the weighted Goldbach count. -/
theorem sandwich_sum {ι : Type*} (s : Finset ι) (a₀ a₁ b₀ b₁ ρ ρ' : ι → ℝ)
    (ha : ∀ i ∈ s, a₀ i ≤ ρ i) (ha' : ∀ i ∈ s, ρ i ≤ a₁ i) (hb : ∀ i ∈ s, b₀ i ≤ ρ' i)
    (hb' : ∀ i ∈ s, ρ' i ≤ b₁ i) (ha1 : ∀ i ∈ s, 0 ≤ a₁ i) (hb1 : ∀ i ∈ s, 0 ≤ b₁ i) :
    ∑ i ∈ s, (a₀ i * b₁ i + a₁ i * b₀ i - a₁ i * b₁ i) ≤ ∑ i ∈ s, ρ i * ρ' i :=
  Finset.sum_le_sum fun i hi =>
    sandwich (ha i hi) (ha' i hi) (hb i hi) (hb' i hi) (ha1 i hi) (hb1 i hi)

/-- Positivity of the sandwich count gives a Goldbach representation: if the count over the
pairs is positive, some pair has `ρ i * ρ' i > 0`. -/
theorem exists_of_pos {ι : Type*} (s : Finset ι) (ρ ρ' : ι → ℝ)
    (h : 0 < ∑ i ∈ s, ρ i * ρ' i) : ∃ i ∈ s, 0 < ρ i * ρ' i := by
  by_contra hc
  push_neg at hc
  have := Finset.sum_nonpos hc
  linarith

/-- The parity limit: minorant densities at most 1, majorant densities at least 2. -/
theorem parity_limit {u₀ u₁ v₀ v₁ : ℝ} (hu₀ : u₀ ≤ 1) (hv₀ : v₀ ≤ 1) (hu₁ : 2 ≤ u₁)
    (hv₁ : 2 ≤ v₁) : u₀ * v₁ + u₁ * v₀ - u₁ * v₁ ≤ 0 := by
  nlinarith [mul_le_mul_of_nonneg_right hu₀ (by linarith : (0 : ℝ) ≤ v₁),
    mul_le_mul_of_nonneg_left hv₀ (by linarith : (0 : ℝ) ≤ u₁),
    mul_le_mul hu₁ hv₁ (by norm_num) (by linarith)]

/-- The constants of (1.5) in P0069, `u₀ > 0.99`, `u₁ < 1.01`, `v₀ > 0.05`, `v₁ < 2.2`, with
`u₀ ≤ u₁`, `v₀ ≤ v₁`, leave a margin above 0.0055. -/
theorem bhp_margin {u₀ u₁ v₀ v₁ : ℝ} (hu0 : 0.99 < u₀) (hu : u₀ ≤ u₁) (hu1 : u₁ < 1.01)
    (hv0 : 0.05 < v₀) (hv : v₀ ≤ v₁) (hv1 : v₁ < 2.2) :
    0.0055 < u₀ * v₁ + u₁ * v₀ - u₁ * v₁ := by
  nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ v₁),
    mul_lt_mul_of_pos_left hv0 (by linarith : (0 : ℝ) < u₁),
    mul_le_mul_of_nonneg_right (le_of_lt hv1) (by linarith : (0 : ℝ) ≤ u₁ - u₀)]

end LeanLab.Routes.R5010
