/-
# R-0019, averaged prime pairs and the sparse shifts 2^k − 2^l: why C₁ < 4 does not come from
# almost-all-h results

Unit U-1143, T3 MOONSHOT, run 20261020T0103Z-16649.

Route. The Linnik ladder, R-0015, K4EH.lean and K3TwoFunction.lean, needs the Goldbach pair upper
constant C₁ below the parity floor 4 for K ≤ 3. C₁ bounds prime pairs p, p + h with h in the
sparse set D(H) = {2^k − 2^l : l < k, 2^k − 2^l ≤ H}. Averages over all h are much better than
4: Lavrik-type results give the Hardy-Littlewood asymptotic for all h ≤ H outside an exceptional
set of size H/(log H)^A. The route asks whether such averages can give C₁ < 4 on D(H).

- `pow2_diff_ge`: 2^(k−1) ≤ 2^k − 2^l for l < k, so k ≤ log₂ H + 1 on D(H).
- `sparse_card`: |D(H)| ≤ (log₂ H + 2)².
- `budget`: (L + 2)² L² ≤ 2^L for L ≥ 20.
- `sparse_inside_budget`: for H ≥ 2^20, |D(H)| · (log₂ H)² ≤ H. So an exceptional set of size
  H/(log₂ H)² can contain every sparse shift: an almost-all-h statement with that budget, or any
  H/(log H)^A, is consistent with every h in D(H) failing, and gives nothing on D(H).

Parity answer: averaging over h is not a sieve and has no parity barrier, but it cannot localise to
a set of size (log H)²; the information needed on D(H) is pointwise in h, where the sieve and its
parity floor return. Numerical test numerics/r0018_sparse_shifts.py: up to 10^7 the 253 shifts
2^k − 2^l ≤ 2^23 have pair counts within 0.988 to 1.003 of Hardy-Littlewood, like random even h,
0.992 to 1.003, so the truth is C₁ = 2 there; the obstruction is proof, not fact.
KNOWN in substance, the exceptional set bounds of Lavrik, Montgomery-Vaughan and Mikawa all allow
a sparse set. BLOCKED as a route, a barrier map. AI-written Lean code, Claude, 2026-10-20.
Goldbach is open.
-/
import Mathlib

namespace LeanLab.Routes.R0019

open Finset

/-- 2^(k−1) ≤ 2^k − 2^l when l < k. -/
theorem pow2_diff_ge {k l : ℕ} (h : l < k) : 2 ^ (k - 1) ≤ 2 ^ k - 2 ^ l := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hl : 2 ^ l ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; simp; omega

/-- The sparse shift set up to H. -/
def D (H : ℕ) : Finset ℕ :=
  (((range (Nat.log 2 H + 2)) ×ˢ (range (Nat.log 2 H + 2))).filter (fun p => p.2 < p.1)).image
    (fun p => 2 ^ p.1 - 2 ^ p.2) |>.filter (· ≤ H)

/-- Every 2^k − 2^l ≤ H with l < k and H ≥ 1 lies in D(H). -/
theorem mem_D {H k l : ℕ} (hH : 1 ≤ H) (hlk : l < k) (hle : 2 ^ k - 2 ^ l ≤ H) :
    2 ^ k - 2 ^ l ∈ D H := by
  have h1 := pow2_diff_ge hlk
  have hk : k - 1 ≤ Nat.log 2 H := Nat.le_log_of_pow_le (by norm_num) (h1.trans hle)
  simp only [D, mem_filter, mem_image, mem_product, mem_range]
  exact ⟨⟨(k, l), ⟨⟨by omega, by omega⟩, hlk⟩, rfl⟩, hle⟩

/-- |D(H)| ≤ (log₂ H + 2)². -/
theorem sparse_card (H : ℕ) : (D H).card ≤ (Nat.log 2 H + 2) ^ 2 := by
  unfold D
  refine (card_filter_le _ _).trans ((card_image_le).trans ((card_filter_le _ _).trans ?_))
  rw [card_product, card_range, sq]

/-- (L + 2)² L² ≤ 2^L for L ≥ 20. -/
theorem budget : ∀ L : ℕ, 20 ≤ L → (L + 2) ^ 2 * L ^ 2 ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    have : (L + 1 + 2) ^ 2 * (L + 1) ^ 2 ≤ (L + 2) ^ 2 * L ^ 2 * 2 := by
      have h20 : 20 ≤ L := hL
      nlinarith [sq_nonneg (L : ℕ), mul_le_mul h20 h20 (by norm_num) (by omega)]
    exact this.trans (Nat.mul_le_mul_right 2 ih)

/-- **The exceptional budget swallows the sparse shifts**: for H ≥ 2^20,
|D(H)| · (log₂ H)² ≤ H. -/
theorem sparse_inside_budget (H : ℕ) (hH : 2 ^ 20 ≤ H) :
    (D H).card * (Nat.log 2 H) ^ 2 ≤ H := by
  set L := Nat.log 2 H
  have hL : 20 ≤ L := Nat.le_log_of_pow_le (by norm_num) hH
  have hpow : 2 ^ L ≤ H := Nat.pow_log_le_self 2 (by omega)
  calc (D H).card * L ^ 2 ≤ (L + 2) ^ 2 * L ^ 2 := Nat.mul_le_mul_right _ (sparse_card H)
    _ ≤ 2 ^ L := budget L hL
    _ ≤ H := hpow

/-- Vacuity: 14 = 2^4 − 2^1 ∈ D(16), and the budget hypothesis holds at H = 2^20. -/
example : 14 ∈ D 16 := by decide
example : (2 : ℕ) ^ 20 ≤ 2 ^ 20 := le_rfl

end LeanLab.Routes.R0019
