import Mathlib

/-!
# Wu 2004 Lemma 4.2, the counting inequality behind the pointwise form

P0036 J. Wu 2004, Section 4, Lemma 4.2. Unit U-5402, CLOUD 20261019T1014Z-cloud22.
AI wrote the Lean code.

For one `a`, let `N₁ ≤ N₂ ≤ N₃ ≤ N₄` be the numbers of the primes of `[w, z)` coprime to `dN`
dividing `a` that lie below `d̲^{1/κ₁}`, `d̲^{1/κ₂}`, `d̲^{1/κ₃}` and `z`. `lemma42_arith` is the
inequality `5·[N₄ = 0] + Γ₂ + Γ₃ + Γ₄ ≤ Γ₁ + Γ₅ + ⋯ + Γ₂₁ + 3E` once each `Γᵢ` is replaced by
its value or bound in terms of the `Nⱼ`, the bounds `Lemma42.lean` proves. Python checked the
exact values against brute force on every pattern of at most 9 primes before this was written.
Binary Goldbach is OPEN.
-/

namespace LeanLab.ChenDoubleSieve.Wu42

set_option maxHeartbeats 4000000 in
/-- The arithmetic core of Lemma 4.2. Hypothesis `hᵢ` is the lower bound for `Γᵢ` that the
smallest-prefix count gives; `c₅` and `c₆` enter through linear lower bounds. -/
theorem lemma42_arith (N₁ N₂ N₃ N₄ L g₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ c₁₅ c₁₆ c₁₇
    c₁₈ c₁₉ c₂₀ c₂₁ e : ℕ)
    (h12 : N₁ ≤ N₂) (h23 : N₂ ≤ N₃) (h34 : N₃ ≤ N₄)
    (hL : L ≤ 5) (hL0 : 1 ≤ N₄ → L = 0) (hg : N₁ = 0 → 1 ≤ g₁)
    (h2 : c₂ ≤ N₄ + e) (h3 : c₃ ≤ N₂ + e) (h4 : c₄ ≤ N₃ + e)
    (h5 : 2 * N₂ ≤ c₅ + 3)
    (h6a : N₁ = 1 → N₃ - N₂ ≤ c₆) (h6b : 2 ≤ N₁ → 2 * (N₃ - N₂) ≤ c₆)
    (h7 : 0 < N₁ → N₁ - max 1 0 ≤ c₇)
    (h8 : 0 < N₁ → N₂ - max 1 N₁ ≤ c₈)
    (h9 : N₁ ≤ 0 ∧ 0 < N₃ ∧ N₁ ≤ 1 ∧ 1 < N₃ → N₃ - max 2 N₁ ≤ c₉)
    (h10 : N₁ ≤ 0 ∧ 0 < N₂ ∧ N₁ ≤ 1 ∧ 1 < N₂ → N₄ - max 2 N₂ ≤ c₁₀)
    (h11 : N₁ ≤ 0 ∧ 0 < N₂ ∧ N₂ ≤ 1 ∧ 1 < N₃ → N₃ - max 2 N₂ ≤ c₁₁)
    (h12' : 0 < N₁ ∧ 1 < N₁ → N₄ - max 2 N₃ ≤ c₁₂)
    (h13 : 0 < N₁ ∧ N₁ ≤ 1 ∧ 1 < N₂ → N₄ - max 2 N₂ ≤ c₁₃)
    (h14 : 0 < N₁ ∧ N₂ ≤ 1 ∧ 1 < N₄ → N₄ - max 2 N₂ ≤ c₁₄)
    (h15 : N₁ ≤ 0 ∧ 0 < N₂ ∧ N₂ ≤ 1 ∧ 1 < N₃ → N₄ - max 2 N₃ ≤ c₁₅)
    (h16 : N₂ ≤ 0 ∧ 0 < N₃ ∧ N₂ ≤ 1 ∧ 1 < N₃ ∧ N₂ ≤ 2 ∧ 2 < N₃ → N₃ - max 3 N₂ ≤ c₁₆)
    (h17 : N₂ ≤ 0 ∧ 0 < N₃ ∧ N₂ ≤ 1 ∧ 1 < N₃ ∧ N₂ ≤ 2 ∧ 2 < N₃ → N₄ - max 3 N₃ ≤ c₁₇)
    (h18 : N₂ ≤ 0 ∧ 0 < N₃ ∧ N₂ ≤ 1 ∧ 1 < N₃ ∧ N₃ ≤ 2 ∧ 2 < N₄ → N₄ - max 3 N₃ ≤ c₁₈)
    (h19 : N₁ ≤ 0 ∧ 0 < N₂ ∧ N₃ ≤ 1 ∧ 1 < N₄ ∧ N₃ ≤ 2 ∧ 2 < N₄ → N₄ - max 3 N₃ ≤ c₁₉)
    (h20 : N₂ ≤ 0 ∧ 0 < N₃ ∧ N₃ ≤ 1 ∧ 1 < N₄ ∧ N₃ ≤ 2 ∧ 2 < N₄ ∧ N₃ ≤ 3 ∧ 3 < N₄ →
      N₄ - max 4 N₃ ≤ c₂₀)
    (h21 : N₃ ≤ 0 ∧ 0 < N₄ ∧ N₃ ≤ 1 ∧ 1 < N₄ ∧ N₃ ≤ 2 ∧ 2 < N₄ ∧ N₃ ≤ 3 ∧ 3 < N₄ ∧
      N₃ ≤ 4 ∧ 4 < N₄ → N₄ - max 5 N₃ ≤ c₂₁) :
    L + c₂ + c₃ + c₄ ≤ 4 + g₁ + c₅ + c₆ + c₇ + c₈ + c₉ + c₁₀ + c₁₁ + c₁₂ + c₁₃ + c₁₄ + c₁₅
      + c₁₆ + c₁₇ + c₁₈ + c₁₉ + c₂₀ + c₂₁ + 3 * e := by
  obtain hA | hA | hA := (by omega : N₁ = 0 ∨ N₁ = 1 ∨ 2 ≤ N₁) <;>
  obtain hB | hB | hB | hB := (by omega : N₂ = 0 ∨ N₂ = 1 ∨ N₂ = 2 ∨ 3 ≤ N₂) <;>
  obtain hC | hC | hC | hC | hC | hC :=
    (by omega : N₃ = 0 ∨ N₃ = 1 ∨ N₃ = 2 ∨ N₃ = 3 ∨ N₃ = 4 ∨ 5 ≤ N₃) <;>
  obtain hD | hD | hD | hD | hD | hD := (by omega : N₄ = 0 ∨ N₄ = 1 ∨ N₄ = 2 ∨ N₄ = 3 ∨ N₄ = 4 ∨ 5 ≤ N₄) <;>
  (first | replace hL0 := hL0 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear hL0) <;>
  (first | replace hg := hg (by clear * - hA hB hC hD h12 h23 h34; omega) | clear hg) <;>
  (first | replace h6a := h6a (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h6a) <;>
  (first | replace h6b := h6b (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h6b) <;>
  (first | replace h7 := h7 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h7) <;>
  (first | replace h8 := h8 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h8) <;>
  (first | replace h9 := h9 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h9) <;>
  (first | replace h10 := h10 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h10) <;>
  (first | replace h11 := h11 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h11) <;>
  (first | replace h12' := h12' (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h12') <;>
  (first | replace h13 := h13 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h13) <;>
  (first | replace h14 := h14 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h14) <;>
  (first | replace h15 := h15 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h15) <;>
  (first | replace h16 := h16 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h16) <;>
  (first | replace h17 := h17 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h17) <;>
  (first | replace h18 := h18 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h18) <;>
  (first | replace h19 := h19 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h19) <;>
  (first | replace h20 := h20 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h20) <;>
  (first | replace h21 := h21 (by clear * - hA hB hC hD h12 h23 h34; omega) | clear h21) <;>
  omega

end LeanLab.ChenDoubleSieve.Wu42
