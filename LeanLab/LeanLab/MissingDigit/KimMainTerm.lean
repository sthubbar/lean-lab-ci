/-
Kim 2024, section 1.3: the claim that the major arc main term is ≍ H for every 2n in [X, X+H]*.
P0057 J. Kim, Goldbach's problem in short intervals for numbers with a missing digit,
arXiv 2412.19975 v1. Section 1.1 defines I₁ = (X − H, X], I₂ = (0, H] and
M*(2n) = #{(h, k) ∈ I₁ × I₂ : h + k = 2n}. Section 1.3 says M*(2n) S(2n) ≍ H.
We prove M*(X + H) = 1, and that X + H is an even element of [X, X+H]* when X = g^k,
H = g^j, 1 ≤ j < k, b ≥ 2. So the lower half of ≍ fails at the top of the interval.
The almost-all theorem survives, since only a lower bound on most of the range is needed.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.MissingDigit.Statements

namespace LeanLab.MissingDigit

open Finset

/-- `M*(m) = #{(h, k) : X − H < h ≤ X, 0 < k ≤ H, h + k = m}`. -/
def Mstar (X H m : ℕ) : ℕ := ((Ioc (X - H) X ×ˢ Ioc 0 H).filter (fun p => p.1 + p.2 = m)).card

/-- Only `(X, H)` sums to `X + H`. -/
theorem Mstar_top {X H : ℕ} (hH : 1 ≤ H) (hHX : H ≤ X) : Mstar X H (X + H) = 1 := by
  unfold Mstar
  rw [Finset.card_eq_one]
  refine ⟨(X, H), ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨-, h1⟩, -, h2⟩, h3⟩
    exact Prod.ext (by omega) (by omega)
  · rintro rfl
    exact ⟨⟨⟨by omega, le_rfl⟩, by omega, le_rfl⟩, rfl⟩

/-- More generally `M*(m) = X + H + 1 − m` near the top: for `X < m ≤ X + H`, the
representations are `h = m − k` with `m − X ≤ k ≤ H`. We record the upper bound. -/
theorem Mstar_le {X H m : ℕ} (hm : X < m) : Mstar X H m ≤ X + H + 1 - m := by
  unfold Mstar
  have hsub : ((Ioc (X - H) X ×ˢ Ioc 0 H).filter (fun p => p.1 + p.2 = m)) ⊆
      (Icc (m - X) H).image (fun k => (m - k, k)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc] at hp
    rw [Finset.mem_image]
    exact ⟨p.2, Finset.mem_Icc.mpr ⟨by omega, hp.1.2.2⟩, Prod.ext (by simp; omega) rfl⟩
  calc _ ≤ ((Icc (m - X) H).image (fun k => (m - k, k))).card := Finset.card_le_card hsub
    _ ≤ (Icc (m - X) H).card := Finset.card_image_le
    _ = H + 1 - (m - X) := Nat.card_Icc _ _
    _ ≤ X + H + 1 - m := by omega

/-- `g^j` misses every digit `b ≥ 2`. -/
theorem md_pow {g b : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) : ∀ j, NoDigit g b (g ^ j) := by
  intro j
  induction j with
  | zero => rw [pow_zero, md_digit hg (by omega) (by omega)]; omega
  | succ j ih => rw [pow_succ, mul_comm, md_mul_base hg (by omega)]; exact ih

/-- `X + H = g^k + g^j` is an even element of `[X, X+H]*` for `1 ≤ j < k`, `b ≥ 2`. -/
theorem top_mem {g b j k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) (hj : 1 ≤ j) (hjk : j < k) :
    g ^ k + g ^ j ∈ (starSet g b (g ^ k) ((g ^ j : ℕ) : ℝ)).filter Even := by
  have hlt : g ^ j < g ^ k := Nat.pow_lt_pow_right (by omega) hjk
  have hpos : 0 < g ^ j := Nat.pow_pos (by omega)
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
  refine ⟨⟨⟨by omega, le_rfl⟩, ?_⟩, ?_⟩
  · rw [md_pow_add hg hb k (g ^ j) hlt]; exact md_pow hg hb j
  · rw [Nat.even_add, Nat.even_pow, Nat.even_pow]
    constructor <;> rintro ⟨h, -⟩ <;> exact ⟨h, by omega⟩

/-- **The lower half of `M*(2n) ≍ H` fails on `[X, X+H]*`**: for every `c > 0` and every
base `g ≥ 2`, digit `b ≥ 2`, there are `X = g^k`, `H = g^j` with `j` as close to `k` as one
likes, and an even `2n ∈ [X, X+H]*` with `M*(2n) = 1 < cH`. Here for each `k ≥ 2` and
`1 ≤ j < k` with `c g^j > 1`. The singular series factor is at most of size `log log n`,
which the Lean does not prove; see FINDINGS F-0007 for the numerics. -/
theorem Mstar_not_gtrsim_H {g b : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) {c : ℝ}
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) (hcj : 1 < c * (g ^ j : ℕ)) :
    ∃ m ∈ (starSet g b (g ^ k) ((g ^ j : ℕ) : ℝ)).filter Even,
      (Mstar (g ^ k) (g ^ j) m : ℝ) < c * (g ^ j : ℕ) := by
  refine ⟨g ^ k + g ^ j, top_mem hg hb hj hjk, ?_⟩
  have hlt : g ^ j ≤ g ^ k := (Nat.pow_lt_pow_right (by omega) hjk).le
  have hpos : 1 ≤ g ^ j := Nat.one_le_pow j g (by omega)
  rw [Mstar_top hpos hlt]
  simpa using hcj

end LeanLab.MissingDigit
