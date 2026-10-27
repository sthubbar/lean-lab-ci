/-
P0057 J. Kim, "Goldbach's problem in short intervals for numbers with a missing digit",
arXiv 2412.19975 v1. Even base analogue of `pow_add_one_mem` and of
`existsGoldbachOddBase_of_almostAll` in `Statements.lean`.
For odd `g` the lab used the even number `g^k + 1`. For even `g` that number is odd, so we use
`g^k + g`, whose base `g` digits are `1` at places `k` and `1` and `0` elsewhere; it needs
`k ≥ 2` and `H ≥ g`. Under the Theorem 1.2 shape `H ≥ X^{a+ε}` with `X = g^k`, so `H ≥ g` once
`k ε ≥ 1`. This removes the odd base restriction from the existence corollary.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. The corollary is conditional on the Theorem 1.2 shape, which Kim proves
only under a zero-free strip assumption.
-/
import Mathlib
import LeanLab.MissingDigit.Statements

namespace LeanLab.MissingDigit
open Finset Real

attribute [local instance] Classical.propDecidable

/-- For even `g ≥ 3`, `b ≥ 2`, `k ≥ 2` and `H ≥ g`, the even number `g^k + g` lies in
`[g^k, g^k+H]^*`. -/
theorem pow_add_base_mem {g b k : ℕ} (hg : 3 ≤ g) (hge : Even g) (hb : 2 ≤ b) (hk : 2 ≤ k)
    {H : ℝ} (hH : (g : ℝ) ≤ H) : g ^ k + g ∈ (starSet g b (g ^ k) H).filter Even := by
  have hlt : g < g ^ k := by
    calc g = g ^ 1 := (pow_one g).symm
      _ < g ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  have hfl : g ≤ ⌊H⌋₊ := Nat.le_floor hH
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, (hge.pow_of_ne_zero (by omega)).add hge⟩
  rw [md_pow_add (by omega) hb k g hlt]
  have h1 := md_mul_base (g := g) (b := b) (y := 1) (by omega) (by omega)
  rw [mul_one] at h1
  rw [h1, md_digit (by omega) (by omega) (by omega)]
  omega

/-- For `g ≥ 2`, `ε > 0`, `a ≥ 0` and `k ε ≥ 1`, the lower end `X^{a+ε}` of the admissible
range, `X = g^k`, is at least `g`. -/
theorem base_le_rpow {g k : ℕ} (hg : 2 ≤ g) {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hk : 1 ≤ (k : ℝ) * ε) : (g : ℝ) ≤ ((g ^ k : ℕ) : ℝ) ^ (a + ε) := by
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hX : (1 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := pow_ge_one_real (by omega)
  calc (g : ℝ) = (g : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (g : ℝ) ^ ((k : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le hg1 hk
    _ = ((g ^ k : ℕ) : ℝ) ^ ε := by
        rw [Real.rpow_mul (by positivity), Real.rpow_natCast, Nat.cast_pow]
    _ ≤ ((g ^ k : ℕ) : ℝ) ^ (a + ε) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- Existence form for every base: as `ExistsGoldbachOddBase` but with no parity condition on
`g`. -/
def ExistsGoldbachAnyBase (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 →
    ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ∃ n ∈ starSet g b (g ^ k) H, Even n ∧ IsGoldbachSum n

/-- The admissible set always holds an even element once `k ≥ 2` and `k ε ≥ 1`, for every base
`g ≥ 3` and digit `b ≥ 2`. -/
theorem evenCount_pos {g b k : ℕ} (hg : 3 ≤ g) (hb : 2 ≤ b) (hk : 2 ≤ k) {a ε : ℝ}
    (ha : 0 ≤ a) (hε : 0 < ε) (hkε : 1 ≤ (k : ℝ) * ε) {H : ℝ}
    (h1 : ((g ^ k : ℕ) : ℝ) ^ (a + ε) ≤ H) : 0 < evenCount g b (g ^ k) H := by
  have hH1 : (1 : ℝ) ≤ H := by
    have hX : (1 : ℝ) ≤ ((g ^ k : ℕ) : ℝ) := pow_ge_one_real (by omega)
    exact le_trans (Real.one_le_rpow hX (by linarith)) h1
  rcases Nat.even_or_odd g with hge | hgo
  · exact Finset.card_pos.2 ⟨_, pow_add_base_mem hg hge hb hk
      (le_trans (base_le_rpow (by omega) ha hε hkε) h1)⟩
  · exact Finset.card_pos.2 ⟨_, pow_add_one_mem hg hgo hb (by omega) hH1⟩

/-- Theorem 1.2 shape with a nonnegative exponent gives an even Goldbach sum in every
admissible `[X, X+H]^*`, for every base, odd or even. -/
theorem existsGoldbachAnyBase_of_almostAll {a : ℝ} (ha : 0 ≤ a) (h : AlmostAllGoldbach a) :
    ExistsGoldbachAnyBase a := by
  intro ε hε
  obtain ⟨g₀, hg₀⟩ := h ε hε
  refine ⟨max g₀ 3, fun g b hg hb hbg => ?_⟩
  have hg3 : 3 ≤ g := le_trans (le_max_right _ _) hg
  obtain ⟨K₀, hK⟩ := hg₀ g b (le_trans (le_max_left _ _) hg) hb hbg 1 1 one_pos one_pos
    (1 / 2) (by norm_num)
  refine ⟨max K₀ (max 2 ⌈1 / ε⌉₊), fun k H hk h1 h2 => ?_⟩
  have hk2 : 2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkε : 1 ≤ (k : ℝ) * ε := by
    have hc : ⌈1 / ε⌉₊ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have : 1 / ε ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hc)
    rwa [div_le_iff₀ hε] at this
  have hexc := hK k H (le_trans (le_max_left _ _) hk) (by rwa [one_mul])
    (by rwa [one_mul])
  have hpos := evenCount_pos hg3 hb hk2 ha hε hkε h1
  apply exists_goldbach_of_exc_lt
  have : (0 : ℝ) < evenCount g b (g ^ k) H := by exact_mod_cast hpos
  exact_mod_cast (show (excCount g b (g ^ k) H : ℝ) < evenCount g b (g ^ k) H by linarith)

/-- The any-base form contains the odd-base form. -/
theorem existsGoldbachOddBase_of_anyBase {a : ℝ} (h : ExistsGoldbachAnyBase a) :
    ExistsGoldbachOddBase a := by
  intro ε hε
  obtain ⟨g₀, hg₀⟩ := h ε hε
  exact ⟨g₀, fun g b hg _ hb hbg => hg₀ g b hg hb hbg⟩

/-- Kernel check of the even base witness: base 10, digit 3, `k = 2`: `110` has no digit `3`. -/
theorem nd_110 : NoDigit 10 3 110 := by decide +kernel

end LeanLab.MissingDigit
