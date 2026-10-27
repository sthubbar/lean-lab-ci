/-
Unit U-5479, T2 FRONTIER, CLOUD 20261019T1116Z-cloud23, I-5064, the unconditional twin of I-5063.

I-5020's sumset step with the Kadiri-Lumley row `log x₀ = log(4 · 10^18)`, `Δ = 36082898`:
a prime `p` in `((1 - 1/Δ) y, y)` for `y > 4 · 10^18`, so `g = x - p < x/Δ`, and the second
prime only clears a gap at scale `x/Δ`. With the maximal gap records of OEIS A002386,
unconditionally a Goldbach number lies in every
* `(x, x + 534]` for `2 ≤ x ≤ 2.2 · 10^19`;
* `(x, x + 654]` for `2 ≤ x ≤ 2.5 · 10^20`;
* `(x, x + 780]` for `2 ≤ x ≤ 3.2 · 10^21`.
I-5020, `Sumset.goldbach_gap_1478_all`, has `1478` up to `7.86 · 10^27`.

Inputs, cited: the `4 · 10^18` even check, `KLRow (4 · 10^18) 36082898`, and one
`DudekStair.GapProp` instance each, the maximality of A002386 records. KNOWN in method.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach stays OPEN.
-/
import Mathlib
import LeanLab.GoldbachGaps.DudekStair

namespace LeanLab.GoldbachGaps.KLStair
open Real LeanLab.GoldbachGaps LeanLab.GoldbachGaps.Sumset LeanLab.GoldbachGaps.DudekStair

/-- The sumset step allowing `p` up to `x + G - 1`, as in `Sumset.core`. -/
theorem core_gen' {B G : ℝ} (hG6 : 6 ≤ G) (hgap : GapProp B G) {x : ℝ} {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hlo : x - (B - G - 2) ≤ p) (hhi : (p : ℝ) ≤ x + G - 1) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + G + 2 := by
  rcases le_or_gt (p : ℝ) x with hpx | hpx
  · exact core_gen (by linarith) hgap hp hp3 hlo hpx
  · have hpo : Odd p := hp.odd_of_ne_two (by omega)
    refine ⟨p + 3, ⟨hpo.add_odd (by decide), p, 3, hp, Nat.prime_three, rfl⟩, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

/-- The general unconditional step: if `(X + 3)/Δ ≤ B - G - 2`, every `(x, x + G + 2]` with
`2 ≤ x ≤ X` holds a Goldbach number. -/
theorem kl_stair (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hK : LeanLab.KadiriLumley2014.KLRow (4 * 10 ^ 18) 36082898)
    {B G X : ℝ} (hG6 : 6 ≤ G) (hgap : GapProp B G) (hBG : B - G - 2 ≤ 10 ^ 18)
    (hX : (X + 3) / 36082898 ≤ B - G - 2) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + G + 2 := by
  rcases le_or_gt x (4 * 10 ^ 18 - 2) with hs | hb
  · obtain ⟨n, hev, hlo, hhi⟩ := even_above x (by linarith)
    have hn4 : 4 ≤ n := by
      have : (2 : ℝ) < n := by linarith
      have h2 : 2 < n := by exact_mod_cast this
      rcases hev with ⟨k, hk⟩; omega
    have hnN : n ≤ 4 * 10 ^ 18 := by
      have : (n : ℝ) ≤ 4 * 10 ^ 18 := by linarith
      exact_mod_cast this
    exact ⟨n, ⟨hev, hE n hev hn4 hnN⟩, hlo, by linarith⟩
  · set y := max x (4 * 10 ^ 18 + 1) with hy
    have hxy : x ≤ y := le_max_left _ _
    have hyx : y ≤ x + 3 := max_le (by linarith) (by linarith)
    obtain ⟨p, hp, hpl, hpu⟩ := hK y (by have := le_max_right x (4 * 10 ^ 18 + 1); linarith)
    have hyX : y / 36082898 ≤ B - G - 2 :=
      le_trans (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hX
    have hpl' : y - y / 36082898 < p := by
      have : (1 - 1 / 36082898 : ℝ) * y = y - y / 36082898 := by ring
      linarith
    have hp3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ p := by linarith
      exact_mod_cast this
    exact core_gen' hG6 hgap hp hp3 (by linarith) (by linarith)

/-- **No RH: `(x, x + 534]` for `2 ≤ x ≤ 2.2e19`**, CONDITIONAL ON the cited computations `hE`,
`hK` and `hgap`. -/
theorem goldbach_534_uncond (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hK : LeanLab.KadiriLumley2014.KLRow (4 * 10 ^ 18) 36082898)
    (hgap : GapProp 6.1e11 532) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 2.2e19) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 534 := by
  obtain ⟨n, h1, h2, h3⟩ :=
    kl_stair hE hK (G := 532) (by norm_num) hgap (by norm_num) (by norm_num) hx hxX
  exact ⟨n, h1, h2, by linarith⟩

/-- **No RH: `(x, x + 654]` for `2 ≤ x ≤ 2.5e20`**, CONDITIONAL ON the cited computations `hE`,
`hK` and `hgap`. -/
theorem goldbach_654_uncond (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hK : LeanLab.KadiriLumley2014.KLRow (4 * 10 ^ 18) 36082898)
    (hgap : GapProp 7e12 652) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 2.5e20) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 654 := by
  obtain ⟨n, h1, h2, h3⟩ :=
    kl_stair hE hK (G := 652) (by norm_num) hgap (by norm_num) (by norm_num) hx hxX
  exact ⟨n, h1, h2, by linarith⟩

/-- **No RH: `(x, x + 780]` for `2 ≤ x ≤ 3.2e21`**, CONDITIONAL ON the cited computations `hE`,
`hK` and `hgap`. -/
theorem goldbach_780_uncond (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hK : LeanLab.KadiriLumley2014.KLRow (4 * 10 ^ 18) 36082898)
    (hgap : GapProp 9e13 778) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 3.2e21) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 780 := by
  obtain ⟨n, h1, h2, h3⟩ :=
    kl_stair hE hK (G := 778) (by norm_num) hgap (by norm_num) (by norm_num) hx hxX
  exact ⟨n, h1, h2, by linarith⟩

end LeanLab.GoldbachGaps.KLStair
