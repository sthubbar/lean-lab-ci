/-
Unit U-5481, T2 FRONTIER, CLOUD 20261019T1116Z-cloud23, I-5064 continued.

The unconditional staircase of KLStair.lean pushed with the Kadiri-Lumley rows
`log x₀ = 45`, `Δ = 95381241`, and `log x₀ = 60`, `Δ = 1966196911`, and the A002386 records
806 at 171231342420521, 1132 at 1693182318746371 and 1442 at 804212830686677669. A Goldbach
number lies in every
* `(x, x + 808]` for `2 ≤ x ≤ 2 · 10^22`;
* `(x, x + 1134]` for `2 ≤ x ≤ 4.1 · 10^24`;
* `(x, x + 1444]` for `2 ≤ x ≤ 2.7 · 10^27`.
I-5020 has `1478` up to `7.86 · 10^27`.

Inputs, cited computations only, no RH: the `4 · 10^18` even check, the three KL rows, and
`GapProp` instances, the maximality of A002386 records below the next record's start
218209405436543, 43841547845541059 and 1425172824437699411. KNOWN in method.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach stays OPEN.
-/
import Mathlib
import LeanLab.GoldbachGaps.KLStair

namespace LeanLab.GoldbachGaps.KLStair2
open Real LeanLab.GoldbachGaps LeanLab.GoldbachGaps.Sumset LeanLab.GoldbachGaps.DudekStair
open LeanLab.GoldbachGaps.KLStair LeanLab.KadiriLumley2014

/-- One KL row above its `x₀`: if `X/Δ ≤ B - G - 2`, every `(x, x + G + 2]` with
`x₀ < x ≤ X` holds a Goldbach number. -/
theorem row_step {x₀ Δ B G X : ℝ} (hK : KLRow x₀ Δ) (hΔ : 1 < Δ) (hx₀ : 10 ≤ x₀)
    (hG2 : 2 ≤ G) (hgap : GapProp B G) (hBG : B - G - 2 ≤ x₀ - x₀ / Δ - 3)
    (hX : X / Δ ≤ B - G - 2) {x : ℝ} (hx : x₀ < x) (hxX : x ≤ X) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + G + 2 := by
  obtain ⟨p, hp, hpl, hpu⟩ := hK x hx
  have hΔ0 : 0 < Δ := by linarith
  have hxΔ : x / Δ ≤ B - G - 2 := le_trans (div_le_div_of_nonneg_right hxX hΔ0.le) hX
  have e : (1 - 1 / Δ) * x = x - x / Δ := by field_simp
  have hp3 : 3 ≤ p := by
    have h1Δ : 0 ≤ 1 - 1 / Δ := by
      have : 1 / Δ < 1 := by rw [div_lt_one hΔ0]; exact hΔ
      linarith
    have m := mul_le_mul_of_nonneg_left hx.le h1Δ
    have e0 : (1 - 1 / Δ) * x₀ = x₀ - x₀ / Δ := by field_simp
    have hX0 : 0 ≤ X / Δ := div_nonneg (by linarith) hΔ0.le
    have : (3 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  exact core_gen hG2 hgap hp hp3 (by linarith) hpu.le

theorem exp45_gt : (3.4e19 : ℝ) < Real.exp 45 := by
  have h := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 45
  rw [← Real.exp_nat_mul, show ((45 : ℕ) : ℝ) * 1 = 45 by norm_num] at h
  have : (3.4e19 : ℝ) < (2.7182818283 : ℝ) ^ 45 := by norm_num
  linarith

theorem exp45_lt : Real.exp 45 < 3.5e19 := by
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 45
  rw [← Real.exp_nat_mul, show ((45 : ℕ) : ℝ) * 1 = 45 by norm_num] at h
  have : (2.7182818286 : ℝ) ^ 45 < 3.5e19 := by norm_num
  linarith

theorem exp60_gt : (1.1e26 : ℝ) < Real.exp 60 := by
  have h := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 60
  rw [← Real.exp_nat_mul, show ((60 : ℕ) : ℝ) * 1 = 60 by norm_num] at h
  have : (1.1e26 : ℝ) < (2.7182818283 : ℝ) ^ 60 := by norm_num
  linarith

/-- **`(x, x + 808]` for `2 ≤ x ≤ 2 · 10^22`**, CONDITIONAL ON the cited `hE`, the rows
`hK18`, `hK45` and the record gaps `h780`, `h806`. -/
theorem goldbach_808 (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hK18 : KLRow (4 * 10 ^ 18) 36082898)
    (hK45 : KLRow (Real.exp 45) 95381241) (h780 : GapProp 9e13 778)
    (h806 : GapProp 2.18e14 806) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 2e22) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 808 := by
  rcases le_or_gt x 3.2e21 with hs | hb
  · obtain ⟨n, h1, h2, h3⟩ := goldbach_780_uncond hE hK18 h780 hx hs
    exact ⟨n, h1, h2, by linarith⟩
  · have hlo := exp45_lt
    have hup := exp45_gt
    obtain ⟨n, h1, h2, h3⟩ := row_step hK45 (by norm_num) (by linarith) (G := 806) (X := 2e22)
      (by norm_num) h806 (by
        have : Real.exp 45 / 95381241 ≤ 3.5e19 / 95381241 :=
          div_le_div_of_nonneg_right hlo.le (by norm_num)
        nlinarith) (by norm_num) (by linarith) hxX
    exact ⟨n, h1, h2, by linarith⟩

/-- **`(x, x + 1134]` for `2 ≤ x ≤ 4.1 · 10^24`**, CONDITIONAL ON the cited inputs. -/
theorem goldbach_1134 (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hK18 : KLRow (4 * 10 ^ 18) 36082898)
    (hK45 : KLRow (Real.exp 45) 95381241) (h780 : GapProp 9e13 778)
    (h806 : GapProp 2.18e14 806) (h1132 : GapProp 4.38e16 1132) {x : ℝ} (hx : 2 ≤ x)
    (hxX : x ≤ 4.1e24) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1134 := by
  rcases le_or_gt x 2e22 with hs | hb
  · obtain ⟨n, h1, h2, h3⟩ := goldbach_808 hE hK18 hK45 h780 h806 hx hs
    exact ⟨n, h1, h2, by linarith⟩
  · have hlo := exp45_lt
    obtain ⟨n, h1, h2, h3⟩ := row_step hK45 (by norm_num) (by linarith [exp45_gt])
      (G := 1132) (X := 4.1e24) (by norm_num) h1132 (by
        have : Real.exp 45 / 95381241 ≤ 3.5e19 / 95381241 :=
          div_le_div_of_nonneg_right hlo.le (by norm_num)
        nlinarith [exp45_gt]) (by norm_num) (by linarith) hxX
    exact ⟨n, h1, h2, by linarith⟩

/-- **`(x, x + 1444]` for `2 ≤ x ≤ 2.7 · 10^27`**, CONDITIONAL ON the cited inputs. -/
theorem goldbach_1444 (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (hK18 : KLRow (4 * 10 ^ 18) 36082898)
    (hK45 : KLRow (Real.exp 45) 95381241) (hK60 : KLRow (Real.exp 60) 1966196911)
    (h780 : GapProp 9e13 778) (h806 : GapProp 2.18e14 806) (h1132 : GapProp 4.38e16 1132)
    (h1442 : GapProp 1.42e18 1442) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 2.7e27) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1444 := by
  rcases le_or_gt x 4.1e24 with hs | hb
  · obtain ⟨n, h1, h2, h3⟩ := goldbach_1134 hE hK18 hK45 h780 h806 h1132 hx hs
    exact ⟨n, h1, h2, by linarith⟩
  rcases le_or_gt x 1.3e26 with hm | hl
  · obtain ⟨n, h1, h2, h3⟩ := row_step hK45 (by norm_num) (by linarith [exp45_gt])
      (G := 1442) (X := 1.3e26) (by norm_num) h1442 (by
        have : Real.exp 45 / 95381241 ≤ 3.5e19 / 95381241 :=
          div_le_div_of_nonneg_right exp45_lt.le (by norm_num)
        nlinarith [exp45_gt]) (by norm_num) (by linarith [exp45_lt]) hm
    exact ⟨n, h1, h2, by linarith⟩
  · have h60 : Real.exp 60 < 1.15e26 := exp60_lt
    obtain ⟨n, h1, h2, h3⟩ := row_step hK60 (by norm_num) (by linarith [exp60_gt])
      (G := 1442) (X := 2.7e27) (by norm_num) h1442 (by
        have : Real.exp 60 / 1966196911 ≤ 1.15e26 / 1966196911 :=
          div_le_div_of_nonneg_right h60.le (by norm_num)
        nlinarith [exp60_gt]) (by norm_num) (by linarith) hxX
    exact ⟨n, h1, h2, by linarith⟩

end LeanLab.GoldbachGaps.KLStair2
