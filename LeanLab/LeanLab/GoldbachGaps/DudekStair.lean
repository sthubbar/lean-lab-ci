/-
Unit U-5478, T2 FRONTIER, CLOUD 20261019T1116Z-cloud23, I-5063, refining I-5060.

Under RH, Dudek's Theorem 2 puts a prime `p` in `(x - (4/π)√x log x, x]`; then `g = x - p` is
at most `(4/π)√x log x`, about `5.9 · 10^11` at `x = 10^20`, and the second prime only has to
clear a prime gap at scale `g`, not at scale `4 · 10^18`. With the maximal gap records of
OEIS A002386, rows kernel checked in Verifications/Top50/GapsSummary.lean, their maximality
cited: under RH a Goldbach number lies in every
* `(x, x + 534]` for `2 ≤ x ≤ 10^20`, from the record gap 532 at 461690510011;
* `(x, x + 654]` for `2 ≤ x ≤ 10^22`, from 652 at 2614941710599;
* `(x, x + 780]` for `2 ≤ x ≤ 10^24`, from 778 at 42842283925351.
`goldbach_10` gives `10 log² x`, about 21000 at `10^20`; I-5060 gives 1478.

Inputs, cited, not proved here: Dudek's Theorem 2 conclusion `hD`; the `4 · 10^18` even check;
`GapProp B G`, every `(a, a + G]` with `2 ≤ a`, `a + G ≤ B` holds a prime, for
`(B, G) = (6.1 · 10^11, 532)`, `(7 · 10^12, 652)`, `(9 · 10^13, 778)`, which is the maximality
of the A002386 records below the next record's start. KNOWN in method; not claimed new.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach stays OPEN.
-/
import Mathlib
import LeanLab.GoldbachGaps.DudekRH

namespace LeanLab.GoldbachGaps.DudekStair
open Real LeanLab.GoldbachGaps LeanLab.GoldbachGaps.Sumset LeanLab.GoldbachGaps.DudekRH

/-- Every `(a, a + G]` with `2 ≤ a` and `a + G ≤ B` holds a prime. Cited instances only. -/
def GapProp (B G : ℝ) : Prop :=
  ∀ a : ℝ, 2 ≤ a → a + G ≤ B → ∃ q : ℕ, q.Prime ∧ a < q ∧ (q : ℝ) ≤ a + G

/-- The sumset step with a gap bound `G` valid up to `B`. -/
theorem core_gen {B G : ℝ} (hG2 : 2 ≤ G) (hgap : GapProp B G) {x : ℝ} {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hlo : x - (B - G - 2) ≤ p) (hhi : (p : ℝ) ≤ x) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + G + 2 := by
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  set g := x - p with hg
  have hs : max g 2 + G ≤ B := by
    have : max g 2 ≤ B - G := max_le (by linarith) (by linarith)
    linarith
  obtain ⟨q, hq, hql, hqu⟩ := hgap (max g 2) (le_max_right _ _) hs
  have hq3 : 3 ≤ q := by
    have : (2 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hql
    have : 2 < q := by exact_mod_cast this
    omega
  have hqo : Odd q := hq.odd_of_ne_two (by omega)
  have hmax : max g 2 ≤ g + 2 := max_le (by linarith) (by linarith)
  refine ⟨p + q, ⟨hpo.add_odd hqo, p, q, hp, hq, rfl⟩, ?_, ?_⟩
  · push_cast; linarith [le_max_left g 2]
  · push_cast; linarith

/-- The general step: if `(4/π)√x log x ≤ B - G - 2` on `[4 · 10^18 - 2, X]`, then under the
inputs every `(x, x + G + 2]` with `2 ≤ x ≤ X` holds a Goldbach number. -/
theorem stair (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    {B G X : ℝ} (hG2 : 2 ≤ G) (hgap : GapProp B G) (hBG : B - G - 2 ≤ 4 * 10 ^ 18 - 10)
    (hdu : ∀ x : ℝ, 4 * 10 ^ 18 - 2 < x → x ≤ X → LeanLab.Dudek2014.dudekH x ≤ B - G - 2)
    {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ X) :
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
  · obtain ⟨p, hp, hpl, hpu⟩ := hD x hx
    have hH := hdu x hb hxX
    have hp3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ p := by linarith
      exact_mod_cast this
    exact core_gen hG2 hgap hp hp3 (by linarith) hpu

/-- `(4/π)√x log x ≤ c √X (k log 10)` for `1 ≤ x ≤ X = 10^k`, the shape used below. -/
theorem dudekH_le_pow {x : ℝ} {k : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ 10 ^ k) :
    LeanLab.Dudek2014.dudekH x ≤ 1.273241 * √((10 : ℝ) ^ k) * (k * 2.30261) := by
  unfold LeanLab.Dudek2014.dudekH
  have hl : Real.log x ≤ k * 2.30261 := by
    have a := Real.log_le_log (by linarith) h2
    rw [Real.log_pow] at a
    have := log_ten_lt
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1
  have hs : √x ≤ √((10 : ℝ) ^ k) := Real.sqrt_le_sqrt h2
  have hpi := Real.pi_gt_d6
  have hq : 4 / π ≤ 1.273241 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  exact mul_le_mul (mul_le_mul hq hs (Real.sqrt_nonneg _) (by norm_num)) hl hl0 (by positivity)

/-- **Under RH, `(x, x + 534]` for `2 ≤ x ≤ 10^20`**, CONDITIONAL ON Dudek's Theorem 2
conclusion `hD`, the `4 · 10^18` even check `hE` and the cited record gap `hgap`. -/
theorem goldbach_534 (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hgap : GapProp 6.1e11 532) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 10 ^ 20) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 534 := by
  have := stair hE hD (G := 532) (X := 10 ^ 20) (by norm_num) hgap (by norm_num) (fun y hy hyX => by
    refine (dudekH_le_pow (k := 20) (by linarith) hyX).trans ?_
    rw [show ((10 : ℝ) ^ 20) = (10 ^ 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num) hx hxX
  obtain ⟨n, h1, h2, h3⟩ := this
  exact ⟨n, h1, h2, by linarith⟩

/-- **Under RH, `(x, x + 654]` for `2 ≤ x ≤ 10^22`**, CONDITIONAL ON Dudek's Theorem 2
conclusion `hD`, the `4 · 10^18` even check `hE` and the cited record gap `hgap`. -/
theorem goldbach_654 (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hgap : GapProp 7e12 652) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 10 ^ 22) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 654 := by
  have := stair hE hD (G := 652) (X := 10 ^ 22) (by norm_num) hgap (by norm_num) (fun y hy hyX => by
    refine (dudekH_le_pow (k := 22) (by linarith) hyX).trans ?_
    rw [show ((10 : ℝ) ^ 22) = (10 ^ 11) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num) hx hxX
  obtain ⟨n, h1, h2, h3⟩ := this
  exact ⟨n, h1, h2, by linarith⟩

/-- **Under RH, `(x, x + 780]` for `2 ≤ x ≤ 10^24`**, CONDITIONAL ON Dudek's Theorem 2
conclusion `hD`, the `4 · 10^18` even check `hE` and the cited record gap `hgap`. -/
theorem goldbach_780 (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hgap : GapProp 9e13 778) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 10 ^ 24) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 780 := by
  have := stair hE hD (G := 778) (X := 10 ^ 24) (by norm_num) hgap (by norm_num) (fun y hy hyX => by
    refine (dudekH_le_pow (k := 24) (by linarith) hyX).trans ?_
    rw [show ((10 : ℝ) ^ 24) = (10 ^ 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num) hx hxX
  obtain ⟨n, h1, h2, h3⟩ := this
  exact ⟨n, h1, h2, by linarith⟩

/-- **Under RH, `(x, x + 1134]` for `2 ≤ x ≤ 10^28`**, CONDITIONAL ON `hD`, `hE` and the
cited record gap `hgap`, 1132 at 1693182318746371, next record 1184 at 43841547845541059. -/
theorem goldbach_1134_RH (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hgap : GapProp 4.38e16 1132) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 10 ^ 28) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1134 := by
  have := stair hE hD (G := 1132) (X := 10 ^ 28) (by norm_num) hgap (by norm_num) (fun y hy hyX => by
    refine (dudekH_le_pow (k := 28) (by linarith) hyX).trans ?_
    rw [show ((10 : ℝ) ^ 28) = (10 ^ 14) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num) hx hxX
  obtain ⟨n, h1, h2, h3⟩ := this
  exact ⟨n, h1, h2, by linarith⟩

/-- **Under RH, `(x, x + 1444]` for `2 ≤ x ≤ 10^32`**, CONDITIONAL ON `hD`, `hE` and the
cited record gap `hgap`, 1442 at 804212830686677669, next record 1476 at 1425172824437699411. -/
theorem goldbach_1444_RH (hE : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hD : ∀ x : ℝ, 2 ≤ x → LeanLab.Dudek2014.PrimeInDudekInterval x)
    (hgap : GapProp 1.42e18 1442) {x : ℝ} (hx : 2 ≤ x) (hxX : x ≤ 10 ^ 32) :
    ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + 1444 := by
  have := stair hE hD (G := 1442) (X := 10 ^ 32) (by norm_num) hgap (by norm_num) (fun y hy hyX => by
    refine (dudekH_le_pow (k := 32) (by linarith) hyX).trans ?_
    rw [show ((10 : ℝ) ^ 32) = (10 ^ 16) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num) hx hxX
  obtain ⟨n, h1, h2, h3⟩ := this
  exact ⟨n, h1, h2, by linarith⟩

end LeanLab.GoldbachGaps.DudekStair
