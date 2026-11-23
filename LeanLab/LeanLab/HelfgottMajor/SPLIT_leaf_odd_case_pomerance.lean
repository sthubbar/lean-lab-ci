import LeanLab.HelfgottMajor.PolyaVinogradov123

/-!
Split of the odd branch `leaf_odd_case` of P0014 Helfgott, Major arcs, page 36, display 4.20,
following the proof of its cited source, Pomerance, Remarks on the Pólya-Vinogradov inequality,
Integers 11A 2011, Article 19, Theorem 1, odd case. The arXiv text of P0014 prints 4.20 without a
reference; Pomerance's Theorem 1 has exactly these constants, as Frolenkov, arXiv 1107.0381,
display 4, restates it.

This file is a second split of `leaf_odd_case`. The older split `SPLIT_leaf_odd_case` imports the
parent file, so the parent cannot import it without a cycle; this file imports only
`PolyaVinogradov123`, which the parent already imports, so the parent can be wired to it.

Route, the Landau and Pomerance proof:

* `leaf_odd_polya_expansion`: the truncated Fourier expansion of the interval indicator, the
  sawtooth expansion with Abel summation tail bound `1/(2 pi (H+1) ||x||)`, summed against `chi`,
  with the Gauss sum `sum_a chi(a) e(ha/q) = conj chi(h) tau(chi)` and `|tau| = sqrt q`; oddness
  folds the `h` and `-h` terms into `2 - 2 cos (2 pi h n / q)`.
* `leaf_pomerance_cos_sum`: Pomerance's cosine sum lemma, his section 4, Frolenkov Lemma 2.
* `leaf_odd_pv_finite_range`: the moduli below `2048`, a finite range.

The assembly `leaf_odd_case_of_leaves` takes `H = ceil (2 sqrt q log q)` for `q >= 2048`.
No definition is introduced. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: the Pólya expansion step of Pomerance's proof, after Landau, with an explicit
truncation error. For an odd primitive character modulo `q` and every cutoff `H >= 1`, the
partial sum up to `n` is the truncated Fourier series of the interval indicator summed against
`chi`; the Gauss sums turn the main term into `tau(chi) / (pi i)` times
`sum_{h <= H} conj chi(h) (1 - cos (2 pi h n / q)) / h`, and the dropped tails of the two sawtooth
series at the points `a/q` and `(a - n)/q` are each at most `1/(2 pi (H+1) ||x||)`, which summed over
`a` gives at most `q (log q + 1 - log 2) / (pi (H+1))` each; the endpoint `a = n mod q` costs `1/2`.
HARD: a real analytic step, Fourier series of the sawtooth with an explicit tail and Gauss sums. -/
theorem leaf_odd_polya_expansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (H : ℕ) (hH : 1 ≤ H) (n : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      sqrt (q : ℝ) / π * ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) +
        2 * (q : ℝ) * (log q + 1 - log 2) / (π * ((H : ℝ) + 1)) + 1 / 2 := by
  sorry

/-- LEAF: Pomerance's cosine sum lemma, Pomerance 2011 section 4, restated as Lemma 2 of
Frolenkov, arXiv 1107.0381: for all real `alpha`, `beta` and every `N >= 1`, the sum over
`m <= N` of `|cos (m alpha) - cos (m beta)| / m` is below `log N + gamma + log 2 + 3 / N`. It is
sharp at `alpha = pi`, `beta = 0`. HARD: a real analytic step, cited and not proved in P0014. -/
theorem leaf_pomerance_cos_sum (α β : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, |cos (m * α) - cos (m * β)| / (m : ℝ) <
      log N + eulerMascheroniConstant + log 2 + 3 / N := by
  sorry

/-- LEAF: the finite range of the odd branch, moduli `q < 2048`. Pomerance's Theorem 1 covers
every `q`; the analytic assembly below closes only from `q = 2048` on, because of the additive
`1/2` and the `1/log q` losses, so these moduli are left as a finite verification of the display.
HARD: a finite but large computation over all odd primitive characters of these moduli. -/
theorem leaf_odd_pv_finite_range {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) (hsmall : q < 2048) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- The odd branch of display 4.20 from the three leaves: the finite range below `2048`, and for
`q >= 2048` the expansion leaf at `H = ceil (2 sqrt q log q)`, the cosine sum leaf at
`alpha = 2 pi n / q`, `beta = 0`, and the arithmetic of the constants, which uses
`log 2 < 0.6931471808`, `gamma < 2/3` and `pi > 3.141592`. -/
theorem leaf_odd_case_of_leaves {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  by_cases hsmall : q < 2048
  · exact leaf_odd_pv_finite_range χ hχ hq h_odd hsmall
  have hq2048 : 2048 ≤ q := Nat.le_of_not_lt hsmall
  have hqR : (2048 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2048
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set L : ℝ := log (q : ℝ) with hLdef
  set s : ℝ := sqrt (q : ℝ) with hsdef
  set P : ℝ := log 2 with hPdef
  set G : ℝ := eulerMascheroniConstant with hGdef
  have hP1 : P < 0.6931471808 := log_two_lt_d9
  have hP0 : 0.6931471803 < P := log_two_gt_d9
  have hG : G < 2 / 3 := eulerMascheroniConstant_lt_two_thirds
  have hπ : 3.141592 < π := pi_gt_d6
  have hπ0 : (0 : ℝ) < π := pi_pos
  -- `L >= 7.6`, from `log 2048 = 11 log 2`
  have hL : (7.6 : ℝ) ≤ L := by
    have h11 : log (2048 : ℝ) = 11 * P := by
      rw [hPdef, show ((2048 : ℝ)) = 2 ^ 11 by norm_num, Real.log_pow]
      norm_num
    have hmono : log (2048 : ℝ) ≤ L := Real.log_le_log (by norm_num) hqR
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  -- `s >= 45`
  have hs : (45 : ℝ) ≤ s := by
    rw [hsdef, Real.le_sqrt (by norm_num) hqpos.le]
    linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hss : s * s = (q : ℝ) := Real.mul_self_sqrt hqpos.le
  have hlogs : log s = L / 2 := by
    rw [hsdef, Real.log_sqrt hqpos.le]
  -- the cutoff
  set x : ℝ := 2 * s * L with hxdef
  have hx0 : (0 : ℝ) < x := by positivity
  set H : ℕ := Nat.ceil x with hHdef
  have hxH : x ≤ (H : ℝ) := Nat.le_ceil x
  have hHx : (H : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hH1 : 1 ≤ H := by
    have : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le hx0 hxH
    exact_mod_cast this
  have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le hx0 hxH
  -- `log H <= P + L/2 + log L + 1/x`
  have hlogH : log (H : ℝ) ≤ P + L / 2 + log L + 1 / x := by
    have h1 : log (H : ℝ) ≤ log (x + 1) := Real.log_le_log hHpos hHx.le
    have h2 : log (x + 1) - log x ≤ 1 / x := by
      rw [← Real.log_div (by linarith) hx0.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (x + 1) / x by positivity)
      have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
      linarith
    have h3 : log x = P + L / 2 + log L := by
      rw [hxdef, Real.log_mul (by positivity) hL0.ne', Real.log_mul (by norm_num) hs0.ne', hlogs]
    linarith
  have h3H : 3 / (H : ℝ) ≤ 3 / x := div_le_div_of_nonneg_left (by norm_num) hx0 hxH
  have h1x : 4 / x = 2 / (s * L) := by
    rw [hxdef]; field_simp; ring
  -- the error term
  have hErr : 2 * (q : ℝ) * (L + 1 - P) / (π * ((H : ℝ) + 1)) ≤
      s / π * (1 + (1 - P) / L) := by
    have hnum : 0 ≤ 2 * (q : ℝ) * (L + 1 - P) := by
      have : 0 ≤ L + 1 - P := by linarith
      positivity
    have hden : π * x ≤ π * ((H : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ hπ0.le; linarith
    have hstep : 2 * (q : ℝ) * (L + 1 - P) / (π * ((H : ℝ) + 1)) ≤
        2 * (q : ℝ) * (L + 1 - P) / (π * x) :=
      div_le_div_of_nonneg_left hnum (by positivity) hden
    have heq : 2 * (q : ℝ) * (L + 1 - P) / (π * x) = s / π * (1 + (1 - P) / L) := by
      rw [← hss, hxdef]
      field_simp
      ring
    linarith
  refine ciSup_le fun n => ?_
  have hexp := leaf_odd_polya_expansion χ hχ hq h_odd H hH1 n
  rw [← hLdef, ← hsdef, ← hPdef] at hexp
  have hcos := leaf_pomerance_cos_sum (2 * π * n / q) 0 H hH1
  rw [← hGdef, ← hPdef] at hcos
  -- the cosine sum dominates the sum of `(1 - cos) / h`
  have hA : ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 H, |cos (m * (2 * π * n / q)) - cos (m * 0)| / (m : ℝ) := by
    refine Finset.sum_le_sum fun h hh => ?_
    have hpos : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    apply div_le_div_of_nonneg_right _ hpos
    rw [mul_zero, cos_zero, abs_sub_comm,
      show (h : ℝ) * (2 * π * n / q) = 2 * π * h * n / q by ring]
    exact le_abs_self _
  set A : ℝ := ∑ h ∈ Finset.Icc 1 H, (1 - cos (2 * π * h * n / q)) / (h : ℝ) with hAdef
  have hAK : A ≤ 2 * P + L / 2 + log L + G + 2 / (s * L) := by
    have : A < log (H : ℝ) + G + P + 3 / (H : ℝ) := lt_of_le_of_lt hA hcos
    have h14 : 1 / x + 3 / x = 4 / x := by ring
    linarith
  set u : ℝ := s / π with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu : (14.3 : ℝ) ≤ u := by
    rw [hudef, le_div_iff₀ hπ0]
    have : π < 3.1416 := pi_lt_d4
    nlinarith
  have huA : u * A ≤ u * (2 * P + L / 2 + log L + G + 2 / (s * L)) :=
    mul_le_mul_of_nonneg_left hAK hu0
  have hsl : u * (2 / (s * L)) = 2 / (π * L) := by
    rw [hudef]; field_simp
  have h2πL : 2 / (π * L) ≤ 0.09 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hfrac : (1 - P) / L ≤ 0.0404 := by
    rw [div_le_iff₀ hL0]
    nlinarith
  have hfac : (0.0482 : ℝ) ≤ π - 2 * P - G - 1 - (1 - P) / L := by linarith
  have hkey : (14.3 : ℝ) * 0.0482 ≤ u * (π - 2 * P - G - 1 - (1 - P) / L) :=
    mul_le_mul hu hfac (by norm_num) hu0
  have e1 : 1 / (2 * π) * s * L = u * (L / 2) := by rw [hudef]; ring
  have e2 : 1 / π * s * log L = u * log L := by rw [hudef]; ring
  have e3 : s = u * π := by rw [hudef]; field_simp
  have hexp' : ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      u * A + u * (1 + (1 - P) / L) + 1 / 2 := by
    linarith [hexp, hErr]
  have hexpand : u * (2 * P + L / 2 + log L + G + 2 / (s * L)) + u * (1 + (1 - P) / L) =
      u * (L / 2) + u * log L + u * π - u * (π - 2 * P - G - 1 - (1 - P) / L) +
        u * (2 / (s * L)) := by ring
  rw [e1, e2]
  linarith [hexpand, huA, hsl, h2πL, hkey, hexp', e3]

end LeanLab.HelfgottMajor.PolyaVinogradov123
