import LeanLab.ChenDoubleSieve.Decomp587k
import LeanLab.ChenDoubleSieve.Decomp587kSplitR0J9

/-!
Phi sub window split of the middle window LEAFs `window_mid` of the cells r0j9, r0j10, r0j11
and r0j13 from the files `Decomp587kSplitR0J9` and siblings.
Wu 2004 Lemma 5.2 page 26, D2,9 to D2,13, Table 1 row 1 page 30. Source: https://arxiv.org/abs/0705.1652.
Each middle window is cut into four equal phi sub windows. This is the first step of the
zeroth order certificate plan of CLOUD S122: on a short phi sub window the range of the kernel
argument on each grid cell is short, so a per cell supremum of omega is close to its value.
Each sub window is a LEAF; the reductions `window_mid_of_leaves` are PROVED and have exactly the
statements of the parent LEAFs `window_mid`.
Numerical margins of the middle windows, from the S122 notes: r0j9 0.248 percent, r0j10 0.512,
r0j11 0.478, r0j13 0.213. A sub window maximum is at most the window maximum, so every
sub window LEAF holds numerically with at least that margin.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 400000
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587.MidSplit1122
open Wu04Functional

/-- Four consecutive closed windows cover their union. Derived bookkeeping for the phi
cuts of Wu 2004 Lemma 5.2 page 26. -/
theorem cover4 (P : ℝ → Prop) {a b c d e φ : ℝ} (ha : a ≤ φ) (he : φ ≤ e)
    (H1 : a ≤ φ → φ ≤ b → P φ) (H2 : b ≤ φ → φ ≤ c → P φ)
    (H3 : c ≤ φ → φ ≤ d → P φ) (H4 : d ≤ φ → φ ≤ e → P φ) : P φ := by
  rcases le_total φ b with h1 | h1
  · exact H1 ha h1
  rcases le_total φ c with h2 | h2
  · exact H2 h1 h2
  rcases le_total φ d with h3 | h3
  · exact H3 h2 h3
  · exact H4 h3 he

namespace R0J9

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 1 of 4, phi between 9 / 4 and 37 / 16. Class HARD. -/
theorem window_mid_1 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (9 / 4 : ℝ) ≤ φ) (hφtop : φ ≤ (37 / 16 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by
  have h := Task587.SplitR0J9.cell_integral_cap hω (n := 1) 6 r0j9_lo r0j9_hi
    (A := (2 : ℝ)) (C := (567144 / 1000000 : ℝ))
    (by norm_num) (by norm_num) (fun u hu => Wu04Buchstab.buchstab_le_567144 hω hu)
    (by intro j; fin_cases j <;> norm_num [r0j9_lo])
    (by intro j; fin_cases j <;> norm_num [r0j9_lo, r0j9_hi])
    (fun x hx => Task587.SplitR0J9.argument_ge (d := 3) (1 : Fin 3)
      (lo := r0j9_lo) (hi := r0j9_hi) (A := (2 : ℝ)) (P := (9 / 4 : ℝ))
      (by norm_num) (by intro j; fin_cases j <;> norm_num [r0j9_lo]) hφ
      (by norm_num [r0j9_hi, Fin.sum_univ_three]) hx)
  change buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤
    (567144 / 1000000 : ℝ) * (∫ x in domain (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)),
      cellPoly 6 (1 : Fin 3) r0j9_lo r0j9_hi x) at h
  rw [r0j9_integral] at h
  exact h.trans (by norm_num)

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 2 of 4, phi between 37 / 16 and 19 / 8. Class HARD. -/
theorem window_mid_2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (37 / 16 : ℝ) ≤ φ) (hφtop : φ ≤ (19 / 8 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 3 of 4, phi between 19 / 8 and 39 / 16. Class HARD. -/
theorem window_mid_3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (19 / 8 : ℝ) ≤ φ) (hφtop : φ ≤ (39 / 16 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 4 of 4, phi between 39 / 16 and 5 / 2. Class HARD. -/
theorem window_mid_4 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (39 / 16 : ℝ) ≤ φ) (hφtop : φ ≤ (5 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by
  sorry

/-- Exactly the statement of the LEAF `SplitR0J9.window_mid`, PROVED from the four sub window
LEAFs above. CONDITIONAL ON those LEAFs. Wu 2004 Lemma 5.2 page 26, D2,9, Table 1 row 1 page 30. -/
theorem window_mid_of_leaves {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (9 / 4 : ℝ) ≤ φ) (hφtop : φ ≤ (5 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) :=
  cover4 (fun φ => buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤
      ((870161 / 62500000) : ℝ)) (b := 37 / 16) (c := 19 / 8) (d := 39 / 16) hφ hφtop
    (window_mid_1 hω hz) (window_mid_2 hω hz) (window_mid_3 hω hz) (window_mid_4 hω hz)

end R0J9

namespace R0J10

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 1 of 4, phi between 21 / 10 and 17 / 8. Class HARD. -/
theorem window_mid_1 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (21 / 10 : ℝ) ≤ φ) (hφtop : φ ≤ (17 / 8 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 2 of 4, phi between 17 / 8 and 43 / 20. Class HARD. -/
theorem window_mid_2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (17 / 8 : ℝ) ≤ φ) (hφtop : φ ≤ (43 / 20 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 3 of 4, phi between 43 / 20 and 87 / 40. Class HARD. -/
theorem window_mid_3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (43 / 20 : ℝ) ≤ φ) (hφtop : φ ≤ (87 / 40 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 4 of 4, phi between 87 / 40 and 11 / 5. Class HARD. -/
theorem window_mid_4 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (87 / 40 : ℝ) ≤ φ) (hφtop : φ ≤ (11 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) := by
  sorry

/-- Exactly the statement of the LEAF `SplitR0J10.window_mid`, PROVED from the four sub window
LEAFs above. CONDITIONAL ON those LEAFs. Wu 2004 Lemma 5.2 page 26, D2,10, Table 1 row 1 page 30. -/
theorem window_mid_of_leaves {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (21 / 10 : ℝ) ≤ φ) (hφtop : φ ≤ (11 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤ ((9342453 / 1000000000) : ℝ) :=
  cover4 (fun φ => buchstabIntegral ω 1 (fun j => (r0j10_lo j : ℝ)) (fun j => (r0j10_hi j : ℝ)) φ ≤
      ((9342453 / 1000000000) : ℝ)) (b := 17 / 8) (c := 43 / 20) (d := 87 / 40) hφ hφtop
    (window_mid_1 hω hz) (window_mid_2 hω hz) (window_mid_3 hω hz) (window_mid_4 hω hz)

end R0J10

namespace R0J11

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 1 of 4, phi between 11 / 5 and 9 / 4. Class HARD. -/
theorem window_mid_1 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (11 / 5 : ℝ) ≤ φ) (hφtop : φ ≤ (9 / 4 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 2 of 4, phi between 9 / 4 and 23 / 10. Class HARD. -/
theorem window_mid_2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (9 / 4 : ℝ) ≤ φ) (hφtop : φ ≤ (23 / 10 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 3 of 4, phi between 23 / 10 and 47 / 20. Class HARD. -/
theorem window_mid_3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (23 / 10 : ℝ) ≤ φ) (hφtop : φ ≤ (47 / 20 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 4 of 4, phi between 47 / 20 and 12 / 5. Class HARD. -/
theorem window_mid_4 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (47 / 20 : ℝ) ≤ φ) (hφtop : φ ≤ (12 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) := by
  sorry

/-- Exactly the statement of the LEAF `SplitR0J11.window_mid`, PROVED from the four sub window
LEAFs above. CONDITIONAL ON those LEAFs. Wu 2004 Lemma 5.2 page 26, D2,11, Table 1 row 1 page 30. -/
theorem window_mid_of_leaves {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (11 / 5 : ℝ) ≤ φ) (hφtop : φ ≤ (12 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤ ((2272569 / 500000000) : ℝ) :=
  cover4 (fun φ => buchstabIntegral ω 1 (fun j => (r0j11_lo j : ℝ)) (fun j => (r0j11_hi j : ℝ)) φ ≤
      ((2272569 / 500000000) : ℝ)) (b := 9 / 4) (c := 23 / 10) (d := 47 / 20) hφ hφtop
    (window_mid_1 hω hz) (window_mid_2 hω hz) (window_mid_3 hω hz) (window_mid_4 hω hz)

end R0J11

namespace R0J13

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 1 of 4, phi between 419 / 200 and 339 / 160. Class HARD. -/
theorem window_mid_1 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (419 / 200 : ℝ) ≤ φ) (hφtop : φ ≤ (339 / 160 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 2 of 4, phi between 339 / 160 and 857 / 400. Class HARD. -/
theorem window_mid_2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (339 / 160 : ℝ) ≤ φ) (hφtop : φ ≤ (857 / 400 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 3 of 4, phi between 857 / 400 and 1733 / 800. Class HARD. -/
theorem window_mid_3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (857 / 400 : ℝ) ≤ φ) (hφtop : φ ≤ (1733 / 800 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30, numerical maximisation of the
Buchstab integral, middle window sub window 4 of 4, phi between 1733 / 800 and 219 / 100. Class HARD. -/
theorem window_mid_4 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (1733 / 800 : ℝ) ≤ φ) (hφtop : φ ≤ (219 / 100 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) := by
  sorry

/-- Exactly the statement of the LEAF `SplitR0J13.window_mid`, PROVED from the four sub window
LEAFs above. CONDITIONAL ON those LEAFs. Wu 2004 Lemma 5.2 page 26, D2,13, Table 1 row 1 page 30. -/
theorem window_mid_of_leaves {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : (419 / 200 : ℝ) ≤ φ) (hφtop : φ ≤ (219 / 100 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤ ((24633499 / 1000000000) : ℝ) :=
  cover4 (fun φ => buchstabIntegral ω 1 (fun j => (r0j13_lo j : ℝ)) (fun j => (r0j13_hi j : ℝ)) φ ≤
      ((24633499 / 1000000000) : ℝ)) (b := 339 / 160) (c := 857 / 400) (d := 1733 / 800) hφ hφtop
    (window_mid_1 hω hz) (window_mid_2 hω hz) (window_mid_3 hω hz) (window_mid_4 hω hz)

end R0J13

end LeanLab.ChenDoubleSieve.Task587.MidSplit1122
