/-
P0015 H. L. Montgomery, R. C. Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27 (1975), 353-370. Read from the journal scan, impan.pl download, page images
pp. 354-369. Unit U-1423, PC run 20261021T1403Z-5629, track T1 PROVE. AI wrote this Lean code;
the Lean kernel checked it. Binary Goldbach is OPEN; Theorem 1 only says exceptions are rare.

What this file adds to MontgomeryVaughan1975.lean, U-6802, whose `Section8Inputs` asked for the
mean square (3.2) AND the major arc count (8.3):

* the paper's major arcs (2.4) p. 355 on the lab's discrete circle `ZMod (2x+1)`:
  `|k/M - a/q| ≤ P/(q x) = 1/(qQ)` with `PQ = x`, `1 ≤ q ≤ P`; `mvMajor`, `mvMinor`;
* `minor_sup_P`, the minor arc bound behind (3.3) p. 356: on `mvMinor x P`, `1 ≤ P ≤ x`,
  `|S| ≤ C (2x/√P + x^{4/5}) log⁴ x`, PROVED from the lab's unconditional Vaughan Theorem 3.1,
  `vinogradovDFT_proved`, through Dirichlet's theorem as on p. 356;
* `minor_sup_33`, (3.3) at `P = x^{6δ}`, `δ ≤ 1/15`: `|S| ≤ 3C x^{1-3δ} log⁴ x`, which is
  `X P^{-1/2} log⁴ X`, stronger in the log power than the paper's `log¹⁷`;
* `minorTerm_33`, the Parseval step (3.2) in the skeleton's form, with `T = M x^{1-2δ}`;
* `MajorCount83`, the paper's (8.3), stated for the lab's discrete major arc part, NOT proved;
* `powerSaving_of_majorCount83`, `theorem1_of_majorCount83`: Theorem 1 CONDITIONAL ON
  `MajorCount83` ALONE; the minor arc half of `Section8Inputs` is discharged;
* elementary steps of sections 6 and 8: `one_sub_exp_neg_ge`, `sub_rpow_ge_of_ge`,
  `sub_rpow_ge_of_lt` (the display before (6.21) p. 366), `card_gcd_gt_le` (the count of
  discarded `n` p. 367), `div_totient_sq_le` (`r̃ φ(r̃)^{-2} = o(1)` p. 367).
-/
import LeanLab.ExceptionalSet.MVVinogradovProved
import LeanLab.ExceptionalSet.MVMinorL4
import LeanLab.ExceptionalSet.MontgomeryVaughan1975
import LeanLab.VanDerCorput1939.Totient

namespace LeanLab.ExceptionalSet.MV75U1423

open Real Finset Filter ZMod
open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-! ### The major arcs (2.4), p. 355 -/

/-- (2.4) p. 355 on the circle `ZMod (2x+1)`: `k` is on a major arc when `|k/M - a/q| ≤ P/(q x)`
for some `1 ≤ q ≤ P` and integer `a`; with `Q = x/P` this is the paper's `1/(qQ)`. -/
noncomputable def mvMajor (x : ℕ) (P : ℝ) : Finset (ZMod (Mx x)) :=
  univ.filter (fun k => ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℤ,
    |(ZMod.val k : ℝ) / (Mx x) - (a : ℝ) / q| ≤ P / (q * x))

/-- the minor arcs `𝔪`, the complement -/
noncomputable def mvMinor (x : ℕ) (P : ℝ) : Finset (ZMod (Mx x)) := (mvMajor x P)ᶜ

/-- vacuity: `k = 0` is on the major arc at `q = 1`, `a = 0`. -/
theorem zero_mem_mvMajor (x : ℕ) {P : ℝ} (hP : 1 ≤ P) : (0 : ZMod (Mx x)) ∈ mvMajor x P := by
  simp only [mvMajor, mem_filter, mem_univ, true_and]
  refine ⟨1, le_rfl, by simpa using hP, 0, ?_⟩
  simp only [ZMod.val_zero, Nat.cast_zero, zero_div, Int.cast_zero, sub_zero, abs_zero,
    Nat.cast_one, one_mul]
  positivity

/-! ### The minor arcs, (3.3) p. 356 -/

/-- p. 356: on the minor arcs at level `1 ≤ P ≤ x` the prime sum is at most
`C (2x/√P + x^{4/5}) log⁴ x`, from Vaughan's Theorem 3.1, which the lab has unconditionally
as `vinogradovDFT_proved`, and Dirichlet's theorem with denominator bound `x/P`: the
denominator then exceeds `P`, else the point is on a major arc. PROVED. -/
theorem minor_sup_P : ∃ (C : ℝ) (X0 : ℕ), 0 ≤ C ∧ ∀ x : ℕ, X0 ≤ x → ∀ P : ℝ, 1 ≤ P →
    P ≤ x → ∀ k ∈ mvMinor x P,
      ‖𝓕 (logPrimes x) k‖ ≤ C * (2 * x / √P + (x : ℝ) ^ (4 / 5 : ℝ)) * Real.log x ^ 4 := by
  obtain ⟨C, X0, hC⟩ := vinogradovDFT_proved
  refine ⟨|C|, max X0 1, abs_nonneg C, fun x hx P hP1 hPx k hk => ?_⟩
  have hx0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hxpos : (0 : ℝ) < x := by linarith
  have hPpos : 0 < P := by linarith
  have hM : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
  have hMpos : (0 : ℝ) < Mx x := by rw [hM]; linarith
  set n := ⌊(x : ℝ) / P⌋₊ with hn
  have hxP : 1 ≤ (x : ℝ) / P := by rw [le_div_iff₀ hPpos]; linarith
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.le_floor (by simpa using hxP)
  have hnle : (n : ℝ) ≤ (x : ℝ) / P := Nat.floor_le (by positivity)
  have hnlt : (x : ℝ) / P < n + 1 := Nat.lt_floor_add_one _
  set ξ : ℝ := (ZMod.val k : ℝ) / (Mx x) with hξ
  obtain ⟨r, hr1, hr2⟩ := exists_rat_abs_sub_le_and_den_le ξ (n := n) (by omega)
  have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have hdenn : (r.den : ℝ) ≤ n := by exact_mod_cast hr2
  have hdenpos : (0 : ℝ) < r.den := by linarith
  -- the denominator exceeds `P`
  have hPden : P < r.den := by
    by_contra hcon
    push_neg at hcon
    apply (mem_compl.mp hk)
    simp only [mvMajor, mem_filter, mem_univ, true_and]
    refine ⟨r.den, r.den_pos, hcon, r.num, ?_⟩
    have hrcast : ((r.num : ℝ) / (r.den : ℝ)) = (r : ℝ) := by rw [Rat.cast_def]
    rw [hrcast]
    calc |ξ - r| ≤ 1 / ((n + 1) * r.den) := hr1
      _ ≤ P / (r.den * x) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          rw [div_lt_iff₀ hPpos] at hnlt
          nlinarith
  have happ : |ξ - r| ≤ 1 / (r.den : ℝ) ^ 2 := by
    refine le_trans hr1 (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith
  have hS := hC x hx0 k r happ
  have hsqP : 0 < √P := Real.sqrt_pos.mpr hPpos
  have t1 : (x : ℝ) / √(r.den : ℝ) ≤ x / √P :=
    div_le_div_of_nonneg_left hxpos.le hsqP (Real.sqrt_le_sqrt hPden.le)
  have t3 : √((x : ℝ) * r.den) ≤ x / √P := by
    rw [le_div_iff₀ hsqP, ← Real.sqrt_mul (by positivity)]
    have h' : (r.den : ℝ) * P ≤ x := by
      have := le_trans hdenn hnle
      rwa [le_div_iff₀ hPpos] at this
    have : (x : ℝ) * r.den * P ≤ (x : ℝ) ^ 2 := by nlinarith
    calc √((x : ℝ) * r.den * P) ≤ √((x : ℝ) ^ 2) := Real.sqrt_le_sqrt this
      _ = x := Real.sqrt_sq hxpos.le
  have hbr : (x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den)
      ≤ 2 * x / √P + (x : ℝ) ^ (4 / 5 : ℝ) := by
    have : 2 * (x : ℝ) / √P = x / √P + x / √P := by ring
    linarith
  have hL4 : 0 ≤ Real.log x ^ 4 := by positivity
  calc ‖𝓕 (logPrimes x) k‖
      ≤ C * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den)) *
          Real.log x ^ 4 := hS
    _ ≤ |C| * ((x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den)) *
          Real.log x ^ 4 := by
        have : 0 ≤ (x : ℝ) / √(r.den : ℝ) + (x : ℝ) ^ (4 / 5 : ℝ) + √((x : ℝ) * r.den) := by
          positivity
        gcongr; exact le_abs_self C
    _ ≤ |C| * (2 * x / √P + (x : ℝ) ^ (4 / 5 : ℝ)) * Real.log x ^ 4 := by gcongr

/-- `√(x^{6δ}) = x^{3δ}` -/
theorem sqrt_P (x δ : ℝ) (hx : 0 ≤ x) : √(x ^ (6 * δ)) = x ^ (3 * δ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; ring_nf

/-- (3.3) p. 356 at `P = x^{6δ}`, `0 < δ ≤ 1/15`: on the minor arcs `|S| ≤ 3C x^{1-3δ} log⁴ x`,
that is `X P^{-1/2} log⁴ X`. PROVED, unconditional. -/
theorem minor_sup_33 : ∃ (C : ℝ) (X0 : ℕ), 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 15 →
    ∀ x : ℕ, X0 ≤ x → ∀ k ∈ mvMinor x ((x : ℝ) ^ (6 * δ)),
      ‖𝓕 (logPrimes x) k‖ ≤ 3 * C * ((x : ℝ) / (x : ℝ) ^ (3 * δ)) * Real.log x ^ 4 := by
  obtain ⟨C, X0, hC0, hC⟩ := minor_sup_P
  refine ⟨C, max X0 1, hC0, fun δ hδ hδ15 x hx k hk => ?_⟩
  have hx0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hP1 : (1 : ℝ) ≤ (x : ℝ) ^ (6 * δ) := Real.one_le_rpow hx1 (by linarith)
  have hPx : (x : ℝ) ^ (6 * δ) ≤ x := by
    calc (x : ℝ) ^ (6 * δ) ≤ (x : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one _
  have h := hC x hx0 _ hP1 hPx k hk
  rw [sqrt_P _ _ hxpos.le] at h
  have hy : 0 < (x : ℝ) ^ (3 * δ) := Real.rpow_pos_of_pos hxpos _
  -- x^{4/5} ≤ x / x^{3δ}
  have h45 : (x : ℝ) ^ (4 / 5 : ℝ) ≤ x / (x : ℝ) ^ (3 * δ) := by
    rw [le_div_iff₀ hy, ← Real.rpow_add hxpos]
    calc (x : ℝ) ^ (4 / 5 + 3 * δ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one _
  have hL4 : 0 ≤ Real.log x ^ 4 := by positivity
  calc ‖𝓕 (logPrimes x) k‖ ≤ C * (2 * x / (x : ℝ) ^ (3 * δ) + (x : ℝ) ^ (4 / 5 : ℝ)) *
        Real.log x ^ 4 := h
    _ ≤ C * (2 * x / (x : ℝ) ^ (3 * δ) + x / (x : ℝ) ^ (3 * δ)) * Real.log x ^ 4 := by gcongr
    _ = 3 * C * ((x : ℝ) / (x : ℝ) ^ (3 * δ)) * Real.log x ^ 4 := by ring

/-! ### (3.2) p. 356, the Parseval step, and Theorem 1 from (8.3) alone -/

/-- `log^{10} x ≤ (10/δ)^{10} x^δ` for `x ≥ 1`. -/
theorem log_pow10_le {δ x : ℝ} (hδ : 0 < δ) (hx : 1 ≤ x) :
    Real.log x ^ 10 ≤ (10 / δ) ^ 10 * x ^ δ := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ (δ / 10) / (δ / 10) := Real.log_le_rpow_div hx0.le (by positivity)
  have h2 : Real.log x ^ 10 ≤ (x ^ (δ / 10) / (δ / 10)) ^ 10 := pow_le_pow_left₀ hL0 h1 10
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, ← rpow_natCast (x ^ (δ / 10)), ← rpow_mul hx0.le]
  have : δ / 10 * ((10 : ℕ) : ℝ) = δ := by push_cast; ring
  rw [this]
  field_simp

/-- (3.2) p. 356 in the skeleton's form: with `T = M x^{1-2δ}` the minor arc term
`M Σ_𝔪 |S|⁴ / T²` is at most `27 C² (10/δ)^{10} x^{1-δ}`. PROVED, unconditional. -/
theorem minorTerm_33 : ∃ (C : ℝ) (X0 : ℕ), ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 15 → ∀ x : ℕ, X0 ≤ x →
    (Mx x : ℝ) * (∑ k ∈ mvMinor x ((x : ℝ) ^ (6 * δ)), ‖𝓕 (logPrimes x) k‖ ^ 4) /
        ((Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ)) ^ 2
      ≤ 27 * C ^ 2 * (10 / δ) ^ 10 * (x : ℝ) ^ (1 - δ) := by
  obtain ⟨C, X0, hC0, hC⟩ := minor_sup_33
  refine ⟨C, max X0 1, fun δ hδ hδ15 x hx => ?_⟩
  have hx0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hM : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
  have hMpos : (0 : ℝ) < Mx x := by rw [hM]; linarith
  have hM3 : (Mx x : ℝ) ≤ 3 * x := by rw [hM]; linarith
  set y := (x : ℝ) ^ δ with hydef
  have hy : 0 < y := Real.rpow_pos_of_pos hxpos _
  have hy3 : (x : ℝ) ^ (3 * δ) = y ^ 3 := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; ring_nf
  have hT : (x : ℝ) ^ (1 - 2 * δ) = x / y ^ 2 := by
    rw [eq_div_iff (by positivity), hydef, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le,
      ← Real.rpow_add hxpos]
    rw [show (1 - 2 * δ + δ * ((2 : ℕ) : ℝ)) = 1 by push_cast; ring, Real.rpow_one]
  have hθ : (x : ℝ) ^ (1 - δ) = x / y := by
    rw [eq_div_iff hy.ne', hydef, ← Real.rpow_add hxpos]; norm_num
  set L := Real.log x with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hx1
  set U := 3 * C * ((x : ℝ) / y ^ 3) * L ^ 4 with hU
  have hsup : ∀ k ∈ mvMinor x ((x : ℝ) ^ (6 * δ)), ‖𝓕 (logPrimes x) k‖ ≤ U := by
    intro k hk; have := hC δ hδ hδ15 x hx0 k hk; rwa [hy3] at this
  have h1 := minorTerm_le_sup (logPrimes x) (mvMinor x ((x : ℝ) ^ (6 * δ)))
    (T := (Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ)) hsup
  have hS := sum_sq_logPrimes_le x
  have hlog := log_pow10_le hδ hx1
  rw [← hydef] at hlog
  refine h1.trans ?_
  rw [hT, hθ]
  have hU2 : U ^ 2 = 9 * C ^ 2 * x ^ 2 * L ^ 8 / y ^ 6 := by
    rw [hU]; field_simp; ring
  rw [hU2]
  have hMS : (Mx x : ℝ) * ∑ j, ‖logPrimes x j‖ ^ 2 ≤ (Mx x : ℝ) * ((Mx x : ℝ) * L ^ 2) :=
    mul_le_mul_of_nonneg_left hS hMpos.le
  have e : (Mx x : ℝ) * (9 * C ^ 2 * x ^ 2 * L ^ 8 / y ^ 6 * ((Mx x : ℝ) * ((Mx x : ℝ) * L ^ 2))) /
      ((Mx x : ℝ) * (x / y ^ 2)) ^ 2 = 9 * C ^ 2 * (Mx x : ℝ) * L ^ 10 / y ^ 2 := by
    field_simp
  calc (Mx x : ℝ) * (9 * C ^ 2 * x ^ 2 * L ^ 8 / y ^ 6 *
          ((Mx x : ℝ) * ∑ j, ‖logPrimes x j‖ ^ 2)) / ((Mx x : ℝ) * (x / y ^ 2)) ^ 2
      ≤ (Mx x : ℝ) * (9 * C ^ 2 * x ^ 2 * L ^ 8 / y ^ 6 *
          ((Mx x : ℝ) * ((Mx x : ℝ) * L ^ 2))) / ((Mx x : ℝ) * (x / y ^ 2)) ^ 2 := by
        gcongr
    _ = 9 * C ^ 2 * (Mx x : ℝ) * L ^ 10 / y ^ 2 := e
    _ ≤ 9 * C ^ 2 * (3 * x) * ((10 / δ) ^ 10 * y) / y ^ 2 := by gcongr
    _ = 27 * C ^ 2 * (10 / δ) ^ 10 * (x / y) := by field_simp; ring

/-- (8.3) p. 367, the input left open, for the lab's discrete major arc part
`Σ_{k ∈ 𝔐} S(k)² e(nk/M)`, which is `M` times the discrete `R₁(n)`: for `x ≥ X0`, at most
`K x^{1-2δ} = K X P^{-1/3}` even `n ∈ (x/2, x]` have major arc part at most
`M x^{1-2δ} = M X P^{-1/3}`. NOT proved: it needs Lemma 4.3 (Gallagher's Theorem 7),
Lemma 4.1 (the exceptional zero) and sections 5 to 7. -/
def MajorCount83 (δ K : ℝ) (X0 : ℕ) : Prop :=
  ∀ x : ℕ, X0 ≤ x →
    ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
        ‖majorPart (logPrimes x) (mvMinor x ((x : ℝ) ^ (6 * δ))) (n : ZMod (Mx x))‖
          ≤ (Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ))).card : ℕ) : ℝ) ≤ K * (x : ℝ) ^ (1 - 2 * δ)

/-- `MajorCount83` and the proved minor arc bound give `MVInputs` at `θ = 1 - δ`. -/
theorem mvInputs_of_majorCount83 {δ K : ℝ} {X0 : ℕ} (hδ : 0 < δ) (hδ15 : δ ≤ 1 / 15)
    (hK : 0 ≤ K) (h : MajorCount83 δ K X0) :
    ∃ (C₂ : ℝ) (X1 : ℕ), MVInputs (1 - δ) K C₂ X1 := by
  obtain ⟨C, X2, hC⟩ := minorTerm_33
  refine ⟨27 * C ^ 2 * (10 / δ) ^ 10, max (max X0 X2) 1, fun x hx => ?_⟩
  have hxa : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hMpos : (0 : ℝ) < Mx x := by unfold Mx; push_cast; linarith
  refine ⟨Mx x, by unfold Mx; omega, by unfold Mx; omega, logPrimes x,
    mvMinor x ((x : ℝ) ^ (6 * δ)), (Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ),
    primeSupported_logPrimes' x, by positivity, ?_, hC δ hδ hδ15 x hxb⟩
  have hle : (x : ℝ) ^ (1 - 2 * δ) ≤ (x : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  exact (h x hxa).trans (mul_le_mul_of_nonneg_left hle hK)

/-- **Montgomery-Vaughan 1975, Theorem 1, CONDITIONAL ON `MajorCount83` alone**, the paper's
(8.3) for the discrete major arc part: `E(X) ≪ X^{1-δ}`. The minor arc input (3.2), (3.3) is
discharged by the lab's Vaughan Theorem 3.1. -/
theorem powerSaving_of_majorCount83 {δ K : ℝ} {X0 : ℕ} (hδ : 0 < δ) (hδ15 : δ ≤ 1 / 15)
    (hK : 0 ≤ K) (h : MajorCount83 δ K X0) : PowerSaving := by
  obtain ⟨C₂, X1, hin⟩ := mvInputs_of_majorCount83 hδ hδ15 hK h
  exact powerSaving_of_inputs (by linarith) (by linarith) hin

/-- Theorem 1 p. 353 in its literal form, CONDITIONAL ON `MajorCount83`. -/
theorem theorem1_of_majorCount83 {δ K : ℝ} {X0 : ℕ} (hδ : 0 < δ) (hδ15 : δ ≤ 1 / 15)
    (hK : 0 ≤ K) (h : MajorCount83 δ K X0) : MV75.Theorem1 :=
  MV75.theorem1_iff_powerSaving.mpr (powerSaving_of_majorCount83 hδ hδ15 hK h)

/-! ### Section 6, the display before (6.21), p. 366 -/

/-- `1 - e^{-t} ≥ t/e` for `0 ≤ t ≤ 1`. -/
theorem one_sub_exp_neg_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * Real.exp (-1) ≤ 1 - Real.exp (-t) := by
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (-1) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  nlinarith

/-- `n^β = n e^{-(1-β) log n}` -/
theorem rpow_eq_exp {n β : ℝ} (hn : 0 < n) : n ^ β = n * Real.exp (-((1 - β) * Real.log n)) := by
  rw [Real.rpow_def_of_pos hn]
  have h := Real.exp_log hn
  calc Real.exp (Real.log n * β)
      = Real.exp (Real.log n) * Real.exp (-((1 - β) * Real.log n)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = n * Real.exp (-((1 - β) * Real.log n)) := by rw [h]

/-- p. 366, case `β̃ ≥ 1 - 1/log X`: for `1 ≤ n ≤ X`, `1 < X`, `n - n^β ≥ e^{-1}(1-β) n log n`.
PROVED. -/
theorem sub_rpow_ge_of_ge {n X β : ℝ} (hn : 1 ≤ n) (hnX : n ≤ X) (hX : 1 < X) (hβ1 : β ≤ 1)
    (hβ : 1 - 1 / Real.log X ≤ β) :
    Real.exp (-1) * ((1 - β) * n * Real.log n) ≤ n - n ^ β := by
  have hn0 : 0 < n := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX
  have hLn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hLnX : Real.log n ≤ Real.log X := Real.log_le_log hn0 hnX
  set t := (1 - β) * Real.log n with ht
  have ht0 : 0 ≤ t := mul_nonneg (by linarith) hLn
  have ht1 : t ≤ 1 := by
    have h1 : 1 - β ≤ 1 / Real.log X := by linarith
    calc t ≤ 1 / Real.log X * Real.log n := mul_le_mul_of_nonneg_right h1 hLn
      _ ≤ 1 / Real.log X * Real.log X := by gcongr
      _ = 1 := by field_simp
  have hk := one_sub_exp_neg_ge ht0 ht1
  rw [rpow_eq_exp hn0, ← ht]
  have : n * (t * Real.exp (-1)) ≤ n * (1 - Real.exp (-t)) := mul_le_mul_of_nonneg_left hk hn0.le
  nlinarith

/-- p. 366, case `β̃ < 1 - 1/log X`: for `1 ≤ n ≤ X`, `1 < X`,
`n - n^β ≥ e^{-1} n log n / log X`. PROVED. -/
theorem sub_rpow_ge_of_lt {n X β : ℝ} (hn : 1 ≤ n) (hnX : n ≤ X) (hX : 1 < X)
    (hβ : β < 1 - 1 / Real.log X) :
    Real.exp (-1) * (n * Real.log n / Real.log X) ≤ n - n ^ β := by
  have hn0 : 0 < n := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX
  have hLn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hLnX : Real.log n ≤ Real.log X := Real.log_le_log hn0 hnX
  have hmono : n ^ β ≤ n ^ (1 - 1 / Real.log X) := Real.rpow_le_rpow_of_exponent_le hn hβ.le
  set s := Real.log n / Real.log X with hs
  have hs0 : 0 ≤ s := div_nonneg hLn hLX.le
  have hs1 : s ≤ 1 := (div_le_one hLX).mpr hLnX
  have hk := one_sub_exp_neg_ge hs0 hs1
  have he : n ^ (1 - 1 / Real.log X) = n * Real.exp (-s) := by
    rw [rpow_eq_exp hn0]; congr 2; rw [hs]; ring
  rw [he] at hmono
  have : n * (s * Real.exp (-1)) ≤ n * (1 - Real.exp (-s)) := mul_le_mul_of_nonneg_left hk hn0.le
  have e : Real.exp (-1) * (n * Real.log n / Real.log X) = n * (s * Real.exp (-1)) := by
    rw [hs]; ring
  rw [e]; nlinarith

/-! ### Section 8, the discarded `n`, p. 367 -/

/-- p. 367: the `n ≤ X` with `(n, r) > D` number at most `X d(r)/D`, by
`Σ_{d | r, d > D} Σ_{n ≤ X, d | n} 1 ≤ Σ_{d | r, d > D} X/d`. PROVED. -/
theorem card_gcd_gt_le (X : ℕ) {r : ℕ} (hr : 0 < r) {D : ℝ} (hD : 0 < D) :
    (((Finset.Ioc 0 X).filter (fun n => D < (Nat.gcd n r : ℝ))).card : ℝ) ≤
      (X : ℝ) * (r.divisors.card : ℝ) / D := by
  set B : Finset ℕ := r.divisors.filter (fun d : ℕ => D < (d : ℝ))
  have hsub : (Finset.Ioc 0 X).filter (fun n : ℕ => D < (Nat.gcd n r : ℝ)) ⊆
      B.biUnion (fun d : ℕ => (Finset.Ioc 0 X).filter (fun n : ℕ => d ∣ n)) := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hnI, hg⟩ := hn
    rw [mem_biUnion]
    exact ⟨Nat.gcd n r, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n r, hr.ne'⟩, hg⟩,
      mem_filter.mpr ⟨hnI, Nat.gcd_dvd_left n r⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h1' : (((Finset.Ioc 0 X).filter (fun n : ℕ => D < (Nat.gcd n r : ℝ))).card : ℝ) ≤
      ∑ d ∈ B, ((((Finset.Ioc 0 X).filter (fun n : ℕ => d ∣ n)).card : ℕ) : ℝ) := by
    exact_mod_cast h1
  refine h1'.trans ?_
  have h2 : ∀ d ∈ B, ((((Finset.Ioc 0 X).filter (fun n : ℕ => d ∣ n)).card : ℕ) : ℝ) ≤
      (X : ℝ) / D := by
    intro d hd
    have hdD : D < (d : ℝ) := (mem_filter.mp hd).2
    have hd0 : (0 : ℝ) < d := lt_trans hD hdD
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    calc ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
      _ ≤ (X : ℝ) / D := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD hdD.le
  calc ∑ d ∈ B, ((((Finset.Ioc 0 X).filter (fun n : ℕ => d ∣ n)).card : ℕ) : ℝ)
      ≤ ∑ _d ∈ B, (X : ℝ) / D := sum_le_sum h2
    _ = (B.card : ℝ) * ((X : ℝ) / D) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (r.divisors.card : ℝ) * ((X : ℝ) / D) := by
        have : B.card ≤ r.divisors.card := card_filter_le _ _
        gcongr
    _ = (X : ℝ) * (r.divisors.card : ℝ) / D := by ring

/-- p. 367: `r̃ φ(r̃)^{-2} ≤ 4/√r̃`, so it is `o(1)` once `r̃ ≫ log P`; from the lab's
`r³ ≤ 16 φ(r)⁴`, VanDerCorput1939/Totient.lean. PROVED. -/
theorem div_totient_sq_le {r : ℕ} (hr : 0 < r) :
    (r : ℝ) / (Nat.totient r : ℝ) ^ 2 ≤ 4 / √(r : ℝ) := by
  have h := LeanLab.VanDerCorput1939.cube_le_totient_pow4 r hr
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  have hφ : 0 < Nat.totient r := Nat.totient_pos.mpr hr
  have hF : (0 : ℝ) < Nat.totient r := by exact_mod_cast hφ
  have h' : (r : ℝ) ^ 3 ≤ 16 * (Nat.totient r : ℝ) ^ 4 := by exact_mod_cast h
  have hs : 0 < √(r : ℝ) := Real.sqrt_pos.mpr hR
  have hss : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hR.le
  -- (r √r / 4)² = r³/16 ≤ φ⁴, so r √r ≤ 4 φ²
  have hsq : (r * √(r : ℝ)) ^ 2 ≤ (4 * (Nat.totient r : ℝ) ^ 2) ^ 2 := by
    have : (r * √(r : ℝ)) ^ 2 = (r : ℝ) ^ 3 := by rw [mul_pow, hss]; ring
    rw [this]; nlinarith
  have hle : (r : ℝ) * √(r : ℝ) ≤ 4 * (Nat.totient r : ℝ) ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  rw [div_le_div_iff₀ (by positivity) hs]
  linarith

end LeanLab.ExceptionalSet.MV75U1423
