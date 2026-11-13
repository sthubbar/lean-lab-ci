import Mathlib
import LeanLab.ExceptionalSet.State1539

/-!
Upstream supply of the fractional boundary count for `DecompJ200.leaf_major_fractional_boundary`.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621.

Page 359, proof of Lemma 4: the paper takes `c = 1/2` in Theorem 2 and omits the details, and
says that a very simple variant yields the upper bound `≪ (z₁ - z₂) N + N ℰ^{-1}`, which suffices
for the paper's applications. Page 364 after display (23) applies that upper bound to the `n` with
`{F(n)} < Δ` or `{F(n)} > 1 - Δ`, giving `O(N Δ + N ℰ^{-1})`.

This file proves the needed upper bound from Theorem 2 alone, by the standard Fejér square:
with `z = Σ_{0 ≤ j < H} e(j x)`, `Re z ≥ H/2` whenever `x` is within `Δ` of an integer and
`H Δ ≤ 1/6`, while `Σ_n |z_n|^2 = Σ_{j,k} Σ_n e((j-k) F(n))`. The `j = k` terms give the main
term and Theorem 2 with `c = 1/2` bounds the others. The result is CONDITIONAL ON the explicit
Theorem 2 hypothesis only; no other input is used.

`F_growth`, `F_ratio_mono`, `window_upper` and `window_lower` are copies of the proved lemmas of
`Decomp371a`, restated for the explicit window set so that `DecompJ200`, which defines `window`
and is imported by `Decomp371a`, can use them without an import cycle.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BoundarySupplyJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (eC calE nu expSumF Theorem2)

/-! ### The additive character -/

theorem eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eC_conj (a : ℝ) : (starRingEnd ℂ) (eC a) = eC (-a) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem eC_eq_exp (a : ℝ) : eC a = Complex.exp (((2 * π * a : ℝ) : ℂ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

theorem norm_eC (a : ℝ) : ‖eC a‖ = 1 := by
  rw [eC_eq_exp]
  exact Complex.norm_exp_ofReal_mul_I _

theorem re_eC (a : ℝ) : (eC a).re = Real.cos (2 * π * a) := by
  rw [eC_eq_exp]
  exact Complex.exp_ofReal_mul_I_re _

/-! ### The Fejér square, page 359 -/

/-- Page 359, the simple variant of Lemma 4. Within `Δ` of an integer, with `H Δ ≤ 1/6`, each of
the `H` terms of `Σ_{j < H} e(j x)` has real part at least `cos(π/3) = 1/2`. -/
theorem re_sum_near (x Δ : ℝ) (H : ℕ) (hHΔ : (H : ℝ) * Δ ≤ 1 / 6)
    (hx : Int.fract x < Δ ∨ 1 - Δ < Int.fract x) :
    (H : ℝ) / 2 ≤ (∑ j ∈ range H, eC ((j : ℝ) * x)).re := by
  obtain ⟨t, m, htΔ, hxt⟩ : ∃ t : ℝ, ∃ m : ℤ, |t| ≤ Δ ∧ x = m + t := by
    rcases hx with h | h
    · exact ⟨Int.fract x, ⌊x⌋, by rw [abs_of_nonneg (Int.fract_nonneg x)]; exact h.le,
        (Int.floor_add_fract x).symm⟩
    · refine ⟨Int.fract x - 1, ⌊x⌋ + 1, ?_, ?_⟩
      · rw [abs_of_nonpos (by linarith [Int.fract_lt_one x])]
        linarith
      · push_cast
        linarith [Int.floor_add_fract x]
  rw [Complex.re_sum]
  have hterm : ∀ j ∈ range H, (1 : ℝ) / 2 ≤ (eC ((j : ℝ) * x)).re := by
    intro j hj
    have hjH : (j : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hj).le
    rw [re_eC]
    have hcos : Real.cos (2 * π * ((j : ℝ) * x)) = Real.cos (2 * π * j * t) := by
      rw [hxt, show 2 * π * ((j : ℝ) * ((m : ℝ) + t)) =
        2 * π * j * t + ((j * m : ℤ) : ℝ) * (2 * π) by push_cast; ring]
      exact Real.cos_add_int_mul_two_pi _ _
    rw [hcos, ← Real.cos_abs, ← Real.cos_pi_div_three]
    have hjt : (j : ℝ) * |t| ≤ 1 / 6 :=
      le_trans (mul_le_mul hjH htΔ (abs_nonneg _) (Nat.cast_nonneg _)) hHΔ
    have habs : |2 * π * (j : ℝ) * t| ≤ π / 3 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * j)]
      have h2 := mul_le_mul_of_nonneg_left hjt (by positivity : (0 : ℝ) ≤ 2 * π)
      nlinarith [Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) habs
  calc (H : ℝ) / 2 = ∑ j ∈ range H, (1 : ℝ) / 2 := by simp; ring
    _ ≤ _ := sum_le_sum hterm

/-- The Fejér identity `|Σ_{j < H} e(j x)|^2 = Σ_{j,k < H} e((j - k) x)`. -/
theorem norm_sq_sum_eq (x : ℝ) (H : ℕ) :
    ‖∑ j ∈ range H, eC ((j : ℝ) * x)‖ ^ 2 =
      (∑ j ∈ range H, ∑ k ∈ range H, eC ((((j : ℤ) - k : ℤ) : ℝ) * x)).re := by
  set z := ∑ j ∈ range H, eC ((j : ℝ) * x)
  have h1 : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, map_sum, Finset.sum_mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  rw [eC_conj, ← eC_add]
  congr 1
  push_cast
  ring

/-- Page 359, the simple variant of Lemma 4 in abstract form: if every nonzero frequency `h` with
`|h| < H` has `‖Σ_{n ∈ I} e(h φ(n))‖ ≤ Q`, then at most `4 #I / H + 4 Q` members of `I` have
`φ(n)` within `Δ` of an integer, provided `H Δ ≤ 1/6`. -/
theorem fejer_count (I : Finset ℕ) (φ : ℕ → ℝ) (H : ℕ) (hH : 1 ≤ H) (Δ Q : ℝ)
    (hHΔ : (H : ℝ) * Δ ≤ 1 / 6) (hQ0 : 0 ≤ Q)
    (hQ : ∀ h : ℤ, h ≠ 0 → |h| < H → ‖∑ n ∈ I, eC ((h : ℝ) * φ n)‖ ≤ Q) :
    ((I.filter (fun n => Int.fract (φ n) < Δ ∨ 1 - Δ < Int.fract (φ n))).card : ℝ) ≤
      4 * I.card / H + 4 * Q := by
  classical
  set G := I.filter (fun n => Int.fract (φ n) < Δ ∨ 1 - Δ < Int.fract (φ n))
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hlow : (G.card : ℝ) * ((H : ℝ) / 2) ^ 2 ≤
      ∑ n ∈ I, ‖∑ j ∈ range H, eC ((j : ℝ) * φ n)‖ ^ 2 := by
    calc (G.card : ℝ) * ((H : ℝ) / 2) ^ 2 = ∑ n ∈ G, ((H : ℝ) / 2) ^ 2 := by simp
      _ ≤ ∑ n ∈ G, ‖∑ j ∈ range H, eC ((j : ℝ) * φ n)‖ ^ 2 := by
        apply sum_le_sum
        intro n hn
        have hre := re_sum_near (φ n) Δ H hHΔ (mem_filter.mp hn).2
        have h0 : (0 : ℝ) ≤ (H : ℝ) / 2 := by positivity
        have hn2 := Complex.abs_re_le_norm (∑ j ∈ range H, eC ((j : ℝ) * φ n))
        have hre' : (H : ℝ) / 2 ≤ ‖∑ j ∈ range H, eC ((j : ℝ) * φ n)‖ :=
          hre.trans ((le_abs_self _).trans hn2)
        exact pow_le_pow_left₀ h0 hre' 2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
  have hrw : ∑ n ∈ I, ‖∑ j ∈ range H, eC ((j : ℝ) * φ n)‖ ^ 2 =
      (∑ j ∈ range H, ∑ k ∈ range H,
        ∑ n ∈ I, eC ((((j : ℤ) - k : ℤ) : ℝ) * φ n)).re := by
    simp_rw [norm_sq_sum_eq]
    rw [← Complex.re_sum]
    congr 1
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  have hterm : ∀ j ∈ range H, ∀ k ∈ range H,
      ‖∑ n ∈ I, eC ((((j : ℤ) - k : ℤ) : ℝ) * φ n)‖ ≤
        (if j = k then (I.card : ℝ) else 0) + Q := by
    intro j hj k hk
    by_cases hjk : j = k
    · subst hjk
      simp only [ite_true]
      have hc : ‖∑ n ∈ I, eC ((((j : ℤ) - j : ℤ) : ℝ) * φ n)‖ ≤ I.card := by
        refine (norm_sum_le _ _).trans ?_
        simp [norm_eC]
      linarith
    · simp only [hjk, ite_false, zero_add]
      apply hQ
      · exact sub_ne_zero.mpr (by exact_mod_cast hjk)
      · have hj' := mem_range.mp hj
        have hk' := mem_range.mp hk
        rw [abs_lt]
        constructor <;> omega
  have hup : ∑ n ∈ I, ‖∑ j ∈ range H, eC ((j : ℝ) * φ n)‖ ^ 2 ≤
      H * I.card + H * H * Q := by
    rw [hrw]
    calc _ ≤ ‖∑ j ∈ range H, ∑ k ∈ range H,
            ∑ n ∈ I, eC ((((j : ℤ) - k : ℤ) : ℝ) * φ n)‖ := Complex.re_le_norm _
      _ ≤ ∑ j ∈ range H, ‖∑ k ∈ range H,
            ∑ n ∈ I, eC ((((j : ℤ) - k : ℤ) : ℝ) * φ n)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range H, ∑ k ∈ range H,
            ‖∑ n ∈ I, eC ((((j : ℤ) - k : ℤ) : ℝ) * φ n)‖ :=
          sum_le_sum (fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j ∈ range H, ∑ k ∈ range H, ((if j = k then (I.card : ℝ) else 0) + Q) :=
          sum_le_sum (fun j hj => sum_le_sum (fun k hk => hterm j hj k hk))
      _ = H * I.card + H * H * Q := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range]
          rw [Finset.sum_ite_of_true (fun x hx => mem_range.mp hx)]
          simp
          ring
  have hkey : (G.card : ℝ) * ((H : ℝ) / 2) ^ 2 ≤ H * I.card + H * H * Q := hlow.trans hup
  have hsq : (0 : ℝ) < ((H : ℝ) / 2) ^ 2 := by positivity
  rw [show 4 * (I.card : ℝ) / H + 4 * Q = (H * I.card + H * H * Q) / (((H : ℝ) / 2) ^ 2) by
    field_simp
    ring]
  exact (le_div_iff₀ hsq).mpr hkey

/-! ### The window, copies from `Decomp371a` -/

/-- The window of section 5, p. 366, written out: definitionally `DecompJ200.window γ N`. -/
noncomputable def windowSet (γ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => F γ N / 2 < nu γ n ∧ (nu γ n : ℝ) ≤ F γ N)

/-- Copy of `BrudernPerelliExplicit.F_mono`: `F γ` is monotone on `n ≥ 1` for `γ > 0`. -/
theorem F_mono {γ : ℝ} (hγ : 0 < γ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    F γ a ≤ F γ b := by
  unfold F
  apply Real.exp_le_exp.mpr
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply Real.rpow_le_rpow (Real.log_nonneg ha')
    (Real.log_le_log (by linarith) hab') hγ.le

/-- Copy of `Decomp371a.F_growth`, P0082 page 372 display 47. -/
theorem F_growth (γ x y : ℝ) (hγ : 1 < γ) (hx : 8 ≤ x) (hxy : x ≤ y) :
    γ * (y - x) ≤ F γ y - F γ x := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have ht := Real.log_two_gt_d9
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hd (z : ℝ) (hz : 8 ≤ z) :
      HasDerivAt (F γ) (F γ z * (γ * Real.log z ^ (γ - 1)) / z) z := by
    have hz0 : 0 < z := by linarith
    have hL : 0 < Real.log z := Real.log_pos (by linarith)
    convert ((Real.hasDerivAt_log hz0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
    · rfl
    · dsimp [F]; ring
  have hbound (z : ℝ) (hz : 8 ≤ z) :
      γ ≤ deriv (F γ) z := by
    have hz0 : 0 < z := by linarith
    have hL : 1 ≤ Real.log z :=
      hlog8.trans (Real.log_le_log (by norm_num) hz)
    have hF : z ≤ F γ z := by
      calc z = Real.exp (Real.log z) := (Real.exp_log hz0).symm
        _ ≤ Real.exp (Real.log z ^ γ) := by
          apply Real.exp_le_exp.mpr
          simpa only [Real.rpow_one] using
            (Real.rpow_le_rpow_of_exponent_le hL hγ.le)
    have hp : 1 ≤ Real.log z ^ (γ - 1) := Real.one_le_rpow hL (by linarith)
    rw [(hd z hz).deriv, le_div_iff₀ hz0]
    calc γ * z ≤ γ * F γ z := mul_le_mul_of_nonneg_left hF (by linarith)
      _ ≤ (γ * F γ z) * Real.log z ^ (γ - 1) :=
        le_mul_of_one_le_right (mul_nonneg (by linarith) (Real.exp_pos _).le) hp
      _ = _ := by ring
  apply (convex_Ici (8 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => hbound z (interior_subset hz)) x hx y (hx.trans hxy) hxy

/-- Copy of `Decomp371a.window_upper`, P0082 page 365 floor window. -/
theorem window_upper (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 8 ≤ N)
    (n : ℕ) (hn : n ∈ windowSet γ N) : n ≤ N := by
  by_contra hnN
  have hstep : (1 : ℝ) ≤ (n : ℝ) - N := by
    have hr : (N : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : N + 1 ≤ n)
    linarith
  have hg := F_growth γ N n hγ (by exact_mod_cast hN) (by exact_mod_cast (by omega : N ≤ n))
  have hγ0 : 0 ≤ γ := by linarith
  have hgap : 1 < F γ n - F γ N := by
    have hm := mul_le_mul_of_nonneg_left hstep hγ0
    nlinarith
  have hfloor : F γ n < (nu γ n : ℝ) + 1 := by
    simpa only [nu] using Int.lt_floor_add_one (F γ n)
  have hnu : (nu γ n : ℝ) ≤ F γ N := (Finset.mem_filter.mp hn).2.2
  linarith

/-- Copy of `Decomp371a.F_ratio_mono`, P0082 page 372 display 47. -/
theorem F_ratio_mono (γ x y : ℝ) (hγ : 1 < γ) (hx : 8 ≤ x) (hxy : x ≤ y) :
    F γ x / x ≤ F γ y / y := by
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have ht := Real.log_two_gt_d9
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hd (z : ℝ) (hz : 8 ≤ z) : HasDerivAt (fun z => F γ z / z)
      (F γ z * (γ * Real.log z ^ (γ - 1) - 1) / z ^ 2) z := by
    have hz0 : 0 < z := by linarith
    have hL : 0 < Real.log z := Real.log_pos (by linarith)
    have hF : HasDerivAt (F γ) (F γ z * (γ * Real.log z ^ (γ - 1)) / z) z := by
      convert ((Real.hasDerivAt_log hz0.ne').rpow_const (p := γ) (Or.inl hL.ne')).exp using 1
      · rfl
      · dsimp [F]; ring
    convert hF.div (hasDerivAt_id z) hz0.ne' using 1
    · rfl
    · dsimp
      field_simp
  apply monotoneOn_of_deriv_nonneg (convex_Ici (8 : ℝ))
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => ?_) hx (hx.trans hxy) hxy
  have hz8 : 8 ≤ z := interior_subset hz
  have hL : 1 ≤ Real.log z := hlog8.trans (Real.log_le_log (by norm_num) hz8)
  have hp : 1 ≤ Real.log z ^ (γ - 1) := Real.one_le_rpow hL (by linarith)
  rw [(hd z hz8).deriv]
  apply div_nonneg
  · apply mul_nonneg (Real.exp_pos _).le
    have hg : 1 ≤ γ * Real.log z ^ (γ - 1) := one_le_mul_of_one_le_of_one_le hγ.le hp
    linarith
  · positivity

/-- Copy of `Decomp371a.window_lower`, P0082 page 365 floor window. -/
theorem window_lower (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N)
    (n : ℕ) (hn : n ∈ windowSet γ N) : N / 2 < n := by
  by_contra hnlow
  have hnN : n ≤ N / 2 := by omega
  let m := max n 8
  have hm8 : 8 ≤ m := Nat.le_max_right _ _
  have hnm : n ≤ m := Nat.le_max_left _ _
  have hmN : 2 * m ≤ N := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hFm : 0 < F γ m := Real.exp_pos _
  have hmono : F γ n ≤ F γ m := by
    by_cases hn0 : n = 0
    · subst n
      have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
      have hpow : 0 ≤ Real.log (m : ℝ) ^ γ := Real.rpow_nonneg hlog _
      simpa only [F, Nat.cast_zero, Real.log_zero, Real.zero_rpow (by linarith : γ ≠ 0),
        Real.exp_zero] using Real.one_le_exp_iff.mpr hpow
    · exact F_mono (by linarith) (by omega) hnm
  have hr := F_ratio_mono γ m N hγ (by exact_mod_cast hm8) (by exact_mod_cast (by omega : m ≤ N))
  have hcross : F γ m * N ≤ F γ N * m := (div_le_div_iff₀ hmpos hNpos).mp hr
  have hhalf : F γ m ≤ F γ N / 2 := by
    calc
      _ ≤ F γ N * m / N := (le_div_iff₀ hNpos).mpr hcross
      _ ≤ F γ N / 2 := by
        rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 2)]
        have hmNr : 2 * (m : ℝ) ≤ N := by exact_mod_cast hmN
        have hFN : 0 < F γ N := Real.exp_pos _
        nlinarith [mul_le_mul_of_nonneg_left hmNr hFN.le]
  have hfloor : (nu γ n : ℝ) ≤ F γ n := Int.floor_le _
  have hnu : F γ N / 2 < (nu γ n : ℝ) := (Finset.mem_filter.mp hn).2.1
  linarith

/-- Copy of `Decomp371a.window_subset_Ioc`, P0082 page 365. -/
theorem window_subset_Ioc (γ : ℝ) (hγ : 1 < γ) (N : ℕ) (hN : 16 ≤ N) :
    windowSet γ N ⊆ Finset.Ioc (N / 2) N := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨window_lower γ hγ N hN n hn,
    window_upper γ hγ N (by omega) n hn⟩

/-! ### The boundary count from Theorem 2, pages 359 and 364 -/

theorem one_le_F (γ x : ℝ) (hx : 1 ≤ x) : 1 ≤ F γ x := by
  unfold F
  exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx) _)

set_option maxHeartbeats 1000000 in
/-- P0082 page 359, Lemma 4 in the upper bound form that the paper says suffices, applied on
page 364 after display (23). With `Δ = ℰ^{-1/8}`, at most `B N Δ` members of the window have
`{F(n)} < Δ` or `{F(n)} > 1 - Δ`, for every small `κ`. CONDITIONAL ON Theorem 2 of page 354,
used with `c = 1/2` and `C = (γ - 1)/2` at the integer frequencies `0 < |h| ≤ Δ^{-1}/6`. -/
theorem boundary_of_theorem2 (hT : Theorem2) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((windowSet γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  have hC0 : 0 < (γ - 1) / 2 := by linarith
  obtain ⟨κT, BT, hκT, hT⟩ :=
    hT γ h1 h2 (1 / 2) ((γ - 1) / 2) (by norm_num) (by norm_num) hC0 (by linarith)
  set p := 3 - 2 * γ with hp_def
  set C := (γ - 1) / 2 with hC_def
  have hp0 : 0 < p := by linarith
  have hp1 : p ≤ 1 := by linarith
  refine ⟨4 * min (min κT C) 1, by positivity, fun κ hκ hκsmall => ?_⟩
  have hm1 := min_le_left (min κT C) 1
  have hm2 := min_le_right (min κT C) 1
  have hm3 := min_le_left κT C
  have hm4 := min_le_right κT C
  have hκT' : κ ≤ 4 * κT := by linarith
  have hκC : κ ≤ 4 * C := by linarith
  have hκ1 : κ ≤ 4 := by linarith
  refine ⟨49 + 4 * |BT|, by positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrow : Tendsto (fun N : ℕ => κ * Real.log N ^ p) atTop atTop :=
    ((tendsto_rpow_atTop hp0).comp hlog).const_mul_atTop hκ
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hgrow.eventually_ge_atTop (8 * Real.log 12))
  refine ⟨max 16 NE, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hgN : 8 * Real.log 12 ≤ κ * Real.log N ^ p := hNE N ((le_max_right _ _).trans hN)
  have hlog2 := Real.log_two_gt_d9
  set L := Real.log (N : ℝ) with hL_def
  have hL2 : 2 ≤ L := by
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have : Real.log 16 ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hN16)
    linarith
  set M := N / 2 with hM_def
  have hM8 : 8 ≤ M := by omega
  have hMN : M + 1 ≤ N := by omega
  have hNM : N ≤ M * M := by nlinarith [Nat.div_add_mod N 2, Nat.mod_lt N (by norm_num : 0 < 2)]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set LM := Real.log (M : ℝ) with hLM_def
  have hLM1 : 1 ≤ LM := by
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have : Real.log 8 ≤ LM := Real.log_le_log (by norm_num) (by exact_mod_cast hM8)
    linarith
  have hLML : L / 2 ≤ LM := by
    have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < N))
      (show (N : ℝ) ≤ (M : ℝ) * M by exact_mod_cast hNM)
    rw [Real.log_mul hMpos.ne' hMpos.ne'] at h
    linarith
  set Δ := calE γ κ N ^ (-(1 / 8 : ℝ)) with hΔ_def
  have hΔeq : Δ = Real.exp (-(κ * L ^ p / 8)) := by
    rw [hΔ_def, calE, ← Real.exp_mul]
    congr 1
    ring
  have hΔpos : 0 < Δ := by rw [hΔeq]; exact Real.exp_pos _
  have hΔ12 : Δ ≤ 1 / 12 := by
    rw [hΔeq]
    calc Real.exp (-(κ * L ^ p / 8)) ≤ Real.exp (-Real.log 12) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 12 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hLp : L ^ p ≤ L := by
    calc L ^ p ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hp1
      _ = L := Real.rpow_one L
  have hLp0 : 0 ≤ L ^ p := Real.rpow_nonneg (by linarith) _
  have hκLp : κ * L ^ p ≤ 4 * L := by
    nlinarith [mul_le_mul_of_nonneg_right hκ1 hLp0]
  have hNΔ : 1 ≤ (N : ℝ) * Δ := by
    have hNexp : (N : ℝ) = Real.exp L := (Real.exp_log (by exact_mod_cast (by omega : 0 < N))).symm
    have hnn : (0 : ℝ) ≤ L - κ * L ^ p / 8 := by linarith
    calc (1 : ℝ) ≤ Real.exp (L - κ * L ^ p / 8) := Real.one_le_exp hnn
      _ = Real.exp L * Real.exp (-(κ * L ^ p / 8)) := by rw [← Real.exp_add]; ring_nf
      _ = (N : ℝ) * Δ := by rw [← hNexp, ← hΔeq]
  -- the Fejér length
  set x := 1 / (6 * Δ) with hx_def
  have hx2 : 2 ≤ x := by
    rw [hx_def, le_div_iff₀ (by positivity)]
    linarith
  set H := ⌊x⌋₊ with hH_def
  have hH1 : 1 ≤ H := Nat.le_floor (by push_cast; linarith)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
  have hHle : (H : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hHgt : x < H + 1 := Nat.lt_floor_add_one x
  have hHΔ : (H : ℝ) * Δ ≤ 1 / 6 := by
    calc (H : ℝ) * Δ ≤ x * Δ := mul_le_mul_of_nonneg_right hHle hΔpos.le
      _ = 1 / 6 := by rw [hx_def]; field_simp
  have h12 : 1 ≤ 12 * Δ * H := by
    have hxΔ : x * (6 * Δ) = 1 := by rw [hx_def]; field_simp
    nlinarith
  -- the exponential sum bound from Theorem 2
  set Q := |BT| * N * Δ with hQ_def
  have hQ0 : 0 ≤ Q := by positivity
  have hinvΔ : 1 / Δ = Real.exp (κ * L ^ p / 8) := by
    rw [hΔeq, Real.exp_neg, one_div, inv_inv]
  have hrange : 1 / Δ ≤ F γ M ^ C := by
    rw [hinvΔ, F, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hγLM : LM ≤ LM ^ γ := by
      calc LM = LM ^ (1 : ℝ) := (Real.rpow_one LM).symm
        _ ≤ LM ^ γ := Real.rpow_le_rpow_of_exponent_le hLM1 h1.le
    have hA : κ * L ^ p / 8 ≤ C * L / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hκC hLp0, mul_le_mul_of_nonneg_left hLp hκ.le]
    have hB : C * L / 2 ≤ C * LM := by nlinarith
    have hC' : C * LM ≤ C * LM ^ γ := mul_le_mul_of_nonneg_left hγLM hC0.le
    rw [← hLM_def]
    linarith
  have hsave : Real.exp (-κT * LM ^ p) ≤ Δ := by
    rw [hΔeq]
    apply Real.exp_le_exp.mpr
    have hhalf : (L / 2) ^ p ≤ LM ^ p := Real.rpow_le_rpow (by linarith) hLML hp0.le
    have h2p : (2 : ℝ) ^ p ≤ 2 := by
      calc (2 : ℝ) ^ p ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
        _ = 2 := Real.rpow_one 2
    have h2p0 : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) _
    have hdiv : (L / 2) ^ p = L ^ p / 2 ^ p := Real.div_rpow (by linarith) (by norm_num) p
    have hge : L ^ p / 2 ≤ L ^ p / 2 ^ p := div_le_div_of_nonneg_left hLp0 h2p0 h2p
    have hκ8 : κ * L ^ p / 8 ≤ κT * (L ^ p / 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hκT' hLp0]
    have hT2 : κT * (L ^ p / 2) ≤ κT * LM ^ p :=
      mul_le_mul_of_nonneg_left (by linarith) hκT.le
    linarith
  have hQ : ∀ h : ℤ, h ≠ 0 → |h| < H →
      ‖∑ n ∈ Finset.Icc M (2 * M), eC ((h : ℝ) * F γ n)‖ ≤ Q := by
    intro h hh hhH
    have habs1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hh
    have habsH : |(h : ℝ)| ≤ 1 / Δ := by
      have hlt : |(h : ℝ)| < H := by
        rw [← Int.cast_abs]
        exact_mod_cast hhH
      have hx6 : x ≤ 1 / Δ := by
        rw [hx_def]
        apply one_div_le_one_div_of_le hΔpos
        linarith
      linarith
    have hF2 : F γ (2 * M) ^ (-(1 / 2 : ℝ)) ≤ |(h : ℝ)| := by
      refine le_trans ?_ habs1
      apply Real.rpow_le_one_of_one_le_of_nonpos _ (by norm_num)
      apply one_le_F
      have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
      push_cast
      linarith
    have hb := hT M (by omega) (h : ℝ) hF2 (habsH.trans hrange)
    have hsum : ∑ n ∈ Finset.Icc M (2 * M), eC ((h : ℝ) * F γ n) = expSumF γ h M := rfl
    rw [hsum]
    refine hb.trans ?_
    rw [hQ_def]
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast (by omega : M ≤ N)
    calc BT * M * Real.exp (-κT * Real.log M ^ p)
        ≤ |BT| * M * Real.exp (-κT * Real.log M ^ p) := by
          gcongr
          exact le_abs_self _
      _ ≤ |BT| * N * Δ := by
          gcongr
  have hcount := fejer_count (Finset.Icc M (2 * M)) (fun n => F γ n) H hH1 Δ Q hHΔ hQ0 hQ
  have hcardI : ((Finset.Icc M (2 * M)).card : ℝ) ≤ N := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : 2 * M + 1 - M ≤ N)
  have hsub : (windowSet γ N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) ⊆
      (Finset.Icc M (2 * M)).filter (fun n : ℕ =>
        Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) ∪ {N} := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hnP⟩
    have hnI := Finset.mem_Ioc.mp (window_subset_Ioc γ h1 N hN16 hnW)
    by_cases hn2 : n ≤ 2 * M
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hn2⟩, hnP⟩)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (by omega))
  have hcard : (((windowSet γ N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ) ≤
      ((Finset.Icc M (2 * M)).filter (fun n : ℕ =>
        Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card + 1 := by
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  have hmain : 4 * ((Finset.Icc M (2 * M)).card : ℝ) / H ≤ 48 * N * Δ := by
    rw [div_le_iff₀ hHpos]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h12 hN0]
  calc _ ≤ _ := hcard
    _ ≤ (4 * ((Finset.Icc M (2 * M)).card : ℝ) / H + 4 * Q) + 1 := by
        linarith [hcount]
    _ ≤ 48 * N * Δ + 4 * Q + (N : ℝ) * Δ := by linarith
    _ = (49 + 4 * |BT|) * N * Δ := by rw [hQ_def]; ring

end LeanLab.ExceptionalSet.BoundarySupplyJ200
