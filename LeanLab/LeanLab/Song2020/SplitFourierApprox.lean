/-
SPLIT of `LeanLab.Song2020.Decomp139.fourier_approximation`, PREP 2026-11-21.
Source: Y. Song, arXiv 2012.06322 v1, papers/P0078.pdf. Lemma 1 on printed page 3;
the S2 estimate on printed pages 4 and 5, from the display after "By Lemma 3.1, we have"
through "Concluding the above estimate, we have S2 << H^(1/2) n^(1-γ/2) + H^(-1) y n^(1-γ)".
Lemma 1 is already PROVED on main as
`Repair591FourierMajorant.song_lemma1_majorant591` and is used here, not restated.
The remaining cited input is Graham and Kolesnik, display 3.3.4, the exponent pair 1/2, 1/2.
The original statement is not restated: the assembly proves its exact type.
AI wrote the Lean code. Not compiled in this design unit. Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139
import LeanLab.Song2020.Repair591FourierMajorant

namespace LeanLab.Song2020.SplitFourierApprox

open LeanLab.Song2020 LeanLab.Song2020.State1562 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-- The real trigonometric majorant of Lemma 1 at truncation level H. -/
def majorant (b : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) : ℝ :=
  (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re

/-- The Lemma 1 coefficients cut to the frequencies the truncated sum uses. -/
def truncCoeff (a : ℕ → ℤ → ℂ) (H : ℕ) (h : ℤ) : ℂ :=
  if |h| ≤ (H : ℤ) then a H h else 0

/-- Page 4, Graham and Kolesnik display 3.3.4 with the exponent pair 1/2, 1/2, in the form
Song uses: the sum of e of h x to the gamma over an initial segment of the window is at most
a constant times h to the 1/2 n to the gamma over 2 plus h inverse n to the 1 minus gamma. -/
def ExponentPairHalf (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, 0 < y → y ≤ (n : ℝ) / 3 →
    ∀ h : ℕ, 1 ≤ h → ∀ t : ℝ,
      ‖∑ m ∈ subWindow n y t, eC ((h : ℝ) * (m : ℝ) ^ γ)‖ ≤
        C * ((h : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (h : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ))

/-- LEAF. Page 4, the display splitting the sawtooth sum into S1 plus S2: at each prime the
sawtooth difference minus its truncated Fourier difference is at most the Lemma 1 majorant
at both points, and the weight times the additive character has modulus the weight.
Elementary: triangle inequality and the modulus of e. -/
theorem leaf_saw_window_triangle (γ : ℝ) (hγ : 0 < γ) (a b : ℕ → ℤ → ℂ) (H : ℕ)
    (hmaj : ∀ x : ℝ, ‖(saw x : ℂ) - fourier a H x‖ ≤ majorant b H x)
    (n : ℕ) (y α : ℝ) :
    ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
      ∑ p ∈ windowPrimes n y, psWeight γ p *
        (majorant b H (-((p : ℝ) + 1) ^ γ) + majorant b H (-(p : ℝ) ^ γ)) := by
  have hw : ∀ p ∈ windowPrimes n y, 0 ≤ psWeight γ p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
    have hpos : 0 < (p : ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos (by linarith) _
    unfold psWeight
    positivity
  have heC : ∀ x : ℝ, ‖eC x‖ = 1 := by
    intro x
    simp [eC, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hd : sawSum γ n y α - truncatedSum a H γ n y α =
      ∑ p ∈ windowPrimes n y, (psWeight γ p : ℂ) * eC (α * p) *
        (((saw (-((p : ℝ) + 1) ^ γ) : ℂ) - fourier a H (-((p : ℝ) + 1) ^ γ)) -
          ((saw (-(p : ℝ) ^ γ) : ℂ) - fourier a H (-(p : ℝ) ^ γ))) := by
    unfold sawSum truncatedSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    push_cast
    ring
  rw [hd]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  have hpw := hw p hp
  rw [norm_mul, norm_mul, heC, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpw]
  refine mul_le_mul_of_nonneg_left ?_ hpw
  exact (norm_sub_le _ _).trans (add_le_add (hmaj _) (hmaj _))

/-- LEAF. CITED: S. W. Graham and G. Kolesnik, van der Corput's Method of Exponential Sums,
LMS Lecture Note Series 126, Cambridge 1991, display 3.3.4 with the exponent pair 1/2, 1/2,
as used by Song on printed page 4, last display. Applied on dyadic pieces of the window. -/
theorem leaf_exponent_pair_half :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ExponentPairHalf γ := by
  sorry

/-! ### Private helpers for the S2 window bound -/

/-- The modulus of `eC` is one. -/
private theorem norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  simp [eC, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The majorant is the real part of its defining finite Fourier sum. -/
private theorem majorant_re (b : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) :
    majorant b H x = (∑ h ∈ Finset.Icc (-(H : ℤ)) H, b H h * eC (x * h)).re := rfl

/-- The majorant is bounded by the sum of the moduli of its coefficients. -/
private theorem abs_majorant_le_sum (b : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) :
    |majorant b H x| ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ := by
  rw [majorant_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun h _ => by rw [norm_mul, norm_eC, mul_one]

/-- The number of frequencies at truncation level `H`. -/
private theorem card_Icc_int (H : ℕ) :
    (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
  rw [Int.card_Icc]
  have h1 : H + 1 - -(H : ℤ) = ((2 * H + 1 : ℕ) : ℤ) := by omega
  rw [h1, Int.toNat_natCast]

/-- Two integer windows of half width `y` with centres one apart have index sets differing in
at most one element at each end, so the partial sums of any unit bound differ by at most two. -/
private theorem shift_window_sum_le (c y τ : ℝ) (hy : 1 ≤ y) (f : ℕ → ℂ)
    (hf : ∀ m, ‖f m‖ ≤ 1) :
    ‖∑ m ∈ (Finset.range (Nat.ceil (c + y) + 1)).filter
        (fun m : ℕ => |(m : ℝ) - c - 1| < y ∧ (m : ℝ) ≤ τ), f m‖ ≤
      ‖∑ m ∈ (Finset.range (Nat.ceil (c + y) + 1)).filter
        (fun m : ℕ => |(m : ℝ) - c| < y ∧ (m : ℝ) ≤ τ), f m‖ + 2 := by
  set Wt := (Finset.range (Nat.ceil (c + y) + 1)).filter
    (fun m : ℕ => |(m : ℝ) - c| < y ∧ (m : ℝ) ≤ τ) with hWt
  set At := (Finset.range (Nat.ceil (c + y) + 1)).filter
    (fun m : ℕ => |(m : ℝ) - c - 1| < y ∧ (m : ℝ) ≤ τ) with hAt
  have key1 : ∀ m : ℕ, |(m : ℝ) - c - 1| < y → ¬ (|(m : ℝ) - c| < y) →
      (m : ℤ) = ⌈c + y⌉ := by
    intro m hA hW
    have h1 := abs_lt.mp hA
    have h2 : y ≤ |(m : ℝ) - c| := le_of_not_gt hW
    rcases le_or_gt (m : ℝ) c with hle | hgt
    · have habs : |(m : ℝ) - c| = c - (m : ℝ) := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [habs] at h2
      linarith [h1.1]
    · have habs : |(m : ℝ) - c| = (m : ℝ) - c := abs_of_nonneg (by linarith)
      rw [habs] at h2
      have hlow : c + y ≤ (m : ℝ) := by linarith
      have hhigh : (m : ℝ) < c + y + 1 := by linarith [h1.2]
      have e1 : ⌈c + y⌉ ≤ (m : ℤ) := by
        rw [Int.ceil_le]; exact_mod_cast hlow
      have e2 : (m : ℤ) ≤ ⌈c + y⌉ := by
        have h3 : ((m : ℤ) : ℝ) < ((⌈c + y⌉ : ℤ) : ℝ) + 1 := by
          push_cast
          linarith [hhigh, Int.le_ceil (c + y)]
        have h4 : (m : ℤ) < ⌈c + y⌉ + 1 := by exact_mod_cast h3
        omega
      omega
  have key2 : ∀ m : ℕ, |(m : ℝ) - c| < y → ¬ (|(m : ℝ) - c - 1| < y) →
      (m : ℤ) = ⌊c - y⌋ + 1 := by
    intro m hW hA
    have h1 := abs_lt.mp hW
    have hgt : c - y < (m : ℝ) := by linarith [h1.1]
    have hle : (m : ℝ) - c - 1 ≤ -y := by
      by_contra hcon
      push_neg at hcon
      exact hA (abs_lt.mpr ⟨hcon, by linarith [h1.2]⟩)
    have hhigh : (m : ℝ) ≤ c - y + 1 := by linarith
    have e1 : ⌊c - y⌋ + 1 ≤ (m : ℤ) := by
      have hlt : ((⌊c - y⌋ : ℤ) : ℝ) < (m : ℝ) := lt_of_le_of_lt (Int.floor_le _) hgt
      have h2 : ⌊c - y⌋ < (m : ℤ) := by exact_mod_cast hlt
      omega
    have e2 : (m : ℤ) ≤ ⌊c - y⌋ + 1 := by
      have h2 : (((m : ℤ) - 1 : ℤ) : ℝ) ≤ c - y := by push_cast; linarith
      have h3 : ((m : ℤ) - 1 : ℤ) ≤ ⌊c - y⌋ := Int.le_floor.mpr h2
      omega
    omega
  have hsub1 : At.filter (fun m => m ∉ Wt) ⊆ {(⌈c + y⌉).toNat} := by
    intro m hm
    rw [Finset.mem_singleton]
    have hmA : m ∈ At := (Finset.mem_filter.mp hm).1
    have hmW : m ∉ Wt := (Finset.mem_filter.mp hm).2
    have hA := (Finset.mem_filter.mp hmA).2
    have hnot : ¬ (|(m : ℝ) - c| < y) := by
      intro h
      exact hmW (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmA).1, h, hA.2⟩)
    have hz : (m : ℤ) = ⌈c + y⌉ := key1 m hA.1 hnot
    rw [← hz]
    exact (Int.toNat_natCast m).symm
  have hsub2 : Wt.filter (fun m => m ∉ At) ⊆ {(⌊c - y⌋ + 1).toNat} := by
    intro m hm
    rw [Finset.mem_singleton]
    have hmW : m ∈ Wt := (Finset.mem_filter.mp hm).1
    have hmA : m ∉ At := (Finset.mem_filter.mp hm).2
    have hW := (Finset.mem_filter.mp hmW).2
    have hnot : ¬ (|(m : ℝ) - c - 1| < y) := by
      intro h
      exact hmA (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmW).1, h, hW.2⟩)
    have hz : (m : ℤ) = ⌊c - y⌋ + 1 := key2 m hW.1 hnot
    rw [← hz]
    exact (Int.toNat_natCast m).symm
  have hcard1 : (At.filter (fun m => m ∉ Wt)).card ≤ 1 := by
    have := Finset.card_le_card hsub1
    simpa using this
  have hcard2 : (Wt.filter (fun m => m ∉ At)).card ≤ 1 := by
    have := Finset.card_le_card hsub2
    simpa using this
  have hb1 : ‖∑ m ∈ At.filter (fun m => m ∉ Wt), f m‖ ≤ 1 := by
    refine (norm_sum_le _ _).trans ?_
    have hs := Finset.sum_le_card_nsmul (At.filter (fun m => m ∉ Wt))
      (fun m => ‖f m‖) 1 (fun m _ => hf m)
    rw [nsmul_eq_mul, mul_one] at hs
    have hc1 : ((At.filter (fun m => m ∉ Wt)).card : ℝ) ≤ 1 := by exact_mod_cast hcard1
    linarith
  have hb2 : ‖∑ m ∈ Wt.filter (fun m => m ∉ At), f m‖ ≤ 1 := by
    refine (norm_sum_le _ _).trans ?_
    have hs := Finset.sum_le_card_nsmul (Wt.filter (fun m => m ∉ At))
      (fun m => ‖f m‖) 1 (fun m _ => hf m)
    rw [nsmul_eq_mul, mul_one] at hs
    have hc1 : ((Wt.filter (fun m => m ∉ At)).card : ℝ) ≤ 1 := by exact_mod_cast hcard2
    linarith
  have hset : At.filter (fun m => m ∈ Wt) = Wt.filter (fun m => m ∈ At) := by
    ext m
    simp only [Finset.mem_filter]
    tauto
  have hsplitA := Finset.sum_filter_add_sum_filter_not (s := At) (p := fun m => m ∈ Wt) (f := f)
  have hsplitW := Finset.sum_filter_add_sum_filter_not (s := Wt) (p := fun m => m ∈ At) (f := f)
  have hdecomp : ∑ m ∈ At, f m = ∑ m ∈ Wt, f m - ∑ m ∈ Wt.filter (fun m => m ∉ At), f m
      + ∑ m ∈ At.filter (fun m => m ∉ Wt), f m := by
    rw [← hsplitA, ← hsplitW, hset]
    ring
  rw [hdecomp]
  have hstep : ‖∑ m ∈ Wt, f m - ∑ m ∈ Wt.filter (fun m => m ∉ At), f m
      + ∑ m ∈ At.filter (fun m => m ∉ Wt), f m‖ ≤
      ‖∑ m ∈ Wt, f m‖ + 1 + 1 := by
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (∑ m ∈ Wt, f m) (∑ m ∈ Wt.filter (fun m => m ∉ At), f m)
    linarith
  linarith

/-- Summation by parts: a bound on the partial sums of `u` bounds the sum against any
nondecreasing weight. -/
private theorem abel_range_bound (w : ℕ → ℝ) (u : ℕ → ℂ) (N : ℕ) (E : ℝ)
    (hE : 0 ≤ E) (hw0 : 0 ≤ w 0) (hwmono : ∀ i, i < N → w i ≤ w (i + 1))
    (hu : ∀ k, k ≤ N → ‖∑ i ∈ Finset.range k, u i‖ ≤ E) :
    ‖∑ i ∈ Finset.range N, w i • u i‖ ≤ 2 * w (N - 1) * E := by
  have hmono : ∀ i, i ≤ N → w 0 ≤ w i := by
    intro i hi
    induction i with
    | zero => exact le_rfl
    | succ k ih => exact (ih (by omega)).trans (hwmono k (by omega))
  have hwN : 0 ≤ w (N - 1) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simpa using hw0
    · exact hw0.trans (hmono (N - 1) (by omega))
  rw [Finset.sum_range_by_parts]
  have h1 : ‖w (N - 1) • ∑ i ∈ Finset.range N, u i‖ ≤ w (N - 1) * E := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwN]
    exact mul_le_mul_of_nonneg_left (hu N le_rfl) hwN
  have h2 : ‖∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), u j‖
      ≤ (w (N - 1) - w 0) * E := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range (N - 1),
        ‖(w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), u j‖ ≤ (w (i + 1) - w i) * E := by
      intro i hi
      have hi' : i < N - 1 := Finset.mem_range.mp hi
      have hle : w i ≤ w (i + 1) := hwmono i (by omega)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (hu (i + 1) (by omega)) (by linarith)
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [← Finset.sum_mul, Finset.sum_range_sub]
  have h3 : ‖w (N - 1) • ∑ i ∈ Finset.range N, u i‖ +
      ‖∑ i ∈ Finset.range (N - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), u j‖
      ≤ 2 * w (N - 1) * E := by
    have h0 : 0 ≤ w 0 * E := mul_nonneg hw0 hE
    nlinarith
  exact (norm_sub_le _ _).trans h3

/-- A coefficient bound bounds the majorant uniformly in the point. -/
private theorem majorant_le_of_coeff (b : ℕ → ℤ → ℂ) (H : ℕ) (Cb : ℝ) (hH : 1 ≤ H)
    (hCb : 0 ≤ Cb)
    (hb : ∀ h : ℤ, |h| ≤ (H : ℤ) → ‖b H h‖ ≤ Cb / (H : ℝ)) (x : ℝ) :
    majorant b H x ≤ 3 * Cb := by
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have h1 : majorant b H x ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ :=
    (le_abs_self _).trans (abs_majorant_le_sum b H x)
  have h2 : ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ ≤
      ((2 * H + 1 : ℕ) : ℝ) * (Cb / (H : ℝ)) := by
    have hs := Finset.sum_le_card_nsmul (Finset.Icc (-(H : ℤ)) H) (fun h => ‖b H h‖)
      (Cb / (H : ℝ)) (fun h hh => hb h (abs_le.mpr (Finset.mem_Icc.mp hh)))
    rw [card_Icc_int, nsmul_eq_mul] at hs
    exact hs
  have h3 : ((2 * H + 1 : ℕ) : ℝ) * (Cb / (H : ℝ)) ≤ 3 * Cb := by
    have hle : ((2 * H + 1 : ℕ) : ℝ) ≤ 3 * (H : ℝ) := by
      push_cast
      linarith
    have hd : 0 ≤ Cb / (H : ℝ) := div_nonneg hCb hH0.le
    calc ((2 * H + 1 : ℕ) : ℝ) * (Cb / (H : ℝ)) ≤ (3 * (H : ℝ)) * (Cb / (H : ℝ)) :=
          mul_le_mul_of_nonneg_right hle hd
      _ = 3 * Cb := by field_simp
  linarith

/-- The exponential of the negative argument is the conjugate. -/
private theorem eC_neg (x : ℝ) : eC (-x) = (starRingEnd ℂ) (eC x) := by
  simp only [eC]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Changing the sign of the phase does not change the norm of a real weighted sum. -/
private theorem norm_sum_eC_neg (w : ℕ → ℝ) (φ : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ m ∈ s, w m • eC (-(φ m))‖ = ‖∑ m ∈ s, w m • eC (φ m)‖ := by
  have hconj : (∑ m ∈ s, w m • eC (-(φ m))) =
      (starRingEnd ℂ) (∑ m ∈ s, w m • eC (φ m)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
    congr 1
    exact eC_neg (φ m)
  rw [hconj, Complex.norm_conj]

/-- A weighted exponential sum over the integer window, against the exponent pair bound on the
initial segments of the window. The parameter `d` is the shift of the phase, `0` for the point
`-p^γ` and `1` for the point `-(p+1)^γ`. -/
private theorem window_abel (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 6 ≤ n)
    (y : ℝ) (hy : 1 ≤ y) (hy3 : y ≤ (n : ℝ) / 3) (k : ℕ) (hk : 1 ≤ k) (E : ℝ) (hE : 0 ≤ E)
    (hEP : ∀ t : ℝ, ‖∑ m ∈ subWindow n y t, eC ((k : ℝ) * (m : ℝ) ^ γ)‖ ≤ E) :
    ∀ d ∈ ({0, 1} : Finset ℕ),
      ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC ((k : ℝ) * ((m : ℝ) + d) ^ γ)‖ ≤
        2 * (n : ℝ) ^ (1 - γ) * (E + 2) := by
  have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hRle : ((Nat.ceil ((n : ℝ) / 3 + y) : ℕ) : ℝ) ≤ (n : ℝ) := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (n : ℝ)/3 + y by linarith)
    linarith
  intro d hd
  have hd01 : d = 0 ∨ d = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  set S : Finset ℕ := (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
    (fun m => |(m : ℝ) - (n : ℝ) / 3| < y ∧ (m : ℝ) ≤ (n : ℝ) / 3 + y) with hS
  set u : ℕ → ℂ := fun m => if m ∈ S then eC ((k : ℝ) * ((m : ℝ) + d) ^ γ) else 0 with hu
  set w : ℕ → ℝ := fun m => (m : ℝ) ^ (1 - γ) with hw
  have hSmem : ∀ m : ℕ, m ∈ S ↔
      (m < Nat.ceil ((n : ℝ) / 3 + y) + 1 ∧ |(m : ℝ) - (n : ℝ) / 3| < y ∧
        (m : ℝ) ≤ (n : ℝ) / 3 + y) := by
    intro m; rw [hS, Finset.mem_filter, Finset.mem_range]
  have hpartial : ∀ j, j ≤ Nat.ceil ((n : ℝ) / 3 + y) + 1 →
      ‖∑ i ∈ Finset.range j, u i‖ ≤ E + 2 := by
    intro j hj
    have key : (Finset.range j).filter (fun i => i ∈ S) = S.filter (fun m => m < j) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    have hrew : ∑ i ∈ Finset.range j, u i =
        ∑ m ∈ S.filter (fun m => m < j), eC ((k : ℝ) * ((m : ℝ) + d) ^ γ) := by
      calc ∑ i ∈ Finset.range j, u i
          = ∑ i ∈ Finset.range j,
              (if i ∈ S then eC ((k : ℝ) * ((i : ℝ) + d) ^ γ) else 0) := by
            simp only [hu]
        _ = ∑ i ∈ (Finset.range j).filter (fun i => i ∈ S),
              eC ((k : ℝ) * ((i : ℝ) + d) ^ γ) :=
            (Finset.sum_filter (s := Finset.range j) (p := fun i => i ∈ S)
              (f := fun i => eC ((k : ℝ) * ((i : ℝ) + d) ^ γ))).symm
        _ = _ := by rw [key]
    rw [hrew]
    rcases hd01 with rfl | rfl
    · simp only [Nat.cast_zero, add_zero]
      have hset : S.filter (fun m => m < j) = subWindow n y ((j : ℝ) - 1) := by
        ext m
        rw [Finset.mem_filter, hSmem m, subWindow]
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          have h4' : (1 : ℕ) ≤ j := by omega
          refine ⟨h1, h2, ?_⟩
          have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
            rw [Nat.cast_sub h4']; norm_num
          have hm : (m : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show m ≤ j - 1 by omega)
          rw [hcast] at hm
          exact hm
        · rintro ⟨h1, h2, h3⟩
          have h3' : (m : ℝ) < (j : ℝ) := by linarith
          have h4 : m < j := by exact_mod_cast h3'
          exact ⟨⟨h1, h2, by linarith [(abs_lt.mp h2).2]⟩, h4⟩
      rw [hset]
      have := hEP ((j : ℝ) - 1)
      linarith
    · have himg1 : (S.filter (fun m => m < j)).image (fun m => m + 1) ⊆
          (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun q : ℕ => |(q : ℝ) - (n : ℝ) / 3 - 1| < y ∧ (q : ℝ) ≤ (j : ℝ)) := by
        intro q hq
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨hmS, hmj⟩ := Finset.mem_filter.mp hm
        obtain ⟨h1, h2, h3⟩ := (hSmem m).mp hmS
        rw [Finset.mem_filter, Finset.mem_range]
        have hm_lt : m < Nat.ceil ((n : ℝ) / 3 + y) := by
          have hlt : (m : ℝ) < (Nat.ceil ((n : ℝ) / 3 + y) : ℕ) := by
            have hcl := Nat.le_ceil ((n : ℝ) / 3 + y)
            linarith [(abs_lt.mp h2).2]
          exact_mod_cast hlt
        refine ⟨Nat.succ_lt_succ hm_lt, ?_, ?_⟩
        · show |((m + 1 : ℕ) : ℝ) - (n : ℝ) / 3 - 1| < y
          have he : ((m : ℝ) + 1) - (n : ℝ) / 3 - 1 = (m : ℝ) - (n : ℝ) / 3 := by ring
          push_cast
          rw [he]
          exact h2
        · show ((m + 1 : ℕ) : ℝ) ≤ (j : ℝ)
          exact_mod_cast (show m + 1 ≤ j by omega)
      have himg2 : (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun q : ℕ => |(q : ℝ) - (n : ℝ) / 3 - 1| < y ∧ (q : ℝ) ≤ (j : ℝ)) ⊆
          (S.filter (fun m => m < j)).image (fun m => m + 1) := by
        intro q hq
        obtain ⟨hqr, hqabs, hqj⟩ := Finset.mem_filter.mp hq
        rw [Finset.mem_range] at hqr
        obtain ⟨hqa1, hqa2⟩ := abs_lt.mp hqabs
        have hq1 : 1 ≤ q := by
          have : (1 : ℝ) ≤ (q : ℝ) := by linarith
          exact_mod_cast this
        have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub hq1]; norm_num
        have hqj' : q - 1 < j := by
          have h1 : q ≤ j := by exact_mod_cast hqj
          omega
        have hqS : q - 1 ∈ S := by
          rw [hSmem]
          refine ⟨?_, ?_, ?_⟩
          · have hlt : ((q - 1 : ℕ) : ℝ) < (Nat.ceil ((n : ℝ) / 3 + y) : ℕ) + 1 := by
              rw [hqcast]
              linarith [Nat.le_ceil ((n : ℝ) / 3 + y)]
            exact_mod_cast hlt
          · rw [hqcast]
            have he : ((q : ℝ) - 1) - (n : ℝ) / 3 = (q : ℝ) - (n : ℝ) / 3 - 1 := by ring
            rw [he]
            exact abs_lt.mpr ⟨hqa1, hqa2⟩
          · rw [hqcast]
            linarith
        rw [Finset.mem_image]
        exact ⟨q - 1, Finset.mem_filter.mpr ⟨hqS, hqj'⟩, by omega⟩
      have himg := Finset.Subset.antisymm himg1 himg2
      have hconv : ∑ m ∈ S.filter (fun m => m < j),
            eC ((k : ℝ) * ((m : ℝ) + ((1 : ℕ) : ℝ)) ^ γ)
          = ∑ m ∈ S.filter (fun m => m < j), eC ((k : ℝ) * (((m + 1 : ℕ)) : ℝ) ^ γ) := by
        apply Finset.sum_congr rfl
        intro m _
        congr 2
        push_cast
        ring
      rw [hconv, ← Finset.sum_image (f := fun q : ℕ => eC ((k : ℝ) * (q : ℝ) ^ γ))
        (g := fun m : ℕ => m + 1) (fun a _ b _ hab => Nat.succ_injective hab), himg]
      have hstep := shift_window_sum_le ((n : ℝ) / 3) y (j : ℝ) hy
        (fun q => eC ((k : ℝ) * (q : ℝ) ^ γ)) (fun q => by rw [norm_eC])
      have hW : ‖∑ q ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
          (fun q : ℕ => |(q : ℝ) - (n : ℝ) / 3| < y ∧ (q : ℝ) ≤ (j : ℝ)),
          eC ((k : ℝ) * (q : ℝ) ^ γ)‖ ≤ E := hEP (j : ℝ)
      linarith
  have hSsub : (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter (fun i => i ∈ S) = S := by
    rw [hS]
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  have hsum : ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
      ((m : ℝ) ^ (1 - γ) : ℝ) • eC ((k : ℝ) * ((m : ℝ) + d) ^ γ) =
      ∑ i ∈ Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1), w i • u i := by
    calc ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC ((k : ℝ) * ((m : ℝ) + d) ^ γ)
        = ∑ i ∈ (Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1)).filter
            (fun i : ℕ => |(i : ℝ) - (n : ℝ) / 3| < y ∧ (i : ℝ) ≤ (n : ℝ) / 3 + y),
            ((i : ℝ) ^ (1 - γ) : ℝ) • eC ((k : ℝ) * ((i : ℝ) + d) ^ γ) := rfl
      _ = ∑ i ∈ Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1),
            (if |(i : ℝ) - (n : ℝ) / 3| < y ∧ (i : ℝ) ≤ (n : ℝ) / 3 + y
              then ((i : ℝ) ^ (1 - γ) : ℝ) • eC ((k : ℝ) * ((i : ℝ) + d) ^ γ) else 0) :=
            (Finset.sum_filter _ _)
      _ = ∑ i ∈ Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1), w i • u i := by
            apply Finset.sum_congr rfl
            intro i hi
            have hmem : i ∈ Finset.range (Nat.ceil ((n : ℝ) / 3 + y) + 1) := hi
            by_cases h : |(i : ℝ) - (n : ℝ) / 3| < y ∧ (i : ℝ) ≤ (n : ℝ) / 3 + y
            · have hiS : i ∈ S := (hSmem i).mpr ⟨Finset.mem_range.mp hmem, h⟩
              simp [hu, hw, h, hiS]
            · have hiS : i ∉ S := fun hc => h ((hSmem i).mp hc).2
              simp [hu, hw, h, hiS]
  rw [hsum]
  refine (abel_range_bound w u (Nat.ceil ((n : ℝ) / 3 + y) + 1) (E + 2)
    (by linarith) ?_ ?_ hpartial).trans ?_
  · have hz : (0 : ℝ) ≤ (0 : ℝ) ^ (1 - γ) := Real.rpow_nonneg (le_refl 0) _
    simpa [hw] using hz
  · rw [hw]
    intro i _
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) (by linarith)
  · have hR1 : w (Nat.ceil ((n : ℝ) / 3 + y) + 1 - 1) ≤ (n : ℝ) ^ (1 - γ) := by
      have h1 : Nat.ceil ((n : ℝ) / 3 + y) + 1 - 1 = Nat.ceil ((n : ℝ) / 3 + y) := by omega
      rw [h1, hw]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hRle (by linarith)
    have h3 : 0 ≤ w (Nat.ceil ((n : ℝ) / 3 + y) + 1 - 1) := by
      rw [hw]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [sq_nonneg ((n : ℝ) ^ (1 - γ)), hE]

/-- The weighted exponential sum of the window with a nonzero integer frequency is controlled
by the exponent pair bound. -/
private theorem window_Z_bound (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (hn : 6 ≤ n)
    (y : ℝ) (hy : 1 ≤ y) (hy3 : y ≤ (n : ℝ) / 3) (C_E : ℝ) (hCE : 0 ≤ C_E)
    (hEP : ∀ (k : ℕ), 1 ≤ k → ∀ t : ℝ,
      ‖∑ m ∈ subWindow n y t, eC ((k : ℝ) * (m : ℝ) ^ γ)‖ ≤
        C_E * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
          ((k : ℝ)⁻¹) * (n : ℝ) ^ (1 - γ)))
    (d : ℕ) (hd : d ∈ ({0, 1} : Finset ℕ)) (h : ℤ) (hh : h ≠ 0) :
    ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
        ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
      2 * (n : ℝ) ^ (1 - γ) * (C_E * (((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (n : ℝ) ^ (γ / 2) + ((((h.natAbs : ℕ) : ℝ))⁻¹) * (n : ℝ) ^ (1 - γ)) + 2) := by
  have hk1 : 1 ≤ h.natAbs := Int.natAbs_pos.mpr hh
  have hER : (0 : ℝ) ≤ C_E * (((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
      (((h.natAbs : ℕ) : ℝ))⁻¹ * (n : ℝ) ^ (1 - γ)) := by
    have h1 : (0 : ℝ) < ((h.natAbs : ℕ) : ℝ) := by exact_mod_cast hk1
    have h2 : (0 : ℝ) < ((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos h1 _
    have h3 : (0 : ℝ) < (n : ℝ) ^ (γ / 2) := Real.rpow_pos_of_pos (by linarith) _
    have h4 : (0 : ℝ) < (((h.natAbs : ℕ) : ℝ))⁻¹ := by positivity
    have h5 : (0 : ℝ) < (n : ℝ) ^ (1 - γ) := Real.rpow_pos_of_pos (by linarith) _
    have hsum : (0 : ℝ) < ((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
        (((h.natAbs : ℕ) : ℝ))⁻¹ * (n : ℝ) ^ (1 - γ) :=
      add_pos (mul_pos h2 h3) (mul_pos h4 h5)
    exact mul_nonneg hCE hsum.le
  have habel := window_abel γ hγ0 hγ1 n hn y hy hy3 h.natAbs hk1 _ hER
    (fun t => hEP h.natAbs hk1 t) d hd
  have hcases : (h : ℝ) = ((h.natAbs : ℕ) : ℝ) ∨ (h : ℝ) = -(((h.natAbs : ℕ) : ℝ)) := by
    obtain h' | h' := Int.natAbs_eq h
    · left
      rw [h']
      simp
    · right
      rw [h']
      simp
  rcases hcases with hc | hc
  · have hfun : ∀ m : ℕ, -((h : ℝ) * ((m : ℝ) + d) ^ γ) =
        -(((h.natAbs : ℕ) : ℝ) * ((m : ℝ) + d) ^ γ) := by
      intro m; rw [hc]
    simp only [hfun]
    exact le_trans (le_of_eq (norm_sum_eC_neg _ _ _)) habel
  · have hfun : ∀ m : ℕ, -((h : ℝ) * ((m : ℝ) + d) ^ γ) =
        (((h.natAbs : ℕ) : ℝ) * ((m : ℝ) + d) ^ γ) := by
      intro m; rw [hc]; ring
    simp only [hfun]
    exact habel

/-- The primes of the window relax to all integers of the window, because the majorant and the
weight are nonnegative, and the majorant expands into its frequencies. -/
private theorem window_relax (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) (y : ℝ)
    (b : ℕ → ℤ → ℂ) (H : ℕ) (hmaj : ∀ x : ℝ, 0 ≤ majorant b H x) (d : ℕ) :
    ∑ p ∈ windowPrimes n y, psWeight γ p * majorant b H (-((p : ℝ) + d) ^ γ) ≤
      (1 / γ) * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ *
        ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
            ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ := by
  have hsub : windowPrimes n y ⊆ subWindow n y ((n : ℝ) / 3 + y) := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    rw [subWindow, Finset.mem_filter]
    exact ⟨h1, h2.2, by linarith [(abs_lt.mp h2.2).2]⟩
  have hnn : ∀ m ∈ subWindow n y ((n : ℝ) / 3 + y),
      0 ≤ psWeight γ m * majorant b H (-((m : ℝ) + d) ^ γ) := by
    intro m _
    refine mul_nonneg ?_ (hmaj _)
    unfold psWeight
    have hp := Real.rpow_nonneg (Nat.cast_nonneg m) (1 - γ)
    positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hnn x hx)).trans ?_
  have hterm : ∀ m : ℕ, psWeight γ m * majorant b H (-((m : ℝ) + d) ^ γ)
      = (1 / γ) * (∑ h ∈ Finset.Icc (-(H : ℤ)) H,
          b H h * (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) *
            eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re := by
    intro m
    have hinner : (m : ℝ) ^ (1 - γ) * majorant b H (-((m : ℝ) + d) ^ γ)
        = ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
            (b H h * (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) *
              eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re := by
      rw [majorant_re, Complex.re_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      have harg : eC ((-((m : ℝ) + d) ^ γ) * (h : ℝ))
          = eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ)) := by
        congr 1
        ring
      rw [harg]
      have e1 : b H h * (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) *
            eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ)) =
          (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) *
            (b H h * eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))) := by ring
      rw [e1]
      have e2 : ((((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) *
            (b H h * eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ)))).re =
          (m : ℝ) ^ (1 - γ) *
            (b H h * eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re := by
        simp [Complex.mul_re]
      rw [e2]
    unfold psWeight
    rw [mul_assoc, hinner, ← Complex.re_sum]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 1 / γ)
  have hinner_re : ∀ m : ℕ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H,
      b H h * (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) * eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re
      = ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (b H h * (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) * eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re :=
    fun m => Complex.re_sum _ _
  simp only [hinner_re]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro h _
  have hstep : ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
        (b H h * (((m : ℝ) ^ (1 - γ) : ℝ) : ℂ) * eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re
      = (b H h * ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_assoc, ← Complex.real_smul]
  rw [hstep]
  refine (le_abs_self _).trans ?_
  rw [← norm_mul]
  exact Complex.abs_re_le_norm _

/-- The integer window contains at most `2y+2` integers. -/
private theorem subWindow_card_le (n : ℕ) (y τ : ℝ) (hy : 0 ≤ y) :
    ((subWindow n y τ).card : ℝ) ≤ 2 * y + 2 := by
  let a : ℤ := ⌊(n : ℝ) / 3 - y⌋
  let b : ℤ := ⌊(n : ℝ) / 3 + y⌋
  have hab : a ≤ b := Int.floor_mono (by linarith)
  have hc : (subWindow n y τ).card ≤ (Finset.Icc a b).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ => (p : ℤ))
    · intro p hp
      have hpw := abs_lt.mp (Finset.mem_filter.mp hp).2.1
      change (p : ℤ) ∈ Finset.Icc a b
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_of_lt_add_one
        have hreal : (a : ℝ) < (p : ℝ) + 1 := by
          have hfl : ((a : ℤ) : ℝ) ≤ (n : ℝ) / 3 - y := by
            dsimp only [a]
            exact Int.floor_le _
          linarith [hpw.1]
        exact_mod_cast hreal
      · exact Int.le_floor.mpr (by exact_mod_cast (show (p : ℝ) ≤ (n : ℝ) / 3 + y by
          linarith [hpw.2]))
    · exact Nat.cast_injective.injOn
  have hcard : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
    have h1 : ((Finset.Icc a b).card : ℤ) = b + 1 - a := Int.card_Icc_of_le a b (by omega)
    exact_mod_cast h1
  have ha := Int.lt_floor_add_one ((n : ℝ) / 3 - y)
  have hb := Int.floor_le ((n : ℝ) / 3 + y)
  have hcr : ((subWindow n y τ).card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast hc
  have ha' : (n : ℝ) / 3 - y - 1 < ((a : ℤ) : ℝ) := by linarith [ha]
  have hb' : ((b : ℤ) : ℝ) ≤ (n : ℝ) / 3 + y := hb
  linarith

/-- LEAF. Pages 4 and 5, from "By Lemma 3.1, we have" to "Concluding the above estimate".
The majorant is nonnegative, so the prime sum is at most the sum over all integers of the
window and its shift by one. The zero frequency gives H inverse y n to the 1 minus gamma.
For 1 at most the absolute value of h at most H, partial summation in the weight
x to the 1 minus gamma over initial segments and the exponent pair bound give
H to the 1/2 n to the 1 minus gamma over 2, and the term n to the 2 minus 2 gamma times
log H over H is absorbed into it since gamma exceeds 2/3. -/
theorem leaf_s2_window_of_exponent_pair :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ExponentPairHalf γ →
    ∀ Cb : ℝ, 0 ≤ Cb → ∀ b : ℕ → ℤ → ℂ,
      (∀ H : ℕ, 1 ≤ H → ∀ h : ℤ, |h| ≤ (H : ℤ) → ‖b H h‖ ≤ Cb / (H : ℝ)) →
      (∀ H : ℕ, 1 ≤ H → ∀ x : ℝ, 0 ≤ majorant b H x) →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∀ H : ℕ, 1 ≤ H →
          ∑ p ∈ windowPrimes n y, psWeight γ p *
            (majorant b H (-((p : ℝ) + 1) ^ γ) + majorant b H (-(p : ℝ) ^ γ)) ≤
              C * tailBudget γ n y H := by
  intro γ hγ hγ1 hEPfun Cb hCb b hb hmaj
  obtain ⟨C_E, hCE, N_E, hEP⟩ := hEPfun
  have hγ0 : 0 < γ := by linarith
  have hγle : γ ≤ 1 := hγ1.le
  refine ⟨(1 / γ) * (24 * Cb * C_E + 32 * Cb), by positivity, max N_E 6, ?_⟩
  intro n hn y hy hy3 H hH
  have hn6 : 6 ≤ n := le_trans (le_max_right _ _) hn
  have hnE : N_E ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hy0 : 0 < y := by
    have h1 : 0 ≤ songExponent γ := by unfold songExponent; linarith
    exact (Real.rpow_pos_of_pos hn0 _).trans_le hy.le
  have hy1 : 1 ≤ y := by
    have h1 : 0 ≤ songExponent γ := by unfold songExponent; linarith
    exact (Real.one_le_rpow hn1 h1).trans hy.le
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hEPk : ∀ (k : ℕ), 1 ≤ k → ∀ t : ℝ,
      ‖∑ m ∈ subWindow n y t, eC ((k : ℝ) * (m : ℝ) ^ γ)‖ ≤
        C_E * ((k : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
          ((k : ℝ)⁻¹) * (n : ℝ) ^ (1 - γ)) :=
    fun k hk t => hEP n hnE y hy0 hy3 k hk t
  -- the window is bounded by `n`
  have hWn : ∀ m ∈ subWindow n y ((n : ℝ) / 3 + y), (m : ℝ) ≤ (n : ℝ) := by
    intro m hm
    have hw := abs_lt.mp (Finset.mem_filter.mp hm).2.1
    linarith [hw.2]
  have hWmass : ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y), (m : ℝ) ^ (1 - γ) ≤
      (n : ℝ) ^ (1 - γ) * (2 * y + 2) := by
    have h1 : ∀ m ∈ subWindow n y ((n : ℝ) / 3 + y),
        (m : ℝ) ^ (1 - γ) ≤ (n : ℝ) ^ (1 - γ) := by
      intro m hm
      exact Real.rpow_le_rpow (Nat.cast_nonneg m) (hWn m hm) (by linarith)
    have h2 := Finset.sum_le_sum h1
    have h3 : ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y), (n : ℝ) ^ (1 - γ) =
        ((subWindow n y ((n : ℝ) / 3 + y)).card : ℝ) * (n : ℝ) ^ (1 - γ) := by
      simp
    have h4 : ((subWindow n y ((n : ℝ) / 3 + y)).card : ℝ) ≤ 2 * y + 2 :=
      subWindow_card_le n y _ (by linarith)
    have h5 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - γ) := Real.rpow_nonneg hn0.le _
    rw [h3] at h2
    nlinarith
  -- the frequency zero term
  have hZ0 : ∀ d ∈ ({0, 1} : Finset ℕ),
      ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((0 : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
        (n : ℝ) ^ (1 - γ) * (2 * y + 2) := by
    intro d hd
    have hz : ∀ m : ℕ, eC (-((0 : ℝ) * ((m : ℝ) + d) ^ γ)) = 1 := by
      intro m
      have : -((0 : ℝ) * ((m : ℝ) + d) ^ γ) = 0 := by ring
      rw [this]
      simp [eC]
    calc ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((0 : ℝ) * ((m : ℝ) + d) ^ γ))‖
        ≤ ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
            ‖((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((0 : ℝ) * ((m : ℝ) + d) ^ γ))‖ :=
          norm_sum_le _ _
      _ = ∑ m ∈ subWindow n y ((n : ℝ) / 3 + y), (m : ℝ) ^ (1 - γ) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [norm_smul, norm_eC, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)]
      _ ≤ (n : ℝ) ^ (1 - γ) * (2 * y + 2) := hWmass
  -- the nonzero frequencies
  have hZh : ∀ d ∈ ({0, 1} : Finset ℕ), ∀ h ∈ Finset.Icc (-(H : ℤ)) H, h ≠ 0 →
      ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
        2 * (n : ℝ) ^ (1 - γ) * (C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
          (n : ℝ) ^ (1 - γ)) + 2) := by
    intro d hd h hhm hh
    obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hhm
    have habs : |h| ≤ (H : ℤ) := abs_le.mpr ⟨hz1, hz2⟩
    have hk1 : 1 ≤ h.natAbs := Int.natAbs_pos.mpr hh
    have hkH : ((h.natAbs : ℕ) : ℝ) ≤ (H : ℝ) := by
      have h1 : ((h.natAbs : ℕ) : ℝ) = |(h : ℝ)| := by
        have h2 : (((h.natAbs : ℕ) : ℤ) : ℝ) = ((|h| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
        have h3 : (((h.natAbs : ℕ) : ℤ) : ℝ) = ((h.natAbs : ℕ) : ℝ) := Int.cast_natCast _
        rw [h3] at h2
        rw [h2, Int.cast_abs]
      rw [h1]
      exact_mod_cast habs
    have hk0 : (0 : ℝ) < ((h.natAbs : ℕ) : ℝ) := by exact_mod_cast hk1
    refine (window_Z_bound γ hγ0 hγ1 n hn6 y hy1 hy3 C_E hCE hEPk d hd h hh).trans ?_
    have e1 : ((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hk0.le hkH (by norm_num)
    have e2 : ((((h.natAbs : ℕ) : ℝ)))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hk0]
      exact_mod_cast hk1
    have e3 : (0 : ℝ) ≤ (n : ℝ) ^ (γ / 2) := Real.rpow_nonneg hn0.le _
    have e4 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - γ) := Real.rpow_nonneg hn0.le _
    have hp1 : ((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) ≤
        (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) :=
      mul_le_mul e1 le_rfl e3 (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ (H:ℝ)) _)
    have hp2 : ((((h.natAbs : ℕ) : ℝ)))⁻¹ * (n : ℝ) ^ (1 - γ) ≤ 1 * (n : ℝ) ^ (1 - γ) :=
      mul_le_mul e2 le_rfl e4 (by norm_num)
    have hin : C_E * (((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
        ((((h.natAbs : ℕ) : ℝ)))⁻¹ * (n : ℝ) ^ (1 - γ)) + 2 ≤
        C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ)) + 2 := by
      have hsum' : ((h.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
          ((((h.natAbs : ℕ) : ℝ)))⁻¹ * (n : ℝ) ^ (1 - γ) ≤
          (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ) := by
        rw [one_mul] at hp2
        linarith
      have hcc := mul_le_mul_of_nonneg_left hsum' hCE
      linarith
    have hf0 : (0 : ℝ) ≤ 2 * (n : ℝ) ^ (1 - γ) := by positivity
    nlinarith
  -- the shifted sum over all frequencies
  have hsum : ∀ d ∈ ({0, 1} : Finset ℕ),
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖b H h‖ *
        ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
        (12 * Cb * C_E + 16 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
          (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by
    intro d hd
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    rw [← Finset.sum_erase_add _ (fun h => ‖b H h‖ *
      ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
        ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖) h0mem]
    -- the zero frequency
    have hzero : ‖b H 0‖ *
        ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((0 : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
        4 * Cb * ((H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by
      have h1 : ‖b H 0‖ ≤ Cb / (H : ℝ) := hb H hH 0 (by simp)
      have h2 := hZ0 d hd
      have h3 : ‖b H 0‖ * ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((0 : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
          (Cb / (H : ℝ)) * ((n : ℝ) ^ (1 - γ) * (2 * y + 2)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      have h4 : (2 * y + 2) ≤ 4 * y := by linarith
      have h5 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - γ) := Real.rpow_nonneg hn0.le _
      have h6 : (n : ℝ) ^ (1 - γ) * (2 * y + 2) ≤ 4 * y * (n : ℝ) ^ (1 - γ) := by
        nlinarith
      have h7 : (Cb / (H : ℝ)) * ((n : ℝ) ^ (1 - γ) * (2 * y + 2)) ≤
          4 * Cb * ((H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by
        rw [div_eq_mul_inv]
        calc (Cb * (H : ℝ)⁻¹) * ((n : ℝ) ^ (1 - γ) * (2 * y + 2))
            = (Cb * (H : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)) * (2 * y + 2) := by ring
          _ ≤ (Cb * (H : ℝ)⁻¹ * (n : ℝ) ^ (1 - γ)) * (4 * y) := by
              apply mul_le_mul_of_nonneg_left h4
              positivity
          _ = 4 * Cb * ((H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by ring
      linarith
    -- the nonzero frequencies
    have herase : ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, ‖b H h‖ *
        ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
          ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
        (12 * Cb * C_E + 12 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by
      have hBB : ∀ h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, ‖b H h‖ *
          ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
            ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
          (Cb / (H : ℝ)) * ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) := by
        intro h hh
        have hmem : h ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_of_mem_erase hh
        have hne : h ≠ 0 := Finset.ne_of_mem_erase hh
        have h1 : ‖b H h‖ ≤ Cb / (H : ℝ) := hb H hH h (abs_le.mpr (Finset.mem_Icc.mp hmem))
        have h2 := hZh d hd h hmem hne
        have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - γ) := Real.rpow_nonneg hn0.le _
        have h4 : (0 : ℝ) ≤ (n : ℝ) ^ (1 - γ / 2) := Real.rpow_nonneg hn0.le _
        have h5 : (0 : ℝ) ≤ (n : ℝ) ^ (γ / 2) := Real.rpow_nonneg hn0.le _
        have h6 : (1 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hHR (by norm_num)
        -- the exponent comparison
        have e1 : (n : ℝ) ^ (1 - γ) ≤ (n : ℝ) ^ (1 - γ / 2) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have e2 : (n : ℝ) ^ (1 - γ) * (n : ℝ) ^ (1 - γ) ≤ (n : ℝ) ^ (1 - γ / 2) := by
          rw [← Real.rpow_add hn0]
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have e3 : (n : ℝ) ^ (1 - γ) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2)) ≤
            (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by
          rw [← mul_assoc, mul_comm ((n : ℝ) ^ (1 - γ)) ((H : ℝ) ^ ((1 : ℝ) / 2)),
            mul_assoc, ← Real.rpow_add hn0, show 1 - γ + γ / 2 = 1 - γ / 2 by ring]
        have e4 : (n : ℝ) ^ (1 - γ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by
          calc (n : ℝ) ^ (1 - γ) ≤ (n : ℝ) ^ (1 - γ / 2) := e1
            _ = 1 * (n : ℝ) ^ (1 - γ / 2) := by rw [one_mul]
            _ ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) :=
                mul_le_mul_of_nonneg_right h6 h4
        have e5 : 2 * (n : ℝ) ^ (1 - γ) * (C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
            (n : ℝ) ^ (1 - γ)) + 2) ≤ (4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by
          have hexp : 2 * (n : ℝ) ^ (1 - γ) * (C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2) +
              (n : ℝ) ^ (1 - γ)) + 2) =
              2 * C_E * ((n : ℝ) ^ (1 - γ) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2))) +
              2 * C_E * ((n : ℝ) ^ (1 - γ) * (n : ℝ) ^ (1 - γ)) + 4 * (n : ℝ) ^ (1 - γ) := by
            ring
          rw [hexp]
          have hDD : (0 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by positivity
          have hA : 2 * C_E * ((n : ℝ) ^ (1 - γ) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2))) ≤
              2 * C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
          have hB : 2 * C_E * ((n : ℝ) ^ (1 - γ) * (n : ℝ) ^ (1 - γ)) ≤
              2 * C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by
            have h1 : (n : ℝ) ^ (1 - γ) * (n : ℝ) ^ (1 - γ) ≤
                (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by
              calc (n : ℝ) ^ (1 - γ) * (n : ℝ) ^ (1 - γ) ≤ (n : ℝ) ^ (1 - γ / 2) := e2
                _ = 1 * (n : ℝ) ^ (1 - γ / 2) := by rw [one_mul]
                _ ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) :=
                    mul_le_mul_of_nonneg_right h6 h4
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
          have hD' : 4 * (n : ℝ) ^ (1 - γ) ≤
              4 * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by linarith [e4]
          nlinarith [hA, hB, hD']
        have h7 : (0 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by positivity
        have hz1 : ‖b H h‖ * ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
            ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖ ≤
            (Cb / (H : ℝ)) * (2 * (n : ℝ) ^ (1 - γ) * (C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) *
              (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ)) + 2)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        have hz2 : (Cb / (H : ℝ)) * (2 * (n : ℝ) ^ (1 - γ) * (C_E * ((H : ℝ) ^ ((1 : ℝ) / 2) *
              (n : ℝ) ^ (γ / 2) + (n : ℝ) ^ (1 - γ)) + 2)) ≤
            (Cb / (H : ℝ)) * ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) :=
          mul_le_mul_of_nonneg_left e5 (by positivity)
        linarith [hz1, hz2]
      calc ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0, ‖b H h‖ *
            ‖∑ m ∈ subWindow n y ((n : ℝ) / 3 + y),
              ((m : ℝ) ^ (1 - γ) : ℝ) • eC (-((h : ℝ) * ((m : ℝ) + d) ^ γ))‖
          ≤ ∑ _h ∈ (Finset.Icc (-(H : ℤ)) H).erase 0,
              (Cb / (H : ℝ)) * ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) :=
            Finset.sum_le_sum hBB
        _ = (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) *
              ((Cb / (H : ℝ)) * ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (12 * Cb * C_E + 12 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by
            have hcard : (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) ≤ 2 * (H : ℝ) + 1 := by
              have h1 : ((Finset.Icc (-(H : ℤ)) H).erase 0).card ≤ (Finset.Icc (-(H : ℤ)) H).card :=
                Finset.card_le_card (Finset.erase_subset _ _)
              have h2 : ((Finset.Icc (-(H : ℤ)) H).card : ℝ) = 2 * (H : ℝ) + 1 := by
                rw [card_Icc_int]; push_cast; ring
              calc (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) ≤ ((Finset.Icc (-(H : ℤ)) H).card : ℝ) := by
                    exact_mod_cast h1
                _ = 2 * (H : ℝ) + 1 := h2
            have h7 : (0 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by positivity
            have h8 : (0 : ℝ) ≤ Cb / (H : ℝ) := by positivity
            have h9 : (0 : ℝ) ≤ (4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by positivity
            have h10 : (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) * ((Cb / (H : ℝ))) ≤ 3 * Cb := by
              have h11 : (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) ≤ 3 * (H : ℝ) := by linarith
              have h12 : (0 : ℝ) ≤ Cb / (H : ℝ) := h8
              calc (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) * (Cb / (H : ℝ)) ≤
                    (3 * (H : ℝ)) * (Cb / (H : ℝ)) := mul_le_mul_of_nonneg_right h11 h12
                _ = 3 * Cb := by field_simp
            have h13 : (((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) * ((Cb / (H : ℝ)) *
                ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)))) =
                ((((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) * (Cb / (H : ℝ))) *
                ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) := by ring
            rw [h13]
            have h14 : ((((Finset.Icc (-(H : ℤ)) H).erase 0).card : ℝ) * (Cb / (H : ℝ))) *
                ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) ≤
                (3 * Cb) * ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) :=
              mul_le_mul_of_nonneg_right h10 h9
            have h15 : (3 * Cb) * ((4 * C_E + 4) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2))) =
                (12 * Cb * C_E + 12 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by ring
            linarith [h14, h15]
    have hTB1 : (0 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) := by positivity
    have hTB2 : (0 : ℝ) ≤ (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ) := by positivity
    have hstep1 : (12 * Cb * C_E + 12 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) ≤
        (12 * Cb * C_E + 16 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) := by
      apply mul_le_mul_of_nonneg_right _ hTB1
      linarith
    have hstep2 : 4 * Cb * ((H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) ≤
        (12 * Cb * C_E + 16 * Cb) * ((H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by
      apply mul_le_mul_of_nonneg_right _ hTB2
      nlinarith [mul_nonneg hCb hCE]
    have hexp : (12 * Cb * C_E + 16 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
        (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) =
        (12 * Cb * C_E + 16 * Cb) * ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2)) +
        (12 * Cb * C_E + 16 * Cb) * ((H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by ring
    linarith [hzero, herase, hstep1, hstep2, hexp]
  -- combine the two shifted sums
  have hsplit : ∑ p ∈ windowPrimes n y, psWeight γ p *
      (majorant b H (-((p : ℝ) + 1) ^ γ) + majorant b H (-(p : ℝ) ^ γ)) =
      (∑ p ∈ windowPrimes n y, psWeight γ p * majorant b H (-((p : ℝ) + 1) ^ γ)) +
      ∑ p ∈ windowPrimes n y, psWeight γ p * majorant b H (-((p : ℝ) + ((0 : ℕ) : ℝ)) ^ γ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_add]
    norm_num
  rw [hsplit]
  have hb1 := window_relax γ hγ0 hγ1 n y b H (hmaj H hH) 1
  have hb0 := window_relax γ hγ0 hγ1 n y b H (hmaj H hH) 0
  have hs1 := hsum 1 (by norm_num)
  have hs0 := hsum 0 (by norm_num)
  have hnn : (0 : ℝ) ≤ 1 / γ := by positivity
  have hTB : (0 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
      (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ) := by positivity
  have hC0 : (0 : ℝ) ≤ 12 * Cb * C_E + 16 * Cb := by positivity
  have e1 := mul_le_mul_of_nonneg_left hs1 hnn
  have e0 := mul_le_mul_of_nonneg_left hs0 hnn
  have hfin : (1 / γ) * ((12 * Cb * C_E + 16 * Cb) *
        ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
          (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ))) +
      (1 / γ) * ((12 * Cb * C_E + 16 * Cb) *
        ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
          (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ))) =
      (1 / γ) * (24 * Cb * C_E + 32 * Cb) *
        ((H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
          (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ)) := by ring
  have htail : tailBudget γ n y H = (H : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (1 - γ / 2) +
      (H : ℝ)⁻¹ * y * (n : ℝ) ^ (1 - γ) := rfl
  rw [htail]
  linarith [hb1, hb0, e1, e0, hfin]

/-- The cut coefficients give the same truncated Fourier polynomial as Lemma 1. -/
theorem fourier_truncCoeff (a : ℕ → ℤ → ℂ) (H : ℕ) (x : ℝ) :
    fourier (truncCoeff a) H x =
      ∑ h ∈ (Finset.Icc (-(H : ℤ)) H).filter (fun h => h ≠ 0), a H h * eC (x * h) := by
  unfold Decomp139.fourier
  refine Finset.sum_congr rfl (fun h hh => ?_)
  have habs : |h| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1)
  show (if |h| ≤ (H : ℤ) then a H h else 0) * eC ((h : ℝ) * x) = a H h * eC (x * (h : ℝ))
  rw [if_pos habs, mul_comm (h : ℝ) x]

/-- Assembly. The exact type of `Decomp139.fourier_approximation`, from the three leaves
and the proved Lemma 1 majorant `song_lemma1_majorant591`. No sorry in this body. -/
theorem fourier_approximation_of_leaves :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  intro γ hγ hγ1
  have hγ0 : 0 < γ := by linarith
  obtain ⟨C₁, hC₁, a, b, hL1⟩ :=
    LeanLab.Song2020.Repair591FourierMajorant.song_lemma1_majorant591
  have hcoef : ∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖truncCoeff a H h‖ ≤ max C₁ 1 / |(h : ℝ)| := by
    intro H h hh
    have hpos : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
    by_cases habs : |h| ≤ (H : ℤ)
    · have hH : 1 ≤ H := by
        obtain ⟨h2, h3⟩ := abs_le.mp habs
        omega
      rw [show truncCoeff a H h = a H h from if_pos habs]
      calc ‖a H h‖ ≤ C₁ / |(h : ℝ)| := (hL1 H hH).1 h hh habs
        _ ≤ max C₁ 1 / |(h : ℝ)| := div_le_div_of_nonneg_right (le_max_left _ _) hpos.le
    · rw [show truncCoeff a H h = 0 from if_neg habs, norm_zero]
      exact div_nonneg (le_trans zero_le_one (le_max_right _ _)) (abs_nonneg _)
  obtain ⟨C₂, hC₂, N₀, hS2⟩ := leaf_s2_window_of_exponent_pair γ hγ hγ1
    (leaf_exponent_pair_half γ hγ hγ1) C₁ hC₁ b
    (fun H hH h hh => (hL1 H hH).2.1 h hh)
    (fun H hH x => le_trans (norm_nonneg _) ((hL1 H hH).2.2 x).2)
  refine ⟨truncCoeff a, max C₁ 1, le_max_right _ _, hcoef, C₂, hC₂, N₀, ?_⟩
  intro n hn y hy1 hy2 H hH α
  refine le_trans (leaf_saw_window_triangle γ hγ0 (truncCoeff a) b H ?_ n y α)
    (hS2 n hn y hy1 hy2 H hH)
  intro x
  rw [fourier_truncCoeff a H x]
  exact ((hL1 H hH).2.2 x).2

/-- Match: the assembly has exactly the type of the sealed step. -/
example : (∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H) :=
  fourier_approximation_of_leaves

end

/-- Twin check against the sealed declaration itself. -/
example : type_of% @LeanLab.Song2020.Decomp139.fourier_approximation :=
  fourier_approximation_of_leaves

end LeanLab.Song2020.SplitFourierApprox

#print axioms LeanLab.Song2020.SplitFourierApprox.fourier_approximation_of_leaves
#print axioms LeanLab.Song2020.SplitFourierApprox.fourier_truncCoeff
