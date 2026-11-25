/-
Split of the LEAF `leaf_signed_fourier_large_translate` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_sum_localizes`, unit U-1539, P0082
Bruedern and Perelli 1998, §7, p. 369 to 370, proof of Lemma 9.

The paper writes the parity weight `(-1)^{ν_n}` as a square wave in `F(n)/2`, replaces it by the
smoothed square wave of display (40) with coefficients `c_h` of size at most about `1/|h|`, and
gets display (41): the signed sum is `Σ_h c_h Φ(α + h/2)` plus an error, with `Φ` the full sum.
The error is controlled by the count of `n` with `F(n)` within `Δ` of an integer, Lemma 4 and
display (31), and by the tail of the Fourier series beyond `|h| ≤ H`.  The split follows that:

* `leaf_signed_smoothed_expansion`, displays (40), (41) and (31) with Lemma 4: the signed sum is
  at most `N ℰ^(-1/3) / 2` plus `Σ_{|h| ≤ ⌊ℰ⌋} |c_h| ‖Φ(α + h/2)‖`, for coefficients with
  `|c_h| ≤ 2 / (|h| + 1)`.  HARD.
* `leaf_square_wave_coeff_sum`, the coefficient sum of display (41): `Σ_{|h| ≤ ⌊ℰ⌋} 2/(|h| + 1)`,
  which is of size `log ℰ`, is eventually at most `ℰ^(2/3) / 2`.  MEDIUM.

`leaf_signed_fourier_large_translate_of_leaves` proves the exact statement of the parent leaf
from these two pieces: if every `‖Φ(α + h/2)‖` with `|h| ≤ ℰ` were at most `N ℰ^(-1)`, the signed
sum would be at most `N ℰ^(-1/3) / 2 + N ℰ^(-1) ℰ^(2/3) / 2 = N ℰ^(-1/3)`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_sum_localizes

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: displays (40) and (41), p. 370, with the count of Lemma 4 and display (31), HARD.
For `1 < γ < 3/2` and `0 < δ < 1`, uniformly in every sufficiently small `κ`, eventually: for
`|α| ≤ F γ N ^ δ` there are coefficients `c_h` with `|c_h| ≤ 2 / (|h| + 1)`, the bound of the
smoothed square wave of display (40), such that the parity signed sum is at most
`N ℰ^(-1/3) / 2 + Σ_{|h| ≤ ⌊ℰ⌋} |c_h| ‖Σ_{N/2 < n ≤ N} e((α + h/2) F(n))‖`.  The term
`N ℰ^(-1/3) / 2` absorbs the smoothing error, bounded through Lemma 4 and display (31), and the
tail of the Fourier series beyond `|h| ≤ ℰ`, with smoothing width `Δ = ℰ^(-1/2)`. -/
theorem leaf_signed_smoothed_expansion (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
        ∃ c : ℤ → ℝ, (∀ h : ℤ, |c h| ≤ 2 / (|(h : ℝ)| + 1)) ∧
          ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖
            ≤ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 +
              ∑ h ∈ Finset.Icc (-⌊calE γ κ N⌋) ⌊calE γ κ N⌋,
                |c h| * ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ := by
  sorry

/-- LEAF: the coefficient sum of display (41), p. 370, MEDIUM.  For `1 < γ < 3/2` and every
`κ > 0`, eventually `Σ_{|h| ≤ ⌊ℰ⌋} 2 / (|h| + 1) ≤ ℰ^(2/3) / 2`: the left side is of size
`log ℰ` and `ℰ = exp(κ (log N)^(3 - 2γ))` tends to infinity. -/
theorem leaf_square_wave_coeff_sum (γ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ h ∈ Finset.Icc (-⌊calE γ κ N⌋) ⌊calE γ κ N⌋, (2 : ℝ) / (|(h : ℝ)| + 1)
        ≤ calE γ κ N ^ (2 / 3 : ℝ) / 2 := by
  -- partial sums bounded by `8 √(M+1)` by induction on `M`
  have hind : ∀ M : ℕ, ∑ h ∈ Finset.Icc (-(M : ℤ)) M, (2 : ℝ) / (|(h : ℝ)| + 1)
      ≤ 8 * Real.sqrt ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero =>
      simp
      have : (1 : ℝ) ≤ Real.sqrt 1 := by rw [Real.sqrt_one]
      linarith
    | succ M ih =>
      have hset : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ)
          = insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Finset.Icc (-(M : ℤ)) M)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
      rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      have e1 : |(((-((M : ℤ) + 1)) : ℤ) : ℝ)| = (M : ℝ) + 1 := by
        push_cast; rw [abs_neg]; exact abs_of_pos (by positivity)
      have e2 : |((((M : ℤ) + 1) : ℤ) : ℝ)| = (M : ℝ) + 1 := by
        push_cast; exact abs_of_pos (by positivity)
      rw [e1, e2]
      set a := Real.sqrt ((M : ℝ) + 1) with ha
      set b := Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) with hb
      have ha2 : a ^ 2 = (M : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hb2 : b ^ 2 = (M : ℝ) + 2 := by
        rw [hb, Real.sq_sqrt (by positivity)]; push_cast; ring
      have ha0 : 0 ≤ a := Real.sqrt_nonneg _
      have hb0 : 0 ≤ b := Real.sqrt_nonneg _
      have hb1 : 1 ≤ b := by nlinarith
      have hab : a ≤ b := by nlinarith
      have hstep : (2 : ℝ) / ((M : ℝ) + 1 + 1) + 2 / ((M : ℝ) + 1 + 1) ≤ 8 * (b - a) := by
        have hpos : (0 : ℝ) < (M : ℝ) + 1 + 1 := by positivity
        rw [← add_div, div_le_iff₀ hpos]
        have hprod : (b - a) * (b + a) = 1 := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hab) hb0, mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hb1)]
      linarith
  set g : ℝ := 3 - 2 * γ with hg
  have hg0 : 0 < g := by linarith
  set A : ℝ := (132 / κ) ^ g⁻¹ with hA
  refine ⟨⌈Real.exp A⌉₊ + 1, fun N hN => ?_⟩
  have hNA : Real.exp A ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp A)
    have h' : (⌈Real.exp A⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hlogA : A ≤ Real.log N := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hNA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  set L := Real.log (N : ℝ) ^ g with hL
  have hLT : 132 / κ ≤ L := by
    have h1 : ((132 / κ) ^ g⁻¹) ^ g ≤ L :=
      Real.rpow_le_rpow hA0 hlogA hg0.le
    rwa [Real.rpow_inv_rpow (by positivity) hg0.ne'] at h1
  have hx : 132 ≤ κ * L := by
    have := mul_le_mul_of_nonneg_left hLT hκ.le
    have h6 : κ * (132 / κ) = 132 := by field_simp
    linarith
  set s := Real.exp (κ * L / 6) with hs
  have hs23 : 23 ≤ s := by
    have := Real.add_one_le_exp (κ * L / 6); linarith
  have hE : calE γ κ N = s ^ 6 := by
    unfold calE; rw [hs, ← Real.exp_nat_mul]; congr 1; rw [hL]; push_cast; ring
  have hE23 : calE γ κ N ^ (2 / 3 : ℝ) = s ^ 4 := by
    unfold calE; rw [← Real.exp_mul, hs, ← Real.exp_nat_mul]; congr 1; rw [hL]; push_cast; ring
  rw [hE23]
  set E := calE γ κ N with hEdef
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hfl0 : 0 ≤ ⌊E⌋ := Int.floor_nonneg.mpr hE0
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ⌊E⌋ = (M : ℤ) := ⟨⌊E⌋.toNat, (Int.toNat_of_nonneg hfl0).symm⟩
  rw [hM]
  refine le_trans (hind M) ?_
  have hME : (M : ℝ) ≤ E := by
    have := Int.floor_le E; rw [hM] at this; exact_mod_cast this
  have hsq : Real.sqrt ((M : ℝ) + 1) ≤ s ^ 4 / 16 := by
    rw [Real.sqrt_le_left (by positivity)]
    have hs2 : (529 : ℝ) ≤ s ^ 2 := by nlinarith
    have h6 : (1 : ℝ) ≤ s ^ 6 := one_le_pow₀ (by linarith)
    have h8 : 529 * s ^ 6 ≤ s ^ 8 := by
      have : s ^ 8 = s ^ 2 * s ^ 6 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hs2 (by linarith)
    have hsq' : (s ^ 4 / 16) ^ 2 = s ^ 8 / 256 := by ring
    rw [hsq']
    rw [hE] at hME
    linarith
  linarith

/-- `leaf_signed_fourier_large_translate`, exact statement, from the two leaves. -/
theorem leaf_signed_fourier_large_translate_of_leaves (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
          N * calE γ κ N ^ (-(1 / 3 : ℝ))
              < ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ →
        ∃ h : ℤ, |(h : ℝ)| ≤ calE γ κ N ∧
          N * calE γ κ N ^ (-1 : ℝ)
            < ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ := by
  obtain ⟨κ₀, hκ₀, hE⟩ := leaf_signed_smoothed_expansion γ δ hγ₁ hγ₂ hδ₀ hδ₁
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨N₁, hN₁⟩ := hE κ hκ hκle
  obtain ⟨N₂, hN₂⟩ := leaf_square_wave_coeff_sum γ hγ₁ hγ₂ κ hκ
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN α hα hlarge
  obtain ⟨c, hc, hexp⟩ := hN₁ N (le_trans (le_max_left _ _) hN) α hα
  have hW := hN₂ N (le_trans (le_max_right _ _) hN)
  set E := calE γ κ N with hEdef
  have hEpos : 0 < E := by rw [hEdef]; unfold calE; exact Real.exp_pos _
  by_contra hno
  push_neg at hno
  set S := Finset.Icc (-⌊E⌋) ⌊E⌋ with hS
  have hterm : ∀ h ∈ S,
      |c h| * ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖
        ≤ (2 / (|(h : ℝ)| + 1)) * (N * E ^ (-1 : ℝ)) := by
    intro h hh
    rw [hS, Finset.mem_Icc] at hh
    have hhE : |(h : ℝ)| ≤ E := by
      rw [abs_le]
      have h1 : ((⌊E⌋ : ℤ) : ℝ) ≤ E := Int.floor_le E
      have h2 : (h : ℝ) ≤ ((⌊E⌋ : ℤ) : ℝ) := by exact_mod_cast hh.2
      have h3 : ((-⌊E⌋ : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh.1
      push_cast at h3
      constructor <;> linarith
    have hb := hno h hhE
    exact mul_le_mul (hc h) hb (norm_nonneg _)
      (div_nonneg (by norm_num) (by positivity))
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hNE : 0 ≤ (N : ℝ) * E ^ (-1 : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hEpos.le _)
  have hprod : (∑ h ∈ S, (2 : ℝ) / (|(h : ℝ)| + 1)) * (N * E ^ (-1 : ℝ))
      ≤ E ^ (2 / 3 : ℝ) / 2 * (N * E ^ (-1 : ℝ)) :=
    mul_le_mul_of_nonneg_right hW hNE
  have hpow : E ^ (2 / 3 : ℝ) * E ^ (-1 : ℝ) = E ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_add hEpos]; norm_num
  have hkey : E ^ (2 / 3 : ℝ) / 2 * (N * E ^ (-1 : ℝ)) = N * E ^ (-(1 / 3 : ℝ)) / 2 := by
    rw [← hpow]; ring
  linarith

end LeanLab.ExceptionalSet.U1539
