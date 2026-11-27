/-
Split of the LEAF `leaf_signed_smoothed_expansion` of
`LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_signed_fourier_large_translate`, unit S5-07,
P0082 Bruedern and Perelli 1998, §7, p. 369 to 370, proof of Lemma 9, displays (40) and (41),
with Lemma 4 of p. 359 as the counting input.

The paper writes the parity weight `(-1)^{ν_n}` as the square wave `s(F(n)/2)`, with
`s(x) = 1` for `{x} < 1/2` and `s(x) = -1` otherwise, and replaces `s` by a smoothed square wave
whose truncated Fourier series agrees with `s` up to a uniform small error away from the jumps.
The split separates the two ingredients:

* `leaf_s5_07_square_wave_truncation`, display (40): for a smoothing width `Δ ≤ 1/4` and a
  truncation `H ≥ 1` there are coefficients `b_h` with `‖b_h‖ ≤ 2/(|h|+1)` such that the
  truncated series `Σ_{|h| ≤ H} b_h e(h y/2)` is within `1/(HΔ)` of `(-1)^{⌊y⌋}` whenever
  `y` is at distance at least `Δ` from the integers, and within `2 + 1/(HΔ)` everywhere.
  This is pure Fourier analysis of an explicit periodic function; it is the only open piece.
* `near_integer_count_of_lemma4`, display (31) and Lemma 4 with `α = 1`: the number of
  `N/2 < n ≤ N` with `F(n)` within `Δ` of an integer is at most `ΔN + 2BN exp(-κ̃ (log N)^{3-2γ})`.
  Proved here from the named hypothesis `Lemma4`, so the assembly is CONDITIONAL ON Lemma4,
  which is the open, cited `U1539.lemma4`.

`leaf_signed_smoothed_expansion_of_leaves` proves the exact statement of the leaf being split, with
`H = ⌊ℰ⌋` and `Δ = ℰ^(-1/2)`: the smoothing error is at most `N/(HΔ) + 2·#near ≤ 4Nℰ^(-1/2) +
4|B|Nℰ^(-1)`, which is eventually below `Nℰ^(-1/3)/2`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_signed_fourier_large_translate

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: display (40), p. 370, the truncated smoothed square wave, MEDIUM. For a width
`0 < Δ ≤ 1/4` and a truncation `H ≥ 1` there are coefficients `b_h` with `‖b_h‖ ≤ 2/(|h|+1)`
such that for every real `y` the truncated series `Σ_{|h| ≤ H} b_h e(h y / 2)` approximates the
square wave `(-1)^{⌊y⌋} = s(y/2)` within `2 + 1/(HΔ)`, and within `1/(HΔ)` when
`Δ ≤ {y} ≤ 1 - Δ`. One takes for `b_h` the Fourier coefficients `2/(π i h)` of `s`, `h` odd,
times the factor `sin(π h Δ)/(π h Δ)` of the average of `s` over a window of length `Δ`; the
averaged wave equals `s(y/2)` away from the jumps, has modulus at most `1`, and its Fourier tail
beyond `H` is at most `4/(π² H Δ)`. -/
theorem leaf_s5_07_square_wave_truncation (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4)
    (H : ℤ) (hH : 1 ≤ H) :
    ∃ b : ℤ → ℂ, (∀ h : ℤ, ‖b h‖ ≤ 2 / (|(h : ℝ)| + 1)) ∧ ∀ y : ℝ,
      ‖(-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ Finset.Icc (-H) H, b h * eC (h / 2 * y)‖
          ≤ 2 + 1 / (H * Δ) ∧
        (Δ ≤ Int.fract y → Int.fract y ≤ 1 - Δ →
          ‖(-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ Finset.Icc (-H) H, b h * eC (h / 2 * y)‖
            ≤ 1 / (H * Δ)) := by
  sorry

private theorem s5_07_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem s5_07_norm_eC (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- Display (31) and Lemma 4 of p. 359 with `α = 1`: the near integer count. Proved from the
named hypothesis `Lemma4`. -/
theorem near_integer_count_of_lemma4 (hL4 : Lemma4) (γ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2) :
    ∃ κ' B : ℝ, 0 < κ' ∧ ∀ N : ℕ, 2 ≤ N → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          ¬ (Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ))).card : ℝ)
        ≤ Δ * N + 2 * (B * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))) := by
  obtain ⟨κ', B, hκ', hL⟩ := hL4 γ hγ₁ hγ₂
  refine ⟨κ', B, hκ', fun N hN Δ hΔ₀ hΔ₁ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hF1 : 1 < F γ N := by
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (Real.rpow_pos_of_pos (Real.log_pos hNr) _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    rw [abs_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num)
  have h1 := hL N hN1 1 hα (by simp) Δ 0 le_rfl hΔ₀ (by linarith)
  have h2 := hL N hN1 1 hα (by simp) 1 (1 - Δ) (by linarith) (by linarith) le_rfl
  simp only [one_mul] at h1 h2
  set S := Finset.Ioc (N / 2) N
  have hsub : S.filter (fun n : ℕ => ¬ (Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ))
      ⊆ S.filter (fun n : ℕ => 0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ) ∪
        S.filter (fun n : ℕ => 1 - Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_union, not_and_or, not_le] at hn ⊢
    have h0 := Int.fract_nonneg (F γ n)
    have h1' := Int.fract_lt_one (F γ n)
    rcases hn with ⟨hS, h | h⟩
    · exact Or.inl ⟨hS, h0, h⟩
    · exact Or.inr ⟨hS, h.le, h1'⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : ((S.filter (fun n : ℕ =>
      ¬ (Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ))).card : ℝ)
      ≤ ((S.filter (fun n : ℕ => 0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)).card : ℝ) +
        ((S.filter (fun n : ℕ => 1 - Δ ≤ Int.fract (F γ n) ∧
          Int.fract (F γ n) < 1)).card : ℝ) := by
    exact_mod_cast hcard
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).2
  linarith

/-- The numerical comparison of the assembly: `4 s⁻³ + 4 b s⁻⁶ ≤ s⁻² / 2` once
`s ≥ 20 + 24 b`, `b ≥ 0`. -/
theorem s5_07_numeric (s b : ℝ) (hb : 0 ≤ b) (hs : 20 + 24 * b ≤ s) :
    4 * (s ^ 3)⁻¹ + 4 * b * (s ^ 6)⁻¹ ≤ (s ^ 2)⁻¹ / 2 := by
  have hs0 : 0 < s := by linarith
  have h2 : 0 < s ^ 2 := by positivity
  have h3 : 0 < s ^ 3 := by positivity
  have h6 : 0 < s ^ 6 := by positivity
  have e3 : (s ^ 3)⁻¹ = (s ^ 2)⁻¹ * s⁻¹ := by rw [← mul_inv]; ring
  have e6 : (s ^ 6)⁻¹ = (s ^ 2)⁻¹ * (s ^ 4)⁻¹ := by rw [← mul_inv]; ring
  rw [e3, e6]
  have hi : s⁻¹ ≤ 1 / 20 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
  have hs4 : s ≤ s ^ 4 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hB' : b * (s ^ 4)⁻¹ ≤ 1 / 24 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
  have hp : 0 ≤ (s ^ 2)⁻¹ := by positivity
  have k1 : 4 * ((s ^ 2)⁻¹ * s⁻¹) ≤ (s ^ 2)⁻¹ * (4 / 20) := by
    have := mul_le_mul_of_nonneg_left hi hp; linarith
  have k2 : 4 * b * ((s ^ 2)⁻¹ * (s ^ 4)⁻¹) ≤ (s ^ 2)⁻¹ * (4 / 24) := by
    have := mul_le_mul_of_nonneg_left hB' hp
    calc 4 * b * ((s ^ 2)⁻¹ * (s ^ 4)⁻¹) = 4 * ((s ^ 2)⁻¹ * (b * (s ^ 4)⁻¹)) := by ring
      _ ≤ 4 * ((s ^ 2)⁻¹ * (1 / 24)) := by linarith
      _ = (s ^ 2)⁻¹ * (4 / 24) := by ring
  linarith

/-- `leaf_signed_smoothed_expansion`, exact statement, from the square wave leaf and the near
integer count, CONDITIONAL ON Lemma4 through `U1539.lemma4`. -/
theorem leaf_signed_smoothed_expansion_of_leaves (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
        ∃ c : ℤ → ℝ, (∀ h : ℤ, |c h| ≤ 2 / (|(h : ℝ)| + 1)) ∧
          ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖
            ≤ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 +
              ∑ h ∈ Finset.Icc (-⌊calE γ κ N⌋) ⌊calE γ κ N⌋,
                |c h| * ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ := by
  obtain ⟨κ', B, hκ', hcount⟩ := near_integer_count_of_lemma4 lemma4 γ hγ₁ hγ₂
  refine ⟨κ', hκ', fun κ hκ hκle => ?_⟩
  set g : ℝ := 3 - 2 * γ with hg
  have hg0 : 0 < g := by linarith
  set T : ℝ := 20 + 24 * |B| with hT
  have hT1 : 1 ≤ T := by have := abs_nonneg B; linarith
  set A : ℝ := (6 * Real.log T / κ) ^ g⁻¹ with hA
  refine ⟨⌈Real.exp A⌉₊ + 2, fun N hN α _ => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNA : Real.exp A ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp A)
    have h' : (⌈Real.exp A⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hlogA : A ≤ Real.log N := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hNA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (div_nonneg (by
    have := Real.log_nonneg hT1; linarith) hκ.le) _
  set L := Real.log (N : ℝ) ^ g with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (le_trans hA0 hlogA) _
  have hLT : 6 * Real.log T / κ ≤ L := by
    have h1 : ((6 * Real.log T / κ) ^ g⁻¹) ^ g ≤ L :=
      Real.rpow_le_rpow hA0 hlogA hg0.le
    rwa [Real.rpow_inv_rpow (div_nonneg (by have := Real.log_nonneg hT1; linarith) hκ.le)
      hg0.ne'] at h1
  have hx : 6 * Real.log T ≤ κ * L := by
    have := mul_le_mul_of_nonneg_left hLT hκ.le
    have h6 : κ * (6 * Real.log T / κ) = 6 * Real.log T := by field_simp
    linarith
  set s := Real.exp (κ * L / 6) with hs
  have hsT : T ≤ s := by
    rw [hs, ← Real.exp_log (by linarith : (0 : ℝ) < T)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs20 : 20 ≤ s := by have := abs_nonneg B; linarith
  have hspos : 0 < s := by linarith
  have hE : calE γ κ N = s ^ 6 := by
    unfold calE; rw [hs, ← Real.exp_nat_mul]; congr 1; rw [hL]; push_cast; ring
  have hE3 : calE γ κ N ^ (-(1 / 3 : ℝ)) = (s ^ 2)⁻¹ := by
    unfold calE
    rw [← Real.exp_mul, hs, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1; rw [hL]; push_cast; ring
  have hexpB : Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) ≤ (s ^ 6)⁻¹ := by
    rw [← hE]; unfold calE; rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    rw [← hg, ← hL]
    nlinarith
  set E := calE γ κ N with hEdef
  set H : ℤ := ⌊E⌋ with hHdef
  have hEge : (20 : ℝ) ≤ E := by
    rw [hE]
    have : s ≤ s ^ 6 := by
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hH1 : 1 ≤ H := by
    rw [hHdef]; exact Int.le_floor.mpr (by push_cast; linarith)
  have hHR : E / 2 ≤ (H : ℝ) := by
    have := Int.lt_floor_add_one E
    rw [← hHdef] at this; linarith
  set Δ : ℝ := (s ^ 3)⁻¹ with hΔ
  have hs3 : (8000 : ℝ) ≤ s ^ 3 := by nlinarith
  have hΔ₀ : 0 < Δ := by positivity
  have hΔ₁ : Δ ≤ 1 / 4 := by
    rw [hΔ]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨b, hb, hbw⟩ := leaf_s5_07_square_wave_truncation Δ hΔ₀ hΔ₁ H hH1
  refine ⟨fun h => ‖b h‖, fun h => by rw [abs_of_nonneg (norm_nonneg _)]; exact hb h, ?_⟩
  simp only [abs_of_nonneg (norm_nonneg _)]
  -- the expansion
  set S := Finset.Ioc (N / 2) N with hSdef
  set I := Finset.Icc (-H) H with hIdef
  set err : ℕ → ℂ := fun n =>
    (-1 : ℂ) ^ (nu γ n) - ∑ h ∈ I, b h * eC (h / 2 * F γ n) with herr
  have hsplit : ∑ n ∈ S, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)
      = ∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n) +
        ∑ n ∈ S, err n * eC (α * F γ n) := by
    have : ∀ n ∈ S, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)
        = ∑ h ∈ I, b h * eC ((α + h / 2) * F γ n) + err n * eC (α * F γ n) := by
      intro n _
      rw [herr]
      simp only
      have hh : ∀ h ∈ I, b h * eC ((α + h / 2) * F γ n)
          = b h * eC (h / 2 * F γ n) * eC (α * F γ n) := by
        intro h _
        rw [mul_assoc, ← s5_07_eC_add]; congr 2; ring
      rw [Finset.sum_congr rfl hh, ← Finset.sum_mul]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun h _ => (Finset.mul_sum _ _ _).symm)
  rw [hsplit]
  have hmain : ‖∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n)‖
      ≤ ∑ h ∈ I, ‖b h‖ * ‖∑ n ∈ S, eC ((α + h / 2) * F γ n)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun h _ => norm_mul _ _)
  -- the error sum
  set near := S.filter (fun n : ℕ => ¬ (Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ))
    with hnear
  have herrn : ∀ n ∈ S, ‖err n * eC (α * F γ n)‖
      ≤ 1 / (H * Δ) + 2 * (if n ∈ near then 1 else 0) := by
    intro n hn
    rw [norm_mul, s5_07_norm_eC, mul_one]
    obtain ⟨hall, hfar⟩ := hbw (F γ n)
    have hnu : nu γ n = ⌊F γ n⌋ := rfl
    simp only [herr, hnu]
    by_cases hmem : n ∈ near
    · rw [if_pos hmem]; linarith
    · rw [if_neg hmem]
      have : Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) ≤ 1 - Δ := by
        by_contra hc; exact hmem (Finset.mem_filter.mpr ⟨hn, hc⟩)
      linarith [hfar this.1 this.2]
  have hcnt : ∑ n ∈ S, (1 / (H * Δ) + 2 * (if n ∈ near then (1 : ℝ) else 0))
      = S.card * (1 / (H * Δ)) + 2 * near.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  have herrsum : ‖∑ n ∈ S, err n * eC (α * F γ n)‖
      ≤ S.card * (1 / (H * Δ)) + 2 * near.card := by
    rw [← hcnt]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum herrn)
  have hnearc := hcount N hN2 Δ hΔ₀ hΔ₁
  have hScard : (S.card : ℝ) ≤ N := by
    have : S.card ≤ N := by
      rw [hSdef, Nat.card_Ioc]; omega
    exact_mod_cast this
  -- numerics in `s`
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hHΔ : 1 / (H * Δ) ≤ 2 * (s ^ 3)⁻¹ := by
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH1
    rw [div_le_iff₀ (by positivity)]
    have h1 : s ^ 6 / 2 ≤ (H : ℝ) := by rw [← hE]; exact hHR
    have h2 : 2 * (s ^ 3)⁻¹ * (H * Δ) = 2 * H * ((s ^ 3)⁻¹ * (s ^ 3)⁻¹) := by rw [hΔ]; ring
    rw [h2]
    have h3 : (s ^ 3)⁻¹ * (s ^ 3)⁻¹ = (s ^ 6)⁻¹ := by
      rw [← mul_inv]; congr 1; ring
    rw [h3]
    have h4 : 2 * (s ^ 6 / 2) * (s ^ 6)⁻¹ = 1 := by field_simp
    have h5 : 0 ≤ (s ^ 6)⁻¹ := by positivity
    nlinarith
  have hBpart : 2 * (B * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)))
      ≤ 2 * (|B| * N * (s ^ 6)⁻¹) := by
    have he0 : 0 ≤ Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
    have : B * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ))
        ≤ |B| * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) hN0) he0
    have h2 : |B| * N * Real.exp (-κ' * Real.log N ^ (3 - 2 * γ)) ≤ |B| * N * (s ^ 6)⁻¹ :=
      mul_le_mul_of_nonneg_left hexpB (mul_nonneg (abs_nonneg B) hN0)
    linarith
  -- final comparison: 4 N s⁻³ + 4 |B| N s⁻⁶ ≤ N s⁻² / 2
  have hfin : (N : ℝ) * (2 * (s ^ 3)⁻¹) + 2 * (Δ * N + 2 * (|B| * N * (s ^ 6)⁻¹))
      ≤ N * (s ^ 2)⁻¹ / 2 := by
    have key := s5_07_numeric s |B| (abs_nonneg B) (by linarith)
    calc (N : ℝ) * (2 * (s ^ 3)⁻¹) + 2 * (Δ * N + 2 * (|B| * N * (s ^ 6)⁻¹))
        = N * (4 * (s ^ 3)⁻¹ + 4 * |B| * (s ^ 6)⁻¹) := by rw [hΔ]; ring
      _ ≤ N * ((s ^ 2)⁻¹ / 2) := mul_le_mul_of_nonneg_left key hN0
      _ = N * (s ^ 2)⁻¹ / 2 := by ring
  have hfull : ‖∑ n ∈ S, err n * eC (α * F γ n)‖ ≤ N * E ^ (-(1 / 3 : ℝ)) / 2 := by
    rw [hEdef, hE3]
    have hc1 : S.card * (1 / (H * Δ)) ≤ (N : ℝ) * (2 * (s ^ 3)⁻¹) := by
      apply mul_le_mul hScard hHΔ (by positivity) hN0
    have hc2 : (near.card : ℝ) ≤ Δ * N + 2 * (|B| * N * (s ^ 6)⁻¹) := by
      rw [hnear]; linarith
    linarith
  calc ‖∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n) +
        ∑ n ∈ S, err n * eC (α * F γ n)‖
      ≤ ‖∑ h ∈ I, b h * ∑ n ∈ S, eC ((α + h / 2) * F γ n)‖ +
        ‖∑ n ∈ S, err n * eC (α * F γ n)‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_comm (N * E ^ (-(1 / 3 : ℝ)) / 2)]; linarith

/-- Twin check: the assembly has the type of the leaf being split. -/
example : type_of% @leaf_signed_smoothed_expansion := @leaf_signed_smoothed_expansion_of_leaves

end LeanLab.ExceptionalSet.U1539
