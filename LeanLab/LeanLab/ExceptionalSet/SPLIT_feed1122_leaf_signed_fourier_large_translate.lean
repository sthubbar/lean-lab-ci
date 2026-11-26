/-
Split of the LEAF statement `leaf_signed_fourier_large_translate` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_sum_localizes`, burst-20261124 unit S6-10,
P0082 Bruedern and Perelli 1998, §7, p. 369 to 370, the proof of Lemma 9.

The paper removes the parity condition on `ν_n` by a smoothed square wave with Fourier
coefficients bounded by display (40), so that display (41) writes the sum as `Σ_h c_h Φ(α + h/2)`
up to the contribution of the `n` with `F(n)` near an integer, which Lemma 4 and display (31)
count.  The split follows exactly those two inputs:

* `leaf_square_wave_trig_approx`, display (40): for `0 < Δ ≤ 1/4` and every `H ≥ 1` there is a
  trigonometric polynomial `Σ_{|h| ≤ H} c_h e(h x / 2)` with `Σ |c_h| ≪ 1 + log (1/Δ)` that
  approximates `(-1)^⌊x⌋` within `≪ 1 / (Δ H)` whenever `x` is at distance at least `Δ` from the
  integers.  This is the truncation of the Fourier series of the square wave smoothed at scale
  `Δ`, whose coefficients satisfy `c_h ≪ min(|h|^(-1), Δ^(-1) h^(-2))`.
* `leaf_near_integer_count`, Lemma 4, p. 359, at `α = 1` with display (31): the number of
  `N/2 < n ≤ N` with `F(n)` within `Δ` of an integer is at most `Δ N + B N exp(-κ (log N)^(3-2γ))`.
  This one is proved here from the lab statement `lemma4` of `State1539`, an open statement.

The assembly `leaf_signed_fourier_large_translate_split` proves the parent statement from the
LEAF and the count with `Δ = ℰ^(-1/2)` and `H = ⌊ℰ⌋`: if every `|h| ≤ ℰ` had `‖Φ(α + h/2)‖ ≤ N ℰ^(-1)`, the
signed sum would be at most `N ℰ^(-1/2) C (1 + log ℰ)`, which is below `N ℰ^(-1/3)` for large `N`.

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_full_sum_minor_arc

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: display (40), p. 370, the smoothed square wave and its Fourier coefficients, in
truncated form.  There is `A > 0` such that for `0 < Δ ≤ 1/4` and every integer `H ≥ 1` some
coefficients `c_h`, `|h| ≤ H`, have `Σ_{|h| ≤ H} |c_h| ≤ A (1 + log (1/Δ))` and
`|(-1)^⌊x⌋ - Σ_{|h| ≤ H} c_h e(h x / 2)| ≤ A / (Δ H)` for every real `x` with
`Δ ≤ {x} ≤ 1 - Δ`.  The paper's function is the square wave convolved with a kernel of width
`Δ`; its coefficients obey `c_h ≪ min(|h|^(-1), Δ^(-1) h^(-2))`, which gives both bounds.
MEDIUM: one dimensional Fourier analysis, no arithmetic input. -/
theorem leaf_square_wave_trig_approx :
    ∃ A : ℝ, 0 < A ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      ∃ c : ℤ → ℂ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ A * (1 + Real.log (1 / Δ)) ∧
        ∀ x : ℝ, Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ →
          ‖(-1 : ℂ) ^ ⌊x⌋ - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖
            ≤ A / (Δ * H) := by
  sorry

/-- Lemma 4, p. 359, at `α = 1`, as used with display (31) on p. 370: for
`1 < γ < 3/2` there are `κ > 0` and `B` such that for `N ≥ 2` and `0 < Δ ≤ 1/4` at most
`Δ N + B N exp(-κ (log N)^(3-2γ))` of the `N/2 < n ≤ N` have `{F(n)} < Δ` or `{F(n)} > 1 - Δ`.
It is Lemma 4 applied to the two intervals `[0, Δ)` and `[1 - Δ, 1)`.  Proved from the lab
statement `lemma4` of `State1539`, itself an open statement, so CONDITIONAL ON Lemma 4. -/
theorem leaf_near_integer_count (γ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 ≤ N → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ)
        ≤ Δ * N + B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  obtain ⟨κ, B, hκ, h4⟩ := lemma4 γ hγ₁ hγ₂
  refine ⟨κ, 2 * B, hκ, ?_⟩
  intro N hN Δ hΔ0 hΔ4
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hF1 : 1 < F γ N := by
    unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
    have hp := Real.rpow_pos_of_pos (Real.log_pos hNr) γ
    have := Real.add_one_lt_exp (ne_of_gt hp)
    linarith
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    rw [abs_one]; exact Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num)
  set I := Finset.Ioc (N / 2) N with hI
  have hc1 := h4 N hN1 1 hα (by simp) Δ 0 le_rfl hΔ0 (by linarith)
  have hc2 := h4 N hN1 1 hα (by simp) 1 (1 - Δ) (by linarith) (by linarith) le_rfl
  simp only [one_mul] at hc1 hc2
  set A1 := I.filter (fun n : ℕ => 0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ) with hA1
  set A2 := I.filter (fun n : ℕ => 1 - Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1) with hA2
  have hsub : I.filter (fun n : ℕ => Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))
      ⊆ A1 ∪ A2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_union, hA1, hA2, Finset.mem_filter, Finset.mem_filter]
    rcases hn.2 with h | h
    · exact Or.inl ⟨hn.1, Int.fract_nonneg _, h⟩
    · exact Or.inr ⟨hn.1, h.le, Int.fract_lt_one _⟩
  have hcard : ((I.filter (fun n : ℕ => Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card
      : ℝ) ≤ (A1.card : ℝ) + A2.card := by
    have := le_trans (Finset.card_le_card hsub) (Finset.card_union_le A1 A2)
    exact_mod_cast this
  have e1 := (abs_le.mp hc1).2
  have e2 := (abs_le.mp hc2).2
  have : (A1.card : ℝ) + A2.card ≤ Δ * N + 2 * B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
    linarith
  linarith

/-- `e(a + b) = e(a) e(b)`. -/
private theorem sft_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ℰ` grows without bound: for `1 < γ < 3/2`, `κ > 0` and any `M`, eventually `M ≤ ℰ`. -/
private theorem sft_calE_large (γ κ M : ℝ) (hγ₂ : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → M ≤ calE γ κ N := by
  set p : ℝ := 3 - 2 * γ with hp
  have hp0 : 0 < p := by linarith
  set X : ℝ := max (Real.log (max M 1)) 0 / κ with hX
  have hX0 : 0 ≤ X := div_nonneg (le_max_right _ _) hκ.le
  set T : ℝ := X ^ (1 / p) with hT
  refine ⟨⌈Real.exp T⌉₊ + 1, ?_⟩
  intro N hN
  have hNe : Real.exp T ≤ (N : ℝ) := by
    have := Nat.le_ceil (Real.exp T)
    have h' : (⌈Real.exp T⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : _ ≤ N)
    linarith
  have hTL : T ≤ Real.log N := by
    rw [← Real.log_exp T]
    exact Real.log_le_log (Real.exp_pos _) hNe
  have hT0 : 0 ≤ T := Real.rpow_nonneg hX0 _
  have hXL : X ≤ Real.log N ^ p := by
    have h1 : T ^ p ≤ Real.log N ^ p := Real.rpow_le_rpow hT0 hTL hp0.le
    have h2 : T ^ p = X := by
      rw [hT, ← Real.rpow_mul hX0, one_div_mul_cancel hp0.ne', Real.rpow_one]
    linarith
  have hlog : Real.log (max M 1) ≤ κ * Real.log N ^ p := by
    have h1 : Real.log (max M 1) ≤ max (Real.log (max M 1)) 0 := le_max_left _ _
    have h2 : max (Real.log (max M 1)) 0 = κ * X := by
      rw [hX]; field_simp
    have := mul_le_mul_of_nonneg_left hXL hκ.le
    linarith
  have hM : max M 1 ≤ calE γ κ N := by
    unfold calE
    rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right M 1))]
    exact Real.exp_le_exp.mpr hlog
  exact le_trans (le_max_left _ _) hM

/-- The final comparison of the assembly: for `C ≥ 0`, eventually in `ℰ`,
`ℰ^(-1/2) C (1 + log ℰ) ≤ ℰ^(-1/3)`. -/
private theorem sft_final_compare (C : ℝ) (hC : 0 ≤ C) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ E : ℝ, M ≤ E →
      E ^ (-(1 / 2 : ℝ)) * (C * (1 + Real.log E)) ≤ E ^ (-(1 / 3 : ℝ)) := by
  refine ⟨(13 * C + 1) ^ (12 : ℝ), ?_, ?_⟩
  · exact Real.one_le_rpow (by linarith) (by norm_num)
  intro E hE
  have hE1 : 1 ≤ E := le_trans (Real.one_le_rpow (by linarith) (by norm_num)) hE
  have hE0 : 0 < E := by linarith
  set v : ℝ := E ^ (1 / 12 : ℝ) with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos hE0 _
  have hv1 : 13 * C + 1 ≤ v := by
    have h := Real.rpow_le_rpow (by positivity) hE (by norm_num : (0 : ℝ) ≤ 1 / 12)
    rw [← Real.rpow_mul (by linarith)] at h
    norm_num at h
    exact h
  have hlog : Real.log E ≤ 12 * v := by
    have := Real.log_le_rpow_div hE0.le (by norm_num : (0 : ℝ) < 1 / 12)
    rw [hv]; linarith
  have hlog0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hkey : C * (1 + Real.log E) ≤ v ^ 2 := by
    have h1 : C * (1 + Real.log E) ≤ C * (1 + 12 * v) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    have hv1' : 1 ≤ v := by linarith
    have h2 := mul_le_mul_of_nonneg_right hv1 hv0.le
    have h3 : C ≤ C * v := le_mul_of_one_le_right hC hv1'
    rw [sq]
    linarith
  have hv2 : v ^ 2 = E ^ (1 / 6 : ℝ) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hE0.le]; norm_num
  have hsplit : E ^ (-(1 / 3 : ℝ)) = E ^ (-(1 / 2 : ℝ)) * E ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hE0]; norm_num
  rw [hsplit, ← hv2]
  exact mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hE0.le _)

/-- `leaf_signed_fourier_large_translate` from display (40), `leaf_square_wave_trig_approx`,
and Lemma 4 with display (31), `leaf_near_integer_count`, with `Δ = ℰ^(-1/2)` and `H = ⌊ℰ⌋`. -/
theorem leaf_signed_fourier_large_translate_split (γ δ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ F γ N ^ δ →
          N * calE γ κ N ^ (-(1 / 3 : ℝ))
              < ‖∑ n ∈ Finset.Ioc (N / 2) N, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ →
        ∃ h : ℤ, |(h : ℝ)| ≤ calE γ κ N ∧
          N * calE γ κ N ^ (-1 : ℝ)
            < ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ := by
  obtain ⟨A, hA, hW⟩ := leaf_square_wave_trig_approx
  obtain ⟨κ₄, B, hκ₄, hcount⟩ := leaf_near_integer_count γ hγ₁ hγ₂
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set C : ℝ := 3 * A + (1 + A) * (1 + B') with hC
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨M, hM1, hMc⟩ := sft_final_compare C hC0
  refine ⟨κ₄, hκ₄, ?_⟩
  intro κ hκ hκle
  obtain ⟨N₁, hN₁⟩ := sft_calE_large γ κ (max M 16) hγ₂ hκ
  refine ⟨N₁ + 2, ?_⟩
  intro N hN α _hα hlarge
  by_contra hno
  push_neg at hno
  set E : ℝ := calE γ κ N with hEdef
  have hEM : max M 16 ≤ E := hN₁ N (by omega)
  have hE16 : 16 ≤ E := le_trans (le_max_right _ _) hEM
  have hE0 : 0 < E := by linarith
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- the parameters `Δ = ℰ^(-1/2)` and `H = ⌊ℰ⌋`
  set Δ : ℝ := E ^ (-(1 / 2 : ℝ)) with hΔ
  have hΔ0 : 0 < Δ := Real.rpow_pos_of_pos hE0 _
  have hsq : E ^ (1 / 2 : ℝ) * Δ = 1 := by
    rw [hΔ, ← Real.rpow_add hE0]; norm_num
  have hE4 : 4 ≤ E ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hE16 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hΔ4 : Δ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right hE4 hΔ0.le
    linarith
  set H : ℕ := ⌊E⌋₊ with hH
  have hH1 : 1 ≤ H := by
    rw [hH]; exact Nat.le_floor (by push_cast; linarith)
  have hHE : (H : ℝ) ≤ E := Nat.floor_le hE0.le
  have hHE2 : E ≤ 2 * (H : ℝ) := by
    have := Nat.lt_floor_add_one E
    rw [← hH] at this
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH1
    linarith
  obtain ⟨c, hcsum, happrox⟩ := hW Δ hΔ0 hΔ4 H hH1
  set K : ℝ := A * (1 + Real.log (1 / Δ)) with hK
  have hlogΔ : Real.log (1 / Δ) = Real.log E / 2 := by
    rw [hΔ, one_div, ← Real.rpow_neg hE0.le, neg_neg, Real.log_rpow hE0]; ring
  have hlogE0 : 0 ≤ Real.log E := Real.log_nonneg (by linarith)
  have hK0 : 0 ≤ K := by rw [hK, hlogΔ]; positivity
  -- the trigonometric polynomial
  set P : ℝ → ℂ := fun x => ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x) with hP
  have hPbd : ∀ x : ℝ, ‖P x‖ ≤ K := by
    intro x
    calc ‖P x‖ ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h * eC ((h : ℝ) / 2 * x)‖ := norm_sum_le _ _
      _ = ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖ := by
          apply Finset.sum_congr rfl; intro h _; rw [norm_mul, norm_eC, mul_one]
      _ ≤ K := hcsum
  set I := Finset.Ioc (N / 2) N with hI
  set bad := I.filter (fun n : ℕ => Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) with hbad
  -- the sum `T = Σ_n P(F(n)) e(αF(n)) = Σ_h c_h Φ(α + h/2)`
  have hT : ∑ n ∈ I, P (F γ n) * eC (α * F γ n) =
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * ∑ n ∈ I, eC ((α + h / 2) * F γ n) := by
    simp only [hP, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro n _
    rw [mul_assoc, ← sft_eC_add]
    congr 2
    ring
  have hTbd : ‖∑ n ∈ I, P (F γ n) * eC (α * F γ n)‖ ≤ K * (N * E ^ (-1 : ℝ)) := by
    rw [hT]
    calc ‖∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * ∑ n ∈ I, eC ((α + h / 2) * F γ n)‖
        ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h * ∑ n ∈ I, eC ((α + h / 2) * F γ n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖ * (N * E ^ (-1 : ℝ)) := by
          apply Finset.sum_le_sum; intro h hh
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply hno
          have hh' := Finset.mem_Icc.mp hh
          have h1 : |h| ≤ (H : ℤ) := abs_le.mpr hh'
          have h2 : |(h : ℝ)| ≤ (H : ℝ) := by
            rw [← Int.cast_abs]; exact_mod_cast h1
          linarith
      _ = (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) * (N * E ^ (-1 : ℝ)) := by
          rw [Finset.sum_mul]
      _ ≤ K * (N * E ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcsum (by positivity)
  -- the difference `S - T`, pointwise
  have hpt : ∀ n ∈ I, ‖(-1 : ℂ) ^ (nu γ n) - P (F γ n)‖
      ≤ A / (Δ * H) + (if n ∈ bad then 1 + K else 0) := by
    intro n hn
    by_cases hb : n ∈ bad
    · rw [if_pos hb]
      have h1 : ‖(-1 : ℂ) ^ (nu γ n)‖ = 1 := by
        rw [norm_zpow, norm_neg, norm_one, one_zpow]
      have h2 := norm_sub_le ((-1 : ℂ) ^ (nu γ n)) (P (F γ n))
      have h3 : 0 ≤ A / (Δ * H) := by positivity
      linarith [hPbd (F γ n)]
    · rw [if_neg hb, add_zero]
      have hb' : ¬ (Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) := by
        intro hc; exact hb (Finset.mem_filter.mpr ⟨hn, hc⟩)
      push_neg at hb'
      exact happrox (F γ n) hb'.1 hb'.2
  have hcard : ((I.card : ℕ) : ℝ) ≤ N := by
    rw [hI, Nat.card_Ioc]; exact_mod_cast Nat.sub_le N (N / 2)
  have hdiff : ‖∑ n ∈ I, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)
      - ∑ n ∈ I, P (F γ n) * eC (α * F γ n)‖
      ≤ N * (A / (Δ * H)) + (1 + K) * (bad.card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ n ∈ I, ((-1 : ℂ) ^ (nu γ n) * eC (α * F γ n) - P (F γ n) * eC (α * F γ n))‖
        ≤ ∑ n ∈ I, ‖(-1 : ℂ) ^ (nu γ n) * eC (α * F γ n) - P (F γ n) * eC (α * F γ n)‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ I, ‖(-1 : ℂ) ^ (nu γ n) - P (F γ n)‖ := by
          apply Finset.sum_congr rfl; intro n _
          rw [← sub_mul, norm_mul, norm_eC, mul_one]
      _ ≤ ∑ n ∈ I, (A / (Δ * H) + (if n ∈ bad then 1 + K else 0)) := Finset.sum_le_sum hpt
      _ = (I.card : ℝ) * (A / (Δ * H)) + (1 + K) * (bad.card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem,
            Finset.inter_eq_right.mpr (Finset.filter_subset _ _), Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ N * (A / (Δ * H)) + (1 + K) * (bad.card : ℝ) := by
          have : 0 ≤ A / (Δ * H) := by positivity
          have := mul_le_mul_of_nonneg_right hcard this
          linarith
  -- the bookkeeping
  have he1 : E ^ (-1 : ℝ) = Δ ^ 2 := by
    rw [hΔ, ← Real.rpow_natCast, ← Real.rpow_mul hE0.le]; norm_num
  have hΔ2E : Δ ^ 2 * E = 1 := by
    rw [← he1, Real.rpow_neg_one, inv_mul_cancel₀ hE0.ne']
  have hΔ1 : Δ ≤ 1 := by linarith
  have hΔsq : Δ ^ 2 ≤ Δ := by
    rw [sq]; have := mul_le_mul_of_nonneg_left hΔ1 hΔ0.le; linarith
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  have hAH : A / (Δ * H) ≤ 2 * A * Δ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 2 * Δ ^ 2 * H := by
      have := mul_le_mul_of_nonneg_left hHE2 (sq_nonneg Δ)
      linarith
    have h2 : A * 1 ≤ A * (2 * Δ ^ 2 * H) := mul_le_mul_of_nonneg_left h1 hA.le
    have h3 : A * (2 * Δ ^ 2 * H) = 2 * A * Δ * (Δ * H) := by ring
    linarith
  have hexp : Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) ≤ Δ ^ 2 := by
    rw [← he1, hEdef, Real.rpow_neg_one]
    unfold calE
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _
    have := mul_le_mul_of_nonneg_right hκle hL0
    linarith
  have hc : (bad.card : ℝ) ≤ Δ * N + B * N * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) :=
    hcount N hN2 Δ hΔ0 hΔ4
  have hcnt : (bad.card : ℝ) ≤ Δ * N + B' * N * Δ ^ 2 := by
    have h1 : B * N * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ))
        ≤ B' * N * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hNpos.le)
        (Real.exp_pos _).le
    have h2 : B' * N * Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) ≤ B' * N * Δ ^ 2 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    linarith
  set ℓ : ℝ := 1 + Real.log E with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hKℓ : K ≤ A * ℓ := by
    rw [hK, hlogΔ]; apply mul_le_mul_of_nonneg_left _ hA.le; linarith
  have hsum : ‖∑ n ∈ I, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖
      ≤ N * (Δ * (C * ℓ)) := by
    have hS : ‖∑ n ∈ I, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖
        ≤ N * (A / (Δ * H)) + (1 + K) * (bad.card : ℝ) + K * (N * E ^ (-1 : ℝ)) := by
      have := norm_add_le (∑ n ∈ I, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)
          - ∑ n ∈ I, P (F γ n) * eC (α * F γ n)) (∑ n ∈ I, P (F γ n) * eC (α * F γ n))
      rw [sub_add_cancel] at this
      linarith
    rw [he1] at hS
    have h1 : N * (A / (Δ * H)) ≤ N * (2 * A * Δ) := mul_le_mul_of_nonneg_left hAH hNpos.le
    have h2 : (1 + K) * (bad.card : ℝ) ≤ (1 + K) * (Δ * N + B' * N * Δ ^ 2) :=
      mul_le_mul_of_nonneg_left hcnt (by linarith)
    have h3 : (1 + K) * (Δ * N + B' * N * Δ ^ 2) ≤ (1 + K) * (N * Δ * (1 + B')) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : B' * N * Δ ^ 2 ≤ B' * N * Δ :=
        mul_le_mul_of_nonneg_left hΔsq (by positivity)
      linarith
    have h4 : K * (N * Δ ^ 2) ≤ K * (N * Δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔsq hNpos.le) hK0
    have hbr : 2 * A + (1 + K) * (1 + B') + K ≤ C * ℓ := by
      have hAℓ : A * 1 ≤ A * ℓ := mul_le_mul_of_nonneg_left hℓ1 hA.le
      have k1 : 2 * A + K ≤ 3 * A * ℓ := by linarith
      have k2 : (1 + K) * (1 + B') ≤ (1 + A) * ℓ * (1 + B') := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
      have k3 : C * ℓ = 3 * A * ℓ + (1 + A) * ℓ * (1 + B') := by rw [hC]; ring
      linarith
    have hNΔ : 0 ≤ N * Δ := by positivity
    have h5 : N * Δ * (2 * A + (1 + K) * (1 + B') + K) ≤ N * Δ * (C * ℓ) :=
      mul_le_mul_of_nonneg_left hbr hNΔ
    have h6 : N * (2 * A * Δ) + (1 + K) * (N * Δ * (1 + B')) + K * (N * Δ)
        = N * Δ * (2 * A + (1 + K) * (1 + B') + K) := by ring
    have h7 : N * Δ * (C * ℓ) = N * (Δ * (C * ℓ)) := by ring
    linarith
  have hfin : Δ * (C * ℓ) ≤ E ^ (-(1 / 3 : ℝ)) :=
    hMc E (le_trans (le_max_left _ _) hEM)
  have : ‖∑ n ∈ I, (-1 : ℂ) ^ (nu γ n) * eC (α * F γ n)‖ ≤ N * E ^ (-(1 / 3 : ℝ)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hfin hNpos.le)
  linarith

end LeanLab.ExceptionalSet.U1539
