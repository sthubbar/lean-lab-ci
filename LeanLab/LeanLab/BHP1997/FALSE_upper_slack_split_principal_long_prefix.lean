/-
Refutation in Lean of the LEAF `upper_slack_split_principal_long_prefix` of
SPLIT_upper_slack_split_slack_distribution, and with it of its parent
`upper_slack_split_slack_distribution` of SPLIT_upper_slack_split_rescaled_short_distribution, as
those statements are written in Lean. The rescaling `lam` and the slack `δ` are universally
quantified there, while the density is the fixed number `v + δ`. Take the constant rescalings one
and two and the slacks one and two, all admissible, at modulus one with the trivial character and
the full prefix `t = 2 x ^ (11/20+ε)`. Subtracting the four bounds gives
`card J / log (x ^ (11/20+ε)) ≤ 6 C x ^ (11/20+ε) / log x ^ 2`, which fails for large `x` since
the interval J has at least `x ^ (11/20+ε) - 1` elements. No prime number input is used and the
raw weight is never evaluated. This is a result about the lab statement, not about P0069.
The theorem below needs no new definition and is fully proved.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- Four bounds give the difference of densities. Pure algebra in ℂ. -/
theorem long_prefix_false_aux (T D1 D2 k : ℂ) (E : ℝ)
    (h11 : ‖T - k * D1‖ ≤ E) (h12 : ‖2 * T - k * D1‖ ≤ E)
    (h21 : ‖T - k * D2‖ ≤ E) (h22 : ‖2 * T - k * D2‖ ≤ E) :
    ‖k * (D2 - D1)‖ ≤ 6 * E := by
  have heq : k * (D2 - D1) =
      ((2 : ℂ) * (T - k * D1) - (2 * T - k * D1)) - ((2 : ℂ) * (T - k * D2) - (2 * T - k * D2)) := by
    ring
  rw [heq]
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  calc _ ≤ ‖(2 : ℂ) * (T - k * D1) - (2 * T - k * D1)‖ +
        ‖(2 : ℂ) * (T - k * D2) - (2 * T - k * D2)‖ := norm_sub_le _ _
    _ ≤ (‖(2 : ℂ) * (T - k * D1)‖ + ‖2 * T - k * D1‖) +
        (‖(2 : ℂ) * (T - k * D2)‖ + ‖2 * T - k * D2‖) :=
          add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ 6 * E := by
          rw [norm_mul, norm_mul, n2]
          linarith

set_option maxHeartbeats 1000000 in
/-- FALSE, as written in Lean: the LEAF `upper_slack_split_principal_long_prefix` of
SPLIT_upper_slack_split_slack_distribution fails under its own hypotheses. Its conclusion, asked for
every slack `δ > 0` and every admissible rescaling `lam`, cannot hold, whatever `ω` and `ε` are; the
cited inputs `h4`, `h9`, `hω`, `hz` play no role. Counterexample: `δ` in one and two, `lam`
constantly one or constantly two with `Λ = 2`, `A = 2`, `q = 1`, the trivial character, and
`t = 2 x ^ (11/20+ε)`. Since the leaf is the special case of the parent
`upper_slack_split_slack_distribution` at the principal character and the long prefix, the parent is
false in the same sense. It confirms in Lean item 3 of notes/burst-20261122/
BHP1997-feed1122-FALSE-record.md, there argued through Chebyshev. -/
theorem upper_slack_split_principal_long_prefix_false
    (_h4 : Thm4.Theorem4Paper) (_h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (_hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (_hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ¬ (∀ δ : ℝ, 0 < δ → ∀ (lam : ℝ → ℕ → ℝ) (Λ : ℝ), (∀ x m, |lam x m| ≤ Λ) →
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) →
      ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ t : ℝ,
        x ^ (11 / 20 + ε) ≤ t → t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε lam x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ *
              ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
                upperDeletedIntegral ω ε + δ : ℝ)) /
              Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  intro H
  set v0 : ℝ := ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
    upperDeletedIntegral ω ε with hv0
  have hb1 : ∀ x m, |(fun (_ : ℝ) (_ : ℕ) => (1 : ℝ)) x m| ≤ 2 := by
    intro x m; norm_num
  have hb2 : ∀ x m, |(fun (_ : ℝ) (_ : ℕ) => (2 : ℝ)) x m| ≤ 2 := by
    intro x m; norm_num
  have hX1 : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
      (1 : ℝ) ≤ (fun (_ : ℝ) (_ : ℕ) => (1 : ℝ)) x m := ⟨0, fun _ _ _ _ => le_refl _⟩
  have hX2 : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
      (1 : ℝ) ≤ (fun (_ : ℝ) (_ : ℕ) => (2 : ℝ)) x m := ⟨0, fun _ _ _ _ => by norm_num⟩
  obtain ⟨C11, h11⟩ := H 1 one_pos _ 2 hb1 hX1 2 two_pos
  obtain ⟨C12, h12⟩ := H 1 one_pos _ 2 hb2 hX2 2 two_pos
  obtain ⟨C21, h21⟩ := H 2 two_pos _ 2 hb1 hX1 2 two_pos
  obtain ⟨C22, h22⟩ := H 2 two_pos _ 2 hb2 hX2 2 two_pos
  set C : ℝ := max (max C11 C12) (max C21 C22) with hC
  set x : ℝ := max (max C 4) (Real.exp (12 * (|C| + 1) + 1)) with hx
  have hxC : C ≤ x := le_trans (le_max_left _ _) (le_max_left _ _)
  have hx4 : (4 : ℝ) ≤ x := le_trans (le_max_right _ _) (le_max_left _ _)
  have hxe : Real.exp (12 * (|C| + 1) + 1) ≤ x := le_max_right _ _
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 12 * (|C| + 1) + 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hlogpos : 0 < Real.log x := by
    have : 0 ≤ |C| := abs_nonneg C
    linarith
  set a : ℝ := 11 / 20 + ε with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; have : (1:ℝ) / 10 ^ 8 ≤ 1 / 4 := by norm_num
                         linarith
  set Y : ℝ := x ^ a with hY
  have hY2 : (2 : ℝ) ≤ Y := by
    have hhalf : x ^ (1 / 2 : ℝ) ≤ Y :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [ha]; linarith)
    have h4' : (2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
      have : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := this.symm
        _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
    linarith
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hL : Real.log Y = a * Real.log x := by rw [hY, Real.log_rpow hx0]
  have hLpos : 0 < Real.log Y := by rw [hL]; positivity
  -- the trivial character at modulus one
  set χ : DirichletCharacter ℂ 1 := 1 with hχ
  have hχm : ∀ m : ℕ, χ (m : ZMod 1) = 1 := by
    intro m; rw [hχ]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  have hdel : Thm2.delta χ = 1 := by rw [Thm2.delta, if_pos hχ]
  have hq : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (2 : ℝ) := by
    have : (1 : ℝ) ≤ Real.log x := by
      have : 0 ≤ |C| := abs_nonneg C
      linarith
    rw [Nat.cast_one]
    calc (1 : ℝ) = 1 ^ (2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) this (by norm_num)
  -- the prefix is the whole interval
  set F := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ 2 * Y) with hF
  have hFJ : F = rightInterval ε x := by
    rw [hF]
    apply Finset.filter_true_of_mem
    intro m hm
    rw [rightInterval] at hm
    have h2 := (Finset.mem_Ioc.mp hm).2
    have : (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast h2
    exact le_trans this (Nat.floor_le (by rw [← ha, ← hY]; linarith))
  have hcard : Y - 1 ≤ (F.card : ℝ) := by
    rw [hFJ, rightInterval, Nat.card_Ioc]
    have hmono : ⌊x ^ (11 / 20 + ε)⌋₊ ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
      Nat.floor_le_floor (by rw [← ha, ← hY]; linarith)
    rw [Nat.cast_sub hmono]
    have e1 := Nat.lt_floor_add_one (2 * x ^ (11 / 20 + ε))
    have e2 := Nat.floor_le (show (0 : ℝ) ≤ x ^ (11 / 20 + ε) by rw [← ha, ← hY]; exact hY0)
    rw [← ha, ← hY] at e1 e2 ⊢
    linarith
  -- the coefficient for lam = 2 is twice the one for lam = 1
  have htwo : ∀ m, upperNormCoeff ε (fun (_ : ℝ) (_ : ℕ) => (2 : ℝ)) x m =
      2 * upperNormCoeff ε (fun (_ : ℝ) (_ : ℕ) => (1 : ℝ)) x m := by
    intro m; unfold upperNormCoeff; split_ifs <;> ring
  set T : ℂ := ∑ m ∈ F, (upperNormCoeff ε (fun (_ : ℝ) (_ : ℕ) => (1 : ℝ)) x m : ℂ) with hT
  set k : ℂ := (F.card : ℂ) with hk
  set D1 : ℂ := Thm2.delta χ * (((v0 + 1 : ℝ)) : ℂ) / (Real.log (x ^ (11 / 20 + ε)) : ℂ) with hD1
  set D2 : ℂ := Thm2.delta χ * (((v0 + 2 : ℝ)) : ℂ) / (Real.log (x ^ (11 / 20 + ε)) : ℂ) with hD2
  set E : ℝ := C * Y * Real.log x ^ (-(2 : ℝ)) with hE
  have hEmono : ∀ c : ℝ, c ≤ C → c * Y * Real.log x ^ (-(2 : ℝ)) ≤ E := by
    intro c hc
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hY0)
      (Real.rpow_nonneg hlogpos.le _)
  have hsum1 : ∀ D : ℂ, ∑ m ∈ F,
      ((upperNormCoeff ε (fun (_ : ℝ) (_ : ℕ) => (1 : ℝ)) x m : ℂ) * χ (m : ZMod 1) - D) =
      T - k * D := by
    intro D
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [hχm, mul_one, hT, hk]
  have hsum2 : ∀ D : ℂ, ∑ m ∈ F,
      ((upperNormCoeff ε (fun (_ : ℝ) (_ : ℕ) => (2 : ℝ)) x m : ℂ) * χ (m : ZMod 1) - D) =
      2 * T - k * D := by
    intro D
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [hχm, mul_one, hT, hk, htwo]
    push_cast
    rw [Finset.mul_sum]
  have hle2Y : Y ≤ 2 * Y := by linarith
  have hC11 : C11 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC12 : C12 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC21 : C21 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC22 : C22 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have b11 := h11 x (le_trans hC11 hxC) 1 le_rfl hq χ hχ (2 * Y) hle2Y le_rfl
  have b12 := h12 x (le_trans hC12 hxC) 1 le_rfl hq χ hχ (2 * Y) hle2Y le_rfl
  have b21 := h21 x (le_trans hC21 hxC) 1 le_rfl hq χ hχ (2 * Y) hle2Y le_rfl
  have b22 := h22 x (le_trans hC22 hxC) 1 le_rfl hq χ hχ (2 * Y) hle2Y le_rfl
  rw [← hF] at b11 b12 b21 b22
  have e11 : ‖T - k * D1‖ ≤ E := by
    have := hsum1 D1; rw [hD1] at this; rw [hD1, ← this]
    exact le_trans (by simpa [hv0] using b11) (hEmono _ hC11)
  have e12 : ‖2 * T - k * D1‖ ≤ E := by
    have := hsum2 D1; rw [hD1] at this; rw [hD1, ← this]
    exact le_trans (by simpa [hv0] using b12) (hEmono _ hC12)
  have e21 : ‖T - k * D2‖ ≤ E := by
    have := hsum1 D2; rw [hD2] at this; rw [hD2, ← this]
    exact le_trans (by simpa [hv0] using b21) (hEmono _ hC21)
  have e22 : ‖2 * T - k * D2‖ ≤ E := by
    have := hsum2 D2; rw [hD2] at this; rw [hD2, ← this]
    exact le_trans (by simpa [hv0] using b22) (hEmono _ hC22)
  have key := long_prefix_false_aux T D1 D2 k E e11 e12 e21 e22
  have hdiff : k * (D2 - D1) = ((F.card / Real.log Y : ℝ) : ℂ) := by
    rw [hk, hD1, hD2, hdel, ← ha, ← hY]
    have hL0 : (Real.log Y : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
    push_cast
    field_simp
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hLpos.le)] at key
  -- now real arithmetic
  rw [hE, Real.rpow_neg hlogpos.le, Real.rpow_two] at key
  rw [div_le_iff₀ hLpos, hL] at key
  have hlx2 : 0 < Real.log x ^ 2 := by positivity
  have key2 : (F.card : ℝ) * Real.log x ≤ 6 * C * Y * a := by
    have : (F.card : ℝ) * Real.log x ^ 2 ≤ 6 * C * Y * a * Real.log x := by
      have h := mul_le_mul_of_nonneg_right key hlx2.le
      have hinv : (Real.log x ^ 2)⁻¹ * Real.log x ^ 2 = 1 := inv_mul_cancel₀ hlx2.ne'
      calc (F.card : ℝ) * Real.log x ^ 2
          ≤ 6 * (C * Y * (Real.log x ^ 2)⁻¹) * (a * Real.log x) * Real.log x ^ 2 := h
        _ = 6 * C * Y * a * Real.log x * ((Real.log x ^ 2)⁻¹ * Real.log x ^ 2) := by ring
        _ = 6 * C * Y * a * Real.log x := by rw [hinv, mul_one]
    have h' : (F.card : ℝ) * Real.log x * Real.log x ≤ 6 * C * Y * a * Real.log x := by
      nlinarith
    exact le_of_mul_le_mul_right h' hlogpos
  have hCabs : C ≤ |C| + 1 := by have := le_abs_self C; linarith
  have hYhalf : Y / 2 ≤ (F.card : ℝ) := by linarith
  have h3 : Y / 2 * Real.log x ≤ 6 * (|C| + 1) * Y := by
    have := mul_le_mul_of_nonneg_right hYhalf hlogpos.le
    have h6 : 6 * C * Y * a ≤ 6 * (|C| + 1) * Y := by
      have hCa : C * a ≤ |C| + 1 := by
        rcases le_or_gt C 0 with hc | hc
        · nlinarith [abs_nonneg C]
        · have := mul_le_mul_of_nonneg_left ha1 hc.le
          linarith
      have := mul_le_mul_of_nonneg_right hCa hY0
      linarith
    linarith
  have h4 : Real.log x ≤ 12 * (|C| + 1) := by
    have hYp : 0 < Y := by linarith
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_left hcon hYp
    linarith
  linarith

end LeanLab.BHP1997.DecompC165d
