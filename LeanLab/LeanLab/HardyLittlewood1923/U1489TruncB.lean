/-
AI-written Lean code, Claude, 2026-10-22, PC run 20261022T1603Z-23862, unit U-1489, paper P0004.

# Hardy-Littlewood 1923, Theorem A from a WEAKER cited explicit formula `TruncExplicitPrimB`

U-1485 VERIFY asked whether the printed remainder of Davenport ch. 19 carries an extra
`x^{1/4} log x`. It does in Davenport's simplified form, where the exceptional zero `1 - β₁`
near `0` is pulled out of the zero sum and `(x^{1-β₁} - 1)/(1 - β₁) ≪ x^{1/4} log x` is put into
the remainder (the same structure is reproduced in Kedlaya's notes, ch. 11, with `x^c log x`).
U-1479's `TruncExplicitPrim` instead keeps the low-zero sum `Σ_{|γ| ≤ 1} m/|ρ|` in the remainder,
which is Montgomery-Vaughan Theorem 12.10 with the bound on its constant `C(χ)`; it needs no
`x^{1/4}` term. To make the chain safe under BOTH readings, this file states

* `TruncExplicitPrimB`: `TruncExplicitPrim` with `A x^{1/4} log x` added to the remainder.

It is implied by `TruncExplicitPrim` (`truncExplicitPrimB_of_trunc`, PROVED) and also by
Davenport's printed form, since `x^{δ}/δ ≤ 1/δ + x^{1/4} log x` for `0 < δ ≤ 1/4`.

PROVED from it, everything else unconditional:
* `psiChiPrimBound_of_B`: `PsiChiPrimBound Θ` for `1/4 ≤ Θ < 1` on `NoZerosRightPrim Θ`.
* `psiPowerLog_of_B`: U-1453's `PsiPowerLog Θ` for `1/4 ≤ Θ` on `NoZerosRight Θ`.
* `printedA_form_all_U1489`: eq 3.113 p. 21, every `r ≥ 3`, `47/64 ≤ Θ < 3/4`,
  CONDITIONAL ON `TruncExplicitPrimB` only. The final assembly repeats the short argument of
  U-1468 `printedA_form_all_U1468` with `PsiPowerLog Θ` in place of the full `ExplicitFormulaLog`,
  since `TruncExplicitPrimB` yields `PsiPowerLog Θ` only for `Θ ≥ 1/4`.

No `sorry`, no axiom. Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.U1482ZeroCount

namespace LeanLab.HardyLittlewood1923.U1489

open Real Finset
open LeanLab.HardyLittlewood1923
open LeanLab.HardyLittlewood1923.U1438 (NoZerosRight)
open LeanLab.HardyLittlewood1923.U1444 (singR)
open LeanLab.HardyLittlewood1923.U1453 (PsiPowerLog)
open LeanLab.HardyLittlewood1923.U1463
open LeanLab.HardyLittlewood1923.U1468
open LeanLab.HardyLittlewood1923.U1473 (NoZerosRightPrim PsiChiPrimBound)
open LeanLab.HardyLittlewood1923.U1479 (IsNTZero mult mult_nonneg TruncExplicitPrim
  exists_zero_finset sum_inv_norm_le zero_re_bounds)
open LeanLab.PNTPort.BV (psiChi)

/-- **Cited**, Davenport ch. 17 and 19 in its printed simplified shape, or Montgomery-Vaughan
Theorem 12.10: U-1479's `TruncExplicitPrim` with the extra remainder term `A x^{1/4} log x`. -/
def TruncExplicitPrimB : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ x T : ℝ, 2 ≤ x → 2 ≤ T → T ≤ x → (q : ℝ) ≤ x →
    ∀ s : Finset ℂ, (∀ ρ, ρ ∈ s ↔ IsNTZero χ ρ ∧ |ρ.im| ≤ T) →
      ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        A * (x * Real.log (q * x) ^ 2 / T + Real.log (q * x) ^ 2 +
          x ^ (1 / 4 : ℝ) * Real.log x +
          ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 1), mult χ ρ / ‖ρ‖)

/-- `TruncExplicitPrimB` is weaker than `TruncExplicitPrim`. -/
theorem truncExplicitPrimB_of_trunc (h : TruncExplicitPrim) : TruncExplicitPrimB := by
  obtain ⟨A, hA, hE⟩ := h
  refine ⟨A, hA, fun q _ χ hχ x T hx hT hTx hqx s hs => (hE q χ hχ x T hx hT hTx hqx s hs).trans ?_⟩
  have : 0 ≤ x ^ (1 / 4 : ℝ) * Real.log x :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  exact mul_le_mul_of_nonneg_left (by linarith) hA

/-- `x^{1/4} log x ≤ x^Θ (log x)² / log 2` for `x ≥ 2`, `Θ ≥ 1/4`. -/
lemma quarter_le {x Θ : ℝ} (hx : 2 ≤ x) (hΘ : 1 / 4 ≤ Θ) :
    x ^ (1 / 4 : ℝ) * Real.log x ≤ 1 / Real.log 2 * (x ^ Θ * Real.log x ^ 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hp : x ^ (1 / 4 : ℝ) ≤ x ^ Θ := Real.rpow_le_rpow_of_exponent_le (by linarith) hΘ
  have hp0 : 0 ≤ x ^ (1 / 4 : ℝ) := by positivity
  have h1 : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2, sq]; exact mul_le_mul_of_nonneg_left hlx (by linarith)
  calc x ^ (1 / 4 : ℝ) * Real.log x ≤ x ^ Θ * (Real.log x ^ 2 / Real.log 2) :=
        mul_le_mul hp h1 (by linarith) (by positivity)
    _ = 1 / Real.log 2 * (x ^ Θ * Real.log x ^ 2) := by ring

/-- **`PsiChiPrimBound Θ` for `1/4 ≤ Θ < 1` from `TruncExplicitPrimB`**, the zero count being
U-1482's PROVED `zeroCountUnit`. -/
theorem psiChiPrimBound_of_B (hE : TruncExplicitPrimB) {Θ : ℝ}
    (hΘ0 : 1 / 4 ≤ Θ) (hΘ1 : Θ < 1) (hZ : NoZerosRightPrim Θ) : PsiChiPrimBound Θ := by
  have hN := U1482.zeroCountUnit
  obtain ⟨A1, hA1, hcnt⟩ := id hN
  obtain ⟨A2, hA2, hexp⟩ := hE
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := 1 - Θ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set c1 : ℝ := (1 / δ + 1) / Real.log 2 + 2 with hc1
  have hc1n : 0 ≤ c1 := by rw [hc1]; positivity
  set Sb : ℝ := 3 * A1 * c1 with hSb
  have hSbn : 0 ≤ Sb := by rw [hSb]; positivity
  refine ⟨Sb + A2 * (8 + Sb) + A2 * (1 / Real.log 2), by positivity,
    fun q χ hq hprim x hx hqx => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  have hx0 : 0 < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  obtain ⟨s, hs⟩ := exists_zero_finset hN hprim hx0.le
  set S : ℝ := ∑ ρ ∈ s, mult χ ρ / ‖ρ‖ with hSdef
  have hLq : 0 ≤ Real.log (q * (x + 2)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact Real.log_nonneg (by nlinarith)
  have hS1 : S ≤ A1 * Real.log (q * (x + 2)) * (1 / δ + 1 + Real.log (x + 1)) := by
    refine sum_inv_norm_le (Z := IsNTZero χ) (mult_nonneg χ) hA1 hLq hδ hx0.le ?_ ?_ s
      (fun ρ hρ => (hs ρ).1 hρ)
    · intro n hn s' hs'
      refine ((hcnt q χ hprim n (Nat.cast_nonneg n)).2 s' hs').trans ?_
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hA1
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    · intro ρ hρ
      have := (zero_re_bounds hZ hprim hρ).2
      rw [hδdef]; exact this
  have hlog3 : Real.log (q * (x + 2)) ≤ 3 * Real.log x := by
    rw [← Real.log_rpow hx0]
    refine Real.log_le_log (by positivity) ?_
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 : (q : ℝ) * (x + 2) ≤ x * (x + 2) := mul_le_mul_of_nonneg_right hqx (by linarith)
    have h2 : x * (x + 2) ≤ x ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ x - 2))
        (by linarith : (0 : ℝ) ≤ x + 1)]
    linarith
  have hlog1 : Real.log (x + 1) ≤ 2 * Real.log x := by
    rw [← Real.log_rpow hx0]
    refine Real.log_le_log (by positivity) ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ x + 1)]
  have hfac : 1 / δ + 1 + Real.log (x + 1) ≤ c1 * Real.log x := by
    have h1 : 1 / δ + 1 ≤ (1 / δ + 1) / Real.log 2 * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlx (by positivity)
    rw [hc1]; nlinarith
  have hS : S ≤ Sb * Real.log x ^ 2 := by
    refine hS1.trans ?_
    calc A1 * Real.log (q * (x + 2)) * (1 / δ + 1 + Real.log (x + 1))
        ≤ A1 * (3 * Real.log x) * (c1 * Real.log x) := by
          have hF0 : 0 ≤ 1 / δ + 1 + Real.log (x + 1) := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x + 1)
            have := one_div_pos.2 hδ
            linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlog3 hA1) hfac hF0
            (mul_nonneg hA1 (by linarith))
      _ = Sb * Real.log x ^ 2 := by rw [hSb]; ring
  have hS0 : 0 ≤ S := sum_nonneg fun ρ _ => div_nonneg (mult_nonneg χ ρ) (norm_nonneg _)
  have hE1 := hexp q χ hprim x x hx hx le_rfl hqx s hs
  have hsmall : ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 1), mult χ ρ / ‖ρ‖ ≤ S :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun ρ _ _ => div_nonneg (mult_nonneg χ ρ) (norm_nonneg _)
  have hlqx : Real.log (q * x) ^ 2 ≤ 4 * Real.log x ^ 2 := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h0 : 0 ≤ Real.log (q * x) := Real.log_nonneg (by nlinarith)
    have h1 : Real.log (q * x) ≤ 2 * Real.log x := by
      rw [← Real.log_rpow hx0]
      refine Real.log_le_log (by positivity) ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith
    nlinarith
  have hxx : x * Real.log (q * x) ^ 2 / x = Real.log (q * x) ^ 2 := by field_simp
  have hq4 := quarter_le hx hΘ0
  set W : ℝ := x ^ Θ * Real.log x ^ 2 with hW
  have hR : ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0) +
      ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        A2 * (8 * Real.log x ^ 2 + S + 1 / Real.log 2 * W) := by
    refine hE1.trans ?_
    rw [hxx]
    exact mul_le_mul_of_nonneg_left (by linarith) hA2
  have hxΘ : 1 ≤ x ^ Θ := Real.one_le_rpow (by linarith) (by linarith)
  have hZs : ‖∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤ x ^ Θ * S := by
    refine (norm_sum_le _ _).trans ?_
    rw [hSdef, mul_sum]
    refine sum_le_sum fun ρ hρ => ?_
    have hre := (zero_re_bounds hZ hprim ((hs ρ).1 hρ).1).1
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mult_nonneg χ ρ),
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hp : x ^ ρ.re ≤ x ^ Θ := Real.rpow_le_rpow_of_exponent_le (by linarith) hre
    rw [mul_div_assoc]
    have h1 : 0 ≤ mult χ ρ / ‖ρ‖ := div_nonneg (mult_nonneg χ ρ) (norm_nonneg _)
    calc mult χ ρ * (x ^ ρ.re / ‖ρ‖) = x ^ ρ.re * (mult χ ρ / ‖ρ‖) := by ring
      _ ≤ x ^ Θ * (mult χ ρ / ‖ρ‖) := mul_le_mul_of_nonneg_right hp h1
  have hL2 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hLW : Real.log x ^ 2 ≤ W := by rw [hW]; exact le_mul_of_one_le_left hL2 hxΘ
  have hSW : x ^ Θ * S ≤ Sb * W := by
    rw [hW]
    calc x ^ Θ * S ≤ x ^ Θ * (Sb * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = Sb * (x ^ Θ * Real.log x ^ 2) := by ring
  have hA2S : A2 * (8 * Real.log x ^ 2 + S + 1 / Real.log 2 * W) ≤
      A2 * (8 * W + Sb * W + 1 / Real.log 2 * W) := by
    refine mul_le_mul_of_nonneg_left ?_ hA2
    have : S ≤ Sb * W := hS.trans (mul_le_mul_of_nonneg_left hLW hSbn)
    linarith
  calc ‖psiChi x χ - (if q = 1 then (x : ℂ) else 0)‖
      = ‖(psiChi x χ - (if q = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
          ∑ ρ ∈ s, (mult χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ := by ring_nf
    _ ≤ A2 * (8 * Real.log x ^ 2 + S + 1 / Real.log 2 * W) + x ^ Θ * S :=
        (norm_sub_le _ _).trans (add_le_add hR hZs)
    _ ≤ A2 * (8 * W + Sb * W + 1 / Real.log 2 * W) + Sb * W := add_le_add hA2S hSW
    _ = (Sb + A2 * (8 + Sb) + A2 * (1 / Real.log 2)) * x ^ Θ * Real.log x ^ 2 := by
        rw [hW]; ring

/-- **U-1453's `PsiPowerLog Θ` for `Θ ≥ 1/4` on `NoZerosRight Θ`, from `TruncExplicitPrimB`.** -/
theorem psiPowerLog_of_B (hE : TruncExplicitPrimB) {Θ : ℝ} (hΘ : 1 / 4 ≤ Θ)
    (hZ : NoZerosRight Θ) : PsiPowerLog Θ := by
  refine U1473.psiPowerLog_of_prim (by linarith) ?_
  rcases lt_or_ge Θ 1 with h1 | h1
  · exact psiChiPrimBound_of_B hE hΘ h1 (U1473.noZerosRightPrim_of hZ)
  · exact U1479.psiChiPrimBound_mono h1 U1473.psiChiPrimBound_one

/-- **Printed Theorem A, eq. 3.113 p. 21, every `r ≥ 3`, every large `n`, `Θ ∈ [47/64, 3/4)`, on
the paper's Hypothesis R at level `Θ`, CONDITIONAL ON `TruncExplicitPrimB` only.** The argument
is U-1468's `printedA_form_all_U1468` with `PsiPowerLog Θ` used at the one `Θ` in play. -/
theorem printedA_form_all_U1489 (hE : TruncExplicitPrimB) :
    ∀ r : ℕ, 3 ≤ r → ∀ Θ : ℝ, 47 / 64 ≤ Θ → Θ < 3 / 4 → NoZerosRight Θ →
      ∃ B : ℕ, ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        |nur r n - (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n| ≤
          K * (n : ℝ) ^ ((r : ℝ) - 1 + (Θ - 3 / 4)) * Real.log n ^ B := by
  intro r hr Θ h0 h1 hZ
  have hψ := psiPowerLog_of_B hE (by linarith) hZ
  obtain ⟨B₀, hA⟩ : ∃ B : ℕ, APow r (Θ - 3 / 4) B :=
    apow_all (θ := Θ) (by linarith) (by linarith) hψ
      (apow_three_of_bound (U1453.printedA3Bound_of_psiPowerLog h0 h1 hψ)) r hr
  obtain ⟨K, hK, n₀, hn⟩ := apow_mono (le_max_left B₀ r) hA
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  refine ⟨max B₀ (s + 2), K + 3 * (s + 2) * 2 ^ s, max n₀ 3, fun n hn' => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL1 := one_le_log_of_three hn3
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) := by positivity
  have hZ0 : 0 ≤ Real.log n ^ max B₀ (s + 2) := by positivity
  by_cases hpar : n % 2 = (s + 2) % 2
  · rw [← Mr_eq_printed_pos hr (by omega) hpar]
    refine (hn n hpar (le_trans (le_max_left _ _) hn')).trans ?_
    have : 0 ≤ 3 * (s + 2 : ℝ) * 2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    nlinarith
  · rw [(singRProductPos (s + 2) hr n (by omega)).2 hpar, mul_zero, sub_zero,
      abs_of_nonneg (nur_nonneg _ _)]
    refine (nur_unlike_le s n hpar).trans ?_
    have q1 : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) s
    have q2 : (n : ℝ) ^ s ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) :=
      npow_le_rpow (by omega) (by push_cast; linarith)
    have q3 : Real.log n ^ (s + 2) ≤ Real.log n ^ max B₀ (s + 2) :=
      log_pow_mono hn3 (le_max_right _ _)
    have hKY : 0 ≤ K * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    calc 3 * ((s : ℝ) + 2) * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 2)
        ≤ 3 * ((s : ℝ) + 2) * (2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4))) *
            Real.log n ^ max B₀ (s + 2) := by
          gcongr
          exact q1.trans (mul_le_mul_of_nonneg_left q2 (by positivity))
      _ ≤ (K + 3 * (s + 2) * 2 ^ s) * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
            Real.log n ^ max B₀ (s + 2) := by
          linarith only [hKY]

/-- The U-1482 headline is recovered: `TruncExplicitPrim` gives the same conclusion through `B`. -/
theorem printedA_form_all_U1489_of_trunc (hE : TruncExplicitPrim) :
    ∀ r : ℕ, 3 ≤ r → ∀ Θ : ℝ, 47 / 64 ≤ Θ → Θ < 3 / 4 → NoZerosRight Θ →
      ∃ B : ℕ, ∃ K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        |nur r n - (n : ℝ) ^ (r - 1) / ((r - 1).factorial : ℝ) * singR r n| ≤
          K * (n : ℝ) ^ ((r : ℝ) - 1 + (Θ - 3 / 4)) * Real.log n ^ B :=
  printedA_form_all_U1489 (truncExplicitPrimB_of_trunc hE)

/-! ### Vacuity -/

/-- The finset premise of `TruncExplicitPrimB` is satisfiable for every primitive `χ` and
`T ≥ 0`, by U-1482's PROVED zero count; and the Θ range meets `1/4 ≤ Θ < 1`. -/
theorem truncB_premise_nonvacuous {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    (∃ s : Finset ℂ, ∀ ρ, ρ ∈ s ↔ IsNTZero χ ρ ∧ |ρ.im| ≤ T) ∧
      (1 / 4 : ℝ) ≤ 47 / 64 ∧ (47 / 64 : ℝ) < 1 :=
  ⟨exists_zero_finset U1482.zeroCountUnit hχ hT, by norm_num, by norm_num⟩

end LeanLab.HardyLittlewood1923.U1489
