import Mathlib
import LeanLab.ExceptionalSet.KernelMomentSupplyJ200
import LeanLab.ExceptionalSet.VaughanSupplyJ200

/-!
Sorry-free supply for the large `Φ_e` part of the kernel moment, P0082 page 369, Lemma 9 and
display (39), at the inner scale of `LEAF_display29_steps`.
Source: P0082, J. Bruedern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378.

Lemma 9 of the paper enters only as an explicit hypothesis `h9 : Lemma9`, as Lemma 4 does in
`EvenMinorSupplyJ200`. Vinogradov's minor arc estimate is the proved copy in
`VaughanSupplyJ200`.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.LargePhiSupplyJ200

open Real MeasureTheory Set Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp eC majorArcs calE Phie nu Lemma9)
open LeanLab.ExceptionalSet.OddKernel467 (evenKernel)

/-- `ℰ(κ)^r = ℰ(κ r)`. -/
theorem calE_rpow (γ κ r : ℝ) (N : ℕ) : calE γ κ N ^ r = calE γ (κ * r) N := by
  simp only [calE, ← Real.exp_mul]
  congr 1
  ring

/-- `ℰ(a) ℰ(b) = ℰ(a + b)`. -/
theorem calE_mul (γ a b : ℝ) (N : ℕ) : calE γ a N * calE γ b N = calE γ (a + b) N := by
  simp only [calE, ← Real.exp_add]
  congr 1
  ring

/-- `ℰ` is monotone in `κ` for `N ≥ 1`. -/
theorem calE_mono (γ a b : ℝ) (N : ℕ) (hN : 1 ≤ N) (hab : a ≤ b) :
    calE γ a N ≤ calE γ b N := by
  unfold calE
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _
  nlinarith

/-- `ℰ(c) ≤ X^η` for large `N`, any `c` and `η > 0`: `(log N)^{3-2γ} = o((log N)^γ)`. -/
theorem calE_le_F_pow (γ c η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → calE γ c N ≤ F γ N ^ η := by
  have hb : 0 < γ - (3 - 2 * γ) := by linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop hb).comp hlog
  apply eventually_atTop.mp
  filter_upwards [ht.eventually (eventually_ge_atTop (|c| / η)), eventually_ge_atTop (2 : ℕ)]
    with N hN hN2
  change |c| / η ≤ Real.log N ^ (γ - (3 - 2 * γ)) at hN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hsplit : Real.log N ^ γ = Real.log N ^ (3 - 2 * γ) * Real.log N ^ (γ - (3 - 2 * γ)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have ha : 0 ≤ Real.log N ^ (3 - 2 * γ) := (Real.rpow_pos_of_pos hL _).le
  have hc : c ≤ η * Real.log N ^ (γ - (3 - 2 * γ)) := by
    rw [div_le_iff₀ hη] at hN
    have := le_abs_self c
    linarith
  unfold calE F
  rw [← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hc ha]

/-- The prime minor arc sum is `≤ 14404 X^{1-3δ} (log X)^4` for `δ ≤ 1/30`, the scalar form of
Vinogradov's estimate. Copy of `MinorSup446.vaughan_scalar`, which reaches `DecompJ200`. -/
theorem vaughan_scalar (X δ : ℝ) (hX : 1 ≤ X) (hL : 1 ≤ Real.log X)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 30) :
    300 * (2 * X / Real.sqrt (X ^ (6 * δ)) + X ^ (4 / 5 : ℝ)) * (1 + Real.log X) ^ 4 +
        2 * Real.sqrt X * Real.log X + Real.log 4 * X ^ (6 * δ) ≤
      14404 * X ^ (1 - 3 * δ) * Real.log X ^ 4 := by
  let V := X ^ (1 - 3 * δ)
  let L := Real.log X
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hV : 0 ≤ V := Real.rpow_nonneg hX0.le _
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hLl : L ≤ L ^ 4 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hL (by norm_num : (1 : ℕ) ≤ 4))
  have h80 : X ^ (4 / 5 : ℝ) ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hP : X ^ (6 * δ) ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hs : Real.sqrt X ≤ V := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hsq : Real.sqrt (X ^ (6 * δ)) = X ^ (3 * δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    ring_nf
  have hp : X / Real.sqrt (X ^ (6 * δ)) = V := by
    dsimp [V]
    rw [hsq, Real.rpow_sub hX0, Real.rpow_one]
  have hLp : (1 + L) ^ 4 ≤ 16 * L ^ 4 := by
    calc
      _ ≤ (2 * L) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = _ := by ring
  have hm : 300 * (2 * X / Real.sqrt (X ^ (6 * δ)) + X ^ (4 / 5 : ℝ)) * (1 + L) ^ 4 ≤
      14400 * V * L ^ 4 := by
    rw [show 2 * X / Real.sqrt (X ^ (6 * δ)) = 2 * V by rw [mul_div_assoc, hp]]
    calc
      _ ≤ 300 * (3 * V) * (16 * L ^ 4) := by gcongr; linarith
      _ = _ := by ring
  have he : 2 * Real.sqrt X * L ≤ 2 * V * L ^ 4 := by gcongr
  have hc : Real.log 4 * X ^ (6 * δ) ≤ 2 * V * L ^ 4 := by
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hl4u : Real.log 4 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    calc
      _ ≤ 2 * V := mul_le_mul hl4u hP (Real.rpow_nonneg hX0.le _) (by norm_num)
      _ ≤ 2 * V * L ^ 4 := le_mul_of_one_le_right (by positivity) hL4
  change _ ≤ 14404 * V * L ^ 4
  change _ ≤ _ at hm he hc
  dsimp only [L] at hm he hc
  linarith

/-- The exponent arithmetic of display (39): with the `L¹` mass `≤ 7 log 4 X log X u`, the
minor arc sup `V ≤ 14404 X^{1-3δ} (log X)^4`, the measure `K ≤ 3c · 2X^{δ-1}` of the
`β` near the `h/2`, and `(log X)^9 c u² ≤ X^{5δ}`, the large part is `≪ N X² u^{-1}`. -/
theorem large_arith (N X δ u c lX L1 V K : ℝ) (hN : 0 ≤ N) (hX : 1 ≤ X) (hu : 0 < u)
    (hlX : 0 ≤ lX) (hc : 0 ≤ c) (hL10 : 0 ≤ L1) (hL1 : L1 ≤ 7 * Real.log 4 * X * lX * u)
    (hV0 : 0 ≤ V) (hV : V ≤ 14404 * X ^ (1 - 3 * δ) * lX ^ 4)
    (hK0 : 0 ≤ K) (hK : K ≤ 3 * c * (2 * X ^ (δ - 1)))
    (hgrow : lX ^ 9 * c * u ^ 2 ≤ X ^ (5 * δ)) :
    L1 * (N * V ^ 2 * K) ≤ (42 * Real.log 4 * 14404 ^ 2) * N * X ^ 2 * u⁻¹ := by
  have hX0 : 0 < X := by linarith
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hw : 0 < X ^ (5 * δ) := Real.rpow_pos_of_pos hX0 _
  have hid : X * (X ^ (1 - 3 * δ)) ^ 2 * X ^ (δ - 1) * X ^ (5 * δ) = X ^ 2 := by
    calc X * (X ^ (1 - 3 * δ)) ^ 2 * X ^ (δ - 1) * X ^ (5 * δ)
        = X ^ (1 : ℝ) * X ^ (1 - 3 * δ) * X ^ (1 - 3 * δ) * X ^ (δ - 1) * X ^ (5 * δ) := by
          rw [Real.rpow_one]; ring
      _ = X ^ ((1 : ℝ) + (1 - 3 * δ) + (1 - 3 * δ) + (δ - 1) + 5 * δ) := by
          rw [Real.rpow_add hX0, Real.rpow_add hX0, Real.rpow_add hX0, Real.rpow_add hX0]
      _ = X ^ ((2 : ℕ) : ℝ) := by congr 1; push_cast; ring
      _ = X ^ 2 := Real.rpow_natCast X 2
  have hstep : L1 * (N * V ^ 2 * K) ≤ (7 * Real.log 4 * X * lX * u) *
      (N * (14404 * X ^ (1 - 3 * δ) * lX ^ 4) ^ 2 * (3 * c * (2 * X ^ (δ - 1)))) := by
    have hV2 : V ^ 2 ≤ (14404 * X ^ (1 - 3 * δ) * lX ^ 4) ^ 2 := pow_le_pow_left₀ hV0 hV 2
    have h1 : N * V ^ 2 * K ≤
        N * (14404 * X ^ (1 - 3 * δ) * lX ^ 4) ^ 2 * (3 * c * (2 * X ^ (δ - 1))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hV2 hN) hK hK0 (by positivity)
    exact mul_le_mul hL1 h1 (by positivity) (by positivity)
  refine hstep.trans ?_
  have hr : (7 * Real.log 4 * X * lX * u) *
      (N * (14404 * X ^ (1 - 3 * δ) * lX ^ 4) ^ 2 * (3 * c * (2 * X ^ (δ - 1)))) =
      (42 * Real.log 4 * 14404 ^ 2) * N * u * (lX ^ 9 * c) *
        (X * (X ^ (1 - 3 * δ)) ^ 2 * X ^ (δ - 1)) := by ring
  rw [hr]
  have hX2 : X * (X ^ (1 - 3 * δ)) ^ 2 * X ^ (δ - 1) = X ^ 2 / X ^ (5 * δ) := by
    rw [← hid]; field_simp
  rw [hX2]
  have hg : lX ^ 9 * c ≤ X ^ (5 * δ) / u ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hgrow
  have hA : 0 ≤ (42 * Real.log 4 * 14404 ^ 2) * N * u := by positivity
  calc (42 * Real.log 4 * 14404 ^ 2) * N * u * (lX ^ 9 * c) * (X ^ 2 / X ^ (5 * δ))
      ≤ (42 * Real.log 4 * 14404 ^ 2) * N * u * (X ^ (5 * δ) / u ^ 2) *
          (X ^ 2 / X ^ (5 * δ)) := by gcongr
    _ = _ := by field_simp

/-- Fubini for the large part: if every fiber over `α ∈ A` is at most `g(α) M`, the double
integral is at most `M ∫_A g`. -/
theorem large_fubini (A : Set ℝ) (hA : MeasurableSet A) (g : ℝ → ℝ) (G : ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hint : Integrable G ((volume.restrict A).prod (volume.restrict A)))
    (hgi : Integrable g (volume.restrict A)) (M : ℝ)
    (hfib : ∀ α ∈ A, (∫ β, S.indicator G (α, β) ∂(volume.restrict A)) ≤ g α * M) :
    (∫ z, S.indicator G z ∂((volume.restrict A).prod (volume.restrict A))) ≤
      (∫ x, g x ∂(volume.restrict A)) * M := by
  have hI := hint.indicator hS
  rw [integral_prod _ hI, ← integral_mul_const]
  apply integral_mono_ae hI.integral_prod_left (hgi.mul_const M)
  filter_upwards [ae_restrict_mem hA] with α hα
  exact hfib α hα

/-- A nonnegative fiber function below `c` times the indicator of a set `U` of volume at most
`m` has integral at most `c m`. -/
theorem fiber_bound (A : Set ℝ) (hA : MeasurableSet A) [IsFiniteMeasure (volume.restrict A)]
    (f : ℝ → ℝ) (hf0 : ∀ β, 0 ≤ f β) (U : Set ℝ) (hU : MeasurableSet U) (c : ℝ)
    (hc : 0 ≤ c) (hfU : ∀ β ∈ A, f β ≤ U.indicator (fun _ => c) β) (m : ℝ) (hm : 0 ≤ m)
    (hUm : volume U ≤ ENNReal.ofReal m) :
    (∫ β, f β ∂(volume.restrict A)) ≤ c * m := by
  have hmono : (∫ β, f β ∂(volume.restrict A)) ≤
      ∫ β, U.indicator (fun _ => c) β ∂(volume.restrict A) := by
    apply integral_mono_of_nonneg (Eventually.of_forall hf0)
      ((integrable_const c).indicator hU)
    filter_upwards [ae_restrict_mem hA] with β hβ
    exact hfU β hβ
  refine hmono.trans ?_
  rw [integral_indicator_const c hU, smul_eq_mul, measureReal_def]
  have hle : ((volume.restrict A) U).toReal ≤ m :=
    ENNReal.toReal_le_of_le_ofReal hm ((Measure.restrict_apply_le _ _).trans hUm)
  nlinarith

/-- The `β` near some `α + h/2` with `|h| ≤ H` have volume at most `#h · 2r`. -/
theorem union_volume (s : Finset ℤ) (center : ℤ → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    volume (⋃ h ∈ s, Icc (center h - r) (center h + r)) ≤
      ENNReal.ofReal (s.card * (2 * r)) := by
  refine (measure_biUnion_finset_le s _).trans ?_
  have he (h : ℤ) : volume (Icc (center h - r) (center h + r)) = ENNReal.ofReal (2 * r) := by
    rw [Real.volume_Icc]; congr 1; ring
  simp_rw [he]
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/-- `X = F(N) ≥ 2` once `N ≥ 16`. Copy of `Display29Steps.two_le_F`. -/
theorem two_le_F (γ : ℝ) (h1 : 1 < γ) (N : ℕ) (hN : 16 ≤ N) : 2 ≤ F γ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    have he := Real.exp_one_lt_d9
    have : (16 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hp : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hL (by linarith)
  have := Real.add_one_le_exp (Real.log (N : ℝ) ^ γ)
  simp only [F]
  linarith

/-- `log X = (log N)^γ ≥ 1` once `N ≥ 16`. -/
theorem one_le_log_F (γ : ℝ) (h1 : 1 < γ) (N : ℕ) (hN : 16 ≤ N) : 1 ≤ Real.log (F γ N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    have he := Real.exp_one_lt_d9
    have : (16 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [F, Real.log_exp]
  exact Real.one_le_rpow hL (by linarith)

/-- P0082 page 369, the large `Φ_e` part, from Lemma 9 and display (39), CONDITIONAL ON
Lemma 9 as the hypothesis `h9`. For `δ < min(δ₉, 1/30)` and `κ ≤ κ₉/4`: the pairs with
`|Φ_e(β - α)| > N ℰ(2κ)^{-2/3}` have `|β - α| ≤ 2ℰ ≤ X^δ` and pass the Lemma 9 threshold, so `β`
lies within `X^{δ-1}` of some `α + h/2`, `|h| ≤ ℰ(κ₉)^{2/3}`; on the minor arcs
`|S(β)| ≤ 14404 X^{1-3δ} (log X)^4`, `|K_e| ≤ 1` and `|Φ_e| ≤ N`, and the `L¹` bound finishes. -/
theorem even_gram_large_of_lemma9 (h9 : Lemma9) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∫ z : ℝ × ℝ,
            {z : ℝ × ℝ | (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) <
                ‖Phie γ N (z.2 - z.1)‖}.indicator (fun z : ℝ × ℝ =>
              ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.1 ^ 2 *
                  evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.1‖ *
                ‖Sp (F γ N ^ (6 * δ)) (F γ N) z.2 ^ 2 *
                  evenKernel (calE γ (2 * κ) N ^ (-(1 / 3 : ℝ))) z.2‖ *
                ‖Phie γ N (z.2 - z.1)‖) z
            ∂(volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N))).prod
              (volume.restrict ((majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N)) (calE γ κ N)))) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ9, hδ9, h9'⟩ := h9 γ h1 h2
  refine ⟨min δ9 (1 / 30), lt_min hδ9 (by norm_num), fun δ hδ hδ0 => ?_⟩
  have hδ9' : δ < δ9 := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hδ30 : δ ≤ 1 / 30 := hδ0.le.trans (min_le_right _ _)
  obtain ⟨κ9, hκ9, N9, hN9⟩ := h9' δ hδ hδ9'
  refine ⟨κ9 / 4, by positivity, fun κ hκ hκle => ?_⟩
  obtain ⟨N3, hN3⟩ := EvenMinorSupplyJ200.log_F_sq_le_calE_quarter γ 1 h1 h2 one_pos
  obtain ⟨N2, hN2⟩ := KernelMomentSupplyJ200.four_le_calE γ κ h2 hκ
  obtain ⟨N5, hN5⟩ := calE_le_F_pow γ (2 * κ) δ h1 h2 hδ
  obtain ⟨N6, hN6⟩ := calE_le_F_pow γ (5 / 4 + 2 * κ9) (5 * δ) h1 h2 (by positivity)
  refine ⟨42 * Real.log 4 * 14404 ^ 2, by positivity,
    max (max (max N3 N2) (max N5 N6)) (max N9 16), fun N hN => ?_⟩
  have hN3' : N3 ≤ N := le_trans (by simp) hN
  have hN2' : N2 ≤ N := le_trans (by simp) hN
  have hN5' : N5 ≤ N := le_trans (by simp) hN
  have hN6' : N6 ≤ N := le_trans (by simp) hN
  have hN9' : N9 ≤ N := le_trans (by simp) hN
  have hN16 : 16 ≤ N := le_trans (by simp) hN
  have hN1 : 1 ≤ N := by omega
  have hX : 2 ≤ F γ N := two_le_F γ h1 N hN16
  have hlX1 : 1 ≤ Real.log (F γ N) := one_le_log_F γ h1 N hN16
  have hE4 : 4 ≤ calE γ κ N := hN2 N hN2'
  have hE0 : 0 < calE γ κ N := by linarith
  have hΔeq : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) = calE γ κ N ^ (-(2 / 3 : ℝ)) :=
    EvenMinorSupplyJ200.calE_two_mul γ κ N
  have hΔ0 : 0 < calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) := by
    rw [hΔeq]; exact Real.rpow_pos_of_pos hE0 _
  have hΔ1 : calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) < 1 := by
    rw [hΔeq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  set P := F γ N ^ (6 * δ) with hPdef
  set X := F γ N with hXdef
  set Δ := calE γ (2 * κ) N ^ (-(1 / 3 : ℝ)) with hΔdef
  set E := calE γ κ N with hEdef
  set A := (majorArcs P X)ᶜ ∩ Set.Icc (-E) E with hAdef
  set T₀ := (N : ℝ) * calE γ (2 * κ) N ^ (-(2 / 3 : ℝ)) with hT₀def
  set c := calE γ κ9 N ^ (2 / 3 : ℝ) with hcdef
  set r := X ^ (δ - 1) with hrdef
  set lX := Real.log X with hlXdef
  set V := 14404 * X ^ (1 - 3 * δ) * lX ^ 4 with hVdef
  set u := E ^ (1 / 3 : ℝ) with hudef
  have hX0 : 0 < X := by linarith
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hX0 _).le
  have hu0 : 0 < u := Real.rpow_pos_of_pos hE0 _
  have hc1 : 1 ≤ c := Real.one_le_rpow
    (by unfold calE; exact Real.one_le_exp (mul_nonneg hκ9.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast hN1)) _))) (by norm_num)
  have hV0 : 0 ≤ V := by positivity
  have hAm : MeasurableSet A :=
    (PrimeKernel264.measurableSet_majorArcs P X).compl.inter measurableSet_Icc
  haveI : IsFiniteMeasure (volume.restrict A) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Set.inter_subset_right).trans_lt measure_Icc_lt_top⟩
  let g : ℝ → ℝ := fun α => ‖Sp P X α ^ 2 * evenKernel Δ α‖
  let φ : ℝ × ℝ → ℝ := fun z => ‖Phie γ N (z.2 - z.1)‖
  let G : ℝ × ℝ → ℝ := fun z => g z.1 * g z.2 * φ z
  have hPc : Continuous (Phie γ N) := by unfold Phie eC; fun_prop
  have hφc : Continuous φ := (hPc.comp (continuous_snd.sub continuous_fst)).norm
  have hgc : Continuous g :=
    (((by unfold Sp eC; fun_prop : Continuous (Sp P X)).pow 2).mul
      (OddKernel467.evenKernel_continuous Δ)).norm
  have hgI : Integrable g := by
    simpa only [g, KernelMomentSupplyJ200.integrand, norm_mul, U1539.norm_eC, mul_one] using
      (KernelMomentSupplyJ200.total_integrable P X Δ 0 hΔ0 hΔ1).norm
  have hgi : Integrable g (volume.restrict A) := hgI.integrableOn
  have hcard : ∀ x, ‖Phie γ N x‖ ≤ N := by
    intro x
    unfold Phie
    refine (norm_sum_le _ _).trans ?_
    simp only [U1539.norm_eC, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h := (Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n => Even (nu γ n))).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
    exact_mod_cast h
  have hgg : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2)
      ((volume.restrict A).prod (volume.restrict A)) := hgi.mul_prod hgi
  have hint : Integrable G ((volume.restrict A).prod (volume.restrict A)) := by
    refine (hgg.const_mul (N : ℝ)).mono'
      (((hgc.comp continuous_fst).mul (hgc.comp continuous_snd)).mul hφc).aestronglyMeasurable
      (Eventually.of_forall (fun z => ?_))
    have hp : 0 ≤ g z.1 * g z.2 := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (norm_nonneg _))]
    have := mul_le_mul_of_nonneg_left (hcard (z.2 - z.1)) hp
    change g z.1 * g z.2 * ‖Phie γ N (z.2 - z.1)‖ ≤ (N : ℝ) * (g z.1 * g z.2)
    linarith
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | T₀ < φ z} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hφc.measurable
  -- the minor arc bound for `g`
  have hgβ : ∀ β ∈ A, g β ≤ V ^ 2 := by
    intro β hβ
    have hs := VaughanSupplyJ200.minor_vaughan_real P X β hX
      (Real.one_le_rpow (by linarith) (by positivity))
      (by
        have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
          (show 6 * δ ≤ 1 by linarith)
        simpa only [Real.rpow_one] using hh) hβ.1
    have hsv := hs.trans (vaughan_scalar X δ (by linarith) hlX1 hδ.le hδ30)
    have hk : ‖evenKernel Δ β‖ ≤ 1 := by
      rw [KernelMomentSupplyJ200.norm_evenKernel]
      have h := KernelTail385.kernel_abs_le_two_sub Δ ((1 / 2) * β) hΔ0 hΔ1
      linarith
    change ‖Sp P X β ^ 2 * evenKernel Δ β‖ ≤ V ^ 2
    rw [norm_mul, norm_pow]
    calc ‖Sp P X β‖ ^ 2 * ‖evenKernel Δ β‖ ≤ ‖Sp P X β‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hk (sq_nonneg _)
      _ ≤ V ^ 2 := by rw [mul_one]; exact pow_le_pow_left₀ (norm_nonneg _) hsv 2
  -- the Lemma 9 threshold and range
  have hthr : (N : ℝ) * calE γ κ9 N ^ (-(1 / 3 : ℝ)) ≤ T₀ := by
    rw [hT₀def, calE_rpow, calE_rpow]
    exact mul_le_mul_of_nonneg_left (calE_mono γ _ _ N hN1 (by linarith)) (Nat.cast_nonneg N)
  have hrange : 2 * E ≤ X ^ δ := by
    have h2E : 2 * E ≤ calE γ (2 * κ) N := by
      rw [show 2 * κ = κ + κ by ring, ← calE_mul]
      nlinarith
    exact h2E.trans (hN5 N hN5')
  -- the index set of `h`
  set H : ℤ := ⌊c⌋ with hHdef
  set hs : Finset ℤ := Finset.Icc (-H) H with hsdef
  have hH0 : 0 ≤ H := Int.floor_nonneg.mpr (by linarith)
  have hcardh : (hs.card : ℝ) ≤ 3 * c := by
    have hc' : hs.card = (2 * H + 1).toNat := by
      rw [hsdef, Int.card_Icc]; congr 1; ring
    rw [hc', show ((2 * H + 1).toNat : ℝ) = ((2 * H + 1 : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg (by omega)]
    push_cast
    have := Int.floor_le c
    linarith
  -- the fiber bound
  have hfib : ∀ α ∈ A, (∫ β, S.indicator G (α, β) ∂(volume.restrict A)) ≤
      g α * ((N : ℝ) * V ^ 2 * (hs.card * (2 * r))) := by
    intro α hα
    let U : Set ℝ := ⋃ h ∈ hs, Set.Icc (α + (h : ℝ) / 2 - r) (α + (h : ℝ) / 2 + r)
    have hU : MeasurableSet U :=
      Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Icc)
    have hga : 0 ≤ g α := norm_nonneg _
    have hcst : 0 ≤ g α * ((N : ℝ) * V ^ 2) := by positivity
    have hfb := fiber_bound A hAm (fun β => S.indicator G (α, β))
      (fun β => Set.indicator_nonneg (fun z _ => mul_nonneg (mul_nonneg (norm_nonneg _)
        (norm_nonneg _)) (norm_nonneg _)) _) U hU (g α * ((N : ℝ) * V ^ 2)) hcst
      (fun β hβ => ?_) (hs.card * (2 * r)) (by positivity)
      (union_volume hs (fun h => α + (h : ℝ) / 2) r hr0)
    · calc _ ≤ _ := hfb
        _ = _ := by ring
    · by_cases hb : (α, β) ∈ S
      · rw [Set.indicator_of_mem hb]
        have hb' : T₀ < ‖Phie γ N (β - α)‖ := hb
        have hab : |β - α| ≤ X ^ δ := by
          have h1' := abs_le.mpr ⟨hα.2.1, hα.2.2⟩
          have h2' := abs_le.mpr ⟨hβ.2.1, hβ.2.2⟩
          have := abs_sub (β) (α)
          linarith
        obtain ⟨h, hh, hhr⟩ := hN9 N hN9' (β - α) hab (lt_of_le_of_lt hthr hb')
        have hmem : β ∈ U := by
          refine Set.mem_iUnion₂.mpr ⟨h, ?_, ?_⟩
          · rw [hsdef, Finset.mem_Icc]
            have hhc : (h : ℝ) ≤ c ∧ -(h : ℝ) ≤ c := by
              constructor
              · exact (le_abs_self _).trans (by exact_mod_cast hh)
              · exact (neg_le_abs _).trans (by exact_mod_cast hh)
            constructor
            · have := Int.le_floor.mpr (show ((-h : ℤ) : ℝ) ≤ c by push_cast; exact hhc.2)
              omega
            · exact Int.le_floor.mpr hhc.1
          · rw [Set.mem_Icc]
            have := abs_le.mp hhr
            constructor <;> linarith [this.1, this.2]
        rw [Set.indicator_of_mem hmem]
        change g α * g β * ‖Phie γ N (β - α)‖ ≤ g α * ((N : ℝ) * V ^ 2)
        have hgb := hgβ β hβ
        have hgb0 : 0 ≤ g β := norm_nonneg _
        have hP := hcard (β - α)
        calc g α * g β * ‖Phie γ N (β - α)‖ ≤ g α * V ^ 2 * N := by gcongr
          _ = _ := by ring
      · rw [Set.indicator_of_notMem hb]
        exact Set.indicator_nonneg (fun _ _ => hcst) _
  have hmain := large_fubini A hAm g G S hSm hint hgi _ hfib
  -- the `L¹` bound
  have hL1 : (∫ x, g x ∂(volume.restrict A)) ≤ 7 * Real.log 4 * X * lX * u := by
    have h23 : Real.sqrt Δ = u⁻¹ := by
      rw [hΔeq, show (-(2 / 3 : ℝ)) = (1 / 3) * (-2) by norm_num,
        Real.rpow_mul hE0.le, ← hudef, Real.rpow_neg hu0.le, Real.sqrt_inv]
      norm_num
      rw [Real.sqrt_sq hu0.le]
    have h := (setIntegral_le_integral (s := A) hgI (Eventually.of_forall
      (fun _ => norm_nonneg _))).trans
      (KernelMomentSupplyJ200.shifted_weighted_mass_sqrt P X Δ hX hΔ0 hΔ1)
    rw [h23, div_inv_eq_mul] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  -- the growth condition
  have hgrow : lX ^ 9 * c * u ^ 2 ≤ X ^ (5 * δ) := by
    have hl9 : lX ^ 9 ≤ calE γ (1 * (1 / 4) * 5) N := by
      have h10 : lX ^ 9 ≤ (lX ^ 2) ^ 5 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hlX1 (by norm_num)
      have hq := hN3 N hN3'
      rw [calE_rpow] at hq
      refine h10.trans ((pow_le_pow_left₀ (sq_nonneg _) hq 5).trans (le_of_eq ?_))
      rw [← Real.rpow_natCast, calE_rpow]
      norm_num
    have hcc : c ≤ calE γ κ9 N := by
      rw [hcdef, calE_rpow]; exact calE_mono γ _ _ N hN1 (by nlinarith)
    have huu : u ^ 2 ≤ calE γ κ9 N := by
      rw [hudef, hEdef, calE_rpow, sq, calE_mul]
      exact calE_mono γ _ _ N hN1 (by linarith)
    have hprod : lX ^ 9 * c * u ^ 2 ≤
        calE γ (1 * (1 / 4) * 5) N * calE γ κ9 N * calE γ κ9 N := by
      have hl0 : 0 ≤ lX ^ 9 := by positivity
      have hc0 : 0 ≤ c := by linarith
      have hE5 : 0 ≤ calE γ (1 * (1 / 4) * 5) N := (Real.exp_pos _).le
      have hE9 : 0 ≤ calE γ κ9 N := (Real.exp_pos _).le
      calc lX ^ 9 * c * u ^ 2 ≤ calE γ (1 * (1 / 4) * 5) N * calE γ κ9 N * u ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul hl9 hcc hc0 hE5) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left huu (mul_nonneg hE5 hE9)
    refine hprod.trans ?_
    rw [calE_mul, calE_mul]
    refine le_trans (le_of_eq ?_) (hN6 N hN6')
    congr 1
    ring
  have hfin := large_arith N X δ u c lX (∫ x, g x ∂(volume.restrict A)) V
    (hs.card * (2 * r)) (Nat.cast_nonneg N) (by linarith) hu0
    (by linarith) (by linarith) (integral_nonneg (fun _ => norm_nonneg _)) hL1 hV0 le_rfl
    (by positivity) (by
      have h2r : 0 ≤ 2 * r := by positivity
      calc (hs.card : ℝ) * (2 * r) ≤ 3 * c * (2 * r) := mul_le_mul_of_nonneg_right hcardh h2r
        _ = _ := by rw [hrdef]) hgrow
  have hu' : u⁻¹ = E ^ (-(1 / 3 : ℝ)) := by rw [hudef, Real.rpow_neg hE0.le]
  rw [hu'] at hfin
  exact hmain.trans hfin

end LeanLab.ExceptionalSet.LargePhiSupplyJ200
