/-
P0068 Zhan 1991, the LEAF `f_j0_moment_311_leaf_S9` of SPLIT_prop1_311_S9.lean, page 266, proof
of Proposition 1, split into three cited LEAFs. Burst 20261124, session S9, unit B-extra-3.
Source: papers/P0068.pdf, journal page 266, pdf page 8, read from the page image.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Page 266: for `|t| ≤ 3T₀`, Perron's formula, the shift to `Re w = 0` with Lemma 7, and Cauchy in `v`
give `f₁(1/2+it, χ) ≪ L^{1/2} (∫_{-N}^{N} |L'(1/2+it+iv, χ)|² dv/(1+|v|))^{1/2} + 1`, `χ ≠ χ₀`.
"By Lemma 2 we get"
`Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} |f₁|² dt ≪ L Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} dt ∫_{-N}^{N} |L'|² dv/(1+|v|) + qH
≪ L ∫_{-N}^{N} dv/(1+|v|) ∫_{T₁+v}^{T₁+v+H} Σ_{χ≠χ₀} |L'(1/2+it, χ)|² dt ≪ L⁵ qH`.
1. `fj0_pointwise_leaf_S9`: LEAF HARD, the pointwise bound, squared.
2. `moment_swap_leaf_S9`: LEAF MEDIUM, integrating in `t` and exchanging the integrals.
3. `Lk_window_leaf_S9`: LEAF MEDIUM, Lemma 2 on the shifted windows, `χ ≠ χ₀`.
4. `int_inv_one_add_abs_S9`: PROVED, `∫_{-R}^{R} dv/(1+|v|) = 2 log(1+R)`.
5. `fj0_moment_of_leaves_S9`: PROVED from 1, 2, 3, the statement of `f_j0_moment_311_leaf_S9`.
-/
import LeanLab.Zhan1991.SPLIT_prop1_311_S9

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: page 266, proof of Proposition 1, the pointwise bound before "By Lemma 2", squared:
Perron's formula for `f_{j₀}` with `c = 1/2 + L⁻¹`, `|t| ≤ 3T₀`, the shift of the integral to
`[-iN, iN]` with Lemma 7, and Cauchy in `v` give, for `χ ≠ χ₀`,
`|f_{j₀}(1/2+it, χ)|² ≪ L ∫_{-N}^{N} |L^{(k)}(1/2+it+iv, χ)|² dv/(1+|v|) + 1`, where `k = 1` for
`j₀ = 1`, coefficient `log n`, and `k = 0` for `2 ≤ j₀ ≤ 10`, coefficient `1`, the case the
paper covers by "without loss of generality". Class HARD. -/
theorem fj0_pointwise_leaf_S9 : ∀ c1 c2 c3 : ℝ, ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (j : Fin 20)
      (χ : DirichletCharacter ℂ q) (t : ℝ),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → j.val < 10 → χ ≠ 1 →
      |t| ≤ 3 * T0cut N A lam →
      ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * (Real.log N * (∫ v in Set.Ioc (-(N : ℝ)) N,
            ‖iteratedDeriv (if j.val = 0 then 1 else 0) (DirichletCharacter.LFunction χ)
              (1 / 2 + ((t + v : ℝ) : ℂ) * Complex.I)‖ ^ 2 / (1 + |v|)) + 1) := by
  sorry

/-- LEAF: page 266, the step from the first to the second line after "By Lemma 2": integrate a
pointwise bound `f_i(t) ≤ K (L ∫_{-R}^{R} g_i(t+v) dv/(1+|v|) + 1)` over `t ∈ (T₁, T₁+H]`, sum over
`i`, and exchange the `t` and `v` integrals, Tonelli for continuous nonnegative integrands on a
bounded box. Class MEDIUM. -/
theorem moment_swap_leaf_S9 {ι : Type*} (s : Finset ι) (f g : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) (hg : ∀ i ∈ s, Continuous (g i))
    (hg0 : ∀ i ∈ s, ∀ t, 0 ≤ g i t) (K L R T1 H : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (h : ∀ i ∈ s, ∀ t ∈ Set.Ioc T1 (T1 + H),
      f i t ≤ K * (L * (∫ v in Set.Ioc (-R) R, g i (t + v) / (1 + |v|)) + 1)) :
    ∑ i ∈ s, ∫ t in Set.Ioc T1 (T1 + H), f i t
      ≤ K * (L * (∫ v in Set.Ioc (-R) R,
          (∑ i ∈ s, ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g i t) / (1 + |v|)) + s.card * H) := by
  sorry

/-- LEAF: page 266, last line, Lemma 2 of page 261, display (2.1), on the windows
`(T₁ + v, T₁ + v + H]`, `|T₁| ≤ 2T₀`, `|v| ≤ N`, `H = N A⁻¹`:
`Σ_{χ≠χ₀} ∫ |L^{(k)}(1/2+it, χ)|² dt ≪ qH L³`, `k ≤ 1`. Negative `t` reduce to positive ones by
`L(1/2 - it, χ) = conj L(1/2 + it, χ̄)`, a bounded range of `t` costs `≪ q L`, and a window shorter
than `T^{1/3}` is enlarged to length `T^{1/3} ≪ H`. Class MEDIUM. -/
theorem Lk_window_leaf_S9 : ∀ c1 c2 c3 : ℝ, ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (k : ℕ) (U : ℝ),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → k ≤ 1 → |U| ≤ 3 * T0cut N A lam + N →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc U (U + N / A),
            ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
        ≤ K * q * (N / A) * Real.log N ^ 3 := by
  sorry

/-- PROVED: `∫_{-R}^{R} dv/(1+|v|) = 2 log(1+R)`, the `≪ L` of the `v` integral on page 266. -/
theorem int_inv_one_add_abs_S9 (R : ℝ) (hR : 0 ≤ R) :
    ∫ v in Set.Ioc (-R) R, 1 / (1 + |v|) = 2 * Real.log (1 + R) := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (by apply Continuous.intervalIntegrable
        exact continuous_const.div (by fun_prop) (fun v => by positivity))
    (by apply Continuous.intervalIntegrable
        exact continuous_const.div (by fun_prop) (fun v => by positivity))]
  have h1 : ∫ v in (0:ℝ)..R, 1 / (1 + |v|) = Real.log (1 + R) := by
    have : ∫ v in (0:ℝ)..R, 1 / (1 + |v|) = ∫ v in (0:ℝ)..R, 1 / (1 + v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hR] at hv
      simp [abs_of_nonneg hv.1]
    rw [this, intervalIntegral.integral_comp_add_left (fun x => 1 / x)]
    rw [integral_one_div_of_pos (by norm_num) (by linarith)]
    simp
  have h2 : ∫ v in (-R)..0, 1 / (1 + |v|) = ∫ v in (0:ℝ)..R, 1 / (1 + |v|) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun v : ℝ => 1 / (1 + |v|))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [h2, h1]; ring

/-- PROVED: `t ↦ |L^{(k)}(1/2+it, χ)|²` is continuous for `χ ≠ χ₀`, `L(s, χ)` being entire. -/
theorem Lk_sq_continuous_S9 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (k : ℕ) : Continuous (fun t : ℝ =>
      ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2) := by
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have hc : Continuous (iteratedDeriv k (DirichletCharacter.LFunction χ)) :=
    (hd.contDiff (n := ⊤)).continuous_iteratedDeriv k (by simp)
  exact ((hc.comp (by fun_prop)).norm).pow 2

/-- PROVED: `t ↦ |f_j(1/2+it, χ)|²` is continuous. -/
theorem fj_sq_continuous_S9 {q : ℕ} (j : ℕ) (x : ℝ) (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => ‖fj j x χ (1 / 2 + t * Complex.I)‖ ^ 2) := by
  refine Continuous.pow (Continuous.norm ?_) 2
  unfold fj
  apply continuous_finsetSum
  intro n hn
  have hn1 : 1 ≤ n := by
    simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

/-- PROVED from the three LEAFs: the statement of `f_j0_moment_311_leaf_S9`, page 266, with
`c₅' = 1`, `c₁' = c₂' = 0`, `c₃ = 1`, `N₀ = max(N₀', N₀'', 3)` and
`K = max(K_p, 0) (4 max(K_w, 0) + 1)`. -/
theorem fj0_moment_of_leaves_S9 : ∃ c5m : ℝ, 0 < c5m ∧ ∀ c5 ≥ c5m, ∃ c1m : ℝ, ∀ c1 ≥ c1m,
    ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T1 : ℝ) (j : Fin 20),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → |T1| ≤ 2 * T0cut N A lam →
      j.val < 10 → (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + N / A), ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * Real.log N ^ (5 : ℝ) * q * (N / A) := by
  refine ⟨1, one_pos, fun c5 _ => ⟨0, fun c1 _ => ⟨0, fun c2 _ => ⟨1, one_pos, ?_⟩⟩⟩⟩
  obtain ⟨Kp, Np, hP⟩ := fj0_pointwise_leaf_S9 c1 c2 1
  obtain ⟨Kw, Nw, hW⟩ := Lk_window_leaf_S9 c1 c2 1
  set Kp' := max Kp 0 with hKp'
  set Kw' := max Kw 0 with hKw'
  have hKp0 : 0 ≤ Kp' := le_max_right _ _
  have hKw0 : 0 ≤ Kw' := le_max_right _ _
  refine ⟨Kp' * (4 * Kw' + 1), max (max Np Nw) 3, ?_⟩
  intro N A lam q _ Nv T1 j hN0 hH hC hT1 hj _
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN0
  have hNP : Np ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN0
  have hNW : Nw ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN0
  set L := Real.log N with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hH' := hH
  obtain ⟨hA1, _, _, _, _, _⟩ := hH'
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hA1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  set H : ℝ := N / A with hHdef
  have hH0 : 0 ≤ H := by positivity
  have hHT0 : H ≤ T0cut N A lam := by
    unfold T0cut
    have : 0 ≤ |lam| * N := by positivity
    have := Real.pi_gt_three
    nlinarith
  set k : ℕ := if j.val = 0 then 1 else 0 with hk
  have hk1 : k ≤ 1 := by rw [hk]; split_ifs <;> norm_num
  set s := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1) with hs
  set g : DirichletCharacter ℂ q → ℝ → ℝ := fun χ t =>
    ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
    with hgdef
  have hmem : ∀ χ ∈ s, χ ≠ 1 := fun χ hχ => (Finset.mem_filter.mp hχ).2
  -- step 1: the pointwise LEAF, with `K_p` replaced by `max(K_p, 0)`
  have hpt : ∀ χ ∈ s, ∀ t ∈ Set.Ioc T1 (T1 + H),
      ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ Kp' * (L * (∫ v in Set.Ioc (-(N : ℝ)) N, g χ (t + v) / (1 + |v|)) + 1) := by
    intro χ hχ t ht
    have htT : |t| ≤ 3 * T0cut N A lam := by
      have h1 : |t| ≤ |T1| + H := by
        rw [abs_le] at hT1 ⊢
        constructor <;> linarith [ht.1, ht.2, abs_le.mp (le_refl |T1|)]
      linarith
    have h := hP N A lam q Nv j χ t hNP hH hC hj (hmem χ hχ) htT
    have hI : 0 ≤ ∫ v in Set.Ioc (-(N : ℝ)) N, g χ (t + v) / (1 + |v|) :=
      MeasureTheory.integral_nonneg (fun v => by
        have : 0 ≤ 1 + |v| := by positivity
        simp only [hgdef]; positivity)
    refine le_trans h ?_
    have hX : 0 ≤ L * (∫ v in Set.Ioc (-(N : ℝ)) N, g χ (t + v) / (1 + |v|)) + 1 := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  -- step 2: the exchange LEAF
  have hsw := moment_swap_leaf_S9 s (fun χ t => ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2)
    g (fun χ _ => fj_sq_continuous_S9 _ _ χ) (fun χ hχ => Lk_sq_continuous_S9 χ (hmem χ hχ) k)
    (fun χ _ t => by simp only [hgdef]; positivity) Kp' L N T1 H (by positivity) hH0 hpt
  refine le_trans hsw ?_
  -- step 3: the window LEAF inside the `v` integral
  set C : ℝ := Kw' * q * H * L ^ 3 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hvint : ∫ v in Set.Ioc (-(N : ℝ)) N,
      (∑ χ ∈ s, ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g χ t) / (1 + |v|)
      ≤ ∫ v in Set.Ioc (-(N : ℝ)) N, C * (1 / (1 + |v|)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · refine Filter.Eventually.of_forall (fun v => ?_)
      apply div_nonneg
      · apply Finset.sum_nonneg; intro χ _
        exact MeasureTheory.integral_nonneg (fun t => by simp only [hgdef]; positivity)
      · positivity
    · exact ((continuous_const.mul (continuous_const.div (by fun_prop)
        (fun v => by positivity))).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall (fun v hv => ?_))
      have hU : |T1 + v| ≤ 3 * T0cut N A lam + N := by
        have hv' : |v| ≤ N := abs_le.mpr ⟨hv.1.le, hv.2⟩
        have := abs_add_le T1 v
        have h0 : 0 ≤ T0cut N A lam := le_trans hH0 hHT0
        linarith
      have hw := hW N A lam q k (T1 + v) hNW hH hk1 hU
      have hw' : ∑ χ ∈ s, ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g χ t ≤ C := by
        refine le_trans hw ?_
        rw [hCdef]
        have : 0 ≤ (q : ℝ) * (N / A) * L ^ 3 := by positivity
        calc Kw * q * (N / A) * L ^ 3 = Kw * ((q : ℝ) * (N / A) * L ^ 3) := by ring
          _ ≤ Kw' * ((q : ℝ) * (N / A) * L ^ 3) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
          _ = Kw' * q * H * L ^ 3 := by rw [hHdef]; ring
      have hpos : 0 < 1 + |v| := by positivity
      beta_reduce
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hw' hpos.le
  rw [MeasureTheory.integral_const_mul, int_inv_one_add_abs_S9 N (by positivity)] at hvint
  -- step 4: constants
  have hlog : Real.log (1 + N) ≤ 2 * L := by
    rw [hLdef, ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show ((N : ℝ) ^ (2 : ℝ)) = (N : ℝ) * N by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
    nlinarith
  have hcard : (s.card : ℝ) ≤ q := by
    have h1 : s.card ≤ Fintype.card (DirichletCharacter ℂ q) := by
      rw [hs]; exact Finset.card_filter_le _ _
    have h2 : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
      simpa only [Nat.card_eq_fintype_card] using
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    have h3 : Nat.totient q ≤ q := Nat.totient_le q
    exact_mod_cast le_trans h1 (h2 ▸ h3)
  have hL5 : L ^ (5 : ℝ) = L ^ 5 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hL5]
  have hL4 : L ^ 3 * L * L ≤ L ^ 5 := le_of_eq (by ring)
  have hL5' : 1 ≤ L ^ 5 := one_le_pow₀ hL
  have hqH : 0 ≤ (q : ℝ) * H := by positivity
  have e1 : L * (C * (2 * Real.log (1 + N))) ≤ 4 * Kw' * ((q : ℝ) * H) * L ^ 5 := by
    have : C * (2 * Real.log (1 + N)) ≤ C * (2 * (2 * L)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    calc L * (C * (2 * Real.log (1 + N))) ≤ L * (C * (2 * (2 * L))) :=
          mul_le_mul_of_nonneg_left this hL0.le
      _ = 4 * Kw' * ((q : ℝ) * H) * (L ^ 3 * L * L) := by rw [hCdef]; ring
      _ ≤ 4 * Kw' * ((q : ℝ) * H) * L ^ 5 := by
          apply mul_le_mul_of_nonneg_left hL4; positivity
  have e2 : (s.card : ℝ) * H ≤ (q : ℝ) * H * L ^ 5 := by
    calc (s.card : ℝ) * H ≤ q * H := mul_le_mul_of_nonneg_right hcard hH0
      _ ≤ (q : ℝ) * H * L ^ 5 := le_mul_of_one_le_right hqH hL5'
  calc Kp' * (L * (∫ v in Set.Ioc (-(N : ℝ)) N,
          (∑ χ ∈ s, ∫ t in Set.Ioc (T1 + v) (T1 + v + H), g χ t) / (1 + |v|)) + s.card * H)
      ≤ Kp' * (L * (C * (2 * Real.log (1 + N))) + s.card * H) := by
        have h1 := mul_le_mul_of_nonneg_left hvint hL0.le
        exact mul_le_mul_of_nonneg_left (by linarith) hKp0
    _ ≤ Kp' * (4 * Kw' * ((q : ℝ) * H) * L ^ 5 + (q : ℝ) * H * L ^ 5) := by
        gcongr
    _ = Kp' * (4 * Kw' + 1) * L ^ 5 * q * (N / A) := by rw [hHdef]; ring

/-- The LEAF `f_j0_moment_311_leaf_S9` of SPLIT_prop1_311_S9.lean, wired through the split. -/
theorem fj0_moment_split_S9 : ∃ c5m : ℝ, 0 < c5m ∧ ∀ c5 ≥ c5m, ∃ c1m : ℝ, ∀ c1 ≥ c1m,
    ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T1 : ℝ) (j : Fin 20),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → |T1| ≤ 2 * T0cut N A lam →
      j.val < 10 → (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + N / A), ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * Real.log N ^ (5 : ℝ) * q * (N / A) :=
  fj0_moment_of_leaves_S9

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.int_inv_one_add_abs_S9
#print axioms LeanLab.Zhan1991.Lk_sq_continuous_S9
#print axioms LeanLab.Zhan1991.fj_sq_continuous_S9
#print axioms LeanLab.Zhan1991.fj0_moment_of_leaves_S9
