/-
P0068 Zhan 1991, the mean value LEAF `mv_FJ_311_leaf_S9` of SPLIT_prop3_311_S9.lean, page 268,
lines 2 and 3 of the proof of Proposition 3, split into three cited LEAFs.
Burst 20261124, session S9, unit B-extra-2. Source: papers/P0068.pdf, journal pages 266 and 268,
pdf pages 8 and 10, read from the page images. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Page 268: `F_i(s, χ) = Π_{j ∈ J_i} f_j(s, χ) = Σ_{n ≤ M_i} b_i(n) χ(n) n^{-s}`, `b_i(n) ≪ d₂₀(n)`;
"By Lemma 6 and (3.13)" `Σ_χ ∫ |F_i|² ≪ Σ_{n ≤ M_i} (qH + n) b_i²(n) n⁻¹ ≪ (qH + M_i) L^{c₀}`.
Page 266, (3.13): `Σ_{n≤x} d_k²(n) ≪ x (log x)^{c_k}`, `Σ_{n≤x} d_k²(n)/n ≪ (log x)^{c_k}`, `k ≥ 1`.
1. `eq313_sum_leaf_S9`, `eq313_recip_leaf_S9`: LEAFs, the two estimates (3.13).
2. `FJ_poly_leaf_S9`: LEAF, multiplying out `F_J` into one Dirichlet polynomial.
3. `mv_poly_lemma6_S9`: PROVED from `Lemma6`, the moment of a Dirichlet polynomial over `χ ≠ χ₀`.
4. `coeff_sum_bound_S9`: PROVED, the coefficient step.
5. `mv_FJ_of_leaves_S9`: PROVED from `Lemma6` and the LEAFs, the statement of `mv_FJ_311_leaf_S9`;
   `mv_FJ_split_S9` wires in `zhan_lemma6_split` of SPLIT_lemma6_1122d.lean.
-/
import LeanLab.Zhan1991.Cauchy311Proof_S9
import LeanLab.Zhan1991.SPLIT_lemma6_1122d

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- `d_k(n)`, the number of ordered factorizations of `n` into `k` positive factors, of the
well-known estimates (3.13), page 266, written as the Dirichlet power `ζ^k`. -/
def dk313 (k : ℕ) : ArithmeticFunction ℕ := (ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ k

/-- LEAF: page 266, display (3.13), first estimate, cited as well known:
`Σ_{n≤x} d_k²(n) ≪ x (log x)^{c_k}` for `k ≥ 1`, here for `x ≥ 2`. Class MEDIUM. -/
theorem eq313_sum_leaf_S9 (k : ℕ) (hk : 1 ≤ k) : ∃ (c : ℕ) (K : ℝ), ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((dk313 k n : ℕ) : ℝ) ^ 2 ≤ K * x * Real.log x ^ c := by
  sorry

/-- LEAF: page 266, display (3.13), second estimate, cited as well known:
`Σ_{n≤x} d_k²(n) n⁻¹ ≪ (log x)^{c_k}` for `k ≥ 1`, here for `x ≥ 2`. Class MEDIUM. -/
theorem eq313_recip_leaf_S9 (k : ℕ) (hk : 1 ≤ k) : ∃ (c : ℕ) (K : ℝ), ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((dk313 k n : ℕ) : ℝ) ^ 2 / n ≤ K * Real.log x ^ c := by
  sorry

/-- LEAF: page 268, the display `F_i(s, χ) = Π_{j ∈ J_i} f_j(s, χ) = Σ_{n ≤ M_i} b_i(n) χ(n) n^{-s}`
with `b_i(n) ≪ d₂₀(n)`: multiplying out the Dirichlet polynomials `f_j` of (3.6), `j ∈ J`, gives
one Dirichlet polynomial supported on `n ≤ 2^{|J|} Π_{j ∈ J} N_j`, with coefficients
independent of `χ` and `s` and at most `d₂₀(n) (1 + log n)`; the factor `1 + log n` comes from
`a₁(n) = log n` and is the `L` of the proof. Class MEDIUM. -/
theorem FJ_poly_leaf_S9 (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) :
    ∃ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ (dk313 20 n : ℝ) * (1 + Real.log n)) ∧
      ∀ X : ℕ, (2 : ℝ) ^ J.card * ∏ j ∈ J, Nv j ≤ X →
        ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ),
          FJ311 Nv J χ s = ∑ n ∈ Finset.Icc 1 X, b n * χ n * (n : ℂ) ^ (-s) := by
  sorry

/-- PROVED from Lemma 6 of page 262: for a Dirichlet polynomial `Σ_{n ≤ X} b(n) χ(n) n^{-s}`,
`Σ_{χ ≠ χ₀} ∫_{T₁}^{T₁+H} |·|² dt ≪ Σ_{n ≤ X} (qH + n) |b(n)|² n⁻¹` for `H ≥ 1`, the first step
of the display on page 268. -/
theorem mv_poly_lemma6_S9 (h6 : Lemma6) : ∃ K6 : ℝ, 0 ≤ K6 ∧
    ∀ (q : ℕ) [NeZero q] (X : ℕ) (b : ℕ → ℂ) (T1 H : ℝ), 1 ≤ H →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H),
            ‖∑ n ∈ Finset.Icc 1 X, b n * χ n * (n : ℂ) ^ (-(1 / 2 + t * Complex.I))‖ ^ 2
        ≤ K6 * ∑ n ∈ Finset.Icc 1 X, ((q : ℝ) * H + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹ := by
  obtain ⟨K, hK⟩ := h6
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro q _ X b T1 H hH
  have hcont : ∀ χ : DirichletCharacter ℂ q, Continuous (fun t : ℝ =>
      ‖∑ n ∈ Finset.Icc 1 X, b n * χ n * (n : ℂ) ^ (-(1 / 2 + t * Complex.I))‖ ^ 2) := by
    intro χ
    refine Continuous.pow (Continuous.norm ?_) 2
    apply continuous_finsetSum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
  have h := hK q 0 X b H T1 (1 / 2) hH
  simp only [zero_add] at h
  have e1 : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + t * Complex.I) = 1 / 2 + t * Complex.I := by
    intro t; push_cast; ring
  have e2 : (-2 * (1 / 2 : ℝ)) = -1 := by norm_num
  simp only [e1, e2, Real.rpow_neg_one] at h
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 X, ((q : ℝ) * H + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹ := by
    apply Finset.sum_nonneg; intro n _; positivity
  calc _ ≤ ∑ χ : DirichletCharacter ℂ q, ∫ t in Set.Ioc T1 (T1 + H),
          ‖∑ n ∈ Finset.Icc 1 X, b n * χ n * (n : ℂ) ^ (-(1 / 2 + t * Complex.I))‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => MeasureTheory.integral_nonneg (fun _ => by positivity))
    _ = ∫ t in Set.Ioc T1 (T1 + H), ∑ χ : DirichletCharacter ℂ q,
          ‖∑ n ∈ Finset.Icc 1 X, b n * χ n * (n : ℂ) ^ (-(1 / 2 + t * Complex.I))‖ ^ 2 :=
        (MeasureTheory.integral_finsetSum _ (fun χ _ =>
          ((hcont χ).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)).symm
    _ = ∫ t in T1..(T1 + H), ∑ χ : DirichletCharacter ℂ q,
          ‖∑ n ∈ Finset.Icc 1 X, b n * χ n * (n : ℂ) ^ (-(1 / 2 + t * Complex.I))‖ ^ 2 :=
        (intervalIntegral.integral_of_le (by linarith)).symm
    _ ≤ K * ∑ n ∈ Finset.Icc 1 X, ((q : ℝ) * H + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹ := h
    _ ≤ max K 0 * ∑ n ∈ Finset.Icc 1 X, ((q : ℝ) * H + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hS0

/-- PROVED, page 268, the coefficient step: if `|b(n)| ≤ d(n) (1 + log n)` then
`Σ_{n ≤ X} (Q + n) |b(n)|² n⁻¹ ≤ (1 + log X)² (Q Σ_{n ≤ X} d(n)² n⁻¹ + Σ_{n ≤ X} d(n)²)`. -/
theorem coeff_sum_bound_S9 (X : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (b : ℕ → ℂ) (d : ℕ → ℝ)
    (hb : ∀ n, ‖b n‖ ≤ d n * (1 + Real.log n)) :
    ∑ n ∈ Finset.Icc 1 X, (Q + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹
      ≤ (1 + Real.log X) ^ 2 * (Q * ∑ n ∈ Finset.Icc 1 X, d n ^ 2 / n +
          ∑ n ∈ Finset.Icc 1 X, d n ^ 2) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogX : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) hnX
  have hb2 : ‖b n‖ ^ 2 ≤ d n ^ 2 * (1 + Real.log X) ^ 2 := by
    have h1 : ‖b n‖ ≤ |d n| * (1 + Real.log X) :=
      le_trans (hb n) (by
        calc d n * (1 + Real.log n) ≤ |d n| * (1 + Real.log n) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          _ ≤ |d n| * (1 + Real.log X) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
    calc ‖b n‖ ^ 2 ≤ (|d n| * (1 + Real.log X)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = d n ^ 2 * (1 + Real.log X) ^ 2 := by rw [mul_pow, sq_abs]
  have hn0 : (0 : ℝ) < n := by linarith
  have hinv : 0 ≤ (n : ℝ)⁻¹ := by positivity
  calc (Q + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹
      ≤ (Q + n) * (d n ^ 2 * (1 + Real.log X) ^ 2) * (n : ℝ)⁻¹ := by
        gcongr
    _ = (1 + Real.log X) ^ 2 * (Q * (d n ^ 2 / n) + d n ^ 2) := by
        field_simp

/-- PROVED from Lemma 6 and the three LEAFs: the mean value LEAF `mv_FJ_311_leaf_S9` of
SPLIT_prop3_311_S9.lean, page 268, lines 2 and 3, with `c₇ = c_a + c_b + 2`, where `c_a, c_b` are
the exponents of (3.13) for `k = 20`, and `N₀ = 3`. -/
theorem mv_FJ_of_leaves_S9 (h6 : Lemma6) : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (T1 H : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 ≤ H →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * ((q : ℝ) * H + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  obtain ⟨K6, hK6, hMV⟩ := mv_poly_lemma6_S9 h6
  obtain ⟨ca, Ka, hA⟩ := eq313_sum_leaf_S9 20 (by norm_num)
  obtain ⟨cb, Kb, hB⟩ := eq313_recip_leaf_S9 20 (by norm_num)
  set Ka' := max Ka 0 with hKa'
  set Kb' := max Kb 0 with hKb'
  have hKa0 : 0 ≤ Ka' := le_max_right _ _
  have hKb0 : 0 ≤ Kb' := le_max_right _ _
  set A1 : ℝ := Kb' * 31 ^ cb with hA1
  set A2 : ℝ := Ka' * 2 ^ 22 * 31 ^ ca with hA2
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  refine ⟨((ca + cb + 2 : ℕ) : ℝ), by positivity, K6 * 32 ^ 2 * (A1 + A2), 3, ?_⟩
  intro N q _ Nv J T1 H hN hC hH
  have hN3 : (3 : ℝ) ≤ N := hN
  set L := Real.log N with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  set P := ∏ j ∈ J, Nv j with hPdef
  have hcard : J.card ≤ 20 := by simpa using Finset.card_le_univ J
  have hcardc : Jᶜ.card ≤ 20 := by simpa using Finset.card_le_univ Jᶜ
  have hlow : ∀ I : Finset (Fin 20), I.card ≤ 20 → (1 / 2 : ℝ) ^ 20 ≤ ∏ j ∈ I, Nv j := by
    intro I hI
    calc (1 / 2 : ℝ) ^ 20 ≤ (1 / 2 : ℝ) ^ I.card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hI
      _ = ∏ j ∈ I, (1 / 2 : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ j ∈ I, Nv j := by gcongr with j hj; exact hC.1 j
  have hPlow : (1 / 2 : ℝ) ^ 20 ≤ P := hlow J hcard
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hPlow
  have hPN : P ≤ 2 ^ 20 * N := by
    have h1 : P * (1 / 2 : ℝ) ^ 20 ≤ P * ∏ j ∈ Jᶜ, Nv j :=
      mul_le_mul_of_nonneg_left (hlow Jᶜ hcardc) hP0.le
    rw [hPdef, Finset.prod_mul_prod_compl] at h1
    have h2 := le_trans h1 hC.2.2.1
    have : P = P * (1 / 2 : ℝ) ^ 20 * 2 ^ 20 := by ring
    rw [this]
    nlinarith
  have h2c : (2 : ℝ) ^ J.card * P ≤ 2 ^ 20 * P :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) hP0.le
  set X : ℕ := max ⌈(2 : ℝ) ^ J.card * P⌉₊ 2 with hXdef
  have hXcast : (X : ℝ) = max (⌈(2 : ℝ) ^ J.card * P⌉₊ : ℝ) 2 := by
    rw [hXdef, Nat.cast_max]; norm_num
  have hX1 : (2 : ℝ) ^ J.card * P ≤ X := by
    rw [hXcast]; exact le_trans (Nat.le_ceil _) (le_max_left _ _)
  have hX2 : (2 : ℝ) ≤ X := by rw [hXcast]; exact le_max_right _ _
  have hX3 : (X : ℝ) ≤ 2 ^ 22 * P := by
    rw [hXcast]
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 ^ J.card * P by positivity)
    apply max_le
    · nlinarith
    · nlinarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogX : Real.log X ≤ 31 * L := by
    have h1 : (X : ℝ) ≤ 2 ^ 42 * N := by nlinarith
    have h2 : Real.log X ≤ Real.log (2 ^ 42 * N) := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
    have := Real.log_two_lt_d9
    push_cast at h2
    linarith
  obtain ⟨b, hb, hF⟩ := FJ_poly_leaf_S9 Nv J
  simp only [hF X hX1 q]
  refine le_trans (hMV q X b T1 H hH) ?_
  have hQ : 0 ≤ (q : ℝ) * H := by positivity
  have hcs := coeff_sum_bound_S9 X ((q : ℝ) * H) hQ b (fun n => (dk313 20 n : ℝ)) hb
  have hAs := hA X hX2
  have hBs := hB X hX2
  rw [Nat.floor_natCast] at hAs hBs
  have hSa : ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2
      ≤ Ka' * 2 ^ 22 * P * (31 ^ ca * L ^ ca) := by
    refine le_trans hAs ?_
    calc Ka * X * Real.log X ^ ca ≤ Ka' * X * Real.log X ^ ca := by
          gcongr; exact le_max_left _ _
      _ ≤ Ka' * (2 ^ 22 * P) * (31 * L) ^ ca := by gcongr
      _ = Ka' * 2 ^ 22 * P * (31 ^ ca * L ^ ca) := by rw [mul_pow]; ring
  have hSb : ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 / n ≤ Kb' * (31 ^ cb * L ^ cb) := by
    refine le_trans hBs ?_
    calc Kb * Real.log X ^ cb ≤ Kb' * Real.log X ^ cb := by
          gcongr; exact le_max_left _ _
      _ ≤ Kb' * (31 * L) ^ cb := by gcongr
      _ = Kb' * (31 ^ cb * L ^ cb) := by rw [mul_pow]
  set u := L ^ (ca + cb) with hu
  have hua : L ^ ca ≤ u := pow_le_pow_right₀ hL (by omega)
  have hub : L ^ cb ≤ u := pow_le_pow_right₀ hL (by omega)
  have hlog1 : (1 + Real.log X) ^ 2 ≤ 32 ^ 2 * L ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hLc : L ^ (((ca + cb + 2 : ℕ) : ℝ)) = L ^ 2 * u := by
    rw [Real.rpow_natCast, hu, ← pow_add]; ring_nf
  rw [hLc]
  have hinner : (q : ℝ) * H * ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 / n +
      ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 ≤ (A1 + A2) * ((q : ℝ) * H + P) * u := by
    have e1 : (q : ℝ) * H * ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 / n
        ≤ (q : ℝ) * H * (A1 * u) := by
      refine mul_le_mul_of_nonneg_left (le_trans hSb ?_) hQ
      rw [hA1, mul_assoc]; gcongr
    have e2 : ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 ≤ A2 * P * u := by
      refine le_trans hSa ?_
      rw [hA2]
      calc Ka' * 2 ^ 22 * P * (31 ^ ca * L ^ ca) = Ka' * 2 ^ 22 * 31 ^ ca * P * L ^ ca := by ring
        _ ≤ Ka' * 2 ^ 22 * 31 ^ ca * P * u := by gcongr
    have hu0 : 0 ≤ u := by positivity
    have e3 : 0 ≤ A1 * P * u := by positivity
    have e4 : 0 ≤ A2 * ((q : ℝ) * H) * u := by positivity
    nlinarith
  have hin0 : 0 ≤ (q : ℝ) * H * ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 / n +
      ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 := by
    apply add_nonneg
    · apply mul_nonneg hQ; apply Finset.sum_nonneg; intro n _; positivity
    · apply Finset.sum_nonneg; intro n _; positivity
  calc K6 * ∑ n ∈ Finset.Icc 1 X, ((q : ℝ) * H + n) * ‖b n‖ ^ 2 * (n : ℝ)⁻¹
      ≤ K6 * ((1 + Real.log X) ^ 2 *
          ((q : ℝ) * H * ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2 / n +
            ∑ n ∈ Finset.Icc 1 X, ((dk313 20 n : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hK6
    _ ≤ K6 * ((32 ^ 2 * L ^ 2) * ((A1 + A2) * ((q : ℝ) * H + P) * u)) := by
        gcongr
    _ = K6 * 32 ^ 2 * (A1 + A2) * ((q : ℝ) * H + P) * (L ^ 2 * u) := by ring

/-- PROVED from the three LEAFs above and the Lemma 6 split of SPLIT_lemma6_1122d.lean: the
statement of `mv_FJ_311_leaf_S9`. -/
theorem mv_FJ_split_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (T1 H : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 ≤ H →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * ((q : ℝ) * H + ∏ j ∈ J, Nv j) * Real.log N ^ c7 :=
  mv_FJ_of_leaves_S9 zhan_lemma6_split

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.mv_poly_lemma6_S9
#print axioms LeanLab.Zhan1991.coeff_sum_bound_S9
#print axioms LeanLab.Zhan1991.mv_FJ_of_leaves_S9
#print axioms LeanLab.Zhan1991.mv_FJ_split_S9
