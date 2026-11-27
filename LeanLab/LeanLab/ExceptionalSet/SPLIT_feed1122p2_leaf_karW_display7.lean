import LeanLab.ExceptionalSet.KaracubaSplit

/-!
Split of `leaf_karW_display7` of `LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_karW_display8`,
burst-20261122 wave 13, session S132. A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971),
p. 246 bottom to p. 247, displays (6) and (7).

Pieces, with `M = P2 = karP2 c1 n P`, `B_s = f^{(s)}(a)/s!`, `ρ = min(c1/3, c3, c4)`.
* `karW_eC_norm`, `‖e(x)‖ = 1`, proved.
* `karW_frak_trivial`, the trivial bound `𝔖_s ≤ (2kM^s+1)²` used on p. 247 for `s ∉ T`, proved.
* `leaf_karW_display7_factor`, display (6) and Lemma 3 for one `s ∈ T`:
  `𝔖_s ≤ 2^{8k} 30k² 9n log P (M+1)^{2s} P^{-ρ s}`. LEAF, HARD.
* `leaf_karW_display7_of_leaves`, the exact statement of `leaf_karW_display7`, proved from the
  pieces: the product over `s ∈ [1, n]` of the per factor bounds, `Σ_{s ≤ n} 2s = n(n+1)` and
  `2^{8kn} ≤ 2^{8k²}` since `n ≤ k`.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- `‖e(x)‖ = 1`. -/
theorem karW_eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The trivial bound for `𝔖_s`, Karacuba p. 247, used for `s ∉ T`: each inner sum has at most
`2K+1` terms of modulus one. -/
theorem karW_frak_trivial (K : ℕ) (b : ℝ) :
    ∑ μ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ‖∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), eC (b * (t : ℝ) * (μ : ℝ))‖
      ≤ ((2 * K + 1 : ℕ) : ℝ) ^ 2 := by
  have hcard : ((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ) = ((2 * K + 1 : ℕ) : ℝ) := by
    rw [Int.card_Icc]
    congr 1
    omega
  calc ∑ μ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ‖∑ t ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), eC (b * (t : ℝ) * (μ : ℝ))‖
      ≤ ∑ _μ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro μ _
        refine (norm_sum_le _ _).trans ?_
        simp [karW_eC_norm]
    _ = ((2 * K + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring

/-- The geometric sum over the symmetric range, with the regularized convention
at an integer phase used on p. 246. -/
theorem karW_sym_geom_task3687 (L : ℕ) (γ : ℝ) :
    ‖∑ x ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), eC (γ * (x : ℝ))‖ ≤
      if Int.fract γ = 0 then ((2 * L + 1 : ℕ) : ℝ) else
        min ((2 * L + 1 : ℕ) : ℝ)
          (1 / min (Int.fract γ) (1 - Int.fract γ)) := by
  have heq : ∑ m ∈ Finset.Icc 1 (2 * L + 1), eC (γ * (m : ℝ)) =
      ∑ x ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), eC (γ * ((L : ℝ) + 1)) * eC (γ * (x : ℝ)) := by
    apply Finset.sum_bij (fun (m : ℕ) _ => (m : ℤ) - (L + 1))
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m _ m' _ h
      omega
    · intro x hx
      refine ⟨(x + (L + 1)).toNat, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hx ⊢
        omega
      · simp only [Finset.mem_Icc] at hx
        omega
    · intro m _
      unfold eC
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  have h := LeanLab.ExceptionalSet.Decomp538a.geometric_sum_bound (2 * L + 1) γ
  rw [heq, ← Finset.mul_sum, norm_mul, karW_eC_norm, one_mul] at h
  exact h

/-- The choice `n >= n0` gives the power saving needed for the third ratio. -/
private theorem karW_n0_cube_task3687 {c1 c2 c4 : ℝ} {n : ℕ}
    (hd : c2 + c4 < c1) (hn : karN0 c1 c2 c4 ≤ n) :
    1 / ((n : ℝ) ^ 2 * (n + 1)) ≤ c1 - (c2 + c4) := by
  set d := c1 - (c2 + c4) with hdd
  have hd0 : 0 < d := by rw [hdd]; linarith
  have hcube : 1 / d ^ ((1 : ℝ) / 3) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hr0 : 0 < d ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hd0 _
  have h1 : 1 ≤ (n : ℝ) * d ^ ((1 : ℝ) / 3) := (div_le_iff₀ hr0).mp hcube
  have h3 : 1 ≤ ((n : ℝ) * d ^ ((1 : ℝ) / 3)) ^ 3 := one_le_pow₀ h1
  have hd3 : (d ^ ((1 : ℝ) / 3)) ^ 3 = d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; norm_num
  rw [mul_pow, hd3] at h3
  have hn1 : (1 : ℝ) ≤ n := by
    have : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 * (n + 1) := by positivity
  rw [div_le_iff₀ hpos]
  have : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * (n + 1) := by nlinarith
  nlinarith

/-- The arithmetic envelope for the three reciprocal terms. -/
private theorem karW_factor_sum_le_task3687
    {q X lq Lg p1 p3 p4 pr nn : ℝ} (s : ℕ)
    (hq : 1 / q ≤ 2 * p3) (hX : X⁻¹ ≤ (2 : ℝ) ^ s * p1)
    (hXX : (X ^ 2)⁻¹ * q ≤ (4 : ℝ) ^ s * p4)
    (hlq0 : 0 ≤ lq) (hlq : lq ≤ nn * Lg) (hLg : 1 ≤ Lg) (hnn : 1 ≤ nn)
    (h1 : p1 ≤ pr) (h3 : p3 ≤ pr) (h4 : p4 ≤ pr) (hp1 : 0 ≤ p1) (hp4 : 0 ≤ p4)
    (hX0 : 0 ≤ X⁻¹) (hXX0 : 0 ≤ (X ^ 2)⁻¹ * q) :
    1 / q + X⁻¹ * lq + (X ^ 2)⁻¹ * q * lq ≤
      (16 : ℝ) ^ s * (9 * nn) * Lg * pr := by
  have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have h4s : (4 : ℝ) ^ s = (2 : ℝ) ^ s * (2 : ℝ) ^ s := by rw [← mul_pow]; norm_num
  have h16s : (16 : ℝ) ^ s = (4 : ℝ) ^ s * (4 : ℝ) ^ s := by rw [← mul_pow]; norm_num
  have h4s1 : (1 : ℝ) ≤ (4 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have hpr : 0 ≤ pr := le_trans hp1 h1
  have hnL : 1 ≤ nn * Lg := by nlinarith
  have hA : 1 / q ≤ 2 * pr * (nn * Lg) := by nlinarith
  have hB : X⁻¹ * lq ≤ (2 : ℝ) ^ s * pr * (nn * Lg) := by
    have : X⁻¹ ≤ (2 : ℝ) ^ s * pr := le_trans hX (by nlinarith)
    calc X⁻¹ * lq ≤ ((2 : ℝ) ^ s * pr) * (nn * Lg) :=
          mul_le_mul this hlq hlq0 (le_trans hX0 this)
      _ = _ := by ring
  have hC : (X ^ 2)⁻¹ * q * lq ≤ (4 : ℝ) ^ s * pr * (nn * Lg) := by
    have : (X ^ 2)⁻¹ * q ≤ (4 : ℝ) ^ s * pr := le_trans hXX (by nlinarith)
    calc (X ^ 2)⁻¹ * q * lq ≤ ((4 : ℝ) ^ s * pr) * (nn * Lg) :=
          mul_le_mul this hlq hlq0 (le_trans hXX0 this)
      _ = _ := by ring
  have hsum : 2 + (2 : ℝ) ^ s + (4 : ℝ) ^ s ≤ 9 * (16 : ℝ) ^ s := by
    rw [h16s, h4s] at *; nlinarith
  have hfin : (2 + (2 : ℝ) ^ s + (4 : ℝ) ^ s) * (pr * (nn * Lg)) ≤
      9 * (16 : ℝ) ^ s * (pr * (nn * Lg)) :=
    mul_le_mul_of_nonneg_right hsum (by positivity)
  nlinarith

/-- The factor estimate used by the explicit symmetric sums.  This is the same
reciprocal-sum calculation as `Decomp538a.karacuba_factor_thirty`, with the
constant enlarged to `30 * 2^(4k)`.  The enlargement removes the paper's
`k >= 7` threshold and is paid for by the `2^(8k)` allowance in the target. -/
theorem karacuba_factor_thirty_general (k s : ℕ) (X : ℝ) (q : ℕ)
    (hk : 2 ≤ k) (hs : s ≤ k) (hX : 1 ≤ X) (hq : 1 ≤ q) :
    6 * (2 * (k : ℝ) * X + 1 + (q : ℝ) * Real.log q) *
        ((2 * (k : ℝ) * X + 1) / q + 1) ≤
      30 * (2 : ℝ) ^ (8 * k - 4 * s) * (k : ℝ) ^ 2 * X ^ 2 *
        (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hXR : (0 : ℝ) ≤ X := by linarith
  have he0 : 0 ≤ 8 * k - 4 * s := by omega
  by_cases hk7 : 7 ≤ k
  · have h := LeanLab.ExceptionalSet.Decomp538a.karacuba_factor_thirty
        (k : ℝ) X q (by exact_mod_cast hk7) hX (by exact_mod_cast hq)
    calc 6 * (2 * (k : ℝ) * X + 1 + (q : ℝ) * Real.log q) *
          ((2 * (k : ℝ) * X + 1) / q + 1) ≤
        30 * (k : ℝ) ^ 2 * X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := h
      _ ≤ 30 * (2 : ℝ) ^ (8 * k - 4 * s) * (k : ℝ) ^ 2 * X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := by
        have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (8 * k - 4 * s) := one_le_pow₀ (by norm_num)
        have hmul : (30 : ℝ) ≤ 30 * (2 : ℝ) ^ (8 * k - 4 * s) := by nlinarith
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
        have hF0 : (0 : ℝ) ≤ 1 / q + X⁻¹ * Real.log q +
            (X ^ 2)⁻¹ * q * Real.log q := by
          have hXinv : (0 : ℝ) ≤ X⁻¹ := inv_nonneg.mpr (by positivity)
          have hX2inv : (0 : ℝ) ≤ (X ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
          positivity
        have hscaled : 30 * (k : ℝ) ^ 2 * X ^ 2 *
            (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) ≤
            30 * (2 : ℝ) ^ (8 * k - 4 * s) * (k : ℝ) ^ 2 * X ^ 2 *
            (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := by
          have hm := mul_le_mul_of_nonneg_left hmul
            (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * X ^ 2 *
              (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q))
          nlinarith [hm]
        exact hscaled
  · have hk67 : k ≤ 6 := by omega
    have hU : 2 * (k : ℝ) * X + 1 ≤ 14 * X + 1 := by
      have hkX : (k : ℝ) * X ≤ 6 * X := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk67) hXR
      linarith
    have hfac1 : 2 * (k : ℝ) * X + 1 + (q : ℝ) * Real.log q ≤
        14 * X + 1 + (q : ℝ) * Real.log q := by linarith
    have hfac2 : (2 * (k : ℝ) * X + 1) / q + 1 ≤ (14 * X + 1) / q + 1 := by
      rw [add_le_add_iff_right]
      exact (div_le_div_iff_of_pos_right hqR).2 (by linarith)
    have hfac1s : 6 * (2 * (k : ℝ) * X + 1 + (q : ℝ) * Real.log q) ≤
        6 * (14 * X + 1 + (q : ℝ) * Real.log q) :=
      mul_le_mul_of_nonneg_left hfac1 (by positivity)
    have hLHS : 6 * (2 * (k : ℝ) * X + 1 + (q : ℝ) * Real.log q) *
          ((2 * (k : ℝ) * X + 1) / q + 1) ≤
        6 * (14 * X + 1 + (q : ℝ) * Real.log q) *
          ((14 * X + 1) / q + 1) :=
      mul_le_mul hfac1s hfac2 (by positivity) (by positivity)
    have h7 := LeanLab.ExceptionalSet.Decomp538a.karacuba_factor_thirty
      (7 : ℝ) X q (by norm_num) hX (by exact_mod_cast hq)
    have hcoef : (49 : ℝ) ≤ (2 : ℝ) ^ (8 * k - 4 * s) * (k : ℝ) ^ 2 := by
      have he4 : 4 ≤ 8 * k - 4 * s := by omega
      have hp16 : (16 : ℝ) ≤ (2 : ℝ) ^ (8 * k - 4 * s) := by
        calc 16 = (2 : ℝ) ^ 4 := by norm_num
          _ ≤ (2 : ℝ) ^ (8 * k - 4 * s) := pow_le_pow_right₀ (by norm_num) he4
      have hk2sq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
        have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith [sq_nonneg (k : ℝ)]
      nlinarith
    have h7' : 6 * (14 * X + 1 + (q : ℝ) * Real.log q) *
          ((14 * X + 1) / q + 1) ≤ 30 * 49 * X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := by
      convert h7 using 1 <;> ring
    have hX2 : (0 : ℝ) ≤ X ^ 2 := by positivity
    have hqlog : (0 : ℝ) ≤ (q : ℝ) * Real.log q := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      exact mul_nonneg (by positivity) (Real.log_nonneg hq1)
    have hF0 : (0 : ℝ) ≤ 1 / q + X⁻¹ * Real.log q +
        (X ^ 2)⁻¹ * q * Real.log q := by
      have hXinv : (0 : ℝ) ≤ X⁻¹ := inv_nonneg.mpr (by positivity)
      have hX2inv : (0 : ℝ) ≤ (X ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
      positivity
    have hcoefmul : 49 * (X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q)) ≤
        ((2 : ℝ) ^ (8 * k - 4 * s) * (k : ℝ) ^ 2) * (X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q)) := by
      have hm := mul_le_mul_of_nonneg_left hcoef
        (by positivity : (0 : ℝ) ≤ X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q))
      convert hm using 1 <;> ring
    calc 6 * (2 * (k : ℝ) * X + 1 + (q : ℝ) * Real.log q) *
          ((2 * (k : ℝ) * X + 1) / q + 1) ≤
        6 * (14 * X + 1 + (q : ℝ) * Real.log q) *
          ((14 * X + 1) / q + 1) := hLHS
      _ ≤ 30 * 49 * X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := h7'
      _ ≤ 30 * (2 : ℝ) ^ (8 * k - 4 * s) * (k : ℝ) ^ 2 * X ^ 2 *
          (1 / q + X⁻¹ * Real.log q + (X ^ 2)⁻¹ * q * Real.log q) := by
        have hmain := mul_le_mul_of_nonneg_left hcoefmul (by norm_num : (0 : ℝ) ≤ 30)
        nlinarith

/-- LEAF: display (6) and Lemma 3 for one index `s ∈ T`, Karacuba p. 246 bottom to p. 247, class
HARD. With `M = P2`, `B_s = f^{(s)}(a)/s!`, `ρ = min(c1/3, c3, c4)` and `k ≥ n(n+1)/4`:
`𝔖_s ≤ 2^{8k} 30k² 9n log P (P2+1)^{2s} P^{-ρ s}`. Steps: the geometric sum bound
`≤ min(2kP2^s+1, 1/(2⟨B_s μ⟩))`; the approximation `B_s = 1/Q_s + θ_s/Q_s²` with
`P^{c2 s} - 1 ≤ Q_s ≤ P^{c2 s}` from `KarHyp` and Lemma 3; the bounds `Q_s^{-1} ≤ 2P^{-c3 s}`,
`P2^{-1} ≤ 2P^{-c1/3}`, `P2^{-2s}Q_s ≤ 2^{2s}P^{-c4 s}` from `n ≥ karN0`. The factor `2^{8k}`
covers the powers of `2` the paper drops. -/
theorem leaf_karW_display7_factor (h3 : KarLemma3) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          n * (n + 1) ≤ 4 * k → ∀ s ∈ T,
              ∑ μ ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                ‖∑ t ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                  eC (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) * (t : ℝ) * (μ : ℝ))‖
            ≤ 2 ^ (8 * k) * (30 * (k : ℝ) ^ 2) * (9 * (n : ℝ)) *
              Real.log (P : ℝ) * ((karP2 c1 n P : ℝ) + 1) ^ (2 * s) *
              (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (s : ℝ))) := by
  sorry

/-- `Σ_{s=1}^n 2s = n(n+1)`. -/
theorem karW_sum_two_s (n : ℕ) : ∑ s ∈ Finset.Icc 1 n, 2 * s = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- The exact statement of `leaf_karW_display7`, from the pieces. -/
theorem leaf_karW_display7_of_leaves (h3 : KarLemma3) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ cc0 : ℝ, 0 < cc0 ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a k : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          n * (n + 1) ≤ 4 * k →
          ∏ s ∈ Finset.Icc 1 n,
              ∑ μ ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                ‖∑ t ∈ Finset.Icc (-((k * karP2 c1 n P ^ s : ℕ) : ℤ)) ((k * karP2 c1 n P ^ s : ℕ) : ℤ),
                  eC (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) * (t : ℝ) * (μ : ℝ))‖
            ≤ 2 ^ (8 * k ^ 2) * (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
              (Real.log (P : ℝ)) ^ n * ((karP2 c1 n P : ℝ) + 1) ^ (n * (n + 1)) *
              (P : ℝ) ^ (-(min (c1 / 3) (min c3 c4) * (∑ s ∈ T, (s : ℝ)))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨cc1, hcc1, H⟩ :=
    leaf_karW_display7_factor h3 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  refine ⟨max cc1 1, by positivity, ?_⟩
  intro N P n f T a k hP hn hn0 hbig hH ha haP hnk
  have hbig1 : Real.exp (cc1 * (n : ℝ) ^ 2) ≤ P :=
    le_trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      hbig
  have hlogP : (n : ℝ) ^ 2 ≤ Real.log P := by
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
    rw [Real.le_log_iff_exp_le hP0]
    refine le_trans (Real.exp_le_exp.2 ?_) hbig
    have : (1 : ℝ) ≤ max cc1 1 := le_max_right _ _
    nlinarith [sq_nonneg (n : ℝ)]
  have hT : T ⊆ Finset.Icc 2 n := hH.2.2.1
  set M : ℕ := karP2 c1 n P with hM
  set ρ : ℝ := min (c1 / 3) (min c3 c4) with hρ
  set A : ℝ := 2 ^ (8 * k) * (30 * (k : ℝ) ^ 2) * (9 * (n : ℝ)) * Real.log (P : ℝ) with hA
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : 1 ≤ k := by nlinarith
  have hA1 : 9 * (k : ℝ) ^ 2 ≤ A := by
    have h2 : (1 : ℝ) ≤ 2 ^ (8 * k) := one_le_pow₀ (by norm_num)
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hL : 1 ≤ 9 * (n : ℝ) * Real.log P := by nlinarith
    have : 30 * (k : ℝ) ^ 2 ≤ A := by
      rw [hA]
      have h0 : 0 ≤ 30 * (k : ℝ) ^ 2 := by positivity
      calc 30 * (k : ℝ) ^ 2 = 1 * (30 * (k : ℝ) ^ 2) * 1 := by ring
        _ ≤ 2 ^ (8 * k) * (30 * (k : ℝ) ^ 2) * (9 * (n : ℝ) * Real.log P) := by gcongr
        _ = _ := by ring
    nlinarith [sq_nonneg (k : ℝ)]
  set g : ℕ → ℝ := fun s => A * ((M : ℝ) + 1) ^ (2 * s) *
    (if s ∈ T then (P : ℝ) ^ (-(ρ * (s : ℝ))) else 1) with hg
  have hfac : ∀ s ∈ Finset.Icc 1 n,
      0 ≤ ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
                ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
                  eC (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) * (t : ℝ) * (μ : ℝ))‖ :=
    fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hle : ∀ s ∈ Finset.Icc 1 n,
      ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
                ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
                  eC (iteratedDeriv s f (a : ℝ) / (s.factorial : ℝ) * (t : ℝ) * (μ : ℝ))‖
        ≤ g s := by
    intro s hs
    by_cases hsT : s ∈ T
    · have := H N P n f T a k hP hn hn0 hbig1 hH ha haP hnk s hsT
      simp only [hg, if_pos hsT]
      rw [hA]; simpa [hM, hρ, mul_assoc] using this
    · simp only [hg, if_neg hsT, mul_one]
      refine (karW_frak_trivial _ _).trans ?_
      have hb : ((2 * (k * M ^ s) + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) * ((M : ℝ) + 1) ^ s := by
        push_cast
        have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have hMs : (M : ℝ) ^ s ≤ ((M : ℝ) + 1) ^ s := pow_le_pow_left₀ (by positivity) (by linarith) s
        have hMs1 : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ s := one_le_pow₀ (by linarith [M.cast_nonneg (α := ℝ)])
        nlinarith
      calc ((2 * (k * M ^ s) + 1 : ℕ) : ℝ) ^ 2 ≤ (3 * (k : ℝ) * ((M : ℝ) + 1) ^ s) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hb 2
        _ = 9 * (k : ℝ) ^ 2 * ((M : ℝ) + 1) ^ (2 * s) := by ring
        _ ≤ A * ((M : ℝ) + 1) ^ (2 * s) := by gcongr
  have hprod := Finset.prod_le_prod₀ hfac hle
  refine hprod.trans ?_
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hTI : Finset.Icc 1 n ∩ T = T := by
    apply Finset.inter_eq_right.2
    intro x hx
    have := hT hx
    simp only [Finset.mem_Icc] at this ⊢
    omega
  have hite : ∏ s ∈ Finset.Icc 1 n, (if s ∈ T then (P : ℝ) ^ (-(ρ * (s : ℝ))) else 1)
      = (P : ℝ) ^ (-(ρ * (∑ s ∈ T, (s : ℝ)))) := by
    rw [Finset.prod_ite_mem, hTI, ← Real.rpow_sum_of_pos hP0, Finset.mul_sum,
      Finset.sum_neg_distrib]
  have hpowsum : ∏ s ∈ Finset.Icc 1 n, ((M : ℝ) + 1) ^ (2 * s) = ((M : ℝ) + 1) ^ (n * (n + 1)) := by
    rw [Finset.prod_pow_eq_pow_sum, karW_sum_two_s]
  have hprodg : ∏ s ∈ Finset.Icc 1 n, g s
      = A ^ n * ((M : ℝ) + 1) ^ (n * (n + 1)) * (P : ℝ) ^ (-(ρ * (∑ s ∈ T, (s : ℝ)))) := by
    simp only [hg]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hite, hpowsum, Finset.prod_const,
      Nat.card_Icc, Nat.add_sub_cancel]
  rw [hprodg]
  have hnk' : n ≤ k := by nlinarith
  have h2 : ((2 : ℝ) ^ (8 * k)) ^ n ≤ 2 ^ (8 * k ^ 2) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  have hAn : A ^ n = ((2 : ℝ) ^ (8 * k)) ^ n * ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
      (Real.log (P : ℝ)) ^ n) := by
    rw [hA]; simp only [mul_pow]; ring
  have hlog0 : 0 ≤ Real.log (P : ℝ) := le_trans (by positivity) hlogP
  have hR0 : 0 ≤ (30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (Real.log (P : ℝ)) ^ n := by
    positivity
  have hQ0 : 0 ≤ ((M : ℝ) + 1) ^ (n * (n + 1)) * (P : ℝ) ^ (-(ρ * (∑ s ∈ T, (s : ℝ)))) := by
    have := Real.rpow_nonneg hP0.le (-(ρ * (∑ s ∈ T, (s : ℝ))))
    positivity
  calc A ^ n * ((M : ℝ) + 1) ^ (n * (n + 1)) * (P : ℝ) ^ (-(ρ * (∑ s ∈ T, (s : ℝ))))
      = ((2 : ℝ) ^ (8 * k)) ^ n * ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
          (Real.log (P : ℝ)) ^ n) *
          (((M : ℝ) + 1) ^ (n * (n + 1)) * (P : ℝ) ^ (-(ρ * (∑ s ∈ T, (s : ℝ))))) := by
        rw [hAn]; ring
    _ ≤ 2 ^ (8 * k ^ 2) * ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n *
          (Real.log (P : ℝ)) ^ n) *
          (((M : ℝ) + 1) ^ (n * (n + 1)) * (P : ℝ) ^ (-(ρ * (∑ s ∈ T, (s : ℝ))))) := by
        gcongr
    _ = _ := by ring

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
