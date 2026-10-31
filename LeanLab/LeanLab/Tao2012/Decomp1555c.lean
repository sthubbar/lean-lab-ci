/-
Tao 2012, arXiv 1201.6656v4, Math. Comp. 83 (2014). Unit U-1555, run 20261026T1219Z-15327.

Proposition 4.10, the mesoscopic L² estimate, Section 4, assembled from the leaves of
Decomp1555a and Decomp1555b:
  ∫_0^1 |S_{η,q}(x,α)|² |D_H(α)|² dα ≤ (1 + ε) 8 H² x M²,  q = √x^♯, H ≥ 100, 0 ≤ η ≤ M,
with ε of (4.15). The sup bound M stands for ‖η‖_∞, so the paper's form is the case M = ‖η‖_∞;
the paper normalises ‖η‖_∞ = 1 and restores it by homogeneity. H is a natural number here; the
paper allows real H ≥ 10², where D_H sums over h ≤ ⌊H⌋ and the right side increases with H.

Section 8 of the paper uses this proposition in the proof of Proposition 8.4, Prop84.lean.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean
kernel.
-/
import LeanLab.Tao2012.Decomp1555b

namespace LeanLab.Tao2012.Decomp1555

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

/-- LEAF. Unit U-1555. Tao 2012, Proposition 4.10 for `1 ≤ x < 4`, where `q = √x^♯ = 1` and
`n = 2` is allowed, so the parity step of the proof does not apply: the bound
`∫ |S|² |D_H|² ≤ (1 + ε) 8 H² x M²` still holds, as `∑_n c_n ≤ M (log 2 + log 3)` and
`∫ |S|² |D_H|² ≤ H² (∑_n c_n)² ≤ 3.3 H² M² ≤ 8 H² x M²`. -/
lemma plancherel_bound (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (H : ℕ) :
    ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, corr η q x h h' = ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), coef η q x n * coef η q x m * (∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, if n + h = m + h' then (1:ℝ) else 0) := by
  unfold corr
  have h1 : ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ) =
    ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ) := by
    calc ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ)
      _ = ∑ h ∈ Icc 1 H, ∑ n ∈ range (⌊x⌋₊ + 1), ∑ h' ∈ Icc 1 H, ∑ m ∈ range (⌊x⌋₊ + 1), (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ) := by
        apply sum_congr rfl
        intro h _
        rw [sum_comm]
      _ = ∑ n ∈ range (⌊x⌋₊ + 1), ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, ∑ m ∈ range (⌊x⌋₊ + 1), (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ) := by
        rw [sum_comm]
      _ = ∑ n ∈ range (⌊x⌋₊ + 1), ∑ h ∈ Icc 1 H, ∑ m ∈ range (⌊x⌋₊ + 1), ∑ h' ∈ Icc 1 H, (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ) := by
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro h _
        rw [sum_comm]
      _ = ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, (if n + h = m + h' then coef η q x n * coef η q x m else 0 : ℝ) := by
        apply sum_congr rfl
        intro n _
        rw [sum_comm]
  rw [h1]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  rw [mul_sum]
  apply sum_congr rfl
  intro h' _
  split_ifs
  · ring
  · ring

lemma bound_indicator (n m h : ℕ) (H : ℕ) : ∑ h' ∈ Icc 1 H, (if n + h = m + h' then (1:ℝ) else 0) ≤ 1 := by
  have : ∑ h' ∈ Icc 1 H, (if n + h = m + h' then (1:ℝ) else 0) = ∑ h' ∈ (Icc 1 H).filter (fun h' => n + h = m + h'), (1:ℝ) := by
    rw [sum_filter]
  rw [this, sum_const, nsmul_eq_mul, mul_one]
  have h_card : ((Icc 1 H).filter (fun h' => n + h = m + h')).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    rw [mem_filter] at ha hb
    linarith [ha.2, hb.2]
  exact_mod_cast h_card

lemma sum_indicator_bound (n m : ℕ) (H : ℕ) : ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, (if n + h = m + h' then (1:ℝ) else 0) ≤ H := by
  have step1 : ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, (if n + h = m + h' then (1:ℝ) else 0) ≤ ∑ h ∈ Icc 1 H, (1:ℝ) := by
    apply sum_le_sum
    intro h _
    exact bound_indicator n m h H
  have step2 : ∑ h ∈ Icc 1 H, (1:ℝ) = H := by simp
  linarith

lemma coef_nonneg (η : ℝ → ℝ) (hη0 : ∀ t, 0 ≤ η t) (q : ℕ) (x : ℝ) (n : ℕ) : 0 ≤ coef η q x n := by
  unfold coef
  have h1 : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ if n.Coprime q then (1:ℝ) else 0 := by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have h3 : 0 ≤ η (n / x) := hη0 _
  positivity

lemma plancherel_le (η : ℝ → ℝ) (q : ℕ) (x : ℝ) (H : ℕ) (hη0 : ∀ t, 0 ≤ η t) :
    ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, corr η q x h h' ≤ (∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n)^2 * H := by
  have h1 := plancherel_bound η q x H
  rw [h1]
  have h2 : ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), coef η q x n * coef η q x m * (∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, if n + h = m + h' then (1:ℝ) else 0) ≤
    ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), coef η q x n * coef η q x m * H := by
    apply sum_le_sum
    intro n _
    apply sum_le_sum
    intro m _
    have h_nonneg1 : 0 ≤ coef η q x n := coef_nonneg η hη0 q x n
    have h_nonneg2 : 0 ≤ coef η q x m := coef_nonneg η hη0 q x m
    have h_nonneg : 0 ≤ coef η q x n * coef η q x m := mul_nonneg h_nonneg1 h_nonneg2
    have h_ind := sum_indicator_bound n m H
    exact mul_le_mul_of_nonneg_left h_ind h_nonneg
  have h3 : ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), coef η q x n * coef η q x m * H = (∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n)^2 * H := by
    have h_sq : (∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n)^2 = ∑ n ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range (⌊x⌋₊ + 1), coef η q x n * coef η q x m := by
      rw [sq, sum_mul]
      apply sum_congr rfl
      intro n _
      rw [mul_sum]
    rw [h_sq]
    rw [sum_mul]
    apply sum_congr rfl
    intro n _
    rw [sum_mul]
  linarith

lemma coef_bound' (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (n : ℕ) (q : ℕ) : coef η q x n ≤ (Λ n : ℝ) * M := by
  unfold coef
  have h1 : η (n / x) ≤ M := hηM _
  have h2 : (if n.Coprime q then (1:ℝ) else 0) ≤ 1 := by
    split_ifs
    · exact le_rfl
    · exact zero_le_one
  have step1 : (Λ n : ℝ) * (if n.Coprime q then 1 else 0) * η (n / x) ≤ (Λ n : ℝ) * 1 * η (n / x) := by
    have h1_sub : 0 ≤ η (n / x) := hη0 _
    have h2_sub : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have h3_sub : (if n.Coprime q then (1:ℝ) else 0) ≤ 1 := by
      split_ifs
      · exact le_rfl
      · exact zero_le_one
    gcongr
  calc (Λ n : ℝ) * (if n.Coprime q then 1 else 0) * η (n / x)
    _ ≤ (Λ n : ℝ) * 1 * η (n / x) := step1
    _ = (Λ n : ℝ) * η (n / x) := by ring
    _ ≤ (Λ n : ℝ) * M := by
      have h2_sub : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      gcongr

lemma sum_eval_4 : ∑ n ∈ range 4, (Λ n : ℝ) = log 2 + log 3 := by
  have step1 : (range 4 : Finset ℕ) = {0, 1, 2, 3} := rfl
  rw [step1]
  have h0 : (Λ (0:ℕ) : ℝ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply]
    have : ¬ IsPrimePow (0:ℕ) := not_isPrimePow_zero
    simp [this]
  have h1 : (Λ (1:ℕ) : ℝ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply]
    have : ¬ IsPrimePow (1:ℕ) := not_isPrimePow_one
    simp [this]
  have h2 : (Λ (2:ℕ) : ℝ) = log 2 := by
    have : (2:ℕ).Prime := Nat.prime_two
    exact ArithmeticFunction.vonMangoldt_apply_prime this
  have h3 : (Λ (3:ℕ) : ℝ) = log 3 := by
    have : (3:ℕ).Prime := Nat.prime_three
    exact ArithmeticFunction.vonMangoldt_apply_prime this
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_insert (by decide)]
  rw [sum_singleton]
  rw [h0, h1, h2, h3]
  ring

lemma log_sq_bound : (log 2 + log 3)^2 ≤ 3.3 := by
  have hlog2 : log 2 ≤ 0.7 := by
    have : log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  have hlog3 : log 3 ≤ 1.1 := by
    have : log 3 < 1.0986122888 := Real.log_three_lt_d9
    linarith
  have hsum : log 2 + log 3 ≤ 1.8 := by linarith
  have hpos : (0:ℝ) ≤ log 2 + log 3 := by
    have h1 : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ log 3 := log_nonneg (by norm_num)
    linarith
  have hsq : (log 2 + log 3)^2 ≤ (1.8:ℝ)^2 := by
    exact sq_le_sq.mpr (by
      have h1 : |log 2 + log 3| = log 2 + log 3 := abs_of_nonneg hpos
      have h2 : |(1.8:ℝ)| = 1.8 := abs_of_nonneg (by norm_num)
      rw [h1, h2]
      exact hsum
    )
  have h_eval : (1.8:ℝ)^2 = 3.24 := by norm_num
  linarith

theorem prop4_10_small_x (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (hx1 : 1 ≤ x) (hx4 : x < 4) {H : ℕ} (hH : 100 ≤ H) :
    meso η (qx x) x H ≤ (1 + eps x H) * (8 * (H : ℝ) ^ 2 * x * M ^ 2) := by
  have qx_eq_1 : qx x = 1 := by
    unfold qx
    have hfloor : ⌊√x⌋₊ = 1 := by
      have h1 : (1:ℝ) ≤ √x := Real.one_le_sqrt.mpr hx1
      have h2 : √x < (2:ℝ) := by
        have hd : (0:ℝ) < 2 := by norm_num
        have : √x < 2 ↔ x < 2^2 := Real.sqrt_lt' hd
        rw [this]
        linarith
      apply (Nat.floor_eq_iff (by positivity)).mpr
      constructor
      · exact_mod_cast h1
      · exact_mod_cast h2
    rw [hfloor]
    exact rfl

  have sum_coef_bound : ∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n ≤ M * (log 2 + log 3) := by
    have h_bound : ∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n ≤ ∑ n ∈ range (⌊x⌋₊ + 1), (Λ n : ℝ) * M := by
      apply sum_le_sum
      intro i _
      apply coef_bound' η hη0 hηM i (qx x)
    have h_bound2 : ∑ n ∈ range (⌊x⌋₊ + 1), (Λ n : ℝ) * M = (∑ n ∈ range (⌊x⌋₊ + 1), (Λ n : ℝ)) * M := by rw [sum_mul]
    rw [h_bound2] at h_bound

    have hfloor_x : ⌊x⌋₊ + 1 ≤ 4 := by
      have h0 : 0 ≤ x := by linarith
      have hlt : ⌊x⌋₊ < 4 := (Nat.floor_lt h0).mpr hx4
      omega
    have h_range : range (⌊x⌋₊ + 1) ⊆ range 4 := by
      intro a ha
      rw [mem_range] at ha ⊢
      omega
    have h_sum : ∑ n ∈ range (⌊x⌋₊ + 1), (Λ n : ℝ) ≤ ∑ n ∈ range 4, (Λ n : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg h_range
      intro i _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
    have h_sum_eval : ∑ n ∈ range 4, (Λ n : ℝ) = log 2 + log 3 := sum_eval_4

    have hM_nonneg : 0 ≤ M := by
      have : 0 ≤ η 0 := hη0 0
      have : η 0 ≤ M := hηM 0
      linarith

    calc ∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n
      _ ≤ (∑ n ∈ range (⌊x⌋₊ + 1), (Λ n : ℝ)) * M := h_bound
      _ ≤ (∑ n ∈ range 4, (Λ n : ℝ)) * M := mul_le_mul_of_nonneg_right h_sum hM_nonneg
      _ = (log 2 + log 3) * M := by rw [h_sum_eval]
      _ = M * (log 2 + log 3) := by ring

  have sum_c_sq_bound : (∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n)^2 ≤ (M * (log 2 + log 3))^2 := by
    have h_nonneg : 0 ≤ ∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n := by
      apply sum_nonneg
      intro i _
      exact coef_nonneg η hη0 (qx x) x i
    have h_nonneg2 : 0 ≤ M * (log 2 + log 3) := by
      have hM_nonneg : 0 ≤ M := by
        have : 0 ≤ η 0 := hη0 0
        have : η 0 ≤ M := hηM 0
        linarith
      have hlog2 : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
      have hlog3 : (0:ℝ) ≤ log 3 := log_nonneg (by norm_num)
      positivity
    exact sq_le_sq.mpr (by
      have h1 : |∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n| = ∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n := abs_of_nonneg h_nonneg
      have h2 : |M * (log 2 + log 3)| = M * (log 2 + log 3) := abs_of_nonneg h_nonneg2
      rw [h1, h2]
      exact sum_coef_bound
    )

  have sum_c_sq_bound2 : (∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n)^2 ≤ M^2 * 3.3 := by
    have h_sq_eq : (M * (log 2 + log 3))^2 = M^2 * (log 2 + log 3)^2 := by ring
    have h1 : (∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n)^2 ≤ M^2 * (log 2 + log 3)^2 := by
      linarith
    have hlog_sq : (log 2 + log 3)^2 ≤ 3.3 := log_sq_bound
    have hM2 : 0 ≤ M^2 := sq_nonneg M
    have h_mul := mul_le_mul_of_nonneg_left hlog_sq hM2
    linarith

  have H_pos : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)

  have H_eq : meso η (qx x) x H = ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, corr η (qx x) x h h' := plancherel_corr η (qx x) x H
  have h_bound1 : ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, corr η (qx x) x h h' ≤ (∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n)^2 * H := plancherel_le η (qx x) x H hη0

  have h_bound2 : (∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n)^2 * H ≤ M^2 * 3.3 * H := by
    apply mul_le_mul_of_nonneg_right sum_c_sq_bound2 H_pos.le

  have h_bound3 : M^2 * 3.3 * H ≤ 8 * (H : ℝ)^2 * x * M^2 := by
    have hH2 : (H : ℝ) ≤ (H : ℝ)^2 := by
      have : (100:ℝ) ≤ H := by exact_mod_cast hH
      nlinarith
    have hx : 1 ≤ x := hx1
    have hc : (3.3:ℝ) ≤ 8 := by norm_num
    have hm1 : 3.3 * (H:ℝ) ≤ 8 * (H:ℝ)^2 * x := by
      calc 3.3 * (H:ℝ) ≤ 8 * (H:ℝ) := mul_le_mul_of_nonneg_right hc H_pos.le
        _ ≤ 8 * (H:ℝ)^2 := mul_le_mul_of_nonneg_left hH2 (by norm_num)
        _ ≤ 8 * (H:ℝ)^2 * x := by
          have h1 : 8 * (H:ℝ)^2 = 8 * (H:ℝ)^2 * 1 := by ring
          have h2 : 8 * (H:ℝ)^2 * 1 ≤ 8 * (H:ℝ)^2 * x := by
            have h_nonneg : 0 ≤ 8 * (H:ℝ)^2 := by positivity
            exact mul_le_mul_of_nonneg_left hx h_nonneg
          linarith
    have hM2 : 0 ≤ M^2 := sq_nonneg M
    have hm2 := mul_le_mul_of_nonneg_right hm1 hM2
    linarith

  have h_eps_nonneg : 0 ≤ eps x H := by
    have hlogx : 0 ≤ log x := log_nonneg hx1
    have hHpos : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    unfold eps
    have term1_nonneg : 0 ≤ 0.13 * log x / H := div_nonneg (mul_nonneg (by norm_num) hlogx) hHpos.le
    have ht1 : (200:ℝ) ≤ 2 * H := by
      have : (100:ℝ) ≤ H := by exact_mod_cast hH
      linarith
    have ht2 : (1:ℝ) ≤ log (2 * H) := by
      calc (1:ℝ) ≤ log 200 := by
            have h_e_le : exp 1 ≤ 200 := by
              have : exp 1 < 3 := by
                have h_d9 : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
                linarith
              linarith
            exact (Real.le_log_iff_exp_le (by norm_num)).mpr h_e_le
        _ ≤ log (2 * H) := log_le_log (by norm_num) ht1
    have h_log_log : 0 ≤ log (log (2 * H)) := log_nonneg ht2
    have gRS_nonneg : 0 ≤ gRS (log (log (2 * H))) := by
      unfold gRS
      have h1 : 0 ≤ exp eulerMascheroniConstant * log (log (2 * H)) := mul_nonneg (exp_pos _).le h_log_log
      have h2 : 0 ≤ 2.507 / log (log (2 * H)) := div_nonneg (by norm_num) h_log_log
      exact add_nonneg h1 h2
    have h_log_9H : 0 ≤ log (9 * H) := by
      have : (1:ℝ) ≤ 9 * H := by
        have : (100:ℝ) ≤ H := by exact_mod_cast hH
        linarith
      exact log_nonneg this
    have term2_nonneg : 0 ≤ gRS (log (log (2 * H))) * log (9 * H) / (2 * H) := by
      apply div_nonneg
      · exact mul_nonneg gRS_nonneg h_log_9H
      · linarith
    linarith

  calc meso η (qx x) x H
    _ = ∑ h ∈ Icc 1 H, ∑ h' ∈ Icc 1 H, corr η (qx x) x h h' := H_eq
    _ ≤ (∑ n ∈ range (⌊x⌋₊ + 1), coef η (qx x) x n)^2 * H := h_bound1
    _ ≤ M^2 * 3.3 * H := h_bound2
    _ ≤ 8 * (H:ℝ)^2 * x * M^2 := h_bound3
    _ ≤ (1 + eps x H) * (8 * (H:ℝ)^2 * x * M^2) := by
      have h1 : 8 * (H:ℝ)^2 * x * M^2 = 1 * (8 * (H:ℝ)^2 * x * M^2) := by ring
      have h2 : 1 ≤ 1 + eps x H := by linarith
      have h_nonneg : 0 ≤ 8 * (H:ℝ)^2 * x * M^2 := by
        have hH2 : 0 ≤ (H:ℝ)^2 := sq_nonneg _
        have hx_pos : 0 ≤ x := by linarith
        have hM2 : 0 ≤ M^2 := sq_nonneg _
        positivity
      have h3 : 1 * (8 * (H:ℝ)^2 * x * M^2) ≤ (1 + eps x H) * (8 * (H:ℝ)^2 * x * M^2) := mul_le_mul_of_nonneg_right h2 h_nonneg
      linarith

/-- The sum over `h` for fixed `h'`, split at `h = h'`: at most
`1.04 M² x log x + 8 𝔖₂ M² x G(h')`. CONDITIONAL ON the leaves of `diag_le` and `offdiag_le`. -/
theorem row_le (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (hx : 4 ≤ x) {H h' : ℕ} (hh' : h' ∈ Icc 1 H) :
    ∑ h ∈ Icc 1 H, corr η (qx x) x h h' ≤
      1.04 * M ^ 2 * x * log x + 8 * twinConst * M ^ 2 * x * G H h' := by
  rw [← add_sum_erase _ _ hh']
  have hd := diag_le η hη0 hηM (qx x) (by linarith : (1 : ℝ) ≤ x) h'
  have ho : ∑ h ∈ (Icc 1 H).erase h', corr η (qx x) x h h' ≤
      8 * twinConst * M ^ 2 * x * G H h' := by
    unfold G
    rw [mul_sum]
    apply sum_le_sum
    intro h hh
    have hne : h ≠ h' := ne_of_mem_erase hh
    have := offdiag_le η hη0 hηM hx hne
    split_ifs at this ⊢
    · exact this
    · simpa using this
  linarith

/-- Proposition 4.10 of Tao 2012, mesoscopic L² estimate, for `x ≥ 4`: with `q = √x^♯`,
`H ≥ 100` and `0 ≤ η ≤ M`, `∫_0^1 |S_{η,q}(x,α)|² |D_H(α)|² dα ≤ (1 + ε) 8 H² x M²`, `ε` as in
(4.15). CONDITIONAL ON the leaves `plancherel_corr`, `corr_diag_le`, `sum_coef_le_psi`,
`corr_offdiag_le`, `twinCount_neg`, `swap_le`, `count_multiples`, `f_euler_partial`,
`twinConst_pos`, `f_le_phi`, `rs_exception`, `gRS_mono`, `small_m`, `loglog27`,
`sum_odd_half`, `log_9H`, and the cited Rosser-Schoenfeld Theorems 12 and 15, Siebert 1976
and Ramaré's Lemma 3.5. `coef_support_odd_prime` is a helper leaf for `corr_offdiag_le`. -/
theorem prop4_10_large_x (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (hx : 4 ≤ x) {H : ℕ} (hH : 100 ≤ H) :
    meso η (qx x) x H ≤ (1 + eps x H) * (8 * (H : ℝ) ^ 2 * x * M ^ 2) := by
  have hHr : (100 : ℝ) ≤ H := by exact_mod_cast hH
  have hx0 : 0 < x := by linarith
  have hT := twinConst_pos
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  rw [plancherel_corr, sum_comm]
  set F := ∑ n ∈ Icc 1 H, f n
  have hrow : ∀ h' ∈ Icc 1 H, ∑ h ∈ Icc 1 H, corr η (qx x) x h h' ≤
      1.04 * M ^ 2 * x * log x + 8 * M ^ 2 * x * H + 8 * M ^ 2 * x * (twinConst * F) := by
    intro h' hh'
    have h1 := row_le η hη0 hηM hx hh'
    have h2 := G_le hh'
    have hc : 0 ≤ 8 * twinConst * M ^ 2 * x := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hc
    have h4 : 8 * twinConst * M ^ 2 * x * (H / twinConst + F) =
        8 * M ^ 2 * x * H + 8 * M ^ 2 * x * (twinConst * F) := by
      field_simp
    linarith
  have hsum := sum_le_sum hrow
  have hcard : ((Icc 1 H).card : ℝ) = H := by simp
  rw [sum_const, nsmul_eq_mul, hcard] at hsum
  have h2nd := second_term_le hH
  have hc8 : 0 ≤ 8 * M ^ 2 * x := by positivity
  have h5 := mul_le_mul_of_nonneg_left h2nd hc8
  have hHpos : (0 : ℝ) < H := by linarith
  have hgoal : (1 + eps x H) * (8 * (H : ℝ) ^ 2 * x * M ^ 2) =
      H * (1.04 * M ^ 2 * x * log x + 8 * M ^ 2 * x * H +
        8 * M ^ 2 * x * (gRS (log (log (2 * (H : ℝ)))) * log (9 * H) / 2)) := by
    unfold eps
    field_simp
    ring
  rw [hgoal]
  have hHnn : (0 : ℝ) ≤ H := hHpos.le
  calc _ ≤ (H : ℝ) * (1.04 * M ^ 2 * x * log x + 8 * M ^ 2 * x * H +
        8 * M ^ 2 * x * (twinConst * F)) := hsum
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hHnn
        linarith

/-- Proposition 4.10 of Tao 2012, mesoscopic L² estimate, Section 4, for all `x ≥ 1`:
`∫_0^1 |S_{η,q}(x,α)|² |D_H(α)|² dα ≤ (1 + ε) 8 H² x M²` with `q = √x^♯`, `H ≥ 100`,
`0 ≤ η ≤ M`. CONDITIONAL ON the leaves listed at `prop4_10_large_x` and `prop4_10_small_x`. -/
theorem prop4_10 (η : ℝ → ℝ) {M : ℝ} (hη0 : ∀ t, 0 ≤ η t) (hηM : ∀ t, η t ≤ M)
    {x : ℝ} (hx : 1 ≤ x) {H : ℕ} (hH : 100 ≤ H) :
    meso η (qx x) x H ≤ (1 + eps x H) * (8 * (H : ℝ) ^ 2 * x * M ^ 2) := by
  rcases lt_or_ge x 4 with h4 | h4
  · exact prop4_10_small_x η hη0 hηM hx h4 hH
  · exact prop4_10_large_x η hη0 hηM h4 hH

end LeanLab.Tao2012.Decomp1555
