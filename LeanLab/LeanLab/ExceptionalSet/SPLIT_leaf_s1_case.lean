/-
Split of the sealed statement `leaf_s1_case` of `LeanLab.ExceptionalSet.KaracubaSplit`, the
case `S = {1}` of the lab class in the source's Theorem 1, stated there as `LeafS1Case`.

The step is cut into three leaves:
* `leaf_s1_deriv_sign`: the two sided bound `N ^ (-θ) ≤ |f'| ≤ N ^ (-Θ)` makes `f'`
  continuous and nowhere zero on `[N, 2N]`, so it keeps one sign there and the phase is
  monotone.
* `leaf_s1_monotone_saving`: for `N ≥ N₀` the sum over `(N, 2N]` saves a fixed power
  `N ^ (c / k ^ 2)`: `k - 1` Weyl differences convert `|f^(k) / k!| ≤ N ^ (-Θ₀ k)` into
  cancellation, and the part of the sum where the linear term dominates is handled by the
  first derivative test against `|f'| ≥ N ^ (-θ)`, which is the weaker bound since `θ > Θ₀`.
  This carries the analytic content of the step.
* `leaf_s1_small_N_boundary`: below `N₀` the trivial bound `‖Σ‖ ≤ N` and
  `N ^ (c / k ^ 2) ≤ N₀ ^ (1 / 9)` for `c ≤ 1`, `k ≥ 3` and `N < N₀` give the same shape,
  with only the constant `B` depending on `N₀`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- LEAF. Step 2 of the split, the analytic saving for large `N`: for `f` of class `C^k` on a
neighbourhood of `[N, 2N]`, `k ≥ 3`, `δ k ≤ 1`, the bound `|f^(k) / k!| ≤ N ^ (-Θ₀ k)`, the
two sided bound on `f'`, and one sign for `f'` on the interval, the sum over `(N, 2N]` is
`O(N ^ (1 - c / k ^ 2))` with `B, c` depending on `θ, Θ, Θ₀, δ` only, not on `N`, `f` or
`k`. -/
theorem leaf_s1_monotone_saving :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < N₀ ∧
        ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ (f : ℝ → ℝ) (k : ℕ),
        3 ≤ k → (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
          |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) →
        δ * k ≤ 1 →
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
          (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
          |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
        ((∀ x ∈ Set.Icc (N : ℝ) (2 * N), 0 < iteratedDeriv 1 f x) ∨
          (∀ x ∈ Set.Icc (N : ℝ) (2 * N), iteratedDeriv 1 f x < 0)) →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  sorry

/-- LEAF. Step 3 of the split, the range below `N₀`: for `0 < c ≤ 1` the trivial bound
`‖Σ_{n ∈ (N, 2N]} e(f n)‖ ≤ N` and `N ^ (c / k ^ 2) ≤ N₀ ^ (1 / 9)`, valid for `1 ≤ N < N₀`
and `3 ≤ k`, give the same inequality with a constant `B` that absorbs `N₀`. No cancellation
is used here. -/
theorem leaf_s1_small_N_boundary :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∀ c N₀ : ℝ, 0 < c → c ≤ 1 → 0 < N₀ →
        ∃ B : ℝ, 0 < B ∧
          ∀ N : ℕ, 1 ≤ N → (N : ℝ) < N₀ → ∀ (f : ℝ → ℝ) (k : ℕ),
          3 ≤ k → (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
          (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
            |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) →
          δ * k ≤ 1 →
          (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
            (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
            |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
          ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1 c N₀ hc0 hc1 hN₀0
  refine ⟨N₀ ^ (1 / 9 : ℝ), Real.rpow_pos_of_pos hN₀0 _, ?_⟩
  intro N hN1 hNlt f k hk3 hsm hder hδk hf'
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have htriv : ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖
        ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖eC (f n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Ioc N (2 * N), (1 : ℝ) :=
          Finset.sum_congr rfl (fun n _ => norm_eC _)
      _ = ((Finset.Ioc N (2 * N)).card : ℝ) := by simp
      _ = (N : ℝ) := by
          have hcard : (Finset.Ioc N (2 * N)).card = N := by
            simp
            omega
          rw [hcard]
  refine htriv.trans ?_
  have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hexp : c / (k : ℝ) ^ 2 ≤ 1 / 9 := by
    have h1 : c / (k : ℝ) ^ 2 ≤ 1 / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hc1 hk2pos.le
    have h2 : 1 / (k : ℝ) ^ 2 ≤ 1 / 9 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9)
      have hk3r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
      nlinarith
    linarith
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hkey : (N : ℝ) ^ (c / (k : ℝ) ^ 2) ≤ N₀ ^ (1 / 9 : ℝ) := by
    calc (N : ℝ) ^ (c / (k : ℝ) ^ 2) ≤ (N : ℝ) ^ (1 / 9 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1r hexp
      _ ≤ N₀ ^ (1 / 9 : ℝ) := Real.rpow_le_rpow hNpos.le hNlt.le (by norm_num)
  have hsplit : (N : ℝ) =
      (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) * (N : ℝ) ^ (c / (k : ℝ) ^ 2) := by
    rw [← Real.rpow_add hNpos]
    rw [show 1 - c / (k : ℝ) ^ 2 + c / (k : ℝ) ^ 2 = 1 by ring, Real.rpow_one]
  calc (N : ℝ) = (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) * (N : ℝ) ^ (c / (k : ℝ) ^ 2) := hsplit
    _ ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) * N₀ ^ (1 / 9 : ℝ) :=
        mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hNpos.le _)
    _ = N₀ ^ (1 / 9 : ℝ) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by ring

/-- LEAF. Step 1 of the split, one sign for `f'`: from `N ≥ 1`, `k ≥ 3`, `C^k` on a
neighbourhood of `[N, 2N]` and the two sided bound on `f'`, the derivative is continuous on
`[N, 2N]` and never `0` there, so it has one sign on the whole interval and the phase carries
no stationary point. -/
theorem leaf_s1_deriv_sign :
    ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ) (θ Θ : ℝ), 3 ≤ k → 0 < Θ → Θ < θ →
      (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
      (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
        (N : ℝ) ^ (-(θ * (1 : ℕ))) ≤ |iteratedDeriv 1 f x / (1 : ℕ).factorial| ∧
        |iteratedDeriv 1 f x / (1 : ℕ).factorial| ≤ (N : ℝ) ^ (-(Θ * (1 : ℕ)))) →
      ((∀ x ∈ Set.Icc (N : ℝ) (2 * N), 0 < iteratedDeriv 1 f x) ∨
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N), iteratedDeriv 1 f x < 0)) := by
  intro N hN f k θ Θ hk3 hΘ hΘθ hsm hf'
  obtain ⟨U, hUop, hUIcc, hC⟩ := hsm
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkont : ContinuousOn (iteratedDeriv 1 f) (Set.Icc (N : ℝ) (2 * N)) := by
    have hle : ((1 : ℕ) : WithTop ℕ∞) ≤ ((k : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : (1 : ℕ) ≤ k)
    have h1 : ContinuousOn (iteratedDerivWithin 1 f U) U :=
      hC.continuousOn_iteratedDerivWithin hle hUop.uniqueDiffOn
    refine (h1.congr ?_).mono hUIcc
    exact (iteratedDerivWithin_of_isOpen (𝕜 := ℝ) (F := ℝ) (f := f) (n := 1) hUop).symm
  have hne : ∀ x ∈ Set.Icc (N : ℝ) (2 * N), iteratedDeriv 1 f x ≠ 0 := by
    intro x hx h0
    have h1 := (hf' x hx).1
    rw [h0] at h1
    simp only [zero_div, abs_zero] at h1
    have hp : (0 : ℝ) < (N : ℝ) ^ (-(θ * (1 : ℕ))) := Real.rpow_pos_of_pos hNpos _
    linarith
  have hNmem : (N : ℝ) ∈ Set.Icc (N : ℝ) (2 * N) := by
    refine ⟨le_refl _, ?_⟩
    have : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    linarith
  rcases lt_or_gt_of_ne (hne N hNmem) with hneg | hpos
  · right
    intro x hx
    rcases lt_or_gt_of_ne (hne x hx) with hxneg | hxpos
    · exact hxneg
    · exfalso
      have hcont : ContinuousOn (iteratedDeriv 1 f) (Set.uIcc (N : ℝ) x) :=
        hkont.mono ((Set.ordConnected_Icc).uIcc_subset hNmem hx)
      have hmem0 : (0 : ℝ) ∈ Set.uIcc (iteratedDeriv 1 f (N : ℝ)) (iteratedDeriv 1 f x) :=
        Set.mem_uIcc.mpr (Or.inl ⟨hneg.le, hxpos.le⟩)
      have himg := intermediate_value_uIcc hcont hmem0
      rw [Set.mem_image] at himg
      obtain ⟨c, hc, hcz⟩ := himg
      exact hne c ((Set.ordConnected_Icc).uIcc_subset hNmem hx hc) hcz
  · left
    intro x hx
    rcases lt_or_gt_of_ne (hne x hx) with hxneg | hxpos
    · exfalso
      have hcont : ContinuousOn (iteratedDeriv 1 f) (Set.uIcc (N : ℝ) x) :=
        hkont.mono ((Set.ordConnected_Icc).uIcc_subset hNmem hx)
      have hmem0 : (0 : ℝ) ∈ Set.uIcc (iteratedDeriv 1 f (N : ℝ)) (iteratedDeriv 1 f x) :=
        Set.mem_uIcc.mpr (Or.inr ⟨hxneg.le, hpos.le⟩)
      have himg := intermediate_value_uIcc hcont hmem0
      rw [Set.mem_image] at himg
      obtain ⟨c, hc, hcz⟩ := himg
      exact hne c ((Set.ordConnected_Icc).uIcc_subset hNmem hx hc) hcz
    · exact hxpos

/-- The step `LeafS1Case` from the three leaves: the sign of `f'` from `leaf_s1_deriv_sign`,
the saving for `N ≥ N₀` from `leaf_s1_monotone_saving` with the exponent `c₁` weakened to
`min c₁ 1`, and the range `N < N₀` from `leaf_s1_small_N_boundary`. No `sorry`. -/
theorem leaf_s1_case_split : LeafS1Case := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₁, c₁, N₀, hB₁, hc₁, hN₀, hbig⟩ :=
    leaf_s1_monotone_saving θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₂, _, hsmall⟩ :=
    leaf_s1_small_N_boundary θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1 (min c₁ 1) N₀
      (lt_min hc₁ one_pos) (min_le_right _ _) hN₀
  refine ⟨max B₁ B₂, min c₁ 1, lt_of_lt_of_le hB₁ (le_max_left _ _), lt_min hc₁ one_pos, ?_⟩
  intro N hN f k hk3 hsm hder hδk hf'
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  rcases lt_or_ge (N : ℝ) N₀ with hlt | hge
  · refine (hsmall N hN hlt f k hk3 hsm hder hδk hf').trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right B₁ B₂)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · have hsgn := leaf_s1_deriv_sign N hN f k θ Θ hk3 hΘ0 hΘθ hsm hf'
    refine (hbig N hge f k hk3 hsm hder hδk hf' hsgn).trans ?_
    refine mul_le_mul (le_max_left B₁ B₂) ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (le_trans hB₁.le (le_max_left _ _))
    apply Real.rpow_le_rpow_of_exponent_le hNr
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hmin : min c₁ 1 / (k : ℝ) ^ 2 ≤ c₁ / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) hk2.le
    linarith

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
