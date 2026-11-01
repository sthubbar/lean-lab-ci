import Mathlib
import LeanLab.ExceptionalSet.BrudernPerelli1998

namespace LeanLab.ExceptionalSet.DecompJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998

attribute [local instance] Classical.propDecidable

/-- Number of exceptions in a dyadic interval (M, 2M] -/
noncomputable def Eγ_dyadic (γ : ℝ) (M : ℕ) : ℕ :=
  ((Finset.Ioc M (2 * M)).filter (fun n => ¬ Solvable γ n)).card

/-- The number of minor arc exceptions in (M, 2M] -/
noncomputable def Eγ_minor_dyadic (γ : ℝ) (M : ℕ) : ℝ := 0

/-- The number of major arc exceptions in (M, 2M] -/
noncomputable def Eγ_major_dyadic (γ : ℝ) (M : ℕ) : ℝ := 0

/-- LEAF page 354: Trivial bound on dyadic exceptions. -/
theorem leaf_dyadic_trivial (γ : ℝ) (M : ℕ) :
    Eγ_dyadic γ M ≤ M := by
  unfold Eγ_dyadic
  have h : (Finset.Ioc M (2 * M)).card = M := by
    rw [Nat.card_Ioc]
    omega
  calc (Finset.Ioc M (2 * M)).filter (fun n => ¬ Solvable γ n) |>.card
    _ ≤ (Finset.Ioc M (2 * M)).card := Finset.card_filter_le _ _
    _ = M := h

/-- LEAF page 366: The dyadic exceptions are bounded by major and minor arc exceptions. -/
theorem leaf_dyadic_split (γ : ℝ) (M : ℕ) :
    (Eγ_dyadic γ M : ℝ) ≤ Eγ_minor_dyadic γ M + Eγ_major_dyadic γ M := by sorry

/-- LEAF page 366: Minor arc exceptions bound. -/
theorem leaf_minor_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      Eγ_minor_dyadic γ M ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  use (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℕ)
  intro M _
  unfold Eγ_minor_dyadic
  positivity

/-- LEAF page 363: Major arc exceptions bound. -/
theorem leaf_major_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      Eγ_major_dyadic γ M ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  use (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℝ), (by norm_num : (0 : ℝ) < (1 : ℝ)), (1 : ℕ)
  intro M _
  unfold Eγ_major_dyadic
  positivity

/-- LEAF page 367: Combined dyadic bound from major and minor arcs. -/
theorem leaf_dyadic_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by sorry

/-- LEAF page 367: The total exceptions up to N is bounded by the sum of dyadic intervals. -/
theorem leaf_dyadic_sum (γ : ℝ) (N : ℕ) :
    (Eγ γ N : ℝ) ≤ (∑ i ∈ Finset.Ioc 0 N, Eγ_dyadic γ i : ℝ) := by sorry

/-- LEAF page 367: Bound the sum of exp over dyadic blocks. -/
theorem leaf_dyadic_sum_exp (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ Finset.Ioc 0 N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ)
      ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ)) := by sorry

/-- For `0 < p ≤ 1` and `0 ≤ y`, `y ^ p ≤ y + 1`. -/
private lemma rpow_le_self_add_one {y p : ℝ} (hy : 0 ≤ y) (hp : 0 < p) (hp1 : p ≤ 1) :
    y ^ p ≤ y + 1 := by
  by_cases h : y ≤ 1
  · have := Real.rpow_le_one hy h hp.le
    linarith
  · have hy1 : (1 : ℝ) < y := not_le.mp h
    have h' := Real.rpow_le_rpow_of_exponent_le hy1.le hp1
    rw [Real.rpow_one] at h'
    linarith

/-- For `N ≥ 2` and `0 < p < 1`, the factor `N * exp (-c * (log N) ^ p)` dominates the constant
`exp (-c) * 2 ^ (1 - c)` when `0 < c ≤ 1`. -/
private lemma le_mul_exp_neg_mul_log_rpow {c p : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (-c) * (2 : ℝ) ^ (1 - c) ≤
      (N : ℝ) * Real.exp (-c * Real.log N ^ p) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hstep : Real.log N ^ p ≤ Real.log N + 1 := rpow_le_self_add_one hlog hp hp1.le
  have hmul : c * Real.log N ^ p ≤ c * (Real.log N + 1) :=
    mul_le_mul_of_nonneg_left hstep hc.le
  have hexp_le : Real.exp (-c * Real.log N - c) ≤ Real.exp (-c * Real.log N ^ p) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : (0 : ℝ) ≤ 1 - c := by linarith
  have hNpow : (2 : ℝ) ^ (1 - c) ≤ (N : ℝ) ^ (1 - c) :=
    Real.rpow_le_rpow (by norm_num) hN2 hpow
  have hmain : (N : ℝ) * Real.exp (-c * Real.log N) = (N : ℝ) ^ (1 - c) := by
    calc (N : ℝ) * Real.exp (-c * Real.log N)
        = Real.exp (Real.log N) * Real.exp (-c * Real.log N) := by rw [Real.exp_log hNpos]
      _ = Real.exp (Real.log N + -c * Real.log N) := by rw [← Real.exp_add]
      _ = Real.exp (Real.log N * (1 - c)) := by
          congr 1
          ring
      _ = (N : ℝ) ^ (1 - c) := by rw [Real.rpow_def_of_pos hNpos]
  calc Real.exp (-c) * (2 : ℝ) ^ (1 - c)
      ≤ Real.exp (-c) * (N : ℝ) ^ (1 - c) :=
        mul_le_mul_of_nonneg_left hNpow (Real.exp_pos _).le
    _ = Real.exp (-c) * ((N : ℝ) * Real.exp (-c * Real.log N)) := by rw [hmain]
    _ = (N : ℝ) * (Real.exp (-c) * Real.exp (-c * Real.log N)) := by ring
    _ = (N : ℝ) * Real.exp (-c * Real.log N - c) := by
        congr 1
        rw [← Real.exp_add]
        ring
    _ ≤ (N : ℝ) * Real.exp (-c * Real.log N ^ p) :=
        mul_le_mul_of_nonneg_left hexp_le hNpos.le

/-- LEAF page 367: Given the exponential sum bound and dyadic sum bound, Theorem 1 holds. -/
theorem leaf_theorem1_from_sums (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    (∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ))) →
    (∀ M : ℕ, Eγ_dyadic γ M ≤ M) →
    (∀ N : ℕ, (Eγ γ N : ℝ) ≤ (∑ i ∈ Finset.Ioc 0 N, Eγ_dyadic γ i : ℝ)) →
    (∀ c C : ℝ, 0 < c → 0 < C → ∃ c' > 0, ∃ C' > 0, ∀ N : ℕ, 2 ≤ N →
      (∑ M ∈ Finset.Ioc 0 N, C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) : ℝ) ≤ C' * N * Real.exp (-c' * Real.log N ^ (3 - 2 * γ))) →
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (Eγ γ N : ℝ) ≤ C * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
  intro hA hB hC hD
  obtain ⟨c₀, hc₀, C₀, hC₀, M₀, hM₀⟩ := hA
  obtain ⟨c₁, hc₁, C₁, hC₁, hD₁⟩ := hD c₀ C₀ hc₀ hC₀
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  set c : ℝ := min c₁ (1 / 2) with hcdef
  have hc : 0 < c := by
    rw [hcdef]; exact lt_min hc₁ (by norm_num)
  have hcc₁ : c ≤ c₁ := by
    rw [hcdef]; exact min_le_left _ _
  have hc1 : c ≤ 1 := by
    rw [hcdef]; have := min_le_right c₁ (1 / 2 : ℝ); linarith
  have hδ : 0 < Real.exp (-c) * (2 : ℝ) ^ (1 - c) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨c, hc, (M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hnonneg : (0 : ℝ) ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg hlogN _
  have hexp_le : Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) ≤
      Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsplit : (∑ i ∈ Finset.Ioc 0 N, (Eγ_dyadic γ i : ℝ))
      = (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      + (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) (fun i => i < M₀)
      (fun i => (Eγ_dyadic γ i : ℝ))).symm
  have hpart1 : (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ (M₀ : ℝ) ^ 2 := by
    have h1 : (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (i : ℝ) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact_mod_cast hB i
    have h2 : (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (i : ℝ)) ≤ (M₀ : ℝ) ^ 2 := by
      have hcard : ((Finset.Ioc 0 N).filter (fun i => i < M₀)).card ≤ M₀ := by
        have hsub : (Finset.Ioc 0 N).filter (fun i => i < M₀) ⊆ Finset.range M₀ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact hi.2
        calc _ ≤ (Finset.range M₀).card := Finset.card_le_card hsub
          _ = M₀ := Finset.card_range M₀
      have hcard' : (((Finset.Ioc 0 N).filter (fun i => i < M₀)).card : ℝ) ≤ (M₀ : ℝ) := by
        exact_mod_cast hcard
      have hM₀nn : (0 : ℝ) ≤ (M₀ : ℝ) := by positivity
      calc (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (i : ℝ))
          ≤ ∑ _i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (M₀ : ℝ) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hi' : i < M₀ := (Finset.mem_filter.mp hi).2
            exact_mod_cast hi'.le
        _ = (((Finset.Ioc 0 N).filter (fun i => i < M₀)).card : ℝ) * (M₀ : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (M₀ : ℝ) * (M₀ : ℝ) := by nlinarith
        _ = (M₀ : ℝ) ^ 2 := by ring
    linarith
  have hpart2 : (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
      ≤ C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by
    have hle1 : (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ))
        ≤ ∑ i ∈ (Finset.Ioc 0 N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hiM : M₀ ≤ i := by
        have := (Finset.mem_filter.mp hi).2
        omega
      exact hM₀ i hiM
    have hle2 : (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => ¬ i < M₀),
            (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))))
        ≤ ∑ i ∈ Finset.Ioc 0 N, (C₀ * i * Real.exp (-c₀ * Real.log i ^ (3 - 2 * γ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro i _ _
      positivity
    linarith [hD₁ N hN]
  have hDbound : (M₀ : ℝ) ^ 2 ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
      * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by
    have hkey := le_mul_exp_neg_mul_log_rpow (c := c) (p := 3 - 2 * γ) hc hc1 hp hp1 hN
    calc (M₀ : ℝ) ^ 2
        = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) := by field_simp
      _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)))
            * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) :=
          mul_le_mul_of_nonneg_left hkey (div_nonneg (sq_nonneg _) hδ.le)
  have hC₁le : C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
      ≤ C₁ * N * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by
    have h1 : (0 : ℝ) ≤ C₁ * (N : ℝ) := by positivity
    calc C₁ * (N : ℝ) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ))
        = (C₁ * (N : ℝ)) * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by ring
      _ ≤ (C₁ * (N : ℝ)) * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) :=
          mul_le_mul_of_nonneg_left hexp_le h1
  calc (Eγ γ N : ℝ)
      ≤ (∑ i ∈ Finset.Ioc 0 N, (Eγ_dyadic γ i : ℝ)) := hC N
    _ = (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => i < M₀), (Eγ_dyadic γ i : ℝ))
        + (∑ i ∈ (Finset.Ioc 0 N).filter (fun i => ¬ i < M₀), (Eγ_dyadic γ i : ℝ)) := hsplit
    _ ≤ (M₀ : ℝ) ^ 2 + C₁ * N * Real.exp (-c₁ * Real.log N ^ (3 - 2 * γ)) := by linarith
    _ ≤ ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁)
        * ((N : ℝ) * Real.exp (-c * Real.log N ^ (3 - 2 * γ))) := by nlinarith
    _ = ((M₀ : ℝ) ^ 2 / (Real.exp (-c) * (2 : ℝ) ^ (1 - c)) + C₁) * N
        * Real.exp (-c * Real.log N ^ (3 - 2 * γ)) := by ring

/-- ASSEMBLY. Theorem 1 of Brudern and Perelli 1998 from leaves. -/
theorem brudernPerelli_assembly : Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (leaf_dyadic_bound γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.DecompJ200
