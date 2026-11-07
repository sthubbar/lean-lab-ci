import LeanLab.ChenDoubleSieve.Decomp366c

/-!
Supply the F4 prime sum limit through a fixed continuous kernel.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
The remaining partial summation input has no moving residual level,
no coprimality condition and no totient weight.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task366
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-! ## Private helpers for the leaf below

These are private helpers for `continuous_prime_triangle`: the explicit Mertens
block estimate, the cell and block partial summation bounds, the slice lemmas
and the continuity of the residual weight. -/

private theorem cell_mass_error {N y w : ℕ} (hN : 2 ≤ N) (hy : 2 ≤ y) (hyw : y ≤ w) :
    |(∑ p ∈ (Finset.Ioc y w).filter Nat.Prime, 1 / (p : ℝ)) -
        ∫ t in (Real.log (y : ℝ) / Real.log (N : ℝ))..
          (Real.log (w : ℝ) / Real.log (N : ℝ)), 1 / t|
      ≤ 22 / Real.log (y : ℝ) := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hy0 : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hw0 : 0 < Real.log (w : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hα : 0 < Real.log (y : ℝ) / Real.log (N : ℝ) := div_pos hy0 hL
  have hβ : 0 < Real.log (w : ℝ) / Real.log (N : ℝ) := div_pos hw0 hL
  have hint : (∫ t in (Real.log (y : ℝ) / Real.log (N : ℝ))..
      (Real.log (w : ℝ) / Real.log (N : ℝ)), 1 / t)
      = Real.log ((Real.log (w : ℝ) / Real.log (N : ℝ)) /
          (Real.log (y : ℝ) / Real.log (N : ℝ))) := integral_one_div_of_pos hα hβ
  have harg : (Real.log (w : ℝ) / Real.log (N : ℝ)) / (Real.log (y : ℝ) / Real.log (N : ℝ))
      = Real.log (w : ℝ) / Real.log (y : ℝ) := by
    field_simp
  rw [hint, harg, LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_eq hyw]
  have hb := LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_error hy hyw
  have hsplit : Real.log (Real.log (w : ℝ)) - Real.log (Real.log (y : ℝ))
      = Real.log (Real.log (w : ℝ) / Real.log (y : ℝ)) :=
    (Real.log_div hw0.ne' hy0.ne').symm
  rw [hsplit] at hb
  exact hb

/-! ### Part 2: the pair domain as an iterated sum of prime blocks -/

/-- The two cutoff facts for the integer endpoints of the prime bands. -/
private theorem ceil_facts {N : ℕ} (hN : 2 ≤ N) :
    ((N : ℝ) ^ kappa1 ≤ (Nat.ceil ((N : ℝ) ^ kappa1) : ℝ)) ∧
      (((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) < (N : ℝ) ^ kappa2) := by
  refine ⟨Nat.le_ceil _, ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hk2 : 0 ≤ kappa2 := by norm_num [kappa2]
  have hge : (1 : ℝ) ≤ (Nat.ceil ((N : ℝ) ^ kappa2) : ℝ) :=
    (one_le_rpow hN1 hk2).trans (Nat.le_ceil _)
  have hge1 : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa2) := by exact_mod_cast hge
  have hcast : ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) =
      (Nat.ceil ((N : ℝ) ^ kappa2) : ℝ) - 1 := by
    rw [Nat.cast_sub hge1]; norm_num
  rw [hcast]
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (N : ℝ) ^ kappa2 by positivity)
  linarith

/-- The unrestricted F4 pair sum is the iterated sum over a prime `p` in the lower
power band and a prime `q` above it. -/
private theorem fullPairs4_sum_iterated {N : ℕ} (hN : 2 ≤ N) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ fullPairs4 N, F p =
      ∑ p ∈ (Finset.Ioc (Nat.ceil ((N : ℝ) ^ kappa1) - 1)
          (Nat.ceil ((N : ℝ) ^ kappa2) - 1)).filter Nat.Prime,
        ∑ q ∈ (Finset.Ioc p (Nat.ceil ((N : ℝ) ^ kappa2) - 1)).filter Nat.Prime,
          F (p, q) := by
  classical
  obtain ⟨hceil1, hBlt⟩ := ceil_facts hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hκ2lt : kappa2 < 1 := by norm_num [kappa2]
  have hκ2le : kappa2 ≤ 1 := hκ2lt.le
  have hNrpowN : (N : ℝ) ^ kappa2 ≤ (N : ℝ) := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1 hκ2le
  -- (1) the raw double sum over the range square, and its iterated reshaping
  have hraw : ∑ p ∈ fullPairs4 N, F p =
      ∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
        ∑ q ∈ (Finset.range N).filter
          (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2), F (p, q) := by
    have h1 : ∑ p ∈ fullPairs4 N, F p = ∑ z ∈ Finset.range N ×ˢ Finset.range N,
        (if (z.1.Prime ∧ z.2.Prime ∧ (N : ℝ) ^ kappa1 ≤ (z.1 : ℝ) ∧ z.1 < z.2 ∧
          (z.2 : ℝ) < (N : ℝ) ^ kappa2) then F z else 0) := by
      rw [fullPairs4, Finset.sum_filter]
    rw [h1, Finset.sum_product]
    simp only [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p.Prime ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)
    · rw [if_pos hp]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      by_cases hq : q.Prime ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2
      · rw [if_pos hq, if_pos (by tauto)]
      · rw [if_neg hq, if_neg (by tauto)]
    · rw [if_neg hp]
      exact Finset.sum_eq_zero (fun q _ => by rw [if_neg (by tauto)])
  rw [hraw]
  -- (2) each inner prime band becomes an interval of integers
  have hC1 : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa2) :=
    Nat.one_le_ceil_iff.2 (rpow_pos_of_pos hN0 _)
  have hinner : ∀ p : ℕ,
      (∑ q ∈ (Finset.range N).filter
          (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2), F (p, q)) =
      ∑ q ∈ (Finset.Ioc p (Nat.ceil ((N : ℝ) ^ kappa2) - 1)).filter Nat.Prime,
        F (p, q) := by
    intro p
    refine Finset.sum_congr ?_ (fun q _ => rfl)
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hqN, hqp, hpq, hqhi⟩
      have hqceil : q < Nat.ceil ((N : ℝ) ^ kappa2) := Nat.lt_ceil.2 hqhi
      exact ⟨⟨hpq, by omega⟩, hqp⟩
    · rintro ⟨⟨hpq, hqle⟩, hqp⟩
      have hqceil : q < Nat.ceil ((N : ℝ) ^ kappa2) :=
        lt_of_le_of_lt hqle (Nat.sub_one_lt (by omega : Nat.ceil ((N : ℝ) ^ kappa2) ≠ 0))
      have hqhi : (q : ℝ) < (N : ℝ) ^ kappa2 := Nat.lt_ceil.1 hqceil
      have hqN : q < N := (Nat.cast_lt (α := ℝ)).1 (hqhi.trans_le hNrpowN)
      exact ⟨hqN, hqp, hpq, hqhi⟩
  simp only [hinner]
  -- (3) the outer prime band becomes an interval of integers
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    obtain ⟨hIoc, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hAp, hpB⟩ := Finset.mem_Ioc.mp hIoc
    have hpN : p < N := by
      have h1 : (p : ℝ) < (N : ℝ) :=
        lt_of_le_of_lt (by exact_mod_cast hpB) (lt_of_lt_of_le hBlt hNrpowN)
      exact (Nat.cast_lt (α := ℝ)).1 h1
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hpN, hpP, ?_⟩
    have hAA1 : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa1) := Nat.one_le_ceil_iff.2 (rpow_pos_of_pos hN0 _)
    have hpAA : Nat.ceil ((N : ℝ) ^ kappa1) ≤ p := by omega
    exact hceil1.trans (by exact_mod_cast hpAA)
  · intro p hp hpn
    obtain ⟨-, hpP, hplow⟩ := Finset.mem_filter.mp hp
    have hpAA : Nat.ceil ((N : ℝ) ^ kappa1) ≤ p := Nat.ceil_le.2 hplow
    have hAA1' : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa1) := Nat.one_le_ceil_iff.2 (rpow_pos_of_pos hN0 _)
    have hBB1 : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa2) := Nat.one_le_ceil_iff.2 (rpow_pos_of_pos hN0 _)
    have hBp : Nat.ceil ((N : ℝ) ^ kappa2) - 1 < p := by
      by_contra hcon
      exact hpn (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, by omega⟩, hpP⟩)
    have hpgt : Nat.ceil ((N : ℝ) ^ kappa2) - 1 < p := hBp
    refine Finset.sum_eq_zero (fun q hq => ?_)
    obtain ⟨hIoc, -⟩ := Finset.mem_filter.mp hq
    obtain ⟨hpq, hqB⟩ := Finset.mem_Ioc.mp hIoc
    omega

/-! ### Part 3: weighted prime reciprocal sums versus their integrals -/

/-- The logarithmic coordinate of a power cutoff lies in the exponent interval. -/
private theorem coord_bounds {N A : ℕ} (hN : 2 ≤ N) (hA : 2 ≤ A)
    (hlo : (N : ℝ) ^ kappa1 ≤ (A : ℝ)) (hhi : (A : ℝ) ≤ (N : ℝ) ^ kappa2) :
    Real.log (A : ℝ) / Real.log (N : ℝ) ∈ Icc kappa1 kappa2 := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : kappa1 ≤ Real.log (A : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hL]
    have h := Real.log_le_log (rpow_pos_of_pos hN0 kappa1) hlo
    rw [Real.log_rpow hN0] at h
    linarith
  have h2 : Real.log (A : ℝ) / Real.log (N : ℝ) ≤ kappa2 := by
    rw [div_le_iff₀ hL]
    have h := Real.log_le_log hA0 hhi
    rw [Real.log_rpow hN0] at h
    linarith
  exact ⟨h1, h2⟩

/-- A prime in the band `(A, M]` has its logarithmic coordinate within `h` above the
coordinate of `A`, and inside the exponent interval. -/
private theorem prime_coord_mem {N A M p : ℕ} {h : ℝ} (hN : 2 ≤ N) (hA : 2 ≤ A)
    (hlo : (N : ℝ) ^ kappa1 ≤ (A : ℝ)) (hhi : (M : ℝ) ≤ (N : ℝ) ^ kappa2)
    (hspan : Real.log (M : ℝ) / Real.log (N : ℝ) -
      Real.log (A : ℝ) / Real.log (N : ℝ) ≤ h)
    (hp : p ∈ (Finset.Ioc A M).filter Nat.Prime) :
    Real.log (p : ℝ) / Real.log (N : ℝ) ∈ Icc kappa1 kappa2 ∧
      |Real.log (p : ℝ) / Real.log (N : ℝ) - Real.log (A : ℝ) / Real.log (N : ℝ)|
        ≤ h := by
  classical
  obtain ⟨hIoc, hpP⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA, hpM⟩ := Finset.mem_Ioc.mp hIoc
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hppos : (0 : ℝ) < p := by
    have hp1 : (A : ℝ) < (p : ℝ) := by exact_mod_cast hpA
    linarith
  have hlow : kappa1 ≤ Real.log (p : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hL]
    have h1 : (N : ℝ) ^ kappa1 < (p : ℝ) := lt_of_le_of_lt hlo (by exact_mod_cast hpA)
    have h2 := Real.log_lt_log (rpow_pos_of_pos hN0 kappa1) h1
    rw [Real.log_rpow hN0] at h2
    linarith
  have hup : Real.log (p : ℝ) / Real.log (N : ℝ) ≤ kappa2 := by
    rw [div_le_iff₀ hL]
    have h1 : (p : ℝ) ≤ (N : ℝ) ^ kappa2 := le_trans (by exact_mod_cast hpM) hhi
    have h2 := Real.log_le_log hppos h1
    rw [Real.log_rpow hN0] at h2
    linarith
  refine ⟨⟨hlow, hup⟩, ?_⟩
  have hAle : Real.log (A : ℝ) / Real.log (N : ℝ) ≤ Real.log (p : ℝ) / Real.log (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact Real.log_le_log hApos (by exact_mod_cast hpA.le)
  have hple : Real.log (p : ℝ) / Real.log (N : ℝ) ≤ Real.log (M : ℝ) / Real.log (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact Real.log_le_log hppos (by exact_mod_cast hpM)
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- Continuity of the `1/t` weighted pieces on a logarithmic cell. -/
private theorem cont_on_cell {φ : ℝ → ℝ} (hcont : ContinuousOn φ (Icc kappa1 kappa2))
    {α ρ : ℝ} (hα0 : 0 < α) (hρ : α ≤ ρ) (hαk : kappa1 ≤ α)
    (hρk : ρ ≤ kappa2) :
    ContinuousOn (fun t : ℝ => φ t / t) (Icc α ρ) := by
  have hsub : Icc α ρ ⊆ Icc kappa1 kappa2 := fun t ht =>
    ⟨hαk.trans ht.1, ht.2.trans hρk⟩
  exact (hcont.mono hsub).div continuousOn_id fun t ht =>
    (lt_of_lt_of_le hα0 ht.1).ne'

/-- One block of the prime reciprocal sum is close to the corresponding integral of
`φ t / t`. -/
private theorem cell_total {φ : ℝ → ℝ} {C η h : ℝ} {N A M : ℕ}
    (hN : 2 ≤ N) (hA : 2 ≤ A) (hAM : A ≤ M)
    (hlo : (N : ℝ) ^ kappa1 ≤ (A : ℝ)) (hhi : (M : ℝ) ≤ (N : ℝ) ^ kappa2)
    (hspan : Real.log (M : ℝ) / Real.log (N : ℝ) - Real.log (A : ℝ) / Real.log (N : ℝ) ≤ h)
    (hcont : ContinuousOn φ (Icc kappa1 kappa2))
    (hbd : ∀ t ∈ Icc kappa1 kappa2, |φ t| ≤ C)
    (hmod : ∀ t ∈ Icc kappa1 kappa2, ∀ u ∈ Icc kappa1 kappa2,
      |t - u| ≤ h → |φ t - φ u| ≤ η) :
    |(∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
        φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
      ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t|
    ≤ 2 * η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ)))
      + (η + C) * (22 / (kappa1 * Real.log (N : ℝ))) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk1L : 0 < kappa1 * Real.log (N : ℝ) := mul_pos hk1 hL
  have hAb : (A : ℝ) ≤ (N : ℝ) ^ kappa2 := le_trans (by exact_mod_cast hAM) hhi
  have hAc : Real.log (A : ℝ) / Real.log (N : ℝ) ∈ Icc kappa1 kappa2 := coord_bounds hN hA hlo hAb
  have hMc : Real.log (M : ℝ) / Real.log (N : ℝ) ∈ Icc kappa1 kappa2 :=
    coord_bounds hN (le_trans hA hAM) (hlo.trans (by exact_mod_cast hAM)) hhi
  have hα0 : (0 : ℝ) < Real.log (A : ℝ) / Real.log (N : ℝ) := lt_of_lt_of_le hk1 hAc.1
  have hρ0 : (0 : ℝ) < Real.log (M : ℝ) / Real.log (N : ℝ) := lt_of_lt_of_le hk1 hMc.1
  have hαρ : Real.log (A : ℝ) / Real.log (N : ℝ) ≤ Real.log (M : ℝ) / Real.log (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact Real.log_le_log hApos (by exact_mod_cast hAM)
  -- the mass estimate and the two endpoint bounds
  have hmassR : |(∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) -
      ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t| ≤ 22 / Real.log (A : ℝ) :=
    cell_mass_error hN hA hAM
  have hintval : (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
      (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t) =
      Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ))) := integral_one_div_of_pos hα0 hρ0
  have hlogA : kappa1 * Real.log (N : ℝ) ≤ Real.log (A : ℝ) := by
    have h := hAc.1
    rw [le_div_iff₀ hL] at h
    linarith
  have herr : 22 / Real.log (A : ℝ) ≤ 22 / (kappa1 * Real.log (N : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) hk1L hlogA
  -- integrability on the cell
  have hIntφ : IntervalIntegrable (fun t : ℝ => φ t / t) volume
      (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ)) := by
    exact (show ContinuousOn (fun t : ℝ => φ t / t)
        (uIcc (Real.log (A : ℝ) / Real.log (N : ℝ))
          (Real.log (M : ℝ) / Real.log (N : ℝ))) from by
      rw [uIcc_of_le hαρ]; exact cont_on_cell hcont hα0 hαρ hAc.1 hMc.2).intervalIntegrable
  have hInt1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume
      (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ)) := by
    refine (show ContinuousOn (fun t : ℝ => 1 / t)
        (uIcc (Real.log (A : ℝ) / Real.log (N : ℝ))
          (Real.log (M : ℝ) / Real.log (N : ℝ))) from ?_).intervalIntegrable
    rw [uIcc_of_le hαρ]
    exact continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hα0 ht.1).ne'
  have hIntc : IntervalIntegrable
      (fun t : ℝ => φ (Real.log (A : ℝ) / Real.log (N : ℝ)) / t) volume
      (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ)) := by
    refine (show ContinuousOn
        (fun t : ℝ => φ (Real.log (A : ℝ) / Real.log (N : ℝ)) / t)
        (uIcc (Real.log (A : ℝ) / Real.log (N : ℝ))
          (Real.log (M : ℝ) / Real.log (N : ℝ))) from ?_).intervalIntegrable
    rw [uIcc_of_le hαρ]
    exact continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hα0 ht.1).ne'
  have hIntsub : IntervalIntegrable
      (fun t : ℝ => (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t) volume
      (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ)) := by
    refine (show ContinuousOn
        (fun t : ℝ => (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t)
        (uIcc (Real.log (A : ℝ) / Real.log (N : ℝ))
          (Real.log (M : ℝ) / Real.log (N : ℝ))) from ?_).intervalIntegrable
    rw [uIcc_of_le hαρ]
    have hc1 : ContinuousOn (fun t : ℝ => φ (Real.log (A : ℝ) / Real.log (N : ℝ)) / t)
        (Icc (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ))) :=
      continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hα0 ht.1).ne'
    exact (hc1.sub (cont_on_cell hcont hα0 hαρ hAc.1 hMc.2)).congr (fun t _ => by
      simp only [Pi.sub_apply]
      rw [sub_div])
  -- the corner constant integral
  have hconst : (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
      (Real.log (M : ℝ) / Real.log (N : ℝ)),
      φ (Real.log (A : ℝ) / Real.log (N : ℝ)) / t) =
      φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
        (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    simp only [mul_one_div]
  have hsubint : (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
      (Real.log (M : ℝ) / Real.log (N : ℝ)),
      (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t) =
      (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)),
        φ (Real.log (A : ℝ) / Real.log (N : ℝ)) / t) -
      (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t) := by
    rw [← intervalIntegral.integral_sub hIntc hIntφ]
    congr 1
    ext t
    rw [sub_div]
  -- pointwise replacement of the kernel by the corner value
  have hpt : ∀ p ∈ (Finset.Ioc A M).filter Nat.Prime,
      |φ (Real.log (p : ℝ) / Real.log (N : ℝ)) -
        φ (Real.log (A : ℝ) / Real.log (N : ℝ))| ≤ η := by
    intro p hp
    obtain ⟨hbox, hdist⟩ := prime_coord_mem (h := h) hN hA hlo hhi hspan hp
    exact hmod _ hbox _ hAc hdist
  have hsum1 : |(∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
        φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
      φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
        (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ))| ≤
      η * (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) := by
    have hEq : (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
          φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
        φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
          (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) =
        ∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
          (φ (Real.log (p : ℝ) / Real.log (N : ℝ)) -
            φ (Real.log (A : ℝ) / Real.log (N : ℝ))) / (p : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_one_div, sub_div])
    rw [hEq]
    calc |∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
          (φ (Real.log (p : ℝ) / Real.log (N : ℝ)) -
            φ (Real.log (A : ℝ) / Real.log (N : ℝ))) / (p : ℝ)|
        ≤ ∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
          |(φ (Real.log (p : ℝ) / Real.log (N : ℝ)) -
            φ (Real.log (A : ℝ) / Real.log (N : ℝ))) / (p : ℝ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, η * (1 / (p : ℝ)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp0 : (0 : ℝ) < p := by
            obtain ⟨hIoc, hpP⟩ := Finset.mem_filter.mp hp
            have h2 : 2 ≤ p := hpP.two_le
            exact_mod_cast (show 0 < p by omega)
          rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
          refine (hpt p hp).trans_eq ?_
          field_simp
      _ = η * (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) := by
          rw [Finset.mul_sum]
  -- the two residual bounds
  have hb3 : |φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
      ((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) -
        ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t)| ≤
      C * (22 / (kappa1 * Real.log (N : ℝ))) := by
    rw [abs_mul]
    have hC' : |φ (Real.log (A : ℝ) / Real.log (N : ℝ))| ≤ C := hbd _ hAc
    exact mul_le_mul hC' (hmassR.trans herr) (abs_nonneg _) (le_trans (abs_nonneg _) hC')
  have hb4 : |(∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)),
        (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t)| ≤
      η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ))) := by
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hαρ
      (f := fun t : ℝ => (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t)
    have hmono : (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)),
        |(φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t|) ≤
        ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (M : ℝ) / Real.log (N : ℝ)), η / t := by
      refine intervalIntegral.integral_mono_on hαρ ?_ ?_ (fun t ht => ?_)
      · refine (show ContinuousOn
            (fun t : ℝ => |(φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t|)
            (uIcc (Real.log (A : ℝ) / Real.log (N : ℝ))
              (Real.log (M : ℝ) / Real.log (N : ℝ))) from ?_).intervalIntegrable
        rw [uIcc_of_le hαρ]
        have hc1 : ContinuousOn (fun t : ℝ => φ (Real.log (A : ℝ) / Real.log (N : ℝ)) / t)
            (Icc (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ))) :=
          continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hα0 ht.1).ne'
        exact ((hc1.sub (cont_on_cell hcont hα0 hαρ hAc.1 hMc.2)).congr
          (fun t _ => by simp only [Pi.sub_apply]; rw [sub_div])).abs
      · refine (show ContinuousOn (fun t : ℝ => η / t)
            (uIcc (Real.log (A : ℝ) / Real.log (N : ℝ))
              (Real.log (M : ℝ) / Real.log (N : ℝ))) from ?_).intervalIntegrable
        rw [uIcc_of_le hαρ]
        exact continuousOn_const.div continuousOn_id fun t ht => (lt_of_lt_of_le hα0 ht.1).ne'
      · have ht0 : 0 < t := lt_of_lt_of_le hα0 ht.1
        have htbox : t ∈ Icc kappa1 kappa2 := ⟨hAc.1.trans ht.1, ht.2.trans hMc.2⟩
        have hd : |Real.log (A : ℝ) / Real.log (N : ℝ) - t| ≤ h := by
          rw [abs_sub_le_iff]
          constructor <;> linarith [ht.1, ht.2]
        have hη' := hmod (Real.log (A : ℝ) / Real.log (N : ℝ)) hAc t htbox hd
        rw [abs_div, abs_of_pos ht0]
        exact div_le_div_of_nonneg_right hη' ht0.le
    have hval : (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)), η / t) =
        η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
          (Real.log (A : ℝ) / Real.log (N : ℝ))) := by
      have hc : (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (M : ℝ) / Real.log (N : ℝ)), η / t) =
          η * (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
            (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        ext t
        ring
      rw [hc, hintval]
    linarith
  -- assemble everything
  have hsplit : (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
        φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
      ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t =
      ((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
          φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
        φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
          (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ))) +
      φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
        ((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) -
          ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
            (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t) +
      (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)),
        (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t) := by
    rw [hsubint, hconst]
    ring
  have hk12v : kappa1 < kappa2 := by norm_num [kappa1, kappa2]
  have hspan0 : 0 ≤ Real.log (M : ℝ) / Real.log (N : ℝ) - Real.log (A : ℝ) / Real.log (N : ℝ) := by
    have hlog : Real.log (A : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log hApos (by exact_mod_cast hAM)
    have h := div_le_div_of_nonneg_right hlog hL.le
    linarith
  have hh0 : 0 ≤ h := le_trans hspan0 hspan
  have hη0 : 0 ≤ η := by
    have h0 := hmod kappa1 ⟨le_refl kappa1, hk12v.le⟩ kappa1 ⟨le_refl kappa1, hk12v.le⟩
      (by simpa using hh0)
    simpa using h0
  set X : ℝ := (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
      φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
    φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
      (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) with hXdef
  set Y : ℝ := φ (Real.log (A : ℝ) / Real.log (N : ℝ)) *
      ((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) -
        ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t) with hYdef
  set Z : ℝ := (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
      (Real.log (M : ℝ) / Real.log (N : ℝ)),
      (φ (Real.log (A : ℝ) / Real.log (N : ℝ)) - φ t) / t) with hZdef
  have hsplit' : (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
        φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
      ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
        (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t = X + Y + Z := by
    rw [hsubint, hconst]
    ring
  have hmassle : (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) ≤
      Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ))) + 22 / (kappa1 * Real.log (N : ℝ)) := by
    have h1 : (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) -
        (∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (M : ℝ) / Real.log (N : ℝ)), 1 / t) ≤ 22 / Real.log (A : ℝ) :=
      (abs_le.1 hmassR).2
    linarith [hintval, herr]
  have h2 : η * (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime, 1 / (p : ℝ)) ≤
      η * (Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ))) + 22 / (kappa1 * Real.log (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hmassle hη0
  have hexp : η * (Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ))) + 22 / (kappa1 * Real.log (N : ℝ))) =
      η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
        (Real.log (A : ℝ) / Real.log (N : ℝ))) + η * (22 / (kappa1 * Real.log (N : ℝ))) := by
    ring
  rw [hsplit']
  have hX' : |X| ≤ η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
      (Real.log (A : ℝ) / Real.log (N : ℝ))) + η * (22 / (kappa1 * Real.log (N : ℝ))) :=
    (hsum1.trans h2).trans_eq hexp
  have hY' : |Y| ≤ C * (22 / (kappa1 * Real.log (N : ℝ))) := hb3
  calc |X + Y + Z| ≤ |X + Y| + |Z| := abs_add_le _ _
    _ ≤ (|X| + |Y|) + |Z| := by
        have h := abs_add_le X Y
        linarith
    _ ≤ (η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
          (Real.log (A : ℝ) / Real.log (N : ℝ))) + η * (22 / (kappa1 * Real.log (N : ℝ))) +
          C * (22 / (kappa1 * Real.log (N : ℝ)))) +
        η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
          (Real.log (A : ℝ) / Real.log (N : ℝ))) := by
        linarith [hX', hY', hb4]
    _ = 2 * η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
          (Real.log (A : ℝ) / Real.log (N : ℝ))) + (η + C) * (22 / (kappa1 * Real.log (N : ℝ))) := by
        ring

/-! ### Part 4: the grid decomposition of a weighted prime sum, by induction -/

/-- `N ^ (log A / log N) = A` for positive integers. -/
private theorem rpow_log_div {N A : ℕ} (hN : 2 ≤ N) (hA : 2 ≤ A) :
    (N : ℝ) ^ (Real.log (A : ℝ) / Real.log (N : ℝ)) = (A : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [Real.rpow_def_of_pos hN0]
  have hexp : Real.log (N : ℝ) * (Real.log (A : ℝ) / Real.log (N : ℝ)) = Real.log (A : ℝ) := by
    rw [mul_comm, div_mul_cancel₀ _ hL.ne']
  rw [hexp, Real.exp_log hA0]

/-- The logarithmic coordinate of the ceiling of `N ^ c` is at least `c`. -/
private theorem ceil_coord_ge {N : ℕ} (hN : 2 ≤ N) (c : ℝ) :
    c ≤ Real.log (Nat.ceil ((N : ℝ) ^ c) : ℝ) / Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h1 : (N : ℝ) ^ c ≤ (Nat.ceil ((N : ℝ) ^ c) : ℝ) := Nat.le_ceil _
  have h2 : (0 : ℝ) < (N : ℝ) ^ c := rpow_pos_of_pos hN0 c
  rw [le_div_iff₀ hL]
  have h3 := Real.log_le_log h2 h1
  rw [Real.log_rpow hN0] at h3
  linarith

/-- The logarithmic coordinate of the ceiling of `N ^ c` overshoots `c` by at most
`1 / (N^kappa1 log N)` when `c ≥ kappa1`. -/
private theorem ceil_coord_le {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc : kappa1 ≤ c) :
    Real.log (Nat.ceil ((N : ℝ) ^ c) : ℝ) / Real.log (N : ℝ) ≤
      c + 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le hk1 hc
  have hpos : (0 : ℝ) < (N : ℝ) ^ c := rpow_pos_of_pos hN0 c
  have hM1 : (1 : ℝ) ≤ (Nat.ceil ((N : ℝ) ^ c) : ℝ) :=
    (one_le_rpow hN1 hc0.le).trans (Nat.le_ceil _)
  have hMlt : ((Nat.ceil ((N : ℝ) ^ c) : ℕ) : ℝ) < (N : ℝ) ^ c + 1 :=
    Nat.ceil_lt_add_one hpos.le
  have hlog : Real.log (Nat.ceil ((N : ℝ) ^ c) : ℝ) ≤
      c * Real.log (N : ℝ) + 1 / (N : ℝ) ^ c := by
    have h1 : Real.log (Nat.ceil ((N : ℝ) ^ c) : ℝ) ≤ Real.log ((N : ℝ) ^ c + 1) :=
      Real.log_le_log (by linarith) hMlt.le
    have h2 : Real.log ((N : ℝ) ^ c + 1) =
        Real.log ((N : ℝ) ^ c) + Real.log (1 + 1 / (N : ℝ) ^ c) := by
      rw [← Real.log_mul hpos.ne' (by positivity)]
      congr 1
      field_simp
    have h3 : Real.log (1 + 1 / (N : ℝ) ^ c) ≤ 1 / (N : ℝ) ^ c := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (N : ℝ) ^ c by positivity)
      linarith
    have h4 : Real.log ((N : ℝ) ^ c) = c * Real.log (N : ℝ) := Real.log_rpow hN0 c
    linarith
  have hpow : (N : ℝ) ^ kappa1 ≤ (N : ℝ) ^ c := rpow_le_rpow_of_exponent_le hN1 hc
  have hpinv : 1 / (N : ℝ) ^ c ≤ 1 / (N : ℝ) ^ kappa1 :=
    one_div_le_one_div_of_le (rpow_pos_of_pos hN0 kappa1) hpow
  rw [div_le_iff₀ hL]
  have hkey : (c + 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ))) * Real.log (N : ℝ) =
      c * Real.log (N : ℝ) + 1 / (N : ℝ) ^ kappa1 := by
    field_simp
  rw [hkey]
  linarith

/-- Quantified one-dimensional partial summation bound for a weighted prime
reciprocal sum across `m` logarithmic cells. -/
private theorem prime_reciprocal_step {φ : ℝ → ℝ} {C η h : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hh : 0 < h) (hcont : ContinuousOn φ (Icc kappa1 kappa2))
    (hbd : ∀ t ∈ Icc kappa1 kappa2, |φ t| ≤ C)
    (hmod : ∀ t ∈ Icc kappa1 kappa2, ∀ u ∈ Icc kappa1 kappa2,
      |t - u| ≤ h → |φ t - φ u| ≤ η) :
    ∀ m : ℕ, 1 ≤ m → ∀ (N : ℕ), 2 ≤ N → ∀ A B : ℕ, 2 ≤ A →
      (N : ℝ) ^ kappa1 ≤ (A : ℝ) → (B : ℝ) ≤ (N : ℝ) ^ kappa2 → (A : ℝ) ≤ (B : ℝ) →
      (Real.log (B : ℝ) / Real.log (N : ℝ) - Real.log (A : ℝ) / Real.log (N : ℝ)) / (m : ℝ) +
          1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ h →
      |(∑ p ∈ (Finset.Ioc A B).filter Nat.Prime,
          φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
        ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
          (Real.log (B : ℝ) / Real.log (N : ℝ)), φ t / t| ≤
        2 * η * Real.log ((Real.log (B : ℝ) / Real.log (N : ℝ)) /
            (Real.log (A : ℝ) / Real.log (N : ℝ))) +
          (η + C) * (m : ℝ) * (22 / (kappa1 * Real.log (N : ℝ))) := by
  intro m
  induction m with
  | zero => intro h0; omega
  | succ m ih =>
    intro _ N hN A B hA2 hlo hhi hAB hspan
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show (0 : ℕ) < N by omega)
    have hL : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
    have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
    have hAb : (A : ℝ) ≤ (N : ℝ) ^ kappa2 := le_trans hAB hhi
    have hA2pos : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.2 (by omega)
    have hABn : A ≤ B := Nat.cast_le.1 hAB
    have hB2pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.2 (by omega)
    have hα1 : kappa1 ≤ Real.log (A : ℝ) / Real.log (N : ℝ) :=
      (coord_bounds hN hA2 hlo hAb).1
    have hβk : Real.log (B : ℝ) / Real.log (N : ℝ) ≤ kappa2 := by
      rw [div_le_iff₀ hL]
      have h := Real.log_le_log hB2pos hhi
      rw [Real.log_rpow hN0] at h
      linarith
    have hspan0 : 0 ≤ Real.log (B : ℝ) / Real.log (N : ℝ) - Real.log (A : ℝ) / Real.log (N : ℝ) := by
      have h := div_le_div_of_nonneg_right (Real.log_le_log hA2pos hAB) hL.le
      linarith
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- a single cell
      subst hm
      have h0 : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
      rw [h0, div_one] at hspan
      have hε0 : 0 ≤ 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) := by positivity
      have hcl := cell_total (φ := φ) (C := C) (η := η) (h := h) (N := N) (A := A) (M := B)
        hN hA2 hABn hlo hhi (by linarith) hcont hbd hmod
      simpa using hcl
    · -- at least two cells: peel off the first cell
      set s : ℝ := (Real.log (B : ℝ) / Real.log (N : ℝ) -
        Real.log (A : ℝ) / Real.log (N : ℝ)) / ((m : ℝ) + 1) with hs
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hsmul : s * ((m : ℝ) + 1) =
          Real.log (B : ℝ) / Real.log (N : ℝ) - Real.log (A : ℝ) / Real.log (N : ℝ) := by
        rw [hs]; field_simp
      have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg hspan0 hm1.le
      have hspanE : s + 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ h := by
        rw [hs]
        simpa only [Nat.cast_add, Nat.cast_one] using hspan
      set M : ℕ := Nat.ceil ((N : ℝ) ^ (Real.log (A : ℝ) / Real.log (N : ℝ) + s)) with hM
      have hMge : Real.log (A : ℝ) / Real.log (N : ℝ) + s ≤
          Real.log (M : ℝ) / Real.log (N : ℝ) := ceil_coord_ge hN _
      have hMle : Real.log (M : ℝ) / Real.log (N : ℝ) ≤
          Real.log (A : ℝ) / Real.log (N : ℝ) + s +
            1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) :=
        ceil_coord_le hN (le_trans hα1 (le_add_of_nonneg_right hs0))
      have hMA : A ≤ M := by
        have hMv : (M : ℝ) =
            ((Nat.ceil ((N : ℝ) ^ (Real.log (A : ℝ) / Real.log (N : ℝ) + s)) : ℕ) : ℝ) :=
          congrArg Nat.cast hM
        have h1 : (A : ℝ) ≤ (M : ℝ) := by
          rw [hMv]
          have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show (1:ℕ) ≤ N by omega : (1:ℕ) ≤ N)
          have hstep : (A : ℝ) ≤ (N : ℝ) ^ (Real.log (A : ℝ) / Real.log (N : ℝ) + s) := by
            calc (A : ℝ) = (N : ℝ) ^ (Real.log (A : ℝ) / Real.log (N : ℝ)) :=
                  (rpow_log_div hN hA2).symm
              _ ≤ (N : ℝ) ^ (Real.log (A : ℝ) / Real.log (N : ℝ) + s) :=
                  rpow_le_rpow_of_exponent_le hN1 (by linarith [hs0])
          exact hstep.trans (Nat.le_ceil _)
        exact Nat.cast_le.1 h1
      have hA2' : 2 ≤ M := le_trans hA2 hMA
      have hloM : (N : ℝ) ^ kappa1 ≤ (M : ℝ) := hlo.trans (by exact_mod_cast hMA)
      have hρge : Real.log (A : ℝ) / Real.log (N : ℝ) ≤
          Real.log (M : ℝ) / Real.log (N : ℝ) := by linarith [hMge, hs0]
      have hρ1 : kappa1 ≤ Real.log (M : ℝ) / Real.log (N : ℝ) := le_trans hα1 hρge
      have hρα : Real.log (A : ℝ) / Real.log (N : ℝ) ≤
          Real.log (B : ℝ) / Real.log (N : ℝ) := by linarith
      have hsβ : Real.log (A : ℝ) / Real.log (N : ℝ) + s ≤
          Real.log (B : ℝ) / Real.log (N : ℝ) := by
        have hle : s ≤ s * ((m : ℝ) + 1) := by nlinarith [hs0, hm1]
        linarith [hsmul]

      rcases Nat.lt_or_ge B M with hBM | hMB
      · -- the whole interval is a single cell
        have hcoordB : Real.log (B : ℝ) / Real.log (N : ℝ) ≤
            Real.log (M : ℝ) / Real.log (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hL.le
          exact Real.log_le_log hB2pos (by exact_mod_cast hBM.le)
        have hspanAB : Real.log (B : ℝ) / Real.log (N : ℝ) -
            Real.log (A : ℝ) / Real.log (N : ℝ) ≤ h := by
          linarith [hMle, hspanE, hcoordB]
        have hcl := cell_total (φ := φ) (C := C) (η := η) (h := h) (N := N) (A := A) (M := B)
          hN hA2 hABn hlo hhi hspanAB hcont hbd hmod
        refine hcl.trans ?_
        have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have herr0 : 0 ≤ 22 / (kappa1 * Real.log (N : ℝ)) := by positivity
        have hcoef : 0 ≤ η + C := by linarith
        have hmge : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [hmpos]
        rw [hcast]
        nlinarith [mul_le_mul_of_nonneg_left hmge hcoef, herr0]
      · -- peel the first cell
        have hcanonM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show (0:ℕ) < M by omega)
        have hρβ : Real.log (M : ℝ) / Real.log (N : ℝ) ≤
            Real.log (B : ℝ) / Real.log (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hL.le
          exact Real.log_le_log hcanonM (by exact_mod_cast hMB)
        have hhiM : (M : ℝ) ≤ (N : ℝ) ^ kappa2 := le_trans (by exact_mod_cast hMB) hhi
        have hspanAM : Real.log (M : ℝ) / Real.log (N : ℝ) -
            Real.log (A : ℝ) / Real.log (N : ℝ) ≤ h := by linarith [hMle, hspanE]
        have hcell := cell_total (φ := φ) (C := C) (η := η) (h := h) (N := N) (A := A) (M := M)
          hN hA2 hMA hlo hhiM hspanAM hcont hbd hmod
        have hspanMB : (Real.log (B : ℝ) / Real.log (N : ℝ) -
            Real.log (M : ℝ) / Real.log (N : ℝ)) / (m : ℝ) +
              1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ h := by
          have h1 : Real.log (B : ℝ) / Real.log (N : ℝ) - Real.log (M : ℝ) / Real.log (N : ℝ) ≤
              s * (m : ℝ) := by nlinarith [hMge, hsmul]
          have h2 : (Real.log (B : ℝ) / Real.log (N : ℝ) -
              Real.log (M : ℝ) / Real.log (N : ℝ)) / (m : ℝ) ≤ s := by
            rw [div_le_iff₀ hmpos]; linarith
          linarith [hspanE]
        have hIH := ih hm N hN M B hA2' hloM hhi (by exact_mod_cast hMB) hspanMB
        -- split the sum
        have hsum : (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) =
            (∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) +
            ∑ p ∈ (Finset.Ioc M B).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) := by
          have h := Finset.sum_Ioc_consecutive
            (f := fun p : ℕ => if p.Prime then φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ) else 0)
            hMA hMB
          simp only [Finset.sum_filter]
          exact h.symm
        -- split the integral
        have hρk : Real.log (M : ℝ) / Real.log (N : ℝ) ≤ kappa2 := le_trans hρβ hβk
        have hcontI : ∀ u v : ℝ, kappa1 ≤ u → v ≤ kappa2 → u ≤ v →
            IntervalIntegrable (fun t : ℝ => φ t / t) volume u v := by
          intro u v hu hv huv
          refine (show ContinuousOn (fun t : ℝ => φ t / t) (uIcc u v) from ?_).intervalIntegrable
          rw [uIcc_of_le huv]
          exact cont_on_cell hcont (lt_of_lt_of_le hk1 hu) huv hu hv
        have hInt1 : IntervalIntegrable (fun t : ℝ => φ t / t) volume
            (Real.log (A : ℝ) / Real.log (N : ℝ)) (Real.log (M : ℝ) / Real.log (N : ℝ)) :=
          hcontI _ _ hα1 hρk hρge
        have hInt2 : IntervalIntegrable (fun t : ℝ => φ t / t) volume
            (Real.log (M : ℝ) / Real.log (N : ℝ)) (Real.log (B : ℝ) / Real.log (N : ℝ)) :=
          hcontI _ _ hρ1 hβk hρβ
        have hintsplit := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
        have hkey : (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
            ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
              (Real.log (B : ℝ) / Real.log (N : ℝ)), φ t / t =
            ((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
              ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
                (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t) +
            ((∑ p ∈ (Finset.Ioc M B).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
              ∫ t in (Real.log (M : ℝ) / Real.log (N : ℝ))..
                (Real.log (B : ℝ) / Real.log (N : ℝ)), φ t / t) := by
          rw [hsum, ← hintsplit]
          ring
        rw [hkey]
        have hlogs : Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
              (Real.log (A : ℝ) / Real.log (N : ℝ))) +
            Real.log ((Real.log (B : ℝ) / Real.log (N : ℝ)) /
              (Real.log (M : ℝ) / Real.log (N : ℝ))) =
            Real.log ((Real.log (B : ℝ) / Real.log (N : ℝ)) /
              (Real.log (A : ℝ) / Real.log (N : ℝ))) := by
          have hM1 : 1 < M := by omega
          have hA1 : 1 < A := by omega
          have hB1' : 1 < B := by omega
          have h1 : (Real.log (M : ℝ) / Real.log (N : ℝ)) /
              (Real.log (A : ℝ) / Real.log (N : ℝ)) ≠ 0 := by
            apply div_ne_zero
            · exact div_ne_zero (Real.log_pos (by exact_mod_cast hM1)).ne' hL.ne'
            · exact div_ne_zero (Real.log_pos (by exact_mod_cast hA1)).ne' hL.ne'
          have h2 : (Real.log (B : ℝ) / Real.log (N : ℝ)) /
              (Real.log (M : ℝ) / Real.log (N : ℝ)) ≠ 0 := by
            apply div_ne_zero
            · exact div_ne_zero (Real.log_pos (by exact_mod_cast hB1')).ne' hL.ne'
            · exact div_ne_zero (Real.log_pos (by exact_mod_cast hM1)).ne' hL.ne'
          have hAnz : Real.log (A : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hA1)).ne'
          have hMnz : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM1)).ne'
          have hBnz : Real.log (B : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hB1')).ne'
          have hqA : Real.log (A : ℝ) / Real.log (N : ℝ) ≠ 0 := div_ne_zero hAnz hL.ne'
          have hqM : Real.log (M : ℝ) / Real.log (N : ℝ) ≠ 0 := div_ne_zero hMnz hL.ne'
          have hqB : Real.log (B : ℝ) / Real.log (N : ℝ) ≠ 0 := div_ne_zero hBnz hL.ne'
          rw [Real.log_div hqM hqA, Real.log_div hqB hqM, Real.log_div hqB hqA]
          ring
        have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        calc |((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
              ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
                (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t) +
            ((∑ p ∈ (Finset.Ioc M B).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
              ∫ t in (Real.log (M : ℝ) / Real.log (N : ℝ))..
                (Real.log (B : ℝ) / Real.log (N : ℝ)), φ t / t)|
            ≤ |((∑ p ∈ (Finset.Ioc A M).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
              ∫ t in (Real.log (A : ℝ) / Real.log (N : ℝ))..
                (Real.log (M : ℝ) / Real.log (N : ℝ)), φ t / t)| +
              |((∑ p ∈ (Finset.Ioc M B).filter Nat.Prime,
              φ (Real.log (p : ℝ) / Real.log (N : ℝ)) / (p : ℝ)) -
              ∫ t in (Real.log (M : ℝ) / Real.log (N : ℝ))..
                (Real.log (B : ℝ) / Real.log (N : ℝ)), φ t / t)| := abs_add_le _ _
          _ ≤ (2 * η * Real.log ((Real.log (M : ℝ) / Real.log (N : ℝ)) /
                (Real.log (A : ℝ) / Real.log (N : ℝ))) +
                (η + C) * (22 / (kappa1 * Real.log (N : ℝ)))) +
              (2 * η * Real.log ((Real.log (B : ℝ) / Real.log (N : ℝ)) /
                (Real.log (M : ℝ) / Real.log (N : ℝ))) +
                (η + C) * (m : ℝ) * (22 / (kappa1 * Real.log (N : ℝ)))) :=
            add_le_add hcell hIH
          _ = 2 * η * Real.log ((Real.log (B : ℝ) / Real.log (N : ℝ)) /
                (Real.log (A : ℝ) / Real.log (N : ℝ))) +
              (η + C) * ((m : ℝ) + 1) * (22 / (kappa1 * Real.log (N : ℝ))) := by
            rw [← hlogs]; ring
          _ = 2 * η * Real.log ((Real.log (B : ℝ) / Real.log (N : ℝ)) /
                (Real.log (A : ℝ) / Real.log (N : ℝ))) +
              (η + C) * (((m + 1 : ℕ)) : ℝ) * (22 / (kappa1 * Real.log (N : ℝ))) := by
            rw [hcast]


/-! ### Part 5: the inner integral compared at two exponents -/

/-- A slice `u ↦ g (s, u) / u` of the kernel is continuous on the exponent interval. -/
private theorem slice_cont {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {s : ℝ} (hs : s ∈ Icc kappa1 kappa2) :
    ContinuousOn (fun u : ℝ => g (s, u) / u) (Icc kappa1 kappa2) := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hpair : ContinuousOn (fun u : ℝ => (s, u)) (Icc kappa1 kappa2) := by fun_prop
  refine (hg.comp hpair (fun u hu => ⟨hs, hu⟩)).div continuousOn_id (fun u hu => ?_)
  exact (lt_of_lt_of_le hk1 hu.1).ne'

/-- Slices are interval integrable on any sub-interval of the exponent interval. -/
private theorem slice_integrable {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {s : ℝ} (hs : s ∈ Icc kappa1 kappa2) :
    ∀ a b : ℝ, a ∈ Icc kappa1 kappa2 → b ∈ Icc kappa1 kappa2 →
      IntervalIntegrable (fun u : ℝ => g (s, u) / u) volume a b := by
  intro a b ha hb
  refine (show ContinuousOn (fun u : ℝ => g (s, u) / u) (uIcc a b) from ?_).intervalIntegrable
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab]
    exact (slice_cont hg hs).mono (fun u hu => ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩)
  · rw [uIcc_of_ge hab]
    exact (slice_cont hg hs).mono (fun u hu => ⟨hb.1.trans hu.1, hu.2.trans ha.2⟩)

/-- The bound for a slice integral over a sub-interval of `[κ1, κ2]`. -/
private theorem slice_norm_le {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {M : ℝ} (hMb : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, |g x| ≤ M)
    (hM0 : 0 ≤ M) {s a b : ℝ} (hs : s ∈ Icc kappa1 kappa2)
    (ha : a ∈ Icc kappa1 kappa2) (hb : b ∈ Icc kappa1 kappa2) (hab : a ≤ b) :
    |(∫ u in a..b, g (s, u) / u)| ≤ M * (b - a) / kappa1 := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ => g (s, u) / u) (a := a) (b := b) (C := M / kappa1) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      have hx1 : kappa1 ≤ x := ha.1.trans hx.1.le
      have hx0 : 0 < x := lt_of_lt_of_le hk1 hx1
      have hmem : (s, x) ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2 := ⟨hs, ⟨hx1, hx.2.trans hb.2⟩⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0]
      exact (div_le_div_of_nonneg_right (hMb _ hmem) hx0.le).trans
        (div_le_div_of_nonneg_left hM0 hk1 hx1))
  simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a), div_mul_eq_mul_div]
    using h

/-- The difference of the inner integral at two exponents is a short piece plus a
kernel difference. -/
private theorem inner_diff_identity {g : ℝ × ℝ → ℝ} {β t t' : ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    (hβ1 : kappa1 ≤ β) (hβ2 : β ≤ kappa2)
    (ht : t ∈ Icc kappa1 kappa2) (ht' : t' ∈ Icc kappa1 kappa2) (hle : t ≤ t') :
    (∫ u in t..β, g (t, u) / u) - (∫ u in t'..β, g (t', u) / u) =
      (∫ u in t..t', g (t, u) / u) + ∫ u in t'..β, (g (t, u) - g (t', u)) / u := by
  have hβmem : β ∈ Icc kappa1 kappa2 := ⟨hβ1, hβ2⟩
  have h1 : (∫ u in t..β, g (t, u) / u) =
      (∫ u in t..t', g (t, u) / u) + ∫ u in t'..β, g (t, u) / u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (slice_integrable hg ht t t' ht ht') (slice_integrable hg ht t' β ht' hβmem)).symm
  have h2 : (∫ u in t'..β, (g (t, u) - g (t', u)) / u) =
      (∫ u in t'..β, g (t, u) / u) - ∫ u in t'..β, g (t', u) / u := by
    rw [← intervalIntegral.integral_sub (μ := volume)
      (slice_integrable hg ht t' β ht' hβmem) (slice_integrable hg ht' t' β ht' hβmem)]
    congr 1
    ext u
    rw [sub_div]
  rw [h1, h2]
  ring

/-- The modulus bound for the kernel difference against `1/u` on an interval inside
the exponent interval. -/
private theorem inner_diff_modulus {g : ℝ × ℝ → ℝ} {η h t t' : ℝ}
    (hmod : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ h → |g x - g y| ≤ η)
    (ht : t ∈ Icc kappa1 kappa2) (ht' : t' ∈ Icc kappa1 kappa2)
    (hdist : |t - t'| ≤ h) :
    ∀ u ∈ Icc kappa1 kappa2, |(g (t, u) - g (t', u)) / u| ≤ η / u := by
  intro u hu
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hu0 : 0 < u := lt_of_lt_of_le hk1 hu.1
  have hd : dist (t, u) (t', u) ≤ h := by
    rw [Prod.dist_eq, max_le_iff]
    exact ⟨by rw [Real.dist_eq]; exact hdist, by simpa using le_trans (abs_nonneg (t - t')) hdist⟩
  have hη := hmod (t, u) ⟨ht, hu⟩ (t', u) ⟨ht', hu⟩ hd
  calc |(g (t, u) - g (t', u)) / u| = |g (t, u) - g (t', u)| / u := by
        rw [abs_div, abs_of_pos hu0]
    _ ≤ η / u := div_le_div_of_nonneg_right hη hu0.le

/-- The kernel-difference integral over `[t', β]` is at most the modulus times
`log (κ2/κ1)`. -/
private theorem inner_diff_tail {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {M η h β t t' : ℝ}
    (hMb : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, |g x| ≤ M)
    (hmod : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ h → |g x - g y| ≤ η)
    (hη0 : 0 ≤ η) (hβ1 : kappa1 ≤ β) (hβ2 : β ≤ kappa2)
    (ht : t ∈ Icc kappa1 kappa2) (ht' : t' ∈ Icc kappa1 kappa2)
    (hdist : |t - t'| ≤ h) :
    |(∫ u in t'..β, (g (t, u) - g (t', u)) / u)| ≤ η * Real.log (kappa2 / kappa1) := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hpt := inner_diff_modulus hmod ht ht' hdist
  have hβmem : β ∈ Icc kappa1 kappa2 := ⟨hβ1, hβ2⟩
  have hcont : ∀ a b : ℝ, a ∈ Icc kappa1 kappa2 → b ∈ Icc kappa1 kappa2 → a ≤ b →
      (∫ u in a..b, |(g (t, u) - g (t', u)) / u|) ≤ ∫ u in a..b, η / u := by
    intro a b ha hb hab
    refine intervalIntegral.integral_mono_on hab ?_ ?_ (fun u hu => hpt u ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩)
    · refine (show ContinuousOn (fun u : ℝ => |(g (t, u) - g (t', u)) / u|) (uIcc a b) from ?_).intervalIntegrable
      rw [uIcc_of_le hab]
      have hc1 : ContinuousOn (fun u : ℝ => g (t, u) / u) (Icc a b) :=
        (slice_cont hg ht).mono (fun u hu => ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩)
      have hc2 : ContinuousOn (fun u : ℝ => g (t', u) / u) (Icc a b) :=
        (slice_cont hg ht').mono (fun u hu => ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩)
      exact ((hc1.sub hc2).congr (fun u _ => by simp only [Pi.sub_apply]; rw [sub_div])).abs
    · refine (show ContinuousOn (fun u : ℝ => η / u) (uIcc a b) from ?_).intervalIntegrable
      rw [uIcc_of_le hab]
      exact continuousOn_const.div continuousOn_id fun u hu =>
        (lt_of_lt_of_le hk1 (ha.1.trans hu.1)).ne'
  have hval : ∀ a b : ℝ, a ∈ Icc kappa1 kappa2 → b ∈ Icc kappa1 kappa2 → a ≤ b →
      (∫ u in a..b, η / u) = η * Real.log (b / a) := by
    intro a b ha hb hab
    have ha0 : 0 < a := lt_of_lt_of_le hk1 ha.1
    have h1 : (∫ u in a..b, η / u) = η * (∫ u in a..b, 1 / u) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext u
      ring
    rw [h1, integral_one_div_of_pos ha0 (lt_of_lt_of_le hk1 hb.1)]
  rcases le_total t' β with hord | hge
  · have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hord
      (f := fun u : ℝ => (g (t, u) - g (t', u)) / u)
    have hmono := hcont t' β ht' hβmem hord
    have hv := hval t' β ht' hβmem hord
    have hlogβ : Real.log (β / t') ≤ Real.log (kappa2 / kappa1) := by
      apply Real.log_le_log (div_pos (lt_of_lt_of_le hk1 hβ1) (lt_of_lt_of_le hk1 ht'.1))
      have hk2 : (0 : ℝ) < kappa2 := lt_of_lt_of_le hk1 (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2)
      have h1 : β / t' ≤ kappa2 / t' :=
        (div_le_div_iff_of_pos_right (lt_of_lt_of_le hk1 ht'.1)).2 hβ2
      have h2 : kappa2 / t' ≤ kappa2 / kappa1 :=
        (div_le_div_iff_of_pos_left hk2 (lt_of_lt_of_le hk1 ht'.1) hk1).2 ht'.1
      linarith
    have hfin : η * Real.log (β / t') ≤ η * Real.log (kappa2 / kappa1) :=
      mul_le_mul_of_nonneg_left hlogβ hη0
    linarith [habs, hmono, hv, hfin]
  · rw [intervalIntegral.integral_symm β t', abs_neg]
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hge
      (f := fun u : ℝ => (g (t, u) - g (t', u)) / u)
    have hmono := hcont β t' hβmem ht' hge
    have hv := hval β t' hβmem ht' hge
    have hlogβ : Real.log (t' / β) ≤ Real.log (kappa2 / kappa1) := by
      apply Real.log_le_log (div_pos (lt_of_lt_of_le hk1 ht'.1) (lt_of_lt_of_le hk1 hβ1))
      have hk2 : (0 : ℝ) < kappa2 := lt_of_lt_of_le hk1 (by norm_num [kappa1, kappa2] : kappa1 ≤ kappa2)
      have h1 : t' / β ≤ kappa2 / β :=
        (div_le_div_iff_of_pos_right (lt_of_lt_of_le hk1 hβ1)).2 ht'.2
      have h2 : kappa2 / β ≤ kappa2 / kappa1 :=
        (div_le_div_iff_of_pos_left hk2 (lt_of_lt_of_le hk1 hβ1) hk1).2 hβ1
      linarith
    have hfin : η * Real.log (t' / β) ≤ η * Real.log (kappa2 / kappa1) :=
      mul_le_mul_of_nonneg_left hlogβ hη0
    linarith [habs, hmono, hv, hfin]

/-- The one-sided form of the exponent-difference bound. -/
private theorem inner_diff_le_of_le {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {M η h β t t' : ℝ}
    (hMb : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, |g x| ≤ M)
    (hmod : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ h → |g x - g y| ≤ η)
    (hη0 : 0 ≤ η) (hM0 : 0 ≤ M) (hβ1 : kappa1 ≤ β) (hβ2 : β ≤ kappa2)
    (ht : t ∈ Icc kappa1 kappa2) (ht' : t' ∈ Icc kappa1 kappa2)
    (hle : t ≤ t') (hdist : |t - t'| ≤ h) :
    |(∫ u in t..β, g (t, u) / u) - (∫ u in t'..β, g (t', u) / u)|
      ≤ M * (t' - t) / kappa1 + η * Real.log (kappa2 / kappa1) := by
  rw [inner_diff_identity hg hβ1 hβ2 ht ht' hle]
  refine (abs_add_le _ _).trans ?_
  have hb1 : |(∫ u in t..t', g (t, u) / u)| ≤ M * (t' - t) / kappa1 :=
    slice_norm_le hg hMb hM0 ht ht ht' hle
  have hb2 := inner_diff_tail hg hMb hmod hη0 hβ1 hβ2 ht ht' hdist
  linarith [hb1, hb2]

/-- The inner integral over `[·, β]` moves by at most `M |t - t'| / κ1` plus the
modulus of the kernel times `log (κ2/κ1)`. -/
private theorem inner_diff_le {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {M η h β t t' : ℝ}
    (hMb : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, |g x| ≤ M)
    (hmod : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ h → |g x - g y| ≤ η)
    (hη0 : 0 ≤ η) (hM0 : 0 ≤ M) (hβ1 : kappa1 ≤ β) (hβ2 : β ≤ kappa2)
    (ht : t ∈ Icc kappa1 kappa2) (ht' : t' ∈ Icc kappa1 kappa2)
    (hdist : |t - t'| ≤ h) :
    |(∫ u in t..β, g (t, u) / u) - (∫ u in t'..β, g (t', u) / u)|
      ≤ M * |t - t'| / kappa1 + η * Real.log (kappa2 / kappa1) := by
  rcases le_total t t' with hle | hle
  · have h := inner_diff_le_of_le hg hMb hmod hη0 hM0 hβ1 hβ2 ht ht' hle hdist
    rw [abs_of_nonpos (by linarith : t - t' ≤ 0)]
    exact h.trans_eq (by ring)
  · have hdist' : |t' - t| ≤ h := by rwa [abs_sub_comm] at hdist
    have h := inner_diff_le_of_le (t := t') (t' := t) hg hMb hmod hη0 hM0 hβ1 hβ2 ht' ht hle hdist'
    rw [abs_sub_comm (∫ u in t..β, g (t, u) / u) (∫ u in t'..β, g (t', u) / u),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - t')]
    exact h


/-! ### Part 6: continuity of the inner integral in its exponent -/

/-- Continuity of `t ↦ ∫_t^β g (t, u) / u` on the exponent interval. -/
private theorem inner_continuous {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2))
    {M β : ℝ} (hMb : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, |g x| ≤ M)
    (hM0 : 0 ≤ M)
    (hucc : ∀ η > 0, ∃ δ > 0, ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ δ → |g x - g y| ≤ η)
    (hβ1 : kappa1 ≤ β) (hβ2 : β ≤ kappa2) :
    ContinuousOn (fun t : ℝ => ∫ u in t..β, g (t, u) / u) (Icc kappa1 kappa2) := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hL : 0 < Real.log (kappa2 / kappa1) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hk1]
    norm_num [kappa1, kappa2]
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hL1 : (0 : ℝ) < Real.log (kappa2 / kappa1) + 1 := by linarith
  have hη0 : 0 < ε / (2 * (Real.log (kappa2 / kappa1) + 1)) := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := hucc (ε / (2 * (Real.log (kappa2 / kappa1) + 1))) hη0
  refine ⟨min δ (ε * kappa1 / (4 * (M + 1))), lt_min hδ0 (by positivity), ?_⟩
  intro a ha had
  have hdist : |a - b| ≤ δ := by
    rw [Real.dist_eq] at had
    exact le_of_lt (lt_of_lt_of_le had (min_le_left _ _))
  have hsmall : |a - b| < ε * kappa1 / (4 * (M + 1)) := by
    rw [Real.dist_eq] at had
    exact lt_of_lt_of_le had (min_le_right _ _)
  have hbnd :=
    inner_diff_le hg hMb (fun x hx y hy hd => hδ x hx y hy hd) (le_of_lt hη0) hM0 hβ1 hβ2
      ha hb hdist
  rw [Real.dist_eq]
  have hstep : ε / (2 * (Real.log (kappa2 / kappa1) + 1)) * Real.log (kappa2 / kappa1) < ε / 2 := by
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (kappa2 / kappa1) + 1))]
    nlinarith
  have hMstep : M * |a - b| / kappa1 < ε / 2 := by
    have h1 : M * |a - b| / kappa1 ≤ M * (ε * kappa1 / (4 * (M + 1))) / kappa1 := by
      apply div_le_div_of_nonneg_right _ hk1.le
      exact mul_le_mul_of_nonneg_left hsmall.le hM0
    have h2 : M * (ε * kappa1 / (4 * (M + 1))) / kappa1 = ε / 4 * (M / (M + 1)) := by
      field_simp
    have h3 : M / (M + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < M + 1)]
      linarith
    have h4 : ε / 4 * (M / (M + 1)) ≤ ε / 4 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ε / 4)
      simpa using this
    linarith
  linarith [hbnd, hstep, hMstep]


/-! ### Part 7: the limit of the prime pair sum -/

/-- Eventually `c / log N ≤ λ`. -/
private theorem eventually_div_log_le {c lam : ℝ} (hlam : 0 < lam) :
    ∀ᶠ N : ℕ in atTop, c / Real.log (N : ℝ) ≤ lam := by
  rcases le_or_gt c 0 with hc | hc
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have h1 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
    exact (div_nonpos_of_nonpos_of_nonneg hc h1.le).trans hlam.le
  · have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually_ge_atTop (c / lam), eventually_ge_atTop 2] with N hN hN2
    have h1 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
    rw [div_le_iff₀ h1]
    rw [div_le_iff₀ hlam] at hN
    linarith

/-- The logarithmic coordinate of `⌈N^c⌉` stays within `ε` of `c` eventually. -/
private theorem eventually_ceil_coord {c : ℝ} (hc : kappa1 ≤ c) {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ N : ℕ in atTop,
      |Real.log (Nat.ceil ((N : ℝ) ^ c) : ℝ) / Real.log (N : ℝ) - c| ≤ ε' := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  filter_upwards [eventually_ge_atTop 2,
    eventually_div_log_le (c := 1 / kappa1) (lam := ε') hε'] with N hN2 hN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show (1 : ℕ) ≤ N by omega)
  have h1 := ceil_coord_ge (N := N) hN2 c
  have h2 := ceil_coord_le (N := N) hN2 hc
  have hpow1 : (1 : ℝ) ≤ (N : ℝ) ^ kappa1 := one_le_rpow hN1 hk1.le
  have h3 : 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ (1 / kappa1) / Real.log (N : ℝ) := by
    rw [show 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) =
      (1 / (N : ℝ) ^ kappa1) / Real.log (N : ℝ) by field_simp]
    exact div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le hk1 (le_trans (by norm_num [kappa1] : kappa1 ≤ 1) hpow1)) hL.le
  rw [abs_le]
  constructor <;> linarith

/-- The logarithmic coordinate of `⌈N^c⌉ - 1` is at least `c - 4/(N^c log N)`. -/
private theorem pred_ceil_coord_ge {N : ℕ} (hN : 2 ≤ N) (hx4 : 4 ≤ (N : ℝ) ^ kappa2) :
    kappa2 - 4 / ((N : ℝ) ^ kappa2 * Real.log (N : ℝ)) ≤
      Real.log ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) / Real.log (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have hx0 : 0 < (N : ℝ) ^ kappa2 := rpow_pos_of_pos hN0 _
  have hcc1 : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa2) := Nat.one_le_ceil_iff.2 hx0
  have hcast : ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) =
      (Nat.ceil ((N : ℝ) ^ kappa2) : ℝ) - 1 := by
    rw [Nat.cast_sub hcc1]; norm_num
  have hBge : (N : ℝ) ^ kappa2 - 2 ≤ ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) := by
    rw [hcast]
    linarith [Nat.le_ceil ((N : ℝ) ^ kappa2)]
  have hx2 : 0 < (N : ℝ) ^ kappa2 - 2 := by linarith
  have hlog1 : Real.log ((N : ℝ) ^ kappa2 - 2) ≤
      Real.log ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) := Real.log_le_log hx2 hBge
  have hsplit : Real.log ((N : ℝ) ^ kappa2 - 2) =
      Real.log ((N : ℝ) ^ kappa2) + Real.log (1 - 2 / (N : ℝ) ^ kappa2) := by
    have hxe : (N : ℝ) ^ kappa2 - 2 = (N : ℝ) ^ kappa2 * (1 - 2 / (N : ℝ) ^ kappa2) := by
      field_simp
    rw [hxe, Real.log_mul hx0.ne' (by
      have hlt : 0 < 1 - 2 / (N : ℝ) ^ kappa2 := by
        rw [sub_pos, div_lt_one hx0]
        linarith
      exact hlt.ne')]
  have hy2 : 2 / (N : ℝ) ^ kappa2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hx0]
    linarith
  have hlow : -(4 / (N : ℝ) ^ kappa2) ≤ Real.log (1 - 2 / (N : ℝ) ^ kappa2) := by
    have hpos : 0 < 1 - 2 / (N : ℝ) ^ kappa2 := by linarith
    have h1 : Real.log (1 - 2 / (N : ℝ) ^ kappa2) =
        -Real.log (1 / (1 - 2 / (N : ℝ) ^ kappa2)) := by
      rw [Real.log_div one_ne_zero hpos.ne', Real.log_one]
      ring
    rw [h1]
    have h2 : 1 / (1 - 2 / (N : ℝ) ^ kappa2) = 1 + (2 / (N : ℝ) ^ kappa2) / (1 - 2 / (N : ℝ) ^ kappa2) := by
      field_simp
      ring
    rw [h2]
    have h3 := Real.log_le_sub_one_of_pos
      (show 0 < 1 + (2 / (N : ℝ) ^ kappa2) / (1 - 2 / (N : ℝ) ^ kappa2) by positivity)
    have h4 : (2 / (N : ℝ) ^ kappa2) / (1 - 2 / (N : ℝ) ^ kappa2) ≤ 4 / (N : ℝ) ^ kappa2 := by
      have h5 : (2 / (N : ℝ) ^ kappa2) / (1 - 2 / (N : ℝ) ^ kappa2) ≤
          (2 / (N : ℝ) ^ kappa2) / (1 / 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      have h6 : (2 / (N : ℝ) ^ kappa2) / (1 / 2) = 4 / (N : ℝ) ^ kappa2 := by
        field_simp
        ring
      linarith
    linarith
  have hlogx : Real.log ((N : ℝ) ^ kappa2) = kappa2 * Real.log (N : ℝ) := Real.log_rpow hN0 kappa2
  have hfin : kappa2 * Real.log (N : ℝ) - 4 / (N : ℝ) ^ kappa2 ≤
      Real.log ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) := by
    linarith [hsplit, hlow, hlog1, hlogx]
  rw [le_div_iff₀ hL]
  have hexp : (kappa2 - 4 / ((N : ℝ) ^ kappa2 * Real.log (N : ℝ))) * Real.log (N : ℝ) =
      kappa2 * Real.log (N : ℝ) - 4 / (N : ℝ) ^ kappa2 := by
    field_simp
  rw [hexp]
  exact hfin

/-- The lower band end `⌈N^κ2⌉ - 1` has logarithmic coordinate close to `κ2`. -/
private theorem eventually_pred_ceil_coord {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ N : ℕ in atTop,
      kappa2 - Real.log ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) / Real.log (N : ℝ) ≤ ε' := by
  have hk2 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa2) atTop atTop :=
    (tendsto_rpow_atTop hk2).comp tendsto_natCast_atTop_atTop
  have hk2v : kappa2 = 29 / 250 := by norm_num [kappa2]
  filter_upwards [eventually_ge_atTop 2, hpow.eventually_ge_atTop 4,
    hpow.eventually_ge_atTop (250 / 29),
    eventually_div_log_le (c := 4 * kappa2) (lam := ε') hε'] with N hN2 hx4 hx86 hNε
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have hlow := pred_ceil_coord_ge hN2 hx4
  have h1 : 4 / ((N : ℝ) ^ kappa2 * Real.log (N : ℝ)) ≤ (4 * kappa2) / Real.log (N : ℝ) := by
    rw [show 4 / ((N : ℝ) ^ kappa2 * Real.log (N : ℝ)) =
      (4 / (N : ℝ) ^ kappa2) / Real.log (N : ℝ) by field_simp]
    rw [div_le_div_iff_of_pos_right hL]
    rw [div_le_iff₀ (rpow_pos_of_pos hN0 _)]
    rw [hk2v] at hx86 ⊢
    nlinarith [hx86]
  linarith


set_option maxHeartbeats 1600000 in
/-- LEAF. Wu 2004 page 39 equation 10.5, the fixed kernel part of the
standard replacement of sums over primes by integrals.
This statement has only reciprocal prime weights on the fixed ordered triangle.
The finite logarithmic perturbation and arithmetic restrictions are absent. -/
theorem continuous_prime_triangle (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2)) :
    Tendsto (fun N : ℕ => ∑ p ∈ fullPairs4 N,
      g (log (p.1 : ℝ) / log N, log (p.2 : ℝ) / log N) /
        ((p.1 : ℝ) * p.2)) atTop
      (𝓝 (∫ t in kappa1..kappa2, (∫ u in t..kappa2, g (t, u) / u) / t)) := by
  classical
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk12 : kappa1 < kappa2 := by norm_num [kappa1, kappa2]
  have hkd : 0 < kappa2 - kappa1 := by linarith
  have hLpos : 0 < Real.log (kappa2 / kappa1) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hk1]
    linarith
  have hcpt : IsCompact (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hcpt.exists_bound_of_continuousOn hg
  set M : ℝ := max C₀ 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hMb : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, |g x| ≤ M := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hucc : ∀ η > 0, ∃ δ > 0, ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ δ → |g x - g y| ≤ η := by
    intro η hη
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
      (hcpt.uniformContinuousOn_of_continuous hg) η hη
    exact ⟨δ, hδ0, fun x hx y hy hd => by
      have h := hδ x hx y hy hd
      rwa [Real.dist_eq] at h⟩
  have hcontW : ContinuousOn (fun t : ℝ => ∫ u in t..kappa2, g (t, u) / u) (Icc kappa1 kappa2) :=
    inner_continuous hg hMb hM0.le hucc hk12.le (le_refl kappa2)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the numerical choices
  set L : ℝ := Real.log (kappa2 / kappa1) with hLdef
  have hL0 : 0 < L := hLpos
  have hK0 : 0 < L + 1 := by linarith
  have hη₁0 : 0 < ε / (64 * L * (L + 1) * (L + 1)) := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := hucc (ε / (64 * L * (L + 1) * (L + 1))) hη₁0
  obtain ⟨n, hn1, hnδ, hnM⟩ : ∃ n : ℕ, 1 ≤ n ∧ 2 * (kappa2 - kappa1) / n ≤ δ ∧
      4 * M * (kappa2 - kappa1) * L / (n * kappa1) ≤ ε / 16 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * (kappa2 - kappa1) / δ)
      (64 * M * (kappa2 - kappa1) * L / (kappa1 * ε)))
    refine ⟨n, ?_, ?_, ?_⟩
    · have hpos : (0 : ℝ) < max (2 * (kappa2 - kappa1) / δ)
          (64 * M * (kappa2 - kappa1) * L / (kappa1 * ε)) :=
        lt_of_lt_of_le (by positivity) (le_max_left _ _)
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans hpos hn
      exact Nat.one_le_iff_ne_zero.2 (by intro h; rw [h] at hn0; norm_num at hn0)
    · have h2 : 2 * (kappa2 - kappa1) / δ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
      have hpos : (0 : ℝ) < 2 * (kappa2 - kappa1) / δ := by positivity
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans hpos h2
      rw [div_lt_iff₀ hδ0] at h2
      rw [div_le_iff₀ hn0]
      nlinarith [h2]
    · have h2 : 64 * M * (kappa2 - kappa1) * L / (kappa1 * ε) < (n : ℝ) :=
        lt_of_le_of_lt (le_max_right _ _) hn
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by positivity) h2.le
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * kappa1)]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < kappa1 * ε)] at h2
      nlinarith [h2, hε, hkd, hM0, hL0]
  set h : ℝ := 2 * (kappa2 - kappa1) / n with hhdef
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hhδ : h ≤ δ := hnδ
  have hmodh : ∀ x ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2,
      ∀ y ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2, dist x y ≤ h →
        |g x - g y| ≤ ε / (64 * L * (L + 1) * (L + 1)) :=
    fun x hx y hy hd => hδ x hx y hy (hd.trans hhδ)
  -- the outer weight: bound and modulus
  have hη₁L : 0 < ε / (64 * L * (L + 1) * (L + 1)) * L := by positivity
  have hWbd : ∀ t ∈ Icc kappa1 kappa2,
      |(∫ u in t..kappa2, g (t, u) / u)| ≤ M * L := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hk1 ht.1
    have hpt : ∀ u ∈ Icc t kappa2, |g (t, u) / u| ≤ M / u := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le ht0 hu.1
      have hmem : (t, u) ∈ Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2 :=
        ⟨ht, ⟨ht.1.trans hu.1, hu.2⟩⟩
      rw [abs_div, abs_of_pos hu0]
      exact div_le_div_of_nonneg_right (hMb _ hmem) hu0.le
    have hmono : (∫ u in t..kappa2, |g (t, u) / u|) ≤ ∫ u in t..kappa2, M / u := by
      refine intervalIntegral.integral_mono_on ht.2 ?_ ?_ hpt
      · refine (show ContinuousOn (fun u : ℝ => |g (t, u) / u|) (uIcc t kappa2) from ?_).intervalIntegrable
        rw [uIcc_of_le ht.2]
        exact ((slice_cont hg ht).mono (fun u hu => ⟨ht.1.trans hu.1, hu.2⟩)).abs
      · refine (show ContinuousOn (fun u : ℝ => M / u) (uIcc t kappa2) from ?_).intervalIntegrable
        rw [uIcc_of_le ht.2]
        exact continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le ht0 hu.1).ne'
    have hval : (∫ u in t..kappa2, M / u) = M * Real.log (kappa2 / t) := by
      have h1 : (∫ u in t..kappa2, M / u) = M * (∫ u in t..kappa2, 1 / u) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        ext u
        ring
      rw [h1, integral_one_div_of_pos ht0 (lt_of_lt_of_le hk1 hk12.le)]
    have hlog : Real.log (kappa2 / t) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log (div_pos (by linarith) ht0)
      exact (div_le_div_iff_of_pos_left (by linarith : (0:ℝ) < kappa2) ht0 hk1).2 ht.1
    calc |(∫ u in t..kappa2, g (t, u) / u)| ≤ ∫ u in t..kappa2, |g (t, u) / u| :=
          intervalIntegral.abs_integral_le_integral_abs (μ := volume) ht.2
      _ ≤ ∫ u in t..kappa2, M / u := hmono
      _ = M * Real.log (kappa2 / t) := hval
      _ ≤ M * L := by nlinarith [hlog, hM0.le]
  have hWmod : ∀ t ∈ Icc kappa1 kappa2, ∀ t' ∈ Icc kappa1 kappa2, |t - t'| ≤ h →
      |(∫ u in t..kappa2, g (t, u) / u) - (∫ u in t'..kappa2, g (t', u) / u)| ≤
        M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L :=
    fun t ht t' ht' hd => by
      have h1 := inner_diff_le hg hMb hmodh hη₁0.le hM0.le hk12.le (le_refl kappa2) ht ht' hd
      have h2 : Real.log (kappa2 / kappa1) = L := hLdef.symm
      rw [h2] at h1
      have h3 : M * |t - t'| / kappa1 ≤ M * h / kappa1 := by
        apply div_le_div_of_nonneg_right _ hk1.le
        exact mul_le_mul_of_nonneg_left hd hM0.le
      linarith
  -- the eventual conditions on `N`
  have hA : ∀ᶠ N : ℕ in atTop, 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤
      (kappa2 - kappa1) / n := by
    have h := eventually_div_log_le (c := 1 / kappa1) (lam := (kappa2 - kappa1) / n) (by positivity)
    filter_upwards [h, eventually_ge_atTop 2] with N hN hN2
    have hLg : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
    have hpow1 : (1 : ℝ) ≤ (N : ℝ) ^ kappa1 :=
      one_le_rpow (by exact_mod_cast (show (1 : ℕ) ≤ N by omega)) hk1.le
    have h3 : 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ (1 / kappa1) / Real.log (N : ℝ) := by
      rw [show 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) =
        (1 / (N : ℝ) ^ kappa1) / Real.log (N : ℝ) by field_simp]
      exact div_le_div_of_nonneg_right
        (one_div_le_one_div_of_le hk1 (le_trans (by norm_num [kappa1] : kappa1 ≤ 1) hpow1)) hLg.le
    linarith
  have hB : ∀ᶠ N : ℕ in atTop, 22 / (kappa1 * Real.log (N : ℝ)) ≤
      ε / (32 * (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1)) := by
    have h := eventually_div_log_le (c := 22 / kappa1)
      (lam := ε / (32 * (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1))) (by positivity)
    filter_upwards [h] with N hN
    calc 22 / (kappa1 * Real.log (N : ℝ)) = (22 / kappa1) / Real.log (N : ℝ) := by field_simp
      _ ≤ _ := hN
  have hC : ∀ᶠ N : ℕ in atTop,
      kappa2 - Real.log ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) / Real.log (N : ℝ) ≤
        min (ε * kappa1 / (32 * M * (L + 1))) (ε * kappa1 / (16 * (M * L))) :=
    eventually_pred_ceil_coord (by positivity)
  have hD : ∀ᶠ N : ℕ in atTop, 22 / (kappa1 * Real.log (N : ℝ)) ≤
      ε / (8 * (M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L + M * L) * (n : ℝ)) := by
    have h := eventually_div_log_le (c := 22 / kappa1)
      (lam := ε / (8 * (M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L + M * L) * (n : ℝ)))
      (by positivity)
    filter_upwards [h] with N hN
    calc 22 / (kappa1 * Real.log (N : ℝ)) = (22 / kappa1) / Real.log (N : ℝ) := by field_simp
      _ ≤ _ := hN
  have hF : ∀ᶠ N : ℕ in atTop, Real.log (Nat.ceil ((N : ℝ) ^ kappa1) : ℝ) / Real.log (N : ℝ) -
      kappa1 ≤ ε * kappa1 / (16 * (M * L)) := by
    have hb := eventually_ceil_coord (c := kappa1) (le_refl kappa1)
      (ε' := ε * kappa1 / (32 * (M * L))) (by positivity)
    filter_upwards [hb] with N hN
    have h2 : ε * kappa1 / (32 * (M * L)) ≤ ε * kappa1 / (16 * (M * L)) := by
      have h1 : ε * kappa1 / (32 * (M * L)) = ε * kappa1 / (16 * (M * L)) * (1 / 2) := by
        field_simp
        ring
      have h3 : (0 : ℝ) ≤ ε * kappa1 / (16 * (M * L)) := by positivity
      linarith
    linarith [(abs_le.1 hN).2, h2]
  have hG : ∀ᶠ N : ℕ in atTop, 22 / (kappa1 * Real.log (N : ℝ)) ≤ 1 := by
    have h := eventually_div_log_le (c := 22 / kappa1) (lam := 1) (by norm_num)
    filter_upwards [h] with N hN
    calc 22 / (kappa1 * Real.log (N : ℝ)) = (22 / kappa1) / Real.log (N : ℝ) := by field_simp
      _ ≤ 1 := hN
  have hH : ∀ᶠ N : ℕ in atTop, 8 * M * (L + 1) / ε ≤ (N : ℝ) ^ kappa1 := by
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
      (tendsto_rpow_atTop hk1).comp tendsto_natCast_atTop_atTop
    exact hpow.eventually_ge_atTop _
  have hI : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (kappa2 - kappa1) := by
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (kappa2 - kappa1)) atTop atTop :=
      (tendsto_rpow_atTop hkd).comp tendsto_natCast_atTop_atTop
    exact hpow.eventually_ge_atTop _
  have hJ : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ kappa1 := by
    have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
      (tendsto_rpow_atTop hk1).comp tendsto_natCast_atTop_atTop
    exact hpow.eventually_ge_atTop _
  have hE : ∀ᶠ N : ℕ in atTop,
      (1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ (kappa2 - kappa1) / n) ∧
      (22 / (kappa1 * Real.log (N : ℝ)) ≤
        ε / (32 * (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1))) ∧
      (kappa2 - Real.log ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) / Real.log (N : ℝ) ≤
        min (ε * kappa1 / (32 * M * (L + 1))) (ε * kappa1 / (16 * (M * L)))) ∧
      (22 / (kappa1 * Real.log (N : ℝ)) ≤
        ε / (8 * (M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L + M * L) * (n : ℝ))) ∧
      (Real.log (Nat.ceil ((N : ℝ) ^ kappa1) : ℝ) / Real.log (N : ℝ) - kappa1 ≤
        ε * kappa1 / (16 * (M * L))) ∧
      (22 / (kappa1 * Real.log (N : ℝ)) ≤ 1) ∧
      (8 * M * (L + 1) / ε ≤ (N : ℝ) ^ kappa1) ∧
      (2 ≤ (N : ℝ) ^ (kappa2 - kappa1)) ∧
      (2 ≤ (N : ℝ) ^ kappa1) := by
    filter_upwards [hA, hB, hC, hD, hF, hG, hH, hI, hJ] with N hA' hB' hC' hD' hF' hG' hH' hI' hJ'
    exact ⟨hA', hB', hC', hD', hF', hG', hH', hI', hJ'⟩
  obtain ⟨NA, hNA⟩ := eventually_atTop.1 hE
  refine ⟨max NA 2, fun N hNm => ?_⟩
  obtain ⟨hA', hB', hC', hD', hF', hG', hH', hI', hJ'⟩ := hNA N (le_trans (le_max_left _ _) hNm)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hNm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLg : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  rw [Real.dist_eq]
  obtain ⟨hceil1, hBlt⟩ := ceil_facts hN2
  -- ### the cutoffs
  set AA : ℕ := Nat.ceil ((N : ℝ) ^ kappa1) with hAA
  set BB : ℕ := Nat.ceil ((N : ℝ) ^ kappa2) - 1 with hBB
  have hAA2 : 2 ≤ AA := by
    rw [hAA]
    exact Nat.lt_ceil.mpr (by push_cast; linarith [hJ'])
  have hloAA : (N : ℝ) ^ kappa1 ≤ (AA : ℝ) := by rw [hAA]; exact Nat.le_ceil _
  have hBBle : (BB : ℝ) ≤ (N : ℝ) ^ kappa2 := by rw [hBB]; exact le_of_lt hBlt
  have hAAleBB : AA ≤ BB := by
    rw [hAA, hBB]
    have h1 : (N : ℝ) ^ kappa1 + 2 ≤ (N : ℝ) ^ kappa2 := by
      have h2 : (N : ℝ) ^ kappa2 = (N : ℝ) ^ kappa1 * (N : ℝ) ^ (kappa2 - kappa1) := by
        rw [← Real.rpow_add (by positivity)]
        ring_nf
      nlinarith [hI', hJ']
    have h3 : (N : ℝ) ^ kappa1 ≤ (Nat.ceil ((N : ℝ) ^ kappa1) : ℝ) := Nat.le_ceil _
    have h4 : 1 ≤ Nat.ceil ((N : ℝ) ^ kappa2) :=
      Nat.one_le_ceil_iff.2 (rpow_pos_of_pos hN0 _)
    have h5 : ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) =
        (Nat.ceil ((N : ℝ) ^ kappa2) : ℝ) - 1 := by
      rw [Nat.cast_sub h4]; norm_num
    have h6 : (N : ℝ) ^ kappa2 ≤ (Nat.ceil ((N : ℝ) ^ kappa2) : ℝ) := Nat.le_ceil _
    have h8 : ((Nat.ceil ((N : ℝ) ^ kappa1) : ℕ) : ℝ) < (N : ℝ) ^ kappa1 + 1 :=
      Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ kappa1)
    have h7 : ((Nat.ceil ((N : ℝ) ^ kappa1) : ℕ) : ℝ) ≤
        ((Nat.ceil ((N : ℝ) ^ kappa2) - 1 : ℕ) : ℝ) := by
      rw [h5]
      linarith [h1, h6, h8]
    exact_mod_cast h7
  have hBB1 : 1 ≤ BB := le_trans (by omega : 1 ≤ AA) hAAleBB
  have hlogAA : (0 : ℝ) < Real.log (AA : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < AA))
  have hlogBB : (0 : ℝ) < Real.log (BB : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < BB))
  -- ### the weight and the inner sum
  set W : ℝ → ℝ := fun t => ∫ u in t..kappa2, g (t, u) / u with hW
  have hWbd' : ∀ t ∈ Icc kappa1 kappa2, |W t| ≤ M * L := fun t ht => by
    rw [hW]; exact hWbd t ht
  have hWmod' : ∀ t ∈ Icc kappa1 kappa2, ∀ t' ∈ Icc kappa1 kappa2, |t - t'| ≤ h →
      |W t - W t'| ≤ M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L :=
    fun t ht t' ht' hd => by rw [hW]; exact hWmod t ht t' ht' hd
  have hcontW' : ContinuousOn W (Icc kappa1 kappa2) := by rw [hW]; exact hcontW
  set Psi : ℕ → ℝ := fun p => ∑ q ∈ (Finset.Ioc p BB).filter Nat.Prime,
      g (Real.log (p : ℝ) / Real.log N, Real.log (q : ℝ) / Real.log N) / (q : ℝ) with hPsi
  -- ### step 1: the pair sum as an iterated sum
  have hSum : (∑ p ∈ fullPairs4 N, g (Real.log (p.1 : ℝ) / Real.log N,
        Real.log (p.2 : ℝ) / Real.log N) / ((p.1 : ℝ) * p.2))
      = ∑ p ∈ (Finset.Ioc (AA - 1) BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p := by
    rw [hAA, hBB, hPsi]
    rw [fullPairs4_sum_iterated hN2 (F := fun z : ℕ × ℕ =>
      g (Real.log (z.1 : ℝ) / Real.log N, Real.log (z.2 : ℝ) / Real.log N) /
        ((z.1 : ℝ) * (z.2 : ℝ)))]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hq2 : 2 ≤ q := (Finset.mem_filter.mp hq).2.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    field_simp
  -- ### step 2: split off the single lower-cutoff term
  have hsplit : (∑ p ∈ (Finset.Ioc (AA - 1) BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
      = (∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
        + ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p := by
    have h := Finset.sum_Ioc_consecutive
      (f := fun p : ℕ => if p.Prime then (1 / (p : ℝ)) * Psi p else 0)
      (by omega : AA - 1 ≤ AA) hAAleBB
    simp only [Finset.sum_filter] at h ⊢
    exact h.symm
  -- ### step 3: the reciprocal mass of the band
  have hmass : (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, 1 / (p : ℝ)) ≤ L + 1 := by
    have h1 := cell_mass_error hN2 hAA2 hAAleBB
    have hint : (∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
        (Real.log (BB : ℝ) / Real.log (N : ℝ)), 1 / t) =
        Real.log ((Real.log (BB : ℝ) / Real.log (N : ℝ)) /
          (Real.log (AA : ℝ) / Real.log (N : ℝ))) :=
      integral_one_div_of_pos (div_pos hlogAA hLg) (div_pos hlogBB hLg)
    have hlogr : Real.log ((Real.log (BB : ℝ) / Real.log (N : ℝ)) /
        (Real.log (AA : ℝ) / Real.log (N : ℝ))) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log (by positivity)
      have hα : kappa1 ≤ Real.log (AA : ℝ) / Real.log (N : ℝ) := by
        rw [le_div_iff₀ hLg]
        have := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) ^ kappa1) hloAA
        rw [Real.log_rpow hN0] at this
        linarith
      have hβ : Real.log (BB : ℝ) / Real.log (N : ℝ) ≤ kappa2 := by
        rw [div_le_iff₀ hLg]
        have := Real.log_le_log (by positivity : (0 : ℝ) < (BB : ℝ)) hBBle
        rw [Real.log_rpow hN0] at this
        linarith
      have h1 : (Real.log (BB : ℝ) / Real.log (N : ℝ)) /
          (Real.log (AA : ℝ) / Real.log (N : ℝ)) ≤
          kappa2 / (Real.log (AA : ℝ) / Real.log (N : ℝ)) :=
        (div_le_div_iff_of_pos_right (div_pos hlogAA hLg)).2 hβ
      have h2 : kappa2 / (Real.log (AA : ℝ) / Real.log (N : ℝ)) ≤ kappa2 / kappa1 :=
        (div_le_div_iff_of_pos_left (by linarith : (0 : ℝ) < kappa2)
          (div_pos hlogAA hLg) hk1).2 hα
      linarith
    have herr : 22 / Real.log (AA : ℝ) ≤ 1 := by
      have h3 : kappa1 * Real.log (N : ℝ) ≤ Real.log (AA : ℝ) := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) ^ kappa1) hloAA
        rw [Real.log_rpow hN0] at h
        linarith
      calc 22 / Real.log (AA : ℝ) ≤ 22 / (kappa1 * Real.log (N : ℝ)) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
        _ ≤ 1 := hG'
    have := (abs_le.1 h1).2
    rw [hint] at this
    linarith
  -- ### step 4: the inner sum is bounded
  have hPsiM : ∀ p : ℕ, AA ≤ p → |Psi p| ≤ M * (L + 1) := by
    intro p hp
    rw [hPsi]
    calc |(∑ q ∈ (Finset.Ioc p BB).filter Nat.Prime,
          g (Real.log (p : ℝ) / Real.log N, Real.log (q : ℝ) / Real.log N) / (q : ℝ))|
        ≤ ∑ q ∈ (Finset.Ioc p BB).filter Nat.Prime,
          |g (Real.log (p : ℝ) / Real.log N, Real.log (q : ℝ) / Real.log N) / (q : ℝ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ (Finset.Ioc p BB).filter Nat.Prime, M * (1 / (q : ℝ)) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          obtain ⟨hIocq, hqP⟩ := Finset.mem_filter.mp hq
          obtain ⟨hpq, hqB⟩ := Finset.mem_Ioc.mp hIocq
          have hq2 : 2 ≤ q := hqP.two_le
          have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
          have hqlo : (N : ℝ) ^ kappa1 ≤ (q : ℝ) :=
            le_trans hloAA (by exact_mod_cast (by omega : AA ≤ q))
          have hqhi : (q : ℝ) ≤ (N : ℝ) ^ kappa2 := le_trans (by exact_mod_cast hqB) hBBle
          have hpc : (Real.log (p : ℝ) / Real.log N) ∈ Icc kappa1 kappa2 := by
            refine coord_bounds hN2 (by omega) (le_trans hloAA (by exact_mod_cast hp)) ?_
            exact le_trans (by exact_mod_cast (by omega : p ≤ BB)) hBBle
          have hqc := coord_bounds hN2 hq2 hqlo hqhi
          have hmem : (Real.log (p : ℝ) / Real.log N, Real.log (q : ℝ) / Real.log N) ∈
              Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2 := ⟨hpc, hqc⟩
          rw [abs_div, abs_of_pos hq0]
          calc |g (Real.log (p : ℝ) / Real.log N, Real.log (q : ℝ) / Real.log N)| / (q : ℝ)
              ≤ M / (q : ℝ) := div_le_div_of_nonneg_right (hMb _ hmem) hq0.le
            _ = M * (1 / (q : ℝ)) := by ring
      _ = M * (∑ q ∈ (Finset.Ioc p BB).filter Nat.Prime, 1 / (q : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ M * (L + 1) := by
          apply mul_le_mul_of_nonneg_left _ hM0.le
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hmass
          · intro q hq
            obtain ⟨hIocq, hqP⟩ := Finset.mem_filter.mp hq
            exact Finset.mem_filter.2
              ⟨Finset.mem_Ioc.2 ⟨by linarith [(Finset.mem_Ioc.mp hIocq).1],
                (Finset.mem_Ioc.mp hIocq).2⟩, hqP⟩
          · intro q _ _; positivity
  -- ### step 5: split off the single term and bound it
  have hsingle : |(∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)| ≤ ε / 8 := by
    have hsub : (Finset.Ioc (AA - 1) AA).filter Nat.Prime ⊆ {AA} := by
      intro p hp
      obtain ⟨hIoc, -⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_singleton.2 (by
        have h1 := (Finset.mem_Ioc.mp hIoc).1
        have h2 := (Finset.mem_Ioc.mp hIoc).2
        omega)
    have hb : ∀ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime,
        |(1 / (p : ℝ)) * Psi p| ≤ M * (L + 1) / (AA : ℝ) := by
      intro p hp
      have hpe : p = AA := Finset.mem_singleton.1 (hsub hp)
      subst hpe
      have h1 : |Psi AA| ≤ M * (L + 1) := hPsiM AA le_rfl
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (AA : ℝ))]
      calc (1 / (AA : ℝ)) * |Psi AA| ≤ (1 / (AA : ℝ)) * (M * (L + 1)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M * (L + 1) / (AA : ℝ) := by ring
    have hcard : ((Finset.Ioc (AA - 1) AA).filter Nat.Prime).card ≤ 1 := by
      have h := Finset.card_le_card hsub
      simpa using h
    calc |(∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)|
        ≤ ∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, |(1 / (p : ℝ)) * Psi p| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, M * (L + 1) / (AA : ℝ) :=
          Finset.sum_le_sum hb
      _ = (((Finset.Ioc (AA - 1) AA).filter Nat.Prime).card : ℝ) * (M * (L + 1) / (AA : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (M * (L + 1) / (AA : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ = M * (L + 1) / (AA : ℝ) := by ring
      _ ≤ ε / 8 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (AA : ℝ))]
          have h2 : 8 * M * (L + 1) / ε ≤ (N : ℝ) ^ kappa1 := hH'
          rw [div_le_iff₀ hε] at h2
          nlinarith [h2, hloAA]
  -- ### the per-`p` inner bound
  have hDelta : ∀ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
      |Psi p - W (Real.log (p : ℝ) / Real.log N)| ≤
        2 * (ε / (64 * L * (L + 1) * (L + 1))) * L
          + (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) *
              (22 / (kappa1 * Real.log (N : ℝ)))
          + M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 := by
    intro p hp
    obtain ⟨hIoc, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hAp, hpB⟩ := Finset.mem_Ioc.mp hIoc
    have hp2 : 2 ≤ p := hpP.two_le
    have hpN : (N : ℝ) ^ kappa1 ≤ (p : ℝ) := le_trans hloAA (by exact_mod_cast hAp.le)
    have hpBB : (p : ℝ) ≤ (BB : ℝ) := by exact_mod_cast hpB
    have hlp0' : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    set lp : ℝ := Real.log (p : ℝ) / Real.log N with hlp
    have hlp0 : 0 < lp := div_pos hlp0' hLg
    have hpc : lp ∈ Icc kappa1 kappa2 := by
      rw [hlp]
      exact coord_bounds hN2 hp2 hpN (le_trans hpBB hBBle)
    set bta : ℝ := Real.log (BB : ℝ) / Real.log N with hbta
    have hbta_le : bta ≤ kappa2 := by
      rw [hbta, div_le_iff₀ hLg]
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (BB : ℝ)) hBBle
      rw [Real.log_rpow hN0] at h
      linarith
    have hlp_le_bta : lp ≤ bta := by
      rw [hlp, hbta]
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) hpBB) hLg.le
    have hcont_p : ContinuousOn (fun u : ℝ => g (lp, u)) (Icc kappa1 kappa2) := by
      have hp2c : ContinuousOn (fun u : ℝ => (lp, u)) (Icc kappa1 kappa2) := by fun_prop
      exact hg.comp hp2c (fun u hu => ⟨hpc, hu⟩)
    have hbd_p : ∀ u ∈ Icc kappa1 kappa2, |g (lp, u)| ≤ M := fun u hu => hMb _ ⟨hpc, hu⟩
    have hmod_p : ∀ t ∈ Icc kappa1 kappa2, ∀ u ∈ Icc kappa1 kappa2, |t - u| ≤ h →
        |g (lp, t) - g (lp, u)| ≤ ε / (64 * L * (L + 1) * (L + 1)) := by
      intro t ht u hu hd
      exact hmodh (lp, t) ⟨hpc, ht⟩ (lp, u) ⟨hpc, hu⟩ (by
        rw [Prod.dist_eq, max_le_iff]
        exact ⟨by simpa using hh0.le, by rw [Real.dist_eq]; exact hd⟩)
    have hspanp : (bta - lp) / (n : ℝ) +
        1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ h := by
      have h1 : bta - lp ≤ kappa2 - kappa1 := by linarith [hbta_le, hpc.1]
      have h2 : (bta - lp) / (n : ℝ) ≤ (kappa2 - kappa1) / (n : ℝ) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : (kappa2 - kappa1) / (n : ℝ) + (kappa2 - kappa1) / (n : ℝ) =
          2 * (kappa2 - kappa1) / (n : ℝ) := by ring
      rw [hhdef]
      linarith [h2, hA', h3]
    have hstep := prime_reciprocal_step (φ := fun u : ℝ => g (lp, u)) (C := M)
      (η := ε / (64 * L * (L + 1) * (L + 1))) (h := h) hM0.le hη₁0.le hh0
      hcont_p hbd_p hmod_p n hn1 N hN2 p BB hp2 hpN hBBle hpBB hspanp
    have hlogr : Real.log (bta / lp) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log (by positivity)
      have h1 : bta / lp ≤ kappa2 / lp := (div_le_div_iff_of_pos_right hlp0).2 hbta_le
      have h2 : kappa2 / lp ≤ kappa2 / kappa1 :=
        (div_le_div_iff_of_pos_left (by linarith : (0 : ℝ) < kappa2) hlp0 hk1).2 hpc.1
      linarith
    have hstep' : |Psi p - (∫ u in lp..bta, g (lp, u) / u)| ≤
        2 * (ε / (64 * L * (L + 1) * (L + 1))) * L
          + (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) *
              (22 / (kappa1 * Real.log (N : ℝ))) := by
      refine hstep.trans ?_
      have h4 : 2 * (ε / (64 * L * (L + 1) * (L + 1))) * Real.log (bta / lp) ≤
          2 * (ε / (64 * L * (L + 1) * (L + 1))) * L :=
        mul_le_mul_of_nonneg_left hlogr (by positivity)
      simp only [hbta, hlp] at h4
      linarith [h4]
    have htail : |(∫ u in lp..bta, g (lp, u) / u) - W lp| ≤
        M * (kappa2 - bta) / kappa1 := by
      have hβmem : bta ∈ Icc kappa1 kappa2 := ⟨le_trans hpc.1 hlp_le_bta, hbta_le⟩
      have hsp := intervalIntegral.integral_add_adjacent_intervals
        (slice_integrable hg hpc lp bta hpc hβmem)
        (slice_integrable hg hpc bta kappa2 hβmem ⟨hk12.le, le_refl kappa2⟩)
      have hWv : W lp = (∫ u in lp..bta, g (lp, u) / u) +
          ∫ u in bta..kappa2, g (lp, u) / u := by
        rw [hW]
        exact hsp.symm
      rw [hWv]
      have htv : |(∫ u in bta..kappa2, g (lp, u) / u)| ≤ M * (kappa2 - bta) / kappa1 :=
        slice_norm_le hg hMb hM0.le hpc hβmem ⟨hk12.le, le_refl kappa2⟩ hbta_le
      have e : (∫ u in lp..bta, g (lp, u) / u) -
          ((∫ u in lp..bta, g (lp, u) / u) + ∫ u in bta..kappa2, g (lp, u) / u) =
          -(∫ u in bta..kappa2, g (lp, u) / u) := by ring
      rw [e, abs_neg]
      exact htv
    have htri : |Psi p - W lp| ≤ |Psi p - (∫ u in lp..bta, g (lp, u) / u)| +
        |(∫ u in lp..bta, g (lp, u) / u) - W lp| := by
      have e : Psi p - W lp = (Psi p - (∫ u in lp..bta, g (lp, u) / u)) +
          ((∫ u in lp..bta, g (lp, u) / u) - W lp) := by ring
      rw [e]
      exact abs_add_le _ _
    simp only [hlp, hbta] at htri hstep' htail ⊢
    linarith [htri, hstep', htail]

  -- ### abbreviations for the error constants
  set e1 : ℝ := ε / (64 * L * (L + 1) * (L + 1)) with he1
  have he10 : 0 < e1 := by rw [he1]; positivity
  have hbta_le : Real.log (BB : ℝ) / Real.log (N : ℝ) ≤ kappa2 := by
    rw [div_le_iff₀ hLg]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (BB : ℝ)) hBBle
    rw [Real.log_rpow hN0] at h
    linarith
  have halpha_ge : kappa1 ≤ Real.log (AA : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hLg]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) ^ kappa1) hloAA
    rw [Real.log_rpow hN0] at h
    linarith
  set Δ : ℝ := 2 * e1 * L + (e1 + M) * (n : ℝ) * (22 / (kappa1 * Real.log (N : ℝ)))
      + M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 with hDel
  have hDel0 : 0 ≤ Δ := by
    rw [hDel]
    have hp1 : (0 : ℝ) ≤ 2 * e1 * L := by linarith [he10, hL0]
    have hp2 : (0 : ℝ) ≤ (e1 + M) * (n : ℝ) * (22 / (kappa1 * Real.log (N : ℝ))) := by
      have := he10
      positivity
    have hp3 : (0 : ℝ) ≤ M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 :=
      div_nonneg (mul_nonneg hM0.le (by linarith [hbta_le])) hk1.le
    linarith
  have hDelta' : ∀ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
      |Psi p - W (Real.log (p : ℝ) / Real.log N)| ≤ Δ := by
    intro p hp
    rw [hDel, he1]
    exact hDelta p hp

  -- ### the sum-level inner bound
  have hinner_le : |(∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
      - (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
          (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))| ≤ ε / 4 := by
    have heq : (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
        - (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
            (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N)) =
        ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
          (1 / (p : ℝ)) * (Psi p - W (Real.log (p : ℝ) / Real.log N)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [heq]
    have h1 : (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
          |(1 / (p : ℝ)) * (Psi p - W (Real.log (p : ℝ) / Real.log N))|)
        ≤ ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, Δ * (1 / (p : ℝ)) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      have hpp : (0 : ℝ) < 1 / (p : ℝ) := by
        have := (Finset.mem_filter.mp hp).2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
        positivity
      rw [abs_mul, abs_of_pos hpp]
      calc (1 / (p : ℝ)) * |Psi p - W (Real.log (p : ℝ) / Real.log N)|
          ≤ (1 / (p : ℝ)) * Δ := mul_le_mul_of_nonneg_left (hDelta' p hp) hpp.le
        _ = Δ * (1 / (p : ℝ)) := by ring
    have h2 : (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, Δ * (1 / (p : ℝ)))
        = Δ * (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, 1 / (p : ℝ)) := by
      rw [Finset.mul_sum]
    have h3 : Δ * (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, 1 / (p : ℝ)) ≤ Δ * (L + 1) :=
      mul_le_mul_of_nonneg_left hmass hDel0
    have hA : 2 * e1 * L * (L + 1) ≤ ε / 32 := by
      have hkey : 2 * e1 * L * (L + 1) = ε / (32 * (L + 1)) := by
        rw [he1]
        field_simp
        ring
      rw [hkey]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * (L + 1))]
      have e2 : ε / 32 * (32 * (L + 1)) = ε * (L + 1) := by field_simp
      rw [e2]
      nlinarith [hε.le, hL0.le]
    have hBv : (e1 + M) * (n : ℝ) * (22 / (kappa1 * Real.log (N : ℝ))) * (L + 1) ≤ ε / 32 := by
      rw [he1]
      have h0 : (0 : ℝ) < (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1) := by
        have := hn1
        have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        positivity
      have hfin : ε / (32 * (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1)) *
          ((ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1)) = ε / 32 := by
        field_simp
      have hcomm : (ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) *
            (22 / (kappa1 * Real.log (N : ℝ))) * (L + 1)
          = 22 / (kappa1 * Real.log (N : ℝ)) *
              ((ε / (64 * L * (L + 1) * (L + 1)) + M) * (n : ℝ) * (L + 1)) := by ring
      rw [hcomm, ← hfin]
      exact mul_le_mul_of_nonneg_right hB' h0.le
    have hCv : M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 * (L + 1) ≤ ε / 32 := by
      have hle : kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ) ≤
          ε * kappa1 / (32 * M * (L + 1)) := hC'.trans (min_le_left _ _)
      have h0 : (0 : ℝ) < M / kappa1 * (L + 1) := by positivity
      have hb := mul_le_mul_of_nonneg_right hle h0.le
      calc M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 * (L + 1)
          = (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) * (M / kappa1 * (L + 1)) := by ring
        _ ≤ (ε * kappa1 / (32 * M * (L + 1))) * (M / kappa1 * (L + 1)) := hb
        _ = ε / 32 := by field_simp
    have h4 : Δ * (L + 1) ≤ ε / 4 := by
      rw [hDel]
      have hexp : (2 * e1 * L + (e1 + M) * (n : ℝ) * (22 / (kappa1 * Real.log (N : ℝ)))
            + M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1) * (L + 1)
          = 2 * e1 * L * (L + 1)
            + (e1 + M) * (n : ℝ) * (22 / (kappa1 * Real.log (N : ℝ))) * (L + 1)
            + M * (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 * (L + 1) := by ring
      rw [hexp]
      linarith [hA, hBv, hCv]
    calc |∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
          ((1 / (p : ℝ)) * (Psi p - W (Real.log (p : ℝ) / Real.log N)))|
        ≤ ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
          |(1 / (p : ℝ)) * (Psi p - W (Real.log (p : ℝ) / Real.log N))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, Δ * (1 / (p : ℝ)) := h1
      _ = Δ * (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, 1 / (p : ℝ)) := h2
      _ ≤ Δ * (L + 1) := h3
      _ ≤ ε / 4 := h4

  -- ### the outer application of partial summation to the weight `W`
  have hWmod'' : ∀ t ∈ Icc kappa1 kappa2, ∀ t' ∈ Icc kappa1 kappa2,
      |t - t'| ≤ h → |W t - W t'| ≤ M * h / kappa1 + e1 * L := by
    intro t ht t' ht' hd
    rw [he1]
    exact hWmod' t ht t' ht' hd
  have hspan_outer :
      (Real.log (BB : ℝ) / Real.log (N : ℝ) - Real.log (AA : ℝ) / Real.log (N : ℝ)) / (n : ℝ)
        + 1 / ((N : ℝ) ^ kappa1 * Real.log (N : ℝ)) ≤ h := by
    have h1 : Real.log (BB : ℝ) / Real.log (N : ℝ) - Real.log (AA : ℝ) / Real.log (N : ℝ)
        ≤ kappa2 - kappa1 := by linarith [hbta_le, halpha_ge]
    have h2 : (Real.log (BB : ℝ) / Real.log (N : ℝ) - Real.log (AA : ℝ) / Real.log (N : ℝ))
          / (n : ℝ) ≤ (kappa2 - kappa1) / (n : ℝ) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h3 : (kappa2 - kappa1) / (n : ℝ) + (kappa2 - kappa1) / (n : ℝ)
        = 2 * (kappa2 - kappa1) / (n : ℝ) := by ring
    rw [hhdef]
    linarith [h2, hA', h3]
  have houter := prime_reciprocal_step (φ := W) (C := M * L)
    (η := M * h / kappa1 + e1 * L) (h := h)
    (by positivity) (by positivity) hh0 hcontW' hWbd' hWmod'' n hn1 N hN2 AA BB hAA2
    hloAA hBBle (by exact_mod_cast hAAleBB) hspan_outer
  have hlogratio : Real.log ((Real.log (BB : ℝ) / Real.log (N : ℝ)) /
      (Real.log (AA : ℝ) / Real.log (N : ℝ))) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by positivity)
    have h1 : (Real.log (BB : ℝ) / Real.log (N : ℝ)) / (Real.log (AA : ℝ) / Real.log (N : ℝ))
        ≤ kappa2 / (Real.log (AA : ℝ) / Real.log (N : ℝ)) :=
      (div_le_div_iff_of_pos_right (div_pos hlogAA hLg)).2 hbta_le
    have h2 : kappa2 / (Real.log (AA : ℝ) / Real.log (N : ℝ)) ≤ kappa2 / kappa1 :=
      (div_le_div_iff_of_pos_left (by linarith : (0 : ℝ) < kappa2)
        (div_pos hlogAA hLg) hk1).2 halpha_ge
    linarith
  have hout1 : 2 * (M * h / kappa1 + e1 * L) *
      Real.log ((Real.log (BB : ℝ) / Real.log (N : ℝ)) /
        (Real.log (AA : ℝ) / Real.log (N : ℝ))) ≤ ε / 16 + ε / 32 := by
    have hstep : 2 * (M * h / kappa1 + e1 * L) *
        Real.log ((Real.log (BB : ℝ) / Real.log (N : ℝ)) /
          (Real.log (AA : ℝ) / Real.log (N : ℝ))) ≤ 2 * (M * h / kappa1 + e1 * L) * L :=
      mul_le_mul_of_nonneg_left hlogratio (by positivity)
    have hMh : 2 * (M * h / kappa1) * L ≤ ε / 16 := by
      have e : 2 * (M * h / kappa1) * L
          = 4 * M * (kappa2 - kappa1) * L / ((n : ℝ) * kappa1) := by
        rw [hhdef]; field_simp; ring
      rw [e]
      exact hnM
    have he1L : 2 * (e1 * L) * L ≤ ε / 32 := by
      have e : 2 * (e1 * L) * L = ε * L / (32 * (L + 1) * (L + 1)) := by
        rw [he1]; field_simp; ring
      rw [e]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * (L + 1) * (L + 1))]
      have e2 : ε / 32 * (32 * (L + 1) * (L + 1)) = ε * ((L + 1) * (L + 1)) := by field_simp
      rw [e2]
      have hL2 : L < (L + 1) * (L + 1) := by nlinarith [sq_nonneg L, hL0.le]
      nlinarith [hL2, hε.le]
    have hexp : 2 * (M * h / kappa1 + e1 * L) * L
        = 2 * (M * h / kappa1) * L + 2 * (e1 * L) * L := by ring
    linarith [hstep, hexp, hMh, he1L]
  have hout2 : (M * h / kappa1 + e1 * L + M * L) * (n : ℝ) *
      (22 / (kappa1 * Real.log (N : ℝ))) ≤ ε / 8 := by
    have hc : (0 : ℝ) < (M * h / kappa1 + e1 * L + M * L) * (n : ℝ) := by
      have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have := he10
      positivity
    have hD'' : 22 / (kappa1 * Real.log (N : ℝ)) ≤
        ε / (8 * ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ))) := by
      have e : (8 * (M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L + M * L) * (n : ℝ))
          = 8 * ((M * h / kappa1 + ε / (64 * L * (L + 1) * (L + 1)) * L + M * L) * (n : ℝ)) := by
        ring
      rw [e] at hD'
      simpa [he1] using hD'
    have hfin : ε / (8 * ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ))) *
        ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ)) = ε / 8 := by
      have hc' : ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ)) ≠ 0 := hc.ne'
      field_simp
    calc (M * h / kappa1 + e1 * L + M * L) * (n : ℝ) *
          (22 / (kappa1 * Real.log (N : ℝ)))
        = 22 / (kappa1 * Real.log (N : ℝ)) *
            ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ)) := by ring
      _ ≤ ε / (8 * ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ))) *
            ((M * h / kappa1 + e1 * L + M * L) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hD'' hc.le
      _ = ε / 8 := hfin
  have houter_le : |(∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
        W (Real.log (p : ℝ) / Real.log N) / (p : ℝ)) -
      ∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
        (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t| ≤ ε / 4 :=
    le_trans houter (by linarith [hout1, hout2])

  -- ### the endpoint correction: the sliver integrals of `W t / t`
  have hWquot_cont : ContinuousOn (fun t : ℝ => W t / t) (Icc kappa1 kappa2) := by
    refine hcontW'.div continuousOn_id (fun t ht => ?_)
    exact (lt_of_lt_of_le hk1 ht.1).ne'
  have hWquot_int : ∀ a b : ℝ, a ∈ Icc kappa1 kappa2 → b ∈ Icc kappa1 kappa2 →
      IntervalIntegrable (fun t : ℝ => W t / t) volume a b := by
    intro a b ha hb
    refine (show ContinuousOn (fun t : ℝ => W t / t) (Set.uIcc a b) from ?_).intervalIntegrable
    refine hWquot_cont.mono (fun t ht => ?_)
    rw [Set.uIcc, Set.mem_Icc] at ht
    exact ⟨(le_min ha.1 hb.1).trans ht.1, ht.2.trans (max_le ha.2 hb.2)⟩
  have halpha_le : Real.log (AA : ℝ) / Real.log (N : ℝ) ≤ Real.log (BB : ℝ) / Real.log (N : ℝ) := by
    rw [div_le_div_iff_of_pos_right hLg]
    exact Real.log_le_log (by positivity : (0 : ℝ) < (AA : ℝ)) (by exact_mod_cast hAAleBB)
  have hsliver1 : |∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t| ≤ ε / 16 := by
    have ha : kappa1 ≤ Real.log (AA : ℝ) / Real.log (N : ℝ) := halpha_ge
    have ha2 : Real.log (AA : ℝ) / Real.log (N : ℝ) ∈ Icc kappa1 kappa2 := ⟨ha, by linarith⟩
    have hstep : |∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t| ≤
        M * L * Real.log ((Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1) := by
      calc |∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t|
          ≤ ∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), |W t / t| :=
            intervalIntegral.abs_integral_le_integral_abs ha
        _ ≤ ∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), M * L / t := by
            refine intervalIntegral.integral_mono_on ha ?_ ?_ (fun t ht => ?_)
            · exact IntervalIntegrable.abs
                (hWquot_int kappa1 _ ⟨le_refl kappa1, hk12.le⟩ ha2)
            · refine (show ContinuousOn (fun t : ℝ => M * L / t)
                (Set.uIcc kappa1 _) from ?_).intervalIntegrable
              have hu : Set.uIcc kappa1 (Real.log (AA : ℝ) / Real.log (N : ℝ))
                  ⊆ Icc kappa1 kappa2 := by
                intro t ht
                rw [Set.uIcc, Set.mem_Icc] at ht
                exact ⟨(le_min (le_refl kappa1) ha).trans ht.1, ht.2.trans (max_le hk12.le ha2.2)⟩
              exact continuousOn_const.div continuousOn_id
                (fun t ht => (lt_of_lt_of_le hk1 (hu ht).1).ne')
            · have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hk1 ht.1
              rw [abs_div, abs_of_pos ht0]
              exact div_le_div_of_nonneg_right (hWbd' t ⟨ht.1, ht.2.trans ha2.2⟩) ht0.le
        _ = M * L * Real.log ((Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1) := by
            have h1 : (∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), M * L / t)
                = M * L * ∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), 1 / t := by
              rw [← intervalIntegral.integral_const_mul (M * L) (fun t : ℝ => 1 / t)]
              congr 1
              ext t
              ring
            rw [h1, integral_one_div_of_pos hk1 (div_pos hlogAA hLg)]
    have hsl : Real.log (AA : ℝ) / Real.log (N : ℝ) - kappa1 ≤ ε * kappa1 / (16 * (M * L)) := hF'
    have hlog : M * L * Real.log ((Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1) ≤ ε / 16 := by
      have hpos : (0 : ℝ) < (Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1 :=
        div_pos (lt_of_lt_of_le hk1 ha) hk1
      have h1 : Real.log ((Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1) ≤
          (Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1 - 1 :=
        Real.log_le_sub_one_of_pos hpos
      have h2 : (Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1 - 1
          = (Real.log (AA : ℝ) / Real.log (N : ℝ) - kappa1) / kappa1 := by field_simp
      have h3 : (Real.log (AA : ℝ) / Real.log (N : ℝ) - kappa1) / kappa1
          ≤ (ε * kappa1 / (16 * (M * L))) / kappa1 :=
        div_le_div_of_nonneg_right hsl hk1.le
      have h4 : (ε * kappa1 / (16 * (M * L))) / kappa1 = ε / (16 * (M * L)) := by field_simp
      have hlog' : Real.log ((Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1)
          ≤ ε / (16 * (M * L)) := by linarith
      have h5 : M * L * (ε / (16 * (M * L))) = ε / 16 := by field_simp
      calc M * L * Real.log ((Real.log (AA : ℝ) / Real.log (N : ℝ)) / kappa1)
          ≤ M * L * (ε / (16 * (M * L))) := mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ = ε / 16 := h5
    linarith [hstep, hlog]
  have hsliver2 : |∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t| ≤ ε / 16 := by
    have hb : Real.log (BB : ℝ) / Real.log (N : ℝ) ≤ kappa2 := hbta_le
    have hb1 : kappa1 ≤ Real.log (BB : ℝ) / Real.log (N : ℝ) := le_trans halpha_ge halpha_le
    have hb2 : Real.log (BB : ℝ) / Real.log (N : ℝ) ∈ Icc kappa1 kappa2 := ⟨hb1, hb⟩
    have hstep : |∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t| ≤
        M * L * Real.log (kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ))) := by
      calc |∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t|
          ≤ ∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, |W t / t| :=
            intervalIntegral.abs_integral_le_integral_abs hb
        _ ≤ ∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, M * L / t := by
            refine intervalIntegral.integral_mono_on hb ?_ ?_ (fun t ht => ?_)
            · exact IntervalIntegrable.abs (hWquot_int _ kappa2 hb2 ⟨hk12.le, le_refl kappa2⟩)
            · refine (show ContinuousOn (fun t : ℝ => M * L / t)
                (Set.uIcc _ kappa2) from ?_).intervalIntegrable
              have hu : Set.uIcc (Real.log (BB : ℝ) / Real.log (N : ℝ)) kappa2
                  ⊆ Icc kappa1 kappa2 := by
                intro t ht
                rw [Set.uIcc, Set.mem_Icc] at ht
                exact ⟨(le_min hb1 hk12.le).trans ht.1, ht.2.trans (max_le hb (le_refl kappa2))⟩
              exact continuousOn_const.div continuousOn_id
                (fun t ht => (lt_of_lt_of_le hk1 (hu ht).1).ne')
            · have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hk1 (hb1.trans ht.1)
              rw [abs_div, abs_of_pos ht0]
              exact div_le_div_of_nonneg_right (hWbd' t ⟨hb1.trans ht.1, ht.2⟩) ht0.le
        _ = M * L * Real.log (kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ))) := by
            have h1 : (∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, M * L / t)
                = M * L * ∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, 1 / t := by
              rw [← intervalIntegral.integral_const_mul (M * L) (fun t : ℝ => 1 / t)]
              congr 1
              ext t
              ring
            rw [h1, integral_one_div_of_pos (div_pos hlogBB hLg) (lt_of_lt_of_le hk1 hk12.le)]
    have hsl : kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ) ≤ ε * kappa1 / (16 * (M * L)) :=
      hC'.trans (min_le_right _ _)
    have hlog : M * L * Real.log (kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ))) ≤ ε / 16 := by
      have hbs : (0 : ℝ) < Real.log (BB : ℝ) / Real.log (N : ℝ) := lt_of_lt_of_le hk1 hb1
      have hpos : (0 : ℝ) < kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ)) :=
        div_pos (by linarith) hbs
      have h1 : Real.log (kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ))) ≤
          kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos hpos
      have h2 : kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ)) - 1
          = (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) /
              (Real.log (BB : ℝ) / Real.log (N : ℝ)) := by field_simp
      have h3 : (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) /
            (Real.log (BB : ℝ) / Real.log (N : ℝ))
          ≤ (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1 :=
        div_le_div_of_nonneg_left (by linarith [hbta_le]) hk1 hb1
      have h4 : (kappa2 - Real.log (BB : ℝ) / Real.log (N : ℝ)) / kappa1
          ≤ (ε * kappa1 / (16 * (M * L))) / kappa1 := div_le_div_of_nonneg_right hsl hk1.le
      have h5 : (ε * kappa1 / (16 * (M * L))) / kappa1 = ε / (16 * (M * L)) := by field_simp
      have hlog' : Real.log (kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ)))
          ≤ ε / (16 * (M * L)) := by linarith
      have h6 : M * L * (ε / (16 * (M * L))) = ε / 16 := by field_simp
      calc M * L * Real.log (kappa2 / (Real.log (BB : ℝ) / Real.log (N : ℝ)))
          ≤ M * L * (ε / (16 * (M * L))) := mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ = ε / 16 := h6
    linarith [hstep, hlog]
  have hsplit_int : (∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
        (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
      = (∫ t in kappa1..kappa2, W t / t)
        - (∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t)
        - (∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hWquot_int kappa1 _ ⟨le_refl kappa1, hk12.le⟩ ⟨halpha_ge, by linarith⟩)
      (hWquot_int _ _ ⟨halpha_ge, by linarith⟩ ⟨by linarith, hbta_le⟩)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hWquot_int _ _ ⟨halpha_ge, by linarith⟩ ⟨by linarith, hbta_le⟩)
      (hWquot_int _ kappa2 ⟨by linarith, hbta_le⟩ ⟨hk12.le, le_refl kappa2⟩)
    have h3 := intervalIntegral.integral_add_adjacent_intervals
      (hWquot_int kappa1 _ ⟨le_refl kappa1, hk12.le⟩ ⟨halpha_ge, by linarith⟩)
      (hWquot_int _ kappa2 ⟨halpha_ge, by linarith⟩ ⟨hk12.le, le_refl kappa2⟩)
    have e1 : (∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
          (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
        = (∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..kappa2, W t / t)
          - (∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t) := by
      rw [← h2]; ring
    have e2 : (∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..kappa2, W t / t)
        = (∫ t in kappa1..kappa2, W t / t)
          - (∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t) := by
      rw [← h3]; ring
    rw [e1, e2]
  have htarget_shift : |(∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
        (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t) - ∫ t in kappa1..kappa2, W t / t|
      ≤ ε / 8 := by
    rw [hsplit_int]
    have e : (∫ t in kappa1..kappa2, W t / t)
        - (∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t)
        - (∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t)
        - (∫ t in kappa1..kappa2, W t / t)
        = -((∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t)
          + (∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t)) := by ring
    rw [e, abs_neg]
    have h := abs_add_le (∫ t in kappa1..(Real.log (AA : ℝ) / Real.log (N : ℝ)), W t / t)
      (∫ t in (Real.log (BB : ℝ) / Real.log (N : ℝ))..kappa2, W t / t)
    linarith [h, hsliver1, hsliver2]

  -- ### final assembly
  have hWTs : (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
        W (Real.log (p : ℝ) / Real.log N) / (p : ℝ))
      = ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
          (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N) :=
    Finset.sum_congr rfl (fun p _ => by ring)
  have hWsum : |(∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
        (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))
      - ∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
          (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t| ≤ ε / 4 := by
    rw [← hWTs]
    exact houter_le
  have hgoal : |(∑ p ∈ fullPairs4 N, g (Real.log (p.1 : ℝ) / Real.log N,
        Real.log (p.2 : ℝ) / Real.log N) / ((p.1 : ℝ) * p.2))
      - ∫ t in kappa1..kappa2, (∫ u in t..kappa2, g (t, u) / u) / t| ≤ 3 * ε / 4 := by
    have hWint : (∫ t in kappa1..kappa2, (∫ u in t..kappa2, g (t, u) / u) / t)
        = ∫ t in kappa1..kappa2, W t / t := by rw [hW]
    rw [hWint, hSum, hsplit]
    have h2 : |(∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
          - ∫ t in kappa1..kappa2, W t / t| ≤ ε / 4 + ε / 4 + ε / 8 := by
      have hab : (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
            - ∫ t in kappa1..kappa2, W t / t
          = ((∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
              - ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
                (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))
            + (((∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
                (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))
              - ∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
                  (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
              + ((∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
                  (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
                - ∫ t in kappa1..kappa2, W t / t)) := by ring
      rw [hab]
      have hT1 := abs_add_le ((∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
              (1 / (p : ℝ)) * Psi p)
            - ∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
              (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))
          (((∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
              (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))
            - ∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
                (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
            + ((∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
                (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
              - ∫ t in kappa1..kappa2, W t / t))
      have hT2 := abs_add_le ((∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime,
              (1 / (p : ℝ)) * W (Real.log (p : ℝ) / Real.log N))
            - ∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
                (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
          ((∫ t in (Real.log (AA : ℝ) / Real.log (N : ℝ))..
                (Real.log (BB : ℝ) / Real.log (N : ℝ)), W t / t)
            - ∫ t in kappa1..kappa2, W t / t)
      linarith [hT1, hT2, hinner_le, hWsum, htarget_shift]
    have htri : |(∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
          + (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
          - ∫ t in kappa1..kappa2, W t / t|
        ≤ |∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p|
          + |(∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
            - ∫ t in kappa1..kappa2, W t / t| := by
      have e : (∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
            + (∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
            - ∫ t in kappa1..kappa2, W t / t
          = (∑ p ∈ (Finset.Ioc (AA - 1) AA).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
            + ((∑ p ∈ (Finset.Ioc AA BB).filter Nat.Prime, (1 / (p : ℝ)) * Psi p)
              - ∫ t in kappa1..kappa2, W t / t) := by ring
      rw [e]
      exact abs_add_le _ _
    linarith [htri, hsingle, h2]
  refine lt_of_le_of_lt hgoal ?_
  linarith


/-- The residual level kernel is continuous on the entire closed exponent square.
CONDITIONAL ON IsLinearSieve only. -/
theorem lower_kernel_continuous (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ContinuousOn (fun x : ℝ × ℝ => f ((1 / 2 - x.1 - x.2) / kappa1))
      (Icc kappa1 kappa2 ×ˢ Icc kappa1 kappa2) := by
  apply h.2.1.comp
    (((continuous_const.sub continuous_fst).sub continuous_snd).div_const kappa1).continuousOn
  intro x hx
  change 0 < (1 / 2 - x.1 - x.2) / kappa1
  apply div_pos _ (by norm_num [kappa1])
  have hx1 := hx.1.2
  have hx2 := hx.2.2
  norm_num [kappa2] at hx1 hx2
  linarith

/-- The fixed continuous kernel supplies the zero loss reciprocal F4 limit.
OPEN through continuous_prime_triangle. -/
theorem reciprocalFullSum4_zero_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    Tendsto (reciprocalFullSum4 f 0) atTop (𝓝 (lowerIntegral4 f)) := by
  have ht := continuous_prime_triangle
    (fun x : ℝ × ℝ => f ((1 / 2 - x.1 - x.2) / kappa1))
    (lower_kernel_continuous F f h)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  apply sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2, _⟩ := fullPairs4_primes hp
  rw [Task367.lowerLevel_zero_coordinates hN hp1.pos hp2.pos]

/-- The exact sealed lowerSum4_tendsto target follows from the smaller fixed
continuous kernel leaf and the proved elementary error estimates.
OPEN only through continuous_prime_triangle. -/
theorem lowerSum4_tendsto_supplied (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  exact lowerSum4_of_zero_loss F f h B hB
    (tendsto_inf_left (reciprocalFullSum4_zero_tendsto F f h))

end LeanLab.ChenDoubleSieve.Task366
