import LeanLab.ExceptionalSet.Decomp371b

/-!
P0082 pages 365 and 366 displays 25 to 27. Separate the moment expansion,
the distant frequency estimate and the nearby frequency estimate.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp404e

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.DecompJ200
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)

/-- P0082 page 365 display 24. The truncated minor arc domain. -/
noncomputable def truncatedDomain (P X : ℝ) : Set ℝ :=
  (majorArcs P X)ᶜ ∩ Set.Icc (-P) P

/-- P0082 page 365 after display 25. The full dyadic index phase sum. -/
noncomputable def phaseSum (γ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (N / 2) N, eC (t * F γ n)

/-- P0082 page 366, contribution to display 26 with distant frequencies.
The integrand is the absolute majorant of the expanded complex integrand. -/
noncomputable def farMoment (γ δ κ : ℝ) (N : ℕ) : ℝ :=
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  ∫ α in truncatedDomain P X,
    ∫ β in truncatedDomain P X ∩ {β : ℝ | X ^ (3 * δ - 1) < |α - β|},
      ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖ *
        ‖Sp P X β ^ 2 * (Kfun Δ β : ℂ)‖ * ‖phaseSum γ N (β - α)‖

/-- P0082 page 366 display 27, contribution with nearby frequencies.
The boundary is included here, so this and farMoment cover the full pair domain. -/
noncomputable def nearMoment (γ δ κ : ℝ) (N : ℕ) : ℝ :=
  let X := F γ N
  let P := X ^ (6 * δ)
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  ∫ α in truncatedDomain P X,
    ∫ β in truncatedDomain P X ∩ {β : ℝ | |α - β| ≤ X ^ (3 * δ - 1)},
      ‖Sp P X α ^ 2 * (Kfun Δ α : ℂ)‖ *
        ‖Sp P X β ^ 2 * (Kfun Δ β : ℂ)‖ * ‖phaseSum γ N (β - α)‖

/-- P0082 page 366 parameter absorption. Every fixed power of calE is
eventually bounded by every positive fixed power of X when gamma exceeds 1. -/
theorem calE_power_le_F_power (γ κ r t : ℝ) (hγ : 1 < γ) (ht : 0 < t) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → calE γ κ N ^ r ≤ F γ N ^ t := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ => κ * r * Real.log N ^ (3 - 3 * γ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by linarith : 0 < -(3 - 3 * γ))).comp hlog)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hr.eventually (gt_mem_nhds ht)] with N hN hrN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hp : 0 < Real.log N ^ γ := Real.rpow_pos_of_pos hL _
  have he : Real.log N ^ (3 - 3 * γ) * Real.log N ^ γ = Real.log N ^ (3 - 2 * γ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hrN.le hp.le
  rw [mul_assoc, he] at hm
  rw [calE, F, ← Real.exp_mul, ← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- P0082 page 366 after display 27. A quarter power of calE
absorbs the two logarithms in the distant frequency estimate. -/
theorem log_F_sq_le_calE_quarter (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (F γ N) ^ 2 ≤ calE γ κ N ^ (1 / 4 : ℝ) := by
  let a := 3 - 2 * γ
  have ha : 0 < a := by dsimp [a]; linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop ha).comp hlog
  have hs := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * γ / a) (κ / 4) (by positivity)).comp ht
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (2 : ℕ), hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN hsN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hpow : (Real.log N ^ a) ^ (2 * γ / a) = (Real.log N ^ γ) ^ 2 := by
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul_natCast hL.le]
    congr 1
    field_simp
    norm_num
  change (Real.log N ^ a) ^ (2 * γ / a) * Real.exp (-(κ / 4) * Real.log N ^ a) < 1 at hsN
  rw [hpow, show -(κ / 4) * Real.log N ^ a = -(κ * Real.log N ^ a * (1 / 4)) by ring,
    Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)] at hsN
  simpa only [F, Real.log_exp, calE, ← Real.exp_mul, one_mul] using hsN.le

/-- LEAF. P0082 page 365 display 26 and page 366 domain split. Expand
the full dyadic second moment, apply Fubini on the truncated compact domain
and bound its real part by the two absolute contributions. This is an
algebraic integral step and contains no cancellation estimate. -/
theorem leaf_moment_split (γ δ κ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc (N / 2) N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
      farMoment γ δ κ N + nearMoment γ δ κ N := by
  sorry

/-- LEAF. P0082 page 366, the first contribution to display 26.
Theorem 2 controls the full index phase sum outside the diagonal strip.
The common kappa cap permits absorption of the weighted integral logarithms. -/
theorem leaf_far_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          farMoment γ δ κ N ≤
            B * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
  sorry

/-- LEAF. P0082 page 366 display 27. The nearby strip uses the trivial
phase sum bound and Vaughan Theorem 3.1 for the prime minor arc sum.
Absorb the printed logarithms into X to a positive delta power. No bound
for the distant phase sum is assumed in this leaf. -/
theorem leaf_near_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        nearMoment γ δ κ N ≤ B * N * F γ N ^ (2 - 2 * δ) := by
  sorry

/-- Assembly. P0082 page 366 after display 27. This is the exact existing
truncated moment statement. It depends only on the expansion and the two
separate frequency estimates above. -/
theorem truncated_moment_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨δf, hδf, hf⟩ := leaf_far_moment γ h1 h2
  obtain ⟨δn, hδn, hn⟩ := leaf_near_moment γ h1 h2
  refine ⟨min δf δn, lt_min hδf hδn, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hf⟩ := hf δ hδ (hδsmall.trans_le (min_le_left _ _))
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bf, hBf, Nf, hf⟩ := hf κ hκ hκsmall
  obtain ⟨Bn, hBn, Nn, hn⟩ := hn δ hδ (hδsmall.trans_le (min_le_right _ _)) κ hκ
  obtain ⟨Nl, hl⟩ := log_F_sq_le_calE_quarter γ κ h1 h2 hκ
  obtain ⟨Np, hp⟩ := calE_power_le_F_power γ κ (3 / 4) (2 * δ) h1 (by positivity)
  refine ⟨Bf + Bn, add_pos hBf hBn, max 16 (max (max Nf Nn) (max Nl Np)), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNN := (le_max_right _ _).trans hN
  have hNf : Nf ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hNN)
  have hNn : Nn ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNN)
  have hNl : Nl ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNN)
  have hNp : Np ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNN)
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hfar : farMoment γ δ κ N ≤
      Bf * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
    calc
      _ ≤ Bf * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := hf N hNf
      _ ≤ Bf * N * F γ N ^ 2 * calE γ κ N ^ (1 / 4 : ℝ) * calE γ κ N ^ (-1 : ℝ) := by
        gcongr
        exact hl N hNl
      _ = _ := by
        rw [mul_assoc (Bf * N * F γ N ^ 2), ← Real.rpow_add hE]
        norm_num
  have hbase : F γ N ^ (2 - 2 * δ) ≤ F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
    rw [Real.rpow_sub hX, Real.rpow_two, Real.rpow_neg hE.le]
    change F γ N ^ 2 / F γ N ^ (2 * δ) ≤ F γ N ^ 2 / calE γ κ N ^ (3 / 4 : ℝ)
    exact div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hE _) (hp N hNp)
  have hnear : nearMoment γ δ κ N ≤
      Bn * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
    calc
      _ ≤ Bn * N * F γ N ^ (2 - 2 * δ) := hn N hNn
      _ ≤ Bn * N * (F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ))) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖truncatedMinor γ δ κ N n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Decomp371a.window_subset_Ioc γ h1 N hN16)
        (fun n _ _ => sq_nonneg _)
    _ ≤ farMoment γ δ κ N + nearMoment γ δ κ N := leaf_moment_split γ δ κ N
    _ ≤ Bf * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) +
        Bn * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := add_le_add hfar hnear
    _ = _ := by ring


end LeanLab.ExceptionalSet.Decomp404e
