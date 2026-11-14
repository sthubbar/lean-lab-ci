import LeanLab.ExceptionalSet.Decomp371a

/-!
Task371 minor arc decomposition of P0082, pages 365 to 366, displays 24 to 27.
The open inputs are the discarded tail and the truncated second moment.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371b

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable)
open LeanLab.ExceptionalSet.U1539 (Sp majorArcs Kfun eC calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- The integral over the truncated minor arcs of P0082 page 365 display 24,
with the same P, X and Delta as the existing minorInt. -/
noncomputable def truncatedMinor (γ δ κ : ℝ) (N n : ℕ) : ℂ :=
  ∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
      Set.Icc (-(F γ N ^ (6 * δ))) (F γ N ^ (6 * δ)),
    Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
      (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ) * eC (-(α * F γ n))

/-- LEAF. P0082 page 365 display 24. The tail is O of X log X over Delta P.
For fixed positive delta and kappa it is eventually below half the threshold.
This leaf contains no exceptional set estimate and holds for every index n. -/
theorem leaf_tail (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ,
      ‖minorInt γ δ κ N n - truncatedMinor γ δ κ N n‖ ≤
        F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  exact DecompJ200.leaf_minor_tail γ h1 h2 δ κ hδ hκ

/-- LEAF. P0082 pages 365 to 366 displays 25 to 27. The truncated second moment
is O of N X squared log X squared over calE. This asks for the weaker exponent
minus three quarters after absorbing the logarithm. The window is the literal
floor window used at the conclusion of section 5. -/
theorem leaf_truncated_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N, ‖truncatedMinor γ δ κ N n‖ ^ 2) ≤
            B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) := by
  exact DecompJ200.leaf_minor_truncated_moment γ h1 h2

/-- The finite Chebyshev step of P0082 page 366 after display 27.
A uniform tail bound and a truncated second moment control the bad count. -/
theorem count_of_tail_and_moment (s : Finset ℕ) (f g : ℕ → ℂ)
    (T A : ℝ) (hT : 0 < T)
    (htail : ∀ n ∈ s, ‖f n - g n‖ ≤ T / 2)
    (hmoment : (∑ n ∈ s, ‖g n‖ ^ 2) ≤ A) :
    (((s.filter (fun n => T < ‖f n‖)).card : ℝ) * (T / 2) ^ 2) ≤ A := by
  classical
  let bad := s.filter (fun n => T < ‖f n‖)
  have hlarge : ∀ n ∈ bad, (T / 2) ^ 2 ≤ ‖g n‖ ^ 2 := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hnf⟩
    have hnorm : ‖f n‖ ≤ ‖f n - g n‖ + ‖g n‖ := norm_le_norm_sub_add _ _
    have hg : T / 2 ≤ ‖g n‖ := by linarith [htail n hns]
    exact pow_le_pow_left₀ (by positivity) hg 2
  calc
    _ ≤ ∑ n ∈ bad, ‖g n‖ ^ 2 := by
      simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum bad (fun n => ‖g n‖ ^ 2) ((T / 2) ^ 2) hlarge
    _ ≤ ∑ n ∈ s, ‖g n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _)
    _ ≤ A := hmoment

/-- Assembly. P0082 page 366, the exact statement of DecompJ200.leaf_minor_bound.
Conditional on leaf_tail and leaf_truncated_moment. -/
theorem minor_bound_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hm⟩ := leaf_truncated_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, Nm, hm⟩ := hm κ hκ hκsmall
  obtain ⟨Nt, ht⟩ := leaf_tail γ h1 h2 δ κ hδ hκ
  refine ⟨4 * B, by positivity, max Nm Nt, fun N hN => ?_⟩
  have hNm : Nm ≤ N := (le_max_left _ _).trans hN
  have hNt : Nt ≤ N := (le_max_right _ _).trans hN
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hT : 0 < F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_pos hX (Real.rpow_pos_of_pos hE _)
  have hc := count_of_tail_and_moment (window γ N)
    (minorInt γ δ κ N) (truncatedMinor γ δ κ N)
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)))
    (B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)))
    hT (fun n _ => ht N hNt n) (hm N hNm)
  change (Eγ_minor_block γ δ κ N : ℝ) *
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 ≤ _ at hc
  have hp : calE γ κ N ^ (-(3 / 4 : ℝ)) =
      calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
  have hfactor : B * (N : ℝ) * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) =
      (4 * B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) *
        (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 := by
    rw [hp]
    ring
  rw [hfactor] at hc
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp hc

/-- Assembly. P0082 page 366: the block bound from the new major and minor
assemblies and the already proved Fourier split. Conditional on the five open inputs. -/
theorem block_bound_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
        B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₁, hδ₁, hmin⟩ := minor_bound_assembly γ h1 h2
  obtain ⟨δ₂, hδ₂, hmaj⟩ := Decomp371a.major_bound_assembly γ h1 h2
  have hδ : 0 < min δ₁ δ₂ / 2 := half_pos (lt_min hδ₁ hδ₂)
  have hδ1 : min δ₁ δ₂ / 2 < δ₁ := by
    have := min_le_left δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  have hδ2 : min δ₁ δ₂ / 2 < δ₂ := by
    have := min_le_right δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  obtain ⟨κ₁, hκ₁, hmin⟩ := hmin _ hδ hδ1
  obtain ⟨κ₂, hκ₂, hmaj⟩ := hmaj _ hδ hδ2
  have hκ : 0 < min κ₁ κ₂ := lt_min hκ₁ hκ₂
  obtain ⟨B₁, hB₁, N₁, hmin⟩ := hmin _ hκ (min_le_left _ _)
  obtain ⟨c₀, B₂, hc₀, hB₂, N₂, hmaj⟩ := hmaj _ hκ (min_le_right _ _)
  obtain ⟨N₃, hsplit⟩ := leaf_dyadic_split γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ h1 h2 hδ hκ hc₀
  refine ⟨min κ₁ κ₂, B₁ + B₂, hκ, add_pos hB₁ hB₂, max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have h₁ := hmin N (le_trans (le_max_left _ _) hN)
  have h₂ := hmaj N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h₃ := hsplit N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have h₃' : (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
      Eγ_minor_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) N +
        Eγ_major_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ N := by exact_mod_cast h₃
  calc _ ≤ _ := h₃'
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

/-- Assembly. P0082 page 366: apply the proved window dissection to the new
block bound. Conditional on the five open analytic inputs. -/
theorem dyadic_bound_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  obtain ⟨κ, B, hκ, hB, N₀, h⟩ := block_bound_assembly γ h1 h2
  obtain ⟨c, hc, C, hC, M0, hM⟩ :=
    leaf_block_dissection γ κ B h1 h2 hκ hB (fun n => ¬ Solvable γ n) N₀ h
  refine ⟨c, hc, C, hC, M0, fun M hM0 => ?_⟩
  have e : Eγ_dyadic γ M = dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold Eγ_dyadic dyadicCount
    congr!
  rw [e]
  exact hM M hM0

/-- Assembly. P0082 page 354 Theorem 1 from the five new inputs. This has the
exact existing Theorem1 type and does not call either original open arc leaf. -/
theorem brudernPerelli_assembly : LeanLab.ExceptionalSet.BrudernPerelli1998.Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (dyadic_bound_assembly γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.Decomp371b
