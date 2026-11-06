import LeanLab.ExceptionalSet.Decomp446a
import LeanLab.ExceptionalSet.MomentSupply446
import LeanLab.ExceptionalSet.Decomp404a
import LeanLab.ExceptionalSet.TailSupply385

/-!
The exact P0082 Theorem 1 from the refined analytic inputs.
Source: pages 362 to 366, Lemma 7 and displays 20 to 27.
All existing statement files remain unchanged.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Assembly446

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable Theorem1)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.DecompJ200
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor count_of_tail_and_moment)

/-- P0082 page 365 Lemma 8. The major bound uses the new even coefficient
leaf, the inherited parity moments, the boundary input and the proved kernel. -/
theorem major_bound_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := Decomp446a.coefficient_lower_assembly γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := Decomp404a.boundary_of_lemma4 LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ :=
    hcoeff κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ :=
    hboundary κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c₀, Ba + Bb, hc₀, add_pos hBa hBb, max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hE)]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos hE) (by norm_num))
  let A := (window γ N).filter (fun n : ℕ =>
    (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  let B := (window γ N).filter (fun n : ℕ =>
    Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
      1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))
  have hsubset : (window γ N).filter (fun n : ℕ =>
      (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) ⊆ A ∪ B := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hnmajor⟩
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ hnB
    · have hgood : ¬ (Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
        intro hbad
        exact hnB (Finset.mem_filter.mpr ⟨hnW, hbad⟩)
      have hid := Decomp404a.major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hnW, by rwa [hid] at hnmajor⟩
  have hcard : (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ (A.card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc
    _ ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- P0082 page 366. The minor bound uses the clean tail supply and the
refined truncated moment assembly. -/
theorem minor_bound_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_minor_block γ δ κ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, hm⟩ := MomentSupply446.truncated_moment_supplied γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, Nm, hm⟩ := hm κ hκ hκsmall
  obtain ⟨Nt, ht⟩ := TailSupply385.leaf_tail_supplied γ h1 h2 δ κ hδ hκ
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

/-- P0082 page 366. Combine the refined major and minor estimates. -/
theorem block_bound_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
        B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₁, hδ₁, hmin⟩ := minor_bound_supplied γ h1 h2
  obtain ⟨δ₂, hδ₂, hmaj⟩ := major_bound_supplied γ h1 h2
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
block bound. Conditional on the seven open analytic inputs. -/
theorem dyadic_bound_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ c > 0, ∃ C > 0, ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      (Eγ_dyadic γ M : ℝ) ≤ C * M * Real.exp (-c * Real.log M ^ (3 - 2 * γ)) := by
  obtain ⟨κ, B, hκ, hB, N₀, h⟩ := block_bound_supplied γ h1 h2
  obtain ⟨c, hc, C, hC, M0, hM⟩ :=
    leaf_block_dissection γ κ B h1 h2 hκ hB (fun n => ¬ Solvable γ n) N₀ h
  refine ⟨c, hc, C, hC, M0, fun M hM0 => ?_⟩
  have e : Eγ_dyadic γ M = dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold Eγ_dyadic dyadicCount
    congr!
  rw [e]
  exact hM M hM0

/-- Assembly. P0082 page 354 Theorem 1 from the seven analytic inputs. This has the
exact existing Theorem1 type and does not call either original open arc leaf. -/
theorem brudernPerelli_assembly : LeanLab.ExceptionalSet.BrudernPerelli1998.Theorem1 := by
  intro γ h1 h2
  exact leaf_theorem1_from_sums γ h1 h2
    (dyadic_bound_supplied γ h1 h2)
    (leaf_dyadic_trivial γ)
    (leaf_dyadic_sum γ)
    (leaf_dyadic_sum_exp γ h1 h2)

end LeanLab.ExceptionalSet.Assembly446
