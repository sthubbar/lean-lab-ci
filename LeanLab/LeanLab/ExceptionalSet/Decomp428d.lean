import LeanLab.ExceptionalSet.Decomp428c

/-!
Distant frequency supply for P0082 page 366 display 26.
The two smaller leaves isolate cancellation and integral localization.
The weighted prime energy is shared with the nearby frequency supply.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp428d

open Real MeasureTheory Filter Topology Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Sp Kfun calE eC norm_eC)
open LeanLab.ExceptionalSet.Decomp404e

/-- Page 366 display 27. The full index phase sum is at most N.
This is the trivial bound used on the nearby strip. -/
theorem phaseSum_norm_le (γ : ℝ) (N : ℕ) (t : ℝ) : ‖phaseSum γ N t‖ ≤ N := by
  unfold phaseSum
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖eC (t * F γ n)‖ := norm_sum_le _ _
    _ = ((N - N / 2 : ℕ) : ℝ) := by simp only [norm_eC, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
    _ ≤ N := by exact_mod_cast Nat.sub_le N (N / 2)

/-- LEAF. P0082 page 366, the distant contribution to display 26.
Theorem 2 controls the finite phase sum when the difference is outside
the nearby strip. Shrinking the common kappa cap permits exponent
minus three halves to pay for the weaker weighted energy bound. -/
theorem leaf_far_phase (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ t : ℝ, F γ N ^ (3 * δ - 1) < |t| → |t| ≤ 2 * F γ N ^ (6 * δ) →
            ‖phaseSum γ N t‖ ≤ C * N * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  exact UpJ200.Decomp467a.far_phase_of_karacuba U1539.lemma10 γ h1 h2

/-- LEAF. P0082 page 366 first contribution to display 26. A bound V
for the distant phase sum leaves the product of two weighted energies.
No cancellation estimate is asserted in this integral step. -/
theorem leaf_far_localization (γ δ κ : ℝ) (N : ℕ) (V : ℝ) (hV : 0 ≤ V)
    (hΔ : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1)
    (hphase : ∀ α ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
        F γ N ^ (3 * δ - 1) < |α - β| → ‖phaseSum γ N (β - α)‖ ≤ V) :
    farMoment γ δ κ N ≤ V *
      (∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
        ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
          (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖) ^ 2 := by
  exact UpJ200.Localization446.leaf_far_localization_supplied γ δ κ N V hV hΔ hphase

/-- Assembly. P0082 page 366 display 26. This is the exact existing
Decomp404e.leaf_far_moment statement. The smaller phase and integral
leaves and the shared weighted energy are the only admitted inputs. -/
theorem far_moment_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          farMoment γ δ κ N ≤
            B * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
  obtain ⟨δ₀, hδ₀, hphase⟩ := leaf_far_phase γ h1 h2
  obtain ⟨Ce, hCe, he⟩ := Decomp428c.leaf_weighted_energy
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hphase⟩ := hphase δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Cs, hCs, Ns, hs⟩ := hphase κ hκ hκsmall
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  refine ⟨Cs * Ce ^ 2, by positivity, max 2 (max Ns Np), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsN := hs N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨hX2, _, hΔ, hΔ1, _⟩ := hp N
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  have henergy := he (F γ N ^ (6 * δ)) (F γ N)
    (calE γ κ N ^ (-(1 / 8 : ℝ))) (by positivity) hX2 hΔ hΔ1
  have hlocal := leaf_far_localization γ δ κ N
    (Cs * N * calE γ κ N ^ (-(3 / 2 : ℝ))) (by positivity) hΔ1
    (fun α hα β hβ hdist => by
      apply hsN (β - α)
      · simpa only [abs_sub_comm] using hdist
      · have ha := hα.2
        have hb := hβ.2
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2])
  have hI : 0 ≤ ∫ α in truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
      ‖Sp (F γ N ^ (6 * δ)) (F γ N) α ^ 2 *
        (Kfun (calE γ κ N ^ (-(1 / 8 : ℝ))) α : ℂ)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hratio : calE γ κ N ^ (-(3 / 2 : ℝ)) /
      (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 = calE γ κ N ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_sub hE]
    norm_num
  calc
    _ ≤ (Cs * N * calE γ κ N ^ (-(3 / 2 : ℝ))) *
        (Ce * F γ N * Real.log (F γ N) / calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 :=
      hlocal.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI henergy 2) (by positivity))
    _ = (Cs * Ce ^ 2) * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 *
        (calE γ κ N ^ (-(3 / 2 : ℝ)) / (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2) := by ring
    _ ≤ (Cs * Ce ^ 2) * N * F γ N ^ 2 * Real.log (F γ N) ^ 2 * calE γ κ N ^ (-1 : ℝ) := by
      rw [hratio]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)) (by positivity)

end LeanLab.ExceptionalSet.Decomp428d
