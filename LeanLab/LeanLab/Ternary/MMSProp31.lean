/-
P0028, arXiv 1610.02017, section 4.3, page 9.
Elementary assembly of the transference argument.
The approximation input is explicit and remains conditional.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSProp33
import LeanLab.Ternary.MMSNormalization

namespace LeanLab.Ternary.MMS
open Finset

/-- Nonnegative inputs give a nonnegative triple convolution. -/
theorem conv3_nonneg {N n : ℕ} {f₁ f₂ f₃ : ℕ → ℝ}
    (h₁ : ∀ a ∈ Icc 1 N, 0 ≤ f₁ a)
    (h₂ : ∀ a ∈ Icc 1 N, 0 ≤ f₂ a)
    (h₃ : ∀ a ∈ Icc 1 N, 0 ≤ f₃ a) :
    0 ≤ conv3 N f₁ f₂ f₃ n := by
  unfold conv3
  apply sum_nonneg
  intro a ha
  apply sum_nonneg
  intro b hb
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (h₁ a ha) (h₂ b hb))
      (h₃ _ (mem_Icc.mpr ⟨by omega, h.2⟩))
  · exact le_rfl

/-- The sparse hypotheses have a concrete local instance.
The constant function one works at every positive N, with a sufficiently large K. -/
theorem prop31Hyp_one (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ η : ℝ, 0 ≤ η →
      Prop31Hyp N η (1 / 6) K (5 / 2) (fun _ => 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ (1 - 1 / (5 / 2 : ℝ)) := Real.rpow_pos_of_pos hNr _
  set K := max 1 (fhatLq N (fun _ => 1) (5 / 2) /
    (N : ℝ) ^ (1 - 1 / (5 / 2 : ℝ)))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro η hη
  refine ⟨fun _ _ => zero_le_one, denseOnAPs_one N η (1 / 6) (by norm_num),
    ⟨fun _ => 1, fun _ _ => le_rfl, ?_⟩, ?_⟩
  · intro γ
    simpa using mul_nonneg hη (Nat.cast_nonneg N)
  · exact (div_le_iff₀ hp).mp (le_max_right _ _)

/-- The analytic work required by section 4.3, after normalizing the structured parts.
For every density and error tolerance, sufficiently pseudorandom inputs have bounded
approximants with the required progression density and a one-sided convolution error.
This is an unproved input, not a restatement of Lemma 4.3. -/
def Prop31Approximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ τ κ : ℝ, 0 < τ → 0 < κ →
    ∀ K q : ℝ, 1 ≤ K → 2 < q → q < 3 →
    ∃ η₀ > (0 : ℝ), ∃ N₀ : ℕ, ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ), N₀ ≤ N →
    Prop31Hyp N η ε K q f₁ → Prop31Hyp N η ε K q f₂ → Prop31Hyp N η ε K q f₃ →
    ∃ g₁ g₂ g₃ : ℕ → ℝ,
      UnitValued N g₁ ∧ UnitValued N g₂ ∧ UnitValued N g₃ ∧
      DenseOnAPs N τ (ε / 4) g₁ ∧ DenseOnAPs N τ (ε / 4) g₂ ∧
      DenseOnAPs N τ (ε / 4) g₃ ∧
      ∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N →
        conv3 N g₁ g₂ g₃ n - conv3 N f₁ f₂ f₃ n ≤ κ * (N : ℝ) ^ 2

/-- Section 4.3 assembly, conditional on the analytic approximation input and Prop32.
The constant c depends only on ε. Large η is handled by positivity. -/
theorem prop31_of_prop32_of_approximation (H32 : Prop32)
    (HA : Prop31Approximation) : Prop31 := by
  intro ε hε hε1
  obtain ⟨τ, hτ, d, hd, Nd, hD⟩ := H32 (ε / 4) (by positivity)
  refine ⟨d / 2, by positivity, ?_⟩
  intro K q hK hq hq3
  obtain ⟨η₀, hη₀, Na, hA⟩ := HA ε hε hε1 τ (d / 2) hτ (by positivity) K q hK hq hq3
  refine ⟨(d / 2) / η₀, ?_⟩
  intro η hη hη1
  refine ⟨max Nd Na, ?_⟩
  intro N f₁ f₂ f₃ hN h₁ h₂ h₃ n hn hnN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
  by_cases hsmall : η ≤ η₀
  · obtain ⟨g₁, g₂, g₃, hg₁, hg₂, hg₃, hd₁, hd₂, hd₃, herr⟩ :=
      hA η hη hsmall N f₁ f₂ f₃ ((le_max_right _ _).trans hN) h₁ h₂ h₃
    have hmain := hD N g₁ g₂ g₃ ((le_max_left _ _).trans hN)
      hg₁ hg₂ hg₃ hd₁ hd₂ hd₃ n hn hnN
    have he := herr n hn hnN
    have hC : 0 ≤ (d / 2) / η₀ * η := by positivity
    have hCN : 0 ≤ ((d / 2) / η₀ * η) * (N : ℝ) ^ 2 := mul_nonneg hC hN0
    nlinarith
  · have hlarge : η₀ ≤ η := (lt_of_not_ge hsmall).le
    have hC : d / 2 ≤ (d / 2) / η₀ * η := by
      calc d / 2 = (d / 2) / η₀ * η₀ := by field_simp
           _ ≤ (d / 2) / η₀ * η := mul_le_mul_of_nonneg_left hlarge (by positivity)
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hC) hN0).trans
      (conv3_nonneg h₁.1 h₂.1 h₃.1)

/-- Theorem 4.1 replaces Prop32. The approximation input remains. -/
theorem prop31_of_thm41_of_approximation (H41 : Thm41)
    (HA : Prop31Approximation) : Prop31 :=
  prop31_of_prop32_of_approximation (prop32_of_thm41 H41) HA

end LeanLab.Ternary.MMS
