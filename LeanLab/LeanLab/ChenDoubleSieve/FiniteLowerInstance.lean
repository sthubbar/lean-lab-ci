import LeanLab.ChenDoubleSieve.NormalizerPositive

/-!
# A finite lower correction with a nonzero normalizer

Source: https://arxiv.org/pdf/0705.1652, pages 9 and 10, equation 3.4.
The lower sieve function is zero in this witness. It is not the analytic sieve pair.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Finset Set
namespace LeanLab.ChenDoubleSieve.Wu04

/-- For the zero lower sieve function, one positive normalizer makes the supremum finite. -/
theorem zero_hkn_finite {δ Δ s : ℝ} {k N₀ N i : ℕ} {V : Fin i → ℝ}
    (hN₀ : N₀ ≤ N) (hN : 2 ≤ N) (hEven : Even N) (hU : UkData δ k N i V Δ)
    (hθ : 0 < Theta δ N i V Δ) :
    ∃ c : ℝ, hkn (fun _ => 0) δ k N₀ s = (c : EReal) := by
  have hlo : (0 : EReal) ≤ hkn (fun _ => 0) δ k N₀ s := by
    exact le_sSup ⟨0, zero_lower_candidate δ k N₀ s, by simp⟩
  let r := Phi δ N i V Δ s / Theta δ N i V Δ
  have hhi : hkn (fun _ => 0) δ k N₀ s ≤ (r : EReal) := by
    apply sSup_le
    rintro _ ⟨c, hc, rfl⟩
    have hh := hc N hN₀ hN hEven i V Δ hU
    simp only [normalized, mul_zero, zero_div, zero_add] at hh
    have hr : c ≤ r := (le_div_iff₀ hθ).mpr hh
    change (c : EReal) ≤ (r : EReal)
    exact_mod_cast hr
  have htop : hkn (fun _ => 0) δ k N₀ s ≠ ⊤ :=
    ne_of_lt (hhi.trans_lt (EReal.coe_lt_top r))
  have hbot : hkn (fun _ => 0) δ k N₀ s ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe 0).trans_le hlo)
  exact ⟨_, (EReal.coe_toReal htop hbot).symm⟩

/-- A complete nonempty witness for the finite lower supremum implication. -/
theorem lower_supremum_instance : ∃ c : ℝ,
    hkn (fun _ => 0) (1/4) 1 65536 (2.2 : ℝ) = (c : EReal) ∧
    (normalized (fun _ => 0) 2.2+c) *
      Theta (1/4) 65536 1 (fun _ => 3+positiveEps) (1+3/2*positiveEps) ≤
      Phi (1/4) 65536 1 (fun _ => 3+positiveEps) (1+3/2*positiveEps) 2.2 := by
  obtain ⟨c,hc⟩ := zero_hkn_finite (s := (2.2 : ℝ)) (by norm_num : 65536 ≤ 65536)
    (by norm_num) (by norm_num) positive_delta_instance Theta_positive_instance
  exact ⟨c,hc,lower_at_sup (by norm_num) (by norm_num) (by norm_num)
    positive_delta_instance Theta_positive_instance hc⟩

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.zero_hkn_finite
#print axioms LeanLab.ChenDoubleSieve.Wu04.lower_supremum_instance
