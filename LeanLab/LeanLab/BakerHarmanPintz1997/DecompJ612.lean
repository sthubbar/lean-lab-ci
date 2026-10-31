import LeanLab.BakerHarmanPintz1997.Statements
import LeanLab.BakerHarmanPintz1997.Decomp1518

namespace LeanLab.BakerHarmanPintz1997
open LeanLab.BakerHarmanPintz1997.Decomp1518
open Finset ArithmeticFunction

/-- LEAF. Page 30, Lemma 15 split. Reduce Lemma 15 to the `Holds42` conclusion using the Lemma 12 (4.9) input and the `j_k` bound. -/
theorem lemma15_core {ε : ℝ} (he : 0 ≤ ε)
    (h12 : Sieve42 ε fun M N z => (∀ x, z x = wof x) ∧
      Ev (fun x => max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)))
    (hJ : ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => jsum (a x) (b x) (M x) (N x) (wof x) (z x) k) :
    Sieve42 ε fun M N z => Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) := by
  intro B a b M N z ha hb hcond
  obtain ⟨X1, hw⟩ := hcond
  have hd : Holds42 ε fun x k => conv2 (a x) (b x) (M x) (N x) (wof x) k := by
    refine h12 B a b M N wof ha hb ⟨fun _ => rfl, max X1 1, fun x hx => Or.inr ?_⟩
    have h := hw x (le_trans (le_max_left _ _) hx)
    refine le_trans (max_le (le_trans h.2.1 h.2.2) h.2.2) ?_
    exact le_trans (Real.rpow_le_rpow_of_exponent_le (le_trans (le_max_right _ _) hx) (by norm_num : (0.4:ℝ) ≤ 0.46))
      (Real.rpow_le_rpow_of_exponent_le (le_trans (le_max_right _ _) hx) (by linarith))
  have hj : Holds42 ε fun x k => jsum (a x) (b x) (M x) (N x) (wof x) (z x) k := hJ B a b M N z ha hb ⟨X1, hw⟩
  have ev_wz : Ev fun x => wof x ≤ z x := by
    obtain ⟨Xw, hwXw⟩ := wof_le_rpow_ev 0.1 (by norm_num)
    exact ⟨max X1 Xw, fun x hx => by
      have h := hw x (le_trans (le_max_left _ _) hx)
      dsimp at h ⊢
      have : z x = x ^ (0.1 : ℝ) := h.1
      rw [this]
      exact hwXw x (le_trans (le_max_right _ _) hx)⟩
  obtain ⟨Xw, hwXw⟩ := wof_le_rpow_ev 0.1 (by norm_num)
  have holds42_sub_hd_hj := holds42_sub hd hj
  refine holds42_congr_ev ⟨max (max X1 Xw) 1, fun x hx k hk => ?_⟩ holds42_sub_hd_hj
  have hwz : wof x ≤ z x := by
    have h := hw x (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx))
    rw [h.1]
    exact hwXw x (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx))
  exact (conv2_buchstab (a x) (b x) (M x) (N x) hk hwz).symm

theorem lemma15_assembly (h12 : Lemma12)
    (hJ : ∀ ε : ℝ, 0 < ε → ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N z : ℝ → ℝ),
      (∀ x n, ‖a x n‖ ≤ tau n ^ B) → (∀ x n, ‖b x n‖ ≤ tau n ^ B) →
      Ev (fun x => z x = x ^ (0.1 : ℝ) ∧ M x ≤ N x ∧ N x ≤ x ^ (0.4 : ℝ)) →
      Holds42 ε fun x k => jsum (a x) (b x) (M x) (N x) (wof x) (z x) k) : Lemma15 := by
  obtain ⟨ε0, h0, h⟩ := lemma12_ev h12
  exact ⟨ε0, h0, fun ε he he0 => lemma15_core (le_of_lt he) (h ε he he0) (hJ ε he)⟩
