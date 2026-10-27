/-
P0087 Akeno 2026 Appendix 5.1 page 36.
The linear sieve delay system has at most one pair on positive arguments.
Existence is a separate input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveFns

namespace LeanLab.Akeno2026.SieveFns
open Set intervalIntegral

theorem omega_unique_upto {ap am bp bm : ℝ → ℝ}
    (ha : IsOmegaPair ap am) (hb : IsOmegaPair bp bm) (n : ℕ) :
    ∀ s : ℝ, 0 < s → s ≤ (n : ℝ) + 2 → ap s = bp s ∧ am s = bm s := by
  induction n with
  | zero =>
    intro s hs hs2
    obtain ⟨hap, ham⟩ := ha.2.1 s hs (by simpa using hs2)
    obtain ⟨hbp, hbm⟩ := hb.2.1 s hs (by simpa using hs2)
    exact ⟨hap.trans hbp.symm, ham.trans hbm.symm⟩
  | succ n ih =>
    intro s hs hsn
    by_cases hs2 : s ≤ 2
    · obtain ⟨hap, ham⟩ := ha.2.1 s hs hs2
      obtain ⟨hbp, hbm⟩ := hb.2.1 s hs hs2
      exact ⟨hap.trans hbp.symm, ham.trans hbm.symm⟩
    · have h2s : (2 : ℝ) ≤ s := le_of_lt (lt_of_not_ge hs2)
      obtain ⟨ham, hap⟩ := omega_delay ha (a := 2) (b := s) le_rfl h2s
      obtain ⟨hbm, hbp⟩ := omega_delay hb (a := 2) (b := s) le_rfl h2s
      have hip : (∫ u in (2 : ℝ)..s, ((u - 1) * ap (u - 1)) / (u - 1)) =
          ∫ u in (2 : ℝ)..s, ((u - 1) * bp (u - 1)) / (u - 1) := by
        apply integral_congr
        intro u hu
        rw [uIcc_of_le h2s] at hu
        dsimp only
        rw [(ih (u - 1) (by linarith [hu.1]) (by push_cast at hsn; linarith [hu.2])).1]
      have him : (∫ u in (2 : ℝ)..s, ((u - 1) * am (u - 1)) / (u - 1)) =
          ∫ u in (2 : ℝ)..s, ((u - 1) * bm (u - 1)) / (u - 1) := by
        apply integral_congr
        intro u hu
        rw [uIcc_of_le h2s] at hu
        dsimp only
        rw [(ih (u - 1) (by linarith [hu.1]) (by push_cast at hsn; linarith [hu.2])).2]
      obtain ⟨hap2, ham2⟩ := ha.2.1 2 (by norm_num) le_rfl
      obtain ⟨hbp2, hbm2⟩ := hb.2.1 2 (by norm_num) le_rfl
      rw [hap2] at hap
      rw [hbp2] at hbp
      rw [ham2] at ham
      rw [hbm2] at hbm
      constructor <;> nlinarith

theorem omega_unique {ap am bp bm : ℝ → ℝ}
    (ha : IsOmegaPair ap am) (hb : IsOmegaPair bp bm) {s : ℝ} (hs : 0 < s) :
    ap s = bp s ∧ am s = bm s := by
  obtain ⟨n, hn⟩ := exists_nat_gt s
  exact omega_unique_upto ha hb n s hs (by linarith)

end LeanLab.Akeno2026.SieveFns
