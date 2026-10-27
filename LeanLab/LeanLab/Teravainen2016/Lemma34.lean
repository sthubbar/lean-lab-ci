/-
P0076 Teräväinen 2016: Lemma 3.4 for every J ≥ 5, from the J = 5 table `lemma_3_4_five` by
induction on J: if 2^(J−1) ∣ n but 2^J ∤ n, halve n, apply the case J, and double both
summands, which shifts both exponents up by one.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Teravainen2016.Definitions

namespace LeanLab.Teravainen2016

/-- Doubling: `a ≡ 2^i (mod 2^(i+2))` gives `2a ≡ 2^(i+1) (mod 2^(i+3))`. -/
theorem double_modEq {a : ℤ} {i : ℕ} (h : a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)]) :
    2 * a ≡ 2 ^ (i + 1) [ZMOD 2 ^ (i + 1 + 2)] := by
  have : 2 * a ≡ 2 * 2 ^ i [ZMOD 2 * 2 ^ (i + 2)] := Int.ModEq.mul_left' h
  rw [show (2 : ℤ) ^ (i + 1 + 2) = 2 * 2 ^ (i + 2) by ring, show (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i by ring]
  exact this

/-- The induction step of Lemma 3.4. -/
theorem lemma34_succ {J : ℕ} (hJ : 5 ≤ J) (h : Lemma34 J) : Lemma34 (J + 1) := by
  intro n hn
  by_cases hd : (2 : ℤ) ^ (J - 1) ∣ n
  · obtain ⟨n', rfl⟩ := hd
    have hJ1 : J - 1 = (J - 2) + 1 := by omega
    have hnm : (2 : ℤ) ^ (J - 1) * n' = 2 * (2 ^ (J - 2) * n') := by rw [hJ1, pow_succ]; ring
    have hm : ¬ (2 : ℤ) ^ (J - 1) ∣ 2 ^ (J - 2) * n' := by
      rintro ⟨c, hc⟩
      apply hn
      refine ⟨c, ?_⟩
      rw [hnm, hc, show J + 1 - 1 = (J - 1) + 1 by omega, pow_succ]; ring
    obtain ⟨a, b, hab, i, j, hi, hj, ha, hb⟩ := h _ hm
    refine ⟨2 * a, 2 * b, ?_, i + 1, j + 1, by omega, by omega, double_modEq ha, double_modEq hb⟩
    rw [hnm, hab]; ring
  · obtain ⟨a, b, hab, i, j, hi, hj, ha, hb⟩ := h n hd
    exact ⟨a, b, hab, i, j, by omega, by omega, ha, hb⟩

/-- **Lemma 3.4 for every `J ≥ 5`**, zero sorry: retires the cited `lemma_3_4`. -/
theorem lemma_3_4_proved (J : ℕ) (hJ : 5 ≤ J) : Lemma34 J := by
  induction J, hJ using Nat.le_induction with
  | base => exact lemma_3_4_five
  | succ J hJ ih => exact lemma34_succ hJ ih

end LeanLab.Teravainen2016
