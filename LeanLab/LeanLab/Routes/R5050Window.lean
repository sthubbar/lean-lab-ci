/-
R-5050, T3, CLOUD 20261019T1116Z-cloud23, unit U-5482: the window form of binary Goldbach.

Binary Goldbach for every even n ≥ 4 is exactly the statement that every window (x, x + 2],
x ≥ 2 real, holds a sum of two primes that is even. The lab's sumset staircases,
GoldbachGaps/DudekStair and KLStair, reach windows of length 534 to 1478; this file records
the endpoint they would have to reach. Not progress on Goldbach, which is OPEN.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.GoldbachGaps.Unconditional

namespace LeanLab.Routes.R5050
open LeanLab LeanLab.GoldbachGaps

/-- Every window `(x, x + H]` with `x ≥ 2` holds an even sum of two primes. -/
def Windows (H : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) ≤ x + H

/-- **Binary Goldbach is the window statement at length 2.** -/
theorem binary_iff_windows : BinaryGoldbach ↔ Windows 2 := by
  constructor
  · intro hB x hx
    obtain ⟨n, hev, hlo, hhi⟩ := even_above x (by linarith)
    have hn4 : 4 ≤ n := by
      have : (2 : ℝ) < n := by linarith
      have h2 : 2 < n := by exact_mod_cast this
      rcases hev with ⟨k, hk⟩; omega
    exact ⟨n, ⟨hev, hB n hev hn4⟩, hlo, hhi⟩
  · intro hW n hev hn4
    have hx : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 2)
    obtain ⟨m, ⟨hmev, hm⟩, hlo, hhi⟩ := hW _ hx
    have hc : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at hlo hhi
    have h1 : n - 2 < m := by
      have : ((n - 2 : ℕ) : ℝ) < m := by rw [hc]; exact hlo
      exact_mod_cast this
    have h2 : m ≤ n := by
      have : (m : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have : m = n := by
      rcases hmev with ⟨a, ha⟩; rcases hev with ⟨b, hb⟩; omega
    rw [← this]; exact hm

/-- Windows only shrink in strength as `H` grows. -/
theorem windows_mono {H H' : ℝ} (h : H ≤ H') (hW : Windows H) : Windows H' := fun x hx => by
  obtain ⟨n, hn, h1, h2⟩ := hW x hx
  exact ⟨n, hn, h1, by linarith⟩

end LeanLab.Routes.R5050
