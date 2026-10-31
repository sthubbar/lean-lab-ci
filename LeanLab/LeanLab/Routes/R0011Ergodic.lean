import Mathlib

/-!
# R-0011, the ergodic route: Furstenberg correspondence and multiple recurrence for p + q = N

T3 MOONSHOT route, unit U-1069, PC run 20261019T1403Z-32628. AI wrote this Lean code.
KNOWN mathematics; a map entry, not progress on Goldbach, which is open.

Route: model the primes by a measure preserving system through Furstenberg's correspondence and
use recurrence or the Moreira-Richter-Robertson sumset method to put `N` in `P + P`.

What this file proves.
* `primes_density_zero`: `π(n)/n → 0`, from Mathlib's Chebyshev bound. Furstenberg's
  correspondence needs positive upper Banach density, so applied to `P` itself it returns a null
  set and says nothing; the route must weight by `Λ`, whose mean is `1`, and that is Green-Tao
  transference, which meets the R-0003 reflection obstruction.
* `mem_sumset_iff_reflect`: `N ∈ A + A` iff `A ∩ (N - A)` is nonempty. Recurrence controls
  `A ∩ (A + n)`, shifts, while Goldbach for one `N` is an intersection with a reflection
  `x ↦ N - x`, which conjugates the shift to its inverse and is not part of the `ℤ` action;
  ergodic averages over `N` see it, a single `N` is not an ergodic quantity.
* `reflect_shift`: the reflection of a shifted set is the reflected set shifted the other way,
  the identity behind that conjugation.
-/

namespace LeanLab.Routes.R0011

open Filter Topology Real
open scoped Pointwise

/-- **the primes have natural density zero**, `π(n)/n → 0` -/
theorem primes_density_zero :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) / n) atTop (𝓝 0) := by
  -- eventually π(x) ≤ (log 4 + 1) x / log x
  have hev := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  have hev' : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting ⌊(n : ℝ)⌋₊ : ℝ) ≤ (log 4 + 1) * n / log n :=
    tendsto_natCast_atTop_atTop.eventually hev
  have hlog : Tendsto (fun n : ℕ => (log 4 + 1) / log n) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using this.inv_tendsto_atTop.const_mul (log 4 + 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · filter_upwards with n
    positivity
  · filter_upwards [hev', eventually_gt_atTop 1] with n hn hn1
    rw [Nat.floor_natCast] at hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [div_le_iff₀ hnpos]
    calc (Nat.primeCounting n : ℝ) ≤ (log 4 + 1) * n / log n := hn
      _ = (log 4 + 1) / log n * n := by ring

/-- `N ∈ A + A` exactly when `A` meets its reflection `N - A`, for subsets of `ℤ` -/
theorem mem_sumset_iff_reflect (A : Set ℤ) (N : ℤ) :
    N ∈ A + A ↔ (A ∩ (fun a => N - a) '' A).Nonempty := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by ring⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨b, hb, a, ha, by show b + a = N; simp only at hab; omega⟩

/-- reflection conjugates the shift to its inverse: `N - (A + n) = (N - A) - n` -/
theorem reflect_shift (A : Set ℤ) (N n : ℤ) :
    (fun a => N - a) '' ((fun a => a + n) '' A) = (fun a => a - n) '' ((fun a => N - a) '' A) := by
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨N - a, ⟨a, ha, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a + n, ⟨a, ha, rfl⟩, by ring⟩

/-- vacuity: `10 ∈ P + P` through the reflection, `3 ∈ P` and `10 - 3 = 7 ∈ P` -/
theorem vacuity : (10 : ℤ) ∈ {p : ℤ | p.natAbs.Prime ∧ 0 < p} + {p : ℤ | p.natAbs.Prime ∧ 0 < p} := by
  rw [mem_sumset_iff_reflect]
  exact ⟨3, ⟨by norm_num, by norm_num⟩, 7, ⟨by norm_num, by norm_num⟩, by norm_num⟩

end LeanLab.Routes.R0011
