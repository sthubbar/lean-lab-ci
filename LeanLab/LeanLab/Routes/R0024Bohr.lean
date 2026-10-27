/-
# R-0024, T3 MOONSHOT: Bogolyubov, Bohr sets, and why Fourier structure cannot fill the evens

Unit U-1202, PC run 20261020T0902Z-22676.

Route: Bogolyubov's lemma puts a Bohr set `B(Γ, ρ) = {n : ‖nγ‖ ≤ ρ for all γ ∈ Γ}` inside
`2A − 2A` for any dense `A`, with `Γ` the large spectrum of `1_A`. Ask whether a binary version
puts a Bohr set inside `P + P` that contains every even number up to `N`.

The barrier, PROVED here: a Bohr set with `ρ < 1/4` that contains every even `n ≤ N` has every
frequency within `2ρ/N`-ish of `0` or `1/2` modulo one. So the only Bohr sets that hold all evens
are the trivial one, `2ℤ`, frequency `1/2`, which is the mod 2 condition and nothing more.
* `dist_mul_le`: if `‖kα‖ ≤ ρ < 1/4` for all `1 ≤ k ≤ K`, then `‖α‖ ≤ ρ/K`, a quantitative
  Dirichlet-type lemma, `‖x‖ = |x − round x|`.
* `bohr_all_evens`: if `‖nα‖ ≤ ρ < 1/4` for every even `n` with `2 ≤ n ≤ 2K`, then `‖2α‖ ≤ ρ/K`.

Numerics, Routes/numerics/r0024_bohr.out: for `N = 30030` the large spectrum of the primes at
`δ = 0.5` is `{0, 1/2}` and its Bohr set is exactly the evens; at Bogolyubov's working level
`δ ≈ √α ≈ 0.3` it has denominators `1, 2, 3, 6` and the Bohr set is the multiples of 6; at
`δ = 0.2`, denominators up to 10, a 1/30 fraction. As `N` grows the density `α ≈ 1/log N`
falls, the needed `δ` falls, more small denominators enter, and the Bohr set shrinks to the
multiples of every small prime: Fourier structure of the primes is their local structure.

KNOWN territory: Bogolyubov-Ruzsa and Green's work on sumsets of primes. AI wrote this Lean code.
Binary Goldbach is OPEN; this route is a barrier map, not progress.
-/
import Mathlib

namespace LeanLab.Routes.R0024

/-- `‖x‖`, distance to the nearest integer. -/
noncomputable def dist0 (x : ℝ) : ℝ := |x - round x|

theorem dist0_add_int (x : ℝ) (m : ℤ) : dist0 (x + m) = dist0 x := by
  unfold dist0; rw [round_add_intCast]; push_cast; ring_nf

theorem dist0_of_small {y : ℝ} (h1 : -(1 / 2) ≤ y) (h2 : y < 1 / 2) : dist0 y = |y| := by
  unfold dist0
  rw [round_eq_zero_iff.2 ⟨h1, h2⟩]; simp

/-- **`dist_mul_le`**: if `‖kα‖ ≤ ρ < 1/4` for all `1 ≤ k ≤ K`, then `‖α‖ ≤ ρ/K`. -/
theorem dist_mul_le {α ρ : ℝ} {K : ℕ} (hK : 1 ≤ K) (hρ : ρ < 1 / 4)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ K → dist0 (k * α) ≤ ρ) : dist0 α ≤ ρ / K := by
  set β := α - round α with hβ
  have hdk : ∀ k : ℕ, dist0 (k * α) = dist0 (k * β) := by
    intro k
    have : (k : ℝ) * α = k * β + ((k * round α : ℤ) : ℝ) := by rw [hβ]; push_cast; ring
    rw [this, dist0_add_int]
  have hβabs : |β| ≤ 1 / 2 := by
    rw [hβ]; exact abs_sub_round α
  have hdα : dist0 α = |β| := rfl
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hρ0 : 0 ≤ ρ := by
    have := h 1 le_rfl hK
    have : 0 ≤ dist0 ((1 : ℕ) * α) := abs_nonneg _
    linarith
  rw [hdα]
  by_contra hcon
  push_neg at hcon
  set t := |β|
  have ht : ρ / K < t := hcon
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
  -- case t > ρ: k = 1
  by_cases hbig : ρ < t
  · have := h 1 le_rfl hK
    simp only [Nat.cast_one, one_mul] at this
    rw [hdα] at this
    linarith
  push_neg at hbig
  -- t ≤ ρ < 1/4: take k = ⌊ρ/t⌋ + 1
  set k := ⌊ρ / t⌋₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkK : k ≤ K := by
    have h1 : ρ / t < K := by
      rw [div_lt_iff₀ ht0]; rw [div_lt_iff₀ (by linarith)] at ht; linarith
    have h2 : (⌊ρ / t⌋₊ : ℝ) ≤ ρ / t := Nat.floor_le (by positivity)
    have : (⌊ρ / t⌋₊ : ℝ) < K := lt_of_le_of_lt h2 h1
    have : ⌊ρ / t⌋₊ < K := by exact_mod_cast this
    omega
  have hkt_gt : ρ < k * t := by
    have := Nat.lt_floor_add_one (ρ / t)
    rw [div_lt_iff₀ ht0] at this
    simp only [hk]; push_cast; linarith
  have hkt_le : k * t ≤ ρ + t := by
    have h2 : (⌊ρ / t⌋₊ : ℝ) ≤ ρ / t := Nat.floor_le (by positivity)
    have : (⌊ρ / t⌋₊ : ℝ) * t ≤ ρ := by
      have := mul_le_mul_of_nonneg_right h2 ht0.le
      rwa [div_mul_cancel₀ _ ht0.ne'] at this
    simp only [hk]; push_cast; linarith
  have hsmall : |(k : ℝ) * β| < 1 / 2 := by
    rw [abs_mul, Nat.abs_cast]; linarith
  have hd : dist0 ((k : ℝ) * β) = |(k : ℝ) * β| :=
    dist0_of_small (by linarith [neg_abs_le ((k : ℝ) * β)]) (by linarith [le_abs_self ((k : ℝ) * β)])
  have := h k hk1 hkK
  rw [hdk k, hd, abs_mul, Nat.abs_cast] at this
  linarith

/-- **`bohr_all_evens`**: a Bohr set `{n : ‖nα‖ ≤ ρ}`, `ρ < 1/4`, that contains every even `n`
with `2 ≤ n ≤ 2K` has `‖2α‖ ≤ ρ/K`: its frequency is within `ρ/(2K)` of `0` or `1/2`. -/
theorem bohr_all_evens {α ρ : ℝ} {K : ℕ} (hK : 1 ≤ K) (hρ : ρ < 1 / 4)
    (h : ∀ n : ℕ, Even n → 2 ≤ n → n ≤ 2 * K → dist0 (n * α) ≤ ρ) : dist0 (2 * α) ≤ ρ / K := by
  apply dist_mul_le hK hρ
  intro k hk1 hkK
  have := h (2 * k) (even_two_mul k) (by omega) (by omega)
  push_cast at this
  rwa [show (2 : ℝ) * k * α = k * (2 * α) by ring] at this

/-- Vacuity: the frequency `1/2` gives the evens exactly, `‖n/2‖ = 0` for even `n`. -/
example : dist0 ((4 : ℕ) * (1 / 2 : ℝ)) = 0 := by
  unfold dist0; norm_num

end LeanLab.Routes.R0024
