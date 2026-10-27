/-
P0078. Yanbo Song, "The ternary Goldbach-Vinogradov theorem with almost equal
Piatetski-Shapiro primes", arXiv 2012.06322 v1, 2020.

Theorem 1: For every large enough odd number n the equation
  n = p₁ + p₂ + p₃,  |pᵢ − n/3| ≤ y,  pᵢ ∈ A_γ  (1 ≤ i ≤ 3)
is solvable for y > n^{(52−45γ)/8} and 44/45 < γ < 1.
Here A_γ = {prime p | p = [m^{1/γ}], m ≥ 1}, [x] the greatest integer not exceeding x,
and γ = 1/c with c > 1.

Encoding: "large enough" is an explicit existential threshold `N₀`, chosen after `γ`
and before `n` and `y`; the paper's wording puts "for every large enough n" before
"solvable for y > ...", so `N₀` does not depend on `y`.

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.
-/
import Mathlib
import LeanLab.Ternary.AlmostEqual

namespace LeanLab.Song2020

open LeanLab.Ternary

/-- Piatetski-Shapiro prime for `γ`: a prime `p` with `p = [m^{1/γ}]` for some `m ≥ 1`. -/
def IsPSPrime (γ : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, 1 ≤ m ∧ (p : ℤ) = ⌊(m : ℝ) ^ (1 / γ)⌋

/-- `n` is a sum of three Piatetski-Shapiro primes for `γ`, each within `y` of `n/3`. -/
def IsAlmostEqualPSTernary (γ : ℝ) (n : ℕ) (y : ℝ) : Prop :=
  ∃ p₁ p₂ p₃ : ℕ, IsPSPrime γ p₁ ∧ IsPSPrime γ p₂ ∧ IsPSPrime γ p₃ ∧ p₁ + p₂ + p₃ = n ∧
    |(p₁ : ℝ) - n / 3| ≤ y ∧ |(p₂ : ℝ) - n / 3| ≤ y ∧ |(p₃ : ℝ) - n / 3| ≤ y

/-- For every large enough odd `n`, every `y > n^θ` admits a representation. -/
def SongWindow (γ θ : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ, (n : ℝ) ^ θ < y →
    IsAlmostEqualPSTernary γ n y

/-- The paper's window exponent `(52 − 45γ)/8`. -/
noncomputable def songExponent (γ : ℝ) : ℝ := (52 - 45 * γ) / 8

/-- Song 2020, Theorem 1. -/
def SongTheorem1 : Prop :=
  ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → SongWindow γ (songExponent γ)

/-! ### The paper, cited, with `sorry` -/

/-- P0078 Song 2020, Theorem 1. Cited, not proved here. -/
theorem song_theorem1 : SongTheorem1 := by sorry

/-! ### Links, zero sorry -/

theorem IsPSPrime.prime {γ : ℝ} {p : ℕ} (h : IsPSPrime γ p) : p.Prime := h.1

/-- At `γ = 1` the Piatetski-Shapiro primes are exactly the primes. -/
theorem isPSPrime_one_iff (p : ℕ) : IsPSPrime 1 p ↔ p.Prime := by
  refine ⟨fun h => h.1, fun hp => ⟨hp, p, hp.one_lt.le, ?_⟩⟩
  simp

theorem isAlmostEqualPSTernary_mono {γ : ℝ} {n : ℕ} {y y' : ℝ} (hy : y ≤ y')
    (H : IsAlmostEqualPSTernary γ n y) : IsAlmostEqualPSTernary γ n y' := by
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  exact ⟨a, b, c, ha, hb, hc, hs, h1.trans hy, h2.trans hy, h3.trans hy⟩

/-- Forget the Piatetski-Shapiro condition. -/
theorem IsAlmostEqualPSTernary.toAlmostEqual {γ : ℝ} {n : ℕ} {y : ℝ}
    (H : IsAlmostEqualPSTernary γ n y) : IsAlmostEqualTernary n y := by
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  exact ⟨a, b, c, ha.1, hb.1, hc.1, hs, h1, h2, h3⟩

/-- At `γ = 1` the two notions agree. -/
theorem isAlmostEqualPSTernary_one_iff {n : ℕ} {y : ℝ} :
    IsAlmostEqualPSTernary 1 n y ↔ IsAlmostEqualTernary n y := by
  refine ⟨fun H => H.toAlmostEqual, fun H => ?_⟩
  obtain ⟨a, b, c, ha, hb, hc, hs, h1, h2, h3⟩ := H
  exact ⟨a, b, c, (isPSPrime_one_iff a).2 ha, (isPSPrime_one_iff b).2 hb,
    (isPSPrime_one_iff c).2 hc, hs, h1, h2, h3⟩

/-- A smaller window exponent is a stronger statement. -/
theorem songWindow_mono {γ θ θ' : ℝ} (hθ : θ ≤ θ') (H : SongWindow γ θ) :
    SongWindow γ θ' := by
  obtain ⟨N₀, hN⟩ := H
  refine ⟨max N₀ 1, fun n ho hn y hy => ?_⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  exact hN n ho ((le_max_left _ _).trans hn) y
    (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le h1 hθ) hy)

/-- Restricted to ordinary primes, a Song window `θ` gives the almost equal Vinogradov
theorem for every strictly larger exponent. -/
theorem almostEqualVinogradov_of_songWindow {γ θ θ' : ℝ} (hθ : θ < θ')
    (H : SongWindow γ θ) : AlmostEqualVinogradov θ' := by
  obtain ⟨N₀, hN⟩ := H
  refine ⟨max N₀ 2, fun n ho hn => ?_⟩
  have h2 : (1 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    linarith
  exact (hN n ho ((le_max_left _ _).trans hn) _
    (Real.rpow_lt_rpow_of_exponent_lt h2 hθ)).toAlmostEqual

/-- At `γ = 1`, the almost equal Vinogradov theorem gives the Song window. -/
theorem songWindow_one_of_almostEqualVinogradov {θ : ℝ} (H : AlmostEqualVinogradov θ) :
    SongWindow 1 θ := by
  obtain ⟨N₀, hN⟩ := H
  exact ⟨N₀, fun n ho hn y hy =>
    isAlmostEqualPSTernary_one_iff.2 (isAlmostEqualTernary_mono hy.le (hN n ho hn))⟩

/-- So Matomaki-Maynard-Shao, cited in `LeanLab.Ternary`, would give the `γ = 1` window
for every `θ > 11/20`. Conditional on that statement as a hypothesis. -/
theorem songWindow_one_of_mms (H : ∀ θ : ℝ, 11 / 20 < θ → AlmostEqualVinogradov θ)
    (θ : ℝ) (hθ : 11 / 20 < θ) : SongWindow 1 θ :=
  songWindow_one_of_almostEqualVinogradov (H θ hθ)

/-- On the paper's range the window exponent lies strictly between 7/8 and 1. -/
theorem songExponent_mem {γ : ℝ} (h1 : 44 / 45 < γ) (h2 : γ < 1) :
    7 / 8 < songExponent γ ∧ songExponent γ < 1 := by
  unfold songExponent; constructor <;> linarith

/-- Theorem 1, restricted to ordinary primes, gives almost equal Vinogradov for every
`θ > 7/8`. This is weaker than Pan-Pan's `θ > 2/3`. -/
theorem almostEqualVinogradov_of_songTheorem1 (H : SongTheorem1) (θ : ℝ) (hθ : 7 / 8 < θ) :
    AlmostEqualVinogradov θ := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = max (44 / 45) ((52 - 8 * θ) / 45) := ⟨_, rfl⟩
  have hga := le_max_left (44 / 45 : ℝ) ((52 - 8 * θ) / 45)
  have hgb := le_max_right (44 / 45 : ℝ) ((52 - 8 * θ) / 45)
  rw [← hg] at hga hgb
  have hg1 : g < 1 := by rw [hg]; exact max_lt (by norm_num) (by linarith)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (g + 1) / 2 := ⟨_, rfl⟩
  have hγ1 : 44 / 45 < γ := by rw [hγ]; linarith
  have hγ2 : γ < 1 := by rw [hγ]; linarith
  have hlt : songExponent γ < θ := by unfold songExponent; rw [hγ]; linarith
  exact almostEqualVinogradov_of_songWindow hlt (H γ hγ1 hγ2)

/-! ### Why `γ` must be restricted: at `γ = 1/2` there are no such primes -/

theorem not_isPSPrime_half (p : ℕ) : ¬ IsPSPrime (1 / 2) p := by
  rintro ⟨hp, m, hm1, hm⟩
  have : (m : ℝ) ^ (1 / (1 / 2 : ℝ)) = ((m ^ 2 : ℕ) : ℝ) := by
    rw [show (1 / (1 / 2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; rfl
  rw [this, Int.floor_natCast] at hm
  have hpm : p = m ^ 2 := by exact_mod_cast hm
  rw [hpm] at hp
  rcases hp.eq_one_or_self_of_dvd m (dvd_pow_self m two_ne_zero) with h | h
  · subst h; norm_num at hp
  · have h2 := hp.two_le
    nlinarith

theorem not_songWindow_half (θ : ℝ) : ¬ SongWindow (1 / 2) θ := by
  rintro ⟨N₀, hN⟩
  obtain ⟨a, -, -, ha, -⟩ := hN (2 * N₀ + 1) ⟨N₀, rfl⟩ (by omega) _ (lt_add_one _)
  exact not_isPSPrime_half a ha

/-! ### Kernel checks at the sample exponent `γ = 2/3`, that is `c = 3/2` -/

theorem floor_rpow_threeHalves (m : ℕ) :
    ⌊(m : ℝ) ^ (1 / (2 / 3 : ℝ))⌋ = (Nat.sqrt (m ^ 3) : ℤ) := by
  have : (m : ℝ) ^ (1 / (2 / 3 : ℝ)) = √((m ^ 3 : ℕ) : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (1 / (2 / 3 : ℝ)) = ((3 : ℕ) : ℝ) * (1 / 2) by norm_num,
      Real.rpow_mul (by positivity), Real.rpow_natCast]
    push_cast; rfl
  rw [this, Real.floor_real_sqrt_eq_nat_sqrt]

theorem isPSPrime_twoThirds_iff (p : ℕ) :
    IsPSPrime (2 / 3) p ↔ p.Prime ∧ ∃ m ∈ Finset.Icc 1 p, Nat.sqrt (m ^ 3) = p := by
  unfold IsPSPrime
  simp only [floor_rpow_threeHalves, Nat.cast_inj, Finset.mem_Icc]
  refine and_congr_right fun _ => ⟨fun ⟨m, hm, he⟩ => ⟨m, ⟨hm, ?_⟩, he.symm⟩,
    fun ⟨m, ⟨hm, _⟩, he⟩ => ⟨m, hm, he.symm⟩⟩
  rw [he]
  calc m = Nat.sqrt (m * m) := (Nat.sqrt_eq m).symm
    _ ≤ Nat.sqrt (m ^ 3) := Nat.sqrt_le_sqrt (by
        rw [pow_succ, sq]; exact Nat.le_mul_of_pos_right _ (by omega))

theorem isPSPrime_twoThirds_2 : IsPSPrime (2 / 3) 2 :=
  (isPSPrime_twoThirds_iff 2).2 ⟨by norm_num, by decide +kernel⟩
theorem isPSPrime_twoThirds_5 : IsPSPrime (2 / 3) 5 :=
  (isPSPrime_twoThirds_iff 5).2 ⟨by norm_num, by decide +kernel⟩
theorem isPSPrime_twoThirds_11 : IsPSPrime (2 / 3) 11 :=
  (isPSPrime_twoThirds_iff 11).2 ⟨by norm_num, by decide +kernel⟩
theorem isPSPrime_twoThirds_31 : IsPSPrime (2 / 3) 31 :=
  (isPSPrime_twoThirds_iff 31).2 ⟨by norm_num, by decide +kernel⟩
theorem not_isPSPrime_twoThirds_3 : ¬ IsPSPrime (2 / 3) 3 := by
  rw [isPSPrime_twoThirds_iff]; decide +kernel
theorem not_isPSPrime_twoThirds_7 : ¬ IsPSPrime (2 / 3) 7 := by
  rw [isPSPrime_twoThirds_iff]; decide +kernel
theorem not_isPSPrime_twoThirds_13 : ¬ IsPSPrime (2 / 3) 13 := by
  rw [isPSPrime_twoThirds_iff]; decide +kernel

end LeanLab.Song2020
