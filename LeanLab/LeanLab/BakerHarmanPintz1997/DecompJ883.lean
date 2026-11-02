import LeanLab.BakerHarmanPintz1997.Decomp90

namespace LeanLab.BakerHarmanPintz1997.DecompJ883
open Finset Real Decomp90
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 21. Explicit Saving Parameter η. -/
theorem fgm_eta (ε : ℝ) (hε : 0 < ε) : 0 < min (ε / 8) (1 / 4) :=
  lt_min (by positivity) (by norm_num)

/-- LEAF. Page 21, Fujii-Gallagher-Montgomery bound. -/
theorem fgm_bound :
  ∃ C_FGM : ℝ, 0 < C_FGM ∧
  ∀ q : ℕ, q ≥ 1 → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
  ∀ N u : ℝ, 1 ≤ N → N ≤ u → u ≤ 2 * N →
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊u⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(t : ℂ) * Complex.I) -
    (if χ = 1 then 1 else 0 : ℂ) * (Nat.totient q : ℂ) / (q : ℂ) *
    ∫ y in N..u, (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_FGM * (q : ℝ) ^ (1 / 2 : ℝ) * (|t| + 1) ^ (1 / 2 : ℝ) * log ((q : ℝ) * (|t| + 2)) := by sorry

/-- LEAF. Page 21. Discretization error between discrete sum and integral. -/
theorem fgm_discretization_error :
  ∃ C_disc : ℝ, 0 ≤ C_disc ∧ ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ,
  ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ) ^ (-1 / 2 : ℂ) -
    ∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ C_disc * (N : ℝ) ^ (-1 / 2 : ℝ) := by sorry

/-- LEAF. Page 21. Main integral evaluation bound. -/
theorem fgm_integral_bound :
  ∀ N N1 : ℝ, 1 ≤ N → N ≤ N1 → N1 ≤ 2 * N → ∀ t : ℝ,
  ‖∫ y in N..N1, (y : ℂ) ^ (-1 / 2 : ℂ) * (y : ℂ) ^ (-(t : ℂ) * Complex.I)‖
  ≤ 5 * (N : ℝ) ^ (1 / 2 : ℝ) / (1 + |t|) := by sorry

/-- LEAF. Page 21. Frequency inequality conversion. -/
theorem fgm_frequency_conversion :
  ∀ x N t : ℝ, 2 ≤ x → x ^ (1/4 : ℝ) ≤ N → N ≤ x →
  |t| ^ (1 / 2 : ℝ) * x ^ (1 / 16 : ℝ) < N →
  (|t| + 1) ^ (1 / 2 : ℝ) ≤ 2 * N ^ (1 - 1 / 16 : ℝ) := by sorry

/-- LEAF. Page 21. Combination of remainder bounds. -/
theorem fgm_combine_remainders :
  ∀ C_FGM K_2 N ε : ℝ, 1 ≤ N → 0 < ε →
  C_FGM * N ^ (-1 / 2 : ℝ) * (K_2 * N ^ (ε / 8)) * (2 * N ^ (1 - ε / 4))
  ≤ 2 * C_FGM * K_2 * N ^ (1 / 2 - min (ε / 8) (1 / 4)) := by sorry

/-- LEAF. Page 21. Main decomposition branch -/
theorem fgm_branch :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 2 ≤ x → ∀ N N1 : ℝ, x ^ ε ≤ N → N ≤ x → N ≤ N1 → N1 ≤ 2 * N →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, |t| ≤ x → |t| ^ (1 / 2 : ℝ) * x ^ (ε / 4) < N →
      ‖∑ n ∈ Ioc ⌊N⌋₊ ⌊N1⌋₊, χ (n : ZMod q) * (n : ℂ) ^ (-(half t))‖ ≤
        C * (N ^ (1 / 2 - η) + N ^ (1 / 2 : ℝ) / (1 + |t|)) := by sorry
