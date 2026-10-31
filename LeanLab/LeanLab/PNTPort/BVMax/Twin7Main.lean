import LeanLab.PNTPort.BVMax.Twin7

/-!
# Rényi's twin theorem with `K = 7`, the unconditional statements

Unit U-6804, CLOUD 20261021T0117Z-cloud55, idea I-5051. AI wrote the Lean code. Known mathematics, Rényi 1948
type with a small explicit `K`; Chen 1973 has `Ω(p + 2) ≤ 2`, far stronger, so nothing here is new
mathematics. Ineffective `N₀`, through Siegel-Walfisz inside the lab's Bombieri-Vinogradov `bvPi`.
The twin prime conjecture is `Ω(p + 2) = 1` and stays OPEN.
-/

namespace LeanLab.PNTPort.BVMax

open Finset LeanLab.PNTSieve.Bonferroni

open Filter in
/-- **Rényi's twin theorem with the count and `K = 7`, PROVED unconditional**: for every large
`N`, `#{p ≤ N prime : Ω(p + 2) ≤ 7} ≥ e^{-36} N/log² N`. Ineffective. -/
theorem twin7_renyi_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    Real.exp (-36) * N / Real.log N ^ 2 ≤
      ((((Icc 1 N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 7)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := twin_rem_family 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B (100 * |K|)
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 2100)))
  refine ⟨max ⌈max (max X X₂) Y⌉₊ 2, fun N hN => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact twin7_count N (hK N hN2) (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's twin theorem with `K = 7`, PROVED unconditional**: there are infinitely many primes
`p` with `Ω(p + 2) ≤ 7`. The twin prime conjecture is `Ω(p + 2) = 1` and stays OPEN; Chen 1973
has `Ω(p + 2) ≤ 2`. -/
theorem twin7_infinite :
    {p : ℕ | p.Prime ∧ ArithmeticFunction.cardFactors (p + 2) ≤ 7}.Infinite := by
  obtain ⟨N₀, hN₀⟩ := twin7_renyi_count
  refine Set.infinite_of_not_bddAbove (fun ⟨M, hM⟩ => ?_)
  set k := ⌈48 * Real.exp 36 * ((M : ℝ) + 1)⌉₊ + N₀ + 2 with hk
  have hkN : N₀ ≤ k ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) k)
  have h := hN₀ (k ^ 2) hkN
  -- the count is at most M
  have hcard : ((((Icc 1 (k ^ 2)).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 7)).card : ℝ) ≤ M := by
    have hsub : (((Icc 1 (k ^ 2)).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (p + 2) ≤ 7)) ⊆ Icc 1 M := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp
      rw [mem_Icc]
      exact ⟨hp.1.1.1, hM ⟨hp.1.2, hp.2⟩⟩
    have hI : (Icc 1 M).card = M := by simp
    have := (card_le_card hsub).trans hI.le
    exact_mod_cast this
  -- the lower bound exceeds M
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  have hkbig : 48 * Real.exp 36 * ((M : ℝ) + 1) ≤ k := by
    have := Nat.le_ceil (48 * Real.exp 36 * ((M : ℝ) + 1))
    have h' : ((⌈48 * Real.exp 36 * ((M : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ k := by
      exact_mod_cast (show ⌈48 * Real.exp 36 * ((M : ℝ) + 1)⌉₊ ≤ k by omega)
    linarith
  have hlk0 : 0 < Real.log k := Real.log_pos (by linarith)
  have hlk : Real.log k ≤ 2 * Real.sqrt k := by
    have := Real.log_le_rpow_div hkpos.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hsq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hkpos.le
  have hlN : Real.log ((k ^ 2 : ℕ) : ℝ) = 2 * Real.log k := by
    push_cast; rw [Real.log_pow]; norm_num
  have hl2 : Real.log ((k ^ 2 : ℕ) : ℝ) ^ 2 ≤ 16 * k := by
    rw [hlN]
    have h0 : 0 ≤ Real.log k := hlk0.le
    have := mul_le_mul hlk hlk h0 (by positivity)
    nlinarith
  have hlpos : 0 < Real.log ((k ^ 2 : ℕ) : ℝ) ^ 2 := by rw [hlN]; positivity
  have he : Real.exp (-36) * Real.exp 36 = 1 := by rw [← Real.exp_add]; norm_num
  have hM1 : (M : ℝ) + 1 ≤ Real.exp (-36) * ((k ^ 2 : ℕ) : ℝ) /
      Real.log ((k ^ 2 : ℕ) : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
    have h1 : ((M : ℝ) + 1) * Real.log ((k ^ 2 : ℕ) : ℝ) ^ 2 ≤ ((M : ℝ) + 1) * (48 * k) :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    have h2 : Real.exp (-36) * (48 * Real.exp 36 * ((M : ℝ) + 1)) ≤ Real.exp (-36) * k :=
      mul_le_mul_of_nonneg_left hkbig (Real.exp_pos _).le
    have h3 : Real.exp (-36) * (48 * Real.exp 36 * ((M : ℝ) + 1)) = 48 * ((M : ℝ) + 1) := by
      rw [show Real.exp (-36) * (48 * Real.exp 36 * ((M : ℝ) + 1)) =
        (Real.exp (-36) * Real.exp 36) * (48 * ((M : ℝ) + 1)) by ring, he, one_mul]
    have h4 : ((M : ℝ) + 1) * (48 * k) ≤ Real.exp (-36) * k * k := by
      have := mul_le_mul_of_nonneg_right (h3 ▸ h2) hkpos.le
      linarith
    have h5 : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) * k := by push_cast; ring
    have h6 : Real.exp (-36) * ((k ^ 2 : ℕ) : ℝ) = Real.exp (-36) * k * k := by rw [h5]; ring
    rw [h6]
    linarith
  linarith

end LeanLab.PNTPort.BVMax
