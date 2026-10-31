import LeanLab.PNTPort.BVMax.Renyi6Step

/-!
# Rényi's theorem with `K = 6` by step weights, the unconditional statements

Unit U-6801, CLOUD 20261021T0117Z-cloud55, idea I-5051. AI wrote the Lean code. Known
mathematics, Rényi 1948 type with a small explicit `K` and stepped Kuhn and Richert type
weights; Pan K = 4 and 5 and Chen 1973 K = 2 are far stronger, so nothing here is new
mathematics. Ineffective `N₀`, through Siegel-Walfisz inside the lab's Bombieri-Vinogradov `bvPi`. Binary Goldbach is `Ω(m) = 1` and stays OPEN.
-/

namespace LeanLab.PNTPort.BVMax.Step6

open Finset LeanLab.PNTSieve.Bonferroni LeanLab.PNTPort.BVMax

open Filter in
/-- **Rényi's theorem with the count and `K = 6`, PROVED unconditional**: for every large even
`N`, `#{p < N prime : Ω(N - p) ≤ 6} ≥ e^{-36} N/(2 log² N)`. Ineffective. -/
theorem renyi6s_fixedK_count : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    Real.exp (-36) * N / (2 * Real.log N ^ 2) ≤
      ((((range N).filter Nat.Prime).filter
        (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 6)).card : ℝ) := by
  obtain ⟨B, -, K, hK⟩ := renyi_rem_family 5 (by norm_num)
  obtain ⟨X, hX⟩ := renyi_large B (100 * |K|)
  obtain ⟨X₂, hX₂⟩ := renyi_large49 B
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 : ℝ) ^ 2100)))
  refine ⟨max ⌈max (max X X₂) Y⌉₊ 2, fun N hN hE => ?_⟩
  have hx : max (max X X₂) Y ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨_, _, _, h3⟩ := hX N ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  exact renyi6s_count N (hK N hN2) hE (hY N ((le_max_right _ _).trans hx))
    (hX₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hx))) h3

/-- **Rényi's theorem with `K = 6`, PROVED unconditional.** There is `N₀` such that every even
`N ≥ N₀` is `p + m` with `p` prime, `m ≥ 1` and `Ω(m) ≤ 6`. Ineffective. Binary Goldbach is
`Ω(m) = 1` and stays OPEN; Chen 1973 has `Ω(m) ≤ 2`. -/
theorem renyi6s_fixedK : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ ArithmeticFunction.cardFactors m ≤ 6 := by
  obtain ⟨N₀, hN₀⟩ := renyi6s_fixedK_count
  refine ⟨max N₀ 4, fun N hN hE => ?_⟩
  have h := hN₀ N ((le_max_left _ _).trans hN) hE
  have h4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < Real.exp (-36) * N / (2 * Real.log N ^ 2) := by positivity
  have hc : 0 < (((range N).filter Nat.Prime).filter
      (fun p => ArithmeticFunction.cardFactors (N - p) ≤ 6)).card := by
    exact_mod_cast hpos.trans_le h
  obtain ⟨p, hp⟩ := card_pos.mp hc
  simp only [mem_filter, mem_range] at hp
  obtain ⟨⟨hpN, hpp⟩, hΩ⟩ := hp
  exact ⟨p, N - p, hpp, by omega, by omega, hΩ⟩

#print axioms renyi6s_count
#print axioms renyi6s_fixedK_count
#print axioms renyi6s_fixedK
#print axioms bad6
#print axioms range_upper
#print axioms prod_ratio

end LeanLab.PNTPort.BVMax.Step6
