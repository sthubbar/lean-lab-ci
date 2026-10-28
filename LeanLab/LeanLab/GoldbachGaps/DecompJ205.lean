import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main

namespace LeanLab.GoldbachGaps.DecompJ205
open Real Chebyshev Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

lemma fejer_eq (N K : ℕ) (hNK : K ≤ N) :
    fejer N K = ∑ n ∈ Icc (N - K) (N + K), ((K : ℝ) - |(n : ℝ) - N|) * Rg n := by
  unfold fejer
  apply sum_bij (fun j _ => j + N - K)
  case hi =>
    intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    have h1 : N - K ≤ a + N - K := by omega
    have h2 : a + N - K ≤ N + K := by omega
    exact ⟨h1, h2⟩
  case h =>
    intro a ha
    simp only [mem_range] at ha
    congr 2
    · have h1 : ((a + N - K : ℕ) : ℝ) = (a : ℝ) + (N : ℝ) - (K : ℝ) := by
        have : a + N ≥ K := by omega
        rw [Nat.cast_sub this, Nat.cast_add]
      rw [h1]
      have : (a : ℝ) + (N : ℝ) - (K : ℝ) - (N : ℝ) = (a : ℝ) - (K : ℝ) := by ring
      rw [this]
    · have h1 : N + a - K = a + N - K := by omega
      rw [h1]
  case i_inj =>
    intro a1 ha1 a2 ha2 heq
    omega
  case i_surj =>
    intro b hb
    simp only [mem_Icc] at hb
    use b - (N - K)
    have h1 : N - K ≤ b := hb.1
    have h2 : b ≤ N + K := hb.2
    refine ⟨?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega

/-- LEAF p. 291: fejer asymptotic from J = o(K^2 N) -/
theorem leaf_fejer_asymp (K : ℕ → ℕ) :
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1) := sorry

/-- LEAF p. 292: S(K+h) - S(K) lower bounds sum R -/
theorem leaf_sum_R_lower (N K h : ℕ) (hpos : 0 < h) :
    (fejer N (K + h) - fejer N K) / (h : ℝ) ≤ ∑ n ∈ Icc (N - K) (N + K), Rg n := sorry

/-- LEAF p. 292: S(K) - S(K-h) upper bounds sum R -/
theorem leaf_sum_R_upper (N K h : ℕ) (hpos : 0 < h) (hK : h ≤ K) :
    ∑ n ∈ Icc (N - K) (N + K), Rg n ≤ (fejer N K - fejer N (K - h)) / (h : ℝ) := sorry

/-- LEAF p. 292: Sum R is ~ 2KN -/
theorem leaf_sum_R_asymp (K : ℕ → ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1) := sorry

/-- LEAF p. 292: R to r relabeling gives Corollary 1 -/
theorem leaf_relabel (h_asymp : ∀ K : ℕ → ℕ, Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1)) : Corollary1 := sorry

theorem assembly_corollary1 : Corollary1 :=
  leaf_relabel leaf_sum_R_asymp

end LeanLab.GoldbachGaps.DecompJ205
