/-
A falsifier for `leaf_threshold_inequality_F2551` of DecompF2551.lean. That leaf asserts the
inner body of Proposition 3.2, page 9 of Teravainen 2016, arXiv 1611.08585v2, for EVERY pair of
positive constants `δ₀`, `C`, while Proposition 3.2 only asserts it for SOME pair. With
`χ ≡ 1`, the left side grows like `δ₀ N / 6` while the weighted sum of `f` over `n ∼ N/3` is
`O(N)` by the upper bound sieve for primes `x² + y² + 1` in the progression `W n + b`. So a large
`δ₀` breaks the leaf. The theorem below proves this in Lean, CONDITIONAL ON that upper bound,
taken as the hypothesis `hU` with a constant `K` allowed to depend on `J`, `w` and `b`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.DecompF2551

namespace LeanLab.Teravainen2016

open Finset
open scoped Classical

/-- `#(dyad N) ≥ N/3 - 2`. -/
theorem dyad_card_lower (N : ℕ) : (N : ℝ) / 3 - 2 ≤ (#(dyad N) : ℝ) := by
  have hsub : Ico (N / 3 + 1) (2 * N / 3) ⊆ dyad N := by
    intro n hn
    rw [mem_Ico] at hn
    have h1 : N ≤ 3 * n := by omega
    have h2 : 3 * n < 2 * N := by omega
    have h1' : (N : ℝ) ≤ 3 * n := by exact_mod_cast h1
    have h2' : (3 : ℝ) * n < 2 * N := by exact_mod_cast h2
    simp only [dyad, mem_filter, mem_range]
    refine ⟨by omega, by linarith, by linarith⟩
  have hc := card_le_card hsub
  rw [Nat.card_Ico] at hc
  have h3 : N ≤ 3 * #(dyad N) + 6 := by omega
  have h3' : (N : ℝ) ≤ 3 * #(dyad N) + 6 := by exact_mod_cast h3
  linarith

/-- `leaf_threshold_inequality_F2551` fails for some positive `δ₀`, `C`, CONDITIONAL ON the
upper bound sieve estimate `hU`: for each admissible `J`, `w` and amenable `0 ≤ b < W` there is
`K` with `∑_{n ∼ N/3} f(n) ≤ K N` for all large `N`. -/
theorem not_leaf_threshold_inequality_F2551_of_upper
    (hU : ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, 0 ≤ b → b < WW J w →
      Amenable (WW J w) b → ∃ K : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∑ n ∈ dyad N, fW (WW J w) b N n ≤ K * N) :
    ¬ (∀ δ₀ C : ℝ, 0 < δ₀ → 0 < C →
      ∀ Cc J w : ℕ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w →
      ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
      ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ N : ℕ, N₀ ≤ N →
      ∀ t : ℤ, (N : ℝ) / 3 < t → (t : ℝ) < 2 * N / 3 →
        δ₀ * (∑ n ∈ dyad N, χ (t - n) - C * N / (w : ℝ) ^ ((1 : ℝ) / 3)) ≤
          ∑ n ∈ dyad N, fW (WW J w) b N n * χ (t - n)) := by
  intro H
  obtain ⟨w, hw⟩ := exists_nat_ge wBig
  have hw1 : (1 : ℝ) ≤ w := by
    have : (1 : ℝ) ≤ wBig := by
      unfold wBig
      exact Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  obtain ⟨b, -, hb0, hbW, -, -, hbam, -⟩ := amenable_pair_exists 5 w le_rfl
  obtain ⟨K, N₁, hK⟩ := hU 5 w le_rfl hw b hb0 hbW hbam
  set δ₀ : ℝ := 6 * (|K| + 1) with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  obtain ⟨N₀, hN₀⟩ := H δ₀ (1 / 12) hδ₀pos (by norm_num) 1 5 w le_rfl hw (by simpa using hw1)
  set N : ℕ := max (max N₀ N₁) 24 with hN
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN1 : N₁ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN24 : 24 ≤ N := le_max_right _ _
  have hN24' : (24 : ℝ) ≤ N := by exact_mod_cast hN24
  have ht1 : 3 * (N / 2) > N := by omega
  have ht2 : 3 * (N / 2) < 2 * N := by omega
  have ht1' : (N : ℝ) < 3 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast ht1
  have ht2' : 3 * ((N / 2 : ℕ) : ℝ) < 2 * N := by exact_mod_cast ht2
  have hcast : ((((N / 2 : ℕ) : ℤ)) : ℝ) = ((N / 2 : ℕ) : ℝ) := Int.cast_natCast _
  have h := hN₀ (fun _ => 1) (fun _ => zero_le_one) fourierComplexity_one b hb0 hbW hbam N hN0
    ((N / 2 : ℕ) : ℤ) (by rw [hcast]; linarith) (by rw [hcast]; linarith)
  simp only [mul_one, sum_const, nsmul_eq_mul] at h
  have hup := hK N hN1
  have hcard := dyad_card_lower N
  have hwpow : (1 : ℝ) ≤ (w : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hw1 (by norm_num)
  have hCN : 1 / 12 * (N : ℝ) / (w : ℝ) ^ ((1 : ℝ) / 3) ≤ 1 / 12 * N := by
    apply div_le_self (by positivity) hwpow
  have hlow : δ₀ * ((N : ℝ) / 6) ≤
      δ₀ * ((#(dyad N) : ℝ) * 1 - 1 / 12 * N / (w : ℝ) ^ ((1 : ℝ) / 3)) := by
    apply mul_le_mul_of_nonneg_left _ hδ₀pos.le
    linarith
  have hKabs : K * N ≤ |K| * N := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
  have : δ₀ * ((N : ℝ) / 6) = (|K| + 1) * N := by rw [hδ₀]; ring
  nlinarith

#print axioms dyad_card_lower
#print axioms not_leaf_threshold_inequality_F2551_of_upper

end LeanLab.Teravainen2016
