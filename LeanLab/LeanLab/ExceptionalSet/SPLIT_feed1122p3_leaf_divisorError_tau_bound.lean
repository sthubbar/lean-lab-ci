import LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_even_divisor_error_vanishes

/-!
Split of `leaf_divisorError_tau_bound` of
`LeanLab.ExceptionalSet.SPLIT_feed1122p2_leaf_even_divisor_error_vanishes`, burst-20261122
wave 13, session S132. Source P0082, Brudern and Perelli 1998, page 359, displays 14 and 15.

`divisorError r P m` is the sum of two envelopes, `(r/P) S₁` with `S₁` the finite sum over
`q ≤ P`, `r ∣ q`, display 14, and `r S₂` with `S₂` the tail over `q > P`, `r ∣ q`, display 15.
* `leaf_divisorError_finite`, display 14: `r S₁ ≤ C τ(m) P^ε`. LEAF, HARD.
* `leaf_divisorError_tail`, display 15: `r S₂ ≤ C τ(m) P^{ε-1}`. LEAF, HARD.
* `leaf_divisorError_tau_bound_of_leaves`, the exact statement, PROVED from the two leaves.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 359 display 14, the finite envelope, class HARD. For every `ε > 0` there is
`C > 0` with `r Σ_{q ≤ P, r ∣ q} q / (φ(q) φ(q/(m,q))) ≤ C τ(m) P^ε` whenever `P ≥ 2`, `1 ≤ r ≤ P`,
`m ≥ 1` and `(m, r) = 1`. The paper's bound is `τ(m) (log log P)^2 log P`. -/
theorem leaf_divisorError_finite :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (P : ℝ) (m : ℤ), 2 ≤ P → 1 ≤ r → (r : ℝ) ≤ P → 1 ≤ m → Int.gcd m r = 1 →
        (r : ℝ) * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
            (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))
          ≤ C * (m.toNat.divisors.card : ℝ) * P ^ ε := by
  sorry

/-- LEAF: P0082 page 359 display 15, the tail envelope, class HARD. For every `ε > 0` there is
`C > 0` with `r Σ_{q > P, r ∣ q} 1 / (φ(q) φ(q/(m,q))) ≤ C τ(m) P^{ε-1}` under the same conditions.
The paper's bound is `τ(m) (log log P)^3 / P`. -/
theorem leaf_divisorError_tail :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (P : ℝ) (m : ℤ), 2 ≤ P → 1 ≤ r → (r : ℝ) ≤ P → 1 ≤ m → Int.gcd m r = 1 →
        (r : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) ∧ r ∣ q then
            1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0)
          ≤ C * (m.toNat.divisors.card : ℝ) * P ^ (ε - 1) := by
  sorry

/-- The exact statement of `leaf_divisorError_tau_bound`, from the two leaves. -/
theorem leaf_divisorError_tau_bound_of_leaves :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (P : ℝ) (m : ℤ), 2 ≤ P → 1 ≤ r → (r : ℝ) ≤ P → 1 ≤ m → Int.gcd m r = 1 →
        divisorError r P m ≤ C * (m.toNat.divisors.card : ℝ) * P ^ (ε - 1) := by
  intro ε hε
  obtain ⟨C1, hC1, H1⟩ := leaf_divisorError_finite ε hε
  obtain ⟨C2, hC2, H2⟩ := leaf_divisorError_tail ε hε
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro r P m hP hr hrP hm hg
  have hP0 : 0 < P := by linarith
  have h1 := H1 r P m hP hr hrP hm hg
  have h2 := H2 r P m hP hr hrP hm hg
  have hpow : P ^ ε / P = P ^ (ε - 1) := by
    rw [Real.rpow_sub_one hP0.ne']
  unfold divisorError
  have e1 : (r : ℝ) / P * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
        (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))
      = ((r : ℝ) * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
        (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))) / P := by ring
  have h1' : (r : ℝ) / P * ∑ q ∈ (Icc 1 ⌊P⌋₊).filter (fun q => r ∣ q),
        (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ))
      ≤ C1 * (m.toNat.divisors.card : ℝ) * P ^ (ε - 1) := by
    rw [e1, div_le_iff₀ hP0, ← hpow]
    have : C1 * (m.toNat.divisors.card : ℝ) * (P ^ ε / P) * P
        = C1 * (m.toNat.divisors.card : ℝ) * P ^ ε := by field_simp
    rw [this]; exact h1
  have := add_le_add h1' h2
  linarith
