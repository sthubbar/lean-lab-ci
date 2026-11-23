import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination

/-!
Split of `leaf_even_divisor_error_vanishes` of
`LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_even_index_coefficient_domination`, burst-20261122
feed1122, session S89. Source P0082, Brudern and Perelli 1998, page 359 displays 14 and 15.

`divisorError r P m` is the sum of two envelopes: the truncated sum of display 14,
`(r/P) ∑_{q ≤ P, r ∣ q} q / (φ(q) φ(q/(m,q)))`, and the tail of display 15,
`r ∑_{q > P, r ∣ q} 1 / (φ(q) φ(q/(m,q)))`. Each leaf asks that one envelope be at most `η/2`
for large `N`, uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`; the
assembly unfolds the definition and adds. Each leaf names one display only.

Why each is true: writing `q = r k`, with `(m, r) = 1`, one has `q/(m,q) = r k/(m,k)` and
`φ(q/(m,q)) ≥ φ(r) φ(k/(m,k))`. Grouping `k` by `(m,k)` gives each envelope at most
`τ(m) log P / P` times a power of `log log P`, and the divisor bound gives `τ(m) = X^{o(1)}`
against `P = X^{6δ}`. Neither bound needs the conductor to be large.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 359 display 14, the truncated envelope of `Γ₁`, is `o(1)`: at most `η/2`
for large `N`, uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`. HARD: the
grouping of `q = r k` by `(m, k)` and the divisor bound `τ(m) = X^{o(1)}`. -/
theorem leaf_divisor_envelope_truncated (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            (r : ℝ) / F γ N ^ (6 * δ) *
              ∑ q ∈ (Icc 1 ⌊F γ N ^ (6 * δ)⌋₊).filter (fun q => r ∣ q),
                (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) ≤ η / 2 := by
  sorry

/-- LEAF: P0082 page 359 display 15, the tail envelope of `Γ₂`, is `o(1)`: at most `η/2` for
large `N`, uniformly over `X/2 < m ≤ X` coprime to `r` and `1 ≤ r ≤ P = X^{6δ}`. HARD: the
same grouping, with the tail of `∑ 1/φ(l)^2` and the divisor bound. -/
theorem leaf_divisor_envelope_tail (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            (r : ℝ) * ∑' q : ℕ, (if F γ N ^ (6 * δ) < (q : ℝ) ∧ r ∣ q then
              1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0) ≤ η / 2 := by
  sorry

/-- Assembly of `leaf_even_divisor_error_vanishes`: the two envelopes, each at most `η/2`. -/
theorem leaf_even_divisor_error_vanishes_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
      ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
          ∀ m : ℤ, F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N → Int.gcd m r = 1 →
            divisorError r (F γ N ^ (6 * δ)) m ≤ η := by
  intro η hη δ hδ hδ1
  obtain ⟨Na, ha⟩ := leaf_divisor_envelope_truncated γ h1 h2 η hη δ hδ hδ1
  obtain ⟨Nb, hb⟩ := leaf_divisor_envelope_tail γ h1 h2 η hη δ hδ hδ1
  refine ⟨max Na Nb, fun N hN r hr hrP m hm1 hm2 hg => ?_⟩
  obtain ⟨hNa, hNb⟩ := max_le_iff.mp hN
  have hA := ha N hNa r hr hrP m hm1 hm2 hg
  have hB := hb N hNb r hr hrP m hm1 hm2 hg
  unfold divisorError
  linarith

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
