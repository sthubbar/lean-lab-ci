import LeanLab.ChenDoubleSieve.Lemma42Uk

/-!
# Wu 2004 Lemmas 4.1 and 4.2 for the twin prime sequence `B = {p + 2 : p ≤ x}`

P0036, Section 8, Theorem 3 sieves `B = {p + 2 : p ≤ x}` with the same weighted inequalities.
Unit U-5414, CLOUD 20261019T1014Z-cloud22. AI wrote the Lean code.
`Btwin x ⊆ {0, …, x + 2}`, so `lemma41_Uk` and `lemma42_Uk` apply with `N = x + 2` playing the
role of the bound on the sequence; `twin_lemma41`, `twin_lemma42` record that, with remainder
`i ((x + 2)/W + 2^i ∏ V_j)`. LIMITATION: `lemma41_Uk` ties the sieve modulus to the same `N`,
so these instances sieve by primes not dividing `d(x + 2)`, which is not Wu's twin prime sieve
set; the pointwise lemmas `lemma41_exact`, `lemma42_nat` hold for any modulus, and a twin version
of the `U_k` summation needs the modulus and the bound separated. Twin primes are not known to
be infinite.
-/

open Finset

noncomputable section
open scoped Classical

namespace LeanLab.ChenDoubleSieve.Wu42

open Wu41 (S Tset)

/-- `B = {p + 2 : p ≤ x prime}`. -/
def Btwin (x : ℕ) : Finset ℕ := ({p ∈ range (x + 1) | p.Prime} : Finset ℕ).image (· + 2)

lemma Btwin_sub (x : ℕ) : Btwin x ⊆ range (x + 2 + 1) := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hb
  have := mem_range.1 (mem_filter.1 hp).1
  exact mem_range.2 (by omega)

/-- **Lemma 4.1 for `B = {p + 2}`**, sieving `P(d(x + 2))`. -/
theorem twin_lemma41 (x i : ℕ) (V : Fin i → ℝ) {Δ W : ℝ} (hΔ : 1 < Δ) (hΔ' : Δ ≤ 3 / 2)
    (hV : ∀ j, 3 ≤ V j) (hW : 0 < W) (w z : (Fin i → ℕ) → ℝ)
    (hw : ∀ t ∈ Tset (x + 2) i V Δ, W ≤ w t) (hwz : ∀ t ∈ Tset (x + 2) i V Δ, w t ≤ z t) :
    2 * ∑ t ∈ Tset (x + 2) i V Δ, (S (Btwin x) (∏ j, t j) ((∏ j, t j) * (x + 2)) (z t) : ℝ) ≤
      ∑ t ∈ Tset (x + 2) i V Δ, ((Wu41.Ω₁ (Btwin x) (∏ j, t j) (x + 2) (w t) : ℝ)
        - Wu41.Ω₂ (Btwin x) (∏ j, t j) (x + 2) (w t) (z t)
        + Wu41.Ω₃ (Btwin x) (∏ j, t j) (x + 2) (w t) (z t))
        + i * (((x + 2 : ℕ) : ℝ) / W + 2 ^ i * ∏ j, V j) :=
  Wu41.lemma41_Uk (Btwin_sub x) i V hΔ hΔ' hV hW w z hw hwz

/-- **Lemma 4.2 for `B = {p + 2}`**. -/
theorem twin_lemma42 (x i : ℕ) (V : Fin i → ℝ) {Δ W : ℝ} (hΔ : 1 < Δ) (hΔ' : Δ ≤ 3 / 2)
    (hV : ∀ j, 3 ≤ V j) (hW : 0 < W) (w k₁ k₂ k₃ z : (Fin i → ℕ) → ℝ)
    (hw : ∀ t ∈ Tset (x + 2) i V Δ, W ≤ w t)
    (h01 : ∀ t ∈ Tset (x + 2) i V Δ, w t ≤ k₁ t) (h12 : ∀ t ∈ Tset (x + 2) i V Δ, k₁ t ≤ k₂ t)
    (h23 : ∀ t ∈ Tset (x + 2) i V Δ, k₂ t ≤ k₃ t) (h34 : ∀ t ∈ Tset (x + 2) i V Δ, k₃ t ≤ z t) :
    5 * ∑ t ∈ Tset (x + 2) i V Δ, (S (Btwin x) (∏ j, t j) ((∏ j, t j) * (x + 2)) (z t) : ℝ)
      + ∑ t ∈ Tset (x + 2) i V Δ,
          (lhs42 (Btwin x) (∏ j, t j) (x + 2) (w t) (k₂ t) (k₃ t) (z t) : ℝ) ≤
      ∑ t ∈ Tset (x + 2) i V Δ,
          (rhs42 (Btwin x) (∏ j, t j) (x + 2) (w t) (k₁ t) (k₂ t) (k₃ t) (z t) : ℝ)
        + 3 * (i * (((x + 2 : ℕ) : ℝ) / W + 2 ^ i * ∏ j, V j)) :=
  lemma42_Uk (Btwin_sub x) i V hΔ hΔ' hV hW w k₁ k₂ k₃ z hw h01 h12 h23 h34

end LeanLab.ChenDoubleSieve.Wu42
