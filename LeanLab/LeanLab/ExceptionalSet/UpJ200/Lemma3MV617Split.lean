import LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit

/-!
# Split of the LEAF `mv_617_tilde` of `Lemma3MVSplit`

Burst burst-20261122, unit mv617tilde_split, run by Claude cloud session S67.

Source P0015, Montgomery and Vaughan 1975, read from the page images of `papers/P0015.pdf`,
pages 364 and 365. On page 364 MV define the exceptional main integral as
`Ĩ(n) = ∫_0^1 T̃(η)² e(-nη) dη`, and only at the foot of page 365 do they write
"Clearly `Ĩ(n) = Σ_{P<k<n-P} (k(n-k))^{β̃-1}`". The lab's `Itilde` of P0082 display (13) is that
finite sum. The split follows MV's order.

* LEAF `mv_617_tilde_integral`: P0015 display (6.1̃7) with `Ĩ(n)` as MV define it on page 364, the
  integral of `T̃²`, and the errors of (6.19) kept explicit as in the parent leaf. HARD.
* LEAF `mv_Itilde_eval`: the evaluation on page 365, `Ĩ(n)` integral equals the finite sum, for
  `1 ≤ n ≤ X` and `P ≥ 0`. EASY, orthogonality of `e(kη)` on `[0,1]`.
* PROVED from the two leaves, no other sorry: `mv_617_tilde_of_leaves`, whose type is checked
  equal to `type_of% @Lemma3MVSplit.mv_617_tilde`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Split

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde mvWtilde)

/-- LEAF: P0015 page 365, the evaluation "Clearly `Ĩ(n) = Σ_{P<k<n-P} (k(n-k))^{β̃-1}`" of the
integral `Ĩ(n) = ∫_0^1 T̃(η)² e(-nη) dη` defined on page 364, class EASY. With
`T̃(η) = -Σ_{P<k≤X} k^{β̃-1} e(kη)` of page 361, orthogonality on `[0,1]` keeps the pairs
`k + l = n` with `P < k, l ≤ X`; for `1 ≤ n ≤ X` the bound `≤ X` is automatic, and `P ≥ 0`
gives `0 < k < n`. -/
theorem mv_Itilde_eval : ∀ β P X : ℝ, 0 ≤ P → ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X →
    (∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * m))) = ((Itilde β P m : ℝ) : ℂ) := by
  sorry

/-- LEAF: P0015 display (6.1̃7), page 365, with `Ĩ(n)` the integral `∫_0^1 T̃(η)² e(-nη) dη`
as defined on page 364, class HARD. It collects (6.4̃), (6.6̃), (6.10̃), (6.12̃), (6.16̃), (6.18),
(6.19) and (6.20) on top of the non exceptional (6.4) to (6.16). If the exceptional character
`χ̃` of modulus `r̃ ≤ P` exists with zero `β̃`, then for even `1 ≤ m ≤ X`
`R₁(m) = 𝔖(m) m + 𝔖̃(m) Ĩ(m) + O(χ̃(m)² r̃ m X / (φ(r̃)² φ(m))) + XΓ₁(m) + XΓ₂(m)
  + O(m φ(m)⁻¹ (X^{1/2} W + W²))`,
the error `X^{1+δ}P⁻¹(n,r̃)` of (6.19) and of the display after it kept explicit as in the
parent leaf `Lemma3MVSplit.mv_617_tilde`, bounded by the lab's `divisorError`, envelopes (14)
and (15) of P0082. Same hypotheses and quantifier order as the parent leaf. -/
theorem mv_617_tilde_integral : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m →
        |(R1 (X ^ θ) X m).re - (m * singSeries m +
            (∫ η in (0 : ℝ)..1, Ttilde β (X ^ θ) X η ^ 2 * eC (-(η * m))).re *
              twistedSing χ m)| ≤
          C * X * divisorError r (X ^ θ) m +
          C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
            ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) +
          C * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) *
            (mvWtilde β (X ^ θ) X χ * Real.sqrt X + mvWtilde β (X ^ θ) X χ ^ 2) := by
  sorry

/-- PROVED from the two leaves `mv_617_tilde_integral` and `mv_Itilde_eval`: the parent LEAF
`Lemma3MVSplit.mv_617_tilde`, P0015 display (6.1̃7). -/
theorem mv_617_tilde_of_leaves : type_of% @Lemma3MVSplit.mv_617_tilde := by
  intro a ha
  obtain ⟨C, hC, h⟩ := mv_617_tilde_integral a ha
  refine ⟨C, hC, fun θ hθ hθ1 => ?_⟩
  obtain ⟨P₀, hP⟩ := h θ hθ hθ1
  refine ⟨P₀, fun X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev => ?_⟩
  have hI := mv_Itilde_eval β (X ^ θ) X (Real.rpow_nonneg hX.le θ) m hm hmX
  have key := hP X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev
  rw [hI, Complex.ofReal_re] at key
  exact key

/-- The assembly has exactly the type of the parent leaf. -/
example : type_of% @mv_617_tilde_of_leaves = type_of% @Lemma3MVSplit.mv_617_tilde := rfl

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Split

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Split.mv_617_tilde_of_leaves
