import LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082
import LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

/-!
# Split of `BPLemma3Hyp` into the displays of Montgomery and Vaughan 1975

Burst burst-20261122, unit lemma3_split, run by Claude cloud session S67.

Source P0082, Brüdern and Perelli 1998, page 358 Lemma 3 with displays (12) to (15) of page 359,
whose proof reads: "This is (6.1̃7) of Montgomery & Vaughan [MV], with the error in (6.19) and
thereafter kept explicit, followed by an appeal to their (7.1̃) to estimate W." Source P0015,
Montgomery and Vaughan 1975, read from the page images of `papers/P0015.pdf`: page 361 for `T̃(η)`
and the decomposition `S(χ̃χ₀,η) = T̃(η) + W(χ̃χ₀,η)`, page 365 for (6.19) and (6.1̃7), page 366 for
(7.1̃).

Structure.
* DEFINITIONS `Ttilde`, `WnormTilde`, `mvWtilde`: P0015 page 361 and display (6.5) and the first
  display of section 7, for the exceptional character.
* LEAF `mv_617_tilde`: P0015 display (6.1̃7), with the error `X^{1+δ}P⁻¹(n,r̃)` of (6.19) and the
  display after it kept explicit as `XΓ₁ + XΓ₂`, bounded by the envelopes (14) and (15) of P0082,
  the lab's `divisorError`.
* LEAF `mv_71_tilde`: P0015 display (7.1̃).
* PROVED, sorry free from the two leaves: `w_terms_le`, the arithmetic that turns
  `n φ(n)⁻¹ (X^{1/2} W + W²)` into the last error term of Lemma 3, and the assembly
  `bpLemma3Hyp_of_leaves : BPLemma3Hyp`.

The P0 after θ order of `BPLemma3Hyp` is kept: both leaves give `C`, `c₆` before `θ`, and the
threshold `P₀` after `θ`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde)
open LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082 (BPLemma3Hyp)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (Wchi Wnorm mvW)

/-! ### Definitions, each a display of P0015 -/

/-- P0015 page 361: `T̃(η) = - Σ_{P<n≤X} n^{β̃-1} e(nη)`, defined when there is an exceptional
zero `β̃`. -/
noncomputable def Ttilde (β P X η : ℝ) : ℂ :=
  -∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, (((n : ℝ) ^ (β - 1) : ℝ) : ℂ) * eC (η * n)

/-- P0015 page 361 and display (6.5) for the exceptional character: `S(χ̃χ₀,η) = T̃(η) +
W(χ̃χ₀,η)`, and `W(χ̃) = (∫_{-1/r̃Q}^{1/r̃Q} |W(χ̃,η)|² dη)^{1/2}`. Since `χ̃ ≠ χ₀`, the lab's
`Wchi` of `χ̃` is `S(χ̃,η)`, and the exceptional `W(χ̃,η)` is `S(χ̃,η) - T̃(η)`. -/
noncomputable def WnormTilde {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) : ℝ :=
  Real.sqrt (∫ η in (-(P / (r * X)))..(P / (r * X)), ‖Wchi P X χ η - Ttilde β P X η‖ ^ 2)

/-- P0015 page 366, first display of section 7, when the exceptional term occurs:
`W = Σ_{q≤P} Σ*_χ W(χ)`, where for the one primitive exceptional character `χ̃` of modulus
`r̃ ≤ P` the summand is the exceptional `W(χ̃)` of page 361. Written as `mvW`, whose `χ̃` summand
is the unmodified `Wnorm`, with that one summand replaced. -/
noncomputable def mvWtilde {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) : ℝ :=
  mvW P X - Wnorm P X χ + WnormTilde β P X χ

/-! ### Leaves -/

/-- LEAF: P0015 display (6.1̃7), page 365, with P0082 page 359 displays (12) to (15), class HARD.
If the exceptional character `χ̃` of modulus `r̃ ≤ P` exists with zero `β̃`, then for even
`1 ≤ m ≤ X`
`R₁(m) = 𝔖(m) m + 𝔖̃(m) Ĩ(m) + O(χ̃(m)² r̃ m X / (φ(r̃)² φ(m))) + XΓ₁(m) + XΓ₂(m)
  + O(m φ(m)⁻¹ (X^{1/2} W + W²))`,
where, as P0082 page 358 says, the error of (6.19) and of the display after it is kept explicit
as `XΓ₁ + XΓ₂`, bounded by the envelopes (14) and (15), the lab's `divisorError`. Same
hypotheses and quantifier order as `BPLemma3Hyp`. -/
theorem mv_617_tilde : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m →
        |(R1 (X ^ θ) X m).re - (m * singSeries m + Itilde β (X ^ θ) m * twistedSing χ m)| ≤
          C * X * divisorError r (X ^ θ) m +
          C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
            ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) +
          C * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) *
            (mvWtilde β (X ^ θ) X χ * Real.sqrt X + mvWtilde β (X ^ θ) X χ ^ 2) := by
  sorry

/-- LEAF: P0015 display (7.1̃), page 366, class HARD. If the exceptional term occurs then
`W ≪ X^{1/2} (1 - β̃) exp(-c₆ log X / log P) log P`; here `log X / log P = 1/θ`. Proved by MV from
Lemma 4.2 and Lemma 4.3, Gallagher's Theorem 7 with the Deuring Heilbronn phenomenon. The range
`θ < 6/100` is the range P0082 page 357 claims; see the QUESTION in the notes file. -/
theorem mv_71_tilde : ∀ a : ℝ, 0 < a → ∃ B c₆ : ℝ, 0 < B ∧ 0 < c₆ ∧
    ∀ θ : ℝ, 0 < θ → θ < 6 / 100 → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
        |mvWtilde β (X ^ θ) X χ| ≤
          B * Real.sqrt X * (1 - β) * Real.exp (-(c₆ / θ)) * Real.log (X ^ θ) := by
  sorry

/-! ### Assembly, PROVED -/

/-- The arithmetic step of P0082 Lemma 3: with `|W| ≤ B X^{1/2} E`, `E = (1-β̃) e log P`,
`0 ≤ (1-β̃) log P ≤ a` and `0 ≤ e ≤ 1`, one has `X^{1/2} W + W² ≤ (B + B² a) X E`. PROVED. -/
theorem w_terms_le (W B X u e a : ℝ) (hB : 0 ≤ B) (hX : 0 ≤ X) (hu : 0 ≤ u) (hua : u ≤ a)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hW : |W| ≤ B * Real.sqrt X * (u * e)) :
    W * Real.sqrt X + W ^ 2 ≤ (B + B ^ 2 * a) * X * (u * e) := by
  have hs : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX
  have hue : 0 ≤ u * e := mul_nonneg hu he
  have h1 : W * Real.sqrt X ≤ B * X * (u * e) := by
    calc W * Real.sqrt X ≤ |W| * Real.sqrt X :=
          mul_le_mul_of_nonneg_right (le_abs_self W) hs
      _ ≤ B * Real.sqrt X * (u * e) * Real.sqrt X := mul_le_mul_of_nonneg_right hW hs
      _ = B * (u * e) * (Real.sqrt X * Real.sqrt X) := by ring
      _ = B * X * (u * e) := by rw [hss]; ring
  have hE2 : (u * e) ^ 2 ≤ a * (u * e) := by
    have : u * e ≤ a := by nlinarith
    nlinarith
  have h2 : W ^ 2 ≤ B ^ 2 * a * X * (u * e) := by
    have hW0 : 0 ≤ B * Real.sqrt X * (u * e) := by positivity
    calc W ^ 2 = |W| ^ 2 := (sq_abs W).symm
      _ ≤ (B * Real.sqrt X * (u * e)) ^ 2 := pow_le_pow_left₀ (abs_nonneg W) hW 2
      _ = B ^ 2 * (Real.sqrt X * Real.sqrt X) * (u * e) ^ 2 := by ring
      _ ≤ B ^ 2 * (Real.sqrt X * Real.sqrt X) * (a * (u * e)) := by
          apply mul_le_mul_of_nonneg_left hE2; positivity
      _ = B ^ 2 * a * X * (u * e) := by rw [hss]; ring
  nlinarith

/-- P0082 page 358 Lemma 3, `BPLemma3Hyp`: "(6.1̃7) of Montgomery & Vaughan, with the error in
(6.19) and thereafter kept explicit, followed by an appeal to their (7.1̃) to estimate W".
PROVED from the two leaves `mv_617_tilde` and `mv_71_tilde`, no further sorry. -/
theorem bpLemma3Hyp_of_leaves : BPLemma3Hyp := by
  intro a ha
  obtain ⟨CA, hCA, hA⟩ := mv_617_tilde a ha
  obtain ⟨B, c₆, hB, hc₆, hW⟩ := mv_71_tilde a ha
  refine ⟨CA * (1 + B + B ^ 2 * a), c₆, by positivity, hc₆, ?_⟩
  intro θ hθ hθ6
  obtain ⟨PA, hPA⟩ := hA θ hθ hθ6
  obtain ⟨PB, hPB⟩ := hW θ hθ hθ6
  refine ⟨max (max PA PB) 2, ?_⟩
  intro X hX hP r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL m hm1 hmX hev
  have hPA' : PA ≤ X ^ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP
  have hPB' : PB ≤ X ^ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP
  have hP2 : (2 : ℝ) ≤ X ^ θ := le_trans (le_max_right _ _) hP
  have hlogP : 0 < Real.log (X ^ θ) := Real.log_pos (by linarith)
  have hA1 := hPA X hX hPA' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL m hm1 hmX hev
  have hW1 := hPB X hX hPB' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL
  set P := X ^ θ with hPdef
  set W := mvWtilde β P X χ
  set M := (m.toNat : ℝ) / (m.toNat.totient : ℝ)
  set u := (1 - β) * Real.log P with hu
  set e := Real.exp (-(c₆ / θ)) with he
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) hlogP.le
  have hua : u ≤ a := by
    have h1 : 1 - β ≤ a / Real.log P := by linarith
    exact (le_div_iff₀ hlogP).mp h1
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; exact neg_nonpos.mpr (div_nonneg hc₆.le hθ.le)
  have hW2 : |W| ≤ B * Real.sqrt X * (u * e) := by
    have : B * Real.sqrt X * (1 - β) * e * Real.log P = B * Real.sqrt X * (u * e) := by
      rw [hu]; ring
    rw [← this]; exact hW1
  have hterms := w_terms_le W B X u e a hB.le hX.le hu0 hua he0 he1 hW2
  have hM : 0 ≤ M := by positivity
  have hD : 0 ≤ divisorError r P m := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hchi : 0 ≤ X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M := by positivity
  have hk : 1 ≤ 1 + B + B ^ 2 * a := by
    have := mul_nonneg (sq_nonneg B) ha.le; linarith
  have hCk : CA ≤ CA * (1 + B + B ^ 2 * a) := le_mul_of_one_le_right hCA.le hk
  have hfin : CA * M * (W * Real.sqrt X + W ^ 2) ≤
      CA * (1 + B + B ^ 2 * a) * X * M * (1 - β) * e * Real.log P := by
    have h1 : CA * M * (W * Real.sqrt X + W ^ 2) ≤ CA * M * ((B + B ^ 2 * a) * X * (u * e)) :=
      mul_le_mul_of_nonneg_left hterms (by positivity)
    have h2 : CA * M * ((B + B ^ 2 * a) * X * (u * e)) ≤
        CA * (1 + B + B ^ 2 * a) * X * M * (u * e) := by
      have hY : 0 ≤ CA * X * M * (u * e) := by positivity
      calc CA * M * ((B + B ^ 2 * a) * X * (u * e)) = (B + B ^ 2 * a) * (CA * X * M * (u * e)) := by
            ring
        _ ≤ (1 + B + B ^ 2 * a) * (CA * X * M * (u * e)) :=
            mul_le_mul_of_nonneg_right (by linarith) hY
        _ = CA * (1 + B + B ^ 2 * a) * X * M * (u * e) := by ring
    calc CA * M * (W * Real.sqrt X + W ^ 2) ≤ CA * (1 + B + B ^ 2 * a) * X * M * (u * e) :=
          h1.trans h2
      _ = CA * (1 + B + B ^ 2 * a) * X * M * (1 - β) * e * Real.log P := by rw [hu]; ring
  have hXD : CA * X * divisorError r P m ≤ CA * (1 + B + B ^ 2 * a) * X * divisorError r P m := by
    have h0 : 0 ≤ X * divisorError r P m := mul_nonneg hX.le hD
    calc CA * X * divisorError r P m = CA * (X * divisorError r P m) := by ring
      _ ≤ CA * (1 + B + B ^ 2 * a) * (X * divisorError r P m) := mul_le_mul_of_nonneg_right hCk h0
      _ = CA * (1 + B + B ^ 2 * a) * X * divisorError r P m := by ring
  have hXc : CA * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M ≤
      CA * (1 + B + B ^ 2 * a) * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M := by
    have e1 : CA * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M =
        CA * (X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M) := by ring
    have e2 : CA * (1 + B + B ^ 2 * a) * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) /
        (r.totient : ℝ) ^ 2 * M =
        CA * (1 + B + B ^ 2 * a) * (X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M) := by
      ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hCk hchi
  calc _ ≤ _ := hA1
    _ ≤ _ := by
      have : CA * X * M * (1 - β) * e * Real.log P =
          CA * X * M * (1 - β) * Real.exp (-(c₆ / θ)) * Real.log P := by rw [he]
      linarith [hfin, hXD, hXc]

end LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit.bpLemma3Hyp_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit.w_terms_le
