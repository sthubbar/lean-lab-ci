import LeanLab.ExceptionalSet.SPLIT_leaf_absent_selected
import LeanLab.ExceptionalSet.Prep1121SingSeries

/-!
Burst S89 burst-20261122 feed1122, cited wall decision for `leaf_absent_even_index` of
`LeanLab.ExceptionalSet.SPLIT_leaf_absent_selected`.

The declaration is the even frequency half of case i of the proof of Lemma 7, P0082 page 362,
J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48 (1998)
353-378: when the exceptional character does not exist, Lemma 2 on page 358 gives
`R₁(m) = m 𝔖(m) + O(m φ(m)⁻¹ X exp(-c₁ log X / log P))`, and `𝔖(m) ≫ m / φ(m)` for even `m`,
so `R₁` at the even frequency, here `ν_n` itself, is `≫ X`.

Wiring audit. The parent statement `Decomp559b.leaf_absent_selected` is already proved in
`Prep1121SingSeries.leaf_absent_selected_of_lemma2_only` CONDITIONAL ON the single named
hypothesis `DQLeafAbsentSelected.Lemma2NoExcBP`, which is Lemma 2 of P0082, cited there by the
paper itself as "Combine (6.17) and (7.1) of Montgomery and Vaughan", P0015, Acta Arith. 27
(1975). The singular series bound of display 11 is PROVED outright in `Prep1121SingSeries`. So
the even half needs no new LEAF: `leaf_absent_even_index_of_lemma2` below has the exact statement of
the declaration with that one cited hypothesis added, and is proved by specialising the parent
to the conductor `r = 1` and the shift `j = 0`. The only gap left is the
Montgomery and Vaughan citation, a CITED-LEFT wall; nothing new is left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- `F(γ,N) ≥ 1` for every natural `N`, since `log N ≥ 0`. PROVED. -/
theorem feed1122_one_le_F_even (γ : ℝ) (N : ℕ) : (1 : ℝ) ≤ F γ N := by
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  exact Real.one_le_exp (Real.rpow_nonneg (Real.log_natCast_nonneg N) γ)

/-- P0082 page 362 Lemma 7 case i, even frequency half. Exactly the statement of
`SPLIT_leaf_absent_selected.leaf_absent_even_index` with the cited Lemma 2 of P0082 added as a hypothesis.
CONDITIONAL ON `DQLeafAbsentSelected.Lemma2NoExcBP`, Montgomery and Vaughan 1975. -/
theorem leaf_absent_even_index_of_lemma2 (hL : DQLeafAbsentSelected.Lemma2NoExcBP) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, Even (nu γ n) →
            ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              c * F γ N ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                  A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := Prep1121SingSeries.leaf_absent_selected_of_lemma2_only hL γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδp hδl => ?_⟩
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδp hδl
  refine ⟨κ₀, hκ₀, fun κ hκp hκl => ?_⟩
  obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκp hκl
  refine ⟨c, A, hc, hA, N₀, fun N hN0 hsel n hn hev hm => ?_⟩
  have h1P : (1 : ℝ) ≤ F γ N ^ (6 * δ) :=
    Real.one_le_rpow (feed1122_one_le_F_even γ N) (by positivity)
  have key := hN N hN0 1 le_rfl (by simpa using h1P) hsel 0 (Or.inl rfl) n hn (by simpa using hev)
    (by simpa using hm) rfl
  simpa using key

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
