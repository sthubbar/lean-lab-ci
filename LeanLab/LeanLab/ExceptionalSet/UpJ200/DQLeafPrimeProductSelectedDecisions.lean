import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
CITED WALL decision for `Decomp559b.leaf_prime_product_selected`, burst 20261120.
Source: P0082, Bruedern and Perelli 1998, Ann. Inst. Fourier 48, https://doi.org/10.5802/aif.1621,
page 358 display 9, display 10 and Lemma 3, page 359 displays 12 to 15, page 363 display 20,
case ii b and display 21. The paper cites Montgomery and Vaughan 1975 formulas 6.17, 7.1, 8.5.

DECISION: NAMED HYPOTHESIS. The leaf is case ii b of the proof of Lemma 7, read pointwise with
the two error terms Gamma1 and Gamma2 of Lemma 3 kept as the explicit envelope `divisorError`
of displays 14 and 15 instead of being removed on average by Lemma 5. Its content is Lemma 3,
which the paper obtains by "a careful examination" of the Montgomery and Vaughan major arc
argument, plus the elementary lower bound for the main term from display 21. Lemma 3 is far
beyond a short split, so the case becomes the named Prop `PrimeProductSelectedP0082`, whose
body is word for word the leaf statement. The conditional theorem below has exactly the leaf's
type. CONDITIONAL, never PROVED.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)

/-- NAMED HYPOTHESIS, cited result. P0082 page 358 Lemma 3 with the error terms of page 359
displays 14 and 15 kept explicit, combined with page 363 display 20 and case ii b, display 21:
if the selected exceptional conductor `r` shares a factor with the even integer `m = ν_n + j`
and some prime `p > 3` divides `r` but not `m`, then `|𝔖~(m)| ≤ 𝔖(m) / 4`, `|I(m)| ≤ m`,
the exceptional middle term vanishes, and `R₁(m) ≫ X` up to `X (Γ₁(m) + Γ₂(m))`.
Here `X = F(N)` and `P = X^(6δ)` as on page 357. Word for word the body of
`Decomp559b.leaf_prime_product_selected`, quantified over `γ` and `a`. -/
def PrimeProductSelectedP0082 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ a : ℝ, 0 < a →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)

/-- P0082 page 363 case ii b. The leaf statement, with exactly the type of
`Decomp559b.leaf_prime_product_selected`, from the named hypothesis.
CONDITIONAL ON `PrimeProductSelectedP0082`. -/
theorem leaf_prime_product_selected_of_hyp (H : PrimeProductSelectedP0082)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
  H γ h1 h2 a ha

/-- Twin check: the hypothesis asks no more than the sealed leaf did.
CONDITIONAL ON `Decomp559b.leaf_prime_product_selected`, an open LEAF. -/
theorem hyp_of_leaf : PrimeProductSelectedP0082 :=
  fun γ h1 h2 a ha => LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected γ h1 h2 a ha

/-- The trivial selection `r = 1` of `SelectedRealZero` never reaches this case:
`gcd (m, 1) = 1`. So the hypothesis is used only when the exceptional character exists,
as in P0082 page 363 case ii. -/
theorem trivial_conductor_excluded (m : ℤ) : ¬ 1 < Int.gcd m 1 := by
  simp

/-- The prime witness hypothesis is satisfiable in the shape of the case:
`r = 30`, adjacent integer `6`, gcd `6`, prime `5`. Arithmetic only, no analytic claim. -/
theorem case_shape_instance :
    1 < Int.gcd 6 30 ∧ ∃ p : ℕ, p.Prime ∧ p ∣ 30 ∧ 3 < p ∧ ¬ (p : ℤ) ∣ 6 :=
  ⟨by decide, 5, Nat.prime_five, by norm_num, by norm_num, by decide⟩

/-- Vacuity instance for the range of `γ`: `γ = 5/4`, `a = 1`. -/
theorem gamma_instance : (1 : ℝ) < 5 / 4 ∧ (5 / 4 : ℝ) < 3 / 2 ∧ (0 : ℝ) < 1 := by norm_num

end LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected
