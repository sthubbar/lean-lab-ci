import LeanLab.ExceptionalSet.DecompF1256
import LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_even_index

/-!
Burst S89 burst-20261122 feed1122, wiring of `leaf_prime_product_even_index_F1256` of `LeanLab.ExceptionalSet.DecompF1256`.

The declaration is the even frequency half of case ii b of the proof of Lemma 7, P0082 page 363,
J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48 (1998)
353-378: a conductor sharing a factor with the even frequency, and a prime `p > 3` dividing the
conductor but not the frequency, where display 21 bounds the exceptional term by a third of the
main term. Its statement is word for word the statement of `leaf_prime_product_even_index` of
`LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_selected`, a second copy made by a parallel
split of the same parent `Decomp559b.leaf_prime_product_selected`. That copy was already split
further in `LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_even_index`, whose theorem `leaf_prime_product_even_index_split` proves the shared
statement from smaller LEAF pieces of the same case.

So the duplicate needs no new LEAF: `leaf_prime_product_even_index_F1256_split` below has the exact statement of the
DecompF1256 declaration and is proved by that existing split. It is carried by the open leaves
of `SPLIT_leaf_prime_product_even_index` and by nothing else; nothing new is left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- P0082 page 363 case ii b, even frequency half. Exactly the statement of
`DecompF1256.leaf_prime_product_even_index_F1256`, proved from the existing split `leaf_prime_product_even_index_split`,
so CONDITIONAL ON the open LEAF pieces of `SPLIT_leaf_prime_product_even_index`. -/
theorem leaf_prime_product_even_index_F1256_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) :=
  leaf_prime_product_even_index_split γ h1 h2 a ha

/-- Twin check: the split theorem has exactly the type of the DecompF1256 declaration. -/
example : type_of% @leaf_prime_product_even_index_F1256 := @leaf_prime_product_even_index_F1256_split

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
