/-
Unit U-1344, PC run 20261021T0203Z-29730: merge of the duplicate corollaries of the
Main Theorem between `LeanLab.HelfgottOverview` and `LeanLab.SchnirelmannBounds`.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

Each HelfgottOverview corollary is shown to have literally the same statement as its
SchnirelmannBounds twin, by `rfl` on the Props, and is re-derived from the twin.
No file of another folder is edited; the canonical copies stay in SchnirelmannBounds.
-/
import LeanLab.HelfgottOverview.Statements
import LeanLab.SchnirelmannBounds.Statements

namespace LeanLab.HelfgottOverview.Merge
open LeanLab.SchnirelmannConstant
open LeanLab.SchnirelmannBounds (odd_atMost3_of_ternary even_atMost4_of_ternary
  atMost4_of_ternary kaniecki_of_ternary)

/-! ### The statements are equal Props -/

/-- Tao's Conjecture 1.2 is the conclusion of `odd_atMost3_of_ternary`. -/
theorem conj12_eq :
    LeanLab.Tao2012.Conjecture1_2 = ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 3 n := rfl

/-- The statement of `HelfgottOverview.odd_atMost3` equals that of
`SchnirelmannBounds.odd_atMost3_of_ternary`. -/
theorem odd_atMost3_stmt_eq :
    (TernaryGoldbach → LeanLab.Tao2012.Conjecture1_2) =
      (TernaryGoldbach → ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 3 n) := rfl

/-! ### Each overview corollary from its SchnirelmannBounds twin -/

theorem odd_atMost3' (hT : TernaryGoldbach) : LeanLab.Tao2012.Conjecture1_2 :=
  odd_atMost3_of_ternary hT

theorem even_atMost4' (hT : TernaryGoldbach) : ∀ n : ℕ, Even n → AtMostPrimes 4 n :=
  even_atMost4_of_ternary hT

theorem atMost4' (hT : TernaryGoldbach) : ∀ n : ℕ, 1 < n → AtMostPrimes 4 n :=
  atMost4_of_ternary hT

theorem atMostK' (hT : TernaryGoldbach) (K : ℕ) (hK : 4 ≤ K) :
    ∀ n : ℕ, 1 < n → AtMostPrimes K n := fun n hn => (atMost4_of_ternary hT n hn).mono hK

/-- `tao_of_ternary` is the first half of `kaniecki_of_ternary`. -/
theorem tao_of_ternary' (hT : TernaryGoldbach) :
    ∀ n : ℕ, Odd n → 1 < n → AtMostPrimes 5 n := (kaniecki_of_ternary hT).1

/-- `ramare_of_ternary` from the second half of `kaniecki_of_ternary`. -/
theorem ramare_of_ternary' (hT : TernaryGoldbach) :
    ∀ n : ℕ, Even n → 1 < n → AtMostPrimes 6 n :=
  fun n he _ => ((kaniecki_of_ternary hT).2 n he).mono (by norm_num)

/-- Both folders' proofs give the same conclusions; proof irrelevance makes them equal. -/
theorem same_proofs (hT : TernaryGoldbach) :
    odd_atMost3 hT = odd_atMost3' hT ∧ even_atMost4 hT = even_atMost4' hT ∧
      atMost4 hT = atMost4' hT := ⟨rfl, rfl, rfl⟩

/-- The overview's `corollaries` from the SchnirelmannBounds twins and the cited Main
Theorem. CONDITIONAL ON `Ternary.helfgott_analytic` and
`Verifications.helfgott_platt_ternary` through `Ternary.helfgott`. -/
theorem corollaries' : LeanLab.Tao2012.Conjecture1_2 ∧
    (∀ n : ℕ, Even n → AtMostPrimes 4 n) ∧ ∀ n : ℕ, 1 < n → AtMostPrimes 4 n :=
  ⟨odd_atMost3' LeanLab.Ternary.helfgott, even_atMost4' LeanLab.Ternary.helfgott,
    atMost4' LeanLab.Ternary.helfgott⟩

/-- Vacuity: a concrete instance of the shared conclusion, with no hypothesis. -/
example : AtMostPrimes 4 9 :=
  ((AtMostPrimes.prime Nat.prime_two).add
    (AtMostPrimes.prime (by norm_num : Nat.Prime 7))).mono (by norm_num)

end LeanLab.HelfgottOverview.Merge
