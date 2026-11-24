import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_leaf_strip_extension131

/-!
Strength of the strip leaves of the split chain of `cor42_window_extension131`, burst-20261122,
CLOUD S101. No statement of any existing file is touched, and nothing below uses a `sorry` theorem.

`leaf_strip_extension131` of `SPLIT_cor42_window_extension131` and `leaf_strip_small_P131` of
`SPLIT_leaf_strip_extension131` quantify over EVERY finite set `E` and every `Cstar`, not only over
the generalised exceptional moduli of Lemma 4.1 of P0045, page 5, display 8, which Corollary 4.2
uses. Taking `E = evenJ131 X` and `Cstar = 1` makes every point of `J(X)` exceptional and every
point of the strip `X/2 ≤ n < 2X/3` nonexceptional, so the hypothesis on `J(X)` becomes vacuous.
The theorems below prove, for each `η`, that each of the two leaf statements is EQUIVALENT to the
exception free strip estimate: for all large `X`, every admissible `P` and every even `n` of the
strip, `|R_M(n) - n 𝔖(n)| ≤ η n 𝔖(n)`, with no exceptional moduli removed.

By Lemma 4.1 of P0045 page 5, a generalised exceptional zero `1 - δ + iγ` with `δ ≤ H / log X`
of a character modulo `r ≤ P` adds a secondary term of relative size about `n ^ (-δ)` to `R_M(n)`
for `n` with `r ∣ C(ε) n`; the exception free estimate for every `η > 0` thus asks for a zero free
region `δ ≥ H(η) / log X` with `H(η) → ∞`, which is beyond current knowledge and excludes Siegel
zeros. This is a QUESTION, not a FINDING: no counterexample is claimed.

`leaf_exceptional_absolute131_statement_iff` does the same for `leaf_exceptional_absolute131`:
with `Cstar = 0`, `E = {1}` and `c = 1 / (Lg X ^ 2 + 1)` every `n` is exceptional, so that leaf is
EQUIVALENT to the plain absolute bound `|R_M(n)| ≪ n 𝔖(n)` on the whole window for every `X` and
every admissible `P`, the last sentence of Corollary 4.2 extended to `[X/2, X]`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- The vacuity witness: with `E = evenJ131 X` and `Cstar = 1`, every point of `J(X)` is
exceptional and every point of the strip `X/2 ≤ n < 2X/3` of the window is nonexceptional. -/
theorem strip_vacuity_witness131 (X : ℕ) :
    (∀ n ∈ evenJ131 X, ¬ Nonexceptional131 1 (evenJ131 X) n) ∧
    (∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 1 (evenJ131 X) n) := by
  constructor
  · intro n hn h
    exact h n hn (by simp)
  · intro n hn hlt r hr hdvd
    have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hr2 : 2 * (X : ℝ) / 3 ≤ r := (mem_filter.mp hr).2.2
    have hle : r ≤ n := Nat.le_of_dvd (by omega) (by simpa using hdvd)
    have hle' : (r : ℝ) ≤ n := by exact_mod_cast hle
    linarith

/-- The statement of `leaf_strip_extension131` at a fixed `η` is equivalent to the exception free
strip estimate at the same `η`: the hypothesis on `J(X)` carries no information. -/
theorem leaf_strip_extension131_statement_iff (η : ℝ) :
    (∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (P : ℝ) (E : Finset ℕ) (Cstar : ℕ),
        AdmissibleP131 X P →
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
        ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ↔
    (∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n →
        |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) := by
  constructor
  · rintro ⟨X₀, h⟩
    refine ⟨X₀, fun X hX P hP n hn hlt => ?_⟩
    have hw := strip_vacuity_witness131 X
    exact h X hX P (evenJ131 X) 1 hP (fun m hm hm' => absurd hm' (hw.1 m hm)) n hn hlt
      (hw.2 n hn hlt)
  · rintro ⟨X₀, h⟩
    exact ⟨X₀, fun X hX P _ _ hP _ n hn hlt _ => h X hX P hP n hn hlt⟩

/-- The statement of `leaf_strip_small_P131` at a fixed `η` is equivalent to the exception free
strip estimate at the same `η`; the cut `P ≤ X ^ (9/20)` is automatic for `X ≥ 2`. -/
theorem leaf_strip_small_P131_statement_iff (η : ℝ) :
    (∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (P : ℝ) (E : Finset ℕ) (Cstar : ℕ),
        AdmissibleP131 X P → P ≤ (X : ℝ) ^ ((9 : ℝ) / 20) →
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
        ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ↔
    (∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n →
        |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) := by
  constructor
  · rintro ⟨X₀, h⟩
    refine ⟨max X₀ 2, fun X hX P hP n hn hlt => ?_⟩
    have hw := strip_vacuity_witness131 X
    have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
    exact h X (le_trans (le_max_left _ _) hX) P (evenJ131 X) 1 hP (admissibleP_le_cut131 hX2 hP)
      (fun m hm hm' => absurd hm' (hw.1 m hm)) n hn hlt (hw.2 n hn hlt)
  · rintro ⟨X₀, h⟩
    exact ⟨X₀, fun X hX P _ _ hP _ _ n hn hlt _ => h X hX P hP n hn hlt⟩

/-- `oddRad131 1 = 1`: the empty product. -/
theorem oddRad131_one : oddRad131 1 = 1 := by
  simp [oddRad131]

/-- The statement of `leaf_exceptional_absolute131` is equivalent to the absolute bound
`|R_M(n)| ≤ A n 𝔖(n)` on the whole window, for every `X` and every admissible `P`: with
`Cstar = 0` and `E = {1}` every `n` is exceptional, and `c = 1 / (Lg X ^ 2 + 1)` makes `{1}` an
admissible exceptional set. -/
theorem leaf_exceptional_absolute131_statement_iff :
    (∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E →
      ∀ n ∈ evenWindow131 X, ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n) ↔
    (∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (P : ℝ), AdmissibleP131 X P →
      ∀ n ∈ evenWindow131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A, hA, fun X P hP n hn => ?_⟩
    have hL : 0 ≤ Lg X ^ 2 := sq_nonneg _
    have hpos : 0 < Lg X ^ 2 + 1 := by linarith
    have hc : 0 < 1 / (Lg X ^ 2 + 1) := by positivity
    have hExc : ExceptionalModuli131 1 (1 / (Lg X ^ 2 + 1)) X {1} := by
      refine ⟨by simp, ?_⟩
      intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr
      rw [oddRad131_one, Nat.cast_one, div_mul_eq_mul_div, one_mul, div_le_one hpos]
      linarith
    exact h X 0 1 _ P {1} hc hP hExc n hn (fun hne => hne 1 (by simp) (by simp))
  · rintro ⟨A, hA, h⟩
    exact ⟨A, hA, fun X _ _ _ P _ _ hP _ n hn _ => h X P hP n hn⟩

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.strip_vacuity_witness131
#print axioms LeanLab.LPZ2007.leaf_strip_extension131_statement_iff
#print axioms LeanLab.LPZ2007.leaf_strip_small_P131_statement_iff
#print axioms LeanLab.LPZ2007.oddRad131_one
#print axioms LeanLab.LPZ2007.leaf_exceptional_absolute131_statement_iff
