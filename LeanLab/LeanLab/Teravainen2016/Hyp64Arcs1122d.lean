/-
P0076 J. Teräväinen, arXiv 1611.08585: a split of the HARD LEAF `hyp64_exp_paper` of
Prop51Paper1122d.lean, Hypothesis 6.4 for `e(ξ m)` with `ξ = Q α` as in (7.3), page 30, proved in
Section 10. The split follows Section 10 exactly: the major arc case `q ∣ Q` and the minor arc
case `(log N)^A ≤ q / (q, Q²)` of Lemma 7.1, each for the semilinear sum `semDisc` and the
linear sum `linDisc` of Hypothesis 6.4. That gives four cited LEAFs, Subsections 10.2, 10.3,
10.4 and 10.5, each after the splitting of variables of Subsection 10.1. The case combination,
the choice of `η₁` and of `A`, and the unpacking of `Lemma71Adapted` are proved here.
The minor arc threshold in Lean is `(log N)^A`, which is at least the `(log x)^A` of page 39
since `x = N / (3 Q) ≤ N`, so the Lean minor arc hypothesis is the stronger one.
A further split of the minor arcs into the Type I and Type II sums of Lemmas 9.1 and 9.2 is not
statable with the existing definitions: those sums arise only after the variable splitting of
Subsection 10.1 and the factorisation of the sieve weights, for which no definitions exist.
burst-20261122 step hyp64_arcs1122d. AI wrote the Lean code. The binary Goldbach conjecture is
OPEN.
-/
import LeanLab.Teravainen2016.Prop51Paper1122d

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### The LEAFs -/

/-- LEAF: Subsection 10.2, page 39, major arcs for the semilinear sieve, after the splitting of
Subsection 10.1. For `ξ = Q α` with `α = W a / q + ε` as in (7.3) and `q ∣ Q`, partial summation
and the Bombieri Vinogradov theorem bound the semilinear sum of Hypothesis 6.4. The argument works
for every `A`, with `N₀` depending on `A`. Class MEDIUM. -/
theorem hyp64_major_sem : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ Cc A : ℕ,
    ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q →
    (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    ∀ (α : ℝ) (a : ℤ) (q : ℕ) (εk : ℝ), α = (WW J w : ℝ) * a / q + εk → IsCoprime a (q : ℤ) →
    1 ≤ q → (q : ℝ) ≤ N / Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) →
    |εk| ≤ Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) * WW J w / (q * N) → q ∣ Q →
    ∀ b : ℤ, Amenable (WW J w) b → ∀ c₀ ∈ QRes Q (WW J w) b,
    ∀ M : Finset ℕ, (∀ m ∈ M, (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    ‖semDisc (3 / 7 - 10 * η) (3 + η) ((N : ℝ) / (3 * Q)) ((Q : ℤ) * WW J w)
      (WW J w * c₀ + b) M (fun m => eC (-((Q : ℝ) * α) * m))‖ ≤
      ((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 199 := by sorry

/-- LEAF: Subsection 10.3, pages 39 to 41, major arcs for the linear sieve, after the splitting
of Subsection 10.1. For `ξ = Q α` as in (7.3) with `q ∣ Q`, partial summation and the
Bombieri Vinogradov type theorem for convolutions cited there bound the linear sum of
Hypothesis 6.4, uniformly over `g` of convolution type. The argument works for every `A`, with
`N₀` depending on `A`. Class MEDIUM. -/
theorem hyp64_major_lin : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ Cc A : ℕ,
    ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q →
    (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    ∀ (α : ℝ) (a : ℤ) (q : ℕ) (εk : ℝ), α = (WW J w : ℝ) * a / q + εk → IsCoprime a (q : ℤ) →
    1 ≤ q → (q : ℝ) ≤ N / Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) →
    |εk| ≤ Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) * WW J w / (q * N) → q ∣ Q →
    ∀ b : ℤ, Amenable (WW J w) b → ∀ c₀ ∈ QRes Q (WW J w) b,
    ∀ M : Finset ℕ, (∀ m ∈ M, (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    ∀ g, ConvType ((N : ℝ) / (3 * Q)) (3 + η) g →
    ‖linDisc (1 / 2 - 10 * η) ((N : ℝ) / (3 * Q)) ((Q : ℤ) * WW J w)
      (WW J w * c₀ + b) M (fun m => eC (-((Q : ℝ) * α) * m)) g‖ ≤
      ((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 199 := by sorry

/-- LEAF: Subsection 10.4, pages 41 to 43, minor arcs for the semilinear sieve, after the
splitting of Subsection 10.1. For `ξ = Q α` as in (7.3) with `(log N)^A ≤ q / (q, Q²)`, partial
summation, Lemma 8.1 for the Type I sums and Lemma 8.2 for the Type II sums, with the
factorisations of Lemma 9.2, bound the semilinear sum of Hypothesis 6.4 once `A` is large in
terms of `C`. Class HARD. -/
theorem hyp64_minor_sem : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ Cc : ℕ,
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A →
    ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q →
    (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    ∀ (α : ℝ) (a : ℤ) (q : ℕ) (εk : ℝ), α = (WW J w : ℝ) * a / q + εk → IsCoprime a (q : ℤ) →
    1 ≤ q → (q : ℝ) ≤ N / Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) →
    |εk| ≤ Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) * WW J w / (q * N) →
    Real.log N ^ A ≤ (q : ℝ) / (Nat.gcd q (Q ^ 2) : ℝ) →
    ∀ b : ℤ, Amenable (WW J w) b → ∀ c₀ ∈ QRes Q (WW J w) b,
    ∀ M : Finset ℕ, (∀ m ∈ M, (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    ‖semDisc (3 / 7 - 10 * η) (3 + η) ((N : ℝ) / (3 * Q)) ((Q : ℤ) * WW J w)
      (WW J w * c₀ + b) M (fun m => eC (-((Q : ℝ) * α) * m))‖ ≤
      ((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 199 := by sorry

/-- LEAF: Subsection 10.5, pages 43 to 44, minor arcs for the linear sieve, after the splitting
of Subsection 10.1. For `ξ = Q α` as in (7.3) with `(log N)^A ≤ q / (q, Q²)`, the estimates of
Cases 1 to 3 of Subsection 10.4 with Lemma 9.1 in place of Lemma 9.2 bound the linear sum of
Hypothesis 6.4 by `x (log x)^{-A/100}`, uniformly over `g` of convolution type, once `A` is
large. Class HARD. -/
theorem hyp64_minor_lin : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ Cc : ℕ,
    ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A →
    ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q →
    (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    ∀ (α : ℝ) (a : ℤ) (q : ℕ) (εk : ℝ), α = (WW J w : ℝ) * a / q + εk → IsCoprime a (q : ℤ) →
    1 ≤ q → (q : ℝ) ≤ N / Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) →
    |εk| ≤ Real.log N ^ (100 * (A * (3 * Cc) ^ Cc)) * WW J w / (q * N) →
    Real.log N ^ A ≤ (q : ℝ) / (Nat.gcd q (Q ^ 2) : ℝ) →
    ∀ b : ℤ, Amenable (WW J w) b → ∀ c₀ ∈ QRes Q (WW J w) b,
    ∀ M : Finset ℕ, (∀ m ∈ M, (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    ∀ g, ConvType ((N : ℝ) / (3 * Q)) (3 + η) g →
    ‖linDisc (1 / 2 - 10 * η) ((N : ℝ) / (3 * Q)) ((Q : ℤ) * WW J w)
      (WW J w * c₀ + b) M (fun m => eC (-((Q : ℝ) * α) * m)) g‖ ≤
      ((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 199 := by sorry

/-! ### The case combination, proved -/

/-- Hypothesis 6.4 for `e(ξ m)` in the paper order from the four LEAFs of Section 10: the
approximation of Lemma 7.1 is unpacked, the major and minor arc cases are split as at the end of
Subsection 10.1, `η₁` is the least of the four, and `A` is the larger of the two minor arc
thresholds. -/
theorem hyp64_exp_of_arcs
    (hMS : type_of% @hyp64_major_sem) (hML : type_of% @hyp64_major_lin)
    (hmS : type_of% @hyp64_minor_sem) (hmL : type_of% @hyp64_minor_lin) : Hyp64ExpP := by
  obtain ⟨e1, he1, H1⟩ := hMS
  obtain ⟨e2, he2, H2⟩ := hML
  obtain ⟨e3, he3, H3⟩ := hmS
  obtain ⟨e4, he4, H4⟩ := hmL
  refine ⟨min (min e1 e2) (min e3 e4), lt_min (lt_min he1 he2) (lt_min he3 he4), ?_⟩
  intro η hη hηle Cc
  have hη1 : η ≤ e1 := le_trans hηle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hη2 : η ≤ e2 := le_trans hηle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hη3 : η ≤ e3 := le_trans hηle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη4 : η ≤ e4 := le_trans hηle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨A3, HA3⟩ := H3 η hη hη3 Cc
  obtain ⟨A4, HA4⟩ := H4 η hη hη4 Cc
  refine ⟨max A3 A4, ?_⟩
  intro J w hJ hw
  obtain ⟨N1, K1⟩ := H1 η hη hη1 Cc (max A3 A4) J w hJ hw
  obtain ⟨N2, K2⟩ := H2 η hη hη2 Cc (max A3 A4) J w hJ hw
  obtain ⟨N3, K3⟩ := HA3 (max A3 A4) (le_max_left _ _) J w hJ hw
  obtain ⟨N4, K4⟩ := HA4 (max A3 A4) (le_max_right _ _) J w hJ hw
  refine ⟨max (max N1 N2) (max N3 N4), ?_⟩
  intro N hN Q hQ hQle α hA b hb c₀ hc₀ M hM hMc
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN4 : N4 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨a, q, εk, hα, hcop, hq1, hqN, hε, hcase⟩ := hA 0
  rcases hcase with hmaj | hmin
  · exact ⟨fun g hg => K2 N hN2 Q hQ hQle α a q εk hα hcop hq1 hqN hε hmaj b hb c₀ hc₀ M hM hMc
        g hg,
      K1 N hN1 Q hQ hQle α a q εk hα hcop hq1 hqN hε hmaj b hb c₀ hc₀ M hM hMc⟩
  · exact ⟨fun g hg => K4 N hN4 Q hQ hQle α a q εk hα hcop hq1 hqN hε hmin b hb c₀ hc₀ M hM hMc
        g hg,
      K3 N hN3 Q hQ hQle α a q εk hα hcop hq1 hqN hε hmin b hb c₀ hc₀ M hM hMc⟩

/-- `hyp64_exp_paper` from the four LEAFs of Section 10. -/
theorem hyp64_exp_paper_of_leaves : type_of% @LeanLab.Teravainen2016.hyp64_exp_paper :=
  hyp64_exp_of_arcs hyp64_major_sem hyp64_major_lin hyp64_minor_sem hyp64_minor_lin

end LeanLab.Teravainen2016

#print axioms LeanLab.Teravainen2016.hyp64_exp_of_arcs
#print axioms LeanLab.Teravainen2016.hyp64_exp_paper_of_leaves
