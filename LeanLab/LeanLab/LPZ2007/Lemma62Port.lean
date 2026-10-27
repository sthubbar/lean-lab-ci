/-
P0045 Lemma 6.2, a PORT of encoding B, LanguascoPintzZaccagnini2007/, into this folder's encoding A.

Unit U-6823, CLOUD 20261021T0217Z-cloud56. The two encodings declare the same names in namespace
`LeanLab.LPZ2007`, so no file can import both. This file copies B's Statements definitions, B's
Lemma61.lean, Lemma62Aux.lean and Lemma62.lean VERBATIM into the fresh namespace
`LeanLab.LPZ2007B`, dropping B's one cited sorry `lpz_lemma61_bound`, which Lemma 6.2 does not use,
and then proves the bridge `lemma62_A : LeanLab.LPZ2007.Lemma62`, the encoding A statement with real
`X`, from B's `lemma62_proved` at `⌈X⌉₊` with `ε/2`.
The copied proofs are B's: units U-5605 and U-5606, CLOUD 20261019T1416Z-cloud26.
AI-written Lean code, Claude. KNOWN mathematics, the paper's p.9 displays (27) to (30).
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Romanov.Lemma
import LeanLab.PNTSieve.MertensProduct
import LeanLab.LPZ2007.Statements

namespace LeanLab.LPZ2007B


/-! ## copied from LanguascoPintzZaccagnini2007/Statements.lean -/
/-
P0045 A. Languasco, J. Pintz, A. Zaccagnini, "On the sum of two primes and k powers of two",
last preprint of Bull. London Math. Soc. 39 (2007) 771-780, read 2026-10-18 from papers/P0045.pdf,
pages 1 to 10, the Theorem on page 2 checked on the rendered page image.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. The Theorem is an almost-all result for two primes and k powers of 2.

Readings. `X` is a natural number, `L = log_2 X` as in the paper, powers of two run over
`ν ∈ [1, ⌊L⌋]`. `R''_k(N)` is the Λ-weighted count of page 2. `(log X)^10` is the natural logarithm,
the base only changes the implied constant. `C(k, N)` is the series (23) of page 8; the paper's proof
makes it, and the implied constant, independent of η, so the Theorem is read with `∃ C K` before `∀ η`.
`ξ(d) = min {μ ≥ 1 : 2^μ ≡ 1 mod d}` for odd `d`, page 7 (μ ≥ 1 so that ξ(1) = 1).
-/

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `L = log_2 X`, page 1. -/
def Lg (X : ℕ) : ℝ := Real.logb 2 X

/-- The range `[1, L]` of the exponents, as natural numbers. -/
def Lp (X : ℕ) : ℕ := ⌊Lg X⌋₊

/-- `R''_k(N) = ∑ Λ(m₁) Λ(m₂)` over `m₁, m₂ ≤ X`, `ν ∈ [1, L]^k`, `m₁ + m₂ + 2^{ν₁} + … + 2^{ν_k} = N`,
page 2. -/
def Rpp (k X N : ℕ) : ℝ :=
  ∑ m₁ ∈ range (X + 1), ∑ m₂ ∈ range (X + 1),
    ∑ ν ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 (Lp X)),
      if m₁ + m₂ + ∑ i, 2 ^ ν i = N then Λ m₁ * Λ m₂ else 0

/-- The exceptional even `N ∈ [1, X]` for a main term `C N * N * L^k` and tolerance `η`. -/
def Exc (k X : ℕ) (C : ℕ → ℝ) (η : ℝ) : Finset ℕ :=
  (Icc 1 X).filter (fun N => Even N ∧ η * N * Lg X ^ k < |Rpp k X N - C N * N * Lg X ^ k|)

/-- The Theorem, page 2: `k ≥ 1`; there is `C(k, N) ∈ [1, 2]` and `K` such that for every `η > 0` and
`X ≥ X₀(k, η)` all even `N ∈ [1, X]` satisfy `|R''_k(N) - C(k, N) N L^k| ≤ η N L^k` apart from at most
`K X^{3/5} (log X)^10` exceptions. -/
def MainTheorem : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ → ℝ, (∀ N, Even N → 1 ≤ C N ∧ C N ≤ 2) ∧ ∃ K : ℝ, ∀ η : ℝ, 0 < η →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((Exc k X C η).card : ℝ) ≤ K * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10

/-- `ξ(d) = min {μ ≥ 1 : 2^μ ≡ 1 mod d}`, page 7. -/
def xi (d : ℕ) : ℕ := sInf {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]}

/-- `f(d) = ∏_{p | d, p > 2} (p - 2)^{-1}`, page 8. -/
def fd (d : ℕ) : ℝ := ∏ p ∈ d.primeFactors.filter (fun p => 2 < p), 1 / ((p : ℝ) - 2)

/-- Odd squarefree positive integers, the `Σ'` of the paper. -/
def OddSqf (d : ℕ) : Prop := 0 < d ∧ Odd d ∧ Squarefree d

/-- The series (26), page 9, as a function on odd squarefree `d`. -/
def seriesTerm (d : ℕ) : ℝ := if OddSqf d then fd d / xi d else 0

/-- Lemma 6.1, page 9, after Romanov: the series (26) converges. Cited. -/
def Lemma61 : Prop := Summable seriesTerm

/-- Page 9: the value of (26) is at most `1.9378`, Corollary 1 of Khalfallah and Pintz. Cited. -/
def Lemma61Bound : Prop := ∑' d, seriesTerm d ≤ 1.9378

/-- `𝔖(n) = ∏_{p ∤ n} (1 - 1/(p-1)²) ∏_{p | n} p/(p-1)`, page 2, as one product over all primes. -/
def Sing (n : ℕ) : ℝ :=
  ∏' p : {p : ℕ // p.Prime},
    if p.1 ∣ n then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

/-- `A(m, r) = ∑_{ν ∈ [1, L'], 2^ν < m, r | m - 2^ν} 𝔖(m - 2^ν)`, `L' = L - √L`, (13) page 7. -/
def Amr (X m r : ℕ) : ℝ :=
  ∑ ν ∈ (Icc 1 ⌊Lg X - Real.sqrt (Lg X)⌋₊).filter (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν),
    Sing (m - 2 ^ ν)

/-- Lemma 6.2, page 9, in the form its proof gives and Section 4 uses with `r ≫ L²`: for `ε > 0`
there are `r₀, X₀` with `A(m, r) ≤ ε L` for `X ≥ X₀`, `m ∈ [X/2, X]` and odd `r ≥ r₀`. As printed,
with no lower bound on `r`, it is false at `r = 1`: VERIFY U-0999, run 20261019T0202Z-9877,
since every term is at least `2c0`; `r₀` added then. Its proof on pages 9 to 10 is cited. -/
def Lemma62 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r₀ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ m r : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X →
    0 < r → Odd r → r₀ ≤ r → Amr X m r ≤ ε * Lg X

/- The Theorem of page 2 AS PRINTED is NOT cited any more: VERIFY U-0999, run 20261019T0202Z-9877,
found `MainTheorem` false twice, on all of `[1, X]` with `L = log_2 X`, QUESTION Q1 of the PC
LPZ2007 folder, and through F-0038, the true constant `2c0 C(k, N)` exceeds 2 on a positive share
of `N`. A `sorry` for it made the module inconsistent. The repaired, cited form is
`lpz_main_J_twoC0` in LeanLab/LPZ2007/Repaired.lean, PC folder.
Old line, kept as text: `theorem lpz_main : MainTheorem := by sorry`. -/

/- Lemma 6.1, Romanov. RETIRED 2026-10-19 by AUDIT U-1082, PC run 20261019T1603Z-20267: PROVED as
`lemma61_proved : Lemma61` in Lemma61.lean, no cited input, which imports this file, so the proof
cannot sit here. Nothing used the cited form. Old line, kept as text:
`theorem lpz_lemma61 : Lemma61 := by sorry` -/

-- B cited here Lemma 6.1 bound 1.9378 of Khalfallah and Pintz.
-- `lpz_lemma61_bound`, cited in encoding B, not copied.

/- Lemma 6.2 in the repaired form `Lemma62`. RETIRED 2026-10-19 by AUDIT U-1082, PC run
20261019T1603Z-20267: PROVED as `lemma62_proved : Lemma62` in Lemma62.lean, no cited input. Nothing
used the cited form. Old line, kept as text: `theorem lpz_lemma62 : Lemma62 := by sorry` -/

end




/-! ## copied from LanguascoPintzZaccagnini2007/Lemma61.lean -/

/-!
# P0045 Lemma 6.1, after Romanov: the series (26) converges

Lab proof, unit U-5605, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics:
Romanov 1934, in Erdős's 1950 form, the same dyadic argument as LeanLab/Romanov/Lemma.lean.
Binary Goldbach is OPEN; P0045 is an almost-all result for two primes and k powers of 2.

`seriesTerm d = f(d)/ξ(d)` on odd squarefree `d`, `f(d) = ∏_{p ∣ d, p > 2} 1/(p - 2)`,
`ξ(d)` the order of 2 mod `d`, as in Statements.lean. Group the `d` by `j = ⌊log₂ ξ(d)⌋`: every
`d` in group `j` divides `M_j = ∏_{e ≤ 2^(j+1)} (2^e - 1)`, which is odd with at most `4^(j+1)` prime
factors; a squarefree `d` is its set of prime factors, so the group's `Σ f(d)` is at most
`∏_{p ∣ M_j} (1 + 1/(p - 2)) ≤ e^27 · 2(j + 1) log 2`, and `ξ(d) ≥ 2^j`.

* `prodH_le`: `∏_{p ∣ n} (1 + 1/(p - 2)) ≤ e^27 log y` for odd `n` with `ω(n) ≤ y`, `y ≥ 4`.
* `partial_le`: every partial sum of `seriesTerm` is at most `8 log 2 · e^27`.
* `lemma61_proved : Lemma61`, the cited `lpz_lemma61` with no cited input, PROVED.
  The numerical bound `Lemma61Bound`, 1.9378, stays cited.
-/


open Finset Real

attribute [local instance] Classical.propDecidable

noncomputable section

lemma prodH_le (n y : ℕ) (hy : 4 ≤ y) (hodd : ∀ p ∈ n.primeFactors, 3 ≤ p)
    (hω : n.primeFactors.card ≤ y) :
    ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 2)) ≤ exp 27 * log y := by
  have hy4 : (4 : ℝ) ≤ y := by exact_mod_cast hy
  have hly : 0 < log (y : ℝ) := log_pos (by linarith)
  have hp3 : ∀ p ∈ n.primeFactors, (3 : ℝ) ≤ p := fun p hp => by exact_mod_cast hodd p hp
  have h1 : ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 2)) ≤
      exp (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2)) := by
    rw [exp_sum]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have := hp3 p hp
      have : 0 < (p : ℝ) - 2 := by linarith
      positivity
    · have := add_one_le_exp (1 / ((p : ℝ) - 2))
      linarith
  set A := n.primeFactors.filter (fun p => p ≤ y)
  set B := n.primeFactors.filter (fun p => ¬ p ≤ y)
  have hsplit := sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ y)
    (fun p => 1 / ((p : ℝ) - 2))
  -- `1/(p - 2) ≤ 1/p + 6/p²` for `p ≥ 3`
  have hpt : ∀ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) ≤ 1 / p + 6 * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    have h3 := hp3 p hp
    have h0 : 0 < (p : ℝ) - 2 := by linarith
    rw [div_le_iff₀ h0]
    have : (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2)) * ((p : ℝ) - 2) = 1 + 4 / p - 12 / p ^ 2 := by
      field_simp; ring
    rw [this]
    have : 12 / (p : ℝ) ^ 2 ≤ 4 / p := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hsubA : A ⊆ (Icc 1 y).filter Nat.Prime := by
    intro p hp
    simp only [A, mem_filter, Nat.mem_primeFactors] at hp
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨hp.1.1.one_lt.le, hp.2⟩, hp.1.1⟩
  have hA : ∑ p ∈ A, 1 / ((p : ℝ) - 2) ≤ log (log y) + 24 := by
    calc ∑ p ∈ A, 1 / ((p : ℝ) - 2) ≤ ∑ p ∈ A, (1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2)) :=
          sum_le_sum fun p hp => hpt p (mem_filter.1 hp).1
      _ = ∑ p ∈ A, 1 / (p : ℝ) + 6 * ∑ p ∈ A, 1 / (p : ℝ) ^ 2 := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ (log (log y) + 12) + 6 * 2 := by
          gcongr
          · refine le_trans (sum_le_sum_of_subset_of_nonneg hsubA fun _ _ _ => by positivity) ?_
            exact LeanLab.PNTSieve.Mertens.sum_inv_primes_le y (by omega)
          · refine le_trans ?_ (LeanLab.PNTSieve.Mertens.sum_inv_sq_le_two y)
            refine sum_le_sum_of_subset_of_nonneg (hsubA.trans (filter_subset _ _))
              fun _ _ _ => by positivity
      _ = log (log y) + 24 := by ring
  have hB : ∑ p ∈ B, 1 / ((p : ℝ) - 2) ≤ 3 := by
    calc ∑ p ∈ B, 1 / ((p : ℝ) - 2) ≤ ∑ _p ∈ B, 3 / (y : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          simp only [B, mem_filter, not_le] at hp
          have hyp : (y : ℝ) < p := by exact_mod_cast hp.2
          have h3 := hp3 p hp.1
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
      _ = 3 * (B.card / (y : ℝ)) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 3 * 1 := by
          gcongr
          rw [div_le_one (by linarith)]
          exact_mod_cast le_trans (card_filter_le _ _) hω
      _ = 3 := by ring
  have hsum : ∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2) ≤ log (log y) + 27 := by
    rw [← hsplit]; linarith
  calc ∏ p ∈ n.primeFactors, (1 + 1 / ((p : ℝ) - 2))
      ≤ exp (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 2)) := h1
    _ ≤ exp (log (log y) + 27) := exp_le_exp.2 hsum
    _ = exp 27 * log y := by rw [exp_add, exp_log hly]; ring

lemma not_two_dvd_M (j : ℕ) : ¬ 2 ∣ Romanov.M j := by
  unfold Romanov.M
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  rintro ⟨e, he, h2⟩
  simp only [mem_Icc] at he
  have : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he.1
  have hev : Even (2 ^ e) := (Nat.even_pow' (by omega)).2 even_two
  obtain ⟨m, hm⟩ := h2
  obtain ⟨r, hr⟩ := hev
  omega

lemma pf_M_ge_three (j : ℕ) : ∀ p ∈ (Romanov.M j).primeFactors, 3 ≤ p := by
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact not_two_dvd_M j (Nat.dvd_of_mem_primeFactors hp)
  have := hpr.two_le
  omega

theorem sumH_M_le (j : ℕ) :
    ∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2) ≤
      exp 27 * (2 * (j + 1) * log 2) := by
  rw [← prod_one_add]
  have hy : 4 ≤ 2 ^ (j + 1) * 2 ^ (j + 1) := by
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have h := prodH_le (Romanov.M j) _ hy (pf_M_ge_three j) (Romanov.card_pf_M_le j)
  have hlog : log ((2 ^ (j + 1) * 2 ^ (j + 1) : ℕ) : ℝ) = 2 * (j + 1) * log 2 := by
    push_cast
    rw [← pow_add, Real.log_pow]
    push_cast; ring
  rw [hlog] at h
  exact h

/-- The order facts for odd squarefree `d`. -/
lemma xi_spec_sqf {d : ℕ} (hd : OddSqf d) :
    1 ≤ xi d ∧ xi d ≤ d ∧ d ∣ 2 ^ xi d - 1 := by
  have hcop : Nat.Coprime 2 d := Nat.coprime_two_left.2 hd.2.1
  have hmem : d.totient ∈ {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]} :=
    ⟨Nat.totient_pos.2 hd.1, Nat.ModEq.pow_totient hcop⟩
  have hs := Nat.sInf_mem ⟨_, hmem⟩
  have hle := Nat.sInf_le hmem
  refine ⟨hs.1, le_trans hle (Nat.totient_le d), ?_⟩
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hs.2.symm

lemma fd_eq {d : ℕ} (hd : OddSqf d) : fd d = ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) := by
  unfold fd
  congr 1
  refine filter_true_of_mem fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hd.2.1) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  have := hpr.two_le
  omega

lemma fd_nonneg {d : ℕ} (hd : OddSqf d) : 0 ≤ fd d := by
  rw [fd_eq hd]
  refine prod_nonneg fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hd.2.1) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
  have : 3 ≤ p := by have := hpr.two_le; omega
  have : (3 : ℝ) ≤ p := by exact_mod_cast this
  have : 0 < (p : ℝ) - 2 := by linarith
  positivity

lemma seriesTerm_nonneg (d : ℕ) : 0 ≤ seriesTerm d := by
  unfold seriesTerm
  split_ifs with h
  · exact div_nonneg (fd_nonneg h) (Nat.cast_nonneg _)
  · exact le_rfl

/-- Every partial sum of the series (26) is at most `8 log 2 · e^27`. -/
theorem partial_le (D : ℕ) : ∑ d ∈ range D, seriesTerm d ≤ 8 * log 2 * exp 27 := by
  set F := (range D).filter OddSqf with hF
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have e1 : ∑ d ∈ range D, seriesTerm d = ∑ d ∈ F, fd d / xi d := by
    rw [← sum_subset (filter_subset OddSqf (range D))]
    · refine sum_congr rfl fun d hd => ?_
      unfold seriesTerm
      rw [if_pos (mem_filter.1 hd).2]
    · intro d _ hd
      unfold seriesTerm
      rw [if_neg]
      intro h
      exact hd (mem_filter.2 ⟨by assumption, h⟩)
  rw [e1]
  have hmaps : ∀ d ∈ F, Nat.log 2 (xi d) ∈ range (D + 1) := by
    intro d hd
    rw [mem_filter, mem_range] at hd
    have := (xi_spec_sqf hd.2).2.1
    have := Nat.log_le_self 2 (xi d)
    rw [mem_range]; omega
  rw [← sum_fiberwise_of_maps_to hmaps]
  have block : ∀ j ∈ range (D + 1), ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / xi d ≤
      (2 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by
    intro j _
    calc ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / xi d
        ≤ ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / 2 ^ j := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_filter, mem_filter] at hd
          have hs := xi_spec_sqf hd.1.2
          have hpow : 2 ^ j ≤ xi d := by rw [← hd.2]; exact Nat.pow_log_le_self 2 (by omega)
          have hpow' : (2 : ℝ) ^ j ≤ xi d := by exact_mod_cast hpow
          exact div_le_div_of_nonneg_left (fd_nonneg hd.1.2) (by positivity) hpow'
      _ = (∑ d ∈ F with Nat.log 2 (xi d) = j, fd d) / 2 ^ j := by rw [sum_div]
      _ ≤ (∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2)) / 2 ^ j := by
          gcongr
          calc ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d
              = ∑ d ∈ F with Nat.log 2 (xi d) = j,
                  ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) := by
                refine sum_congr rfl fun d hd => ?_
                rw [mem_filter, mem_filter] at hd
                exact fd_eq hd.1.2
            _ = ∑ s ∈ (F.filter (fun d => Nat.log 2 (xi d) = j)).image Nat.primeFactors,
                  ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
                rw [sum_image]
                intro a ha b hb hab
                have ha' : OddSqf a := (mem_filter.1 (mem_filter.1 (mem_coe.1 ha)).1).2
                have hb' : OddSqf b := (mem_filter.1 (mem_filter.1 (mem_coe.1 hb)).1).2
                rw [← Nat.prod_primeFactors_of_squarefree ha'.2.2,
                  ← Nat.prod_primeFactors_of_squarefree hb'.2.2, hab]
            _ ≤ ∑ s ∈ (Romanov.M j).primeFactors.powerset, ∏ p ∈ s, 1 / ((p : ℝ) - 2) := by
                refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
                · rw [mem_image] at hs
                  obtain ⟨d, hd, rfl⟩ := hs
                  rw [mem_filter, mem_filter] at hd
                  have hsp := xi_spec_sqf hd.1.2
                  have hlt : xi d < 2 ^ (j + 1) := by
                    rw [← hd.2]; exact Nat.lt_pow_succ_log_self (by norm_num) _
                  rw [mem_powerset]
                  exact Nat.primeFactors_mono (hsp.2.2.trans (Romanov.dvd_M hsp.1 hlt))
                    (Romanov.M_ne_zero j)
                · refine prod_nonneg fun p hp => ?_
                  have := pf_M_ge_three j p (mem_powerset.1 hs hp)
                  have : (3 : ℝ) ≤ p := by exact_mod_cast this
                  have : 0 < (p : ℝ) - 2 := by linarith
                  positivity
      _ ≤ (exp 27 * (2 * (j + 1) * log 2)) / 2 ^ j := by gcongr; exact sumH_M_le j
      _ = (2 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := by ring
  calc ∑ j ∈ range (D + 1), ∑ d ∈ F with Nat.log 2 (xi d) = j, fd d / xi d
      ≤ ∑ j ∈ range (D + 1), (2 * log 2 * exp 27) * (((j : ℝ) + 1) / 2 ^ j) := sum_le_sum block
    _ = (2 * log 2 * exp 27) * ∑ j ∈ range (D + 1), (((j : ℝ) + 1) / 2 ^ j) := by rw [mul_sum]
    _ ≤ (2 * log 2 * exp 27) * 4 :=
        mul_le_mul_of_nonneg_left (Romanov.sum_succ_div_pow_le _) (by positivity)
    _ = 8 * log 2 * exp 27 := by ring

/-- **P0045 Lemma 6.1**, after Romanov: the series (26) converges. No cited input. -/
theorem lemma61_proved : Lemma61 :=
  summable_of_sum_range_le seriesTerm_nonneg partial_le

end



/-! ## copied from LanguascoPintzZaccagnini2007/Lemma62Aux.lean -/

/-!
# P0045 Lemma 6.2, the arithmetic inputs

Lab proof, unit U-5606, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics.
Binary Goldbach is OPEN.

* `xi_odd`: for odd `d ≥ 1`, `1 ≤ ξ(d)` and `d ∣ 2^ξ(d) - 1`.
* `xi_dvd`: `d ∣ 2^μ - 1` forces `ξ(d) ∣ μ`.
* `xi_mono`: `d ∣ e`, `e` odd, gives `ξ(d) ≤ ξ(e)`.
* `log_lt_xi`: `log₂ r < ξ(r)`.
* `card_nu_le`: `#{ν ∈ [1, K] : 2^ν < m, e ∣ m - 2^ν} ≤ K/ξ(e) + 1` for odd `e`.
* `H n = ∏_{p ∣ n, p > 2} (1 + 1/(p - 2))` and `sing_le_two_H`: `𝔖(n) ≤ 2 H(n)` for `n ≥ 1`.
-/


open Finset Real Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

lemma xi_odd {d : ℕ} (hd : Odd d) (hd0 : 0 < d) : 1 ≤ xi d ∧ d ∣ 2 ^ xi d - 1 := by
  have hcop : Nat.Coprime 2 d := Nat.coprime_two_left.2 hd
  have hmem : d.totient ∈ {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]} :=
    ⟨Nat.totient_pos.2 hd0, Nat.ModEq.pow_totient hcop⟩
  have hs := Nat.sInf_mem ⟨_, hmem⟩
  exact ⟨hs.1, (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hs.2.symm⟩

lemma xi_le_of {d μ : ℕ} (hμ : 1 ≤ μ) (h : d ∣ 2 ^ μ - 1) : xi d ≤ μ := by
  refine Nat.sInf_le ⟨hμ, ?_⟩
  exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 h).symm

lemma xi_dvd {d μ : ℕ} (hd : Odd d) (hd0 : 0 < d) (h : d ∣ 2 ^ μ - 1) : xi d ∣ μ := by
  rcases Nat.eq_zero_or_pos μ with h0 | hμ
  · rw [h0]; exact dvd_zero _
  obtain ⟨h1, h2⟩ := xi_odd hd hd0
  have hg := Nat.dvd_gcd h2 h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  have hg0 : 0 < Nat.gcd (xi d) μ := Nat.gcd_pos_of_pos_left _ h1
  have hle : xi d ≤ Nat.gcd (xi d) μ := xi_le_of hg0 hg
  have hge : Nat.gcd (xi d) μ ≤ xi d := Nat.le_of_dvd h1 (Nat.gcd_dvd_left _ _)
  have : Nat.gcd (xi d) μ = xi d := le_antisymm hge hle
  rw [← this]; exact Nat.gcd_dvd_right _ _

lemma xi_mono {d e : ℕ} (he : Odd e) (he0 : 0 < e) (hde : d ∣ e) : xi d ≤ xi e := by
  obtain ⟨h1, h2⟩ := xi_odd he he0
  exact xi_le_of h1 (hde.trans h2)

lemma log_lt_xi {r : ℕ} (hr : Odd r) (hr0 : 0 < r) : Nat.log 2 r < xi r := by
  obtain ⟨h1, h2⟩ := xi_odd hr hr0
  have hpos : 0 < 2 ^ xi r - 1 := by
    have : 2 ≤ 2 ^ xi r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ xi r := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hle : r ≤ 2 ^ xi r - 1 := Nat.le_of_dvd hpos h2
  exact Nat.log_lt_of_lt_pow hr0.ne' (by omega)

/-- Two admissible `ν` differ by a multiple of `ξ(e)`. -/
lemma xi_dvd_sub {e m a b : ℕ} (he : Odd e) (he0 : 0 < e) (hab : a ≤ b) (hb : 2 ^ b < m)
    (ha' : e ∣ m - 2 ^ a) (hb' : e ∣ m - 2 ^ b) : xi e ∣ b - a := by
  apply xi_dvd he he0
  have hpa : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
  have hdiff : e ∣ 2 ^ b - 2 ^ a := by
    have := Nat.dvd_sub ha' hb'
    have e1 : m - 2 ^ a - (m - 2 ^ b) = 2 ^ b - 2 ^ a := by omega
    rwa [e1] at this
  have hsplit : 2 ^ b - 2 ^ a = 2 ^ a * (2 ^ (b - a) - 1) := by
    have : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [this, Nat.mul_sub_one]
  rw [hsplit] at hdiff
  have hcop : Nat.Coprime e (2 ^ a) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 he)
  exact hcop.dvd_of_dvd_mul_left hdiff

/-- At most `K/ξ(e) + 1` exponents `ν ∈ [1, K]` with `2^ν < m` and `e ∣ m - 2^ν`. -/
theorem card_nu_le {e : ℕ} (he : Odd e) (he0 : 0 < e) (K m : ℕ) :
    #{ν ∈ Icc 1 K | 2 ^ ν < m ∧ e ∣ m - 2 ^ ν} ≤ K / xi e + 1 := by
  set V := (Icc 1 K).filter (fun ν => 2 ^ ν < m ∧ e ∣ m - 2 ^ ν) with hV
  rcases V.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  set ν₀ := V.min' h
  have hν₀ : ν₀ ∈ V := V.min'_mem h
  have hξ := (xi_odd he he0).1
  refine le_trans (card_le_card_of_injOn (fun ν => (ν - ν₀) / xi e) (t := range (K / xi e + 1))
    (fun ν hν => ?_) (fun a ha b hb hab => ?_)) (by simp)
  · rw [mem_coe, mem_filter, mem_Icc] at hν
    rw [mem_coe, mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  · have ha0 : ν₀ ≤ a := V.min'_le a ha
    have hb0 : ν₀ ≤ b := V.min'_le b hb
    rw [mem_coe, mem_filter] at ha hb
    rw [mem_filter] at hν₀
    have hda := xi_dvd_sub he he0 ha0 ha.2.1 hν₀.2.2 ha.2.2
    have hdb := xi_dvd_sub he he0 hb0 hb.2.1 hν₀.2.2 hb.2.2
    simp only at hab
    have e1 := Nat.div_mul_cancel hda
    have e2 := Nat.div_mul_cancel hdb
    have : a - ν₀ = b - ν₀ := by rw [← e1, ← e2, hab]
    omega

/-- `H(n) = ∏_{p ∣ n, p > 2} (1 + 1/(p - 2))`. -/
def H (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

lemma one_le_H (n : ℕ) : 1 ≤ H n := by
  unfold H
  calc (1 : ℝ) = ∏ _p ∈ n.primeFactors.filter (fun p => 2 < p), (1 : ℝ) := by simp
    _ ≤ _ := by
      refine prod_le_prod₀ (fun _ _ => zero_le_one) fun p hp => ?_
      have : 2 < p := (mem_filter.1 hp).2
      have : (3 : ℝ) ≤ p := by exact_mod_cast this
      have : 0 < (p : ℝ) - 2 := by linarith
      have : 0 ≤ 1 / ((p : ℝ) - 2) := by positivity
      linarith

/-- The factor of `𝔖` at `p`. -/
def singF (n : ℕ) (p : {p : ℕ // p.Prime}) : ℝ :=
  if p.1 ∣ n then (p.1 : ℝ) / ((p.1 : ℝ) - 1) else 1 - 1 / ((p.1 : ℝ) - 1) ^ 2

/-- `G''(q) = 2` at `q = 2`, `1 + 1/(q - 2)` otherwise. -/
def G2 (q : ℕ) : ℝ := if q = 2 then 2 else 1 + 1 / ((q : ℝ) - 2)

lemma one_le_G2 {q : ℕ} (hq : 2 ≤ q) : 1 ≤ G2 q := by
  unfold G2
  split_ifs with h
  · norm_num
  · have : (3 : ℝ) ≤ q := by exact_mod_cast (by omega : 3 ≤ q)
    have : 0 < (q : ℝ) - 2 := by linarith
    have : 0 ≤ 1 / ((q : ℝ) - 2) := by positivity
    linarith

/-- Every finite partial product of `𝔖(n)` is at most `2 H(n)`, `n ≥ 1`. -/
lemma partial_le_two_H {n : ℕ} (hn : n ≠ 0) (S : Finset {p : ℕ // p.Prime}) :
    ∏ p ∈ S, singF n p ≤ 2 * H n := by
  set G' : ℕ → ℝ := fun q => if q ∣ n then G2 q else 1 with hG'
  have hG'1 : ∀ q, 2 ≤ q → 1 ≤ G' q := by
    intro q hq; simp only [hG']; split_ifs
    · exact one_le_G2 hq
    · exact le_rfl
  have hF0 : ∀ p : {p : ℕ // p.Prime}, 0 ≤ singF n p := by
    intro p
    have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
    unfold singF
    split_ifs
    · exact div_nonneg (by linarith) (by linarith)
    · have : 1 ≤ ((p.1 : ℝ) - 1) ^ 2 := by nlinarith
      have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
  have hFG : ∀ p : {p : ℕ // p.Prime}, singF n p ≤ G' p.1 := by
    intro p
    have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
    simp only [hG']
    unfold singF G2
    split_ifs with h1 h3
    · rw [h3]; norm_num
    · have h3' : (3 : ℝ) ≤ p.1 := by
        have := p.2.two_le
        exact_mod_cast (by omega : 3 ≤ p.1)
      rw [div_le_iff₀ (by linarith)]
      have h0 : 0 < (p.1 : ℝ) - 2 := by linarith
      have e : (1 + 1 / ((p.1 : ℝ) - 2)) * ((p.1 : ℝ) - 1) =
          (p.1 - 1) + (p.1 - 1) / (p.1 - 2) := by ring
      rw [e]
      have : 1 ≤ ((p.1 : ℝ) - 1) / ((p.1 : ℝ) - 2) := by rw [le_div_iff₀ h0]; linarith
      linarith
    · have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 2 := by positivity
      linarith
  set S' := S.map (Function.Embedding.subtype _) with hS'
  have hS'p : ∀ q ∈ S', q.Prime := by
    intro q hq
    rw [hS', Finset.mem_map] at hq
    obtain ⟨p, _, rfl⟩ := hq
    exact p.2
  have hpf2 : ∀ q ∈ n.primeFactors, 2 ≤ q := fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le
  calc ∏ p ∈ S, singF n p ≤ ∏ p ∈ S, G' p.1 := prod_le_prod₀ (fun p _ => hF0 p) fun p _ => hFG p
    _ = ∏ q ∈ S', G' q := by rw [hS', prod_map]; rfl
    _ ≤ ∏ q ∈ S' ∪ n.primeFactors, G' q := by
        refine prod_le_prod_of_subset_of_one_le₀ subset_union_left
          (fun q hq => le_trans zero_le_one (hG'1 q (hS'p q hq).two_le)) fun q hq _ => ?_
        rcases mem_union.1 hq with h | h
        · exact hG'1 q (hS'p q h).two_le
        · exact hG'1 q (hpf2 q h)
    _ = ∏ q ∈ n.primeFactors, G' q := by
        symm
        refine prod_subset subset_union_right fun q hq hnot => ?_
        simp only [hG']
        rw [if_neg]
        intro hd
        rcases mem_union.1 hq with h | h
        · exact hnot (Nat.mem_primeFactors.2 ⟨hS'p q h, hd, hn⟩)
        · exact hnot h
    _ = ∏ q ∈ n.primeFactors, G2 q := by
        refine prod_congr rfl fun q hq => ?_
        simp only [hG']
        rw [if_pos (Nat.dvd_of_mem_primeFactors hq)]
    _ = (∏ q ∈ n.primeFactors with 2 < q, G2 q) * ∏ q ∈ n.primeFactors with ¬ 2 < q, G2 q :=
        (prod_filter_mul_prod_filter_not _ _ _).symm
    _ ≤ H n * 2 := by
        have hH : ∏ q ∈ n.primeFactors with 2 < q, G2 q = H n := by
          unfold H
          refine prod_congr rfl fun q hq => ?_
          unfold G2
          rw [if_neg (by have := (mem_filter.1 hq).2; omega)]
        rw [hH]
        refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (one_le_H n))
        calc ∏ q ∈ n.primeFactors with ¬ 2 < q, G2 q ≤ ∏ q ∈ ({2} : Finset ℕ), G2 q := by
              refine prod_le_prod_of_subset_of_one_le₀ (fun q hq => ?_)
                (fun q hq => le_trans zero_le_one (one_le_G2 (hpf2 q (mem_filter.1 hq).1)))
                fun q hq _ => by rw [mem_singleton] at hq; rw [hq]; exact one_le_G2 le_rfl
              rw [mem_filter] at hq
              have := hpf2 q hq.1
              rw [mem_singleton]; omega
          _ = 2 := by simp [G2]
    _ = 2 * H n := by ring

/-- `𝔖(n) ≤ 2 H(n)` for `n ≥ 1`. -/
theorem sing_le_two_H {n : ℕ} (hn : n ≠ 0) : Sing n ≤ 2 * H n := by
  have hS : Sing n = ∏' p, singF n p := rfl
  rw [hS]
  by_cases hm : Multipliable (singF n)
  · exact le_of_tendsto hm.hasProd (Eventually.of_forall fun S => partial_le_two_H hn S)
  · rw [tprod_eq_one_of_not_multipliable hm]
    have := one_le_H n
    linarith

end



/-! ## copied from LanguascoPintzZaccagnini2007/Lemma62.lean -/

/-!
# P0045 Lemma 6.2, in the lab's repaired form with `r ≥ r₀`

Lab proof, unit U-5606, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Known mathematics;
the argument of the paper, page 9 displays (27) to (30). Binary Goldbach is OPEN.

For `ν` in the admissible set `V` write `n_ν = m - 2^ν`. With `𝔖(n) ≤ 2H(n)`,
`H(n) = Σ_{s ⊆ odd prime factors of n} W(s)`, `W(s) = ∏_{p ∈ s} 1/(p - 2)`; swapping the sums, the set
`s`, with `d = ∏ s`, is counted at most `L/ξ([d, r]) + 1` times. Then
* `d ≤ D`: `ξ([d, r]) ≥ ξ(r) > log₂ r`, and `Σ_{d ≤ D} W ≤ e^27 log D`;
* `d > D`: `ξ([d, r]) ≥ ξ(d)`, the tail of the series (26) of Lemma 6.1;
* the `+1` terms: at most `H` of `P = ∏ n_ν`, which has at most `L²` prime factors, so `≪ log L`.

* `sum_H_le`: the three-part bound.
* `lemma62_proved : Lemma62`, the cited `lpz_lemma62` with no cited input, PROVED.
-/


open Finset Real Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The odd prime factors. -/
def opf (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => 2 < p)

/-- `W(s) = ∏_{p ∈ s} 1/(p - 2)`. -/
def W (s : Finset ℕ) : ℝ := ∏ p ∈ s, 1 / ((p : ℝ) - 2)

lemma H_eq_sum (n : ℕ) : H n = ∑ s ∈ (opf n).powerset, W s := by
  unfold H W opf; exact prod_one_add _

lemma W_nonneg {s : Finset ℕ} (hs : ∀ p ∈ s, 2 < p) : 0 ≤ W s := by
  unfold W
  refine prod_nonneg fun p hp => ?_
  have : (3 : ℝ) ≤ p := by exact_mod_cast (hs p hp)
  have : 0 < (p : ℝ) - 2 := by linarith
  positivity

lemma opf_spec {n p : ℕ} (h : p ∈ opf n) : p.Prime ∧ 2 < p ∧ p ∣ n := by
  unfold opf at h
  rw [mem_filter, Nat.mem_primeFactors] at h
  exact ⟨h.1.1, h.2, h.1.2.1⟩

/-- The facts about `d = ∏ s` for a set `s` of odd primes. -/
lemma set_facts {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) :
    OddSqf (∏ p ∈ s, p) ∧ (∏ p ∈ s, p).primeFactors = s ∧ fd (∏ p ∈ s, p) = W s := by
  have hpr : ∀ p ∈ s, p.Prime := fun p hp => (hs p hp).1
  have hpos : 0 < ∏ p ∈ s, p := prod_pos fun p hp => (hpr p hp).pos
  have hodd : Odd (∏ p ∈ s, p) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨p, hp, hdvd⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hpr p hp)).1 hdvd
    have := (hs p hp).2
    omega
  have hsq : Squarefree (∏ p ∈ s, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hne => ?_)
      fun p hp => (hpr p hp).prime.irreducible.squarefree
    exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hpr p hp) (hpr q hq)).2 hne)
  have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hpr
  have hos : OddSqf (∏ p ∈ s, p) := ⟨hpos, hodd, hsq⟩
  refine ⟨hos, hpf, ?_⟩
  rw [fd_eq hos, hpf]; rfl

lemma prod_dvd_of_subset {s : Finset ℕ} {n : ℕ} (hn : n ≠ 0) (h : s ⊆ opf n) :
    ∏ p ∈ s, p ∣ n :=
  prod_primes_dvd n (fun p hp => (opf_spec (h hp)).1.prime) fun p hp => (opf_spec (h hp)).2.2

lemma opf_mono {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) : opf a ⊆ opf b := by
  unfold opf
  exact filter_subset_filter _ (Nat.primeFactors_mono hab hb)

/-- The odd primes up to `D` carry `Σ W ≤ e^27 log D`. -/
lemma sum_W_small (D : ℕ) (hD : 4 ≤ D) :
    ∑ s ∈ ((Icc 3 D).filter Nat.Prime).powerset, W s ≤ exp 27 * log D := by
  set Q := (Icc 3 D).filter Nat.Prime with hQ
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (mem_filter.1 hp).2
  have hpf : (∏ p ∈ Q, p).primeFactors = Q := Nat.primeFactors_prod hQp
  have h := prodH_le (∏ p ∈ Q, p) D hD (fun p hp => by
      rw [hpf] at hp; exact (mem_Icc.1 (mem_filter.1 hp).1).1)
    (by rw [hpf]; refine le_trans (card_filter_le _ _) ?_; simp)
  rw [hpf] at h
  unfold W
  rw [← prod_one_add]
  exact h

/-- A finite set of `d > D` carries at most the tail of (26). -/
lemma tail_le (D : ℕ) (T : Finset ℕ) (hT : ∀ d ∈ T, D < d) :
    ∑ d ∈ T, seriesTerm d ≤ ∑' k, seriesTerm (k + (D + 1)) := by
  have hsum : Summable (fun k => seriesTerm (k + (D + 1))) :=
    (summable_nat_add_iff (D + 1)).2 lemma61_proved
  have e : ∑ d ∈ T, seriesTerm d = ∑ k ∈ T.image (fun d => d - (D + 1)), seriesTerm (k + (D + 1)) := by
    rw [sum_image]
    · refine sum_congr rfl fun d hd => ?_
      have := hT d hd
      congr 1; omega
    · intro a ha b hb hab
      have := hT a ha; have := hT b hb
      simp only at hab; omega
  rw [e]
  exact hsum.sum_le_tsum _ fun k _ => seriesTerm_nonneg _

/-- **The three-part bound** for `Σ_{ν ∈ V} H(m - 2^ν)`. -/
theorem sum_H_le (V : Finset ℕ) (K' m r D : ℕ) (L : ℝ)
    (hV : ∀ ν ∈ V, ν ∈ Icc 1 K' ∧ 2 ^ ν < m ∧ r ∣ m - 2 ^ ν) (hr : Odd r) (hr0 : 0 < r)
    (hK : (K' : ℝ) ≤ L) (hD : 4 ≤ D) :
    ∑ ν ∈ V, H (m - 2 ^ ν) ≤ L * (exp 27 * log D) / xi r +
      L * ∑' k, seriesTerm (k + (D + 1)) +
      ∑ s ∈ (opf (∏ ν ∈ V, (m - 2 ^ ν))).powerset, W s := by
  have hn0 : ∀ ν ∈ V, m - 2 ^ ν ≠ 0 := fun ν hν => by have := (hV ν hν).2.1; omega
  set P := ∏ ν ∈ V, (m - 2 ^ ν) with hP
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn0
  set Pν : ℕ → Finset (Finset ℕ) := fun ν => (opf (m - 2 ^ ν)).powerset with hPν
  set U := V.biUnion Pν with hU
  have hPU : ∀ ν ∈ V, Pν ν ⊆ U := fun ν hν => subset_biUnion_of_mem Pν hν
  have hUs : ∀ s ∈ U, ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro s hs p hp
    rw [hU, mem_biUnion] at hs
    obtain ⟨ν, _, hsν⟩ := hs
    have := opf_spec (mem_powerset.1 hsν hp)
    exact ⟨this.1, this.2.1⟩
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg _) hK
  -- step 1: expand and swap
  have step1 : ∑ ν ∈ V, H (m - 2 ^ ν) = ∑ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) * W s := by
    calc ∑ ν ∈ V, H (m - 2 ^ ν) = ∑ ν ∈ V, ∑ s ∈ U, if s ∈ Pν ν then W s else 0 := by
          refine sum_congr rfl fun ν hν => ?_
          rw [H_eq_sum, sum_ite_mem, inter_eq_right.2 (hPU ν hν)]
      _ = ∑ s ∈ U, ∑ ν ∈ V, if s ∈ Pν ν then W s else 0 := sum_comm
      _ = _ := by
          refine sum_congr rfl fun s _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
  -- step 2: the count
  have hcount : ∀ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) ≤
      L / xi (Nat.lcm (∏ p ∈ s, p) r) + 1 := by
    intro s hs
    obtain ⟨hos, -, -⟩ := set_facts (hUs s hs)
    set d := ∏ p ∈ s, p
    have hlodd : Odd (Nat.lcm d r) := (hos.2.1.mul hr).of_dvd_nat (Nat.lcm_dvd_mul d r)
    have hlpos : 0 < Nat.lcm d r := Nat.lcm_pos hos.1 hr0
    have hsub : V.filter (fun ν => s ∈ Pν ν) ⊆
        (Icc 1 K').filter (fun ν => 2 ^ ν < m ∧ Nat.lcm d r ∣ m - 2 ^ ν) := by
      intro ν hν
      rw [mem_filter] at hν
      obtain ⟨h1, h2, h3⟩ := hV ν hν.1
      rw [mem_filter]
      refine ⟨h1, h2, Nat.lcm_dvd ?_ h3⟩
      exact prod_dvd_of_subset (hn0 ν hν.1) (mem_powerset.1 hν.2)
    have h1 := le_trans (card_le_card hsub) (card_nu_le hlodd hlpos K' m)
    have hxi : (0 : ℝ) < xi (Nat.lcm d r) := by exact_mod_cast (xi_odd hlodd hlpos).1
    calc (#{ν ∈ V | s ∈ Pν ν} : ℝ) ≤ ((K' / xi (Nat.lcm d r) + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ (K' : ℝ) / xi (Nat.lcm d r) + 1 := by push_cast; linarith [Nat.cast_div_le (m := K') (n := xi (Nat.lcm d r)) (α := ℝ)]
      _ ≤ L / xi (Nat.lcm d r) + 1 := by gcongr
  have hW0 : ∀ s ∈ U, 0 ≤ W s := fun s hs => W_nonneg fun p hp => (hUs s hs p hp).2
  have step2 : ∑ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) * W s ≤
      ∑ s ∈ U, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s + ∑ s ∈ U, W s := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun s hs => ?_
    have := mul_le_mul_of_nonneg_right (hcount s hs) (hW0 s hs)
    linarith
  -- the `+1` part
  have part3 : ∑ s ∈ U, W s ≤ ∑ s ∈ (opf P).powerset, W s := by
    refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
    · rw [hU, mem_biUnion] at hs
      obtain ⟨ν, hν, hsν⟩ := hs
      rw [mem_powerset]
      exact (mem_powerset.1 hsν).trans (opf_mono (dvd_prod_of_mem _ hν) hP0)
    · exact W_nonneg fun p hp => (opf_spec (mem_powerset.1 hs hp)).2.1
  -- the main part, split at `D`
  have hsplit := sum_filter_add_sum_filter_not U (fun s => ∏ p ∈ s, p ≤ D)
    (fun s => L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s)
  have hxr : (0 : ℝ) < xi r := by exact_mod_cast (xi_odd hr hr0).1
  have part1 : ∑ s ∈ U with ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s ≤
      L * (exp 27 * log D) / xi r := by
    calc ∑ s ∈ U with ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s
        ≤ ∑ s ∈ U with ∏ p ∈ s, p ≤ D, L / xi r * W s := by
          refine sum_le_sum fun s hs => ?_
          rw [mem_filter] at hs
          refine mul_le_mul_of_nonneg_right ?_ (hW0 s hs.1)
          obtain ⟨hos, -, -⟩ := set_facts (hUs s hs.1)
          have hlodd : Odd (Nat.lcm (∏ p ∈ s, p) r) :=
            (hos.2.1.mul hr).of_dvd_nat (Nat.lcm_dvd_mul _ r)
          have hlpos : 0 < Nat.lcm (∏ p ∈ s, p) r := Nat.lcm_pos hos.1 hr0
          have hm : xi r ≤ xi (Nat.lcm (∏ p ∈ s, p) r) :=
            xi_mono hlodd hlpos (Nat.dvd_lcm_right _ r)
          have hm' : (xi r : ℝ) ≤ xi (Nat.lcm (∏ p ∈ s, p) r) := by exact_mod_cast hm
          exact div_le_div_of_nonneg_left hL0 hxr hm'
      _ = L / xi r * ∑ s ∈ U with ∏ p ∈ s, p ≤ D, W s := by rw [mul_sum]
      _ ≤ L / xi r * ∑ s ∈ ((Icc 3 D).filter Nat.Prime).powerset, W s := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hL0 hxr.le)
          refine sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) fun s hs _ => ?_
          · rw [mem_filter] at hs
            rw [mem_powerset]
            intro p hp
            have hps := hUs s hs.1 p hp
            have hle : p ≤ ∏ q ∈ s, q :=
              Nat.le_of_dvd (prod_pos fun q hq => (hUs s hs.1 q hq).1.pos) (dvd_prod_of_mem _ hp)
            rw [mem_filter, mem_Icc]
            exact ⟨⟨by omega, le_trans hle hs.2⟩, hps.1⟩
          · exact W_nonneg fun p hp => by
              have := (mem_Icc.1 (mem_filter.1 (mem_powerset.1 hs hp)).1).1; omega
      _ ≤ L / xi r * (exp 27 * log D) :=
          mul_le_mul_of_nonneg_left (sum_W_small D hD) (div_nonneg hL0 hxr.le)
      _ = L * (exp 27 * log D) / xi r := by ring
  have part2 : ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s ≤
      L * ∑' k, seriesTerm (k + (D + 1)) := by
    calc ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s
        ≤ ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, L * seriesTerm (∏ p ∈ s, p) := by
          refine sum_le_sum fun s hs => ?_
          rw [mem_filter] at hs
          obtain ⟨hos, -, hfd⟩ := set_facts (hUs s hs.1)
          have hlodd : Odd (Nat.lcm (∏ p ∈ s, p) r) :=
            (hos.2.1.mul hr).of_dvd_nat (Nat.lcm_dvd_mul _ r)
          have hlpos : 0 < Nat.lcm (∏ p ∈ s, p) r := Nat.lcm_pos hos.1 hr0
          have hm : xi (∏ p ∈ s, p) ≤ xi (Nat.lcm (∏ p ∈ s, p) r) :=
            xi_mono hlodd hlpos (Nat.dvd_lcm_left _ r)
          have hxd : (0 : ℝ) < xi (∏ p ∈ s, p) := by
            exact_mod_cast (xi_odd hos.2.1 hos.1).1
          have hm' : (xi (∏ p ∈ s, p) : ℝ) ≤ xi (Nat.lcm (∏ p ∈ s, p) r) := by exact_mod_cast hm
          have hst : seriesTerm (∏ p ∈ s, p) = W s / xi (∏ p ∈ s, p) := by
            unfold seriesTerm; rw [if_pos hos, hfd]
          rw [hst]
          calc L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s ≤ L / xi (∏ p ∈ s, p) * W s :=
                mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hL0 hxd hm') (hW0 s hs.1)
            _ = L * (W s / xi (∏ p ∈ s, p)) := by ring
      _ = L * ∑ s ∈ U with ¬ ∏ p ∈ s, p ≤ D, seriesTerm (∏ p ∈ s, p) := by rw [mul_sum]
      _ = L * ∑ d ∈ (U.filter (fun s => ¬ ∏ p ∈ s, p ≤ D)).image (fun s => ∏ p ∈ s, p),
            seriesTerm d := by
          rw [sum_image]
          intro a ha b hb hab
          have ha' := (set_facts (hUs a (mem_filter.1 (mem_coe.1 ha)).1)).2.1
          have hb' := (set_facts (hUs b (mem_filter.1 (mem_coe.1 hb)).1)).2.1
          simp only at hab
          rw [← ha', ← hb', hab]
      _ ≤ L * ∑' k, seriesTerm (k + (D + 1)) := by
          refine mul_le_mul_of_nonneg_left (tail_le D _ fun d hd => ?_) hL0
          rw [mem_image] at hd
          obtain ⟨s, hs, rfl⟩ := hd
          rw [mem_filter] at hs
          omega
  calc ∑ ν ∈ V, H (m - 2 ^ ν) = ∑ s ∈ U, (#{ν ∈ V | s ∈ Pν ν} : ℝ) * W s := step1
    _ ≤ ∑ s ∈ U, L / xi (Nat.lcm (∏ p ∈ s, p) r) * W s + ∑ s ∈ U, W s := step2
    _ ≤ _ := by rw [← hsplit]; linarith

/-- The `+1` part: `Σ_{s ⊆ opf P} W(s) ≤ e^27 log y` once `ω(P) ≤ y`, `y ≥ 4`. -/
lemma sum_W_opf_le (P y : ℕ) (hy : 4 ≤ y) (hω : P.primeFactors.card ≤ y) :
    ∑ s ∈ (opf P).powerset, W s ≤ exp 27 * log y := by
  have hQp : ∀ p ∈ opf P, p.Prime := fun p hp => (opf_spec hp).1
  have hpf : (∏ p ∈ opf P, p).primeFactors = opf P := Nat.primeFactors_prod hQp
  have h := prodH_le (∏ p ∈ opf P, p) y hy (fun p hp => by
      rw [hpf] at hp; have := (opf_spec hp).2.1; omega)
    (by rw [hpf]; exact le_trans (card_filter_le _ _) hω)
  rw [hpf] at h
  unfold W
  rw [← prod_one_add]
  exact h

/-- `log(L² + 5) ≤ 2 + 4√L` for `L ≥ 1`. -/
lemma log_sq_add_le (L : ℝ) (hL : 1 ≤ L) : log (L ^ 2 + 5) ≤ 2 + 4 * Real.sqrt L := by
  have h1 : log (L ^ 2 + 5) ≤ log (6 * L ^ 2) := log_le_log (by positivity) (by nlinarith)
  rw [log_mul (by norm_num) (by positivity), log_pow] at h1
  have h6 : log 6 ≤ 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    have h7 : (6 : ℝ) ≤ exp 2 := by
      have := Real.exp_one_gt_d9
      have : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    calc log 6 ≤ log (exp 2) := log_le_log (by norm_num) h7
      _ = 2 := log_exp 2
  have hl := Real.log_le_rpow_div (x := L) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hl
  push_cast at h1
  linarith

lemma aux_third (C δ L ly : ℝ) (hC0 : 0 < C) (hδ0 : 0 < δ) (hL0 : (6 * C / δ) ^ 2 + 1 ≤ L)
    (hly : ly ≤ 2 + 4 * Real.sqrt L) : C * ly ≤ δ * L := by
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * C / δ)]
  have hsqrt : 6 * C / δ ≤ Real.sqrt L := by
    rw [show 6 * C / δ = Real.sqrt ((6 * C / δ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hL1
  have h1 : C * ly ≤ C * (2 + 4 * Real.sqrt L) := mul_le_mul_of_nonneg_left hly hC0.le
  have h2 : C * (2 + 4 * Real.sqrt L) ≤ 6 * C * Real.sqrt L := by
    have := mul_nonneg hC0.le (sub_nonneg.2 hs1)
    linarith
  have h3 : 6 * C ≤ Real.sqrt L * δ := (div_le_iff₀ hδ0).1 hsqrt
  have h4 : 6 * C * Real.sqrt L ≤ δ * L := by
    have := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg L)
    calc 6 * C * Real.sqrt L ≤ Real.sqrt L * δ * Real.sqrt L := this
      _ = δ * (Real.sqrt L * Real.sqrt L) := by ring
      _ = δ * L := by rw [hsL]
  linarith

lemma aux_first (L a δ ξ : ℝ) (hL : 0 ≤ L) (hξ : 0 < ξ) (hδ : 0 < δ) (h : a / δ ≤ ξ) :
    L * a / ξ ≤ δ * L := by
  rw [div_le_iff₀ hξ]
  have h1 : a ≤ ξ * δ := (div_le_iff₀ hδ).1 h
  have := mul_le_mul_of_nonneg_left h1 hL
  linarith

lemma aux_final (S Hs A B T ε L : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) (h1 : S ≤ 2 * Hs)
    (h2 : Hs ≤ A + B + T) (hA : A ≤ ε / 16 * L) (hB : B ≤ ε / 16 * L) (hT : T ≤ ε / 16 * L) :
    S ≤ ε * L := by
  have : 0 ≤ ε * L := mul_nonneg hε.le hL
  linarith

/-- **P0045 Lemma 6.2** in the lab's repaired form: for `ε > 0` there are `r₀, X₀` with
`A(m, r) ≤ ε L` for `X ≥ X₀`, `m ∈ [X/2, X]` and odd `r ≥ r₀`. No cited input. -/
theorem lemma62_proved : Lemma62 := by
  intro ε hε
  set C := exp 27 with hC
  have hC0 : 0 < C := exp_pos 27
  set δ := ε / 16 with hδ
  have hδ0 : 0 < δ := by positivity
  -- the tail
  obtain ⟨D₁, hD₁⟩ := (tendsto_order.1 (tendsto_sum_nat_add seriesTerm)).2 δ hδ0 |>.exists_forall_of_atTop
  set D := max D₁ 4 with hDdef
  have hD4 : 4 ≤ D := le_max_right _ _
  have htail : ∑' k, seriesTerm (k + (D + 1)) < δ := hD₁ (D + 1) (by omega)
  have hlogD : 0 < log (D : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < D))
  -- `r₀`
  set N₁ := ⌈C * log D / δ⌉₊ with hN₁
  refine ⟨2 ^ N₁, 2 ^ ⌈(6 * C / δ) ^ 2 + 1⌉₊, fun X hX m r hm1 hm2 hr0 hr hrr => ?_⟩
  set L := Lg X with hLdef
  have hX1 : 1 ≤ X := le_trans Nat.one_le_two_pow hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hLge : ((⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤ L := by
    rw [hLdef, Lg]
    have : ((2 ^ ⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
    calc ((⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) = Real.logb 2 ((2 ^ ⌈(6 * C / δ) ^ 2 + 1⌉₊ : ℕ) : ℝ) := by
          push_cast; rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
      _ ≤ Real.logb 2 X := Real.logb_le_logb_of_le (by norm_num) (by positivity) this
  have hL0 : (6 * C / δ) ^ 2 + 1 ≤ L := le_trans (Nat.le_ceil _) hLge
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * C / δ)]
  -- the admissible set
  set K' := ⌊L - Real.sqrt L⌋₊ with hK'
  have hK'L : (K' : ℝ) ≤ L := by
    rcases le_or_gt 0 (L - Real.sqrt L) with h | h
    · exact le_trans (Nat.floor_le h) (by linarith [Real.sqrt_nonneg L])
    · rw [hK', Nat.floor_eq_zero.2 (by linarith)]; push_cast; linarith
  unfold Amr
  rw [← hLdef]
  set V := (Icc 1 K').filter (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν) with hV
  have hVp : ∀ ν ∈ V, ν ∈ Icc 1 K' ∧ 2 ^ ν < m ∧ r ∣ m - 2 ^ ν := fun ν hν => by
    rw [hV, mem_filter] at hν; exact ⟨hν.1, hν.2.1, hν.2.2⟩
  have hmain := sum_H_le V K' m r D L hVp hr hr0 hK'L hD4
  -- the `+1` part: `ω(P) ≤ L²`
  set P := ∏ ν ∈ V, (m - 2 ^ ν) with hP
  have hn0 : ∀ ν ∈ V, m - 2 ^ ν ≠ 0 := fun ν hν => by have := (hVp ν hν).2.1; omega
  have hP0 : P ≠ 0 := prod_ne_zero_iff.2 hn0
  have hcardV : (V.card : ℝ) ≤ L := by
    have : V.card ≤ K' := by
      calc V.card ≤ (Icc 1 K').card := card_le_card (filter_subset _ _)
        _ = K' := by simp
    exact le_trans (by exact_mod_cast this) hK'L
  have hω : (P.primeFactors.card : ℝ) ≤ L ^ 2 := by
    have h1 : 2 ^ P.primeFactors.card ≤ P := Romanov.two_pow_card_le P hP0
    have h2 : P ≤ X ^ V.card := by
      have hmX : m ≤ X := by exact_mod_cast hm2
      calc P ≤ ∏ _ν ∈ V, X := prod_le_prod' fun ν _ => le_trans (Nat.sub_le m _) hmX
        _ = X ^ V.card := by rw [prod_const]
    have h3 : ((2 : ℝ) ^ P.primeFactors.card) ≤ (X : ℝ) ^ V.card := by
      exact_mod_cast le_trans h1 h2
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_pow] at h4
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hLX : Real.log X = L * Real.log 2 := by
      rw [hLdef, Lg, Real.logb, div_mul_cancel₀ _ hl2.ne']
    rw [hLX] at h4
    have : (P.primeFactors.card : ℝ) ≤ V.card * L := by
      have := h4
      nlinarith
    nlinarith
  set y := ⌈L ^ 2⌉₊ + 4 with hy
  have hy4 : 4 ≤ y := by omega
  have hωy : P.primeFactors.card ≤ y := by
    have : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ := by
      have h := le_trans hω (Nat.le_ceil (L ^ 2))
      exact_mod_cast h
    omega
  have hpart3 := sum_W_opf_le P y hy4 hωy
  have hlogy : log (y : ℝ) ≤ log (L ^ 2 + 5) := by
    apply log_le_log (by positivity)
    rw [hy]; push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ L ^ 2)]
  have hsq := log_sq_add_le L hL1
  -- `ξ(r)` is large
  have hxi : C * log D / δ ≤ xi r := by
    have h1 : N₁ ≤ Nat.log 2 r := Nat.le_log_of_pow_le (by norm_num) hrr
    have h2 := log_lt_xi hr hr0
    have : (N₁ : ℝ) ≤ xi r := by exact_mod_cast (by omega : N₁ ≤ xi r)
    exact le_trans (Nat.le_ceil _) this
  have hxr : (0 : ℝ) < xi r := by exact_mod_cast (xi_odd hr hr0).1
  have hpart1 : L * (C * log D) / xi r ≤ δ * L := aux_first L _ δ _ (by linarith) hxr hδ0 hxi
  have hpart3' : C * log y ≤ δ * L := aux_third C δ L _ hC0 hδ0 hL0 (le_trans hlogy hsq)
  have hsing : ∑ ν ∈ V, Sing (m - 2 ^ ν) ≤ 2 * ∑ ν ∈ V, H (m - 2 ^ ν) := by
    rw [mul_sum]; exact sum_le_sum fun ν hν => sing_le_two_H (hn0 ν hν)
  have htail' : L * ∑' k, seriesTerm (k + (D + 1)) ≤ δ * L := by
    have := mul_le_mul_of_nonneg_left htail.le (by linarith : (0 : ℝ) ≤ L); linarith
  have hmain' : ∑ ν ∈ V, H (m - 2 ^ ν) ≤ L * (C * log D) / xi r +
      L * ∑' k, seriesTerm (k + (D + 1)) + C * log y := by
    have := hmain
    rw [← hC] at this
    linarith
  exact aux_final _ _ _ _ _ ε L (by linarith) hε hsing hmain' hpart1 htail' hpart3'

end



end LeanLab.LPZ2007B

/-! ## the bridge to encoding A -/

namespace LeanLab.LPZ2007.Lemma62Port

open Finset Real

theorem sing_eq_Sing (n : ℕ) : LeanLab.LPZ2007.sing n = LeanLab.LPZ2007B.Sing n := rfl

theorem sing_nonneg' (n : ℕ) : 0 ≤ LeanLab.LPZ2007.sing n := by
  unfold LeanLab.LPZ2007.sing
  refine tprod_nonneg fun p => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  split_ifs
  · exact div_nonneg (by linarith) (by linarith)
  · have h1 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; exact h1
    linarith

/-- `t ↦ t − √t` is monotone on `[1, ∞)`. -/
theorem sub_sqrt_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) : s - √s ≤ t - √t := by
  have ha := Real.sqrt_le_sqrt hst
  have ha1 : 1 ≤ √s := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hs
  have e1 := Real.sq_sqrt (show 0 ≤ s by linarith)
  have e2 := Real.sq_sqrt (show 0 ≤ t by linarith)
  nlinarith

/-- **Lemma 6.2 p.9 in encoding A**, the repaired form with `r ≥ r₀`, PROVED from encoding B's
`lemma62_proved` at `⌈X⌉₊` and `ε/2`. -/
theorem lemma62_A : LeanLab.LPZ2007.Lemma62 := by
  intro ε hε
  obtain ⟨r0, X0, H⟩ := LeanLab.LPZ2007B.lemma62_proved (ε / 2) (by positivity)
  refine ⟨r0, max (X0 : ℝ) 2, fun X hX m hm1 hm2 r hr hr0 => ?_⟩
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hX0 : 0 < X := by linarith
  set X' := ⌈X⌉₊ with hX'
  have hXX' : X ≤ (X' : ℝ) := Nat.le_ceil X
  have hX'1 : (X' : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one hX0.le).le
  have hX0' : X0 ≤ X' := by
    have : (X0 : ℝ) ≤ X' := ((le_max_left _ _).trans hX).trans hXX'
    exact_mod_cast this
  have hmX' : (X' : ℝ) / 2 ≤ m := by
    have : X' ≤ 2 * m := Nat.ceil_le.2 (by push_cast; linarith)
    have : (X' : ℝ) ≤ 2 * m := by exact_mod_cast this
    linarith
  have hmX'' : m ≤ X' := by
    have : (m : ℝ) ≤ X' := hm2.trans hXX'
    exact_mod_cast this
  have hB := H X' hX0' m r hmX' hmX'' hr.pos hr hr0
  -- the two logarithms
  have hL1 : 1 ≤ LeanLab.LPZ2007.Lg X := by
    unfold LeanLab.LPZ2007.Lg
    rw [show (1 : ℝ) = Real.logb 2 2 by rw [Real.logb_self_eq_one (by norm_num)]]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hX2
  have hLL : LeanLab.LPZ2007.Lg X ≤ LeanLab.LPZ2007B.Lg X' := by
    unfold LeanLab.LPZ2007.Lg LeanLab.LPZ2007B.Lg
    exact Real.logb_le_logb_of_le (by norm_num) hX0 hXX'
  have hLL1 : LeanLab.LPZ2007B.Lg X' ≤ LeanLab.LPZ2007.Lg X + 1 := by
    unfold LeanLab.LPZ2007.Lg LeanLab.LPZ2007B.Lg
    have h2X : (X' : ℝ) ≤ 2 * X := by linarith
    have hpos : (0 : ℝ) < X' := by linarith
    calc Real.logb 2 (X' : ℝ) ≤ Real.logb 2 (2 * X) :=
          Real.logb_le_logb_of_le (by norm_num) hpos h2X
      _ = Real.logb 2 X + 1 := by
          rw [Real.logb_mul (by norm_num) hX0.ne', Real.logb_self_eq_one (by norm_num)]; ring
  -- the sums
  have hsub : (Icc 1 ⌊LeanLab.LPZ2007.Lp X⌋₊).filter (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν) ⊆
      (Icc 1 ⌊LeanLab.LPZ2007B.Lg X' - √(LeanLab.LPZ2007B.Lg X')⌋₊).filter
        (fun ν => 2 ^ ν < m ∧ r ∣ m - 2 ^ ν) := by
    refine filter_subset_filter _ (Icc_subset_Icc_right (Nat.floor_le_floor ?_))
    unfold LeanLab.LPZ2007.Lp
    exact sub_sqrt_mono hL1 hLL
  have hA : LeanLab.LPZ2007.Amr X m r ≤ LeanLab.LPZ2007B.Amr X' m r := by
    unfold LeanLab.LPZ2007.Amr LeanLab.LPZ2007B.Amr
    convert sum_le_sum_of_subset_of_nonneg hsub (fun ν _ _ => sing_nonneg' (m - 2 ^ ν)) using 1
    exact sum_congr (by ext; simp) (fun _ _ => rfl)
  calc LeanLab.LPZ2007.Amr X m r ≤ ε / 2 * LeanLab.LPZ2007B.Lg X' := hA.trans hB
    _ ≤ ε / 2 * (LeanLab.LPZ2007.Lg X + 1) := by gcongr
    _ ≤ ε * LeanLab.LPZ2007.Lg X := by nlinarith

end LeanLab.LPZ2007.Lemma62Port

namespace LeanLab.LPZ2007

/-- The former cited declaration, now proved with its exact original statement. -/
theorem lemma62 : Lemma62 := Lemma62Port.lemma62_A

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.lemma62
