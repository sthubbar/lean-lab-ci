import Mathlib
import LeanLab.BakerHarmanPintz1997.Statements

/-!
# Baker, Harman, Pintz 1997, Theorem 3 (I) as printed is false

Audit U-1009, run 20261019T0503Z-10740. AI wrote this Lean code.

Theorem 3 (I), p. 4, prints `0.99M/𝓛 < π(x;q,a) - π(x-M;q,a) < 1.01M/𝓛` for every
`q ≤ 𝓛^A` and `(a,q) = 1`, without the factor `1/φ(q)`. Summing the lower bound over the
`φ(q)` reduced classes gives more primes in `(x - M, x]` than there are integers once
`φ(q) ≥ 2𝓛`, and such `q ≤ 𝓛²` exist by Bertrand. So the printed statement fails for every `x`
large, with `A = 2`, `ε = 0.05`, `M = x/𝓛`. This is a misprint: the proof picks out the class
`a mod q` "using characters in standard fashion", which gives `M/(φ(q)𝓛)`. Cosmetic; the
lab's cited `Theorem3I` now carries `φ(q)`. Elementary, no analytic input.
-/

namespace LeanLab.BakerHarmanPintz1997.Theorem3ILiteral
open Real Finset

/-- primes in `(⌊y⌋, ⌊x⌋]` in the class `a mod q` -/
noncomputable def win (y x : ℝ) (q a : ℕ) : Finset ℕ :=
  (Ioc ⌊y⌋₊ ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)

theorem piAP_le (y x : ℝ) (q a : ℕ) :
    piAP x q a ≤ piAP y q a + (win y x q a).card := by
  unfold piAP win
  calc ((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card
      ≤ ((Icc 1 ⌊y⌋₊ ∪ Ioc ⌊y⌋₊ ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card := by
        apply card_le_card
        apply filter_subset_filter
        intro n hn
        simp only [mem_Icc] at hn
        simp only [mem_union, mem_Icc, mem_Ioc]
        by_cases h : n ≤ ⌊y⌋₊
        · exact Or.inl ⟨hn.1, h⟩
        · exact Or.inr ⟨by omega, hn.2⟩
    _ ≤ _ := by rw [filter_union]; exact card_union_le _ _

/-- the windows over distinct reduced residues are disjoint, so their sizes add to at most the
number of integers in `(⌊y⌋, ⌊x⌋]` -/
theorem sum_win_le (y x : ℝ) (q : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a < q) :
    ∑ a ∈ S, (win y x q a).card ≤ ⌊x⌋₊ - ⌊y⌋₊ := by
  set s := (Ioc ⌊y⌋₊ ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q ∈ S) with hs
  have hfib := card_eq_sum_card_fiberwise (f := fun p => p % q) (s := s) (t := S)
    (by intro p hp; simp only [hs, coe_filter, Set.mem_setOf_eq, mem_coe] at hp ⊢; exact hp.2.2)
  have heq : ∀ a ∈ S, (win y x q a).card = (s.filter (fun p => p % q = a)).card := by
    intro a ha
    congr 1
    ext p
    have : a % q = a := Nat.mod_eq_of_lt (hS a ha)
    simp only [win, hs, mem_filter, this]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, h3 ▸ ha⟩, h3⟩
    · rintro ⟨⟨h1, h2, _⟩, h3⟩; exact ⟨h1, h2, h3⟩
  rw [sum_congr rfl heq, ← hfib]
  calc s.card ≤ (Ioc ⌊y⌋₊ ⌊x⌋₊).card := card_filter_le _ _
    _ = ⌊x⌋₊ - ⌊y⌋₊ := Nat.card_Ioc _ _

theorem floor_window (x M : ℝ) (hM : 0 ≤ M) (hxM : 0 ≤ x - M) :
    ((⌊x⌋₊ - ⌊x - M⌋₊ : ℕ) : ℝ) ≤ M + 1 := by
  have h1 : ⌊x - M⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub h1]
  have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h3 : x - M < (⌊x - M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith

/-- **Theorem 3 (I) as printed is false.** PROVED. -/
theorem not_theorem3I_literal : ¬ Theorem3I_literal := by
  intro h
  obtain ⟨C3, hC3⟩ := h 0.05 (by norm_num) 2 (by norm_num)
  set x : ℝ := max (C3 + 1) (exp 25) with hx
  have hx25 : exp 25 ≤ x := le_max_right _ _
  have hxpos : 0 < x := lt_of_lt_of_le (exp_pos 25) hx25
  have hxC : C3 < x := by have := le_max_left (C3 + 1) (exp 25); linarith
  set Lx : ℝ := L x with hLx
  have hL25 : 25 ≤ Lx := by
    rw [hLx, L]; calc (25 : ℝ) = log (exp 25) := (log_exp 25).symm
      _ ≤ log x := log_le_log (exp_pos 25) hx25
  have hLpos : 0 < Lx := by linarith
  -- x^r = exp (r L)
  have hpow : ∀ r : ℝ, x ^ r = exp (r * Lx) := by
    intro r; rw [rpow_def_of_pos hxpos, hLx, L, mul_comm]
  -- L ≤ x^{0.4}
  have hL04 : Lx ≤ x ^ (0.4 : ℝ) := by
    rw [hpow]
    have e1 : 0.2 * Lx + 1 ≤ exp (0.2 * Lx) := by linarith [add_one_le_exp (0.2 * Lx)]
    have e2 : exp (0.4 * Lx) = exp (0.2 * Lx) * exp (0.2 * Lx) := by
      rw [← exp_add]; ring_nf
    rw [e2]; nlinarith
  set M : ℝ := x / Lx with hMdef
  have hx1 : x ^ (0.6 : ℝ) * x ^ (0.4 : ℝ) = x := by
    rw [← rpow_add hxpos]; norm_num
  have hlow : x ^ (0.55 + 0.05 : ℝ) ≤ M := by
    rw [hMdef, le_div_iff₀ hLpos]
    have : (0.55 + 0.05 : ℝ) = 0.6 := by norm_num
    rw [this]
    calc x ^ (0.6 : ℝ) * Lx ≤ x ^ (0.6 : ℝ) * x ^ (0.4 : ℝ) :=
          mul_le_mul_of_nonneg_left hL04 (rpow_nonneg hxpos.le _)
      _ = x := hx1
  have hM2 : 2 ≤ M := by
    have : 2 ≤ x ^ (0.55 + 0.05 : ℝ) := by
      rw [hpow]; linarith [add_one_le_exp ((0.55 + 0.05) * Lx)]
    linarith
  have hMx : M ≤ x := by
    rw [hMdef, div_le_iff₀ hLpos]; nlinarith
  -- Bertrand: a prime q with ⌈3L⌉ < q ≤ 2⌈3L⌉
  set n : ℕ := ⌈3 * Lx⌉₊ with hn
  have hn0 : n ≠ 0 := by
    have : (0 : ℝ) < 3 * Lx := by linarith
    rw [hn]; exact (Nat.ceil_pos.mpr this).ne'
  obtain ⟨q, hqp, hnq, hq2n⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have hn_ge : 3 * Lx ≤ n := Nat.le_ceil _
  have hn_le : (n : ℝ) < 3 * Lx + 1 := Nat.ceil_lt_add_one (by linarith)
  have hq_ge : (n : ℝ) + 1 ≤ q := by exact_mod_cast hnq
  have hq_le : (q : ℝ) ≤ 2 * n := by exact_mod_cast hq2n
  have hqL : (q : ℝ) ≤ Lx ^ (2 : ℝ) := by
    rw [rpow_two]; nlinarith
  have hq1 : 1 ≤ q := hqp.one_lt.le
  -- the reduced residues
  set S : Finset ℕ := (range q).filter (Nat.Coprime q) with hS
  have hScard : S.card = Nat.totient q := by rw [hS, Nat.totient]
  have htot : (Nat.totient q : ℝ) = q - 1 := by
    rw [Nat.totient_prime hqp, Nat.cast_sub hq1]; simp
  have hSlt : ∀ a ∈ S, a < q := by
    intro a ha; rw [hS, mem_filter, mem_range] at ha; exact ha.1
  have hSne : S.Nonempty := by
    refine ⟨1, ?_⟩; rw [hS, mem_filter, mem_range]
    exact ⟨hqp.one_lt, Nat.coprime_one_right q⟩
  -- each class has more than 0.99 M / L primes in the window
  have hcls : ∀ a ∈ S, 0.99 * M / Lx < ((win (x - M) x q a).card : ℝ) := by
    intro a ha
    have hcop : Nat.Coprime a q := by
      rw [hS, mem_filter] at ha; exact ha.2.symm
    have h1 := (hC3 x hxC M hlow le_rfl q a hq1 hqL hcop).1
    have h2 := piAP_le (x - M) x q a
    have h2' : (piAP x q a : ℝ) ≤ piAP (x - M) q a + (win (x - M) x q a).card := by
      exact_mod_cast h2
    linarith
  have hsum := sum_lt_sum_of_nonempty hSne hcls
  rw [sum_const, hScard, nsmul_eq_mul] at hsum
  have hwin : ((∑ a ∈ S, (win (x - M) x q a).card : ℕ) : ℝ) ≤ M + 1 := by
    calc ((∑ a ∈ S, (win (x - M) x q a).card : ℕ) : ℝ) ≤ ((⌊x⌋₊ - ⌊x - M⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast sum_win_le (x - M) x q S hSlt
      _ ≤ M + 1 := floor_window x M (by linarith) (by linarith)
  push_cast at hwin
  -- φ(q) · 0.99 M / L ≥ 1.98 M ≥ M + 1
  have hbig : M + 1 ≤ (Nat.totient q : ℝ) * (0.99 * M / Lx) := by
    rw [htot]
    have : 2 * Lx ≤ (q : ℝ) - 1 := by linarith
    have h3 : (2 * Lx) * (0.99 * M / Lx) = 1.98 * M := by field_simp; ring
    have h4 : (2 * Lx) * (0.99 * M / Lx) ≤ ((q : ℝ) - 1) * (0.99 * M / Lx) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  linarith

end LeanLab.BakerHarmanPintz1997.Theorem3ILiteral
