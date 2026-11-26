import LeanLab.Halupczok2012.Split398aMajor

/-!
Split of leaf `Split398aMajor.a7_R1_sup`, PP1993 page 46 display 12, into faithful leaves.
Source: A. Perelli and J. Pintz, J. London Math. Soc. 47, 1993, pages 41 to 49, PP1993.
Proof of display 12: for n coprime to q, e of an/q is 1/phi q times the sum over chi mod q
of chi of a, tau of chi bar and chi of n; the principal character has tau equal to mu q, so
R1 equals 1/phi q times the sum over chi of chi of a, tau of chi bar, and the twisted sum
of Lambda chi minus delta_chi against e of n eta, plus the prime powers n not coprime to q.
Each twisted sum is bounded by partial summation in eta with display 6 on sub intervals.
Leaves: `e1_expansion` MEDIUM, `e2_twisted_partial_summation` MEDIUM.
Proved: `gauss_norm_le`, `charsum_bound`, and the assembly `a7_of_leaves`, which has
exactly the statement of `a7_R1_sup`; it cannot close that leaf in place, since this file
imports Split398aMajor. The Gauss sum is bounded trivially by q, a loss of
L^{B/2} against the paper's q^{1/2}, absorbed since display 12 holds for every C'.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMajorA7

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a
  LeanLab.Halupczok2012.Split398aMajor

/-- LEAF: PP1993 p. 46, the character expansion before display 12, R1 equal to 1/phi q
times the sum over chi of chi of a, tau of chi bar and W1 of chi and eta, plus an error. For
q at most N, N at least 2 and a reduced, the error is at most 2 log^2 N, the prime powers
not coprime to q; tau of chi_0 is mu q. The page writes the error O of Y^{1/2}; this bound
was checked numerically for q = 7, 8, 9, 10, 12. Class MEDIUM. -/
theorem e1_expansion : ∀ N Y η : ℝ, ∀ (q : ℕ) [NeZero q], ∀ a : ℕ,
    a.Coprime q → (q : ℝ) ≤ N → 2 ≤ N →
    ‖firstR N Y q a η - (1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) *
          ∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
            phase ((n : ℝ) * η)‖ ≤ 2 * Real.log N ^ 2 := by
  sorry

/-- LEAF: PP1993 p. 46 display 12, the partial summation step. Given display 6, for every
chi mod q with q at most L^B and eta in xi'_q, the twisted sum of Lambda n chi n minus
delta_chi against e of n eta over N - Y below n at most N is at most K Y L^{2B - C'};
partial summation in eta costs 1 + 2 pi |eta| Y, at most a constant times L^{2B}, and
display 6 is applied on every sub interval N - Y below n at most t, with the trivial bound
for the sub intervals shorter than Y L^{-C'}. Class MEDIUM. -/
theorem e2_twisted_partial_summation (h6 : ShortSW) :
    ∀ ε A C' : ℝ, 0 < ε → 0 < A → 0 < C' → ∃ K N0 : ℝ, ∀ N Y η : ℝ, ∀ (q : ℕ) [NeZero q],
    ∀ χ : DirichletCharacter ℂ q,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → q ∈ majorQ N ε A → η ∈ xiArc N Y ε A q →
    ‖∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
        phase ((n : ℝ) * η)‖ ≤ K * Y * Real.log N ^ (2 * bigB ε A - C') := by
  sorry

/-- Proved: the trivial bound for the Gauss sum, its norm is at most q. -/
theorem gauss_norm_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)‖ ≤ q := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b : ZMod q, ‖(starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)‖ ≤ ∑ _b : ZMod q, (1 : ℝ) := by
        refine sum_le_sum fun b _ => ?_
        rw [norm_mul]
        unfold phase
        rw [LeanLab.PNTPort.LargeSieve.norm_e, mul_one, Complex.norm_conj]
        exact DirichletCharacter.norm_le_one χ b
    _ = q := by simp [ZMod.card]

/-- Proved: the sum over characters, given a bound M on every twisted sum, is at most q M. -/
theorem charsum_bound (q : ℕ) [NeZero q] (a : ℕ) (T : DirichletCharacter ℂ q → ℂ) (M : ℝ)
    (hT : ∀ χ, ‖T χ‖ ≤ M) :
    ‖(1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) * T χ‖ ≤ q * M := by
  letI : Fintype (DirichletCharacter ℂ q) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hT 1)
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hphi : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [norm_mul]
  have hs : ‖∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) * T χ‖ ≤
      Nat.totient q * (q * M) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ : DirichletCharacter ℂ q, ‖χ (a : ZMod q) *
            (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) * T χ‖
          ≤ ∑ _χ : DirichletCharacter ℂ q, (q * M : ℝ) := by
            refine sum_le_sum fun χ _ => ?_
            rw [norm_mul, norm_mul]
            have h1 := DirichletCharacter.norm_le_one χ (a : ZMod q)
            have h2 := gauss_norm_le q χ
            have h3 := hT χ
            have h0 : 0 ≤ ‖χ (a : ZMod q)‖ := norm_nonneg _
            have h0' : 0 ≤ ‖∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)‖ := norm_nonneg _
            calc ‖χ (a : ZMod q)‖ * ‖∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)‖ * ‖T χ‖
                ≤ 1 * q * M := by gcongr
              _ = q * M := by ring
      _ = Nat.totient q * (q * M) := by rw [sum_const, card_univ, nsmul_eq_mul, hcard]
  calc ‖1 / (Nat.totient q : ℂ)‖ * _ ≤ ‖1 / (Nat.totient q : ℂ)‖ * (Nat.totient q * (q * M)) :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = q * M := by
        rw [norm_div, norm_one, Complex.norm_natCast]
        field_simp

/-- Proved: the assembly, with exactly the statement of `Split398aMajor.a7_R1_sup`, from the
leaves `e1_expansion` and `e2_twisted_partial_summation`. -/
theorem a7_of_leaves (h6 : ShortSW) : A7Stmt := by
  intro ε A C' hε hA hC'
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  set B := bigB ε A with hBdef
  obtain ⟨K, N1, hK⟩ := e2_twisted_partial_summation h6 ε A (C' + B) hε hA (by linarith)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (((log_rpow_le_eventually (2 + C' - 2 * B) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)).and
    (log_rpow_le_eventually B (show (0 : ℝ) < 1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num))).and (Filter.eventually_ge_atTop (max N1 3)))
  refine ⟨max K 0 + 1, N0, ?_⟩
  intro N Y q a η hN hlow hYN hq ha hη
  obtain ⟨⟨c1, c2⟩, hN3⟩ := hN0 N hN
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN3
  have hN3' : 3 ≤ N := (le_max_right _ _).trans hN3
  have hNpos : 0 < N := by linarith
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log N with hLdef
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  haveI : NeZero q := ⟨by omega⟩
  have hqL : (q : ℝ) ≤ L ^ B := by
    have h := (mem_Icc.mp hq).2
    exact (Nat.le_floor_iff (Real.rpow_nonneg hL0.le _)).mp h
  have hqN : (q : ℝ) ≤ N := by
    rw [Real.rpow_one, one_mul] at c2
    linarith
  have haq : a.Coprime q := (mem_filter.mp ha).2
  have hP1 : 1 ≤ N ^ ((7 : ℝ) / 12) := Real.one_le_rpow (by linarith) (by norm_num)
  have hPY : N ^ ((7 : ℝ) / 12) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hlow
  have hY0 : 0 < Y := by linarith
  have hE1 := e1_expansion N Y η q a haq hqN (by linarith)
  have hT : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
        phase ((n : ℝ) * η)‖ ≤ max K 0 * Y * L ^ (2 * B - (C' + B)) := fun χ =>
    (hK N Y η q χ hN1 hlow hYN hq hη).trans
      (by gcongr; exact le_max_left _ _)
  have hE3 := charsum_bound q a _ _ hT
  have hpow : (q : ℝ) * (max K 0 * Y * L ^ (2 * B - (C' + B))) ≤
      max K 0 * Y * L ^ (2 * B - C') := by
    have e : L ^ (2 * B - C') = L ^ B * L ^ (2 * B - (C' + B)) := by
      rw [← Real.rpow_add hL0]; ring_nf
    rw [e]
    have : 0 ≤ max K 0 * Y * L ^ (2 * B - (C' + B)) := by positivity
    nlinarith [le_max_right K 0, Real.rpow_nonneg hL0.le (2 * B - (C' + B))]
  have hcorr : 2 * L ^ 2 ≤ Y * L ^ (2 * B - C') := by
    have e : L ^ (2 : ℕ) = L ^ (2 + C' - 2 * B) * L ^ (2 * B - C') := by
      rw [← Real.rpow_add hL0, ← Real.rpow_natCast]; ring_nf
    rw [e]
    have hp : 0 < L ^ (2 * B - C') := Real.rpow_pos_of_pos hL0 _
    nlinarith
  calc ‖firstR N Y q a η‖ ≤ ‖firstR N Y q a η - (1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) *
          ∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
            phase ((n : ℝ) * η)‖ + ‖(1 / (Nat.totient q : ℂ)) *
        ∑ᶠ χ : DirichletCharacter ℂ q, χ (a : ZMod q) *
          (∑ b : ZMod q, (starRingEnd ℂ) (χ b) * phase ((b.val : ℝ) / q)) *
          ∑ n ∈ kRange (N - Y) Y, ((Λ n : ℂ) * χ (n : ZMod q) - deltaChi χ) *
            phase ((n : ℝ) * η)‖ := norm_le_norm_sub_add _ _
    _ ≤ 2 * L ^ 2 + max K 0 * Y * L ^ (2 * B - C') := add_le_add hE1 (hE3.trans hpow)
    _ ≤ (max K 0 + 1) * Y * L ^ (2 * B - C') := by nlinarith

end LeanLab.Halupczok2012.Split398aMajorA7
