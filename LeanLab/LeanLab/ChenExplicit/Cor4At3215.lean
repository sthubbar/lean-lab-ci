/-
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1103Z-29422, unit U-1406, track T2 FRONTIER.
P0009 BJS 2022, arXiv 2207.09452 v6, Section 10, p. 63, P0009.txt lines 3790 to 3806: Corollary 4 from
a count bound. BJS argue π₂*(N) ⩾ π₂(N) − 1 − √N: a P₂ that is not square-free and > 1 is q² with
q² < N, so it costs at most √N representations, and η = 1 at most one. Here with the count bound
π₂(N) > 10⁻⁵ U_N N / log² N of PrintedWiring3215 in place of 2·10⁻⁴.

* `bad_square`, `chenCount_le_of_none`, `small_vs_main`: PROVED unconditional. If no p + η with
  η > 1 square-free and ω η ⩽ 2 exists, then chenCount N ⩽ ⌊√N⌋ + 2; and ⌊√N⌋ + 2 ⩽ 10⁻⁵ U_N N/log² N
  once log N ⩾ 9.174·10¹³.
* `cor4_3215_of_printedC`: every even N > exp(exp 32.15) is p + η with η > 1 square-free and
  ω(η) ⩽ 2, CONDITIONAL ON PrintedThm44, PrintedThm50C, PrintedThm51C, PrintedLemma42 at 32.15.
* `cor4_3215_of_printed`: the same CONDITIONAL ON the verbatim Theorems 50 and 51.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.PrintedWiring3215

open Real Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit.Cor4At3215

open LeanLab.ChenExplicit LeanLab.ChenExplicit.PrintedWiring3215

/-- The Corollary 4 conclusion with η > 1, as in Statements.BJS4strong, above exp(exp t). -/
def BJS4strongAt (t : ℝ) : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp t) < N →
    ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ 1 < m ∧ Squarefree m ∧ ω m ≤ 2

/-- A nonzero m with Ω m ⩽ 2 that is not square-free is the square of a prime. -/
lemma bad_square {m : ℕ} (h0 : m ≠ 0) (hΩ : Ω m ≤ 2) (hsq : ¬ Squarefree m) :
    ∃ q : ℕ, q.Prime ∧ m = q * q := by
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨q, hq, k, hk⟩ := hsq
  have hq' : q.Prime := hq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact h0 hk
  have hqq : q * q ≠ 0 := mul_ne_zero hq'.ne_zero hq'.ne_zero
  have hΩm : Ω m = 2 + Ω k := by
    rw [hk, ArithmeticFunction.cardFactors_mul hqq hk0,
      ArithmeticFunction.cardFactors_mul hq'.ne_zero hq'.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hq']
  have hk1 : Ω k = 0 := by omega
  rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hk1 with h | h
  · exact absurd h hk0
  · exact ⟨q, hq', by rw [hk, h, mul_one]⟩

/-- **If N has no representation p + η with η > 1 square-free and ω η ⩽ 2, then
π₂(N) ⩽ ⌊√N⌋ + 2**, the counting step of p. 63. -/
lemma chenCount_le_of_none (N : ℕ)
    (hnone : ¬ ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ 1 < m ∧ Squarefree m ∧ ω m ≤ 2) :
    chenCount N ≤ Nat.sqrt N + 2 := by
  classical
  unfold chenCount
  refine (card_le_card (t := (insert (N - 1) ((range (Nat.sqrt N + 1)).image (fun q : ℕ => N - q * q)) : Finset ℕ))
    ?_).trans ?_
  · intro p hp
    rw [mem_filter, mem_range] at hp
    obtain ⟨hpN, hpp, hm0, hΩ⟩ := hp
    rw [mem_insert, mem_image]
    by_cases h1 : N - p = 1
    · left; omega
    · right
      by_cases hs : Squarefree (N - p)
      · exfalso
        apply hnone
        refine ⟨p, N - p, hpp, by omega, by omega, hs, ?_⟩
        rw [(ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hm0).mpr hs]
        exact hΩ
      · obtain ⟨q, -, hqe⟩ := bad_square hm0 hΩ hs
        have hle : q * q ≤ N := by rw [← hqe]; exact Nat.sub_le N p
        refine ⟨q, mem_range.mpr (Nat.lt_succ_of_le (Nat.le_sqrt.mpr hle)), ?_⟩
        generalize q * q = s at hqe hle ⊢
        omega
  · calc (insert (N - 1) ((range (Nat.sqrt N + 1)).image (fun q => N - q * q))).card
        ≤ ((range (Nat.sqrt N + 1)).image (fun q => N - q * q)).card + 1 := card_insert_le _ _
      _ ≤ (range (Nat.sqrt N + 1)).card + 1 :=
          Nat.add_le_add_right (card_image_le (s := range (Nat.sqrt N + 1)) (f := fun q : ℕ => N - q * q)) 1
      _ = Nat.sqrt N + 2 := by rw [card_range]

/-- **⌊√N⌋ + 2 ⩽ 10⁻⁵ U_N N / log² N for log N ⩾ 9.174·10¹³**, from U_N ⩾ 1/1000 and
L⁶/720 ⩽ e^L. -/
lemma small_vs_main (N : ℕ) (h1 : 1 < (N : ℝ)) (h9 : (9.174 : ℝ) * 10 ^ 13 ≤ Real.log N) :
    ((Nat.sqrt N : ℕ) : ℝ) + 2 ≤ 1 / 100000 * mainTerm N := by
  set L := Real.log (N : ℝ) with hLd
  have hNp : (0 : ℝ) < N := by linarith
  have hNe : exp L = (N : ℝ) := exp_log hNp
  have hU := U_ge N
  have hL0 : 0 < L := by linarith
  have hexp : 9 * 10 ^ 16 * L ^ 4 ≤ (N : ℝ) := by
    rw [← hNe]
    have h6 := Real.pow_div_factorial_le_exp L hL0.le 6
    have hf : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hf] at h6
    have hL2 : (6.48 : ℝ) * 10 ^ 19 ≤ L ^ 2 := by nlinarith
    have hL4 : 0 ≤ L ^ 4 := by positivity
    have : 9 * 10 ^ 16 * L ^ 4 * 720 ≤ L ^ 4 * L ^ 2 := by nlinarith
    have e6 : L ^ 6 = L ^ 4 * L ^ 2 := by ring
    rw [e6] at h6
    linarith
  set c : ℝ := 1 / (10 ^ 8 * L ^ 2) with hc
  have hc0 : 0 < c := by positivity
  have hmain : c * N ≤ 1 / 100000 * mainTerm N := by
    simp only [mainTerm]
    rw [hc]
    have hL2 : 0 < L ^ 2 := by positivity
    rw [show 1 / 100000 * (U N * N / L ^ 2) = (U N / 100000) * N / L ^ 2 by ring,
      show 1 / (10 ^ 8 * L ^ 2) * (N : ℝ) = (1 / 10 ^ 8) * N / L ^ 2 by field_simp]
    apply div_le_div_of_nonneg_right _ hL2.le
    apply mul_le_mul_of_nonneg_right _ hNp.le
    linarith
  have hc2N : 9 ≤ c ^ 2 * N := by
    have e : c ^ 2 * N = N / (10 ^ 16 * L ^ 4) := by rw [hc]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  set s : ℝ := ((Nat.sqrt N : ℕ) : ℝ) with hs
  have hs2 : s * s ≤ N := by
    rw [hs]; exact_mod_cast Nat.sqrt_le N
  have hN1 : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hs1 : 1 ≤ s := by
    rw [hs]; exact_mod_cast Nat.sqrt_pos.mpr hN1
  have hcN : 0 ≤ c * N := by positivity
  have hsq : (3 * s) * (3 * s) ≤ (c * N) * (c * N) := by
    have : 9 * (N : ℝ) ≤ c ^ 2 * N * N := by nlinarith
    nlinarith
  have h3 : 3 * s ≤ c * N := by nlinarith
  linarith

/-- **Corollary 4 at exp(exp 32.15)**: every even N > exp(exp 32.15) is p + η with η > 1
square-free and ω(η) ⩽ 2. CONDITIONAL ON PrintedThm44, PrintedThm50C, PrintedThm51C and
PrintedLemma42 at 32.15. -/
theorem cor4_3215_of_printedC (k1 : ℕ → ℝ)
    (h : PrintedThm44 k1 ∧ PrintedThm50C k1 ∧ PrintedThm51C ∧ PrintedLemma42) :
    BJS4strongAt (3215 / 100) := by
  intro N hE hN
  have hc := (chenPos_3215_of_printedC k1 h).2 N hE hN
  by_contra hnone
  have hle := chenCount_le_of_none N hnone
  have hX : X2 < (N : ℝ) := hN
  obtain ⟨h1, -, h9⟩ := logN_facts hX
  have hsm := small_vs_main N h1 h9
  have hle' : (chenCount N : ℝ) ≤ ((Nat.sqrt N : ℕ) : ℝ) + 2 := by exact_mod_cast hle
  linarith

/-- **Corollary 4 at exp(exp 32.15), CONDITIONAL ON PrintedThm44, the verbatim PrintedThm50 and
PrintedThm51, and PrintedLemma42.** -/
theorem cor4_3215_of_printed (k1 : ℕ → ℝ)
    (h : PrintedThm44 k1 ∧ PrintedThm50 k1 ∧ PrintedThm51 ∧ PrintedLemma42) :
    BJS4strongAt (3215 / 100) :=
  cor4_3215_of_printedC k1 ⟨h.1, printed50_imp_C k1 h.2.1, printed51_imp_C h.2.2.1, h.2.2.2⟩

/-- Vacuity of `small_vs_main`: its hypotheses hold for N = 2·(⌈X₂⌉ + 1), an even N > X₂. -/
example : ∃ N : ℕ, Even N ∧ 1 < (N : ℝ) ∧ (9.174 : ℝ) * 10 ^ 13 ≤ Real.log N := by
  obtain ⟨N, hE, hX, -⟩ := hyps_inhabited
  obtain ⟨h1, -, h9⟩ := logN_facts hX
  exact ⟨N, hE, h1, h9⟩

end LeanLab.ChenExplicit.Cor4At3215

#print axioms LeanLab.ChenExplicit.Cor4At3215.bad_square
#print axioms LeanLab.ChenExplicit.Cor4At3215.chenCount_le_of_none
#print axioms LeanLab.ChenExplicit.Cor4At3215.small_vs_main
#print axioms LeanLab.ChenExplicit.Cor4At3215.cor4_3215_of_printedC
#print axioms LeanLab.ChenExplicit.Cor4At3215.cor4_3215_of_printed
