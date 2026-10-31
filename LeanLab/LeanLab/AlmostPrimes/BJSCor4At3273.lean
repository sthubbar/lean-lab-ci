/-
P0009 BJS 2022, Corollary 4 at the corrected threshold. The paper, page 63: the non square-free
η counted by π₂(N) are squares of primes or 1, at most √N of them, so π₂*(N) ≥ π₂(N) − 1 − √N > 0
by Theorem 3. Here the same step: any Chen count above the main term `2·10⁻⁴ U_N N / log² N`
forces a square-free `m > 1` with `ω m ≤ 2`, for every `t ≥ 32`. With `chen_3273` this gives
Corollary 4 at exp(exp 32.73), CONDITIONAL ON BJS Theorems 44, 50, 51 as corrected per F-0020 to
F-0022. Unit U-1024, run 20261019T0403Z-4324. AI-written Lean code, Claude. Checked only by the
Lean kernel. Goldbach is open.
-/
import LeanLab.ChenExplicit.Assembly
import LeanLab.AlmostPrimes.BJSThm5Chain

open Real Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

namespace LeanLab.AlmostPrimes.Cor4

open LeanLab.ChenExplicit LeanLab.ChenExplicit.AT3273

/-- Corollary 4 in the strong form the proof gives, at threshold `exp(exp t)`. -/
def Cor4At (t : ℝ) : Prop :=
  ∀ N : ℕ, Even N → Real.exp (Real.exp t) < N →
    ∃ p m : ℕ, p.Prime ∧ N = p + m ∧ 1 < m ∧ Squarefree m ∧ ω m ≤ 2

/-- A nonzero `m` with `Ω m ≤ 2` that is not a square-free number above 1 is a perfect square. -/
theorem square_of_bad {m : ℕ} (hm : m ≠ 0) (hΩ : Ω m ≤ 2) (hbad : ¬ (1 < m ∧ Squarefree m)) :
    ∃ k : ℕ, 1 ≤ k ∧ m = k ^ 2 := by
  by_cases h1 : m = 1
  · exact ⟨1, le_rfl, by simp [h1]⟩
  have hsq : ¬ Squarefree m := fun h => hbad ⟨by omega, h⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨p, hp, r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hm hr
  have hpp : p * p = p ^ 2 := by ring
  rw [hpp] at hr
  have : Ω m = 2 + Ω r := by
    rw [hr, ArithmeticFunction.cardFactors_mul (pow_ne_zero 2 hp.ne_zero) hr0,
      ArithmeticFunction.cardFactors_apply_prime_pow hp]
  have hr1 : Ω r = 0 := by omega
  rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.1 hr1 with h | h
  · exact absurd h hr0
  · exact ⟨p, hp.one_lt.le, by rw [hr, h, mul_one]⟩

/-- `ω n ≤ Ω n`. -/
theorem omega_le_Omega (n : ℕ) : ω n ≤ Ω n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ArithmeticFunction.cardFactors_apply]
  exact n.primeFactorsList.dedup_sublist.length_le

open Classical in
/-- Primes `p < N` whose Chen partner `N - p` is not a square-free number above 1. -/
noncomputable def badSet (N : ℕ) : Finset ℕ :=
  {p ∈ range N | p.Prime ∧ Nat.IsAtMostAlmostPrime 2 (N - p) ∧
    ¬ (1 < N - p ∧ Squarefree (N - p))}

/-- The bad Chen representations number at most `⌊√N⌋`. -/
theorem card_bad_le (N : ℕ) : #(badSet N) ≤ Nat.sqrt N := by
  classical
  have key : ∀ p ∈ badSet N,
      1 ≤ Nat.sqrt (N - p) ∧ (Nat.sqrt (N - p)) ^ 2 = N - p ∧ p < N := by
    intro p hp
    simp only [badSet, mem_filter, mem_range] at hp
    obtain ⟨hpN, -, ⟨h0, hΩ⟩, hbad⟩ := hp
    obtain ⟨k, hk, hkm⟩ := square_of_bad h0 hΩ hbad
    rw [hkm, show k ^ 2 = k * k by ring, Nat.sqrt_eq]
    exact ⟨hk, by ring, hpN⟩
  calc _ ≤ #(Icc 1 (Nat.sqrt N)) := by
        apply card_le_card_of_injOn (fun p => Nat.sqrt (N - p))
        · intro p hp
          obtain ⟨h1, -, -⟩ := key p hp
          simp only [coe_Icc, Set.mem_Icc]
          exact ⟨h1, Nat.sqrt_le_sqrt (Nat.sub_le N p)⟩
        · intro a ha b hb hab
          obtain ⟨-, ha2, haN⟩ := key a ha
          obtain ⟨-, hb2, hbN⟩ := key b hb
          simp only at hab
          have : N - a = N - b := by rw [← ha2, ← hb2, hab]
          omega
    _ = Nat.sqrt N := by simp

/-- `2·10⁻⁷ N / log² N ≥ √N` once `log N ≥ 2.4·10⁸`. -/
theorem main_ge_sqrt {N : ℕ} (hL : (240000000 : ℝ) ≤ Real.log N) :
    √(N : ℝ) ≤ (2 / 10000000 : ℝ) * N / Real.log N ^ 2 := by
  set L := Real.log N
  have hN0 : (0 : ℝ) < N := by
    by_contra h; push Not at h
    have : (N : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg N)
    simp [L, this] at hL; linarith
  have hNe : (N : ℝ) = Real.exp L := (Real.exp_log hN0).symm
  have hsq : √(N : ℝ) = Real.exp (L / 2) := by
    rw [hNe, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hL0 : 0 < L := by linarith
  have h3 : (L / 2) ^ 3 / 6 ≤ Real.exp (L / 2) := by
    have := Real.pow_div_factorial_le_exp (x := L / 2) (by positivity) 3
    simpa [Nat.factorial] using this
  rw [hsq, le_div_iff₀ (by positivity)]
  have hNeq : (N : ℝ) = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [hNe, ← Real.exp_add]; ring_nf
  rw [hNeq]
  have hE : 0 < Real.exp (L / 2) := Real.exp_pos _
  have : L ^ 2 ≤ (2 / 10000000) * Real.exp (L / 2) := by nlinarith
  nlinarith

/-- **The Corollary 4 step, unconditional.** The counting form at `t ≥ 32` gives Corollary 4. -/
theorem cor4_of_BJS3At {t : ℝ} (ht : 32 ≤ t) (h : BJS3At t) : Cor4At t := by
  classical
  intro N hE hN
  have h1 := h N hE hN
  have hL : (240000000 : ℝ) ≤ Real.log N := by
    have hpos : 0 < Real.exp (Real.exp t) := Real.exp_pos _
    have : Real.exp t ≤ Real.log N := by
      rw [← Real.log_exp (Real.exp t)]; exact Real.log_le_log hpos hN.le
    have hh : (2.7182818283 : ℝ) ^ 32 ≤ Real.exp 32 := by
      rw [show (32 : ℝ) = (32 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 32
    have h32 : (2.7182818283 : ℝ) ^ 32 ≤ Real.exp t := hh.trans (Real.exp_le_exp.2 ht)
    have h2 : (6 : ℝ) * 10 ^ 13 ≤ 2.7182818283 ^ 32 := by norm_num
    linarith
  have hU := U_ge N
  have hmain := main_ge_sqrt hL
  have hlow : √(N : ℝ) < chenCount N := by
    have : (2 / 10000000 : ℝ) * N / Real.log N ^ 2 ≤ (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    linarith
  by_contra hno
  push Not at hno
  have hc : chenCount N ≤ Nat.sqrt N := by
    unfold chenCount
    refine (card_le_card ?_).trans (card_bad_le N)
    intro p hp
    simp only [badSet, mem_filter, mem_range] at hp ⊢
    refine ⟨hp.1, hp.2.1, hp.2.2, fun ⟨h1, hs⟩ => ?_⟩
    have hω : ω (N - p) ≤ 2 := (omega_le_Omega _).trans hp.2.2.2
    exact absurd (hno p (N - p) hp.2.1 (by omega) h1 hs) (not_lt.2 hω)
  have : (chenCount N : ℝ) ≤ √(N : ℝ) :=
    (by exact_mod_cast hc : (chenCount N : ℝ) ≤ Nat.sqrt N).trans Real.nat_sqrt_le_real_sqrt
  linarith

/-- **BJS Corollary 4 at exp(exp 32.73)**, CONDITIONAL ON BJS Theorems 44, 50, 51 as corrected
per F-0020 to F-0022, through `chen_3273`. -/
theorem bjs_cor4_3273 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3273 / 100) (cA3273 caseA w)) (hQ : Thm50At (3273 / 100) (cQ3273 caseA))
    (hB : Thm51At (3273 / 100) cB3273) : Cor4At (3273 / 100) :=
  cor4_of_BJS3At (by norm_num) (chen_3273 caseA w hw hA hQ hB)

end LeanLab.AlmostPrimes.Cor4
