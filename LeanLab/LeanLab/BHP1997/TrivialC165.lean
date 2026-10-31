/-
P0069, page 22, an elementary audit of the Perron leaf.
The absolute value method proves the logarithmic length subrange.
It loses N squared in the general fourth moment and leaves the full
analytic input OPEN. AI wrote the Lean code. CODEX task165.
Goldbach is open.
-/
import LeanLab.BHP1997.MeanValue132

namespace LeanLab.BHP1997.TrivialC165
open Classical Complex MeanValue132

/-- Page 22, an auxiliary telescoping bound for reciprocal square roots. -/
theorem reciprocal_sqrt_step (k : ℕ) :
    1 / Real.sqrt (k + 1 : ℝ) ≤ 2 * (Real.sqrt (k + 1 : ℝ) - Real.sqrt (k : ℝ)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkp : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hkp)]
  nlinarith [Real.sq_sqrt hk, Real.sq_sqrt hkp.le,
    sq_nonneg (Real.sqrt (k + 1 : ℝ) - Real.sqrt (k : ℝ))]

/-- Page 22, the absolute coefficient bound uses the reciprocal square
root sum, at most twice the square root of the length. -/
theorem reciprocal_sqrt_sum (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt (M : ℝ) := by
  induction M with
  | zero => simp
  | succ M hM =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs := reciprocal_sqrt_step M
    push_cast
    linarith

/-- Page 22, the absolute value estimate for the unweighted partial sum.
This uses only character norms at most 1 and the reciprocal square root sum. -/
theorem partialSum_norm_le {q : ℕ} (N : ℝ) (hN : 0 ≤ N)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖partialSum N χ t‖ ≤ 2 * Real.sqrt N := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊N⌋₊) :
      ‖χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ ≤ 1 / Real.sqrt (n : ℝ) := by
    have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hn0]
    have hh : (Thm4.half t).re = (1 / 2 : ℝ) := by simp [Thm4.half]
    rw [hh, ← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (Real.sqrt_nonneg _)
  calc
    ‖partialSum N χ t‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊,
        ‖χ (n : ZMod q) / (n : ℂ) ^ Thm4.half t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, 1 / Real.sqrt (n : ℝ) := Finset.sum_le_sum hterm
    _ ≤ 2 * Real.sqrt (⌊N⌋₊ : ℝ) := reciprocal_sqrt_sum _
    _ ≤ 2 * Real.sqrt N := by gcongr; exact Nat.floor_le hN

/-- Pages 11 and 22, the number of well-spaced pairs in the time range
is at most phi of q times 2T plus 1. The modulus is nonzero. -/
theorem wellSpaced_card_le {q : ℕ} [NeZero q]
    (S : Finset (ℝ × DirichletCharacter ℂ q)) {T : ℝ} (hT : 0 ≤ T)
    (hspace : Thm4.WellSpaced S) (htimes : ∀ p ∈ S, |p.1| ≤ T) :
    (S.card : ℝ) ≤ (q.totient : ℝ) * (2 * T + 1) := by
  let f : ℝ × DirichletCharacter ℂ q → ℕ × DirichletCharacter ℂ q :=
    fun p => (⌊p.1 + T⌋₊, p.2)
  let M := ⌊2 * T⌋₊ + 1
  have hinj : Set.InjOn f (S : Set (ℝ × DirichletCharacter ℂ q)) := by
    intro p hp r hr hpr
    have hc : p.2 = r.2 := congrArg (fun z : ℕ × DirichletCharacter ℂ q => z.2) hpr
    have hf : ⌊p.1 + T⌋₊ = ⌊r.1 + T⌋₊ := congrArg (fun z : ℕ × DirichletCharacter ℂ q => z.1) hpr
    have hp0 : 0 ≤ p.1 + T := by linarith [(abs_le.mp (htimes p hp)).1]
    have hr0 : 0 ≤ r.1 + T := by linarith [(abs_le.mp (htimes r hr)).1]
    by_contra hne
    have hs := hspace p hp r hr hne hc
    have hp1 := Nat.floor_le hp0
    have hp2 := Nat.lt_floor_add_one (p.1 + T)
    have hr1 := Nat.floor_le hr0
    have hr2 := Nat.lt_floor_add_one (r.1 + T)
    rw [hf] at hp1 hp2
    have hh : |p.1 - r.1| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith
  have hsub : S.image f ⊆ (Finset.range M).product Finset.univ := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ?_, Finset.mem_univ _⟩
    have hh := Nat.floor_mono (show r.1 + T ≤ 2 * T by linarith [(abs_le.mp (htimes r hr)).2])
    dsimp [f, M]
    omega
  have hcard : S.card ≤ M * q.totient := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.product_eq_sprod,
      Finset.card_product, Finset.card_range] at hh
    have hc : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    simpa only [Finset.card_univ, hc] using hh
  have hcast : (S.card : ℝ) ≤ (M : ℝ) * q.totient := by exact_mod_cast hcard
  have hM : (M : ℝ) ≤ 2 * T + 1 := by
    dsimp [M]
    push_cast
    linarith [Nat.floor_le (show 0 ≤ 2 * T by positivity)]
  have hh := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ q.totient)
  nlinarith

/-- Page 22, the trivial fourth moment loses N squared. This bound
explains why the absolute value method does not close the full Lemma 9. -/
theorem fourth_moment_trivial {q : ℕ} [NeZero q]
    (S : Finset (ℝ × DirichletCharacter ℂ q)) {N T : ℝ} (hN : 0 ≤ N) (hT : 2 ≤ T)
    (hspace : Thm4.WellSpaced S) (htimes : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ‖partialSum N p.2 p.1‖ ^ 4) ≤ 40 * (q : ℝ) * T * N ^ 2 := by
  have hpoint (p : ℝ × DirichletCharacter ℂ q) :
      ‖partialSum N p.2 p.1‖ ^ 4 ≤ 16 * N ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (partialSum_norm_le N hN p.2 p.1) 4
    have hs : Real.sqrt N ^ 4 = N ^ 2 := by nlinarith [Real.sq_sqrt hN]
    simpa only [mul_pow, hs, show (2 : ℝ) ^ 4 = 16 by norm_num] using hh
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ S) => hpoint p)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc := wellSpaced_card_le S (by linarith) hspace htimes
  have hphi : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hbound : (S.card : ℝ) ≤ (q : ℝ) * (5 / 2 * T) := by
    calc
      (S.card : ℝ) ≤ (q.totient : ℝ) * (2 * T + 1) := hc
      _ ≤ (q : ℝ) * (2 * T + 1) := mul_le_mul_of_nonneg_right hphi (by linarith)
      _ ≤ (q : ℝ) * (5 / 2 * T) := mul_le_mul_of_nonneg_left (by linarith) hq0
  nlinarith [mul_le_mul_of_nonneg_right hbound (show 0 ≤ 16 * N ^ 2 by positivity)]

/-- Page 22, an elementary subrange of the Lemma 9 main term.
For N at most a fixed log power, the absolute value method gives the
required qT times log power fourth moment, with no analytic input. -/
theorem logarithmic_length_moment {q : ℕ} [NeZero q]
    (S : Finset (ℝ × DirichletCharacter ℂ q)) {x N T K : ℝ}
    (hx : 2 ≤ x) (hN : 0 ≤ N) (hT : 2 ≤ T)
    (hNK : N ≤ Real.log x ^ K)
    (hspace : Thm4.WellSpaced S) (htimes : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ‖partialSum N p.2 p.1‖ ^ 4) ≤
      40 * (q : ℝ) * T * Real.log x ^ (2 * K) := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow : N ^ 2 ≤ Real.log x ^ (2 * K) := by
    calc
      N ^ 2 ≤ (Real.log x ^ K) ^ 2 := pow_le_pow_left₀ hN hNK 2
      _ = Real.log x ^ (2 * K) := by
        rw [← Real.rpow_mul_natCast hlog.le]
        congr 1
        ring
  exact (fourth_moment_trivial S hN hT hspace htimes).trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))

end LeanLab.BHP1997.TrivialC165
