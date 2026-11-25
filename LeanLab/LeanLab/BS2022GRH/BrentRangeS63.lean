/-
Schoenfeld 1976, Math. Comp. 30, p. 340: the Brent range of the proof of Corollary 1,
`|π x - li x| ≤ 4613.5` for `5·10⁷ ≤ x ≤ 49·10⁸`.

Schoenfeld's display, with `p` the least prime exceeding `x`:
`|π x - li x| = {li x - π x} < [li x + 1/2] - π x + 1/2 ≤ [li p + 1/2] - {π p - 1} + 1/2 ≤ 4613.5`.
The cited steps are LEAF theorems with a class tag; the glue is proved.

AI wrote this Lean code, Claude, ROUTE BURST S63 burst-20261122, unit brent_range.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.LiPV

namespace LeanLab.BS2022GRH.BrentRangeS63
open Real
open LeanLab.BS2022GRH.PaperInputs148

noncomputable section

/-- LEAF: Brent 1975 Table 1, as used by Schoenfeld 1976 p. 340. HARD.
For all primes `p < 50·10⁸`, `[li p + 1/2] - π p ≤ 4612`. -/
theorem brent_table : ∀ p : ℕ, p.Prime → p < 5 * 10 ^ 9 →
    ((⌊liPV p + 1 / 2⌋ : ℤ) : ℝ) - primeCount p ≤ 4612 := by
  sorry

/-- LEAF: Schoenfeld 1976 p. 340, "a consequence of Brent [3], [4]": `li x - π x > 0`
on the range `5·10⁷ ≤ x ≤ 49·10⁸`. HARD. -/
theorem li_gt_pi : ∀ x : ℝ, 5 * 10 ^ 7 ≤ x → x ≤ 49 * 10 ^ 8 →
    primeCount x < liPV x := by
  sorry

set_option maxRecDepth 1000000 in
/-- LEAF: Brent [3] prime gaps, used implicitly by Schoenfeld 1976 p. 340 so that the least
prime above `x ≤ 49·10⁸` lies below `50·10⁸`. EASY numerical: a prime in `(49·10⁸, 50·10⁸)`.
PROVED in S63 with the witness 4900000013 and the norm_num primality extension. -/
theorem prime_below_5e9 : ∃ q : ℕ, q.Prime ∧ 49 * 10 ^ 8 < q ∧ q < 5 * 10 ^ 9 :=
  ⟨4900000013, by norm_num, by norm_num, by norm_num⟩

/-- Monotonicity of the logarithmic integral on `[2, ∞)`, from `liPV_eq_add`
and positivity of `1 / log t` for `t > 1`. Proved. -/
theorem liPV_mono : ∀ a b : ℝ, 2 ≤ a → a ≤ b → liPV a ≤ liPV b := by
  intro a b ha hab
  have hii : ∀ u v : ℝ, 2 ≤ u → 2 ≤ v →
      IntervalIntegrable (fun t => 1 / log t) MeasureTheory.volume u v := by
    intro u v hu hv
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun t ht => by
        rw [Set.mem_uIcc] at ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    · intro t ht
      rw [Set.mem_uIcc] at ht
      have : (1 : ℝ) < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      exact (Real.log_pos this).ne'
  rw [liPV_eq_add ha, liPV_eq_add (le_trans ha hab),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 2 a le_rfl ha)
      (hii a b ha (le_trans ha hab))]
  have : 0 ≤ ∫ t in a..b, 1 / log t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    have : (1 : ℝ) < t := by linarith [ht.1]
    exact (one_div_pos.mpr (Real.log_pos this)).le
  linarith

/-- If `p` is the least prime exceeding `n`, then `π p = π n + 1`. -/
lemma card_least_prime (n p : ℕ) (hnp : n < p) (hp : p.Prime)
    (hmin : ∀ k, n < k → k < p → ¬ k.Prime) :
    ((Finset.range (p + 1)).filter (fun k => k.Prime)).card
      = ((Finset.range (n + 1)).filter (fun k => k.Prime)).card + 1 := by
  have h : (Finset.range (p + 1)).filter (fun k => k.Prime)
      = insert p ((Finset.range (n + 1)).filter (fun k => k.Prime)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hk, hkp⟩
      by_cases hkn : k < n + 1
      · exact Or.inr ⟨hkn, hkp⟩
      · left
        by_contra hne
        exact hmin k (by omega) (by omega) hkp
    · rintro (rfl | ⟨hk, hkp⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, hkp⟩
  rw [h, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Schoenfeld 1976 p. 340, the Brent range: glue from the leaves above. -/
theorem brent_range_glue : ∀ x : ℝ, 5 * 10 ^ 7 ≤ x → x ≤ 49 * 10 ^ 8 →
    |primeCount x - liPV x| ≤ 4613.5 := by
  classical
  intro x h1 h2
  set n := ⌊x⌋₊ with hn
  have hex : ∃ p, n < p ∧ p.Prime := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, by omega, hp2⟩
  set p := Nat.find hex with hpdef
  have hpspec := Nat.find_spec hex
  have hmin : ∀ k, n < k → k < p → ¬ k.Prime := fun k hk hkp hpr =>
    Nat.find_min hex hkp ⟨hk, hpr⟩
  obtain ⟨q, hq, hq1, hq2⟩ := prime_below_5e9
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hnq : n < q := by
    have : (n : ℝ) ≤ x := Nat.floor_le hx0
    have : ((49 * 10 ^ 8 : ℕ) : ℝ) < q := by exact_mod_cast hq1
    push_cast at this
    exact_mod_cast (show (n : ℝ) < q by linarith)
  have hpq : p ≤ q := Nat.find_min' hex ⟨hnq, hq⟩
  have hp5 : p < 5 * 10 ^ 9 := lt_of_le_of_lt hpq hq2
  have hxp : x < (p : ℝ) := by
    have h3 : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have h4 : n + 1 ≤ p := hpspec.1
    have : ((n + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast h4
    push_cast at this
    linarith
  have hmono := liPV_mono x p (by linarith) hxp.le
  have hpos := li_gt_pi x h1 h2
  have hbt := brent_table p hpspec.2 hp5
  have hcount : primeCount (p : ℝ) = primeCount x + 1 := by
    unfold primeCount
    rw [Nat.floor_natCast, card_least_prime n p hpspec.1 hpspec.2 hmin]
    push_cast; ring
  have hfl : liPV p + 1 / 2 < ((⌊liPV p + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  rw [hcount] at hbt
  linarith

end

end LeanLab.BS2022GRH.BrentRangeS63

#print axioms LeanLab.BS2022GRH.BrentRangeS63.liPV_mono
#print axioms LeanLab.BS2022GRH.BrentRangeS63.card_least_prime
#print axioms LeanLab.BS2022GRH.BrentRangeS63.brent_range_glue
#print axioms LeanLab.BS2022GRH.BrentRangeS63.prime_below_5e9
