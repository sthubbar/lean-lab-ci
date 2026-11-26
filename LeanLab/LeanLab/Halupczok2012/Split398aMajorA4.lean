import LeanLab.Halupczok2012.Decomp398a
import LeanLab.PNTPort.BV.Helpers

/-!
Split of the leaf `Split398aMajor.a4_sigma1`, PP1993 page 45, the two unnumbered displays
after display 7: given A3, Sigma_1 at 2k equals the singular series times M* plus
O of Y times the Ramanujan tail plus O of Y L^{-B}.
Source: A. Perelli and J. Pintz, J. London Math. Soc. 47, 1993, pages 41 to 49, PP1993.
The proof regroups the sum over reduced residues into the Ramanujan sum c_q of -m,
replaces each integral by M* with the error of A3, sums that error with the weight
mu^2 q over phi^2 q times |c_q| at most 1 over phi q, and identifies the truncated
Ramanujan series with S of 2k minus the tail.
Two leaves: `sum_div_totient_le`, the mean value of q over phi q, PROVED, and
`singular_ramanujan`, the singular series of p. 41 as the full Ramanujan series, open.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMajorA4

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a

/-- PP1993 p. 43: M* of m is at most Y, since k = m - h runs injectively in 1 to Y. -/
theorem ppM_le (m : ℕ) (N Y : ℝ) (hY : 0 ≤ Y) : LeanLab.Halupczok2012.ppM m N Y ≤ Y := by
  unfold LeanLab.Halupczok2012.ppM
  have h1 : ((Ioo 0 m).filter (LeanLab.Halupczok2012.ppCond m N Y)).card ≤
      (Icc 1 ⌊Y⌋₊).card := by
    apply card_le_card_of_injOn (fun h => m - h)
    · intro h hh
      simp only [coe_filter, Set.mem_setOf_eq, mem_Ioo] at hh
      simp only [coe_Icc, Set.mem_Icc]
      refine ⟨by omega, Nat.le_floor hh.2.2.2⟩
    · intro h hh h' hh' heq
      simp only [coe_filter, Set.mem_setOf_eq, mem_Ioo] at hh hh'
      simp only at heq
      omega
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  calc (((Ioo 0 m).filter (LeanLab.Halupczok2012.ppCond m N Y)).card : ℝ)
      ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ Y := Nat.floor_le hY

/-- LEAF: PP1993 p. 45, summing the error of A3 over q at most L^B with weight mu^2 q
over phi^2 q times |c_q| at most 1 over phi q needs the mean value of q over phi q,
the sum over q at most Q of q over phi q at most c Q, from q over phi q equal to the sum
over d dividing q of mu^2 d over phi d. Class MEDIUM. PROVED, with c = 4, from
PNTPort.BV.Helpers inv_totient_eq and sum_inv_mul_totient_le. -/
theorem sum_div_totient_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ Q : ℕ, ∑ q ∈ Icc 1 Q, (q : ℝ) / (Nat.totient q : ℝ) ≤ c * Q := by
  refine ⟨4, by norm_num, fun Q => ?_⟩
  open LeanLab.PNTPort.BV in
  have hq : ∀ q ∈ Icc 1 Q, (q : ℝ) / (Nat.totient q : ℝ) = ∑ d ∈ q.divisors, sqfTot d := by
    intro q hq
    have hq0 : q ≠ 0 := by rw [Finset.mem_Icc] at hq; omega
    have h := LeanLab.PNTPort.BV.inv_totient_eq hq0
    have : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    rw [div_eq_mul_one_div, h]
    field_simp
  rw [sum_congr rfl hq]
  have hswap : ∑ q ∈ Icc 1 Q, ∑ d ∈ q.divisors, LeanLab.PNTPort.BV.sqfTot d =
      ∑ d ∈ Icc 1 Q, ∑ q ∈ (Icc 1 Q).filter (d ∣ ·), LeanLab.PNTPort.BV.sqfTot d := by
    apply Finset.sum_comm'
    intro q d
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd, hq0⟩
      have := Nat.le_of_dvd (by omega) hd
      have := Nat.pos_of_dvd_of_pos hd (by omega)
      exact ⟨⟨⟨h1, h2⟩, hd⟩, by omega, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, hd⟩, h3, h4⟩
      exact ⟨⟨h1, h2⟩, hd, by omega⟩
  rw [hswap]
  have hcard : ∀ d ∈ Icc 1 Q, (((Icc 1 Q).filter (d ∣ ·)).card : ℝ) ≤ (Q : ℝ) / d := by
    intro d hd
    have h1 : (Icc 1 Q).filter (d ∣ ·) = (Ioc 0 Q).filter (d ∣ ·) := by
      congr 1
    rw [h1, Nat.Ioc_filter_dvd_card_eq_div]
    exact Nat.cast_div_le
  calc ∑ d ∈ Icc 1 Q, ∑ q ∈ (Icc 1 Q).filter (d ∣ ·), LeanLab.PNTPort.BV.sqfTot d
      = ∑ d ∈ Icc 1 Q, LeanLab.PNTPort.BV.sqfTot d * ((Icc 1 Q).filter (d ∣ ·)).card := by
        refine sum_congr rfl fun d _ => ?_
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ d ∈ Icc 1 Q, LeanLab.PNTPort.BV.sqfTot d * ((Q : ℝ) / d) := by
        refine sum_le_sum fun d hd => ?_
        exact mul_le_mul_of_nonneg_left (hcard d hd) (LeanLab.PNTPort.BV.sqfTot_nonneg d)
    _ = Q * ∑ d ∈ Icc 1 Q, LeanLab.PNTPort.BV.sqfTot d / d := by
        rw [mul_sum]
        refine sum_congr rfl fun d _ => ?_
        ring
    _ ≤ Q * 4 := mul_le_mul_of_nonneg_left (LeanLab.PNTPort.BV.sum_inv_mul_totient_le Q)
        (by positivity)
    _ = 4 * Q := by ring

/-- LEAF: PP1993 p. 41 and p. 45, the singular series of display 2 is the full Ramanujan
series, S of 2k equal to the sum over all q of mu^2 q over phi^2 q times c_q of -2k,
absolutely convergent, here c_q written out as the sum of e of a times -2k over q
over reduced a, by the Euler product of U1457SingSeries local_factor and
euler_expand. Class MEDIUM. -/
theorem singular_ramanujan (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun q : ℕ => ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ∑ a ∈ (Icc 1 q).filter (fun a => a.Coprime q),
        phase ((a : ℝ) * ((-((2 * k : ℕ) : ℤ) : ℤ) : ℝ) / q)) ((S (2 * k) : ℝ) : ℂ) := by
  sorry

end LeanLab.Halupczok2012.Split398aMajorA4
