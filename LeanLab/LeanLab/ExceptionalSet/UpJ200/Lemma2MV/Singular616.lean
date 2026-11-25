import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions
import LeanLab.ExceptionalSet.SingularSeriesLower672
import LeanLab.MissingDigit.SingularSeries

/-!
# P0015 display (6.16), the singular series as a Ramanujan series

Burst burst-20261122, Claude cloud session S53, helper for the LEAF `mv_singular_series_616` of
`Lemma2MVSplit`. Source P0015, Montgomery and Vaughan 1975, page 363 display (6.16), and page 354
for the Ramanujan sum `c_q(m) = Σ'_{h mod q} e(hm/q)`.

The coefficient `μ(q)² φ(q)⁻² c_q(-n)` of the first term of (6.4), written out with the lab's `eC`,
equals the real number `HeathBrown1985.gm n q`. The lab already proves `Σ_q gm n q = 𝔖(n)`
with absolute convergence, `HeathBrown1985.hasSum_gm` and `summable_abs_gm`, and
`Task672.singularSeries_eq_hb672` identifies the two product forms of `𝔖(n)`. So (6.16) holds.
PROVED, sorry free, by reuse.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MV

open Finset
open scoped ArithmeticFunction.Moebius

/-- `e(x)` of P0015 page 354 in the two lab spellings agree. -/
lemma sing616_eC_eq_e (x : ℝ) :
    LeanLab.ExceptionalSet.U1539.eC x = LeanLab.PNTPort.LargeSieve.e x := by
  unfold LeanLab.ExceptionalSet.U1539.eC LeanLab.PNTPort.LargeSieve.e
  congr 1; push_cast; ring

/-- P0015 display (6.4), first term: its coefficient `μ(q)² φ(q)⁻² c_q(-n)` equals
`HeathBrown1985.gm n q`. For `q = 0` both sides vanish. -/
theorem sing616_weight_eq (q n : ℕ) :
    ((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      ∑ h ∈ (range q).filter (fun h => Nat.Coprime h q),
        LeanLab.ExceptionalSet.U1539.eC ((h : ℝ) * ((-(n : ℤ) : ℤ) : ℝ) / q) =
      ((LeanLab.HeathBrown1985.gm n q : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [LeanLab.HeathBrown1985.gm_zero]
  · rw [← LeanLab.MissingDigit.KimSeries.term_eq_gm,
      LeanLab.MissingDigit.KimSeries.term_eq_negative_exponential hq]
    push_cast
    congr 1
    refine sum_congr rfl (fun h _ => ?_)
    rw [sing616_eC_eq_e]
    congr 1
    ring

/-- P0015 display (6.16): for `n ≥ 1` the series `Σ_q gm n q` converges absolutely to the
singular series of P0082 page 358 display 11. -/
theorem sing616_main (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => |LeanLab.HeathBrown1985.gm n q|) ∧
      HasSum (fun q : ℕ => LeanLab.HeathBrown1985.gm n q)
        (LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.singularSeries n) := by
  refine ⟨?_, ?_⟩
  · simpa [Real.norm_eq_abs] using LeanLab.HeathBrown1985.summable_abs_gm n hn
  · rw [LeanLab.ExceptionalSet.Task672.singularSeries_eq_hb672 n hn]
    exact LeanLab.HeathBrown1985.hasSum_gm n hn

#print axioms sing616_weight_eq
#print axioms sing616_main

end LeanLab.ExceptionalSet.UpJ200.Lemma2MV
