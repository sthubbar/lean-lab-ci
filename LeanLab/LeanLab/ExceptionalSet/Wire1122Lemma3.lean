import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
import LeanLab.ExceptionalSet.UpJ200.Lemma3MVItildeEval

/-!
# Wiring: P0015 display (6.1̃7) through the S74 split and the proved evaluation of `Ĩ(n)`

Burst burst-20261122, Claude cloud session S74, branch claude/ExceptionalSet-wire_lemma3,
stacked on claude/ExceptionalSet-itilde_eval and claude/ExceptionalSet-mv617_integral.

`Lemma3MV617Split.mv_617_tilde_of_leaves` proves the LEAF `Lemma3MVSplit.mv_617_tilde` from the
two leaves `mv_617_tilde_integral` and `mv_Itilde_eval` by name. Here the same argument runs
with the proved `Lemma3MVItildeEval.mv_Itilde_eval_proved` and the S74 assembly
`Lemma3MV617Integral.mv_617_tilde_integral_of_steps`, so `mv_617_tilde` rests only on the seven
LEAFs of that split, P0015 pages 361 to 365. The QUESTION on `mv_615_absorbed` recorded in the
notes of mv617_integral applies.

No new definition, no sorry, no statement changed. AI wrote the Lean code. Binary Goldbach is
open.
-/

namespace LeanLab.ExceptionalSet.Wire1122Lemma3

open LeanLab.ExceptionalSet.UpJ200

/-- P0015 display (6.1̃7), the exact type of the LEAF `Lemma3MVSplit.mv_617_tilde`, from the
proved evaluation of `Ĩ(n)` on page 365 and the split of the integral form on pages 361 to 365. -/
theorem mv_617_tilde_wired : type_of% @Lemma3MVSplit.mv_617_tilde := by
  intro a ha
  obtain ⟨C, hC, h⟩ := Lemma3MV617Integral.mv_617_tilde_integral_of_steps a ha
  refine ⟨C, hC, fun θ hθ hθ1 => ?_⟩
  obtain ⟨P₀, hP⟩ := h θ hθ hθ1
  refine ⟨P₀, fun X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev => ?_⟩
  have hI := Lemma3MVItildeEval.mv_Itilde_eval_proved β (X ^ θ) X (Real.rpow_nonneg hX.le θ)
    m hm hmX
  have key := hP X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev
  rw [hI, Complex.ofReal_re] at key
  exact key

end LeanLab.ExceptionalSet.Wire1122Lemma3

#print axioms LeanLab.ExceptionalSet.Wire1122Lemma3.mv_617_tilde_wired
