import LeanLab.HelfgottMajor.SPLIT_book_error_le_half_exp
import LeanLab.HelfgottMajor.FALSE_conductor_log_le_quarter_exp

/-!
Machine link for the disproof in `FALSE_conductor_log_le_quarter_exp.lean`.

That file negates a textual copy of the leaf `conductor_log_le_quarter_exp`. Here the negation is
stated against the type of the declaration itself, taken with `type_of%`, so no transcription
can drift. Only the statements of the refuted declarations are used, never their proofs, so the
`sorry` under the leaf does not enter the axioms of these theorems. AI wrote this Lean code.
-/

namespace LeanLab.HelfgottMajor.FalseConductorLog
open Real

/-- FALSE, machine linked. The type of the leaf `Decomp269c.conductor_log_le_quarter_exp` is a
false proposition. -/
theorem conductor_log_le_quarter_exp_type_false :
    ¬ (type_of% @LeanLab.HelfgottMajor.Decomp269c.conductor_log_le_quarter_exp) :=
  fun h => conductor_log_le_quarter_exp_false (fun q t hq ht => h q t hq ht)

/-- FALSE, machine linked. The type of the assembled target
`Decomp269c.book_error_le_half_exp_split`, the bound of `bookError q (t + 1)` by
`exp (0.6 * t) / 2` for every nonzero `q` and every `t` at least `100`, is a false proposition. -/
theorem book_error_le_half_exp_split_type_false :
    ¬ (type_of% @LeanLab.HelfgottMajor.Decomp269c.book_error_le_half_exp_split) := by
  intro h
  refine explicit_book_error_le_half_exp_false (fun q t hq ht => ?_)
  have : NeZero q := ⟨hq⟩
  have := h q t ht
  unfold ZeroCount1623.bookError at this
  exact this

end LeanLab.HelfgottMajor.FalseConductorLog

#print axioms LeanLab.HelfgottMajor.FalseConductorLog.conductor_log_le_quarter_exp_type_false
#print axioms LeanLab.HelfgottMajor.FalseConductorLog.book_error_le_half_exp_split_type_false
