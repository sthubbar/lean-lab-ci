/-
AI wrote this Lean code. Claude, route burst session 5, assembly jackpot check, 2026-11-12.
Binary Goldbach is open; this file concerns only the Tolev 2009 exceptional set paper.

Replays `Decomp83.legacy_assembly` with downstream twins of its two route steps:
* `MajorArc341.major_arc_leaf : BoundE1`, sorry free per its axioms check.
* `Decomp424c.minor_arc_sup_leaf : Sup12Uniform`, CONDITIONAL ON the open leaf
  `Decomp424a.grouped_annular_decomposition`.
The statement keeps the hypothesis `hSeries` exactly as in `Decomp83.legacy_assembly`,
so the result stays CONDITIONAL ON that identity. No existing file is changed.
-/
import LeanLab.Tolev2009.Decomp83
import LeanLab.Tolev2009.MajorArc341
import LeanLab.Tolev2009.Decomp424c

namespace LeanLab.Tolev2009.FinishAssembly1112

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.SeriesIdentification

/-- The published assembly, with the two steps replaced by their downstream twins. -/
theorem published_assembly_finished : TheTheorem halupczokSeries :=
  PublishedTheorem.publishedTheorem_of_display9_sup12
    MajorArc341.major_arc_leaf Decomp424c.minor_arc_sup_leaf

/-- Exact statement of `Decomp83.legacy_assembly`, replayed with the twins. -/
theorem legacy_assembly_finished (hSeries : halupczokS = halupczokSeries) :
    TheTheorem halupczokS :=
  Decomp83.legacy_transfer hSeries published_assembly_finished

end LeanLab.Tolev2009.FinishAssembly1112
