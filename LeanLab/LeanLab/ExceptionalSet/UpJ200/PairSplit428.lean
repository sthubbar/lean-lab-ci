import LeanLab.ExceptionalSet.UpJ200.Moment385
import LeanLab.ExceptionalSet.UpJ200.Decomp404e

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.PairSplit428`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
The product integral split used on P0082 page 366 between displays 26 and 27.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.PairSplit428

open Real MeasureTheory Set ComplexConjugate

/-- Split an integrable pair kernel into the distant and nearby strips.
Source: P0082 page 366 between displays 26 and 27. -/
theorem integral_pair_split (A : Set ℝ) (g : ℝ × ℝ → ℝ) (r : ℝ)
    (hg : Integrable g ((volume.restrict A).prod (volume.restrict A))) :
    (∫ z : ℝ × ℝ, g z ∂(volume.restrict A).prod (volume.restrict A)) =
      (∫ α in A, ∫ β in A ∩ {β : ℝ | r < |α - β|}, g (α, β)) +
      (∫ α in A, ∫ β in A ∩ {β : ℝ | |α - β| ≤ r}, g (α, β)) := by
  let D : Set (ℝ × ℝ) := {z | r < |z.1 - z.2|}
  have hD : MeasurableSet D := by
    exact measurableSet_lt measurable_const ((measurable_fst.sub measurable_snd).abs)
  have hd := hg.indicator hD
  have hn := hg.indicator hD.compl
  have he : g = (fun z => D.indicator g z + Dᶜ.indicator g z) := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  conv_lhs => rw [he]
  rw [integral_add hd hn, integral_prod _ hd, integral_prod _ hn]
  congr 1
  · apply integral_congr_ae
    filter_upwards with α
    have hsec : MeasurableSet {β : ℝ | r < |α - β|} := by
      exact measurableSet_lt measurable_const ((measurable_const.sub measurable_id).abs)
    have hfun : (fun β => D.indicator g (α, β)) =
        ({β : ℝ | r < |α - β|}).indicator (fun β => g (α, β)) := by
      ext β
      simp only [Set.indicator_apply, D, Set.mem_setOf_eq]
    rw [hfun, setIntegral_indicator hsec]
  · apply integral_congr_ae
    filter_upwards with α
    have hsec : MeasurableSet {β : ℝ | |α - β| ≤ r} := by
      exact measurableSet_le ((measurable_const.sub measurable_id).abs) measurable_const
    have hfun : (fun β => Dᶜ.indicator g (α, β)) =
        ({β : ℝ | |α - β| ≤ r}).indicator (fun β => g (α, β)) := by
      ext β
      simp only [Set.indicator_apply, D, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    rw [hfun, setIntegral_indicator hsec]

end LeanLab.ExceptionalSet.UpJ200.PairSplit428
