import LeanLab.PNTPort.ExplicitPsi1.DudekLemma4

/-! `Zpatch = Zreal` on `y > 1`, unit U-6560, CLOUD 20261020T1518Z-cloud45. AI wrote this file. -/

namespace LeanLab.PNTPort.ExplicitPsi1.Trivial

theorem Zpatch_eq {y : ℝ} (hy : 1 < y) : Zpatch y = Zreal y := by
  unfold Zpatch; exact if_pos hy

end LeanLab.PNTPort.ExplicitPsi1.Trivial
