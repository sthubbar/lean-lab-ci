/-
P0022, Kaniecki 1995. PC run 20261021T0303Z-27628, unit U-1340, T1.
The guarded Lemma 5 and the Remark through Lemma5Kernel.lean: `Kernel9` and `Const451`
replaced by `Const4`, the kernel integral being PROVED there.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Kernel
import LeanLab.Kaniecki1995.Lemma4Guard

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995

/-- **Lemma 5, guarded**, CONDITIONAL ON `Lemma4G`, `Parseval1920`, `Bound21`, `Const4`. -/
theorem lemma5G_of_K4 (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21) (hC : Const4) :
    Lemma5G :=
  lemma5G_of h4 hP h21 (bound22_of_K4 hC)

/-- **The Remark, p. 373**, CONDITIONAL ON `Lemma4G`, `Parseval1920`, `Bound21`, `Const4`. -/
theorem remark_of_lemma4G_K4 (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21)
    (hC : Const4) : RemarkStatement :=
  remark_ofG (lemma5G_of_K4 h4 hP h21 hC) eq23

/-- **Theorem, odd part, p. 362**, CONDITIONAL ON `Lemma4G`, `Parseval1920`, `Bound21`,
`Const4`, the three Dudek chain inputs of Lemma 6, Young-Potler, Sinisalo and Chen-Wang. -/
theorem theoremOdd_of_lemma4G_K4 (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21)
    (hC : Const4)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) (hS : Sinisalo)
    (hCW : ChenWang) : TheoremOdd :=
  theoremOdd_ofG (lemma5G_of_K4 h4 hP h21 hC) eq23
    (L6T.lemma6_of_trudgian hN hSch hG) hYP hS hCW

/-- **Theorem, even part, p. 362**, CONDITIONAL ON `Lemma4G`, `Parseval1920`, `Bound21`,
`Const4`, the three Dudek chain inputs of Lemma 6, Young-Potler and Chen-Wang. -/
theorem theoremEven_of_lemma4G_K4 (h4 : Lemma4G) (hP : Parseval1920) (h21 : Bound21)
    (hC : Const4)
    (hN : LeanLab.Dudek2014.SigmaT.TrudgianN70 LeanLab.PNTPort.ExplicitPsi1.Trivial.gZ)
    (hSch : LeanLab.Dudek2014.Section22.Schoenfeld)
    (hG : LeanLab.GoldbachGaps.Sumset.GapBound1476) (hYP : YoungPotler) (hCW : ChenWang) :
    TheoremEven :=
  theoremEven_ofG (lemma5G_of_K4 h4 hP h21 hC) eq23
    (L6T.lemma6_of_trudgian hN hSch hG) hYP hCW

end LeanLab.Kaniecki1995.L5
