/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Grid 1/160 T7 trial. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveCTables160
import LeanLab.Akeno2026.SieveC160R7K1120
import LeanLab.Akeno2026.SieveC160R7K1200
import LeanLab.Akeno2026.SieveC160R7K1280
import LeanLab.Akeno2026.SieveC160R7K1360
import LeanLab.Akeno2026.SieveC160R7K1440
import LeanLab.Akeno2026.SieveC160R7K1520
import LeanLab.Akeno2026.SieveC160R7K1600
namespace LeanLab.Akeno2026.SieveFns.Grid160
open Real Set MeasureTheory intervalIntegral
theorem chk_c7 : ∀ k < 1640, 1120 ≤ k → checks7 k := by
  intro k hk hlo
  by_cases h1120 : k < 1200
  · exact chk_c7_1120 k h1120 (by omega)
  by_cases h1200 : k < 1280
  · exact chk_c7_1200 k h1200 (by omega)
  by_cases h1280 : k < 1360
  · exact chk_c7_1280 k h1280 (by omega)
  by_cases h1360 : k < 1440
  · exact chk_c7_1360 k h1360 (by omega)
  by_cases h1440 : k < 1520
  · exact chk_c7_1440 k h1440 (by omega)
  by_cases h1520 : k < 1600
  · exact chk_c7_1520 k h1520 (by omega)
  exact chk_c7_1600 k hk (by omega)
theorem TB_c7 (k : ℕ) (h1 : 1120 ≤ k) (h2 : k ≤ 1640) : TB (cR 7) 160 10000000000 cL7 cU7 k := by
  refine level_ind (f := cR 6) (e := cR 5) (Lf := cL6) (Uf := cU6) (Le := cL5) (Ue := cU5) (N := 1640)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (cR_monoOn 6 _) (cR_monoOn 5 _)
    (fun j hj1 hj2 => TB_c6 j (by omega) (by omega))
    (fun i hi1 hi2 => ⟨TB_c5 i (by omega) (by omega), TB_c5 (i + 1) (by omega) (by omega)⟩)
    (TB_c_base 5 cL7 cU7 (by decide +kernel) (by decide +kernel)) (of_ball chk_c7) k h1 h2
  · intro a b ha hab; exact cR_delay 5 (by norm_num at ha ⊢; linarith) hab
  · intro p x hp hpx; exact cR_delay 4 (by norm_num at hp ⊢; linarith) hpx

end LeanLab.Akeno2026.SieveFns.Grid160
