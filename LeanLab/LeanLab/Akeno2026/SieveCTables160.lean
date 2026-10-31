/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Grid 1/160 certificates. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveC160R2K320
import LeanLab.Akeno2026.SieveC160R2K400
import LeanLab.Akeno2026.SieveC160R2K480
import LeanLab.Akeno2026.SieveC160R2K560
import LeanLab.Akeno2026.SieveC160R2K640
import LeanLab.Akeno2026.SieveC160R2K720
import LeanLab.Akeno2026.SieveC160R2K800
import LeanLab.Akeno2026.SieveC160R2K880
import LeanLab.Akeno2026.SieveC160R2K960
import LeanLab.Akeno2026.SieveC160R2K1040
import LeanLab.Akeno2026.SieveC160R2K1120
import LeanLab.Akeno2026.SieveC160R3K480
import LeanLab.Akeno2026.SieveC160R3K560
import LeanLab.Akeno2026.SieveC160R3K640
import LeanLab.Akeno2026.SieveC160R3K720
import LeanLab.Akeno2026.SieveC160R3K800
import LeanLab.Akeno2026.SieveC160R3K880
import LeanLab.Akeno2026.SieveC160R3K960
import LeanLab.Akeno2026.SieveC160R3K1040
import LeanLab.Akeno2026.SieveC160R3K1120
import LeanLab.Akeno2026.SieveC160R3K1200
import LeanLab.Akeno2026.SieveC160R3K1280
import LeanLab.Akeno2026.SieveC160R4K640
import LeanLab.Akeno2026.SieveC160R4K720
import LeanLab.Akeno2026.SieveC160R4K800
import LeanLab.Akeno2026.SieveC160R4K880
import LeanLab.Akeno2026.SieveC160R4K960
import LeanLab.Akeno2026.SieveC160R4K1040
import LeanLab.Akeno2026.SieveC160R4K1120
import LeanLab.Akeno2026.SieveC160R4K1200
import LeanLab.Akeno2026.SieveC160R4K1280
import LeanLab.Akeno2026.SieveC160R4K1360
import LeanLab.Akeno2026.SieveC160R4K1440
import LeanLab.Akeno2026.SieveC160R5K800
import LeanLab.Akeno2026.SieveC160R5K880
import LeanLab.Akeno2026.SieveC160R5K960
import LeanLab.Akeno2026.SieveC160R5K1040
import LeanLab.Akeno2026.SieveC160R5K1120
import LeanLab.Akeno2026.SieveC160R5K1200
import LeanLab.Akeno2026.SieveC160R5K1280
import LeanLab.Akeno2026.SieveC160R5K1360
import LeanLab.Akeno2026.SieveC160R5K1440
import LeanLab.Akeno2026.SieveC160R5K1520
import LeanLab.Akeno2026.SieveC160R5K1600
import LeanLab.Akeno2026.SieveC160R6K960
import LeanLab.Akeno2026.SieveC160R6K1040
import LeanLab.Akeno2026.SieveC160R6K1120
import LeanLab.Akeno2026.SieveC160R6K1200
import LeanLab.Akeno2026.SieveC160R6K1280
import LeanLab.Akeno2026.SieveC160R6K1360
import LeanLab.Akeno2026.SieveC160R6K1440
import LeanLab.Akeno2026.SieveC160R6K1520
import LeanLab.Akeno2026.SieveC160R6K1600
namespace LeanLab.Akeno2026.SieveFns.Grid160
open Real Set MeasureTheory intervalIntegral
theorem chk_c2 : ∀ k < 1200, 320 ≤ k → checks2 k := by
  intro k hk hlo
  by_cases h320 : k < 400
  · exact chk_c2_320 k h320 (by omega)
  by_cases h400 : k < 480
  · exact chk_c2_400 k h400 (by omega)
  by_cases h480 : k < 560
  · exact chk_c2_480 k h480 (by omega)
  by_cases h560 : k < 640
  · exact chk_c2_560 k h560 (by omega)
  by_cases h640 : k < 720
  · exact chk_c2_640 k h640 (by omega)
  by_cases h720 : k < 800
  · exact chk_c2_720 k h720 (by omega)
  by_cases h800 : k < 880
  · exact chk_c2_800 k h800 (by omega)
  by_cases h880 : k < 960
  · exact chk_c2_880 k h880 (by omega)
  by_cases h960 : k < 1040
  · exact chk_c2_960 k h960 (by omega)
  by_cases h1040 : k < 1120
  · exact chk_c2_1040 k h1040 (by omega)
  exact chk_c2_1120 k hk (by omega)
theorem chk_c3 : ∀ k < 1320, 480 ≤ k → checks3 k := by
  intro k hk hlo
  by_cases h480 : k < 560
  · exact chk_c3_480 k h480 (by omega)
  by_cases h560 : k < 640
  · exact chk_c3_560 k h560 (by omega)
  by_cases h640 : k < 720
  · exact chk_c3_640 k h640 (by omega)
  by_cases h720 : k < 800
  · exact chk_c3_720 k h720 (by omega)
  by_cases h800 : k < 880
  · exact chk_c3_800 k h800 (by omega)
  by_cases h880 : k < 960
  · exact chk_c3_880 k h880 (by omega)
  by_cases h960 : k < 1040
  · exact chk_c3_960 k h960 (by omega)
  by_cases h1040 : k < 1120
  · exact chk_c3_1040 k h1040 (by omega)
  by_cases h1120 : k < 1200
  · exact chk_c3_1120 k h1120 (by omega)
  by_cases h1200 : k < 1280
  · exact chk_c3_1200 k h1200 (by omega)
  exact chk_c3_1280 k hk (by omega)
theorem chk_c4 : ∀ k < 1480, 640 ≤ k → checks4 k := by
  intro k hk hlo
  by_cases h640 : k < 720
  · exact chk_c4_640 k h640 (by omega)
  by_cases h720 : k < 800
  · exact chk_c4_720 k h720 (by omega)
  by_cases h800 : k < 880
  · exact chk_c4_800 k h800 (by omega)
  by_cases h880 : k < 960
  · exact chk_c4_880 k h880 (by omega)
  by_cases h960 : k < 1040
  · exact chk_c4_960 k h960 (by omega)
  by_cases h1040 : k < 1120
  · exact chk_c4_1040 k h1040 (by omega)
  by_cases h1120 : k < 1200
  · exact chk_c4_1120 k h1120 (by omega)
  by_cases h1200 : k < 1280
  · exact chk_c4_1200 k h1200 (by omega)
  by_cases h1280 : k < 1360
  · exact chk_c4_1280 k h1280 (by omega)
  by_cases h1360 : k < 1440
  · exact chk_c4_1360 k h1360 (by omega)
  exact chk_c4_1440 k hk (by omega)
theorem chk_c5 : ∀ k < 1640, 800 ≤ k → checks5 k := by
  intro k hk hlo
  by_cases h800 : k < 880
  · exact chk_c5_800 k h800 (by omega)
  by_cases h880 : k < 960
  · exact chk_c5_880 k h880 (by omega)
  by_cases h960 : k < 1040
  · exact chk_c5_960 k h960 (by omega)
  by_cases h1040 : k < 1120
  · exact chk_c5_1040 k h1040 (by omega)
  by_cases h1120 : k < 1200
  · exact chk_c5_1120 k h1120 (by omega)
  by_cases h1200 : k < 1280
  · exact chk_c5_1200 k h1200 (by omega)
  by_cases h1280 : k < 1360
  · exact chk_c5_1280 k h1280 (by omega)
  by_cases h1360 : k < 1440
  · exact chk_c5_1360 k h1360 (by omega)
  by_cases h1440 : k < 1520
  · exact chk_c5_1440 k h1440 (by omega)
  by_cases h1520 : k < 1600
  · exact chk_c5_1520 k h1520 (by omega)
  exact chk_c5_1600 k hk (by omega)
theorem chk_c6 : ∀ k < 1640, 960 ≤ k → checks6 k := by
  intro k hk hlo
  by_cases h960 : k < 1040
  · exact chk_c6_960 k h960 (by omega)
  by_cases h1040 : k < 1120
  · exact chk_c6_1040 k h1040 (by omega)
  by_cases h1120 : k < 1200
  · exact chk_c6_1120 k h1120 (by omega)
  by_cases h1200 : k < 1280
  · exact chk_c6_1200 k h1200 (by omega)
  by_cases h1280 : k < 1360
  · exact chk_c6_1280 k h1280 (by omega)
  by_cases h1360 : k < 1440
  · exact chk_c6_1360 k h1360 (by omega)
  by_cases h1440 : k < 1520
  · exact chk_c6_1440 k h1440 (by omega)
  by_cases h1520 : k < 1600
  · exact chk_c6_1520 k h1520 (by omega)
  exact chk_c6_1600 k hk (by omega)
theorem tab_c_base : cL2 320 = 0 ∧ cU2 320 = 0 ∧ cL3 480 = 0 ∧ cU3 480 = 0 ∧ cL4 640 = 0 ∧
    cU4 640 = 0 ∧ cL5 800 = 0 ∧ cU5 800 = 0 := by decide +kernel

theorem TB_c1 (j : ℕ) (hj : 160 ≤ j) : TB (cR 1) 160 10000000000 cD cD j := by
  have : (1 : ℝ) ≤ (j : ℝ) / 160 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (show 1 * 160 ≤ j by omega)
  unfold TB cD; push_cast; rw [cR_one this]; norm_num

theorem TB_c_base (r : ℕ) (L U : ℕ → ℕ) (hL : L (160 * (r + 2)) = 0) (hU : U (160 * (r + 2)) = 0) :
    TB (cR (r + 2)) 160 10000000000 L U (160 * (r + 2)) := by
  have : ((160 * (r + 2) : ℕ) : ℝ) / (160 : ℕ) = (r : ℝ) + 2 := by push_cast; field_simp
  unfold TB; rw [this, cR_base, hL, hU]; simp

theorem cR_monoOn (r : ℕ) (c : ℝ) : MonotoneOn (cR r) (Ici c) := (cR_mono_nonneg r).1.monotoneOn _

theorem TB_c2 (k : ℕ) (h1 : 320 ≤ k) (h2 : k ≤ 1200) : TB (cR 2) 160 10000000000 cL2 cU2 k := by
  refine level_ind_const (f := cR 1) (Lf := cD) (Uf := cD) (N := 1200) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_ (fun j hj1 hj2 => TB_c1 j (by omega))
    (TB_c_base 0 cL2 cU2 tab_c_base.1 tab_c_base.2.1) (of_ball chk_c2) k h1 h2
  · intro a b ha hab; exact cR_delay 0 (by norm_num at ha ⊢; linarith) hab
  · intro x y hx hy; norm_num at hx hy; rw [cR_one hx.1, cR_one hy.1]

theorem TB_c3 (k : ℕ) (h1 : 480 ≤ k) (h2 : k ≤ 1320) : TB (cR 3) 160 10000000000 cL3 cU3 k := by
  refine level_ind (f := cR 2) (e := cR 1) (Lf := cL2) (Uf := cU2) (Le := cD) (Ue := cD) (N := 1320)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (cR_monoOn 2 _) (cR_monoOn 1 _)
    (fun j hj1 hj2 => TB_c2 j (by omega) (by omega))
    (fun i hi1 hi2 => ⟨TB_c1 i (by omega), TB_c1 (i + 1) (by omega)⟩)
    (TB_c_base 1 cL3 cU3 tab_c_base.2.2.1 tab_c_base.2.2.2.1) (of_ball chk_c3) k h1 h2
  · intro a b ha hab; exact cR_delay 1 (by norm_num at ha ⊢; linarith) hab
  · intro p x hp hpx; exact cR_delay 0 (by norm_num at hp ⊢; linarith) hpx

theorem TB_c4 (k : ℕ) (h1 : 640 ≤ k) (h2 : k ≤ 1480) : TB (cR 4) 160 10000000000 cL4 cU4 k := by
  refine level_ind (f := cR 3) (e := cR 2) (Lf := cL3) (Uf := cU3) (Le := cL2) (Ue := cU2) (N := 1480)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (cR_monoOn 3 _) (cR_monoOn 2 _)
    (fun j hj1 hj2 => TB_c3 j (by omega) (by omega))
    (fun i hi1 hi2 => ⟨TB_c2 i (by omega) (by omega), TB_c2 (i + 1) (by omega) (by omega)⟩)
    (TB_c_base 2 cL4 cU4 tab_c_base.2.2.2.2.1 tab_c_base.2.2.2.2.2.1) (of_ball chk_c4) k h1 h2
  · intro a b ha hab; exact cR_delay 2 (by norm_num at ha ⊢; linarith) hab
  · intro p x hp hpx; exact cR_delay 1 (by norm_num at hp ⊢; linarith) hpx

theorem TB_c5 (k : ℕ) (h1 : 800 ≤ k) (h2 : k ≤ 1640) : TB (cR 5) 160 10000000000 cL5 cU5 k := by
  refine level_ind (f := cR 4) (e := cR 3) (Lf := cL4) (Uf := cU4) (Le := cL3) (Ue := cU3) (N := 1640)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (cR_monoOn 4 _) (cR_monoOn 3 _)
    (fun j hj1 hj2 => TB_c4 j (by omega) (by omega))
    (fun i hi1 hi2 => ⟨TB_c3 i (by omega) (by omega), TB_c3 (i + 1) (by omega) (by omega)⟩)
    (TB_c_base 3 cL5 cU5 tab_c_base.2.2.2.2.2.2.1 tab_c_base.2.2.2.2.2.2.2) (of_ball chk_c5) k h1 h2
  · intro a b ha hab; exact cR_delay 3 (by norm_num at ha ⊢; linarith) hab
  · intro p x hp hpx; exact cR_delay 2 (by norm_num at hp ⊢; linarith) hpx

theorem TB_c6 (k : ℕ) (h1 : 960 ≤ k) (h2 : k ≤ 1640) : TB (cR 6) 160 10000000000 cL6 cU6 k := by
  refine level_ind (f := cR 5) (e := cR 4) (Lf := cL5) (Uf := cU5) (Le := cL4) (Ue := cU4) (N := 1640)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (cR_monoOn 5 _) (cR_monoOn 4 _)
    (fun j hj1 hj2 => TB_c5 j (by omega) (by omega))
    (fun i hi1 hi2 => ⟨TB_c4 i (by omega) (by omega), TB_c4 (i + 1) (by omega) (by omega)⟩)
    (TB_c_base 4 cL6 cU6 (by decide +kernel) (by decide +kernel)) (of_ball chk_c6) k h1 h2
  · intro a b ha hab; exact cR_delay 4 (by norm_num at ha ⊢; linarith) hab
  · intro p x hp hpx; exact cR_delay 3 (by norm_num at hp ⊢; linarith) hpx

end LeanLab.Akeno2026.SieveFns.Grid160
