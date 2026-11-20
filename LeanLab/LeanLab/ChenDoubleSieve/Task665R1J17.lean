import LeanLab.ChenDoubleSieve.Task665R1J17Cert0
import LeanLab.ChenDoubleSieve.Task665R1J17Cert1
import LeanLab.ChenDoubleSieve.Task665R1J17Cert2
import LeanLab.ChenDoubleSieve.Task665R1J17Cert3
import LeanLab.ChenDoubleSieve.Task665R1J17Cert4
import LeanLab.ChenDoubleSieve.Task665R1J17Cert5
import LeanLab.ChenDoubleSieve.Task665R1J17Cert6
import LeanLab.ChenDoubleSieve.Task665R1J17Cert7

/-!
Exact row two D2,17 certificate data for Wu 2004 page 26.
The parameters are Table 1 row two page 30.
The unchanged verifier is the Prove2Me R1J16 port, mission 87d77bf0.
The existing accepted theorem is LL_Decomp587j.r1j16_short.
Author kmehltretter82. Apache 2.0. Accepted 2026-11-19.
AI generated these independent trees and wrote the Lean assembly.
Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace LeanLab.ChenDoubleSieve.Task665R1
open LeanLab.Ported.Prove2Me.Decomp587jR1J16.SolBuchstabR1J16

open Real Set MeasureTheory Wu04Functional Task587

/-- The interval certificates prove the complete row two compact D2,17 bound. -/
theorem r1j17_certified {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r1j17_lo j : ℝ)) (fun j => (r1j17_hi j : ℝ)) φ ≤
      ((92979 / 1000000000) : ℝ) := by
  have he0 : (1990656 : ℝ) / D_grid = 2 := by norm_num [D_grid]
  have het : (3483648 : ℝ) / D_grid = (7 / 2 : ℝ) := by norm_num [D_grid]
  have hlo0 : (1990656 : ℝ) / D_grid ≤ φ := by rw [he0]; exact hφ
  have htop : φ ≤ (3483648 : ℝ) / D_grid := by rw [het]; exact hφtop
  by_cases hc0 : φ ≤ (1996488 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 1990656) (pb := 1996488) (t := j17Tree0) hlo0 hc0 j17Check0
  have hlo1 : (1996488 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc0).le
  by_cases hc1 : φ ≤ (2002320 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 1996488) (pb := 2002320) (t := j17Tree1) hlo1 hc1 j17Check1
  have hlo2 : (2002320 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc1).le
  by_cases hc2 : φ ≤ (2005236 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2002320) (pb := 2005236) (t := j17Tree2) hlo2 hc2 j17Check2
  have hlo3 : (2005236 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc2).le
  by_cases hc3 : φ ≤ (2008152 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2005236) (pb := 2008152) (t := j17Tree3) hlo3 hc3 j17Check3
  have hlo4 : (2008152 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc3).le
  by_cases hc4 : φ ≤ (2011068 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2008152) (pb := 2011068) (t := j17Tree4) hlo4 hc4 j17Check4
  have hlo5 : (2011068 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc4).le
  by_cases hc5 : φ ≤ (2012526 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2011068) (pb := 2012526) (t := j17Tree5) hlo5 hc5 j17Check5
  have hlo6 : (2012526 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc5).le
  by_cases hc6 : φ ≤ (2013984 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2012526) (pb := 2013984) (t := j17Tree6) hlo6 hc6 j17Check6
  have hlo7 : (2013984 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc6).le
  by_cases hc7 : φ ≤ (2014713 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2013984) (pb := 2014713) (t := j17Tree7) hlo7 hc7 j17Check7
  have hlo8 : (2014713 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc7).le
  by_cases hc8 : φ ≤ (2015442 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2014713) (pb := 2015442) (t := j17Tree8) hlo8 hc8 j17Check8
  have hlo9 : (2015442 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc8).le
  by_cases hc9 : φ ≤ (2016171 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2015442) (pb := 2016171) (t := j17Tree9) hlo9 hc9 j17Check9
  have hlo10 : (2016171 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc9).le
  by_cases hc10 : φ ≤ (2016900 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2016171) (pb := 2016900) (t := j17Tree10) hlo10 hc10 j17Check10
  have hlo11 : (2016900 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc10).le
  by_cases hc11 : φ ≤ (2017264 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2016900) (pb := 2017264) (t := j17Tree11) hlo11 hc11 j17Check11
  have hlo12 : (2017264 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc11).le
  by_cases hc12 : φ ≤ (2017629 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2017264) (pb := 2017629) (t := j17Tree12) hlo12 hc12 j17Check12
  have hlo13 : (2017629 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc12).le
  by_cases hc13 : φ ≤ (2017993 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2017629) (pb := 2017993) (t := j17Tree13) hlo13 hc13 j17Check13
  have hlo14 : (2017993 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc13).le
  by_cases hc14 : φ ≤ (2018358 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2017993) (pb := 2018358) (t := j17Tree14) hlo14 hc14 j17Check14
  have hlo15 : (2018358 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc14).le
  by_cases hc15 : φ ≤ (2018722 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2018358) (pb := 2018722) (t := j17Tree15) hlo15 hc15 j17Check15
  have hlo16 : (2018722 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc15).le
  by_cases hc16 : φ ≤ (2018904 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2018722) (pb := 2018904) (t := j17Tree16) hlo16 hc16 j17Check16
  have hlo17 : (2018904 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc16).le
  by_cases hc17 : φ ≤ (2019087 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2018904) (pb := 2019087) (t := j17Tree17) hlo17 hc17 j17Check17
  have hlo18 : (2019087 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc17).le
  by_cases hc18 : φ ≤ (2019269 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2019087) (pb := 2019269) (t := j17Tree18) hlo18 hc18 j17Check18
  have hlo19 : (2019269 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc18).le
  by_cases hc19 : φ ≤ (2019451 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2019269) (pb := 2019451) (t := j17Tree19) hlo19 hc19 j17Check19
  have hlo20 : (2019451 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc19).le
  by_cases hc20 : φ ≤ (2019633 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2019451) (pb := 2019633) (t := j17Tree20) hlo20 hc20 j17Check20
  have hlo21 : (2019633 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc20).le
  by_cases hc21 : φ ≤ (2019816 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2019633) (pb := 2019816) (t := j17Tree21) hlo21 hc21 j17Check21
  have hlo22 : (2019816 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc21).le
  by_cases hc22 : φ ≤ (2019998 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2019816) (pb := 2019998) (t := j17Tree22) hlo22 hc22 j17Check22
  have hlo23 : (2019998 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc22).le
  by_cases hc23 : φ ≤ (2020180 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2019998) (pb := 2020180) (t := j17Tree23) hlo23 hc23 j17Check23
  have hlo24 : (2020180 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc23).le
  by_cases hc24 : φ ≤ (2020362 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2020180) (pb := 2020362) (t := j17Tree24) hlo24 hc24 j17Check24
  have hlo25 : (2020362 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc24).le
  by_cases hc25 : φ ≤ (2020545 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2020362) (pb := 2020545) (t := j17Tree25) hlo25 hc25 j17Check25
  have hlo26 : (2020545 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc25).le
  by_cases hc26 : φ ≤ (2020727 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2020545) (pb := 2020727) (t := j17Tree26) hlo26 hc26 j17Check26
  have hlo27 : (2020727 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc26).le
  by_cases hc27 : φ ≤ (2020909 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2020727) (pb := 2020909) (t := j17Tree27) hlo27 hc27 j17Check27
  have hlo28 : (2020909 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc27).le
  by_cases hc28 : φ ≤ (2021091 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2020909) (pb := 2021091) (t := j17Tree28) hlo28 hc28 j17Check28
  have hlo29 : (2021091 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc28).le
  by_cases hc29 : φ ≤ (2021274 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2021091) (pb := 2021274) (t := j17Tree29) hlo29 hc29 j17Check29
  have hlo30 : (2021274 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc29).le
  by_cases hc30 : φ ≤ (2021456 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2021274) (pb := 2021456) (t := j17Tree30) hlo30 hc30 j17Check30
  have hlo31 : (2021456 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc30).le
  by_cases hc31 : φ ≤ (2021638 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2021456) (pb := 2021638) (t := j17Tree31) hlo31 hc31 j17Check31
  have hlo32 : (2021638 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc31).le
  by_cases hc32 : φ ≤ (2021820 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2021638) (pb := 2021820) (t := j17Tree32) hlo32 hc32 j17Check32
  have hlo33 : (2021820 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc32).le
  by_cases hc33 : φ ≤ (2022003 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2021820) (pb := 2022003) (t := j17Tree33) hlo33 hc33 j17Check33
  have hlo34 : (2022003 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc33).le
  by_cases hc34 : φ ≤ (2022185 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2022003) (pb := 2022185) (t := j17Tree34) hlo34 hc34 j17Check34
  have hlo35 : (2022185 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc34).le
  by_cases hc35 : φ ≤ (2022367 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2022185) (pb := 2022367) (t := j17Tree35) hlo35 hc35 j17Check35
  have hlo36 : (2022367 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc35).le
  by_cases hc36 : φ ≤ (2022549 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2022367) (pb := 2022549) (t := j17Tree36) hlo36 hc36 j17Check36
  have hlo37 : (2022549 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc36).le
  by_cases hc37 : φ ≤ (2022732 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2022549) (pb := 2022732) (t := j17Tree37) hlo37 hc37 j17Check37
  have hlo38 : (2022732 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc37).le
  by_cases hc38 : φ ≤ (2022914 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2022732) (pb := 2022914) (t := j17Tree38) hlo38 hc38 j17Check38
  have hlo39 : (2022914 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc38).le
  by_cases hc39 : φ ≤ (2023096 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2022914) (pb := 2023096) (t := j17Tree39) hlo39 hc39 j17Check39
  have hlo40 : (2023096 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc39).le
  by_cases hc40 : φ ≤ (2023278 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2023096) (pb := 2023278) (t := j17Tree40) hlo40 hc40 j17Check40
  have hlo41 : (2023278 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc40).le
  by_cases hc41 : φ ≤ (2023461 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2023278) (pb := 2023461) (t := j17Tree41) hlo41 hc41 j17Check41
  have hlo42 : (2023461 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc41).le
  by_cases hc42 : φ ≤ (2023643 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2023461) (pb := 2023643) (t := j17Tree42) hlo42 hc42 j17Check42
  have hlo43 : (2023643 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc42).le
  by_cases hc43 : φ ≤ (2023825 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2023643) (pb := 2023825) (t := j17Tree43) hlo43 hc43 j17Check43
  have hlo44 : (2023825 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc43).le
  by_cases hc44 : φ ≤ (2024190 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2023825) (pb := 2024190) (t := j17Tree44) hlo44 hc44 j17Check44
  have hlo45 : (2024190 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc44).le
  by_cases hc45 : φ ≤ (2024554 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2024190) (pb := 2024554) (t := j17Tree45) hlo45 hc45 j17Check45
  have hlo46 : (2024554 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc45).le
  by_cases hc46 : φ ≤ (2024919 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2024554) (pb := 2024919) (t := j17Tree46) hlo46 hc46 j17Check46
  have hlo47 : (2024919 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc46).le
  by_cases hc47 : φ ≤ (2025283 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2024919) (pb := 2025283) (t := j17Tree47) hlo47 hc47 j17Check47
  have hlo48 : (2025283 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc47).le
  by_cases hc48 : φ ≤ (2025648 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2025283) (pb := 2025648) (t := j17Tree48) hlo48 hc48 j17Check48
  have hlo49 : (2025648 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc48).le
  by_cases hc49 : φ ≤ (2026377 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2025648) (pb := 2026377) (t := j17Tree49) hlo49 hc49 j17Check49
  have hlo50 : (2026377 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc49).le
  by_cases hc50 : φ ≤ (2027106 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2026377) (pb := 2027106) (t := j17Tree50) hlo50 hc50 j17Check50
  have hlo51 : (2027106 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc50).le
  by_cases hc51 : φ ≤ (2027835 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2027106) (pb := 2027835) (t := j17Tree51) hlo51 hc51 j17Check51
  have hlo52 : (2027835 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc51).le
  by_cases hc52 : φ ≤ (2028564 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2027835) (pb := 2028564) (t := j17Tree52) hlo52 hc52 j17Check52
  have hlo53 : (2028564 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc52).le
  by_cases hc53 : φ ≤ (2030022 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2028564) (pb := 2030022) (t := j17Tree53) hlo53 hc53 j17Check53
  have hlo54 : (2030022 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc53).le
  by_cases hc54 : φ ≤ (2031480 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2030022) (pb := 2031480) (t := j17Tree54) hlo54 hc54 j17Check54
  have hlo55 : (2031480 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc54).le
  by_cases hc55 : φ ≤ (2034396 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2031480) (pb := 2034396) (t := j17Tree55) hlo55 hc55 j17Check55
  have hlo56 : (2034396 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc55).le
  by_cases hc56 : φ ≤ (2037312 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2034396) (pb := 2037312) (t := j17Tree56) hlo56 hc56 j17Check56
  have hlo57 : (2037312 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc56).le
  by_cases hc57 : φ ≤ (2083968 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2037312) (pb := 2083968) (t := j17Tree57) hlo57 hc57 j17Check57
  have hlo58 : (2083968 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc57).le
  by_cases hc58 : φ ≤ (2177280 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2083968) (pb := 2177280) (t := j17Tree58) hlo58 hc58 j17Check58
  have hlo59 : (2177280 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc58).le
  by_cases hc59 : φ ≤ (2363904 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2177280) (pb := 2363904) (t := j17Tree59) hlo59 hc59 j17Check59
  have hlo60 : (2363904 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc59).le
  by_cases hc60 : φ ≤ (2737152 : ℝ) / D_grid
  · exact j17_interval_bound hω hz (pa := 2363904) (pb := 2737152) (t := j17Tree60) hlo60 hc60 j17Check60
  have hlo61 : (2737152 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc60).le
  exact j17_interval_bound hω hz (pa := 2737152) (pb := 3483648) (t := j17Tree61) hlo61 htop j17Check61

end LeanLab.ChenDoubleSieve.Task665R1
#print axioms LeanLab.ChenDoubleSieve.Task665R1.r1j17_certified
