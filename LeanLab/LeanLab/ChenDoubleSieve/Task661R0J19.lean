import LeanLab.ChenDoubleSieve.Task661R0J19Cert0
import LeanLab.ChenDoubleSieve.Task661R0J19Cert1
import LeanLab.ChenDoubleSieve.Task661R0J19Cert2
import LeanLab.ChenDoubleSieve.Task661R0J19Cert3
import LeanLab.ChenDoubleSieve.Task661R0J19Cert4
import LeanLab.ChenDoubleSieve.Task661R0J19Cert5
import LeanLab.ChenDoubleSieve.Task661R0J19Cert6
import LeanLab.ChenDoubleSieve.Task661R0J19Cert7
import LeanLab.ChenDoubleSieve.Task661R0J19Cert8
import LeanLab.ChenDoubleSieve.Task661R0J19Cert9
import LeanLab.ChenDoubleSieve.Task661R0J19Cert10
import LeanLab.ChenDoubleSieve.Task661R0J19Cert11
import LeanLab.ChenDoubleSieve.Task661R0J19Cert12
import LeanLab.ChenDoubleSieve.Task661R0J19Cert13

/-!
Exact ordered cell certificates for Wu 2004 page 26.
The parameters are Table 1 row 1 page 30.
The verifier comes from Prove2Me mission 1e48f99d, author kmehltretter82,
Apache 2.0, accepted proof LL_Decomp587l.r0j16_short.
AI wrote the new bridges, certificate generators and interval assemblies.
Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task661
open Wu04Functional Task587
open LeanLab.Ported.Prove2Me.R0J16.SolBuchstabR0J16

/-- The ordered cell certificates cover the complete compact phi interval. -/
theorem r0j19_certified {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) φ ≤
      ((70737 / 1000000000) : ℝ) := by
  have he0 : (7245824 : ℝ) / D_grid = 2 := by norm_num [D_grid]
  have het : (12680192 : ℝ) / D_grid = (7 / 2 : ℝ) := by norm_num [D_grid]
  have hlo0 : (7245824 : ℝ) / D_grid ≤ φ := by rw [he0]; exact hφ
  have htop : φ ≤ (12680192 : ℝ) / D_grid := by rw [het]; exact hφtop
  by_cases hc0 : φ ≤ (7415648 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7245824) (pb := 7415648) (t := j19Tree0) hlo0 hc0 j19Check0
  have hlo1 : (7415648 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc0).le
  by_cases hc1 : φ ≤ (7500560 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7415648) (pb := 7500560) (t := j19Tree1) hlo1 hc1 j19Check1
  have hlo2 : (7500560 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc1).le
  by_cases hc2 : φ ≤ (7543016 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7500560) (pb := 7543016) (t := j19Tree2) hlo2 hc2 j19Check2
  have hlo3 : (7543016 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc2).le
  by_cases hc3 : φ ≤ (7564244 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7543016) (pb := 7564244) (t := j19Tree3) hlo3 hc3 j19Check3
  have hlo4 : (7564244 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc3).le
  by_cases hc4 : φ ≤ (7585472 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7564244) (pb := 7585472) (t := j19Tree4) hlo4 hc4 j19Check4
  have hlo5 : (7585472 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc4).le
  by_cases hc5 : φ ≤ (7596086 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7585472) (pb := 7596086) (t := j19Tree5) hlo5 hc5 j19Check5
  have hlo6 : (7596086 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc5).le
  by_cases hc6 : φ ≤ (7606700 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7596086) (pb := 7606700) (t := j19Tree6) hlo6 hc6 j19Check6
  have hlo7 : (7606700 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc6).le
  by_cases hc7 : φ ≤ (7612007 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7606700) (pb := 7612007) (t := j19Tree7) hlo7 hc7 j19Check7
  have hlo8 : (7612007 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc7).le
  by_cases hc8 : φ ≤ (7617314 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7612007) (pb := 7617314) (t := j19Tree8) hlo8 hc8 j19Check8
  have hlo9 : (7617314 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc8).le
  by_cases hc9 : φ ≤ (7622621 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7617314) (pb := 7622621) (t := j19Tree9) hlo9 hc9 j19Check9
  have hlo10 : (7622621 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc9).le
  by_cases hc10 : φ ≤ (7625274 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7622621) (pb := 7625274) (t := j19Tree10) hlo10 hc10 j19Check10
  have hlo11 : (7625274 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc10).le
  by_cases hc11 : φ ≤ (7627928 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7625274) (pb := 7627928) (t := j19Tree11) hlo11 hc11 j19Check11
  have hlo12 : (7627928 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc11).le
  by_cases hc12 : φ ≤ (7630581 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7627928) (pb := 7630581) (t := j19Tree12) hlo12 hc12 j19Check12
  have hlo13 : (7630581 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc12).le
  by_cases hc13 : φ ≤ (7633235 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7630581) (pb := 7633235) (t := j19Tree13) hlo13 hc13 j19Check13
  have hlo14 : (7633235 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc13).le
  by_cases hc14 : φ ≤ (7634561 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7633235) (pb := 7634561) (t := j19Tree14) hlo14 hc14 j19Check14
  have hlo15 : (7634561 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc14).le
  by_cases hc15 : φ ≤ (7635888 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7634561) (pb := 7635888) (t := j19Tree15) hlo15 hc15 j19Check15
  have hlo16 : (7635888 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc15).le
  by_cases hc16 : φ ≤ (7637215 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7635888) (pb := 7637215) (t := j19Tree16) hlo16 hc16 j19Check16
  have hlo17 : (7637215 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc16).le
  by_cases hc17 : φ ≤ (7638542 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7637215) (pb := 7638542) (t := j19Tree17) hlo17 hc17 j19Check17
  have hlo18 : (7638542 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc17).le
  by_cases hc18 : φ ≤ (7639205 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7638542) (pb := 7639205) (t := j19Tree18) hlo18 hc18 j19Check18
  have hlo19 : (7639205 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc18).le
  by_cases hc19 : φ ≤ (7639868 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7639205) (pb := 7639868) (t := j19Tree19) hlo19 hc19 j19Check19
  have hlo20 : (7639868 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc19).le
  by_cases hc20 : φ ≤ (7640531 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7639868) (pb := 7640531) (t := j19Tree20) hlo20 hc20 j19Check20
  have hlo21 : (7640531 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc20).le
  by_cases hc21 : φ ≤ (7641195 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7640531) (pb := 7641195) (t := j19Tree21) hlo21 hc21 j19Check21
  have hlo22 : (7641195 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc21).le
  by_cases hc22 : φ ≤ (7641858 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7641195) (pb := 7641858) (t := j19Tree22) hlo22 hc22 j19Check22
  have hlo23 : (7641858 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc22).le
  by_cases hc23 : φ ≤ (7642522 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7641858) (pb := 7642522) (t := j19Tree23) hlo23 hc23 j19Check23
  have hlo24 : (7642522 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc23).le
  by_cases hc24 : φ ≤ (7643185 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7642522) (pb := 7643185) (t := j19Tree24) hlo24 hc24 j19Check24
  have hlo25 : (7643185 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc24).le
  by_cases hc25 : φ ≤ (7643517 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7643185) (pb := 7643517) (t := j19Tree25) hlo25 hc25 j19Check25
  have hlo26 : (7643517 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc25).le
  by_cases hc26 : φ ≤ (7643849 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7643517) (pb := 7643849) (t := j19Tree26) hlo26 hc26 j19Check26
  have hlo27 : (7643849 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc26).le
  by_cases hc27 : φ ≤ (7644180 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7643849) (pb := 7644180) (t := j19Tree27) hlo27 hc27 j19Check27
  have hlo28 : (7644180 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc27).le
  by_cases hc28 : φ ≤ (7644512 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7644180) (pb := 7644512) (t := j19Tree28) hlo28 hc28 j19Check28
  have hlo29 : (7644512 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc28).le
  by_cases hc29 : φ ≤ (7644843 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7644512) (pb := 7644843) (t := j19Tree29) hlo29 hc29 j19Check29
  have hlo30 : (7644843 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc29).le
  by_cases hc30 : φ ≤ (7645175 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7644843) (pb := 7645175) (t := j19Tree30) hlo30 hc30 j19Check30
  have hlo31 : (7645175 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc30).le
  by_cases hc31 : φ ≤ (7645506 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7645175) (pb := 7645506) (t := j19Tree31) hlo31 hc31 j19Check31
  have hlo32 : (7645506 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc31).le
  by_cases hc32 : φ ≤ (7645838 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7645506) (pb := 7645838) (t := j19Tree32) hlo32 hc32 j19Check32
  have hlo33 : (7645838 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc32).le
  by_cases hc33 : φ ≤ (7646170 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7645838) (pb := 7646170) (t := j19Tree33) hlo33 hc33 j19Check33
  have hlo34 : (7646170 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc33).le
  by_cases hc34 : φ ≤ (7646502 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7646170) (pb := 7646502) (t := j19Tree34) hlo34 hc34 j19Check34
  have hlo35 : (7646502 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc34).le
  by_cases hc35 : φ ≤ (7646833 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7646502) (pb := 7646833) (t := j19Tree35) hlo35 hc35 j19Check35
  have hlo36 : (7646833 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc35).le
  by_cases hc36 : φ ≤ (7647165 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7646833) (pb := 7647165) (t := j19Tree36) hlo36 hc36 j19Check36
  have hlo37 : (7647165 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc36).le
  by_cases hc37 : φ ≤ (7647497 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7647165) (pb := 7647497) (t := j19Tree37) hlo37 hc37 j19Check37
  have hlo38 : (7647497 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc37).le
  by_cases hc38 : φ ≤ (7647829 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7647497) (pb := 7647829) (t := j19Tree38) hlo38 hc38 j19Check38
  have hlo39 : (7647829 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc38).le
  by_cases hc39 : φ ≤ (7648160 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7647829) (pb := 7648160) (t := j19Tree39) hlo39 hc39 j19Check39
  have hlo40 : (7648160 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc39).le
  by_cases hc40 : φ ≤ (7648326 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7648160) (pb := 7648326) (t := j19Tree40) hlo40 hc40 j19Check40
  have hlo41 : (7648326 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc40).le
  by_cases hc41 : φ ≤ (7648492 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7648326) (pb := 7648492) (t := j19Tree41) hlo41 hc41 j19Check41
  have hlo42 : (7648492 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc41).le
  by_cases hc42 : φ ≤ (7648658 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7648492) (pb := 7648658) (t := j19Tree42) hlo42 hc42 j19Check42
  have hlo43 : (7648658 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc42).le
  by_cases hc43 : φ ≤ (7648824 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7648658) (pb := 7648824) (t := j19Tree43) hlo43 hc43 j19Check43
  have hlo44 : (7648824 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc43).le
  by_cases hc44 : φ ≤ (7648990 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7648824) (pb := 7648990) (t := j19Tree44) hlo44 hc44 j19Check44
  have hlo45 : (7648990 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc44).le
  by_cases hc45 : φ ≤ (7649156 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7648990) (pb := 7649156) (t := j19Tree45) hlo45 hc45 j19Check45
  have hlo46 : (7649156 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc45).le
  by_cases hc46 : φ ≤ (7649321 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7649156) (pb := 7649321) (t := j19Tree46) hlo46 hc46 j19Check46
  have hlo47 : (7649321 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc46).le
  by_cases hc47 : φ ≤ (7649487 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7649321) (pb := 7649487) (t := j19Tree47) hlo47 hc47 j19Check47
  have hlo48 : (7649487 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc47).le
  by_cases hc48 : φ ≤ (7649653 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7649487) (pb := 7649653) (t := j19Tree48) hlo48 hc48 j19Check48
  have hlo49 : (7649653 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc48).le
  by_cases hc49 : φ ≤ (7649819 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7649653) (pb := 7649819) (t := j19Tree49) hlo49 hc49 j19Check49
  have hlo50 : (7649819 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc49).le
  by_cases hc50 : φ ≤ (7649984 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7649819) (pb := 7649984) (t := j19Tree50) hlo50 hc50 j19Check50
  have hlo51 : (7649984 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc50).le
  by_cases hc51 : φ ≤ (7650150 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7649984) (pb := 7650150) (t := j19Tree51) hlo51 hc51 j19Check51
  have hlo52 : (7650150 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc51).le
  by_cases hc52 : φ ≤ (7650316 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7650150) (pb := 7650316) (t := j19Tree52) hlo52 hc52 j19Check52
  have hlo53 : (7650316 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc52).le
  by_cases hc53 : φ ≤ (7650482 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7650316) (pb := 7650482) (t := j19Tree53) hlo53 hc53 j19Check53
  have hlo54 : (7650482 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc53).le
  by_cases hc54 : φ ≤ (7650647 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7650482) (pb := 7650647) (t := j19Tree54) hlo54 hc54 j19Check54
  have hlo55 : (7650647 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc54).le
  by_cases hc55 : φ ≤ (7650813 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7650647) (pb := 7650813) (t := j19Tree55) hlo55 hc55 j19Check55
  have hlo56 : (7650813 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc55).le
  by_cases hc56 : φ ≤ (7650979 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7650813) (pb := 7650979) (t := j19Tree56) hlo56 hc56 j19Check56
  have hlo57 : (7650979 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc56).le
  by_cases hc57 : φ ≤ (7651145 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7650979) (pb := 7651145) (t := j19Tree57) hlo57 hc57 j19Check57
  have hlo58 : (7651145 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc57).le
  by_cases hc58 : φ ≤ (7651311 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7651145) (pb := 7651311) (t := j19Tree58) hlo58 hc58 j19Check58
  have hlo59 : (7651311 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc58).le
  by_cases hc59 : φ ≤ (7651477 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7651311) (pb := 7651477) (t := j19Tree59) hlo59 hc59 j19Check59
  have hlo60 : (7651477 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc59).le
  by_cases hc60 : φ ≤ (7651643 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7651477) (pb := 7651643) (t := j19Tree60) hlo60 hc60 j19Check60
  have hlo61 : (7651643 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc60).le
  by_cases hc61 : φ ≤ (7651809 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7651643) (pb := 7651809) (t := j19Tree61) hlo61 hc61 j19Check61
  have hlo62 : (7651809 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc61).le
  by_cases hc62 : φ ≤ (7651974 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7651809) (pb := 7651974) (t := j19Tree62) hlo62 hc62 j19Check62
  have hlo63 : (7651974 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc62).le
  by_cases hc63 : φ ≤ (7652140 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7651974) (pb := 7652140) (t := j19Tree63) hlo63 hc63 j19Check63
  have hlo64 : (7652140 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc63).le
  by_cases hc64 : φ ≤ (7652306 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7652140) (pb := 7652306) (t := j19Tree64) hlo64 hc64 j19Check64
  have hlo65 : (7652306 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc64).le
  by_cases hc65 : φ ≤ (7652472 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7652306) (pb := 7652472) (t := j19Tree65) hlo65 hc65 j19Check65
  have hlo66 : (7652472 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc65).le
  by_cases hc66 : φ ≤ (7652638 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7652472) (pb := 7652638) (t := j19Tree66) hlo66 hc66 j19Check66
  have hlo67 : (7652638 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc66).le
  by_cases hc67 : φ ≤ (7652804 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7652638) (pb := 7652804) (t := j19Tree67) hlo67 hc67 j19Check67
  have hlo68 : (7652804 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc67).le
  by_cases hc68 : φ ≤ (7652970 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7652804) (pb := 7652970) (t := j19Tree68) hlo68 hc68 j19Check68
  have hlo69 : (7652970 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc68).le
  by_cases hc69 : φ ≤ (7653136 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7652970) (pb := 7653136) (t := j19Tree69) hlo69 hc69 j19Check69
  have hlo70 : (7653136 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc69).le
  by_cases hc70 : φ ≤ (7653301 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7653136) (pb := 7653301) (t := j19Tree70) hlo70 hc70 j19Check70
  have hlo71 : (7653301 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc70).le
  by_cases hc71 : φ ≤ (7653467 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7653301) (pb := 7653467) (t := j19Tree71) hlo71 hc71 j19Check71
  have hlo72 : (7653467 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc71).le
  by_cases hc72 : φ ≤ (7653633 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7653467) (pb := 7653633) (t := j19Tree72) hlo72 hc72 j19Check72
  have hlo73 : (7653633 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc72).le
  by_cases hc73 : φ ≤ (7653799 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7653633) (pb := 7653799) (t := j19Tree73) hlo73 hc73 j19Check73
  have hlo74 : (7653799 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc73).le
  by_cases hc74 : φ ≤ (7653965 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7653799) (pb := 7653965) (t := j19Tree74) hlo74 hc74 j19Check74
  have hlo75 : (7653965 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc74).le
  by_cases hc75 : φ ≤ (7654131 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7653965) (pb := 7654131) (t := j19Tree75) hlo75 hc75 j19Check75
  have hlo76 : (7654131 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc75).le
  by_cases hc76 : φ ≤ (7654297 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7654131) (pb := 7654297) (t := j19Tree76) hlo76 hc76 j19Check76
  have hlo77 : (7654297 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc76).le
  by_cases hc77 : φ ≤ (7654463 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7654297) (pb := 7654463) (t := j19Tree77) hlo77 hc77 j19Check77
  have hlo78 : (7654463 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc77).le
  by_cases hc78 : φ ≤ (7654794 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7654463) (pb := 7654794) (t := j19Tree78) hlo78 hc78 j19Check78
  have hlo79 : (7654794 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc78).le
  by_cases hc79 : φ ≤ (7655126 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7654794) (pb := 7655126) (t := j19Tree79) hlo79 hc79 j19Check79
  have hlo80 : (7655126 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc79).le
  by_cases hc80 : φ ≤ (7655457 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7655126) (pb := 7655457) (t := j19Tree80) hlo80 hc80 j19Check80
  have hlo81 : (7655457 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc80).le
  by_cases hc81 : φ ≤ (7655789 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7655457) (pb := 7655789) (t := j19Tree81) hlo81 hc81 j19Check81
  have hlo82 : (7655789 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc81).le
  by_cases hc82 : φ ≤ (7656120 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7655789) (pb := 7656120) (t := j19Tree82) hlo82 hc82 j19Check82
  have hlo83 : (7656120 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc82).le
  by_cases hc83 : φ ≤ (7656452 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7656120) (pb := 7656452) (t := j19Tree83) hlo83 hc83 j19Check83
  have hlo84 : (7656452 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc83).le
  by_cases hc84 : φ ≤ (7656784 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7656452) (pb := 7656784) (t := j19Tree84) hlo84 hc84 j19Check84
  have hlo85 : (7656784 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc84).le
  by_cases hc85 : φ ≤ (7657116 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7656784) (pb := 7657116) (t := j19Tree85) hlo85 hc85 j19Check85
  have hlo86 : (7657116 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc85).le
  by_cases hc86 : φ ≤ (7657447 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7657116) (pb := 7657447) (t := j19Tree86) hlo86 hc86 j19Check86
  have hlo87 : (7657447 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc86).le
  by_cases hc87 : φ ≤ (7657779 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7657447) (pb := 7657779) (t := j19Tree87) hlo87 hc87 j19Check87
  have hlo88 : (7657779 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc87).le
  by_cases hc88 : φ ≤ (7658111 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7657779) (pb := 7658111) (t := j19Tree88) hlo88 hc88 j19Check88
  have hlo89 : (7658111 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc88).le
  by_cases hc89 : φ ≤ (7658443 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7658111) (pb := 7658443) (t := j19Tree89) hlo89 hc89 j19Check89
  have hlo90 : (7658443 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc89).le
  by_cases hc90 : φ ≤ (7659106 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7658443) (pb := 7659106) (t := j19Tree90) hlo90 hc90 j19Check90
  have hlo91 : (7659106 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc90).le
  by_cases hc91 : φ ≤ (7659770 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7659106) (pb := 7659770) (t := j19Tree91) hlo91 hc91 j19Check91
  have hlo92 : (7659770 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc91).le
  by_cases hc92 : φ ≤ (7660433 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7659770) (pb := 7660433) (t := j19Tree92) hlo92 hc92 j19Check92
  have hlo93 : (7660433 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc92).le
  by_cases hc93 : φ ≤ (7661096 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7660433) (pb := 7661096) (t := j19Tree93) hlo93 hc93 j19Check93
  have hlo94 : (7661096 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc93).le
  by_cases hc94 : φ ≤ (7661759 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7661096) (pb := 7661759) (t := j19Tree94) hlo94 hc94 j19Check94
  have hlo95 : (7661759 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc94).le
  by_cases hc95 : φ ≤ (7662423 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7661759) (pb := 7662423) (t := j19Tree95) hlo95 hc95 j19Check95
  have hlo96 : (7662423 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc95).le
  by_cases hc96 : φ ≤ (7663750 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7662423) (pb := 7663750) (t := j19Tree96) hlo96 hc96 j19Check96
  have hlo97 : (7663750 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc96).le
  by_cases hc97 : φ ≤ (7665077 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7663750) (pb := 7665077) (t := j19Tree97) hlo97 hc97 j19Check97
  have hlo98 : (7665077 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc97).le
  by_cases hc98 : φ ≤ (7666403 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7665077) (pb := 7666403) (t := j19Tree98) hlo98 hc98 j19Check98
  have hlo99 : (7666403 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc98).le
  by_cases hc99 : φ ≤ (7667730 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7666403) (pb := 7667730) (t := j19Tree99) hlo99 hc99 j19Check99
  have hlo100 : (7667730 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc99).le
  by_cases hc100 : φ ≤ (7670384 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7667730) (pb := 7670384) (t := j19Tree100) hlo100 hc100 j19Check100
  have hlo101 : (7670384 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc100).le
  by_cases hc101 : φ ≤ (7673037 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7670384) (pb := 7673037) (t := j19Tree101) hlo101 hc101 j19Check101
  have hlo102 : (7673037 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc101).le
  by_cases hc102 : φ ≤ (7675691 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7673037) (pb := 7675691) (t := j19Tree102) hlo102 hc102 j19Check102
  have hlo103 : (7675691 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc102).le
  by_cases hc103 : φ ≤ (7680998 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7675691) (pb := 7680998) (t := j19Tree103) hlo103 hc103 j19Check103
  have hlo104 : (7680998 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc103).le
  by_cases hc104 : φ ≤ (7691612 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7680998) (pb := 7691612) (t := j19Tree104) hlo104 hc104 j19Check104
  have hlo105 : (7691612 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc104).le
  by_cases hc105 : φ ≤ (7712840 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7691612) (pb := 7712840) (t := j19Tree105) hlo105 hc105 j19Check105
  have hlo106 : (7712840 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc105).le
  by_cases hc106 : φ ≤ (7755296 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7712840) (pb := 7755296) (t := j19Tree106) hlo106 hc106 j19Check106
  have hlo107 : (7755296 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc106).le
  by_cases hc107 : φ ≤ (7925120 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7755296) (pb := 7925120) (t := j19Tree107) hlo107 hc107 j19Check107
  have hlo108 : (7925120 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc107).le
  by_cases hc108 : φ ≤ (8604416 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 7925120) (pb := 8604416) (t := j19Tree108) hlo108 hc108 j19Check108
  have hlo109 : (8604416 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc108).le
  by_cases hc109 : φ ≤ (9963008 : ℝ) / D_grid
  · exact j19_interval_bound hω hz (pa := 8604416) (pb := 9963008) (t := j19Tree109) hlo109 hc109 j19Check109
  have hlo110 : (9963008 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc109).le
  exact j19_interval_bound hω hz (pa := 9963008) (pb := 12680192) (t := j19Tree110) hlo110 htop j19Check110

end LeanLab.ChenDoubleSieve.Task661

