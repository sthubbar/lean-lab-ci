import LeanLab.ChenDoubleSieve.Task661R0J17Cert0
import LeanLab.ChenDoubleSieve.Task661R0J17Cert1
import LeanLab.ChenDoubleSieve.Task661R0J17Cert2
import LeanLab.ChenDoubleSieve.Task661R0J17Cert3
import LeanLab.ChenDoubleSieve.Task661R0J17Cert4
import LeanLab.ChenDoubleSieve.Task661R0J17Cert5
import LeanLab.ChenDoubleSieve.Task661R0J17Cert6
import LeanLab.ChenDoubleSieve.Task661R0J17Cert7
import LeanLab.ChenDoubleSieve.Task661R0J17Cert8
import LeanLab.ChenDoubleSieve.Task661R0J17Cert9

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
theorem r0j17_certified {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) := by
  have he0 : (7245824 : ℝ) / D_grid = 2 := by norm_num [D_grid]
  have het : (12680192 : ℝ) / D_grid = (7 / 2 : ℝ) := by norm_num [D_grid]
  have hlo0 : (7245824 : ℝ) / D_grid ≤ φ := by rw [he0]; exact hφ
  have htop : φ ≤ (12680192 : ℝ) / D_grid := by rw [het]; exact hφtop
  by_cases hc0 : φ ≤ (7288280 : ℝ) / D_grid
  · exact j17Bound0 hω hz hlo0 hc0
  have hlo1 : (7288280 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc0).le
  by_cases hc1 : φ ≤ (7309508 : ℝ) / D_grid
  · exact j17Bound1 hω hz hlo1 hc1
  have hlo2 : (7309508 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc1).le
  by_cases hc2 : φ ≤ (7320122 : ℝ) / D_grid
  · exact j17Bound2 hω hz hlo2 hc2
  have hlo3 : (7320122 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc2).le
  by_cases hc3 : φ ≤ (7325429 : ℝ) / D_grid
  · exact j17Bound3 hω hz hlo3 hc3
  have hlo4 : (7325429 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc3).le
  by_cases hc4 : φ ≤ (7330736 : ℝ) / D_grid
  · exact j17Bound4 hω hz hlo4 hc4
  have hlo5 : (7330736 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc4).le
  by_cases hc5 : φ ≤ (7336043 : ℝ) / D_grid
  · exact j17Bound5 hω hz hlo5 hc5
  have hlo6 : (7336043 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc5).le
  by_cases hc6 : φ ≤ (7341350 : ℝ) / D_grid
  · exact j17Bound6 hω hz hlo6 hc6
  have hlo7 : (7341350 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc6).le
  by_cases hc7 : φ ≤ (7344003 : ℝ) / D_grid
  · exact j17Bound7 hω hz hlo7 hc7
  have hlo8 : (7344003 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc7).le
  by_cases hc8 : φ ≤ (7346657 : ℝ) / D_grid
  · exact j17Bound8 hω hz hlo8 hc8
  have hlo9 : (7346657 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc8).le
  by_cases hc9 : φ ≤ (7349310 : ℝ) / D_grid
  · exact j17Bound9 hω hz hlo9 hc9
  have hlo10 : (7349310 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc9).le
  by_cases hc10 : φ ≤ (7350637 : ℝ) / D_grid
  · exact j17Bound10 hω hz hlo10 hc10
  have hlo11 : (7350637 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc10).le
  by_cases hc11 : φ ≤ (7351964 : ℝ) / D_grid
  · exact j17Bound11 hω hz hlo11 hc11
  have hlo12 : (7351964 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc11).le
  by_cases hc12 : φ ≤ (7353290 : ℝ) / D_grid
  · exact j17Bound12 hω hz hlo12 hc12
  have hlo13 : (7353290 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc12).le
  by_cases hc13 : φ ≤ (7354617 : ℝ) / D_grid
  · exact j17Bound13 hω hz hlo13 hc13
  have hlo14 : (7354617 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc13).le
  by_cases hc14 : φ ≤ (7355944 : ℝ) / D_grid
  · exact j17Bound14 hω hz hlo14 hc14
  have hlo15 : (7355944 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc14).le
  by_cases hc15 : φ ≤ (7357271 : ℝ) / D_grid
  · exact j17Bound15 hω hz hlo15 hc15
  have hlo16 : (7357271 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc15).le
  by_cases hc16 : φ ≤ (7358597 : ℝ) / D_grid
  · exact j17Bound16 hω hz hlo16 hc16
  have hlo17 : (7358597 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc16).le
  by_cases hc17 : φ ≤ (7359260 : ℝ) / D_grid
  · exact j17Bound17 hω hz hlo17 hc17
  have hlo18 : (7359260 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc17).le
  by_cases hc18 : φ ≤ (7359924 : ℝ) / D_grid
  · exact j17Bound18 hω hz hlo18 hc18
  have hlo19 : (7359924 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc18).le
  by_cases hc19 : φ ≤ (7360587 : ℝ) / D_grid
  · exact j17Bound19 hω hz hlo19 hc19
  have hlo20 : (7360587 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc19).le
  by_cases hc20 : φ ≤ (7361251 : ℝ) / D_grid
  · exact j17Bound20 hω hz hlo20 hc20
  have hlo21 : (7361251 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc20).le
  by_cases hc21 : φ ≤ (7361914 : ℝ) / D_grid
  · exact j17Bound21 hω hz hlo21 hc21
  have hlo22 : (7361914 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc21).le
  by_cases hc22 : φ ≤ (7362578 : ℝ) / D_grid
  · exact j17Bound22 hω hz hlo22 hc22
  have hlo23 : (7362578 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc22).le
  by_cases hc23 : φ ≤ (7363241 : ℝ) / D_grid
  · exact j17Bound23 hω hz hlo23 hc23
  have hlo24 : (7363241 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc23).le
  by_cases hc24 : φ ≤ (7363904 : ℝ) / D_grid
  · exact j17Bound24 hω hz hlo24 hc24
  have hlo25 : (7363904 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc24).le
  by_cases hc25 : φ ≤ (7364567 : ℝ) / D_grid
  · exact j17Bound25 hω hz hlo25 hc25
  have hlo26 : (7364567 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc25).le
  by_cases hc26 : φ ≤ (7365231 : ℝ) / D_grid
  · exact j17Bound26 hω hz hlo26 hc26
  have hlo27 : (7365231 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc26).le
  by_cases hc27 : φ ≤ (7365894 : ℝ) / D_grid
  · exact j17Bound27 hω hz hlo27 hc27
  have hlo28 : (7365894 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc27).le
  by_cases hc28 : φ ≤ (7366226 : ℝ) / D_grid
  · exact j17Bound28 hω hz hlo28 hc28
  have hlo29 : (7366226 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc28).le
  by_cases hc29 : φ ≤ (7366558 : ℝ) / D_grid
  · exact j17Bound29 hω hz hlo29 hc29
  have hlo30 : (7366558 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc29).le
  by_cases hc30 : φ ≤ (7366889 : ℝ) / D_grid
  · exact j17Bound30 hω hz hlo30 hc30
  have hlo31 : (7366889 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc30).le
  by_cases hc31 : φ ≤ (7367221 : ℝ) / D_grid
  · exact j17Bound31 hω hz hlo31 hc31
  have hlo32 : (7367221 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc31).le
  by_cases hc32 : φ ≤ (7367553 : ℝ) / D_grid
  · exact j17Bound32 hω hz hlo32 hc32
  have hlo33 : (7367553 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc32).le
  by_cases hc33 : φ ≤ (7367885 : ℝ) / D_grid
  · exact j17Bound33 hω hz hlo33 hc33
  have hlo34 : (7367885 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc33).le
  by_cases hc34 : φ ≤ (7368216 : ℝ) / D_grid
  · exact j17Bound34 hω hz hlo34 hc34
  have hlo35 : (7368216 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc34).le
  by_cases hc35 : φ ≤ (7368548 : ℝ) / D_grid
  · exact j17Bound35 hω hz hlo35 hc35
  have hlo36 : (7368548 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc35).le
  by_cases hc36 : φ ≤ (7368879 : ℝ) / D_grid
  · exact j17Bound36 hω hz hlo36 hc36
  have hlo37 : (7368879 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc36).le
  by_cases hc37 : φ ≤ (7369211 : ℝ) / D_grid
  · exact j17Bound37 hω hz hlo37 hc37
  have hlo38 : (7369211 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc37).le
  by_cases hc38 : φ ≤ (7369542 : ℝ) / D_grid
  · exact j17Bound38 hω hz hlo38 hc38
  have hlo39 : (7369542 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc38).le
  by_cases hc39 : φ ≤ (7369874 : ℝ) / D_grid
  · exact j17Bound39 hω hz hlo39 hc39
  have hlo40 : (7369874 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc39).le
  by_cases hc40 : φ ≤ (7370206 : ℝ) / D_grid
  · exact j17Bound40 hω hz hlo40 hc40
  have hlo41 : (7370206 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc40).le
  by_cases hc41 : φ ≤ (7370538 : ℝ) / D_grid
  · exact j17Bound41 hω hz hlo41 hc41
  have hlo42 : (7370538 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc41).le
  by_cases hc42 : φ ≤ (7370869 : ℝ) / D_grid
  · exact j17Bound42 hω hz hlo42 hc42
  have hlo43 : (7370869 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc42).le
  by_cases hc43 : φ ≤ (7371201 : ℝ) / D_grid
  · exact j17Bound43 hω hz hlo43 hc43
  have hlo44 : (7371201 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc43).le
  by_cases hc44 : φ ≤ (7371533 : ℝ) / D_grid
  · exact j17Bound44 hω hz hlo44 hc44
  have hlo45 : (7371533 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc44).le
  by_cases hc45 : φ ≤ (7371865 : ℝ) / D_grid
  · exact j17Bound45 hω hz hlo45 hc45
  have hlo46 : (7371865 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc45).le
  by_cases hc46 : φ ≤ (7372196 : ℝ) / D_grid
  · exact j17Bound46 hω hz hlo46 hc46
  have hlo47 : (7372196 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc46).le
  by_cases hc47 : φ ≤ (7372528 : ℝ) / D_grid
  · exact j17Bound47 hω hz hlo47 hc47
  have hlo48 : (7372528 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc47).le
  by_cases hc48 : φ ≤ (7372860 : ℝ) / D_grid
  · exact j17Bound48 hω hz hlo48 hc48
  have hlo49 : (7372860 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc48).le
  by_cases hc49 : φ ≤ (7373192 : ℝ) / D_grid
  · exact j17Bound49 hω hz hlo49 hc49
  have hlo50 : (7373192 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc49).le
  by_cases hc50 : φ ≤ (7373523 : ℝ) / D_grid
  · exact j17Bound50 hω hz hlo50 hc50
  have hlo51 : (7373523 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc50).le
  by_cases hc51 : φ ≤ (7373855 : ℝ) / D_grid
  · exact j17Bound51 hω hz hlo51 hc51
  have hlo52 : (7373855 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc51).le
  by_cases hc52 : φ ≤ (7374518 : ℝ) / D_grid
  · exact j17Bound52 hω hz hlo52 hc52
  have hlo53 : (7374518 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc52).le
  by_cases hc53 : φ ≤ (7375181 : ℝ) / D_grid
  · exact j17Bound53 hω hz hlo53 hc53
  have hlo54 : (7375181 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc53).le
  by_cases hc54 : φ ≤ (7375845 : ℝ) / D_grid
  · exact j17Bound54 hω hz hlo54 hc54
  have hlo55 : (7375845 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc54).le
  by_cases hc55 : φ ≤ (7376508 : ℝ) / D_grid
  · exact j17Bound55 hω hz hlo55 hc55
  have hlo56 : (7376508 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc55).le
  by_cases hc56 : φ ≤ (7377172 : ℝ) / D_grid
  · exact j17Bound56 hω hz hlo56 hc56
  have hlo57 : (7377172 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc56).le
  by_cases hc57 : φ ≤ (7377835 : ℝ) / D_grid
  · exact j17Bound57 hω hz hlo57 hc57
  have hlo58 : (7377835 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc57).le
  by_cases hc58 : φ ≤ (7378499 : ℝ) / D_grid
  · exact j17Bound58 hω hz hlo58 hc58
  have hlo59 : (7378499 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc58).le
  by_cases hc59 : φ ≤ (7379162 : ℝ) / D_grid
  · exact j17Bound59 hω hz hlo59 hc59
  have hlo60 : (7379162 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc59).le
  by_cases hc60 : φ ≤ (7379825 : ℝ) / D_grid
  · exact j17Bound60 hω hz hlo60 hc60
  have hlo61 : (7379825 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc60).le
  by_cases hc61 : φ ≤ (7381152 : ℝ) / D_grid
  · exact j17Bound61 hω hz hlo61 hc61
  have hlo62 : (7381152 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc61).le
  by_cases hc62 : φ ≤ (7382479 : ℝ) / D_grid
  · exact j17Bound62 hω hz hlo62 hc62
  have hlo63 : (7382479 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc62).le
  by_cases hc63 : φ ≤ (7383806 : ℝ) / D_grid
  · exact j17Bound63 hω hz hlo63 hc63
  have hlo64 : (7383806 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc63).le
  by_cases hc64 : φ ≤ (7385132 : ℝ) / D_grid
  · exact j17Bound64 hω hz hlo64 hc64
  have hlo65 : (7385132 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc64).le
  by_cases hc65 : φ ≤ (7386459 : ℝ) / D_grid
  · exact j17Bound65 hω hz hlo65 hc65
  have hlo66 : (7386459 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc65).le
  by_cases hc66 : φ ≤ (7389113 : ℝ) / D_grid
  · exact j17Bound66 hω hz hlo66 hc66
  have hlo67 : (7389113 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc66).le
  by_cases hc67 : φ ≤ (7391766 : ℝ) / D_grid
  · exact j17Bound67 hω hz hlo67 hc67
  have hlo68 : (7391766 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc67).le
  by_cases hc68 : φ ≤ (7394420 : ℝ) / D_grid
  · exact j17Bound68 hω hz hlo68 hc68
  have hlo69 : (7394420 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc68).le
  by_cases hc69 : φ ≤ (7399727 : ℝ) / D_grid
  · exact j17Bound69 hω hz hlo69 hc69
  have hlo70 : (7399727 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc69).le
  by_cases hc70 : φ ≤ (7405034 : ℝ) / D_grid
  · exact j17Bound70 hω hz hlo70 hc70
  have hlo71 : (7405034 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc70).le
  by_cases hc71 : φ ≤ (7415648 : ℝ) / D_grid
  · exact j17Bound71 hω hz hlo71 hc71
  have hlo72 : (7415648 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc71).le
  by_cases hc72 : φ ≤ (7436876 : ℝ) / D_grid
  · exact j17Bound72 hω hz hlo72 hc72
  have hlo73 : (7436876 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc72).le
  by_cases hc73 : φ ≤ (7458104 : ℝ) / D_grid
  · exact j17Bound73 hω hz hlo73 hc73
  have hlo74 : (7458104 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc73).le
  by_cases hc74 : φ ≤ (7500560 : ℝ) / D_grid
  · exact j17Bound74 hω hz hlo74 hc74
  have hlo75 : (7500560 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc74).le
  by_cases hc75 : φ ≤ (7585472 : ℝ) / D_grid
  · exact j17Bound75 hω hz hlo75 hc75
  have hlo76 : (7585472 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc75).le
  by_cases hc76 : φ ≤ (7925120 : ℝ) / D_grid
  · exact j17Bound76 hω hz hlo76 hc76
  have hlo77 : (7925120 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc76).le
  by_cases hc77 : φ ≤ (8604416 : ℝ) / D_grid
  · exact j17Bound77 hω hz hlo77 hc77
  have hlo78 : (8604416 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc77).le
  by_cases hc78 : φ ≤ (9963008 : ℝ) / D_grid
  · exact j17Bound78 hω hz hlo78 hc78
  have hlo79 : (9963008 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc78).le
  by_cases hc79 : φ ≤ (11321600 : ℝ) / D_grid
  · exact j17Bound79 hω hz hlo79 hc79
  have hlo80 : (11321600 : ℝ) / D_grid ≤ φ := (lt_of_not_ge hc79).le
  exact j17Bound80 hω hz hlo80 htop

end LeanLab.ChenDoubleSieve.Task661

