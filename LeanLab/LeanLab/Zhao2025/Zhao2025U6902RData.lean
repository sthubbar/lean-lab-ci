import Mathlib
import LeanLab.Zhao2025.Zhao2025U6902R

/-!
# Zhao 2025, the twenty R inputs of the five U-6837 layout C cases, certified

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6902, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

For each case `cNNN`, `rA` is (3.42), (3.43) with `λ₁ = λ₂ = λ₁,₁`, `rB` with `λ₁ = λ₁,₁`,
`λ₂ = λ*`, `r3` with `λ₁ = λ₂ = λ*`, all with the `N*` shown; `sR` is (3.38) with `λ₁ = λ₂ = λ₁,₁`.
`x` and `N*` from gen/u6902_r.py.  Each theorem is PROVED by kernel computation; with
`Rbound_of_342_343` and `Rbound_of_338` it bounds `R(Λ)` CONDITIONAL ON those displays.
The targets are the values used in `case060_closes` to `case068_closes`.
-/

namespace LeanLab.Zhao2025.U6900

set_option maxRecDepth 100000 in
theorem c060_rA_ok : chkR4 (1309/1000 : ℚ) (337/250 : ℚ) (3/5 : ℚ) (3/5 : ℚ) (91/100 : ℚ) 3 (1497/5000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c060_rB_ok : chkR4 (233/250 : ℚ) (337/250 : ℚ) (3/5 : ℚ) (91/100 : ℚ) (91/100 : ℚ) 4 (5877/25000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c060_r3_ok : chkR4 (523/500 : ℚ) (337/250 : ℚ) (91/100 : ℚ) (91/100 : ℚ) (91/100 : ℚ) 4 (1479/10000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c060_sR_ok : chkR8 (37/50 : ℚ) (337/250 : ℚ) (3/5 : ℚ) (3/5 : ℚ) (91/100 : ℚ) (28991/50000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c062_rA_ok : chkR4 (1317/1000 : ℚ) (271/200 : ℚ) (31/50 : ℚ) (31/50 : ℚ) (17/20 : ℚ) 3 (14653/50000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c062_rB_ok : chkR4 (331/250 : ℚ) (271/200 : ℚ) (31/50 : ℚ) (17/20 : ℚ) (17/20 : ℚ) 3 (5041/20000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c062_r3_ok : chkR4 (351/250 : ℚ) (271/200 : ℚ) (17/20 : ℚ) (17/20 : ℚ) (17/20 : ℚ) 3 (383/2000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c062_sR_ok : chkR8 (94/125 : ℚ) (271/200 : ℚ) (31/50 : ℚ) (31/50 : ℚ) (17/20 : ℚ) (11923/20000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c064_rA_ok : chkR4 (661/500 : ℚ) (1363/1000 : ℚ) (16/25 : ℚ) (16/25 : ℚ) (37/50 : ℚ) 3 (14869/50000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c064_rB_ok : chkR4 (53/40 : ℚ) (1363/1000 : ℚ) (16/25 : ℚ) (37/50 : ℚ) (37/50 : ℚ) 3 (6959/25000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c064_r3_ok : chkR4 (1361/1000 : ℚ) (1363/1000 : ℚ) (37/50 : ℚ) (37/50 : ℚ) (37/50 : ℚ) 3 (24889/100000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c064_sR_ok : chkR8 (747/1000 : ℚ) (1363/1000 : ℚ) (16/25 : ℚ) (16/25 : ℚ) (37/50 : ℚ) (33213/50000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c066_rA_ok : chkR4 (1331/1000 : ℚ) (137/100 : ℚ) (33/50 : ℚ) (33/50 : ℚ) (37/50 : ℚ) 3 (3603/12500 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c066_rB_ok : chkR4 (1333/1000 : ℚ) (137/100 : ℚ) (33/50 : ℚ) (37/50 : ℚ) (37/50 : ℚ) 3 (1369/5000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c066_r3_ok : chkR4 (1361/1000 : ℚ) (137/100 : ℚ) (37/50 : ℚ) (37/50 : ℚ) (37/50 : ℚ) 3 (1569/6250 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c066_sR_ok : chkR8 (19/25 : ℚ) (137/100 : ℚ) (33/50 : ℚ) (33/50 : ℚ) (37/50 : ℚ) (16233/25000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c068_rA_ok : chkR4 (669/500 : ℚ) (689/500 : ℚ) (17/25 : ℚ) (17/25 : ℚ) (351/500 : ℚ) 3 (5747/20000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c068_rB_ok : chkR4 (669/500 : ℚ) (689/500 : ℚ) (17/25 : ℚ) (351/500 : ℚ) (351/500 : ℚ) 3 (14171/50000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c068_r3_ok : chkR4 (673/500 : ℚ) (689/500 : ℚ) (351/500 : ℚ) (351/500 : ℚ) (351/500 : ℚ) 3 (27703/100000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem c068_sR_ok : chkR8 (753/1000 : ℚ) (689/500 : ℚ) (17/25 : ℚ) (17/25 : ℚ) (351/500 : ℚ) (33957/50000 : ℚ) = true := by decide +kernel

end LeanLab.Zhao2025.U6900
