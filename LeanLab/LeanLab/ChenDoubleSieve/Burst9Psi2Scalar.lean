import LeanLab.ChenDoubleSieve.Burst9Psi2Panels

/-!
# Burst 9: certified `J` and `K` terms of Wu's Ψ₂ for the four Proposition 4 rows of Table 1

Source: Wu 2004, arXiv 0705.1652, Lemma 5.2, page 26, and Table 1, page 30. For each row the
three `J` integrals are bounded above and the two `K` integrals below by exact rational panel
sums checked with `decide +kernel`: 128 panels for `J` with `c ≥ 2` and for `K`, 256 left
endpoint panels for the reversed `J 2 (κ₂ − 1)`, `κ₂ − 1 < 2`. All PROVED.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst9Psi2
open Wu04Functional

/-! #### Row 1 of Table 1, `s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44` -/

theorem cert_Jsp_0 : jUpperSum (177/50) 128 ≤ (140987492719/500000000000) := by decide +kernel
theorem cert_Jk1_0 : jUpperSum (253/100) 128 ≤ (25782811713/500000000000) := by decide +kernel
theorem cert_Jk2_0 : ∑ j ∈ range 256, rCell (19/10) 256 j ≤ (1344314939/500000000000) := by decide +kernel
theorem cert_K1_0 : (189650211327/250000000000) ≤ kLowerSum (227/50) (1 - 1 / (11/5)) (1 - 1 / (227/50)) 128 := by
  decide +kernel
theorem cert_K2_0 : (75381309803/500000000000) ≤ kLowerSum (353/100) (1 - 1 / (61/25)) (1 - 1 / (353/100)) 128 := by
  decide +kernel

/-- The `J` and `K` terms of `Ψ₂` in row 1, Wu 2004 Lemma 5.2 page 26. PROVED. -/
theorem scalar_row0 :
    J 2 ((tableParams 0).sp - 1) ≤ (140987492719/500000000000 : ℝ) ∧ J 2 ((tableParams 0).k1 - 1) ≤ (25782811713/500000000000 : ℝ) ∧
    J 2 ((tableParams 0).k2 - 1) ≤ (1344314939/500000000000 : ℝ) ∧
    (189650211327/250000000000 : ℝ) ≤ K (tableParams 0).sp (1 - 1 / (tableParams 0).s) (1 - 1 / (tableParams 0).sp) ∧
    (75381309803/500000000000 : ℝ) ≤ K (tableParams 0).k1 (1 - 1 / (tableParams 0).k3) (1 - 1 / (tableParams 0).k1) := by
  have h1 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jsp_0
  have h2 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jk1_0
  have h3 := J_rev_upper_of_cert (by norm_num) (by norm_num) (by norm_num) cert_Jk2_0
  have h4 := K_lower_of_cert (by norm_num) (by norm_num) cert_K1_0
  have h5 := K_lower_of_cert (by norm_num) (by norm_num) cert_K2_0
  push_cast at h1 h2 h3 h4 h5
  norm_num [tableParams] at h1 h2 h3 h4 h5 ⊢
  exact ⟨h1, h2, h3, h4, h5⟩

/-! #### Row 2 of Table 1, `s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43` -/

theorem cert_Jsp_1 : jUpperSum (7/2) 128 ≤ (271471874851/1000000000000) := by decide +kernel
theorem cert_Jk1_1 : jUpperSum (127/50) 128 ≤ (6657010919/125000000000) := by decide +kernel
theorem cert_Jk2_1 : ∑ j ∈ range 256, rCell (47/25) 256 j ≤ (3927342993/1000000000000) := by decide +kernel
theorem cert_K1_1 : (350681866259/500000000000) ≤ kLowerSum (9/2) (1 - 1 / (23/10)) (1 - 1 / (9/2)) 128 := by
  decide +kernel
theorem cert_K2_1 : (155855707957/1000000000000) ≤ kLowerSum (177/50) (1 - 1 / (243/100)) (1 - 1 / (177/50)) 128 := by
  decide +kernel

/-- The `J` and `K` terms of `Ψ₂` in row 2, Wu 2004 Lemma 5.2 page 26. PROVED. -/
theorem scalar_row1 :
    J 2 ((tableParams 1).sp - 1) ≤ (271471874851/1000000000000 : ℝ) ∧ J 2 ((tableParams 1).k1 - 1) ≤ (6657010919/125000000000 : ℝ) ∧
    J 2 ((tableParams 1).k2 - 1) ≤ (3927342993/1000000000000 : ℝ) ∧
    (350681866259/500000000000 : ℝ) ≤ K (tableParams 1).sp (1 - 1 / (tableParams 1).s) (1 - 1 / (tableParams 1).sp) ∧
    (155855707957/1000000000000 : ℝ) ≤ K (tableParams 1).k1 (1 - 1 / (tableParams 1).k3) (1 - 1 / (tableParams 1).k1) := by
  have h1 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jsp_1
  have h2 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jk1_1
  have h3 := J_rev_upper_of_cert (by norm_num) (by norm_num) (by norm_num) cert_Jk2_1
  have h4 := K_lower_of_cert (by norm_num) (by norm_num) cert_K1_1
  have h5 := K_lower_of_cert (by norm_num) (by norm_num) cert_K2_1
  push_cast at h1 h2 h3 h4 h5
  norm_num [tableParams] at h1 h2 h3 h4 h5 ⊢
  exact ⟨h1, h2, h3, h4, h5⟩

/-! #### Row 3 of Table 1, `s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40` -/

theorem cert_Jsp_2 : jUpperSum (173/50) 128 ≤ (261031973553/1000000000000) := by decide +kernel
theorem cert_Jk1_2 : jUpperSum (257/100) 128 ≤ (7304934837/125000000000) := by decide +kernel
theorem cert_Jk2_2 : ∑ j ∈ range 256, rCell (187/100) 256 j ≤ (1160635281/250000000000) := by decide +kernel
theorem cert_K1_2 : (644716572381/1000000000000) ≤ kLowerSum (223/50) (1 - 1 / (12/5)) (1 - 1 / (223/50)) 128 := by
  decide +kernel
theorem cert_K2_2 : (34303102487/200000000000) ≤ kLowerSum (357/100) (1 - 1 / (12/5)) (1 - 1 / (357/100)) 128 := by
  decide +kernel

/-- The `J` and `K` terms of `Ψ₂` in row 3, Wu 2004 Lemma 5.2 page 26. PROVED. -/
theorem scalar_row2 :
    J 2 ((tableParams 2).sp - 1) ≤ (261031973553/1000000000000 : ℝ) ∧ J 2 ((tableParams 2).k1 - 1) ≤ (7304934837/125000000000 : ℝ) ∧
    J 2 ((tableParams 2).k2 - 1) ≤ (1160635281/250000000000 : ℝ) ∧
    (644716572381/1000000000000 : ℝ) ≤ K (tableParams 2).sp (1 - 1 / (tableParams 2).s) (1 - 1 / (tableParams 2).sp) ∧
    (34303102487/200000000000 : ℝ) ≤ K (tableParams 2).k1 (1 - 1 / (tableParams 2).k3) (1 - 1 / (tableParams 2).k1) := by
  have h1 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jsp_2
  have h2 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jk1_2
  have h3 := J_rev_upper_of_cert (by norm_num) (by norm_num) (by norm_num) cert_Jk2_2
  have h4 := K_lower_of_cert (by norm_num) (by norm_num) cert_K1_2
  have h5 := K_lower_of_cert (by norm_num) (by norm_num) cert_K2_2
  push_cast at h1 h2 h3 h4 h5
  norm_num [tableParams] at h1 h2 h3 h4 h5 ⊢
  exact ⟨h1, h2, h3, h4, h5⟩

/-! #### Row 4 of Table 1, `s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50` -/

theorem cert_Jsp_3 : jUpperSum (78/25) 128 ≤ (21944442411/125000000000) := by decide +kernel
theorem cert_Jk1_3 : jUpperSum (64/25) 128 ≤ (56693323819/1000000000000) := by decide +kernel
theorem cert_Jk2_3 : ∑ j ∈ range 256, rCell (191/100) 256 j ≤ (2162433889/1000000000000) := by decide +kernel
theorem cert_K1_3 : (215333197627/500000000000) ≤ kLowerSum (103/25) (1 - 1 / (5/2)) (1 - 1 / (103/25)) 128 := by
  decide +kernel
theorem cert_K2_3 : (799061389/5000000000) ≤ kLowerSum (89/25) (1 - 1 / (5/2)) (1 - 1 / (89/25)) 128 := by
  decide +kernel

/-- The `J` and `K` terms of `Ψ₂` in row 4, Wu 2004 Lemma 5.2 page 26. PROVED. -/
theorem scalar_row3 :
    J 2 ((tableParams 3).sp - 1) ≤ (21944442411/125000000000 : ℝ) ∧ J 2 ((tableParams 3).k1 - 1) ≤ (56693323819/1000000000000 : ℝ) ∧
    J 2 ((tableParams 3).k2 - 1) ≤ (2162433889/1000000000000 : ℝ) ∧
    (215333197627/500000000000 : ℝ) ≤ K (tableParams 3).sp (1 - 1 / (tableParams 3).s) (1 - 1 / (tableParams 3).sp) ∧
    (799061389/5000000000 : ℝ) ≤ K (tableParams 3).k1 (1 - 1 / (tableParams 3).k3) (1 - 1 / (tableParams 3).k1) := by
  have h1 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jsp_3
  have h2 := J_upper_of_cert (by norm_num) (by norm_num) cert_Jk1_3
  have h3 := J_rev_upper_of_cert (by norm_num) (by norm_num) (by norm_num) cert_Jk2_3
  have h4 := K_lower_of_cert (by norm_num) (by norm_num) cert_K1_3
  have h5 := K_lower_of_cert (by norm_num) (by norm_num) cert_K2_3
  push_cast at h1 h2 h3 h4 h5
  norm_num [tableParams] at h1 h2 h3 h4 h5 ⊢
  exact ⟨h1, h2, h3, h4, h5⟩

end LeanLab.ChenDoubleSieve.Burst9Psi2

#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.scalar_row0
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.scalar_row1
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.scalar_row2
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.scalar_row3
