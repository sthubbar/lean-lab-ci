/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Supporting finite certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task303LowData

namespace LeanLab.DtRS1998.Task303.Low

open LeanLab.DtRS1998 Certificate294 LeanLab.Verifications.Top50.Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async true

/-- Even offsets in closed window 100 have a prime complement, page 210. -/
theorem window100 : ∀ x : ℕ, 100000000 ≤ x → x ≤ 100000000 → 2 ∣ x →
    ∃ d ∈ offsets, (x + d).Prime := by
  intro x hx0 hx1 he
  have hsub : ([23, 39, 47, 53, 71, 77, 89, 149, 221, 243, 299, 339, 383, 389, 399, 411, 509, 519, 521, 537, 551, 581, 591, 593, 611, 687, 729, 761, 767, 779, 831, 891, 899, 917, 927, 933, 959, 977, 989, 1001, 1013, 1067, 1073, 1131, 1163, 1181, 1187, 1209, 1361, 1373, 1383, 1421, 1431, 1439, 1577, 1601, 1617, 1631, 1647, 1653, 1659, 1673, 1691, 1731, 1773, 1787, 1809, 1829, 1869, 1871, 1907, 1941, 1961, 1989, 2007, 2021, 2037, 2063, 2079, 2151, 2157, 2201, 2247, 2249, 2271, 2301, 2303, 2333, 2367, 2373, 2397, 2423, 2433, 2481, 2553, 2601, 2619, 2627, 2643, 2661, 2679, 2703, 2721, 2747, 2751, 2753, 2777, 2819, 2859, 2891, 2901, 2903, 2913, 2931, 3017, 3029, 3047, 3081, 3099, 3161, 3321, 3363, 3909] : List ℕ).all (fun d => offsets.contains d) = true := by decide +kernel
  obtain ⟨d, hd, hp⟩ := offset_window (x0 := 100000000) (x1 := 100000000) (lo := 100000023) (W := 3887)
    (Ds := [23, 39, 47, 53, 71, 77, 89, 149, 221, 243, 299, 339, 383, 389, 399, 411, 509, 519, 521, 537, 551, 581, 591, 593, 611, 687, 729, 761, 767, 779, 831, 891, 899, 917, 927, 933, 959, 977, 989, 1001, 1013, 1067, 1073, 1131, 1163, 1181, 1187, 1209, 1361, 1373, 1383, 1421, 1431, 1439, 1577, 1601, 1617, 1631, 1647, 1653, 1659, 1673, 1691, 1731, 1773, 1787, 1809, 1829, 1869, 1871, 1907, 1941, 1961, 1989, 2007, 2021, 2037, 2063, 2079, 2151, 2157, 2201, 2247, 2249, 2271, 2301, 2303, 2333, 2367, 2373, 2397, 2423, 2433, 2481, 2553, 2601, 2619, 2627, 2643, 2661, 2679, 2703, 2721, 2747, 2751, 2753, 2777, 2819, 2859, 2891, 2901, 2903, 2913, 2931, 3017, 3029, 3047, 3081, 3099, 3161, 3321, 3363, 3909]) (by decide) (by norm_num [B2]) (by decide +kernel)
    (by decide +kernel) hx0 hx1 (Nat.dvd_sub he (by decide))
  exact ⟨d, by simpa using List.all_eq_true.mp hsub d hd, hp⟩

#print axioms window100

end LeanLab.DtRS1998.Task303.Low
