import Mathlib
import LeanLab.ChebyshevExplicit.Feed1122_Novelty1615_chebyshev_pi_bounds_from_96098_p2_cert
import LeanLab.ChebyshevExplicit.Feed1122_Novelty1615_chebyshev_pi_bounds_from_96098_p2_data0
import LeanLab.ChebyshevExplicit.Feed1122_Novelty1615_chebyshev_pi_bounds_from_96098_p2_data1
import LeanLab.ChebyshevExplicit.Feed1122_Novelty1615_chebyshev_pi_bounds_from_96098_p2_data2
import LeanLab.ChebyshevExplicit.Feed1122_Novelty1615_chebyshev_pi_bounds_from_96098_p2_data3

/-!
# ChebyshevExplicit, burst 1122, upper range `2000000 < m < 3300000` of U-1615

AI wrote this Lean code. Binary Goldbach is open.

The proved chain `S68PiCert.pb0` to `pb13` of `LeanLab/AlmostPrimes/PortedDusart/PiFinite.lean` is
replayed to its end state at `n = 2150977`, which bounds the prime count there and gives
`π m (log m - 1.1) ≤ m` for `60184 ≤ m < 2150969`. From that state the stepper `pstep2` of
`..._p2_cert.lean` runs on new certificate data `P2Data.up0` to `up7` up to `L = 3300001`.
-/

namespace LeanLab.ChebyshevExplicit.Novelty1615.P2Cert

open S68PiCert DusartCert

/-- PROVED: the 1.1 shifted form gives the product form once `m ≥ 156979`. -/
lemma mul_of_shift {m : ℕ} (h1 : 156979 ≤ m)
    (hg : (Nat.primeCounting m : ℝ) * (Real.log m - 11 / 10) ≤ m) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  have hl := log_ge_of_ge h1
  have hp : (0 : ℝ) ≤ Nat.primeCounting m := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ (Nat.primeCounting m : ℝ) * (10555 / 100000 * Real.log m - 1216105 / 1000000) :=
    mul_nonneg hp (by linarith)
  nlinarith

lemma logS3 : Real.log ((2150969 : ℕ) : ℝ) ≤ ((logHi QQ 2150969 1 21 : ℕ) : ℝ) / (QQ : ℝ) := by
  have h := (log_bounds QQ 2150969 1 21 (by decide +kernel)).2
  have hQ : (0 : ℝ) < QQ := by exact_mod_cast QQ_pos
  rw [le_div_iff₀ hQ]
  simp only [Nat.cast_one, div_one] at h
  linarith

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 0. -/
theorem pu0 : prun2 QQ P2Data.up0 (2150977, gaps.drop 35, 159313, logHi QQ 2150969 1 21, 2150969) =
    some (2295347, gaps.drop 11, 169190, 270178251002516624513, 2295341) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 1. -/
theorem pu1 : prun2 QQ P2Data.up1 (2295347, gaps.drop 11, 169190, 270178251002516624513, 2295341) =
    some (2439727, gaps.drop 35, 178966, 271303535060442748396, 2439719) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 2. -/
theorem pu2 : prun2 QQ P2Data.up2 (2439727, gaps.drop 35, 178966, 271303535060442748396, 2439719) =
    some (2584097, gaps.drop 11, 188809, 272364060793852163905, 2584091) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 3. -/
theorem pu3 : prun2 QQ P2Data.up3 (2584097, gaps.drop 11, 188809, 272364060793852163905, 2584091) =
    some (2728477, gaps.drop 35, 198554, 273366970310079128600, 2728471) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 4. -/
theorem pu4 : prun2 QQ P2Data.up4 (2728477, gaps.drop 35, 198554, 273366970310079128600, 2728471) =
    some (2872847, gaps.drop 11, 208305, 274317974121801145750, 2872823) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 5. -/
theorem pu5 : prun2 QQ P2Data.up5 (2872847, gaps.drop 11, 208305, 274317974121801145750, 2872823) =
    some (3017227, gaps.drop 35, 217964, 275222539871864485047, 3017207) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 6. -/
theorem pu6 : prun2 QQ P2Data.up6 (3017227, gaps.drop 35, 217964, 275222539871864485047, 3017207) =
    some (3161597, gaps.drop 11, 227614, 276084826248228635890, 3161593) := by decide +kernel

set_option maxRecDepth 200000 in
/-- Kernel certificate run over upper block 7. -/
theorem pu7 : prun2 QQ P2Data.up7 (3161597, gaps.drop 11, 227614, 276084826248228635890, 3161593) =
    some (3300007, gaps.drop 15, 236901, 276875212501606210631, 3300001) := by decide +kernel

/-- PROVED: the replayed `PiFinite` chain, its end state at `2150977`. -/
theorem replay14 : Nat.count Nat.Prime 2150977 ≤ 159313 ∧
    (∃ i < 48, gaps.drop 35 = gaps.drop i ∧ 2150977 % 210 = res.getD i 0) ∧
    ∀ m, 60184 ≤ m → m < 2150969 →
      ((Nat.primeCounting m : ℝ) * (Real.log m - 11 / 10) ≤ m) := by
  have I0 := inv0
  have I1 := prun_sound QQ QQ_pos _ _ _ (by exact I0) pb0
  have I2 := prun_sound QQ QQ_pos _ _ _ (by exact I1) pb1
  have I3 := prun_sound QQ QQ_pos _ _ _ (by exact I2) pb2
  have I4 := prun_sound QQ QQ_pos _ _ _ (by exact I3) pb3
  have I5 := prun_sound QQ QQ_pos _ _ _ (by exact I4) pb4
  have I6 := prun_sound QQ QQ_pos _ _ _ (by exact I5) pb5
  have I7 := prun_sound QQ QQ_pos _ _ _ (by exact I6) pb6
  have I8 := prun_sound QQ QQ_pos _ _ _ (by exact I7) pb7
  have I9 := prun_sound QQ QQ_pos _ _ _ (by exact I8) pb8
  have I10 := prun_sound QQ QQ_pos _ _ _ (by exact I9) pb9
  have I11 := prun_sound QQ QQ_pos _ _ _ (by exact I10) pb10
  have I12 := prun_sound QQ QQ_pos _ _ _ (by exact I11) pb11
  have I13 := prun_sound QQ QQ_pos _ _ _ (by exact I12) pb12
  have I14 := prun_sound QQ QQ_pos _ _ _ (by exact I13) pb13
  obtain ⟨i, hi, hgs, hn, hn11, hk, hL, hlog, hLn, hgood⟩ := I14
  exact ⟨hk, ⟨i, hi, hgs, hn⟩, fun m h1 h2 => hgood m h1 (by omega) h2⟩

/-- PROVED: `π m log m ≤ 1.10555 m` on `2150969 ≤ m < 3300001`, by the new kernel certificate. -/
theorem pi_upper_2150969_3300001 (m : ℕ) (h1 : 2150969 ≤ m) (h2 : m < 3300001) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  obtain ⟨hk, ⟨i, hi, hgs, hn⟩, -⟩ := replay14
  have J0 : Inv2 2150969 QQ 2150977 (gaps.drop 35) 159313 (logHi QQ 2150969 1 21) 2150969 := by
    refine ⟨i, hi, hgs, hn, by norm_num, hk, le_rfl, logS3, Or.inl rfl, ?_⟩
    intro m h1 h2 h3; omega
  have J1 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J0) pu0
  have J2 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J1) pu1
  have J3 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J2) pu2
  have J4 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J3) pu3
  have J5 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J4) pu4
  have J6 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J5) pu5
  have J7 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J6) pu6
  have J8 := prun2_sound 2150969 QQ (by norm_num) QQ_pos _ _ _ (by exact J7) pu7
  obtain ⟨_, _, _, _, _, _, _, _, _, hgood⟩ := J8
  exact hgood m h1 (by omega) h2

/-- PROVED, formerly a LEAF: the finite check of U-1615 on `2000000 < m < 3300000`. -/
theorem pi_upper_2000000_3300000 (m : ℕ) (h1 : 2000000 < m) (h2 : m < 3300000) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  by_cases h : m < 2150969
  · exact mul_of_shift (by omega) (replay14.2.2 m (by omega) h)
  · exact pi_upper_2150969_3300001 m (by omega) (by omega)

/-- PROVED from the pieces: product form on `96098 ≤ m < 3300000`. -/
theorem pi_upper_mul_96098_3300000 (m : ℕ) (h1 : 96098 ≤ m) (h2 : m < 3300000) :
    (Nat.primeCounting m : ℝ) * Real.log m ≤ 110555 / 100000 * m := by
  by_cases ha : m < 156979
  · exact pi_upper_96098_156979 m h1 ha
  by_cases hb : m ≤ 2000000
  · exact pi_upper_156979_2000000 m (by omega) hb
  exact pi_upper_2000000_3300000 m (by omega) h2

end LeanLab.ChebyshevExplicit.Novelty1615.P2Cert
