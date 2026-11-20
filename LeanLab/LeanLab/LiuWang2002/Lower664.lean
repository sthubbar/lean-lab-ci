import LeanLab.Ported.Prove2Me.LL_Decomp368b_primorial_c3

/-!
Derived finite supply for the already proved first two Decomp368b ranges.
Source Schoenfeld 1976 page 356 display 5.1 star.
The smaller windows avoid importing the old checkpoint chains.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task664
open LeanLab.Ported.Prove2Me.Task664
open ThetaSieve PrimC3Cert

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The exact first block supplies the upper theta state at 917507. -/
theorem lower_initial :
    (Q : ℝ) * th (917507 - 1) ≤ (16906844048882946037829117 : ℕ) := by
  have hstart : Seg.hi PrimData0.s0 = LHi 2 ∧ Seg.L PrimData0.s0 = 3 := by
    decide +kernel
  have hI : (Q : ℝ) * th (Seg.L PrimData0.s0 - 1) ≤ Seg.hi PrimData0.s0 := by
    rw [hstart.1, hstart.2]
    exact HiInv_three
  have hc : chainOK (PrimData0.s0 :: PrimData0.segs.tail) = true := by
    decide +kernel
  have hok : ∀ s ∈ PrimData0.s0 :: PrimData0.segs.tail, Seg.bok s = true := by
    simpa only [PrimData0.segs, List.tail_cons] using PrimorialCert.block_0.1
  have h := bchain_hi_sound PrimData0.segs.tail PrimData0.s0 hc hok hI
  have he : Seg.hi' (chainEnd PrimData0.s0 PrimData0.segs.tail) = 16906844048882946037829117 ∧
      Seg.L (chainEnd PrimData0.s0 PrimData0.segs.tail) +
        2 * Seg.W (chainEnd PrimData0.s0 PrimData0.segs.tail) = 917507 := by
    decide +kernel
  rw [he.1, he.2] at h
  exact?

/-- A strict integer certificate above one million through four million. -/
theorem lower_certificate :
    primChain 18458400208034708012 1000000 128 256 48 917507
      16906844048882946037829117 = true := by
  decide +kernel

/-- The lower supply has no cited analytic premise. -/
theorem primorial_1m_4m (n : ℕ) (hn : 1000000 < n) (hn' : n ≤ 4000000) :
    primorial n * 25 ^ n < 68 ^ n := by
  have h := primChain_sound 48 917507 16906844048882946037829117
    lower_certificate lower_initial n hn (by omega) (by omega)
  have hc := c_le cpos
  rw [cval] at hc
  have hscaled : (Q : ℝ) * th n < Q * (n * Real.log (68 / 25)) := by
    calc
      (Q : ℝ) * th n < (n : ℝ) * (18458400208034708012 : ℕ) := h
      _ ≤ (n : ℝ) * (Q * Real.log (68 / 25)) :=
        mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
      _ = Q * (n * Real.log (68 / 25)) := by ring
  apply primorial_of_theta n (by omega)
  exact lt_of_mul_lt_mul_left hscaled Q_pos.le

end LeanLab.LiuWang2002.Task664
#print axioms LeanLab.LiuWang2002.Task664.lower_initial
#print axioms LeanLab.LiuWang2002.Task664.lower_certificate
#print axioms LeanLab.LiuWang2002.Task664.primorial_1m_4m
