/-
U-1385, run PC 20261021T0803Z-19426. Part 8 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
Chains row 22, lifted from 727 to 751, through the seven windows of Part4 to Part7
to get seg_23 with the original statement, SmallGBUpTo 751 10000000.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.OeSHP2014.OeSHP2014U1385Part3
import LeanLab.OeSHP2014.OeSHP2014U1385Part4
import LeanLab.OeSHP2014.OeSHP2014U1385Part5
import LeanLab.OeSHP2014.OeSHP2014U1385Part6
import LeanLab.OeSHP2014.OeSHP2014U1385Part7

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem small_lift {N N' B : ℕ} (h : SmallGBUpTo N B) (hN : N ≤ N') : SmallGBUpTo N' B := by
  intro n hn h4 hnB
  obtain ⟨q, hq, hqN, hqn, hp⟩ := h n hn h4 hnB
  exact ⟨q, hq, le_trans hqN hN, hqn, hp⟩

/-- Row 23 chain, step 1. -/
theorem seg23_1 : SmallGBUpTo 751 4692060 :=
  small_extend2 (a := 3807402) (A := 3807404) (lo := 3806644) (W := 885416) (small_lift seg_22 (by norm_num))
    ⟨1903701, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_1

/-- Row 23 chain, step 2. -/
theorem seg23_2 : SmallGBUpTo 751 5576718 :=
  small_extend2 (a := 4692060) (A := 4692062) (lo := 4691302) (W := 885416) (seg23_1)
    ⟨2346030, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_2

/-- Row 23 chain, step 3. -/
theorem seg23_3 : SmallGBUpTo 751 6461376 :=
  small_extend2 (a := 5576718) (A := 5576720) (lo := 5575960) (W := 885416) (seg23_2)
    ⟨2788359, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_3

/-- Row 23 chain, step 4. -/
theorem seg23_4 : SmallGBUpTo 751 7346034 :=
  small_extend2 (a := 6461376) (A := 6461378) (lo := 6460618) (W := 885416) (seg23_3)
    ⟨3230688, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_4

/-- Row 23 chain, step 5. -/
theorem seg23_5 : SmallGBUpTo 751 8230692 :=
  small_extend2 (a := 7346034) (A := 7346036) (lo := 7345276) (W := 885416) (seg23_4)
    ⟨3673017, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_5

/-- Row 23 chain, step 6. -/
theorem seg23_6 : SmallGBUpTo 751 9115350 :=
  small_extend2 (a := 8230692) (A := 8230694) (lo := 8229934) (W := 885416) (seg23_5)
    ⟨4115346, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_6

/-- Every even m with 4 ≤ m ≤ 10000000 has minGB m ≤ 751. -/
theorem seg_23 : SmallGBUpTo 751 10000000 :=
  small_extend2 (a := 9115350) (A := 9115352) (lo := 9114592) (W := 885408) (seg23_6)
    ⟨4557675, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num [B2]) (by norm_num)
    (take_prime 133) take_le_23 window23_7

end LeanLab.OeSHP2014.U1385
