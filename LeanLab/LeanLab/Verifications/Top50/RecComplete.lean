/-
I-0065: the record list of the least Goldbach prime, OEIS A025018 and A025019, is complete for
even n ≤ 10^5. For each record setter m_i ≤ 10^5 with value p_i, every even n with
m_i ≤ n < m_(i+1), or n ≤ 10^5 for the last, has minGB n ≤ p_i; with recTable_minGB this
says the record setters up to 10^5 are exactly the listed ones. Kernel checked, zero sorry.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.RecordsSummary
import LeanLab.Verifications.Top50.RecB1
import LeanLab.Verifications.Top50.RecB2
import LeanLab.Verifications.Top50.RecB3
import LeanLab.Verifications.Top50.RecB4
import LeanLab.Verifications.Top50.RecB5
import LeanLab.Verifications.Top50.RecB6
import LeanLab.Verifications.Top50.RecB7
import LeanLab.Verifications.Top50.RecB8
import LeanLab.Verifications.Top50.RecB9
import LeanLab.Verifications.Top50.RecB10
import LeanLab.Verifications.Top50.RecB11
import LeanLab.Verifications.Top50.RecB12
import LeanLab.Verifications.Top50.RecB13
import LeanLab.Verifications.Top50.RecB14
import LeanLab.Verifications.Top50.RecB15
import LeanLab.Verifications.Top50.RecB16
import LeanLab.Verifications.Top50.RecB17
import LeanLab.Verifications.Top50.RecB18
import LeanLab.Verifications.Top50.RecB19
import LeanLab.Verifications.Top50.RecB20
import LeanLab.Verifications.Top50.RecB21
import LeanLab.Verifications.Top50.RecB22
import LeanLab.Verifications.Top50.RecB23
import LeanLab.Verifications.Top50.RecB24
import LeanLab.Verifications.Top50.RecB25
import LeanLab.Verifications.Top50.RecB26
import LeanLab.Verifications.Top50.RecB27
import LeanLab.Verifications.Top50.RecB28
import LeanLab.Verifications.Top50.RecB29

namespace LeanLab.Verifications.Top50.Fast

open LeanLab.Verifications LeanLab.Verifications.Top50

theorem seg_1 : ∀ n, Even n → 4 ≤ n → n ≤ 4 → minGB n ≤ 2 := by
  intro n hn h1 h2
  exact block_range (a := 4) ⟨2, rfl⟩ (by norm_num) recBlock_1 n hn (by omega) (by omega)

theorem seg_2 : ∀ n, Even n → 6 ≤ n → n ≤ 10 → minGB n ≤ 3 := by
  intro n hn h1 h2
  exact block_range (a := 6) ⟨3, rfl⟩ (by norm_num) recBlock_2 n hn (by omega) (by omega)

theorem seg_3 : ∀ n, Even n → 12 ≤ n → n ≤ 28 → minGB n ≤ 5 := by
  intro n hn h1 h2
  exact block_range (a := 12) ⟨6, rfl⟩ (by norm_num) recBlock_3 n hn (by omega) (by omega)

theorem seg_4 : ∀ n, Even n → 30 ≤ n → n ≤ 96 → minGB n ≤ 7 := by
  intro n hn h1 h2
  exact block_range (a := 30) ⟨15, rfl⟩ (by norm_num) recBlock_4 n hn (by omega) (by omega)

theorem seg_5 : ∀ n, Even n → 98 ≤ n → n ≤ 218 → minGB n ≤ 19 := by
  intro n hn h1 h2
  exact block_range (a := 98) ⟨49, rfl⟩ (by norm_num) recBlock_5 n hn (by omega) (by omega)

theorem seg_6 : ∀ n, Even n → 220 ≤ n → n ≤ 306 → minGB n ≤ 23 := by
  intro n hn h1 h2
  exact block_range (a := 220) ⟨110, rfl⟩ (by norm_num) recBlock_6 n hn (by omega) (by omega)

theorem seg_7 : ∀ n, Even n → 308 ≤ n → n ≤ 554 → minGB n ≤ 31 := by
  intro n hn h1 h2
  exact block_range (a := 308) ⟨154, rfl⟩ (by norm_num) recBlock_7 n hn (by omega) (by omega)

theorem seg_8 : ∀ n, Even n → 556 ≤ n → n ≤ 990 → minGB n ≤ 47 := by
  intro n hn h1 h2
  exact block_range (a := 556) ⟨278, rfl⟩ (by norm_num) recBlock_8 n hn (by omega) (by omega)

theorem seg_9 : ∀ n, Even n → 992 ≤ n → n ≤ 2640 → minGB n ≤ 73 := by
  intro n hn h1 h2
  exact block_range (a := 992) ⟨496, rfl⟩ (by norm_num) recBlock_9 n hn (by omega) (by omega)

theorem seg_10 : ∀ n, Even n → 2642 ≤ n → n ≤ 5370 → minGB n ≤ 103 := by
  intro n hn h1 h2
  exact block_range (a := 2642) ⟨1321, rfl⟩ (by norm_num) recBlock_10 n hn (by omega) (by omega)

theorem seg_11 : ∀ n, Even n → 5372 ≤ n → n ≤ 7424 → minGB n ≤ 139 := by
  intro n hn h1 h2
  exact block_range (a := 5372) ⟨2686, rfl⟩ (by norm_num) recBlock_11 n hn (by omega) (by omega)

theorem seg_12 : ∀ n, Even n → 7426 ≤ n → n ≤ 43530 → minGB n ≤ 173 := by
  intro n hn h1 h2
  by_cases h0 : n < 17426
  · exact block_range (a := 7426) ⟨3713, rfl⟩ (by norm_num) recBlock_12 n hn (by omega) (by omega)
  by_cases h1 : n < 27426
  · exact block_range (a := 17426) ⟨8713, rfl⟩ (by norm_num) recBlock_13 n hn (by omega) (by omega)
  by_cases h2 : n < 37426
  · exact block_range (a := 27426) ⟨13713, rfl⟩ (by norm_num) recBlock_14 n hn (by omega) (by omega)
  by_cases h3 : n < 42426
  · exact block_range (a := 37426) ⟨18713, rfl⟩ (by norm_num) recBlock_15 n hn (by omega) (by omega)
  exact block_range (a := 42426) ⟨21213, rfl⟩ (by norm_num) recBlock_16 n hn (by omega) (by omega)

theorem seg_13 : ∀ n, Even n → 43532 ≤ n → n ≤ 54242 → minGB n ≤ 211 := by
  intro n hn h1 h2
  by_cases h0 : n < 48532
  · exact block_range (a := 43532) ⟨21766, rfl⟩ (by norm_num) recBlock_17 n hn (by omega) (by omega)
  by_cases h1 : n < 53532
  · exact block_range (a := 48532) ⟨24266, rfl⟩ (by norm_num) recBlock_18 n hn (by omega) (by omega)
  exact block_range (a := 53532) ⟨26766, rfl⟩ (by norm_num) recBlock_19 n hn (by omega) (by omega)

theorem seg_14 : ∀ n, Even n → 54244 ≤ n → n ≤ 63272 → minGB n ≤ 233 := by
  intro n hn h1 h2
  by_cases h0 : n < 59244
  · exact block_range (a := 54244) ⟨27122, rfl⟩ (by norm_num) recBlock_20 n hn (by omega) (by omega)
  exact block_range (a := 59244) ⟨29622, rfl⟩ (by norm_num) recBlock_21 n hn (by omega) (by omega)

theorem seg_15 : ∀ n, Even n → 63274 ≤ n → n ≤ 100000 → minGB n ≤ 293 := by
  intro n hn h1 h2
  by_cases h0 : n < 68274
  · exact block_range (a := 63274) ⟨31637, rfl⟩ (by norm_num) recBlock_22 n hn (by omega) (by omega)
  by_cases h1 : n < 73274
  · exact block_range (a := 68274) ⟨34137, rfl⟩ (by norm_num) recBlock_23 n hn (by omega) (by omega)
  by_cases h2 : n < 78274
  · exact block_range (a := 73274) ⟨36637, rfl⟩ (by norm_num) recBlock_24 n hn (by omega) (by omega)
  by_cases h3 : n < 83274
  · exact block_range (a := 78274) ⟨39137, rfl⟩ (by norm_num) recBlock_25 n hn (by omega) (by omega)
  by_cases h4 : n < 88274
  · exact block_range (a := 83274) ⟨41637, rfl⟩ (by norm_num) recBlock_26 n hn (by omega) (by omega)
  by_cases h5 : n < 93274
  · exact block_range (a := 88274) ⟨44137, rfl⟩ (by norm_num) recBlock_27 n hn (by omega) (by omega)
  by_cases h6 : n < 98274
  · exact block_range (a := 93274) ⟨46637, rfl⟩ (by norm_num) recBlock_28 n hn (by omega) (by omega)
  exact block_range (a := 98274) ⟨49137, rfl⟩ (by norm_num) recBlock_29 n hn (by omega) (by omega)

/-- Segments (m_i, last n, p_i). -/
def segTable : List (ℕ × ℕ × ℕ) := [
    (4, 4, 2),
    (6, 10, 3),
    (12, 28, 5),
    (30, 96, 7),
    (98, 218, 19),
    (220, 306, 23),
    (308, 554, 31),
    (556, 990, 47),
    (992, 2640, 73),
    (2642, 5370, 103),
    (5372, 7424, 139),
    (7426, 43530, 173),
    (43532, 54242, 211),
    (54244, 63272, 233),
    (63274, 100000, 293)]

/-- **I-0065.** On each record segment up to 10^5, the least Goldbach prime stays at most the
segment's record, kernel checked. -/
theorem records_complete_1e5 : ∀ x ∈ segTable, ∀ n, Even n → x.1 ≤ n → n ≤ x.2.1 →
    minGB n ≤ x.2.2 := by
  intro x hx
  simp only [segTable, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact seg_1
  · exact seg_2
  · exact seg_3
  · exact seg_4
  · exact seg_5
  · exact seg_6
  · exact seg_7
  · exact seg_8
  · exact seg_9
  · exact seg_10
  · exact seg_11
  · exact seg_12
  · exact seg_13
  · exact seg_14
  · exact seg_15

/-- So every even n with 4 ≤ n ≤ 10^5 has least Goldbach prime at most 293. -/
theorem minGB_le_293 : ∀ n, Even n → 4 ≤ n → n ≤ 10 ^ 5 → minGB n ≤ 293 := by
  intro n hn h1 h2
  have hev := hn
  obtain ⟨r, hr⟩ := hev
  norm_num at h2
  by_cases g0 : n ≤ 4
  · have := seg_1 n hn (by omega) g0; omega
  by_cases g1 : n ≤ 10
  · have := seg_2 n hn (by omega) g1; omega
  by_cases g2 : n ≤ 28
  · have := seg_3 n hn (by omega) g2; omega
  by_cases g3 : n ≤ 96
  · have := seg_4 n hn (by omega) g3; omega
  by_cases g4 : n ≤ 218
  · have := seg_5 n hn (by omega) g4; omega
  by_cases g5 : n ≤ 306
  · have := seg_6 n hn (by omega) g5; omega
  by_cases g6 : n ≤ 554
  · have := seg_7 n hn (by omega) g6; omega
  by_cases g7 : n ≤ 990
  · have := seg_8 n hn (by omega) g7; omega
  by_cases g8 : n ≤ 2640
  · have := seg_9 n hn (by omega) g8; omega
  by_cases g9 : n ≤ 5370
  · have := seg_10 n hn (by omega) g9; omega
  by_cases g10 : n ≤ 7424
  · have := seg_11 n hn (by omega) g10; omega
  by_cases g11 : n ≤ 43530
  · have := seg_12 n hn (by omega) g11; omega
  by_cases g12 : n ≤ 54242
  · have := seg_13 n hn (by omega) g12; omega
  by_cases g13 : n ≤ 63272
  · have := seg_14 n hn (by omega) g13; omega
  have := seg_15 n hn (by omega) (by omega); omega

end LeanLab.Verifications.Top50.Fast
