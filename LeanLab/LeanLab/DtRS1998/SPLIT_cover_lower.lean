/-
Split of `cover_lower` in `LeanLab.DtRS1998.Decomp455d`.

The target asserts that every index `j` with `251000000 ≤ j < 312500000` has an offset
`a` in the fixed list `offsets` with `a ≤ 10 ^ 300` and `2 * j + a` prime. This file cuts
that index range into six consecutive subranges, one leaf per subrange, and regroups
them with an integer partition proved inside `cover_lower_split`.

Each leaf is the same prime-companion assertion on a strictly shorter index range, and
each one drops the size bound on the offset, which is a separate estimate already
available for the whole list. So no leaf restates the target and every leaf is strictly
weaker than it.

All six leaves are open. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455d

namespace LeanLab.DtRS1998.Decomp455d

open Decomp455a

set_option maxRecDepth 100000

set_option maxRecDepth 1000000

private theorem c_part1_win_0 : ∀ i : ℕ, 251000000 ≤ i → i < 251200000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 502000000) (x1 := 502399998) (lo := 502000069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_1 : ∀ i : ℕ, 251200000 ≤ i → i < 251400000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 502400000) (x1 := 502799998) (lo := 502400069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_2 : ∀ i : ℕ, 251400000 ≤ i → i < 251496054 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 502800000) (x1 := 502992106) (lo := 502800069) (W := 303179)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_251496054 : ∀ i : ℕ, 251496054 ≤ i → i < 251496055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 251496054 := by omega
  subst hi
  exact ⟨125219, by decide, by norm_num⟩
private theorem c_part1_win_4 : ∀ i : ℕ, 251496055 ≤ i → i < 251696055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 502992110) (x1 := 503392108) (lo := 502992179) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_5 : ∀ i : ℕ, 251696055 ≤ i → i < 251896055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 503392110) (x1 := 503792108) (lo := 503392179) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_6 : ∀ i : ℕ, 251896055 ≤ i → i < 252096055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 503792110) (x1 := 504192108) (lo := 503792179) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_7 : ∀ i : ℕ, 252096055 ≤ i → i < 252296055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 504192110) (x1 := 504592108) (lo := 504192179) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_8 : ∀ i : ℕ, 252296055 ≤ i → i < 252496055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 504592110) (x1 := 504992108) (lo := 504592179) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_9 : ∀ i : ℕ, 252496055 ≤ i → i < 252696055 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 504992110) (x1 := 505392108) (lo := 504992179) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_10 : ∀ i : ℕ, 252696055 ≤ i → i < 252748974 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 505392110) (x1 := 505497946) (lo := 505392179) (W := 216909)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_252748974 : ∀ i : ℕ, 252748974 ≤ i → i < 252748975 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 252748974 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part1_win_12 : ∀ i : ℕ, 252748975 ≤ i → i < 252933729 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 505497950) (x1 := 505867456) (lo := 505498019) (W := 480579)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_252933729 : ∀ i : ℕ, 252933729 ≤ i → i < 252933730 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 252933729 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part1_win_14 : ∀ i : ℕ, 252933730 ≤ i → i < 253133730 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 505867460) (x1 := 506267458) (lo := 505867529) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_15 : ∀ i : ℕ, 253133730 ≤ i → i < 253160514 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 506267460) (x1 := 506321026) (lo := 506267529) (W := 164639)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_253160514 : ∀ i : ℕ, 253160514 ≤ i → i < 253160515 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 253160514 := by omega
  subst hi
  exact ⟨127301, by decide, by norm_num⟩
private theorem c_part1_win_17 : ∀ i : ℕ, 253160515 ≤ i → i < 253351137 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 506321030) (x1 := 506702272) (lo := 506321099) (W := 492315)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_253351137 : ∀ i : ℕ, 253351137 ≤ i → i < 253351138 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 253351137 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part1_win_19 : ∀ i : ℕ, 253351138 ≤ i → i < 253551138 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 506702276) (x1 := 507102274) (lo := 506702345) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_20 : ∀ i : ℕ, 253551138 ≤ i → i < 253751138 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 507102276) (x1 := 507502274) (lo := 507102345) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_21 : ∀ i : ℕ, 253751138 ≤ i → i < 253836669 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 507502276) (x1 := 507673336) (lo := 507502345) (W := 282133)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_253836669 : ∀ i : ℕ, 253836669 ≤ i → i < 253836670 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 253836669 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part1_win_23 : ∀ i : ℕ, 253836670 ≤ i → i < 254036670 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 507673340) (x1 := 508073338) (lo := 507673409) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_24 : ∀ i : ℕ, 254036670 ≤ i → i < 254236670 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 508073340) (x1 := 508473338) (lo := 508073409) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_25 : ∀ i : ℕ, 254236670 ≤ i → i < 254313051 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 508473340) (x1 := 508626100) (lo := 508473409) (W := 263833)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_254313051 : ∀ i : ℕ, 254313051 ≤ i → i < 254313052 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 254313051 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part1_win_27 : ∀ i : ℕ, 254313052 ≤ i → i < 254513052 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 508626104) (x1 := 509026102) (lo := 508626173) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_28 : ∀ i : ℕ, 254513052 ≤ i → i < 254713052 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 509026104) (x1 := 509426102) (lo := 509026173) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_29 : ∀ i : ℕ, 254713052 ≤ i → i < 254809059 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 509426104) (x1 := 509618116) (lo := 509426173) (W := 303085)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_254809059 : ∀ i : ℕ, 254809059 ≤ i → i < 254809060 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 254809059 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part1_win_31 : ∀ i : ℕ, 254809060 ≤ i → i < 254971211 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 509618120) (x1 := 509942420) (lo := 509618189) (W := 435373)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_254971211 : ∀ i : ℕ, 254971211 ≤ i → i < 254971212 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 254971211 := by omega
  subst hi
  exact ⟨115317, by decide, by norm_num⟩
private theorem c_part1_win_33 : ∀ i : ℕ, 254971212 ≤ i → i < 255171212 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 509942424) (x1 := 510342422) (lo := 509942493) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_34 : ∀ i : ℕ, 255171212 ≤ i → i < 255371212 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 510342424) (x1 := 510742422) (lo := 510342493) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_35 : ∀ i : ℕ, 255371212 ≤ i → i < 255571212 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 510742424) (x1 := 511142422) (lo := 510742493) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_36 : ∀ i : ℕ, 255571212 ≤ i → i < 255621429 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 511142424) (x1 := 511242856) (lo := 511142493) (W := 211505)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_255621429 : ∀ i : ℕ, 255621429 ≤ i → i < 255621430 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 255621429 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part1_win_38 : ∀ i : ℕ, 255621430 ≤ i → i < 255821430 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 511242860) (x1 := 511642858) (lo := 511242929) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_39 : ∀ i : ℕ, 255821430 ≤ i → i < 256021430 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 511642860) (x1 := 512042858) (lo := 511642929) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_40 : ∀ i : ℕ, 256021430 ≤ i → i < 256098114 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512042860) (x1 := 512196226) (lo := 512042929) (W := 264439)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_256098114 : ∀ i : ℕ, 256098114 ≤ i → i < 256098115 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 256098114 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part1_win_42 : ∀ i : ℕ, 256098115 ≤ i → i < 256264271 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512196230) (x1 := 512528540) (lo := 512196299) (W := 443383)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_256264271 : ∀ i : ℕ, 256264271 ≤ i → i < 256264272 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 256264271 := by omega
  subst hi
  exact ⟨421491, by decide, by norm_num⟩
private theorem c_part1_win_44 : ∀ i : ℕ, 256264272 ≤ i → i < 256464272 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512528544) (x1 := 512928542) (lo := 512528613) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_45 : ∀ i : ℕ, 256464272 ≤ i → i < 256493553 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512928544) (x1 := 512987104) (lo := 512928613) (W := 169633)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_256493553 : ∀ i : ℕ, 256493553 ≤ i → i < 256493554 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 256493553 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part1_win_47 : ∀ i : ℕ, 256493554 ≤ i → i < 256566153 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512987108) (x1 := 513132304) (lo := 512987177) (W := 256269)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_256566153 : ∀ i : ℕ, 256566153 ≤ i → i < 256566154 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 256566153 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part1_win_49 : ∀ i : ℕ, 256566154 ≤ i → i < 256766154 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 513132308) (x1 := 513532306) (lo := 513132377) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_50 : ∀ i : ℕ, 256766154 ≤ i → i < 256966154 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 513532308) (x1 := 513932306) (lo := 513532377) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_51 : ∀ i : ℕ, 256966154 ≤ i → i < 256991981 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 513932308) (x1 := 513983960) (lo := 513932377) (W := 162725)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_256991981 : ∀ i : ℕ, 256991981 ≤ i → i < 256991982 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 256991981 := by omega
  subst hi
  exact ⟨126429, by decide, by norm_num⟩
private theorem c_part1_win_53 : ∀ i : ℕ, 256991982 ≤ i → i < 257191982 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 513983964) (x1 := 514383962) (lo := 513984033) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_54 : ∀ i : ℕ, 257191982 ≤ i → i < 257269746 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 514383964) (x1 := 514539490) (lo := 514384033) (W := 266599)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_257269746 : ∀ i : ℕ, 257269746 ≤ i → i < 257269747 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 257269746 := by omega
  subst hi
  exact ⟨127301, by decide, by norm_num⟩
private theorem c_part1_win_56 : ∀ i : ℕ, 257269747 ≤ i → i < 257469747 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 514539494) (x1 := 514939492) (lo := 514539563) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_57 : ∀ i : ℕ, 257469747 ≤ i → i < 257596352 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 514939494) (x1 := 515192702) (lo := 514939563) (W := 364281)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_257596352 : ∀ i : ℕ, 257596352 ≤ i → i < 257596353 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 257596352 := by omega
  subst hi
  exact ⟨115317, by decide, by norm_num⟩
private theorem c_part1_win_59 : ∀ i : ℕ, 257596353 ≤ i → i < 257796353 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 515192706) (x1 := 515592704) (lo := 515192775) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_60 : ∀ i : ℕ, 257796353 ≤ i → i < 257856399 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 515592706) (x1 := 515712796) (lo := 515592775) (W := 231163)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_257856399 : ∀ i : ℕ, 257856399 ≤ i → i < 257856400 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 257856399 := by omega
  subst hi
  exact ⟨123533, by decide, by norm_num⟩
private theorem c_part1_win_62 : ∀ i : ℕ, 257856400 ≤ i → i < 258056400 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 515712800) (x1 := 516112798) (lo := 515712869) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_63 : ∀ i : ℕ, 258056400 ≤ i → i < 258256400 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 516112800) (x1 := 516512798) (lo := 516112869) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_64 : ∀ i : ℕ, 258256400 ≤ i → i < 258341202 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 516512800) (x1 := 516682402) (lo := 516512869) (W := 280675)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_258341202 : ∀ i : ℕ, 258341202 ≤ i → i < 258341203 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 258341202 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part1_win_66 : ∀ i : ℕ, 258341203 ≤ i → i < 258541203 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 516682406) (x1 := 517082404) (lo := 516682475) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_67 : ∀ i : ℕ, 258541203 ≤ i → i < 258741203 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 517082406) (x1 := 517482404) (lo := 517082475) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_68 : ∀ i : ℕ, 258741203 ≤ i → i < 258864897 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 517482406) (x1 := 517729792) (lo := 517482475) (W := 358459)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_258864897 : ∀ i : ℕ, 258864897 ≤ i → i < 258864898 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 258864897 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part1_win_70 : ∀ i : ℕ, 258864898 ≤ i → i < 259064898 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 517729796) (x1 := 518129794) (lo := 517729865) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_71 : ∀ i : ℕ, 259064898 ≤ i → i < 259264898 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 518129796) (x1 := 518529794) (lo := 518129865) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_72 : ∀ i : ℕ, 259264898 ≤ i → i < 259464898 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 518529796) (x1 := 518929794) (lo := 518529865) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_73 : ∀ i : ℕ, 259464898 ≤ i → i < 259485774 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 518929796) (x1 := 518971546) (lo := 518929865) (W := 152823)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_259485774 : ∀ i : ℕ, 259485774 ≤ i → i < 259485775 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 259485774 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part1_win_75 : ∀ i : ℕ, 259485775 ≤ i → i < 259685775 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 518971550) (x1 := 519371548) (lo := 518971619) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_76 : ∀ i : ℕ, 259685775 ≤ i → i < 259885775 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 519371550) (x1 := 519771548) (lo := 519371619) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_77 : ∀ i : ℕ, 259885775 ≤ i → i < 260085775 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 519771550) (x1 := 520171548) (lo := 519771619) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_78 : ∀ i : ℕ, 260085775 ≤ i → i < 260130099 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 520171550) (x1 := 520260196) (lo := 520171619) (W := 199719)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_res_260130099 : ∀ i : ℕ, 260130099 ≤ i → i < 260130100 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 260130099 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part1_win_80 : ∀ i : ℕ, 260130100 ≤ i → i < 260330100 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 520260200) (x1 := 520660198) (lo := 520260269) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_81 : ∀ i : ℕ, 260330100 ≤ i → i < 260530100 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 520660200) (x1 := 521060198) (lo := 520660269) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_82 : ∀ i : ℕ, 260530100 ≤ i → i < 260730100 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 521060200) (x1 := 521460198) (lo := 521060269) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_83 : ∀ i : ℕ, 260730100 ≤ i → i < 260930100 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 521460200) (x1 := 521860198) (lo := 521460269) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_win_84 : ∀ i : ℕ, 260930100 ≤ i → i < 261000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 521860200) (x1 := 521999998) (lo := 521860269) (W := 250871)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part1_all : ∀ i : ℕ, 251000000 ≤ i → i < 261000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hlo hi
  by_cases h0 : i < 251200000
  · exact c_part1_win_0 i hlo h0
  by_cases h1 : i < 251400000
  · exact c_part1_win_1 i (Nat.not_lt.mp h0) h1
  by_cases h2 : i < 251496054
  · exact c_part1_win_2 i (Nat.not_lt.mp h1) h2
  by_cases h3 : i < 251496055
  · exact c_part1_res_251496054 i (Nat.not_lt.mp h2) h3
  by_cases h4 : i < 251696055
  · exact c_part1_win_4 i (Nat.not_lt.mp h3) h4
  by_cases h5 : i < 251896055
  · exact c_part1_win_5 i (Nat.not_lt.mp h4) h5
  by_cases h6 : i < 252096055
  · exact c_part1_win_6 i (Nat.not_lt.mp h5) h6
  by_cases h7 : i < 252296055
  · exact c_part1_win_7 i (Nat.not_lt.mp h6) h7
  by_cases h8 : i < 252496055
  · exact c_part1_win_8 i (Nat.not_lt.mp h7) h8
  by_cases h9 : i < 252696055
  · exact c_part1_win_9 i (Nat.not_lt.mp h8) h9
  by_cases h10 : i < 252748974
  · exact c_part1_win_10 i (Nat.not_lt.mp h9) h10
  by_cases h11 : i < 252748975
  · exact c_part1_res_252748974 i (Nat.not_lt.mp h10) h11
  by_cases h12 : i < 252933729
  · exact c_part1_win_12 i (Nat.not_lt.mp h11) h12
  by_cases h13 : i < 252933730
  · exact c_part1_res_252933729 i (Nat.not_lt.mp h12) h13
  by_cases h14 : i < 253133730
  · exact c_part1_win_14 i (Nat.not_lt.mp h13) h14
  by_cases h15 : i < 253160514
  · exact c_part1_win_15 i (Nat.not_lt.mp h14) h15
  by_cases h16 : i < 253160515
  · exact c_part1_res_253160514 i (Nat.not_lt.mp h15) h16
  by_cases h17 : i < 253351137
  · exact c_part1_win_17 i (Nat.not_lt.mp h16) h17
  by_cases h18 : i < 253351138
  · exact c_part1_res_253351137 i (Nat.not_lt.mp h17) h18
  by_cases h19 : i < 253551138
  · exact c_part1_win_19 i (Nat.not_lt.mp h18) h19
  by_cases h20 : i < 253751138
  · exact c_part1_win_20 i (Nat.not_lt.mp h19) h20
  by_cases h21 : i < 253836669
  · exact c_part1_win_21 i (Nat.not_lt.mp h20) h21
  by_cases h22 : i < 253836670
  · exact c_part1_res_253836669 i (Nat.not_lt.mp h21) h22
  by_cases h23 : i < 254036670
  · exact c_part1_win_23 i (Nat.not_lt.mp h22) h23
  by_cases h24 : i < 254236670
  · exact c_part1_win_24 i (Nat.not_lt.mp h23) h24
  by_cases h25 : i < 254313051
  · exact c_part1_win_25 i (Nat.not_lt.mp h24) h25
  by_cases h26 : i < 254313052
  · exact c_part1_res_254313051 i (Nat.not_lt.mp h25) h26
  by_cases h27 : i < 254513052
  · exact c_part1_win_27 i (Nat.not_lt.mp h26) h27
  by_cases h28 : i < 254713052
  · exact c_part1_win_28 i (Nat.not_lt.mp h27) h28
  by_cases h29 : i < 254809059
  · exact c_part1_win_29 i (Nat.not_lt.mp h28) h29
  by_cases h30 : i < 254809060
  · exact c_part1_res_254809059 i (Nat.not_lt.mp h29) h30
  by_cases h31 : i < 254971211
  · exact c_part1_win_31 i (Nat.not_lt.mp h30) h31
  by_cases h32 : i < 254971212
  · exact c_part1_res_254971211 i (Nat.not_lt.mp h31) h32
  by_cases h33 : i < 255171212
  · exact c_part1_win_33 i (Nat.not_lt.mp h32) h33
  by_cases h34 : i < 255371212
  · exact c_part1_win_34 i (Nat.not_lt.mp h33) h34
  by_cases h35 : i < 255571212
  · exact c_part1_win_35 i (Nat.not_lt.mp h34) h35
  by_cases h36 : i < 255621429
  · exact c_part1_win_36 i (Nat.not_lt.mp h35) h36
  by_cases h37 : i < 255621430
  · exact c_part1_res_255621429 i (Nat.not_lt.mp h36) h37
  by_cases h38 : i < 255821430
  · exact c_part1_win_38 i (Nat.not_lt.mp h37) h38
  by_cases h39 : i < 256021430
  · exact c_part1_win_39 i (Nat.not_lt.mp h38) h39
  by_cases h40 : i < 256098114
  · exact c_part1_win_40 i (Nat.not_lt.mp h39) h40
  by_cases h41 : i < 256098115
  · exact c_part1_res_256098114 i (Nat.not_lt.mp h40) h41
  by_cases h42 : i < 256264271
  · exact c_part1_win_42 i (Nat.not_lt.mp h41) h42
  by_cases h43 : i < 256264272
  · exact c_part1_res_256264271 i (Nat.not_lt.mp h42) h43
  by_cases h44 : i < 256464272
  · exact c_part1_win_44 i (Nat.not_lt.mp h43) h44
  by_cases h45 : i < 256493553
  · exact c_part1_win_45 i (Nat.not_lt.mp h44) h45
  by_cases h46 : i < 256493554
  · exact c_part1_res_256493553 i (Nat.not_lt.mp h45) h46
  by_cases h47 : i < 256566153
  · exact c_part1_win_47 i (Nat.not_lt.mp h46) h47
  by_cases h48 : i < 256566154
  · exact c_part1_res_256566153 i (Nat.not_lt.mp h47) h48
  by_cases h49 : i < 256766154
  · exact c_part1_win_49 i (Nat.not_lt.mp h48) h49
  by_cases h50 : i < 256966154
  · exact c_part1_win_50 i (Nat.not_lt.mp h49) h50
  by_cases h51 : i < 256991981
  · exact c_part1_win_51 i (Nat.not_lt.mp h50) h51
  by_cases h52 : i < 256991982
  · exact c_part1_res_256991981 i (Nat.not_lt.mp h51) h52
  by_cases h53 : i < 257191982
  · exact c_part1_win_53 i (Nat.not_lt.mp h52) h53
  by_cases h54 : i < 257269746
  · exact c_part1_win_54 i (Nat.not_lt.mp h53) h54
  by_cases h55 : i < 257269747
  · exact c_part1_res_257269746 i (Nat.not_lt.mp h54) h55
  by_cases h56 : i < 257469747
  · exact c_part1_win_56 i (Nat.not_lt.mp h55) h56
  by_cases h57 : i < 257596352
  · exact c_part1_win_57 i (Nat.not_lt.mp h56) h57
  by_cases h58 : i < 257596353
  · exact c_part1_res_257596352 i (Nat.not_lt.mp h57) h58
  by_cases h59 : i < 257796353
  · exact c_part1_win_59 i (Nat.not_lt.mp h58) h59
  by_cases h60 : i < 257856399
  · exact c_part1_win_60 i (Nat.not_lt.mp h59) h60
  by_cases h61 : i < 257856400
  · exact c_part1_res_257856399 i (Nat.not_lt.mp h60) h61
  by_cases h62 : i < 258056400
  · exact c_part1_win_62 i (Nat.not_lt.mp h61) h62
  by_cases h63 : i < 258256400
  · exact c_part1_win_63 i (Nat.not_lt.mp h62) h63
  by_cases h64 : i < 258341202
  · exact c_part1_win_64 i (Nat.not_lt.mp h63) h64
  by_cases h65 : i < 258341203
  · exact c_part1_res_258341202 i (Nat.not_lt.mp h64) h65
  by_cases h66 : i < 258541203
  · exact c_part1_win_66 i (Nat.not_lt.mp h65) h66
  by_cases h67 : i < 258741203
  · exact c_part1_win_67 i (Nat.not_lt.mp h66) h67
  by_cases h68 : i < 258864897
  · exact c_part1_win_68 i (Nat.not_lt.mp h67) h68
  by_cases h69 : i < 258864898
  · exact c_part1_res_258864897 i (Nat.not_lt.mp h68) h69
  by_cases h70 : i < 259064898
  · exact c_part1_win_70 i (Nat.not_lt.mp h69) h70
  by_cases h71 : i < 259264898
  · exact c_part1_win_71 i (Nat.not_lt.mp h70) h71
  by_cases h72 : i < 259464898
  · exact c_part1_win_72 i (Nat.not_lt.mp h71) h72
  by_cases h73 : i < 259485774
  · exact c_part1_win_73 i (Nat.not_lt.mp h72) h73
  by_cases h74 : i < 259485775
  · exact c_part1_res_259485774 i (Nat.not_lt.mp h73) h74
  by_cases h75 : i < 259685775
  · exact c_part1_win_75 i (Nat.not_lt.mp h74) h75
  by_cases h76 : i < 259885775
  · exact c_part1_win_76 i (Nat.not_lt.mp h75) h76
  by_cases h77 : i < 260085775
  · exact c_part1_win_77 i (Nat.not_lt.mp h76) h77
  by_cases h78 : i < 260130099
  · exact c_part1_win_78 i (Nat.not_lt.mp h77) h78
  by_cases h79 : i < 260130100
  · exact c_part1_res_260130099 i (Nat.not_lt.mp h78) h79
  by_cases h80 : i < 260330100
  · exact c_part1_win_80 i (Nat.not_lt.mp h79) h80
  by_cases h81 : i < 260530100
  · exact c_part1_win_81 i (Nat.not_lt.mp h80) h81
  by_cases h82 : i < 260730100
  · exact c_part1_win_82 i (Nat.not_lt.mp h81) h82
  by_cases h83 : i < 260930100
  · exact c_part1_win_83 i (Nat.not_lt.mp h82) h83
  exact c_part1_win_84 i (Nat.not_lt.mp h83) hi

private theorem c_part2_win_0 : ∀ i : ℕ, 261000000 ≤ i → i < 261050193 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 522000000) (x1 := 522100384) (lo := 522000069) (W := 211457)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_261050193 : ∀ i : ℕ, 261050193 ≤ i → i < 261050194 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 261050193 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part2_win_2 : ∀ i : ℕ, 261050194 ≤ i → i < 261250194 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 522100388) (x1 := 522500386) (lo := 522100457) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_3 : ∀ i : ℕ, 261250194 ≤ i → i < 261450194 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 522500388) (x1 := 522900386) (lo := 522500457) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_4 : ∀ i : ℕ, 261450194 ≤ i → i < 261650194 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 522900388) (x1 := 523300386) (lo := 522900457) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_5 : ∀ i : ℕ, 261650194 ≤ i → i < 261676667 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 523300388) (x1 := 523353332) (lo := 523300457) (W := 164017)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_261676667 : ∀ i : ℕ, 261676667 ≤ i → i < 261676668 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 261676667 := by omega
  subst hi
  exact ⟨111213, by decide, by norm_num⟩
private theorem c_part2_win_7 : ∀ i : ℕ, 261676668 ≤ i → i < 261876668 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 523353336) (x1 := 523753334) (lo := 523353405) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_8 : ∀ i : ℕ, 261876668 ≤ i → i < 261980199 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 523753336) (x1 := 523960396) (lo := 523753405) (W := 318133)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_261980199 : ∀ i : ℕ, 261980199 ≤ i → i < 261980200 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 261980199 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part2_win_10 : ∀ i : ℕ, 261980200 ≤ i → i < 261998589 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 523960400) (x1 := 523997176) (lo := 523960469) (W := 147849)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_261998589 : ∀ i : ℕ, 261998589 ≤ i → i < 261998590 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 261998589 := by omega
  subst hi
  exact ⟨127301, by decide, by norm_num⟩
private theorem c_part2_win_12 : ∀ i : ℕ, 261998590 ≤ i → i < 262198590 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 523997180) (x1 := 524397178) (lo := 523997249) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_13 : ∀ i : ℕ, 262198590 ≤ i → i < 262398590 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 524397180) (x1 := 524797178) (lo := 524397249) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_14 : ∀ i : ℕ, 262398590 ≤ i → i < 262569033 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 524797180) (x1 := 525138064) (lo := 524797249) (W := 451957)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_262569033 : ∀ i : ℕ, 262569033 ≤ i → i < 262569034 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 262569033 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part2_win_16 : ∀ i : ℕ, 262569034 ≤ i → i < 262769034 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 525138068) (x1 := 525538066) (lo := 525138137) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_17 : ∀ i : ℕ, 262769034 ≤ i → i < 262849577 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 525538068) (x1 := 525699152) (lo := 525538137) (W := 272157)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_262849577 : ∀ i : ℕ, 262849577 ≤ i → i < 262849578 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 262849577 := by omega
  subst hi
  exact ⟨118107, by decide, by norm_num⟩
private theorem c_part2_win_19 : ∀ i : ℕ, 262849578 ≤ i → i < 263049578 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 525699156) (x1 := 526099154) (lo := 525699225) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_20 : ∀ i : ℕ, 263049578 ≤ i → i < 263249578 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 526099156) (x1 := 526499154) (lo := 526099225) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_21 : ∀ i : ℕ, 263249578 ≤ i → i < 263279067 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 526499156) (x1 := 526558132) (lo := 526499225) (W := 170049)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_263279067 : ∀ i : ℕ, 263279067 ≤ i → i < 263279068 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 263279067 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part2_win_23 : ∀ i : ℕ, 263279068 ≤ i → i < 263479068 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 526558136) (x1 := 526958134) (lo := 526558205) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_24 : ∀ i : ℕ, 263479068 ≤ i → i < 263513682 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 526958136) (x1 := 527027362) (lo := 526958205) (W := 180299)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_263513682 : ∀ i : ℕ, 263513682 ≤ i → i < 263513683 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 263513682 := by omega
  subst hi
  exact ⟨1668413, by decide, by norm_num⟩
private theorem c_part2_win_26 : ∀ i : ℕ, 263513683 ≤ i → i < 263713683 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 527027366) (x1 := 527427364) (lo := 527027435) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_27 : ∀ i : ℕ, 263713683 ≤ i → i < 263913683 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 527427366) (x1 := 527827364) (lo := 527427435) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_28 : ∀ i : ℕ, 263913683 ≤ i → i < 264113683 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 527827366) (x1 := 528227364) (lo := 527827435) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_29 : ∀ i : ℕ, 264113683 ≤ i → i < 264313683 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 528227366) (x1 := 528627364) (lo := 528227435) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_30 : ∀ i : ℕ, 264313683 ≤ i → i < 264331428 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 528627366) (x1 := 528662854) (lo := 528627435) (W := 146561)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_264331428 : ∀ i : ℕ, 264331428 ≤ i → i < 264331429 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 264331428 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part2_win_32 : ∀ i : ℕ, 264331429 ≤ i → i < 264531429 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 528662858) (x1 := 529062856) (lo := 528662927) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_33 : ∀ i : ℕ, 264531429 ≤ i → i < 264731429 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 529062858) (x1 := 529462856) (lo := 529062927) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_34 : ∀ i : ℕ, 264731429 ≤ i → i < 264830721 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 529462858) (x1 := 529661440) (lo := 529462927) (W := 309655)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_264830721 : ∀ i : ℕ, 264830721 ≤ i → i < 264830722 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 264830721 := by omega
  subst hi
  exact ⟨125219, by decide, by norm_num⟩
private theorem c_part2_win_36 : ∀ i : ℕ, 264830722 ≤ i → i < 264919602 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 529661444) (x1 := 529839202) (lo := 529661513) (W := 288831)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_264919602 : ∀ i : ℕ, 264919602 ≤ i → i < 264919603 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 264919602 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part2_win_38 : ∀ i : ℕ, 264919603 ≤ i → i < 265119603 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 529839206) (x1 := 530239204) (lo := 529839275) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_39 : ∀ i : ℕ, 265119603 ≤ i → i < 265319603 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 530239206) (x1 := 530639204) (lo := 530239275) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_40 : ∀ i : ℕ, 265319603 ≤ i → i < 265519603 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 530639206) (x1 := 531039204) (lo := 530639275) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_41 : ∀ i : ℕ, 265519603 ≤ i → i < 265573404 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531039206) (x1 := 531146806) (lo := 531039275) (W := 218673)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_265573404 : ∀ i : ℕ, 265573404 ≤ i → i < 265573405 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 265573404 := by omega
  subst hi
  exact ⟨1668413, by decide, by norm_num⟩
private theorem c_part2_win_43 : ∀ i : ℕ, 265573405 ≤ i → i < 265773405 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531146810) (x1 := 531546808) (lo := 531146879) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_44 : ∀ i : ℕ, 265773405 ≤ i → i < 265973405 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531546810) (x1 := 531946808) (lo := 531546879) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_45 : ∀ i : ℕ, 265973405 ≤ i → i < 266173405 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531946810) (x1 := 532346808) (lo := 531946879) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_46 : ∀ i : ℕ, 266173405 ≤ i → i < 266213381 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 532346810) (x1 := 532426760) (lo := 532346879) (W := 191023)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_266213381 : ∀ i : ℕ, 266213381 ≤ i → i < 266213382 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 266213381 := by omega
  subst hi
  exact ⟨115317, by decide, by norm_num⟩
private theorem c_part2_win_48 : ∀ i : ℕ, 266213382 ≤ i → i < 266413382 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 532426764) (x1 := 532826762) (lo := 532426833) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_49 : ∀ i : ℕ, 266413382 ≤ i → i < 266613382 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 532826764) (x1 := 533226762) (lo := 532826833) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_50 : ∀ i : ℕ, 266613382 ≤ i → i < 266813382 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 533226764) (x1 := 533626762) (lo := 533226833) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_51 : ∀ i : ℕ, 266813382 ≤ i → i < 266853843 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 533626764) (x1 := 533707684) (lo := 533626833) (W := 191993)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_266853843 : ∀ i : ℕ, 266853843 ≤ i → i < 266853844 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 266853843 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part2_win_53 : ∀ i : ℕ, 266853844 ≤ i → i < 267053844 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 533707688) (x1 := 534107686) (lo := 533707757) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_54 : ∀ i : ℕ, 267053844 ≤ i → i < 267079293 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 534107688) (x1 := 534158584) (lo := 534107757) (W := 161969)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_267079293 : ∀ i : ℕ, 267079293 ≤ i → i < 267079294 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 267079293 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part2_win_56 : ∀ i : ℕ, 267079294 ≤ i → i < 267185499 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 534158588) (x1 := 534370996) (lo := 534158657) (W := 323481)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_267185499 : ∀ i : ℕ, 267185499 ≤ i → i < 267185500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 267185499 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part2_win_58 : ∀ i : ℕ, 267185500 ≤ i → i < 267385500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 534371000) (x1 := 534770998) (lo := 534371069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_59 : ∀ i : ℕ, 267385500 ≤ i → i < 267585500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 534771000) (x1 := 535170998) (lo := 534771069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_60 : ∀ i : ℕ, 267585500 ≤ i → i < 267785500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 535171000) (x1 := 535570998) (lo := 535171069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_61 : ∀ i : ℕ, 267785500 ≤ i → i < 267985500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 535571000) (x1 := 535970998) (lo := 535571069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_62 : ∀ i : ℕ, 267985500 ≤ i → i < 268011609 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 535971000) (x1 := 536023216) (lo := 535971069) (W := 163289)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_268011609 : ∀ i : ℕ, 268011609 ≤ i → i < 268011610 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 268011609 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part2_win_64 : ∀ i : ℕ, 268011610 ≤ i → i < 268127649 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 536023220) (x1 := 536255296) (lo := 536023289) (W := 343149)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_268127649 : ∀ i : ℕ, 268127649 ≤ i → i < 268127650 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 268127649 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part2_win_66 : ∀ i : ℕ, 268127650 ≤ i → i < 268327650 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 536255300) (x1 := 536655298) (lo := 536255369) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_67 : ∀ i : ℕ, 268327650 ≤ i → i < 268527650 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 536655300) (x1 := 537055298) (lo := 536655369) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_68 : ∀ i : ℕ, 268527650 ≤ i → i < 268727650 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 537055300) (x1 := 537455298) (lo := 537055369) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_69 : ∀ i : ℕ, 268727650 ≤ i → i < 268896597 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 537455300) (x1 := 537793192) (lo := 537455369) (W := 448965)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_268896597 : ∀ i : ℕ, 268896597 ≤ i → i < 268896598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 268896597 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part2_win_71 : ∀ i : ℕ, 268896598 ≤ i → i < 269096598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 537793196) (x1 := 538193194) (lo := 537793265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_72 : ∀ i : ℕ, 269096598 ≤ i → i < 269213412 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538193196) (x1 := 538426822) (lo := 538193265) (W := 344699)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_269213412 : ∀ i : ℕ, 269213412 ≤ i → i < 269213413 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 269213412 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part2_win_74 : ∀ i : ℕ, 269213413 ≤ i → i < 269250312 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538426826) (x1 := 538500622) (lo := 538426895) (W := 184869)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_269250312 : ∀ i : ℕ, 269250312 ≤ i → i < 269250313 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 269250312 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part2_win_76 : ∀ i : ℕ, 269250313 ≤ i → i < 269338358 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538500626) (x1 := 538676714) (lo := 538500695) (W := 287161)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_269338358 : ∀ i : ℕ, 269338358 ≤ i → i < 269338359 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 269338358 := by omega
  subst hi
  exact ⟨158457, by decide, by norm_num⟩
private theorem c_part2_win_78 : ∀ i : ℕ, 269338359 ≤ i → i < 269538359 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538676718) (x1 := 539076716) (lo := 538676787) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_79 : ∀ i : ℕ, 269538359 ≤ i → i < 269738359 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 539076718) (x1 := 539476716) (lo := 539076787) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_80 : ∀ i : ℕ, 269738359 ≤ i → i < 269938359 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 539476718) (x1 := 539876716) (lo := 539476787) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_81 : ∀ i : ℕ, 269938359 ≤ i → i < 270138359 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 539876718) (x1 := 540276716) (lo := 539876787) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_82 : ∀ i : ℕ, 270138359 ≤ i → i < 270218859 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 540276718) (x1 := 540437716) (lo := 540276787) (W := 272071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_270218859 : ∀ i : ℕ, 270218859 ≤ i → i < 270218860 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 270218859 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part2_win_84 : ∀ i : ℕ, 270218860 ≤ i → i < 270418860 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 540437720) (x1 := 540837718) (lo := 540437789) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_win_85 : ∀ i : ℕ, 270418860 ≤ i → i < 270508719 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 540837720) (x1 := 541017436) (lo := 540837789) (W := 290789)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_270508719 : ∀ i : ℕ, 270508719 ≤ i → i < 270508720 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 270508719 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part2_win_87 : ∀ i : ℕ, 270508720 ≤ i → i < 270527079 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 541017440) (x1 := 541054156) (lo := 541017509) (W := 147789)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_270527079 : ∀ i : ℕ, 270527079 ≤ i → i < 270527080 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 270527079 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part2_win_89 : ∀ i : ℕ, 270527080 ≤ i → i < 270717944 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 541054160) (x1 := 541435886) (lo := 541054229) (W := 492799)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_270717944 : ∀ i : ℕ, 270717944 ≤ i → i < 270717945 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 270717944 := by omega
  subst hi
  exact ⟨117039, by decide, by norm_num⟩
private theorem c_part2_win_91 : ∀ i : ℕ, 270717945 ≤ i → i < 270877893 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 541435890) (x1 := 541755784) (lo := 541435959) (W := 430967)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_res_270877893 : ∀ i : ℕ, 270877893 ≤ i → i < 270877894 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 270877893 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part2_win_93 : ∀ i : ℕ, 270877894 ≤ i → i < 271000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 541755788) (x1 := 541999998) (lo := 541755857) (W := 355283)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part2_all : ∀ i : ℕ, 261000000 ≤ i → i < 271000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hlo hi
  by_cases h0 : i < 261050193
  · exact c_part2_win_0 i hlo h0
  by_cases h1 : i < 261050194
  · exact c_part2_res_261050193 i (Nat.not_lt.mp h0) h1
  by_cases h2 : i < 261250194
  · exact c_part2_win_2 i (Nat.not_lt.mp h1) h2
  by_cases h3 : i < 261450194
  · exact c_part2_win_3 i (Nat.not_lt.mp h2) h3
  by_cases h4 : i < 261650194
  · exact c_part2_win_4 i (Nat.not_lt.mp h3) h4
  by_cases h5 : i < 261676667
  · exact c_part2_win_5 i (Nat.not_lt.mp h4) h5
  by_cases h6 : i < 261676668
  · exact c_part2_res_261676667 i (Nat.not_lt.mp h5) h6
  by_cases h7 : i < 261876668
  · exact c_part2_win_7 i (Nat.not_lt.mp h6) h7
  by_cases h8 : i < 261980199
  · exact c_part2_win_8 i (Nat.not_lt.mp h7) h8
  by_cases h9 : i < 261980200
  · exact c_part2_res_261980199 i (Nat.not_lt.mp h8) h9
  by_cases h10 : i < 261998589
  · exact c_part2_win_10 i (Nat.not_lt.mp h9) h10
  by_cases h11 : i < 261998590
  · exact c_part2_res_261998589 i (Nat.not_lt.mp h10) h11
  by_cases h12 : i < 262198590
  · exact c_part2_win_12 i (Nat.not_lt.mp h11) h12
  by_cases h13 : i < 262398590
  · exact c_part2_win_13 i (Nat.not_lt.mp h12) h13
  by_cases h14 : i < 262569033
  · exact c_part2_win_14 i (Nat.not_lt.mp h13) h14
  by_cases h15 : i < 262569034
  · exact c_part2_res_262569033 i (Nat.not_lt.mp h14) h15
  by_cases h16 : i < 262769034
  · exact c_part2_win_16 i (Nat.not_lt.mp h15) h16
  by_cases h17 : i < 262849577
  · exact c_part2_win_17 i (Nat.not_lt.mp h16) h17
  by_cases h18 : i < 262849578
  · exact c_part2_res_262849577 i (Nat.not_lt.mp h17) h18
  by_cases h19 : i < 263049578
  · exact c_part2_win_19 i (Nat.not_lt.mp h18) h19
  by_cases h20 : i < 263249578
  · exact c_part2_win_20 i (Nat.not_lt.mp h19) h20
  by_cases h21 : i < 263279067
  · exact c_part2_win_21 i (Nat.not_lt.mp h20) h21
  by_cases h22 : i < 263279068
  · exact c_part2_res_263279067 i (Nat.not_lt.mp h21) h22
  by_cases h23 : i < 263479068
  · exact c_part2_win_23 i (Nat.not_lt.mp h22) h23
  by_cases h24 : i < 263513682
  · exact c_part2_win_24 i (Nat.not_lt.mp h23) h24
  by_cases h25 : i < 263513683
  · exact c_part2_res_263513682 i (Nat.not_lt.mp h24) h25
  by_cases h26 : i < 263713683
  · exact c_part2_win_26 i (Nat.not_lt.mp h25) h26
  by_cases h27 : i < 263913683
  · exact c_part2_win_27 i (Nat.not_lt.mp h26) h27
  by_cases h28 : i < 264113683
  · exact c_part2_win_28 i (Nat.not_lt.mp h27) h28
  by_cases h29 : i < 264313683
  · exact c_part2_win_29 i (Nat.not_lt.mp h28) h29
  by_cases h30 : i < 264331428
  · exact c_part2_win_30 i (Nat.not_lt.mp h29) h30
  by_cases h31 : i < 264331429
  · exact c_part2_res_264331428 i (Nat.not_lt.mp h30) h31
  by_cases h32 : i < 264531429
  · exact c_part2_win_32 i (Nat.not_lt.mp h31) h32
  by_cases h33 : i < 264731429
  · exact c_part2_win_33 i (Nat.not_lt.mp h32) h33
  by_cases h34 : i < 264830721
  · exact c_part2_win_34 i (Nat.not_lt.mp h33) h34
  by_cases h35 : i < 264830722
  · exact c_part2_res_264830721 i (Nat.not_lt.mp h34) h35
  by_cases h36 : i < 264919602
  · exact c_part2_win_36 i (Nat.not_lt.mp h35) h36
  by_cases h37 : i < 264919603
  · exact c_part2_res_264919602 i (Nat.not_lt.mp h36) h37
  by_cases h38 : i < 265119603
  · exact c_part2_win_38 i (Nat.not_lt.mp h37) h38
  by_cases h39 : i < 265319603
  · exact c_part2_win_39 i (Nat.not_lt.mp h38) h39
  by_cases h40 : i < 265519603
  · exact c_part2_win_40 i (Nat.not_lt.mp h39) h40
  by_cases h41 : i < 265573404
  · exact c_part2_win_41 i (Nat.not_lt.mp h40) h41
  by_cases h42 : i < 265573405
  · exact c_part2_res_265573404 i (Nat.not_lt.mp h41) h42
  by_cases h43 : i < 265773405
  · exact c_part2_win_43 i (Nat.not_lt.mp h42) h43
  by_cases h44 : i < 265973405
  · exact c_part2_win_44 i (Nat.not_lt.mp h43) h44
  by_cases h45 : i < 266173405
  · exact c_part2_win_45 i (Nat.not_lt.mp h44) h45
  by_cases h46 : i < 266213381
  · exact c_part2_win_46 i (Nat.not_lt.mp h45) h46
  by_cases h47 : i < 266213382
  · exact c_part2_res_266213381 i (Nat.not_lt.mp h46) h47
  by_cases h48 : i < 266413382
  · exact c_part2_win_48 i (Nat.not_lt.mp h47) h48
  by_cases h49 : i < 266613382
  · exact c_part2_win_49 i (Nat.not_lt.mp h48) h49
  by_cases h50 : i < 266813382
  · exact c_part2_win_50 i (Nat.not_lt.mp h49) h50
  by_cases h51 : i < 266853843
  · exact c_part2_win_51 i (Nat.not_lt.mp h50) h51
  by_cases h52 : i < 266853844
  · exact c_part2_res_266853843 i (Nat.not_lt.mp h51) h52
  by_cases h53 : i < 267053844
  · exact c_part2_win_53 i (Nat.not_lt.mp h52) h53
  by_cases h54 : i < 267079293
  · exact c_part2_win_54 i (Nat.not_lt.mp h53) h54
  by_cases h55 : i < 267079294
  · exact c_part2_res_267079293 i (Nat.not_lt.mp h54) h55
  by_cases h56 : i < 267185499
  · exact c_part2_win_56 i (Nat.not_lt.mp h55) h56
  by_cases h57 : i < 267185500
  · exact c_part2_res_267185499 i (Nat.not_lt.mp h56) h57
  by_cases h58 : i < 267385500
  · exact c_part2_win_58 i (Nat.not_lt.mp h57) h58
  by_cases h59 : i < 267585500
  · exact c_part2_win_59 i (Nat.not_lt.mp h58) h59
  by_cases h60 : i < 267785500
  · exact c_part2_win_60 i (Nat.not_lt.mp h59) h60
  by_cases h61 : i < 267985500
  · exact c_part2_win_61 i (Nat.not_lt.mp h60) h61
  by_cases h62 : i < 268011609
  · exact c_part2_win_62 i (Nat.not_lt.mp h61) h62
  by_cases h63 : i < 268011610
  · exact c_part2_res_268011609 i (Nat.not_lt.mp h62) h63
  by_cases h64 : i < 268127649
  · exact c_part2_win_64 i (Nat.not_lt.mp h63) h64
  by_cases h65 : i < 268127650
  · exact c_part2_res_268127649 i (Nat.not_lt.mp h64) h65
  by_cases h66 : i < 268327650
  · exact c_part2_win_66 i (Nat.not_lt.mp h65) h66
  by_cases h67 : i < 268527650
  · exact c_part2_win_67 i (Nat.not_lt.mp h66) h67
  by_cases h68 : i < 268727650
  · exact c_part2_win_68 i (Nat.not_lt.mp h67) h68
  by_cases h69 : i < 268896597
  · exact c_part2_win_69 i (Nat.not_lt.mp h68) h69
  by_cases h70 : i < 268896598
  · exact c_part2_res_268896597 i (Nat.not_lt.mp h69) h70
  by_cases h71 : i < 269096598
  · exact c_part2_win_71 i (Nat.not_lt.mp h70) h71
  by_cases h72 : i < 269213412
  · exact c_part2_win_72 i (Nat.not_lt.mp h71) h72
  by_cases h73 : i < 269213413
  · exact c_part2_res_269213412 i (Nat.not_lt.mp h72) h73
  by_cases h74 : i < 269250312
  · exact c_part2_win_74 i (Nat.not_lt.mp h73) h74
  by_cases h75 : i < 269250313
  · exact c_part2_res_269250312 i (Nat.not_lt.mp h74) h75
  by_cases h76 : i < 269338358
  · exact c_part2_win_76 i (Nat.not_lt.mp h75) h76
  by_cases h77 : i < 269338359
  · exact c_part2_res_269338358 i (Nat.not_lt.mp h76) h77
  by_cases h78 : i < 269538359
  · exact c_part2_win_78 i (Nat.not_lt.mp h77) h78
  by_cases h79 : i < 269738359
  · exact c_part2_win_79 i (Nat.not_lt.mp h78) h79
  by_cases h80 : i < 269938359
  · exact c_part2_win_80 i (Nat.not_lt.mp h79) h80
  by_cases h81 : i < 270138359
  · exact c_part2_win_81 i (Nat.not_lt.mp h80) h81
  by_cases h82 : i < 270218859
  · exact c_part2_win_82 i (Nat.not_lt.mp h81) h82
  by_cases h83 : i < 270218860
  · exact c_part2_res_270218859 i (Nat.not_lt.mp h82) h83
  by_cases h84 : i < 270418860
  · exact c_part2_win_84 i (Nat.not_lt.mp h83) h84
  by_cases h85 : i < 270508719
  · exact c_part2_win_85 i (Nat.not_lt.mp h84) h85
  by_cases h86 : i < 270508720
  · exact c_part2_res_270508719 i (Nat.not_lt.mp h85) h86
  by_cases h87 : i < 270527079
  · exact c_part2_win_87 i (Nat.not_lt.mp h86) h87
  by_cases h88 : i < 270527080
  · exact c_part2_res_270527079 i (Nat.not_lt.mp h87) h88
  by_cases h89 : i < 270717944
  · exact c_part2_win_89 i (Nat.not_lt.mp h88) h89
  by_cases h90 : i < 270717945
  · exact c_part2_res_270717944 i (Nat.not_lt.mp h89) h90
  by_cases h91 : i < 270877893
  · exact c_part2_win_91 i (Nat.not_lt.mp h90) h91
  by_cases h92 : i < 270877894
  · exact c_part2_res_270877893 i (Nat.not_lt.mp h91) h92
  exact c_part2_win_93 i (Nat.not_lt.mp h92) hi

private theorem c_part3_win_0 : ∀ i : ℕ, 271000000 ≤ i → i < 271200000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 542000000) (x1 := 542399998) (lo := 542000069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_1 : ∀ i : ℕ, 271200000 ≤ i → i < 271400000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 542400000) (x1 := 542799998) (lo := 542400069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_2 : ∀ i : ℕ, 271400000 ≤ i → i < 271560938 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 542800000) (x1 := 543121874) (lo := 542800069) (W := 432947)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_271560938 : ∀ i : ℕ, 271560938 ≤ i → i < 271560939 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 271560938 := by omega
  subst hi
  exact ⟨291297, by decide, by norm_num⟩
private theorem c_part3_win_4 : ∀ i : ℕ, 271560939 ≤ i → i < 271760939 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543121878) (x1 := 543521876) (lo := 543121947) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_5 : ∀ i : ℕ, 271760939 ≤ i → i < 271861224 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543521878) (x1 := 543722446) (lo := 543521947) (W := 311641)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_271861224 : ∀ i : ℕ, 271861224 ≤ i → i < 271861225 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 271861224 := by omega
  subst hi
  exact ⟨1334189, by decide, by norm_num⟩
private theorem c_part3_win_7 : ∀ i : ℕ, 271861225 ≤ i → i < 271979280 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543722450) (x1 := 543958558) (lo := 543722519) (W := 347181)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_271979280 : ∀ i : ℕ, 271979280 ≤ i → i < 271979281 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 271979280 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part3_win_9 : ∀ i : ℕ, 271979281 ≤ i → i < 272002575 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543958562) (x1 := 544005148) (lo := 543958631) (W := 157659)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_272002575 : ∀ i : ℕ, 272002575 ≤ i → i < 272002576 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 272002575 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part3_win_11 : ∀ i : ℕ, 272002576 ≤ i → i < 272175399 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544005152) (x1 := 544350796) (lo := 544005221) (W := 456717)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_272175399 : ∀ i : ℕ, 272175399 ≤ i → i < 272175400 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 272175399 := by omega
  subst hi
  exact ⟨1334189, by decide, by norm_num⟩
private theorem c_part3_win_13 : ∀ i : ℕ, 272175400 ≤ i → i < 272354738 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544350800) (x1 := 544709474) (lo := 544350869) (W := 469747)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_272354738 : ∀ i : ℕ, 272354738 ≤ i → i < 272354739 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 272354738 := by omega
  subst hi
  exact ⟨158457, by decide, by norm_num⟩
private theorem c_part3_win_15 : ∀ i : ℕ, 272354739 ≤ i → i < 272507412 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544709478) (x1 := 545014822) (lo := 544709547) (W := 416417)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_272507412 : ∀ i : ℕ, 272507412 ≤ i → i < 272507413 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 272507412 := by omega
  subst hi
  exact ⟨116717, by decide, by norm_num⟩
private theorem c_part3_win_17 : ∀ i : ℕ, 272507413 ≤ i → i < 272707413 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 545014826) (x1 := 545414824) (lo := 545014895) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_18 : ∀ i : ℕ, 272707413 ≤ i → i < 272907413 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 545414826) (x1 := 545814824) (lo := 545414895) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_19 : ∀ i : ℕ, 272907413 ≤ i → i < 273107413 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 545814826) (x1 := 546214824) (lo := 545814895) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_20 : ∀ i : ℕ, 273107413 ≤ i → i < 273244437 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 546214826) (x1 := 546488872) (lo := 546214895) (W := 385119)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_273244437 : ∀ i : ℕ, 273244437 ≤ i → i < 273244438 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 273244437 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part3_win_22 : ∀ i : ℕ, 273244438 ≤ i → i < 273444438 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 546488876) (x1 := 546888874) (lo := 546488945) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_23 : ∀ i : ℕ, 273444438 ≤ i → i < 273644438 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 546888876) (x1 := 547288874) (lo := 546888945) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_24 : ∀ i : ℕ, 273644438 ≤ i → i < 273844438 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 547288876) (x1 := 547688874) (lo := 547288945) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_25 : ∀ i : ℕ, 273844438 ≤ i → i < 274044438 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 547688876) (x1 := 548088874) (lo := 547688945) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_26 : ∀ i : ℕ, 274044438 ≤ i → i < 274137581 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 548088876) (x1 := 548275160) (lo := 548088945) (W := 297357)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_274137581 : ∀ i : ℕ, 274137581 ≤ i → i < 274137582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 274137581 := by omega
  subst hi
  exact ⟨118419, by decide, by norm_num⟩
private theorem c_part3_win_28 : ∀ i : ℕ, 274137582 ≤ i → i < 274337582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 548275164) (x1 := 548675162) (lo := 548275233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_29 : ∀ i : ℕ, 274337582 ≤ i → i < 274537582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 548675164) (x1 := 549075162) (lo := 548675233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_30 : ∀ i : ℕ, 274537582 ≤ i → i < 274737582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 549075164) (x1 := 549475162) (lo := 549075233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_31 : ∀ i : ℕ, 274737582 ≤ i → i < 274937582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 549475164) (x1 := 549875162) (lo := 549475233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_32 : ∀ i : ℕ, 274937582 ≤ i → i < 275137582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 549875164) (x1 := 550275162) (lo := 549875233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_33 : ∀ i : ℕ, 275137582 ≤ i → i < 275337582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 550275164) (x1 := 550675162) (lo := 550275233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_34 : ∀ i : ℕ, 275337582 ≤ i → i < 275537582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 550675164) (x1 := 551075162) (lo := 550675233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_35 : ∀ i : ℕ, 275537582 ≤ i → i < 275737582 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 551075164) (x1 := 551475162) (lo := 551075233) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_36 : ∀ i : ℕ, 275737582 ≤ i → i < 275888439 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 551475164) (x1 := 551776876) (lo := 551475233) (W := 412785)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_275888439 : ∀ i : ℕ, 275888439 ≤ i → i < 275888440 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 275888439 := by omega
  subst hi
  exact ⟨123533, by decide, by norm_num⟩
private theorem c_part3_win_38 : ∀ i : ℕ, 275888440 ≤ i → i < 276088440 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 551776880) (x1 := 552176878) (lo := 551776949) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_39 : ∀ i : ℕ, 276088440 ≤ i → i < 276288440 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 552176880) (x1 := 552576878) (lo := 552176949) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_40 : ∀ i : ℕ, 276288440 ≤ i → i < 276488440 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 552576880) (x1 := 552976878) (lo := 552576949) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_41 : ∀ i : ℕ, 276488440 ≤ i → i < 276550689 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 552976880) (x1 := 553101376) (lo := 552976949) (W := 235569)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_276550689 : ∀ i : ℕ, 276550689 ≤ i → i < 276550690 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 276550689 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part3_win_43 : ∀ i : ℕ, 276550690 ≤ i → i < 276685869 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 553101380) (x1 := 553371736) (lo := 553101449) (W := 381429)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_276685869 : ∀ i : ℕ, 276685869 ≤ i → i < 276685870 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 276685869 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part3_win_45 : ∀ i : ℕ, 276685870 ≤ i → i < 276765927 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 553371740) (x1 := 553531852) (lo := 553371809) (W := 271185)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_276765927 : ∀ i : ℕ, 276765927 ≤ i → i < 276765928 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 276765927 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part3_win_47 : ∀ i : ℕ, 276765928 ≤ i → i < 276791291 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 553531856) (x1 := 553582580) (lo := 553531925) (W := 161797)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_276791291 : ∀ i : ℕ, 276791291 ≤ i → i < 276791292 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 276791291 := by omega
  subst hi
  exact ⟨132219, by decide, by norm_num⟩
private theorem c_part3_win_49 : ∀ i : ℕ, 276791292 ≤ i → i < 276991292 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 553582584) (x1 := 553982582) (lo := 553582653) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_50 : ∀ i : ℕ, 276991292 ≤ i → i < 277082499 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 553982584) (x1 := 554164996) (lo := 553982653) (W := 293485)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_277082499 : ∀ i : ℕ, 277082499 ≤ i → i < 277082500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 277082499 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part3_win_52 : ∀ i : ℕ, 277082500 ≤ i → i < 277282500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 554165000) (x1 := 554564998) (lo := 554165069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_53 : ∀ i : ℕ, 277282500 ≤ i → i < 277383747 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 554565000) (x1 := 554767492) (lo := 554565069) (W := 313565)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_277383747 : ∀ i : ℕ, 277383747 ≤ i → i < 277383748 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 277383747 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part3_win_55 : ∀ i : ℕ, 277383748 ≤ i → i < 277583748 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 554767496) (x1 := 555167494) (lo := 554767565) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_56 : ∀ i : ℕ, 277583748 ≤ i → i < 277598349 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 555167496) (x1 := 555196696) (lo := 555167565) (W := 140273)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_277598349 : ∀ i : ℕ, 277598349 ≤ i → i < 277598350 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 277598349 := by omega
  subst hi
  exact ⟨123533, by decide, by norm_num⟩
private theorem c_part3_win_58 : ∀ i : ℕ, 277598350 ≤ i → i < 277784484 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 555196700) (x1 := 555568966) (lo := 555196769) (W := 483339)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_277784484 : ∀ i : ℕ, 277784484 ≤ i → i < 277784485 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 277784484 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part3_win_60 : ∀ i : ℕ, 277784485 ≤ i → i < 277936152 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 555568970) (x1 := 555872302) (lo := 555569039) (W := 414405)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_277936152 : ∀ i : ℕ, 277936152 ≤ i → i < 277936153 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 277936152 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part3_win_62 : ∀ i : ℕ, 277936153 ≤ i → i < 278073501 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 555872306) (x1 := 556147000) (lo := 555872375) (W := 385767)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_278073501 : ∀ i : ℕ, 278073501 ≤ i → i < 278073502 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 278073501 := by omega
  subst hi
  exact ⟨131207, by decide, by norm_num⟩
private theorem c_part3_win_64 : ∀ i : ℕ, 278073502 ≤ i → i < 278273502 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 556147004) (x1 := 556547002) (lo := 556147073) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_65 : ∀ i : ℕ, 278273502 ≤ i → i < 278473502 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 556547004) (x1 := 556947002) (lo := 556547073) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_66 : ∀ i : ℕ, 278473502 ≤ i → i < 278670873 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 556947004) (x1 := 557341744) (lo := 556947073) (W := 505813)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_278670873 : ∀ i : ℕ, 278670873 ≤ i → i < 278670874 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 278670873 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part3_win_68 : ∀ i : ℕ, 278670874 ≤ i → i < 278870874 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 557341748) (x1 := 557741746) (lo := 557341817) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_69 : ∀ i : ℕ, 278870874 ≤ i → i < 279020061 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 557741748) (x1 := 558040120) (lo := 557741817) (W := 409445)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_279020061 : ∀ i : ℕ, 279020061 ≤ i → i < 279020062 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 279020061 := by omega
  subst hi
  exact ⟨125219, by decide, by norm_num⟩
private theorem c_part3_win_71 : ∀ i : ℕ, 279020062 ≤ i → i < 279220062 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 558040124) (x1 := 558440122) (lo := 558040193) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_72 : ∀ i : ℕ, 279220062 ≤ i → i < 279420062 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 558440124) (x1 := 558840122) (lo := 558440193) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_73 : ∀ i : ℕ, 279420062 ≤ i → i < 279620062 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 558840124) (x1 := 559240122) (lo := 558840193) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_74 : ∀ i : ℕ, 279620062 ≤ i → i < 279692979 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 559240124) (x1 := 559385956) (lo := 559240193) (W := 256905)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_279692979 : ∀ i : ℕ, 279692979 ≤ i → i < 279692980 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 279692979 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part3_win_76 : ∀ i : ℕ, 279692980 ≤ i → i < 279892980 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 559385960) (x1 := 559785958) (lo := 559386029) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_77 : ∀ i : ℕ, 279892980 ≤ i → i < 280092980 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 559785960) (x1 := 560185958) (lo := 559786029) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_78 : ∀ i : ℕ, 280092980 ≤ i → i < 280292980 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 560185960) (x1 := 560585958) (lo := 560186029) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_79 : ∀ i : ℕ, 280292980 ≤ i → i < 280461333 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 560585960) (x1 := 560922664) (lo := 560586029) (W := 447777)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_280461333 : ∀ i : ℕ, 280461333 ≤ i → i < 280461334 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 280461333 := by omega
  subst hi
  exact ⟨127301, by decide, by norm_num⟩
private theorem c_part3_win_81 : ∀ i : ℕ, 280461334 ≤ i → i < 280610097 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 560922668) (x1 := 561220192) (lo := 560922737) (W := 408597)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_280610097 : ∀ i : ℕ, 280610097 ≤ i → i < 280610098 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 280610097 := by omega
  subst hi
  exact ⟨116717, by decide, by norm_num⟩
private theorem c_part3_win_83 : ∀ i : ℕ, 280610098 ≤ i → i < 280647912 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 561220196) (x1 := 561295822) (lo := 561220265) (W := 186699)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_280647912 : ∀ i : ℕ, 280647912 ≤ i → i < 280647913 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 280647912 := by omega
  subst hi
  exact ⟨3166973, by decide, by norm_num⟩
private theorem c_part3_win_85 : ∀ i : ℕ, 280647913 ≤ i → i < 280652754 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 561295826) (x1 := 561305506) (lo := 561295895) (W := 120753)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_res_280652754 : ∀ i : ℕ, 280652754 ≤ i → i < 280652755 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 280652754 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part3_win_87 : ∀ i : ℕ, 280652755 ≤ i → i < 280852755 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 561305510) (x1 := 561705508) (lo := 561305579) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_win_88 : ∀ i : ℕ, 280852755 ≤ i → i < 281000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 561705510) (x1 := 561999998) (lo := 561705579) (W := 405561)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part3_all : ∀ i : ℕ, 271000000 ≤ i → i < 281000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hlo hi
  by_cases h0 : i < 271200000
  · exact c_part3_win_0 i hlo h0
  by_cases h1 : i < 271400000
  · exact c_part3_win_1 i (Nat.not_lt.mp h0) h1
  by_cases h2 : i < 271560938
  · exact c_part3_win_2 i (Nat.not_lt.mp h1) h2
  by_cases h3 : i < 271560939
  · exact c_part3_res_271560938 i (Nat.not_lt.mp h2) h3
  by_cases h4 : i < 271760939
  · exact c_part3_win_4 i (Nat.not_lt.mp h3) h4
  by_cases h5 : i < 271861224
  · exact c_part3_win_5 i (Nat.not_lt.mp h4) h5
  by_cases h6 : i < 271861225
  · exact c_part3_res_271861224 i (Nat.not_lt.mp h5) h6
  by_cases h7 : i < 271979280
  · exact c_part3_win_7 i (Nat.not_lt.mp h6) h7
  by_cases h8 : i < 271979281
  · exact c_part3_res_271979280 i (Nat.not_lt.mp h7) h8
  by_cases h9 : i < 272002575
  · exact c_part3_win_9 i (Nat.not_lt.mp h8) h9
  by_cases h10 : i < 272002576
  · exact c_part3_res_272002575 i (Nat.not_lt.mp h9) h10
  by_cases h11 : i < 272175399
  · exact c_part3_win_11 i (Nat.not_lt.mp h10) h11
  by_cases h12 : i < 272175400
  · exact c_part3_res_272175399 i (Nat.not_lt.mp h11) h12
  by_cases h13 : i < 272354738
  · exact c_part3_win_13 i (Nat.not_lt.mp h12) h13
  by_cases h14 : i < 272354739
  · exact c_part3_res_272354738 i (Nat.not_lt.mp h13) h14
  by_cases h15 : i < 272507412
  · exact c_part3_win_15 i (Nat.not_lt.mp h14) h15
  by_cases h16 : i < 272507413
  · exact c_part3_res_272507412 i (Nat.not_lt.mp h15) h16
  by_cases h17 : i < 272707413
  · exact c_part3_win_17 i (Nat.not_lt.mp h16) h17
  by_cases h18 : i < 272907413
  · exact c_part3_win_18 i (Nat.not_lt.mp h17) h18
  by_cases h19 : i < 273107413
  · exact c_part3_win_19 i (Nat.not_lt.mp h18) h19
  by_cases h20 : i < 273244437
  · exact c_part3_win_20 i (Nat.not_lt.mp h19) h20
  by_cases h21 : i < 273244438
  · exact c_part3_res_273244437 i (Nat.not_lt.mp h20) h21
  by_cases h22 : i < 273444438
  · exact c_part3_win_22 i (Nat.not_lt.mp h21) h22
  by_cases h23 : i < 273644438
  · exact c_part3_win_23 i (Nat.not_lt.mp h22) h23
  by_cases h24 : i < 273844438
  · exact c_part3_win_24 i (Nat.not_lt.mp h23) h24
  by_cases h25 : i < 274044438
  · exact c_part3_win_25 i (Nat.not_lt.mp h24) h25
  by_cases h26 : i < 274137581
  · exact c_part3_win_26 i (Nat.not_lt.mp h25) h26
  by_cases h27 : i < 274137582
  · exact c_part3_res_274137581 i (Nat.not_lt.mp h26) h27
  by_cases h28 : i < 274337582
  · exact c_part3_win_28 i (Nat.not_lt.mp h27) h28
  by_cases h29 : i < 274537582
  · exact c_part3_win_29 i (Nat.not_lt.mp h28) h29
  by_cases h30 : i < 274737582
  · exact c_part3_win_30 i (Nat.not_lt.mp h29) h30
  by_cases h31 : i < 274937582
  · exact c_part3_win_31 i (Nat.not_lt.mp h30) h31
  by_cases h32 : i < 275137582
  · exact c_part3_win_32 i (Nat.not_lt.mp h31) h32
  by_cases h33 : i < 275337582
  · exact c_part3_win_33 i (Nat.not_lt.mp h32) h33
  by_cases h34 : i < 275537582
  · exact c_part3_win_34 i (Nat.not_lt.mp h33) h34
  by_cases h35 : i < 275737582
  · exact c_part3_win_35 i (Nat.not_lt.mp h34) h35
  by_cases h36 : i < 275888439
  · exact c_part3_win_36 i (Nat.not_lt.mp h35) h36
  by_cases h37 : i < 275888440
  · exact c_part3_res_275888439 i (Nat.not_lt.mp h36) h37
  by_cases h38 : i < 276088440
  · exact c_part3_win_38 i (Nat.not_lt.mp h37) h38
  by_cases h39 : i < 276288440
  · exact c_part3_win_39 i (Nat.not_lt.mp h38) h39
  by_cases h40 : i < 276488440
  · exact c_part3_win_40 i (Nat.not_lt.mp h39) h40
  by_cases h41 : i < 276550689
  · exact c_part3_win_41 i (Nat.not_lt.mp h40) h41
  by_cases h42 : i < 276550690
  · exact c_part3_res_276550689 i (Nat.not_lt.mp h41) h42
  by_cases h43 : i < 276685869
  · exact c_part3_win_43 i (Nat.not_lt.mp h42) h43
  by_cases h44 : i < 276685870
  · exact c_part3_res_276685869 i (Nat.not_lt.mp h43) h44
  by_cases h45 : i < 276765927
  · exact c_part3_win_45 i (Nat.not_lt.mp h44) h45
  by_cases h46 : i < 276765928
  · exact c_part3_res_276765927 i (Nat.not_lt.mp h45) h46
  by_cases h47 : i < 276791291
  · exact c_part3_win_47 i (Nat.not_lt.mp h46) h47
  by_cases h48 : i < 276791292
  · exact c_part3_res_276791291 i (Nat.not_lt.mp h47) h48
  by_cases h49 : i < 276991292
  · exact c_part3_win_49 i (Nat.not_lt.mp h48) h49
  by_cases h50 : i < 277082499
  · exact c_part3_win_50 i (Nat.not_lt.mp h49) h50
  by_cases h51 : i < 277082500
  · exact c_part3_res_277082499 i (Nat.not_lt.mp h50) h51
  by_cases h52 : i < 277282500
  · exact c_part3_win_52 i (Nat.not_lt.mp h51) h52
  by_cases h53 : i < 277383747
  · exact c_part3_win_53 i (Nat.not_lt.mp h52) h53
  by_cases h54 : i < 277383748
  · exact c_part3_res_277383747 i (Nat.not_lt.mp h53) h54
  by_cases h55 : i < 277583748
  · exact c_part3_win_55 i (Nat.not_lt.mp h54) h55
  by_cases h56 : i < 277598349
  · exact c_part3_win_56 i (Nat.not_lt.mp h55) h56
  by_cases h57 : i < 277598350
  · exact c_part3_res_277598349 i (Nat.not_lt.mp h56) h57
  by_cases h58 : i < 277784484
  · exact c_part3_win_58 i (Nat.not_lt.mp h57) h58
  by_cases h59 : i < 277784485
  · exact c_part3_res_277784484 i (Nat.not_lt.mp h58) h59
  by_cases h60 : i < 277936152
  · exact c_part3_win_60 i (Nat.not_lt.mp h59) h60
  by_cases h61 : i < 277936153
  · exact c_part3_res_277936152 i (Nat.not_lt.mp h60) h61
  by_cases h62 : i < 278073501
  · exact c_part3_win_62 i (Nat.not_lt.mp h61) h62
  by_cases h63 : i < 278073502
  · exact c_part3_res_278073501 i (Nat.not_lt.mp h62) h63
  by_cases h64 : i < 278273502
  · exact c_part3_win_64 i (Nat.not_lt.mp h63) h64
  by_cases h65 : i < 278473502
  · exact c_part3_win_65 i (Nat.not_lt.mp h64) h65
  by_cases h66 : i < 278670873
  · exact c_part3_win_66 i (Nat.not_lt.mp h65) h66
  by_cases h67 : i < 278670874
  · exact c_part3_res_278670873 i (Nat.not_lt.mp h66) h67
  by_cases h68 : i < 278870874
  · exact c_part3_win_68 i (Nat.not_lt.mp h67) h68
  by_cases h69 : i < 279020061
  · exact c_part3_win_69 i (Nat.not_lt.mp h68) h69
  by_cases h70 : i < 279020062
  · exact c_part3_res_279020061 i (Nat.not_lt.mp h69) h70
  by_cases h71 : i < 279220062
  · exact c_part3_win_71 i (Nat.not_lt.mp h70) h71
  by_cases h72 : i < 279420062
  · exact c_part3_win_72 i (Nat.not_lt.mp h71) h72
  by_cases h73 : i < 279620062
  · exact c_part3_win_73 i (Nat.not_lt.mp h72) h73
  by_cases h74 : i < 279692979
  · exact c_part3_win_74 i (Nat.not_lt.mp h73) h74
  by_cases h75 : i < 279692980
  · exact c_part3_res_279692979 i (Nat.not_lt.mp h74) h75
  by_cases h76 : i < 279892980
  · exact c_part3_win_76 i (Nat.not_lt.mp h75) h76
  by_cases h77 : i < 280092980
  · exact c_part3_win_77 i (Nat.not_lt.mp h76) h77
  by_cases h78 : i < 280292980
  · exact c_part3_win_78 i (Nat.not_lt.mp h77) h78
  by_cases h79 : i < 280461333
  · exact c_part3_win_79 i (Nat.not_lt.mp h78) h79
  by_cases h80 : i < 280461334
  · exact c_part3_res_280461333 i (Nat.not_lt.mp h79) h80
  by_cases h81 : i < 280610097
  · exact c_part3_win_81 i (Nat.not_lt.mp h80) h81
  by_cases h82 : i < 280610098
  · exact c_part3_res_280610097 i (Nat.not_lt.mp h81) h82
  by_cases h83 : i < 280647912
  · exact c_part3_win_83 i (Nat.not_lt.mp h82) h83
  by_cases h84 : i < 280647913
  · exact c_part3_res_280647912 i (Nat.not_lt.mp h83) h84
  by_cases h85 : i < 280652754
  · exact c_part3_win_85 i (Nat.not_lt.mp h84) h85
  by_cases h86 : i < 280652755
  · exact c_part3_res_280652754 i (Nat.not_lt.mp h85) h86
  by_cases h87 : i < 280852755
  · exact c_part3_win_87 i (Nat.not_lt.mp h86) h87
  exact c_part3_win_88 i (Nat.not_lt.mp h87) hi

private theorem c_part4_win_0 : ∀ i : ℕ, 281000000 ≤ i → i < 281200000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 562000000) (x1 := 562399998) (lo := 562000069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_1 : ∀ i : ℕ, 281200000 ≤ i → i < 281400000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 562400000) (x1 := 562799998) (lo := 562400069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_2 : ∀ i : ℕ, 281400000 ≤ i → i < 281600000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 562800000) (x1 := 563199998) (lo := 562800069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_3 : ∀ i : ℕ, 281600000 ≤ i → i < 281680347 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563200000) (x1 := 563360692) (lo := 563200069) (W := 271765)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_281680347 : ∀ i : ℕ, 281680347 ≤ i → i < 281680348 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 281680347 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part4_win_5 : ∀ i : ℕ, 281680348 ≤ i → i < 281683284 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563360696) (x1 := 563366566) (lo := 563360765) (W := 116943)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_281683284 : ∀ i : ℕ, 281683284 ≤ i → i < 281683285 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 281683284 := by omega
  subst hi
  exact ⟨127301, by decide, by norm_num⟩
private theorem c_part4_win_7 : ∀ i : ℕ, 281683285 ≤ i → i < 281883285 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563366570) (x1 := 563766568) (lo := 563366639) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_8 : ∀ i : ℕ, 281883285 ≤ i → i < 281971479 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563766570) (x1 := 563942956) (lo := 563766639) (W := 287459)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_281971479 : ∀ i : ℕ, 281971479 ≤ i → i < 281971480 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 281971479 := by omega
  subst hi
  exact ⟨336179, by decide, by norm_num⟩
private theorem c_part4_win_10 : ∀ i : ℕ, 281971480 ≤ i → i < 282171480 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563942960) (x1 := 564342958) (lo := 563943029) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_11 : ∀ i : ℕ, 282171480 ≤ i → i < 282246504 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 564342960) (x1 := 564493006) (lo := 564343029) (W := 261119)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_282246504 : ∀ i : ℕ, 282246504 ≤ i → i < 282246505 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 282246504 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part4_win_13 : ∀ i : ℕ, 282246505 ≤ i → i < 282446505 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 564493010) (x1 := 564893008) (lo := 564493079) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_14 : ∀ i : ℕ, 282446505 ≤ i → i < 282646505 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 564893010) (x1 := 565293008) (lo := 564893079) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_15 : ∀ i : ℕ, 282646505 ≤ i → i < 282758103 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 565293010) (x1 := 565516204) (lo := 565293079) (W := 334267)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_282758103 : ∀ i : ℕ, 282758103 ≤ i → i < 282758104 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 282758103 := by omega
  subst hi
  exact ⟨133391, by decide, by norm_num⟩
private theorem c_part4_win_17 : ∀ i : ℕ, 282758104 ≤ i → i < 282958104 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 565516208) (x1 := 565916206) (lo := 565516277) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_18 : ∀ i : ℕ, 282958104 ≤ i → i < 283158104 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 565916208) (x1 := 566316206) (lo := 565916277) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_19 : ∀ i : ℕ, 283158104 ≤ i → i < 283358104 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 566316208) (x1 := 566716206) (lo := 566316277) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_20 : ∀ i : ℕ, 283358104 ≤ i → i < 283558104 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 566716208) (x1 := 567116206) (lo := 566716277) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_21 : ∀ i : ℕ, 283558104 ≤ i → i < 283659807 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 567116208) (x1 := 567319612) (lo := 567116277) (W := 314477)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_283659807 : ∀ i : ℕ, 283659807 ≤ i → i < 283659808 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 283659807 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part4_win_23 : ∀ i : ℕ, 283659808 ≤ i → i < 283859808 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 567319616) (x1 := 567719614) (lo := 567319685) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_24 : ∀ i : ℕ, 283859808 ≤ i → i < 283900923 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 567719616) (x1 := 567801844) (lo := 567719685) (W := 193301)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_283900923 : ∀ i : ℕ, 283900923 ≤ i → i < 283900924 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 283900923 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part4_win_26 : ∀ i : ℕ, 283900924 ≤ i → i < 284023479 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 567801848) (x1 := 568046956) (lo := 567801917) (W := 356181)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_284023479 : ∀ i : ℕ, 284023479 ≤ i → i < 284023480 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 284023479 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part4_win_28 : ∀ i : ℕ, 284023480 ≤ i → i < 284199837 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568046960) (x1 := 568399672) (lo := 568047029) (W := 463785)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_284199837 : ∀ i : ℕ, 284199837 ≤ i → i < 284199838 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 284199837 := by omega
  subst hi
  exact ⟨1334189, by decide, by norm_num⟩
private theorem c_part4_win_30 : ∀ i : ℕ, 284199838 ≤ i → i < 284399838 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568399676) (x1 := 568799674) (lo := 568399745) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_31 : ∀ i : ℕ, 284399838 ≤ i → i < 284499597 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568799676) (x1 := 568999192) (lo := 568799745) (W := 310589)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_284499597 : ∀ i : ℕ, 284499597 ≤ i → i < 284499598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 284499597 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part4_win_33 : ∀ i : ℕ, 284499598 ≤ i → i < 284699598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568999196) (x1 := 569399194) (lo := 568999265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_34 : ∀ i : ℕ, 284699598 ≤ i → i < 284899598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 569399196) (x1 := 569799194) (lo := 569399265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_35 : ∀ i : ℕ, 284899598 ≤ i → i < 285099598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 569799196) (x1 := 570199194) (lo := 569799265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_36 : ∀ i : ℕ, 285099598 ≤ i → i < 285299598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 570199196) (x1 := 570599194) (lo := 570199265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_37 : ∀ i : ℕ, 285299598 ≤ i → i < 285499598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 570599196) (x1 := 570999194) (lo := 570599265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_38 : ∀ i : ℕ, 285499598 ≤ i → i < 285699598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 570999196) (x1 := 571399194) (lo := 570999265) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_39 : ∀ i : ℕ, 285699598 ≤ i → i < 285896883 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 571399196) (x1 := 571793764) (lo := 571399265) (W := 505641)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_285896883 : ∀ i : ℕ, 285896883 ≤ i → i < 285896884 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 285896883 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part4_win_41 : ∀ i : ℕ, 285896884 ≤ i → i < 286096884 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 571793768) (x1 := 572193766) (lo := 571793837) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_42 : ∀ i : ℕ, 286096884 ≤ i → i < 286296884 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 572193768) (x1 := 572593766) (lo := 572193837) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_43 : ∀ i : ℕ, 286296884 ≤ i → i < 286300005 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 572593768) (x1 := 572600008) (lo := 572593837) (W := 117313)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_286300005 : ∀ i : ℕ, 286300005 ≤ i → i < 286300006 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 286300005 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part4_win_45 : ∀ i : ℕ, 286300006 ≤ i → i < 286500006 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 572600012) (x1 := 573000010) (lo := 572600081) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_46 : ∀ i : ℕ, 286500006 ≤ i → i < 286700006 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 573000012) (x1 := 573400010) (lo := 573000081) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_47 : ∀ i : ℕ, 286700006 ≤ i → i < 286900006 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 573400012) (x1 := 573800010) (lo := 573400081) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_48 : ∀ i : ℕ, 286900006 ≤ i → i < 286985376 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 573800012) (x1 := 573970750) (lo := 573800081) (W := 281811)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_286985376 : ∀ i : ℕ, 286985376 ≤ i → i < 286985377 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 286985376 := by omega
  subst hi
  exact ⟨125219, by decide, by norm_num⟩
private theorem c_part4_win_50 : ∀ i : ℕ, 286985377 ≤ i → i < 287168907 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 573970754) (x1 := 574337812) (lo := 573970823) (W := 478131)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_287168907 : ∀ i : ℕ, 287168907 ≤ i → i < 287168908 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 287168907 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part4_win_52 : ∀ i : ℕ, 287168908 ≤ i → i < 287169363 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 574337816) (x1 := 574338724) (lo := 574337885) (W := 111981)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_287169363 : ∀ i : ℕ, 287169363 ≤ i → i < 287169364 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 287169363 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part4_win_54 : ∀ i : ℕ, 287169364 ≤ i → i < 287216424 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 574338728) (x1 := 574432846) (lo := 574338797) (W := 205191)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_287216424 : ∀ i : ℕ, 287216424 ≤ i → i < 287216425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 287216424 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part4_win_56 : ∀ i : ℕ, 287216425 ≤ i → i < 287416425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 574432850) (x1 := 574832848) (lo := 574432919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_57 : ∀ i : ℕ, 287416425 ≤ i → i < 287616425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 574832850) (x1 := 575232848) (lo := 574832919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_58 : ∀ i : ℕ, 287616425 ≤ i → i < 287816425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 575232850) (x1 := 575632848) (lo := 575232919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_59 : ∀ i : ℕ, 287816425 ≤ i → i < 288016425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 575632850) (x1 := 576032848) (lo := 575632919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_60 : ∀ i : ℕ, 288016425 ≤ i → i < 288216425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 576032850) (x1 := 576432848) (lo := 576032919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_61 : ∀ i : ℕ, 288216425 ≤ i → i < 288416425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 576432850) (x1 := 576832848) (lo := 576432919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_62 : ∀ i : ℕ, 288416425 ≤ i → i < 288616425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 576832850) (x1 := 577232848) (lo := 576832919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_63 : ∀ i : ℕ, 288616425 ≤ i → i < 288816425 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 577232850) (x1 := 577632848) (lo := 577232919) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_64 : ∀ i : ℕ, 288816425 ≤ i → i < 288883431 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 577632850) (x1 := 577766860) (lo := 577632919) (W := 245083)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_288883431 : ∀ i : ℕ, 288883431 ≤ i → i < 288883432 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 288883431 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part4_win_66 : ∀ i : ℕ, 288883432 ≤ i → i < 289083432 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 577766864) (x1 := 578166862) (lo := 577766933) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_67 : ∀ i : ℕ, 289083432 ≤ i → i < 289283432 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 578166864) (x1 := 578566862) (lo := 578166933) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_68 : ∀ i : ℕ, 289283432 ≤ i → i < 289467716 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 578566864) (x1 := 578935430) (lo := 578566933) (W := 479639)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_289467716 : ∀ i : ℕ, 289467716 ≤ i → i < 289467717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 289467716 := by omega
  subst hi
  exact ⟨118107, by decide, by norm_num⟩
private theorem c_part4_win_70 : ∀ i : ℕ, 289467717 ≤ i → i < 289667717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 578935434) (x1 := 579335432) (lo := 578935503) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_71 : ∀ i : ℕ, 289667717 ≤ i → i < 289867717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 579335434) (x1 := 579735432) (lo := 579335503) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_72 : ∀ i : ℕ, 289867717 ≤ i → i < 290067717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 579735434) (x1 := 580135432) (lo := 579735503) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_73 : ∀ i : ℕ, 290067717 ≤ i → i < 290267717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 580135434) (x1 := 580535432) (lo := 580135503) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_74 : ∀ i : ℕ, 290267717 ≤ i → i < 290467717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 580535434) (x1 := 580935432) (lo := 580535503) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_75 : ∀ i : ℕ, 290467717 ≤ i → i < 290667717 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 580935434) (x1 := 581335432) (lo := 580935503) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_76 : ∀ i : ℕ, 290667717 ≤ i → i < 290721462 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 581335434) (x1 := 581442922) (lo := 581335503) (W := 218561)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_res_290721462 : ∀ i : ℕ, 290721462 ≤ i → i < 290721463 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 290721462 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part4_win_78 : ∀ i : ℕ, 290721463 ≤ i → i < 290921463 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 581442926) (x1 := 581842924) (lo := 581442995) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_win_79 : ∀ i : ℕ, 290921463 ≤ i → i < 291000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 581842926) (x1 := 581999998) (lo := 581842995) (W := 268145)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part4_all : ∀ i : ℕ, 281000000 ≤ i → i < 291000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hlo hi
  by_cases h0 : i < 281200000
  · exact c_part4_win_0 i hlo h0
  by_cases h1 : i < 281400000
  · exact c_part4_win_1 i (Nat.not_lt.mp h0) h1
  by_cases h2 : i < 281600000
  · exact c_part4_win_2 i (Nat.not_lt.mp h1) h2
  by_cases h3 : i < 281680347
  · exact c_part4_win_3 i (Nat.not_lt.mp h2) h3
  by_cases h4 : i < 281680348
  · exact c_part4_res_281680347 i (Nat.not_lt.mp h3) h4
  by_cases h5 : i < 281683284
  · exact c_part4_win_5 i (Nat.not_lt.mp h4) h5
  by_cases h6 : i < 281683285
  · exact c_part4_res_281683284 i (Nat.not_lt.mp h5) h6
  by_cases h7 : i < 281883285
  · exact c_part4_win_7 i (Nat.not_lt.mp h6) h7
  by_cases h8 : i < 281971479
  · exact c_part4_win_8 i (Nat.not_lt.mp h7) h8
  by_cases h9 : i < 281971480
  · exact c_part4_res_281971479 i (Nat.not_lt.mp h8) h9
  by_cases h10 : i < 282171480
  · exact c_part4_win_10 i (Nat.not_lt.mp h9) h10
  by_cases h11 : i < 282246504
  · exact c_part4_win_11 i (Nat.not_lt.mp h10) h11
  by_cases h12 : i < 282246505
  · exact c_part4_res_282246504 i (Nat.not_lt.mp h11) h12
  by_cases h13 : i < 282446505
  · exact c_part4_win_13 i (Nat.not_lt.mp h12) h13
  by_cases h14 : i < 282646505
  · exact c_part4_win_14 i (Nat.not_lt.mp h13) h14
  by_cases h15 : i < 282758103
  · exact c_part4_win_15 i (Nat.not_lt.mp h14) h15
  by_cases h16 : i < 282758104
  · exact c_part4_res_282758103 i (Nat.not_lt.mp h15) h16
  by_cases h17 : i < 282958104
  · exact c_part4_win_17 i (Nat.not_lt.mp h16) h17
  by_cases h18 : i < 283158104
  · exact c_part4_win_18 i (Nat.not_lt.mp h17) h18
  by_cases h19 : i < 283358104
  · exact c_part4_win_19 i (Nat.not_lt.mp h18) h19
  by_cases h20 : i < 283558104
  · exact c_part4_win_20 i (Nat.not_lt.mp h19) h20
  by_cases h21 : i < 283659807
  · exact c_part4_win_21 i (Nat.not_lt.mp h20) h21
  by_cases h22 : i < 283659808
  · exact c_part4_res_283659807 i (Nat.not_lt.mp h21) h22
  by_cases h23 : i < 283859808
  · exact c_part4_win_23 i (Nat.not_lt.mp h22) h23
  by_cases h24 : i < 283900923
  · exact c_part4_win_24 i (Nat.not_lt.mp h23) h24
  by_cases h25 : i < 283900924
  · exact c_part4_res_283900923 i (Nat.not_lt.mp h24) h25
  by_cases h26 : i < 284023479
  · exact c_part4_win_26 i (Nat.not_lt.mp h25) h26
  by_cases h27 : i < 284023480
  · exact c_part4_res_284023479 i (Nat.not_lt.mp h26) h27
  by_cases h28 : i < 284199837
  · exact c_part4_win_28 i (Nat.not_lt.mp h27) h28
  by_cases h29 : i < 284199838
  · exact c_part4_res_284199837 i (Nat.not_lt.mp h28) h29
  by_cases h30 : i < 284399838
  · exact c_part4_win_30 i (Nat.not_lt.mp h29) h30
  by_cases h31 : i < 284499597
  · exact c_part4_win_31 i (Nat.not_lt.mp h30) h31
  by_cases h32 : i < 284499598
  · exact c_part4_res_284499597 i (Nat.not_lt.mp h31) h32
  by_cases h33 : i < 284699598
  · exact c_part4_win_33 i (Nat.not_lt.mp h32) h33
  by_cases h34 : i < 284899598
  · exact c_part4_win_34 i (Nat.not_lt.mp h33) h34
  by_cases h35 : i < 285099598
  · exact c_part4_win_35 i (Nat.not_lt.mp h34) h35
  by_cases h36 : i < 285299598
  · exact c_part4_win_36 i (Nat.not_lt.mp h35) h36
  by_cases h37 : i < 285499598
  · exact c_part4_win_37 i (Nat.not_lt.mp h36) h37
  by_cases h38 : i < 285699598
  · exact c_part4_win_38 i (Nat.not_lt.mp h37) h38
  by_cases h39 : i < 285896883
  · exact c_part4_win_39 i (Nat.not_lt.mp h38) h39
  by_cases h40 : i < 285896884
  · exact c_part4_res_285896883 i (Nat.not_lt.mp h39) h40
  by_cases h41 : i < 286096884
  · exact c_part4_win_41 i (Nat.not_lt.mp h40) h41
  by_cases h42 : i < 286296884
  · exact c_part4_win_42 i (Nat.not_lt.mp h41) h42
  by_cases h43 : i < 286300005
  · exact c_part4_win_43 i (Nat.not_lt.mp h42) h43
  by_cases h44 : i < 286300006
  · exact c_part4_res_286300005 i (Nat.not_lt.mp h43) h44
  by_cases h45 : i < 286500006
  · exact c_part4_win_45 i (Nat.not_lt.mp h44) h45
  by_cases h46 : i < 286700006
  · exact c_part4_win_46 i (Nat.not_lt.mp h45) h46
  by_cases h47 : i < 286900006
  · exact c_part4_win_47 i (Nat.not_lt.mp h46) h47
  by_cases h48 : i < 286985376
  · exact c_part4_win_48 i (Nat.not_lt.mp h47) h48
  by_cases h49 : i < 286985377
  · exact c_part4_res_286985376 i (Nat.not_lt.mp h48) h49
  by_cases h50 : i < 287168907
  · exact c_part4_win_50 i (Nat.not_lt.mp h49) h50
  by_cases h51 : i < 287168908
  · exact c_part4_res_287168907 i (Nat.not_lt.mp h50) h51
  by_cases h52 : i < 287169363
  · exact c_part4_win_52 i (Nat.not_lt.mp h51) h52
  by_cases h53 : i < 287169364
  · exact c_part4_res_287169363 i (Nat.not_lt.mp h52) h53
  by_cases h54 : i < 287216424
  · exact c_part4_win_54 i (Nat.not_lt.mp h53) h54
  by_cases h55 : i < 287216425
  · exact c_part4_res_287216424 i (Nat.not_lt.mp h54) h55
  by_cases h56 : i < 287416425
  · exact c_part4_win_56 i (Nat.not_lt.mp h55) h56
  by_cases h57 : i < 287616425
  · exact c_part4_win_57 i (Nat.not_lt.mp h56) h57
  by_cases h58 : i < 287816425
  · exact c_part4_win_58 i (Nat.not_lt.mp h57) h58
  by_cases h59 : i < 288016425
  · exact c_part4_win_59 i (Nat.not_lt.mp h58) h59
  by_cases h60 : i < 288216425
  · exact c_part4_win_60 i (Nat.not_lt.mp h59) h60
  by_cases h61 : i < 288416425
  · exact c_part4_win_61 i (Nat.not_lt.mp h60) h61
  by_cases h62 : i < 288616425
  · exact c_part4_win_62 i (Nat.not_lt.mp h61) h62
  by_cases h63 : i < 288816425
  · exact c_part4_win_63 i (Nat.not_lt.mp h62) h63
  by_cases h64 : i < 288883431
  · exact c_part4_win_64 i (Nat.not_lt.mp h63) h64
  by_cases h65 : i < 288883432
  · exact c_part4_res_288883431 i (Nat.not_lt.mp h64) h65
  by_cases h66 : i < 289083432
  · exact c_part4_win_66 i (Nat.not_lt.mp h65) h66
  by_cases h67 : i < 289283432
  · exact c_part4_win_67 i (Nat.not_lt.mp h66) h67
  by_cases h68 : i < 289467716
  · exact c_part4_win_68 i (Nat.not_lt.mp h67) h68
  by_cases h69 : i < 289467717
  · exact c_part4_res_289467716 i (Nat.not_lt.mp h68) h69
  by_cases h70 : i < 289667717
  · exact c_part4_win_70 i (Nat.not_lt.mp h69) h70
  by_cases h71 : i < 289867717
  · exact c_part4_win_71 i (Nat.not_lt.mp h70) h71
  by_cases h72 : i < 290067717
  · exact c_part4_win_72 i (Nat.not_lt.mp h71) h72
  by_cases h73 : i < 290267717
  · exact c_part4_win_73 i (Nat.not_lt.mp h72) h73
  by_cases h74 : i < 290467717
  · exact c_part4_win_74 i (Nat.not_lt.mp h73) h74
  by_cases h75 : i < 290667717
  · exact c_part4_win_75 i (Nat.not_lt.mp h74) h75
  by_cases h76 : i < 290721462
  · exact c_part4_win_76 i (Nat.not_lt.mp h75) h76
  by_cases h77 : i < 290721463
  · exact c_part4_res_290721462 i (Nat.not_lt.mp h76) h77
  by_cases h78 : i < 290921463
  · exact c_part4_win_78 i (Nat.not_lt.mp h77) h78
  exact c_part4_win_79 i (Nat.not_lt.mp h78) hi

private theorem c_part5_win_0 : ∀ i : ℕ, 291000000 ≤ i → i < 291114702 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 582000000) (x1 := 582229402) (lo := 582000069) (W := 340475)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_291114702 : ∀ i : ℕ, 291114702 ≤ i → i < 291114703 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 291114702 := by omega
  subst hi
  exact ⟨123533, by decide, by norm_num⟩
private theorem c_part5_win_2 : ∀ i : ℕ, 291114703 ≤ i → i < 291314703 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 582229406) (x1 := 582629404) (lo := 582229475) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_3 : ∀ i : ℕ, 291314703 ≤ i → i < 291514703 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 582629406) (x1 := 583029404) (lo := 582629475) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_4 : ∀ i : ℕ, 291514703 ≤ i → i < 291714703 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 583029406) (x1 := 583429404) (lo := 583029475) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_5 : ∀ i : ℕ, 291714703 ≤ i → i < 291895482 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 583429406) (x1 := 583790962) (lo := 583429475) (W := 472629)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_291895482 : ∀ i : ℕ, 291895482 ≤ i → i < 291895483 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 291895482 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part5_win_7 : ∀ i : ℕ, 291895483 ≤ i → i < 292095483 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 583790966) (x1 := 584190964) (lo := 583791035) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_8 : ∀ i : ℕ, 292095483 ≤ i → i < 292295483 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 584190966) (x1 := 584590964) (lo := 584191035) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_9 : ∀ i : ℕ, 292295483 ≤ i → i < 292405992 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 584590966) (x1 := 584811982) (lo := 584591035) (W := 332089)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_292405992 : ∀ i : ℕ, 292405992 ≤ i → i < 292405993 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 292405992 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part5_win_11 : ∀ i : ℕ, 292405993 ≤ i → i < 292605993 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 584811986) (x1 := 585211984) (lo := 584812055) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_12 : ∀ i : ℕ, 292605993 ≤ i → i < 292616532 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 585211986) (x1 := 585233062) (lo := 585212055) (W := 132149)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_292616532 : ∀ i : ℕ, 292616532 ≤ i → i < 292616533 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 292616532 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part5_win_14 : ∀ i : ℕ, 292616533 ≤ i → i < 292816533 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 585233066) (x1 := 585633064) (lo := 585233135) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_15 : ∀ i : ℕ, 292816533 ≤ i → i < 293016533 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 585633066) (x1 := 586033064) (lo := 585633135) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_16 : ∀ i : ℕ, 293016533 ≤ i → i < 293187012 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586033066) (x1 := 586374022) (lo := 586033135) (W := 452029)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_293187012 : ∀ i : ℕ, 293187012 ≤ i → i < 293187013 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 293187012 := by omega
  subst hi
  exact ⟨1668413, by decide, by norm_num⟩
private theorem c_part5_win_18 : ∀ i : ℕ, 293187013 ≤ i → i < 293387013 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586374026) (x1 := 586774024) (lo := 586374095) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_19 : ∀ i : ℕ, 293387013 ≤ i → i < 293495298 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586774026) (x1 := 586990594) (lo := 586774095) (W := 327641)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_293495298 : ∀ i : ℕ, 293495298 ≤ i → i < 293495299 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 293495298 := by omega
  subst hi
  exact ⟨3361883, by decide, by norm_num⟩
private theorem c_part5_win_21 : ∀ i : ℕ, 293495299 ≤ i → i < 293695299 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586990598) (x1 := 587390596) (lo := 586990667) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_22 : ∀ i : ℕ, 293695299 ≤ i → i < 293799606 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 587390598) (x1 := 587599210) (lo := 587390667) (W := 319685)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_293799606 : ∀ i : ℕ, 293799606 ≤ i → i < 293799607 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 293799606 := by omega
  subst hi
  exact ⟨336179, by decide, by norm_num⟩
private theorem c_part5_win_24 : ∀ i : ℕ, 293799607 ≤ i → i < 293999607 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 587599214) (x1 := 587999212) (lo := 587599283) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_25 : ∀ i : ℕ, 293999607 ≤ i → i < 294126194 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 587999214) (x1 := 588252386) (lo := 587999283) (W := 364245)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_294126194 : ∀ i : ℕ, 294126194 ≤ i → i < 294126195 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 294126194 := by omega
  subst hi
  exact ⟨115401, by decide, by norm_num⟩
private theorem c_part5_win_27 : ∀ i : ℕ, 294126195 ≤ i → i < 294326195 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 588252390) (x1 := 588652388) (lo := 588252459) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_28 : ∀ i : ℕ, 294326195 ≤ i → i < 294526195 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 588652390) (x1 := 589052388) (lo := 588652459) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_29 : ∀ i : ℕ, 294526195 ≤ i → i < 294726195 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 589052390) (x1 := 589452388) (lo := 589052459) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_30 : ∀ i : ℕ, 294726195 ≤ i → i < 294751247 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 589452390) (x1 := 589502492) (lo := 589452459) (W := 161175)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_294751247 : ∀ i : ℕ, 294751247 ≤ i → i < 294751248 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 294751247 := by omega
  subst hi
  exact ⟨132219, by decide, by norm_num⟩
private theorem c_part5_win_32 : ∀ i : ℕ, 294751248 ≤ i → i < 294951248 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 589502496) (x1 := 589902494) (lo := 589502565) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_33 : ∀ i : ℕ, 294951248 ≤ i → i < 295151248 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 589902496) (x1 := 590302494) (lo := 589902565) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_34 : ∀ i : ℕ, 295151248 ≤ i → i < 295351248 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 590302496) (x1 := 590702494) (lo := 590302565) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_35 : ∀ i : ℕ, 295351248 ≤ i → i < 295484223 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 590702496) (x1 := 590968444) (lo := 590702565) (W := 377021)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_295484223 : ∀ i : ℕ, 295484223 ≤ i → i < 295484224 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 295484223 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part5_win_37 : ∀ i : ℕ, 295484224 ≤ i → i < 295684224 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 590968448) (x1 := 591368446) (lo := 590968517) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_38 : ∀ i : ℕ, 295684224 ≤ i → i < 295884224 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 591368448) (x1 := 591768446) (lo := 591368517) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_39 : ∀ i : ℕ, 295884224 ≤ i → i < 295980164 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 591768448) (x1 := 591960326) (lo := 591768517) (W := 302951)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_295980164 : ∀ i : ℕ, 295980164 ≤ i → i < 295980165 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 295980164 := by omega
  subst hi
  exact ⟨124449, by decide, by norm_num⟩
private theorem c_part5_win_41 : ∀ i : ℕ, 295980165 ≤ i → i < 296012618 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 591960330) (x1 := 592025234) (lo := 591960399) (W := 175977)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_296012618 : ∀ i : ℕ, 296012618 ≤ i → i < 296012619 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 296012618 := by omega
  subst hi
  exact ⟨115317, by decide, by norm_num⟩
private theorem c_part5_win_43 : ∀ i : ℕ, 296012619 ≤ i → i < 296014293 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592025238) (x1 := 592028584) (lo := 592025307) (W := 114419)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_296014293 : ∀ i : ℕ, 296014293 ≤ i → i < 296014294 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 296014293 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part5_win_45 : ∀ i : ℕ, 296014294 ≤ i → i < 296214294 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592028588) (x1 := 592428586) (lo := 592028657) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_46 : ∀ i : ℕ, 296214294 ≤ i → i < 296269082 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592428588) (x1 := 592538162) (lo := 592428657) (W := 220647)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_296269082 : ∀ i : ℕ, 296269082 ≤ i → i < 296269083 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 296269082 := by omega
  subst hi
  exact ⟨111213, by decide, by norm_num⟩
private theorem c_part5_win_48 : ∀ i : ℕ, 296269083 ≤ i → i < 296469083 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592538166) (x1 := 592938164) (lo := 592538235) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_49 : ∀ i : ℕ, 296469083 ≤ i → i < 296669083 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592938166) (x1 := 593338164) (lo := 592938235) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_50 : ∀ i : ℕ, 296669083 ≤ i → i < 296851062 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 593338166) (x1 := 593702122) (lo := 593338235) (W := 475029)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_296851062 : ∀ i : ℕ, 296851062 ≤ i → i < 296851063 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 296851062 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part5_win_52 : ∀ i : ℕ, 296851063 ≤ i → i < 297051063 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 593702126) (x1 := 594102124) (lo := 593702195) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_53 : ∀ i : ℕ, 297051063 ≤ i → i < 297166352 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 594102126) (x1 := 594332702) (lo := 594102195) (W := 341649)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_297166352 : ∀ i : ℕ, 297166352 ≤ i → i < 297166353 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 297166352 := by omega
  subst hi
  exact ⟨111213, by decide, by norm_num⟩
private theorem c_part5_win_55 : ∀ i : ℕ, 297166353 ≤ i → i < 297366353 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 594332706) (x1 := 594732704) (lo := 594332775) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_56 : ∀ i : ℕ, 297366353 ≤ i → i < 297566353 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 594732706) (x1 := 595132704) (lo := 594732775) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_57 : ∀ i : ℕ, 297566353 ≤ i → i < 297582597 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595132706) (x1 := 595165192) (lo := 595132775) (W := 143559)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_297582597 : ∀ i : ℕ, 297582597 ≤ i → i < 297582598 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 297582597 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part5_win_59 : ∀ i : ℕ, 297582598 ≤ i → i < 297598662 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595165196) (x1 := 595197322) (lo := 595165265) (W := 143199)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_297598662 : ∀ i : ℕ, 297598662 ≤ i → i < 297598663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 297598662 := by omega
  subst hi
  exact ⟨699059, by decide, by norm_num⟩
private theorem c_part5_win_61 : ∀ i : ℕ, 297598663 ≤ i → i < 297798663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595197326) (x1 := 595597324) (lo := 595197395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_62 : ∀ i : ℕ, 297798663 ≤ i → i < 297998663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595597326) (x1 := 595997324) (lo := 595597395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_63 : ∀ i : ℕ, 297998663 ≤ i → i < 298198663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595997326) (x1 := 596397324) (lo := 595997395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_64 : ∀ i : ℕ, 298198663 ≤ i → i < 298398663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 596397326) (x1 := 596797324) (lo := 596397395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_65 : ∀ i : ℕ, 298398663 ≤ i → i < 298598663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 596797326) (x1 := 597197324) (lo := 596797395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_66 : ∀ i : ℕ, 298598663 ≤ i → i < 298798663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 597197326) (x1 := 597597324) (lo := 597197395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_67 : ∀ i : ℕ, 298798663 ≤ i → i < 298998663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 597597326) (x1 := 597997324) (lo := 597597395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_68 : ∀ i : ℕ, 298998663 ≤ i → i < 299198663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 597997326) (x1 := 598397324) (lo := 597997395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_69 : ∀ i : ℕ, 299198663 ≤ i → i < 299398663 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 598397326) (x1 := 598797324) (lo := 598397395) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_70 : ∀ i : ℕ, 299398663 ≤ i → i < 299464089 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 598797326) (x1 := 598928176) (lo := 598797395) (W := 241923)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_299464089 : ∀ i : ℕ, 299464089 ≤ i → i < 299464090 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 299464089 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part5_win_72 : ∀ i : ℕ, 299464090 ≤ i → i < 299664090 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 598928180) (x1 := 599328178) (lo := 598928249) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_73 : ∀ i : ℕ, 299664090 ≤ i → i < 299669739 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 599328180) (x1 := 599339476) (lo := 599328249) (W := 122369)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_299669739 : ∀ i : ℕ, 299669739 ≤ i → i < 299669740 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 299669739 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part5_win_75 : ∀ i : ℕ, 299669740 ≤ i → i < 299869740 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 599339480) (x1 := 599739478) (lo := 599339549) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_76 : ∀ i : ℕ, 299869740 ≤ i → i < 300069740 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 599739480) (x1 := 600139478) (lo := 599739549) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_77 : ∀ i : ℕ, 300069740 ≤ i → i < 300218007 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600139480) (x1 := 600436012) (lo := 600139549) (W := 407605)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_300218007 : ∀ i : ℕ, 300218007 ≤ i → i < 300218008 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 300218007 := by omega
  subst hi
  exact ⟨116717, by decide, by norm_num⟩
private theorem c_part5_win_79 : ∀ i : ℕ, 300218008 ≤ i → i < 300231516 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600436016) (x1 := 600463030) (lo := 600436085) (W := 138087)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_300231516 : ∀ i : ℕ, 300231516 ≤ i → i < 300231517 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 300231516 := by omega
  subst hi
  exact ⟨125219, by decide, by norm_num⟩
private theorem c_part5_win_81 : ∀ i : ℕ, 300231517 ≤ i → i < 300267783 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600463034) (x1 := 600535564) (lo := 600463103) (W := 183603)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_res_300267783 : ∀ i : ℕ, 300267783 ≤ i → i < 300267784 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 300267783 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part5_win_83 : ∀ i : ℕ, 300267784 ≤ i → i < 300467784 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600535568) (x1 := 600935566) (lo := 600535637) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_84 : ∀ i : ℕ, 300467784 ≤ i → i < 300667784 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600935568) (x1 := 601335566) (lo := 600935637) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_85 : ∀ i : ℕ, 300667784 ≤ i → i < 300867784 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 601335568) (x1 := 601735566) (lo := 601335637) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_win_86 : ∀ i : ℕ, 300867784 ≤ i → i < 301000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 601735568) (x1 := 601999998) (lo := 601735637) (W := 375503)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part5_all : ∀ i : ℕ, 291000000 ≤ i → i < 301000000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hlo hi
  by_cases h0 : i < 291114702
  · exact c_part5_win_0 i hlo h0
  by_cases h1 : i < 291114703
  · exact c_part5_res_291114702 i (Nat.not_lt.mp h0) h1
  by_cases h2 : i < 291314703
  · exact c_part5_win_2 i (Nat.not_lt.mp h1) h2
  by_cases h3 : i < 291514703
  · exact c_part5_win_3 i (Nat.not_lt.mp h2) h3
  by_cases h4 : i < 291714703
  · exact c_part5_win_4 i (Nat.not_lt.mp h3) h4
  by_cases h5 : i < 291895482
  · exact c_part5_win_5 i (Nat.not_lt.mp h4) h5
  by_cases h6 : i < 291895483
  · exact c_part5_res_291895482 i (Nat.not_lt.mp h5) h6
  by_cases h7 : i < 292095483
  · exact c_part5_win_7 i (Nat.not_lt.mp h6) h7
  by_cases h8 : i < 292295483
  · exact c_part5_win_8 i (Nat.not_lt.mp h7) h8
  by_cases h9 : i < 292405992
  · exact c_part5_win_9 i (Nat.not_lt.mp h8) h9
  by_cases h10 : i < 292405993
  · exact c_part5_res_292405992 i (Nat.not_lt.mp h9) h10
  by_cases h11 : i < 292605993
  · exact c_part5_win_11 i (Nat.not_lt.mp h10) h11
  by_cases h12 : i < 292616532
  · exact c_part5_win_12 i (Nat.not_lt.mp h11) h12
  by_cases h13 : i < 292616533
  · exact c_part5_res_292616532 i (Nat.not_lt.mp h12) h13
  by_cases h14 : i < 292816533
  · exact c_part5_win_14 i (Nat.not_lt.mp h13) h14
  by_cases h15 : i < 293016533
  · exact c_part5_win_15 i (Nat.not_lt.mp h14) h15
  by_cases h16 : i < 293187012
  · exact c_part5_win_16 i (Nat.not_lt.mp h15) h16
  by_cases h17 : i < 293187013
  · exact c_part5_res_293187012 i (Nat.not_lt.mp h16) h17
  by_cases h18 : i < 293387013
  · exact c_part5_win_18 i (Nat.not_lt.mp h17) h18
  by_cases h19 : i < 293495298
  · exact c_part5_win_19 i (Nat.not_lt.mp h18) h19
  by_cases h20 : i < 293495299
  · exact c_part5_res_293495298 i (Nat.not_lt.mp h19) h20
  by_cases h21 : i < 293695299
  · exact c_part5_win_21 i (Nat.not_lt.mp h20) h21
  by_cases h22 : i < 293799606
  · exact c_part5_win_22 i (Nat.not_lt.mp h21) h22
  by_cases h23 : i < 293799607
  · exact c_part5_res_293799606 i (Nat.not_lt.mp h22) h23
  by_cases h24 : i < 293999607
  · exact c_part5_win_24 i (Nat.not_lt.mp h23) h24
  by_cases h25 : i < 294126194
  · exact c_part5_win_25 i (Nat.not_lt.mp h24) h25
  by_cases h26 : i < 294126195
  · exact c_part5_res_294126194 i (Nat.not_lt.mp h25) h26
  by_cases h27 : i < 294326195
  · exact c_part5_win_27 i (Nat.not_lt.mp h26) h27
  by_cases h28 : i < 294526195
  · exact c_part5_win_28 i (Nat.not_lt.mp h27) h28
  by_cases h29 : i < 294726195
  · exact c_part5_win_29 i (Nat.not_lt.mp h28) h29
  by_cases h30 : i < 294751247
  · exact c_part5_win_30 i (Nat.not_lt.mp h29) h30
  by_cases h31 : i < 294751248
  · exact c_part5_res_294751247 i (Nat.not_lt.mp h30) h31
  by_cases h32 : i < 294951248
  · exact c_part5_win_32 i (Nat.not_lt.mp h31) h32
  by_cases h33 : i < 295151248
  · exact c_part5_win_33 i (Nat.not_lt.mp h32) h33
  by_cases h34 : i < 295351248
  · exact c_part5_win_34 i (Nat.not_lt.mp h33) h34
  by_cases h35 : i < 295484223
  · exact c_part5_win_35 i (Nat.not_lt.mp h34) h35
  by_cases h36 : i < 295484224
  · exact c_part5_res_295484223 i (Nat.not_lt.mp h35) h36
  by_cases h37 : i < 295684224
  · exact c_part5_win_37 i (Nat.not_lt.mp h36) h37
  by_cases h38 : i < 295884224
  · exact c_part5_win_38 i (Nat.not_lt.mp h37) h38
  by_cases h39 : i < 295980164
  · exact c_part5_win_39 i (Nat.not_lt.mp h38) h39
  by_cases h40 : i < 295980165
  · exact c_part5_res_295980164 i (Nat.not_lt.mp h39) h40
  by_cases h41 : i < 296012618
  · exact c_part5_win_41 i (Nat.not_lt.mp h40) h41
  by_cases h42 : i < 296012619
  · exact c_part5_res_296012618 i (Nat.not_lt.mp h41) h42
  by_cases h43 : i < 296014293
  · exact c_part5_win_43 i (Nat.not_lt.mp h42) h43
  by_cases h44 : i < 296014294
  · exact c_part5_res_296014293 i (Nat.not_lt.mp h43) h44
  by_cases h45 : i < 296214294
  · exact c_part5_win_45 i (Nat.not_lt.mp h44) h45
  by_cases h46 : i < 296269082
  · exact c_part5_win_46 i (Nat.not_lt.mp h45) h46
  by_cases h47 : i < 296269083
  · exact c_part5_res_296269082 i (Nat.not_lt.mp h46) h47
  by_cases h48 : i < 296469083
  · exact c_part5_win_48 i (Nat.not_lt.mp h47) h48
  by_cases h49 : i < 296669083
  · exact c_part5_win_49 i (Nat.not_lt.mp h48) h49
  by_cases h50 : i < 296851062
  · exact c_part5_win_50 i (Nat.not_lt.mp h49) h50
  by_cases h51 : i < 296851063
  · exact c_part5_res_296851062 i (Nat.not_lt.mp h50) h51
  by_cases h52 : i < 297051063
  · exact c_part5_win_52 i (Nat.not_lt.mp h51) h52
  by_cases h53 : i < 297166352
  · exact c_part5_win_53 i (Nat.not_lt.mp h52) h53
  by_cases h54 : i < 297166353
  · exact c_part5_res_297166352 i (Nat.not_lt.mp h53) h54
  by_cases h55 : i < 297366353
  · exact c_part5_win_55 i (Nat.not_lt.mp h54) h55
  by_cases h56 : i < 297566353
  · exact c_part5_win_56 i (Nat.not_lt.mp h55) h56
  by_cases h57 : i < 297582597
  · exact c_part5_win_57 i (Nat.not_lt.mp h56) h57
  by_cases h58 : i < 297582598
  · exact c_part5_res_297582597 i (Nat.not_lt.mp h57) h58
  by_cases h59 : i < 297598662
  · exact c_part5_win_59 i (Nat.not_lt.mp h58) h59
  by_cases h60 : i < 297598663
  · exact c_part5_res_297598662 i (Nat.not_lt.mp h59) h60
  by_cases h61 : i < 297798663
  · exact c_part5_win_61 i (Nat.not_lt.mp h60) h61
  by_cases h62 : i < 297998663
  · exact c_part5_win_62 i (Nat.not_lt.mp h61) h62
  by_cases h63 : i < 298198663
  · exact c_part5_win_63 i (Nat.not_lt.mp h62) h63
  by_cases h64 : i < 298398663
  · exact c_part5_win_64 i (Nat.not_lt.mp h63) h64
  by_cases h65 : i < 298598663
  · exact c_part5_win_65 i (Nat.not_lt.mp h64) h65
  by_cases h66 : i < 298798663
  · exact c_part5_win_66 i (Nat.not_lt.mp h65) h66
  by_cases h67 : i < 298998663
  · exact c_part5_win_67 i (Nat.not_lt.mp h66) h67
  by_cases h68 : i < 299198663
  · exact c_part5_win_68 i (Nat.not_lt.mp h67) h68
  by_cases h69 : i < 299398663
  · exact c_part5_win_69 i (Nat.not_lt.mp h68) h69
  by_cases h70 : i < 299464089
  · exact c_part5_win_70 i (Nat.not_lt.mp h69) h70
  by_cases h71 : i < 299464090
  · exact c_part5_res_299464089 i (Nat.not_lt.mp h70) h71
  by_cases h72 : i < 299664090
  · exact c_part5_win_72 i (Nat.not_lt.mp h71) h72
  by_cases h73 : i < 299669739
  · exact c_part5_win_73 i (Nat.not_lt.mp h72) h73
  by_cases h74 : i < 299669740
  · exact c_part5_res_299669739 i (Nat.not_lt.mp h73) h74
  by_cases h75 : i < 299869740
  · exact c_part5_win_75 i (Nat.not_lt.mp h74) h75
  by_cases h76 : i < 300069740
  · exact c_part5_win_76 i (Nat.not_lt.mp h75) h76
  by_cases h77 : i < 300218007
  · exact c_part5_win_77 i (Nat.not_lt.mp h76) h77
  by_cases h78 : i < 300218008
  · exact c_part5_res_300218007 i (Nat.not_lt.mp h77) h78
  by_cases h79 : i < 300231516
  · exact c_part5_win_79 i (Nat.not_lt.mp h78) h79
  by_cases h80 : i < 300231517
  · exact c_part5_res_300231516 i (Nat.not_lt.mp h79) h80
  by_cases h81 : i < 300267783
  · exact c_part5_win_81 i (Nat.not_lt.mp h80) h81
  by_cases h82 : i < 300267784
  · exact c_part5_res_300267783 i (Nat.not_lt.mp h81) h82
  by_cases h83 : i < 300467784
  · exact c_part5_win_83 i (Nat.not_lt.mp h82) h83
  by_cases h84 : i < 300667784
  · exact c_part5_win_84 i (Nat.not_lt.mp h83) h84
  by_cases h85 : i < 300867784
  · exact c_part5_win_85 i (Nat.not_lt.mp h84) h85
  exact c_part5_win_86 i (Nat.not_lt.mp h85) hi

private theorem c_part6_win_0 : ∀ i : ℕ, 301000000 ≤ i → i < 301200000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 602000000) (x1 := 602399998) (lo := 602000069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_1 : ∀ i : ℕ, 301200000 ≤ i → i < 301400000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 602400000) (x1 := 602799998) (lo := 602400069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_2 : ∀ i : ℕ, 301400000 ≤ i → i < 301600000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 602800000) (x1 := 603199998) (lo := 602800069) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_3 : ∀ i : ℕ, 301600000 ≤ i → i < 301725729 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 603200000) (x1 := 603451456) (lo := 603200069) (W := 362529)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_301725729 : ∀ i : ℕ, 301725729 ≤ i → i < 301725730 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 301725729 := by omega
  subst hi
  exact ⟨131189, by decide, by norm_num⟩
private theorem c_part6_win_5 : ∀ i : ℕ, 301725730 ≤ i → i < 301925730 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 603451460) (x1 := 603851458) (lo := 603451529) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_6 : ∀ i : ℕ, 301925730 ≤ i → i < 301993859 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 603851460) (x1 := 603987716) (lo := 603851529) (W := 247329)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_301993859 : ∀ i : ℕ, 301993859 ≤ i → i < 301993860 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 301993859 := by omega
  subst hi
  exact ⟨111213, by decide, by norm_num⟩
private theorem c_part6_win_8 : ∀ i : ℕ, 301993860 ≤ i → i < 302193860 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 603987720) (x1 := 604387718) (lo := 603987789) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_9 : ∀ i : ℕ, 302193860 ≤ i → i < 302389259 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 604387720) (x1 := 604778516) (lo := 604387789) (W := 501869)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302389259 : ∀ i : ℕ, 302389259 ≤ i → i < 302389260 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302389259 := by omega
  subst hi
  exact ⟨126429, by decide, by norm_num⟩
private theorem c_part6_win_11 : ∀ i : ℕ, 302389260 ≤ i → i < 302413284 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 604778520) (x1 := 604826566) (lo := 604778589) (W := 159119)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302413284 : ∀ i : ℕ, 302413284 ≤ i → i < 302413285 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302413284 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part6_win_13 : ∀ i : ℕ, 302413285 ≤ i → i < 302507412 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 604826570) (x1 := 605014822) (lo := 604826639) (W := 299325)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302507412 : ∀ i : ℕ, 302507412 ≤ i → i < 302507413 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302507412 := by omega
  subst hi
  exact ⟨123923, by decide, by norm_num⟩
private theorem c_part6_win_15 : ∀ i : ℕ, 302507413 ≤ i → i < 302607864 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 605014826) (x1 := 605215726) (lo := 605014895) (W := 311973)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302607864 : ∀ i : ℕ, 302607864 ≤ i → i < 302607865 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302607864 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_17 : ∀ i : ℕ, 302607865 ≤ i → i < 302668872 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 605215730) (x1 := 605337742) (lo := 605215799) (W := 233085)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302668872 : ∀ i : ℕ, 302668872 ≤ i → i < 302668873 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302668872 := by omega
  subst hi
  exact ⟨117023, by decide, by norm_num⟩
private theorem c_part6_win_19 : ∀ i : ℕ, 302668873 ≤ i → i < 302780499 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 605337746) (x1 := 605560996) (lo := 605337815) (W := 334323)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302780499 : ∀ i : ℕ, 302780499 ≤ i → i < 302780500 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302780499 := by omega
  subst hi
  exact ⟨123533, by decide, by norm_num⟩
private theorem c_part6_win_21 : ∀ i : ℕ, 302780500 ≤ i → i < 302975082 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 605561000) (x1 := 605950162) (lo := 605561069) (W := 500235)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_302975082 : ∀ i : ℕ, 302975082 ≤ i → i < 302975083 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 302975082 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part6_win_23 : ∀ i : ℕ, 302975083 ≤ i → i < 303055467 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 605950166) (x1 := 606110932) (lo := 605950235) (W := 271839)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_303055467 : ∀ i : ℕ, 303055467 ≤ i → i < 303055468 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 303055467 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part6_win_25 : ∀ i : ℕ, 303055468 ≤ i → i < 303255468 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 606110936) (x1 := 606510934) (lo := 606111005) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_26 : ∀ i : ℕ, 303255468 ≤ i → i < 303455468 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 606510936) (x1 := 606910934) (lo := 606511005) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_27 : ∀ i : ℕ, 303455468 ≤ i → i < 303655468 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 606910936) (x1 := 607310934) (lo := 606911005) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_28 : ∀ i : ℕ, 303655468 ≤ i → i < 303855468 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 607310936) (x1 := 607710934) (lo := 607311005) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_29 : ∀ i : ℕ, 303855468 ≤ i → i < 303955572 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 607710936) (x1 := 607911142) (lo := 607711005) (W := 311279)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_303955572 : ∀ i : ℕ, 303955572 ≤ i → i < 303955573 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 303955572 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_31 : ∀ i : ℕ, 303955573 ≤ i → i < 304155573 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 607911146) (x1 := 608311144) (lo := 607911215) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_32 : ∀ i : ℕ, 304155573 ≤ i → i < 304285542 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 608311146) (x1 := 608571082) (lo := 608311215) (W := 371009)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_304285542 : ∀ i : ℕ, 304285542 ≤ i → i < 304285543 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 304285542 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part6_win_34 : ∀ i : ℕ, 304285543 ≤ i → i < 304485543 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 608571086) (x1 := 608971084) (lo := 608571155) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_35 : ∀ i : ℕ, 304485543 ≤ i → i < 304685543 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 608971086) (x1 := 609371084) (lo := 608971155) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_36 : ∀ i : ℕ, 304685543 ≤ i → i < 304885543 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 609371086) (x1 := 609771084) (lo := 609371155) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_37 : ∀ i : ℕ, 304885543 ≤ i → i < 305085543 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 609771086) (x1 := 610171084) (lo := 609771155) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_38 : ∀ i : ℕ, 305085543 ≤ i → i < 305142924 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 610171086) (x1 := 610285846) (lo := 610171155) (W := 225833)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_305142924 : ∀ i : ℕ, 305142924 ≤ i → i < 305142925 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 305142924 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_40 : ∀ i : ℕ, 305142925 ≤ i → i < 305289282 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 610285850) (x1 := 610578562) (lo := 610285919) (W := 403785)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_305289282 : ∀ i : ℕ, 305289282 ≤ i → i < 305289283 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 305289282 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_42 : ∀ i : ℕ, 305289283 ≤ i → i < 305489283 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 610578566) (x1 := 610978564) (lo := 610578635) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_43 : ∀ i : ℕ, 305489283 ≤ i → i < 305689283 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 610978566) (x1 := 611378564) (lo := 610978635) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_44 : ∀ i : ℕ, 305689283 ≤ i → i < 305889283 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 611378566) (x1 := 611778564) (lo := 611378635) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_45 : ∀ i : ℕ, 305889283 ≤ i → i < 306089283 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 611778566) (x1 := 612178564) (lo := 611778635) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_46 : ∀ i : ℕ, 306089283 ≤ i → i < 306223797 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 612178566) (x1 := 612447592) (lo := 612178635) (W := 380099)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_306223797 : ∀ i : ℕ, 306223797 ≤ i → i < 306223798 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 306223797 := by omega
  subst hi
  exact ⟨116717, by decide, by norm_num⟩
private theorem c_part6_win_48 : ∀ i : ℕ, 306223798 ≤ i → i < 306236831 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 612447596) (x1 := 612473660) (lo := 612447665) (W := 137137)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_306236831 : ∀ i : ℕ, 306236831 ≤ i → i < 306236832 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 306236831 := by omega
  subst hi
  exact ⟨117039, by decide, by norm_num⟩
private theorem c_part6_win_50 : ∀ i : ℕ, 306236832 ≤ i → i < 306436832 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 612473664) (x1 := 612873662) (lo := 612473733) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_51 : ∀ i : ℕ, 306436832 ≤ i → i < 306636832 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 612873664) (x1 := 613273662) (lo := 612873733) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_52 : ∀ i : ℕ, 306636832 ≤ i → i < 306643047 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613273664) (x1 := 613286092) (lo := 613273733) (W := 123501)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_306643047 : ∀ i : ℕ, 306643047 ≤ i → i < 306643048 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 306643047 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_54 : ∀ i : ℕ, 306643048 ≤ i → i < 306843048 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613286096) (x1 := 613686094) (lo := 613286165) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_55 : ∀ i : ℕ, 306843048 ≤ i → i < 306886241 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613686096) (x1 := 613772480) (lo := 613686165) (W := 197457)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_306886241 : ∀ i : ℕ, 306886241 ≤ i → i < 306886242 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 306886241 := by omega
  subst hi
  exact ⟨158457, by decide, by norm_num⟩
private theorem c_part6_win_57 : ∀ i : ℕ, 306886242 ≤ i → i < 307086242 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613772484) (x1 := 614172482) (lo := 613772553) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_58 : ∀ i : ℕ, 307086242 ≤ i → i < 307136036 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 614172484) (x1 := 614272070) (lo := 614172553) (W := 210659)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_307136036 : ∀ i : ℕ, 307136036 ≤ i → i < 307136037 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 307136036 := by omega
  subst hi
  exact ⟨126429, by decide, by norm_num⟩
private theorem c_part6_win_60 : ∀ i : ℕ, 307136037 ≤ i → i < 307336037 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 614272074) (x1 := 614672072) (lo := 614272143) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_61 : ∀ i : ℕ, 307336037 ≤ i → i < 307482837 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 614672074) (x1 := 614965672) (lo := 614672143) (W := 404671)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_307482837 : ∀ i : ℕ, 307482837 ≤ i → i < 307482838 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 307482837 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part6_win_63 : ∀ i : ℕ, 307482838 ≤ i → i < 307589097 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 614965676) (x1 := 615178192) (lo := 614965745) (W := 323589)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_307589097 : ∀ i : ℕ, 307589097 ≤ i → i < 307589098 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 307589097 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part6_win_65 : ∀ i : ℕ, 307589098 ≤ i → i < 307631321 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 615178196) (x1 := 615262640) (lo := 615178265) (W := 195517)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_307631321 : ∀ i : ℕ, 307631321 ≤ i → i < 307631322 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 307631321 := by omega
  subst hi
  exact ⟨131337, by decide, by norm_num⟩
private theorem c_part6_win_67 : ∀ i : ℕ, 307631322 ≤ i → i < 307831322 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 615262644) (x1 := 615662642) (lo := 615262713) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_68 : ∀ i : ℕ, 307831322 ≤ i → i < 308031322 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 615662644) (x1 := 616062642) (lo := 615662713) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_69 : ∀ i : ℕ, 308031322 ≤ i → i < 308231322 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616062644) (x1 := 616462642) (lo := 616062713) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_70 : ∀ i : ℕ, 308231322 ≤ i → i < 308391528 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616462644) (x1 := 616783054) (lo := 616462713) (W := 431483)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_308391528 : ∀ i : ℕ, 308391528 ≤ i → i < 308391529 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 308391528 := by omega
  subst hi
  exact ⟨3361883, by decide, by norm_num⟩
private theorem c_part6_win_72 : ∀ i : ℕ, 308391529 ≤ i → i < 308591529 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616783058) (x1 := 617183056) (lo := 616783127) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_73 : ∀ i : ℕ, 308591529 ≤ i → i < 308625507 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 617183058) (x1 := 617251012) (lo := 617183127) (W := 179027)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_308625507 : ∀ i : ℕ, 308625507 ≤ i → i < 308625508 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 308625507 := by omega
  subst hi
  exact ⟨116357, by decide, by norm_num⟩
private theorem c_part6_win_75 : ∀ i : ℕ, 308625508 ≤ i → i < 308690229 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 617251016) (x1 := 617380456) (lo := 617251085) (W := 240513)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_308690229 : ∀ i : ℕ, 308690229 ≤ i → i < 308690230 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 308690229 := by omega
  subst hi
  exact ⟨125771, by decide, by norm_num⟩
private theorem c_part6_win_77 : ∀ i : ℕ, 308690230 ≤ i → i < 308890230 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 617380460) (x1 := 617780458) (lo := 617380529) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_78 : ∀ i : ℕ, 308890230 ≤ i → i < 308970828 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 617780460) (x1 := 617941654) (lo := 617780529) (W := 272267)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_308970828 : ∀ i : ℕ, 308970828 ≤ i → i < 308970829 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 308970828 := by omega
  subst hi
  exact ⟨122411, by decide, by norm_num⟩
private theorem c_part6_win_80 : ∀ i : ℕ, 308970829 ≤ i → i < 309170829 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 617941658) (x1 := 618341656) (lo := 617941727) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_81 : ∀ i : ℕ, 309170829 ≤ i → i < 309370829 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 618341658) (x1 := 618741656) (lo := 618341727) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_82 : ∀ i : ℕ, 309370829 ≤ i → i < 309570829 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 618741658) (x1 := 619141656) (lo := 618741727) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_83 : ∀ i : ℕ, 309570829 ≤ i → i < 309625782 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619141658) (x1 := 619251562) (lo := 619141727) (W := 220977)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_309625782 : ∀ i : ℕ, 309625782 ≤ i → i < 309625783 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 309625782 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_85 : ∀ i : ℕ, 309625783 ≤ i → i < 309825783 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619251566) (x1 := 619651564) (lo := 619251635) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_86 : ∀ i : ℕ, 309825783 ≤ i → i < 309862344 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619651566) (x1 := 619724686) (lo := 619651635) (W := 184193)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_309862344 : ∀ i : ℕ, 309862344 ≤ i → i < 309862345 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 309862344 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part6_win_88 : ∀ i : ℕ, 309862345 ≤ i → i < 309928518 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619724690) (x1 := 619857034) (lo := 619724759) (W := 243417)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_309928518 : ∀ i : ℕ, 309928518 ≤ i → i < 309928519 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 309928518 := by omega
  subst hi
  exact ⟨3166973, by decide, by norm_num⟩
private theorem c_part6_win_90 : ∀ i : ℕ, 309928519 ≤ i → i < 310067844 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619857038) (x1 := 620135686) (lo := 619857107) (W := 389721)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_310067844 : ∀ i : ℕ, 310067844 ≤ i → i < 310067845 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 310067844 := by omega
  subst hi
  exact ⟨3166973, by decide, by norm_num⟩
private theorem c_part6_win_92 : ∀ i : ℕ, 310067845 ≤ i → i < 310267845 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 620135690) (x1 := 620535688) (lo := 620135759) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_93 : ∀ i : ℕ, 310267845 ≤ i → i < 310467845 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 620535690) (x1 := 620935688) (lo := 620535759) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_94 : ∀ i : ℕ, 310467845 ≤ i → i < 310559547 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 620935690) (x1 := 621119092) (lo := 620935759) (W := 294475)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_310559547 : ∀ i : ℕ, 310559547 ≤ i → i < 310559548 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 310559547 := by omega
  subst hi
  exact ⟨3361883, by decide, by norm_num⟩
private theorem c_part6_win_96 : ∀ i : ℕ, 310559548 ≤ i → i < 310759548 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 621119096) (x1 := 621519094) (lo := 621119165) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_97 : ∀ i : ℕ, 310759548 ≤ i → i < 310862024 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 621519096) (x1 := 621724046) (lo := 621519165) (W := 316023)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_310862024 : ∀ i : ℕ, 310862024 ≤ i → i < 310862025 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 310862024 := by omega
  subst hi
  exact ⟨111213, by decide, by norm_num⟩
private theorem c_part6_win_99 : ∀ i : ℕ, 310862025 ≤ i → i < 311062025 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 621724050) (x1 := 622124048) (lo := 621724119) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_100 : ∀ i : ℕ, 311062025 ≤ i → i < 311085156 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622124050) (x1 := 622170310) (lo := 622124119) (W := 157333)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_311085156 : ∀ i : ℕ, 311085156 ≤ i → i < 311085157 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 311085156 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part6_win_102 : ∀ i : ℕ, 311085157 ≤ i → i < 311285157 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622170314) (x1 := 622570312) (lo := 622170383) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_103 : ∀ i : ℕ, 311285157 ≤ i → i < 311353697 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622570314) (x1 := 622707392) (lo := 622570383) (W := 248151)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_311353697 : ∀ i : ℕ, 311353697 ≤ i → i < 311353698 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 311353697 := by omega
  subst hi
  exact ⟨111213, by decide, by norm_num⟩
private theorem c_part6_win_105 : ∀ i : ℕ, 311353698 ≤ i → i < 311390307 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622707396) (x1 := 622780612) (lo := 622707465) (W := 184289)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_311390307 : ∀ i : ℕ, 311390307 ≤ i → i < 311390308 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 311390307 := by omega
  subst hi
  exact ⟨115217, by decide, by norm_num⟩
private theorem c_part6_win_107 : ∀ i : ℕ, 311390308 ≤ i → i < 311590308 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622780616) (x1 := 623180614) (lo := 622780685) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_108 : ∀ i : ℕ, 311590308 ≤ i → i < 311672469 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 623180616) (x1 := 623344936) (lo := 623180685) (W := 275393)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_311672469 : ∀ i : ℕ, 311672469 ≤ i → i < 311672470 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 311672469 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_110 : ∀ i : ℕ, 311672470 ≤ i → i < 311725104 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 623344940) (x1 := 623450206) (lo := 623345009) (W := 216339)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_311725104 : ∀ i : ℕ, 311725104 ≤ i → i < 311725105 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 311725104 := by omega
  subst hi
  exact ⟨125219, by decide, by norm_num⟩
private theorem c_part6_win_112 : ∀ i : ℕ, 311725105 ≤ i → i < 311925105 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 623450210) (x1 := 623850208) (lo := 623450279) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_113 : ∀ i : ℕ, 311925105 ≤ i → i < 311978172 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 623850210) (x1 := 623956342) (lo := 623850279) (W := 217205)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_311978172 : ∀ i : ℕ, 311978172 ≤ i → i < 311978173 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 311978172 := by omega
  subst hi
  exact ⟨113783, by decide, by norm_num⟩
private theorem c_part6_win_115 : ∀ i : ℕ, 311978173 ≤ i → i < 312057972 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 623956346) (x1 := 624115942) (lo := 623956415) (W := 270669)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_res_312057972 : ∀ i : ℕ, 312057972 ≤ i → i < 312057973 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  have hi : i = 312057972 := by omega
  subst hi
  exact ⟨112979, by decide, by norm_num⟩
private theorem c_part6_win_117 : ∀ i : ℕ, 312057973 ≤ i → i < 312257973 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 624115946) (x1 := 624515944) (lo := 624116015) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_118 : ∀ i : ℕ, 312257973 ≤ i → i < 312457973 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 624515946) (x1 := 624915944) (lo := 624516015) (W := 511071)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_win_119 : ∀ i : ℕ, 312457973 ≤ i → i < 312500000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hi0 hi1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 624915946) (x1 := 624999998) (lo := 624916015) (W := 195125)
    (Ds := offsets.take 170) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * i) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
private theorem c_part6_all : ∀ i : ℕ, 301000000 ≤ i → i < 312500000 →
    ∃ a ∈ offsets, (2 * i + a).Prime := by
  intro i hlo hi
  by_cases h0 : i < 301200000
  · exact c_part6_win_0 i hlo h0
  by_cases h1 : i < 301400000
  · exact c_part6_win_1 i (Nat.not_lt.mp h0) h1
  by_cases h2 : i < 301600000
  · exact c_part6_win_2 i (Nat.not_lt.mp h1) h2
  by_cases h3 : i < 301725729
  · exact c_part6_win_3 i (Nat.not_lt.mp h2) h3
  by_cases h4 : i < 301725730
  · exact c_part6_res_301725729 i (Nat.not_lt.mp h3) h4
  by_cases h5 : i < 301925730
  · exact c_part6_win_5 i (Nat.not_lt.mp h4) h5
  by_cases h6 : i < 301993859
  · exact c_part6_win_6 i (Nat.not_lt.mp h5) h6
  by_cases h7 : i < 301993860
  · exact c_part6_res_301993859 i (Nat.not_lt.mp h6) h7
  by_cases h8 : i < 302193860
  · exact c_part6_win_8 i (Nat.not_lt.mp h7) h8
  by_cases h9 : i < 302389259
  · exact c_part6_win_9 i (Nat.not_lt.mp h8) h9
  by_cases h10 : i < 302389260
  · exact c_part6_res_302389259 i (Nat.not_lt.mp h9) h10
  by_cases h11 : i < 302413284
  · exact c_part6_win_11 i (Nat.not_lt.mp h10) h11
  by_cases h12 : i < 302413285
  · exact c_part6_res_302413284 i (Nat.not_lt.mp h11) h12
  by_cases h13 : i < 302507412
  · exact c_part6_win_13 i (Nat.not_lt.mp h12) h13
  by_cases h14 : i < 302507413
  · exact c_part6_res_302507412 i (Nat.not_lt.mp h13) h14
  by_cases h15 : i < 302607864
  · exact c_part6_win_15 i (Nat.not_lt.mp h14) h15
  by_cases h16 : i < 302607865
  · exact c_part6_res_302607864 i (Nat.not_lt.mp h15) h16
  by_cases h17 : i < 302668872
  · exact c_part6_win_17 i (Nat.not_lt.mp h16) h17
  by_cases h18 : i < 302668873
  · exact c_part6_res_302668872 i (Nat.not_lt.mp h17) h18
  by_cases h19 : i < 302780499
  · exact c_part6_win_19 i (Nat.not_lt.mp h18) h19
  by_cases h20 : i < 302780500
  · exact c_part6_res_302780499 i (Nat.not_lt.mp h19) h20
  by_cases h21 : i < 302975082
  · exact c_part6_win_21 i (Nat.not_lt.mp h20) h21
  by_cases h22 : i < 302975083
  · exact c_part6_res_302975082 i (Nat.not_lt.mp h21) h22
  by_cases h23 : i < 303055467
  · exact c_part6_win_23 i (Nat.not_lt.mp h22) h23
  by_cases h24 : i < 303055468
  · exact c_part6_res_303055467 i (Nat.not_lt.mp h23) h24
  by_cases h25 : i < 303255468
  · exact c_part6_win_25 i (Nat.not_lt.mp h24) h25
  by_cases h26 : i < 303455468
  · exact c_part6_win_26 i (Nat.not_lt.mp h25) h26
  by_cases h27 : i < 303655468
  · exact c_part6_win_27 i (Nat.not_lt.mp h26) h27
  by_cases h28 : i < 303855468
  · exact c_part6_win_28 i (Nat.not_lt.mp h27) h28
  by_cases h29 : i < 303955572
  · exact c_part6_win_29 i (Nat.not_lt.mp h28) h29
  by_cases h30 : i < 303955573
  · exact c_part6_res_303955572 i (Nat.not_lt.mp h29) h30
  by_cases h31 : i < 304155573
  · exact c_part6_win_31 i (Nat.not_lt.mp h30) h31
  by_cases h32 : i < 304285542
  · exact c_part6_win_32 i (Nat.not_lt.mp h31) h32
  by_cases h33 : i < 304285543
  · exact c_part6_res_304285542 i (Nat.not_lt.mp h32) h33
  by_cases h34 : i < 304485543
  · exact c_part6_win_34 i (Nat.not_lt.mp h33) h34
  by_cases h35 : i < 304685543
  · exact c_part6_win_35 i (Nat.not_lt.mp h34) h35
  by_cases h36 : i < 304885543
  · exact c_part6_win_36 i (Nat.not_lt.mp h35) h36
  by_cases h37 : i < 305085543
  · exact c_part6_win_37 i (Nat.not_lt.mp h36) h37
  by_cases h38 : i < 305142924
  · exact c_part6_win_38 i (Nat.not_lt.mp h37) h38
  by_cases h39 : i < 305142925
  · exact c_part6_res_305142924 i (Nat.not_lt.mp h38) h39
  by_cases h40 : i < 305289282
  · exact c_part6_win_40 i (Nat.not_lt.mp h39) h40
  by_cases h41 : i < 305289283
  · exact c_part6_res_305289282 i (Nat.not_lt.mp h40) h41
  by_cases h42 : i < 305489283
  · exact c_part6_win_42 i (Nat.not_lt.mp h41) h42
  by_cases h43 : i < 305689283
  · exact c_part6_win_43 i (Nat.not_lt.mp h42) h43
  by_cases h44 : i < 305889283
  · exact c_part6_win_44 i (Nat.not_lt.mp h43) h44
  by_cases h45 : i < 306089283
  · exact c_part6_win_45 i (Nat.not_lt.mp h44) h45
  by_cases h46 : i < 306223797
  · exact c_part6_win_46 i (Nat.not_lt.mp h45) h46
  by_cases h47 : i < 306223798
  · exact c_part6_res_306223797 i (Nat.not_lt.mp h46) h47
  by_cases h48 : i < 306236831
  · exact c_part6_win_48 i (Nat.not_lt.mp h47) h48
  by_cases h49 : i < 306236832
  · exact c_part6_res_306236831 i (Nat.not_lt.mp h48) h49
  by_cases h50 : i < 306436832
  · exact c_part6_win_50 i (Nat.not_lt.mp h49) h50
  by_cases h51 : i < 306636832
  · exact c_part6_win_51 i (Nat.not_lt.mp h50) h51
  by_cases h52 : i < 306643047
  · exact c_part6_win_52 i (Nat.not_lt.mp h51) h52
  by_cases h53 : i < 306643048
  · exact c_part6_res_306643047 i (Nat.not_lt.mp h52) h53
  by_cases h54 : i < 306843048
  · exact c_part6_win_54 i (Nat.not_lt.mp h53) h54
  by_cases h55 : i < 306886241
  · exact c_part6_win_55 i (Nat.not_lt.mp h54) h55
  by_cases h56 : i < 306886242
  · exact c_part6_res_306886241 i (Nat.not_lt.mp h55) h56
  by_cases h57 : i < 307086242
  · exact c_part6_win_57 i (Nat.not_lt.mp h56) h57
  by_cases h58 : i < 307136036
  · exact c_part6_win_58 i (Nat.not_lt.mp h57) h58
  by_cases h59 : i < 307136037
  · exact c_part6_res_307136036 i (Nat.not_lt.mp h58) h59
  by_cases h60 : i < 307336037
  · exact c_part6_win_60 i (Nat.not_lt.mp h59) h60
  by_cases h61 : i < 307482837
  · exact c_part6_win_61 i (Nat.not_lt.mp h60) h61
  by_cases h62 : i < 307482838
  · exact c_part6_res_307482837 i (Nat.not_lt.mp h61) h62
  by_cases h63 : i < 307589097
  · exact c_part6_win_63 i (Nat.not_lt.mp h62) h63
  by_cases h64 : i < 307589098
  · exact c_part6_res_307589097 i (Nat.not_lt.mp h63) h64
  by_cases h65 : i < 307631321
  · exact c_part6_win_65 i (Nat.not_lt.mp h64) h65
  by_cases h66 : i < 307631322
  · exact c_part6_res_307631321 i (Nat.not_lt.mp h65) h66
  by_cases h67 : i < 307831322
  · exact c_part6_win_67 i (Nat.not_lt.mp h66) h67
  by_cases h68 : i < 308031322
  · exact c_part6_win_68 i (Nat.not_lt.mp h67) h68
  by_cases h69 : i < 308231322
  · exact c_part6_win_69 i (Nat.not_lt.mp h68) h69
  by_cases h70 : i < 308391528
  · exact c_part6_win_70 i (Nat.not_lt.mp h69) h70
  by_cases h71 : i < 308391529
  · exact c_part6_res_308391528 i (Nat.not_lt.mp h70) h71
  by_cases h72 : i < 308591529
  · exact c_part6_win_72 i (Nat.not_lt.mp h71) h72
  by_cases h73 : i < 308625507
  · exact c_part6_win_73 i (Nat.not_lt.mp h72) h73
  by_cases h74 : i < 308625508
  · exact c_part6_res_308625507 i (Nat.not_lt.mp h73) h74
  by_cases h75 : i < 308690229
  · exact c_part6_win_75 i (Nat.not_lt.mp h74) h75
  by_cases h76 : i < 308690230
  · exact c_part6_res_308690229 i (Nat.not_lt.mp h75) h76
  by_cases h77 : i < 308890230
  · exact c_part6_win_77 i (Nat.not_lt.mp h76) h77
  by_cases h78 : i < 308970828
  · exact c_part6_win_78 i (Nat.not_lt.mp h77) h78
  by_cases h79 : i < 308970829
  · exact c_part6_res_308970828 i (Nat.not_lt.mp h78) h79
  by_cases h80 : i < 309170829
  · exact c_part6_win_80 i (Nat.not_lt.mp h79) h80
  by_cases h81 : i < 309370829
  · exact c_part6_win_81 i (Nat.not_lt.mp h80) h81
  by_cases h82 : i < 309570829
  · exact c_part6_win_82 i (Nat.not_lt.mp h81) h82
  by_cases h83 : i < 309625782
  · exact c_part6_win_83 i (Nat.not_lt.mp h82) h83
  by_cases h84 : i < 309625783
  · exact c_part6_res_309625782 i (Nat.not_lt.mp h83) h84
  by_cases h85 : i < 309825783
  · exact c_part6_win_85 i (Nat.not_lt.mp h84) h85
  by_cases h86 : i < 309862344
  · exact c_part6_win_86 i (Nat.not_lt.mp h85) h86
  by_cases h87 : i < 309862345
  · exact c_part6_res_309862344 i (Nat.not_lt.mp h86) h87
  by_cases h88 : i < 309928518
  · exact c_part6_win_88 i (Nat.not_lt.mp h87) h88
  by_cases h89 : i < 309928519
  · exact c_part6_res_309928518 i (Nat.not_lt.mp h88) h89
  by_cases h90 : i < 310067844
  · exact c_part6_win_90 i (Nat.not_lt.mp h89) h90
  by_cases h91 : i < 310067845
  · exact c_part6_res_310067844 i (Nat.not_lt.mp h90) h91
  by_cases h92 : i < 310267845
  · exact c_part6_win_92 i (Nat.not_lt.mp h91) h92
  by_cases h93 : i < 310467845
  · exact c_part6_win_93 i (Nat.not_lt.mp h92) h93
  by_cases h94 : i < 310559547
  · exact c_part6_win_94 i (Nat.not_lt.mp h93) h94
  by_cases h95 : i < 310559548
  · exact c_part6_res_310559547 i (Nat.not_lt.mp h94) h95
  by_cases h96 : i < 310759548
  · exact c_part6_win_96 i (Nat.not_lt.mp h95) h96
  by_cases h97 : i < 310862024
  · exact c_part6_win_97 i (Nat.not_lt.mp h96) h97
  by_cases h98 : i < 310862025
  · exact c_part6_res_310862024 i (Nat.not_lt.mp h97) h98
  by_cases h99 : i < 311062025
  · exact c_part6_win_99 i (Nat.not_lt.mp h98) h99
  by_cases h100 : i < 311085156
  · exact c_part6_win_100 i (Nat.not_lt.mp h99) h100
  by_cases h101 : i < 311085157
  · exact c_part6_res_311085156 i (Nat.not_lt.mp h100) h101
  by_cases h102 : i < 311285157
  · exact c_part6_win_102 i (Nat.not_lt.mp h101) h102
  by_cases h103 : i < 311353697
  · exact c_part6_win_103 i (Nat.not_lt.mp h102) h103
  by_cases h104 : i < 311353698
  · exact c_part6_res_311353697 i (Nat.not_lt.mp h103) h104
  by_cases h105 : i < 311390307
  · exact c_part6_win_105 i (Nat.not_lt.mp h104) h105
  by_cases h106 : i < 311390308
  · exact c_part6_res_311390307 i (Nat.not_lt.mp h105) h106
  by_cases h107 : i < 311590308
  · exact c_part6_win_107 i (Nat.not_lt.mp h106) h107
  by_cases h108 : i < 311672469
  · exact c_part6_win_108 i (Nat.not_lt.mp h107) h108
  by_cases h109 : i < 311672470
  · exact c_part6_res_311672469 i (Nat.not_lt.mp h108) h109
  by_cases h110 : i < 311725104
  · exact c_part6_win_110 i (Nat.not_lt.mp h109) h110
  by_cases h111 : i < 311725105
  · exact c_part6_res_311725104 i (Nat.not_lt.mp h110) h111
  by_cases h112 : i < 311925105
  · exact c_part6_win_112 i (Nat.not_lt.mp h111) h112
  by_cases h113 : i < 311978172
  · exact c_part6_win_113 i (Nat.not_lt.mp h112) h113
  by_cases h114 : i < 311978173
  · exact c_part6_res_311978172 i (Nat.not_lt.mp h113) h114
  by_cases h115 : i < 312057972
  · exact c_part6_win_115 i (Nat.not_lt.mp h114) h115
  by_cases h116 : i < 312057973
  · exact c_part6_res_312057972 i (Nat.not_lt.mp h115) h116
  by_cases h117 : i < 312257973
  · exact c_part6_win_117 i (Nat.not_lt.mp h116) h117
  by_cases h118 : i < 312457973
  · exact c_part6_win_118 i (Nat.not_lt.mp h117) h118
  exact c_part6_win_119 i (Nat.not_lt.mp h118) hi


/-- LEAF: Step 1 of 6 of the index cut, the indices 251000000 up to 261000000. Some
offset of the fixed list makes 2 * j + a prime. The leaf claims nothing about an index
outside this subrange and nothing about the size of the offset, so it is strictly
weaker than the target. -/
theorem cover_lower_part1 :
    ∀ j : ℕ, 251000000 ≤ j → j < 261000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  exact c_part1_all j (by omega) (by omega)

/-- LEAF: Step 2 of 6 of the index cut, the indices 261000000 up to 271000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part2 :
    ∀ j : ℕ, 261000000 ≤ j → j < 271000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  exact c_part2_all j (by omega) (by omega)

/-- LEAF: Step 3 of 6 of the index cut, the indices 271000000 up to 281000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part3 :
    ∀ j : ℕ, 271000000 ≤ j → j < 281000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  exact c_part3_all j (by omega) (by omega)

/-- LEAF: Step 4 of 6 of the index cut, the indices 281000000 up to 291000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part4 :
    ∀ j : ℕ, 281000000 ≤ j → j < 291000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  exact c_part4_all j (by omega) (by omega)

/-- LEAF: Step 5 of 6 of the index cut, the indices 291000000 up to 301000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_lower_part5 :
    ∀ j : ℕ, 291000000 ≤ j → j < 301000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  exact c_part5_all j (by omega) (by omega)

/-- LEAF: Step 6 of 6 of the index cut, the last indices 301000000 up to 312500000; this
one is shorter than ten million indices because the target range stops at 312500000.
Some offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target:
one subrange only, and no size bound on the offset. -/
theorem cover_lower_part6 :
    ∀ j : ℕ, 301000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  exact c_part6_all j (by omega) (by omega)

/-- The integer bookkeeping of the cut: every index of the target range lies in one of
the six subranges above. Arithmetic only, no prime is mentioned. -/
private theorem cover_lower_partition (j : ℕ)
    (hlo : 251000000 ≤ j) (hj : j < 312500000) :
    j < 261000000 ∨ (261000000 ≤ j ∧ j < 271000000) ∨
      (271000000 ≤ j ∧ j < 281000000) ∨ (281000000 ≤ j ∧ j < 291000000) ∨
      (291000000 ≤ j ∧ j < 301000000) ∨ (301000000 ≤ j ∧ j < 312500000) := by
  omega

/-- The offset size estimate of the target, discharged by the whole-list bound of the
certificate data rather than by any new work in this file. -/
private theorem cover_lower_mem_le (a : ℕ) (ha : a ∈ offsets) : a ≤ 10 ^ 300 :=
  offsets_le a ha

/-- The target statement of `cover_lower`, cut into the six index subranges above and
regrouped: each index picks the leaf of its subrange for the prime companion, and the
size of that offset comes from the whole-list estimate. No sorry of its own. -/
theorem cover_lower_split :
    ∀ j : ℕ, 251000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hlo hj
  rcases cover_lower_partition j hlo hj with h1 | ⟨h2, h3⟩ | ⟨h4, h5⟩ | ⟨h6, h7⟩ |
    ⟨h8, h9⟩ | ⟨h10, h11⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part1 j hlo h1
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part2 j h2 h3
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part3 j h4 h5
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part4 j h6 h7
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part5 j h8 h9
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_lower_part6 j h10 h11
    exact ⟨a, ha, cover_lower_mem_le a ha, hp⟩

#print axioms cover_lower_split

end LeanLab.DtRS1998.Decomp455d
