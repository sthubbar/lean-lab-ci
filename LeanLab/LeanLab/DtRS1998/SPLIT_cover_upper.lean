/-
Split of `cover_upper` in `LeanLab.DtRS1998.Decomp455d`.

The target asserts that every index `j` with `312500000 ≤ j < 375000000` has an offset
`a` in the fixed list `offsets` with `a ≤ 10 ^ 300` and `2 * j + a` prime. This file cuts
that index range into six consecutive subranges, one leaf per subrange, and regroups
them with an integer partition proved inside `cover_upper_split`.

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

/-- Certificate window: the indices `312500000 ≤ j < 313000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118037` bits from `625000069`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_0 :
    ∀ j : ℕ, 312500000 ≤ j → j < 313000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 625000000) (x1 := 625999998) (lo := 625000069) (W := 1118037)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `313000000 ≤ j < 313500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1100363` bits from `626000069`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_1 :
    ∀ j : ℕ, 313000000 ≤ j → j < 313500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 626000000) (x1 := 626999998) (lo := 626000069) (W := 1100363)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `313500000 ≤ j < 314000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `627000069`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_2 :
    ∀ j : ℕ, 313500000 ≤ j → j < 314000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 627000000) (x1 := 627999998) (lo := 627000069) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `314000000 ≤ j < 314316972`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`743643` bits from `628000069`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_3 :
    ∀ j : ℕ, 314000000 ≤ j → j < 314316972 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 628000000) (x1 := 628633942) (lo := 628000069) (W := 743643)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 314316972`: its covering offset `125219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125219 = 628759163` by `minFac`. -/
private theorem cu_p1_4 :
    ∀ j : ℕ, 314316972 ≤ j → j < 314316973 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 314316972 := by omega
  subst hj
  refine ⟨125219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `314316973 ≤ j < 314658572`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`796911` bits from `628634015`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_5 :
    ∀ j : ℕ, 314316973 ≤ j → j < 314658572 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 628633946) (x1 := 629317142) (lo := 628634015) (W := 796911)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 314658572`: its covering offset `131337` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131337 = 629448481` by `minFac`. -/
private theorem cu_p1_6 :
    ∀ j : ℕ, 314658572 ≤ j → j < 314658573 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 314658572 := by omega
  subst hj
  refine ⟨131337, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `314658573 ≤ j < 315158573`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `629317215`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_7 :
    ∀ j : ℕ, 314658573 ≤ j → j < 315158573 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 629317146) (x1 := 630317144) (lo := 629317215) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `315158573 ≤ j < 315549939`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`891943` bits from `630317215`), the offsets being the
first `166` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_8 :
    ∀ j : ℕ, 315158573 ≤ j → j < 315549939 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 630317146) (x1 := 631099876) (lo := 630317215) (W := 891943)
    (Ds := offsets.take 166) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 315549939`: its covering offset `133391` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 133391 = 631233269` by `minFac`. -/
private theorem cu_p1_9 :
    ∀ j : ℕ, 315549939 ≤ j → j < 315549940 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 315549939 := by omega
  subst hj
  refine ⟨133391, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `315549940 ≤ j < 315849609`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`715625` bits from `631099949`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_10 :
    ∀ j : ℕ, 315549940 ≤ j → j < 315849609 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 631099880) (x1 := 631699216) (lo := 631099949) (W := 715625)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 315849609`: its covering offset `122411` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 122411 = 631821629` by `minFac`. -/
private theorem cu_p1_11 :
    ∀ j : ℕ, 315849609 ≤ j → j < 315849610 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 315849609 := by omega
  subst hj
  refine ⟨122411, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `315849610 ≤ j < 316349610`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1107261` bits from `631699289`), the offsets being the
first `163` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_12 :
    ∀ j : ℕ, 315849610 ≤ j → j < 316349610 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 631699220) (x1 := 632699218) (lo := 631699289) (W := 1107261)
    (Ds := offsets.take 163) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `316349610 ≤ j < 316522172`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`446603` bits from `632699289`), the offsets being the
first `159` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_13 :
    ∀ j : ℕ, 316349610 ≤ j → j < 316522172 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 632699220) (x1 := 633044342) (lo := 632699289) (W := 446603)
    (Ds := offsets.take 159) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 316522172`: its covering offset `126429` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 126429 = 633170773` by `minFac`. -/
private theorem cu_p1_14 :
    ∀ j : ℕ, 316522172 ≤ j → j < 316522173 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 316522172 := by omega
  subst hj
  refine ⟨126429, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `316522173 ≤ j < 317022173`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1104771` bits from `633044415`), the offsets being the
first `162` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_15 :
    ∀ j : ℕ, 316522173 ≤ j → j < 317022173 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 633044346) (x1 := 634044344) (lo := 633044415) (W := 1104771)
    (Ds := offsets.take 162) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `317022173 ≤ j < 317522173`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `634044415`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_16 :
    ∀ j : ℕ, 317022173 ≤ j → j < 317522173 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 634044346) (x1 := 635044344) (lo := 634044415) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `317522173 ≤ j < 317858307`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`787415` bits from `635044415`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_17 :
    ∀ j : ℕ, 317522173 ≤ j → j < 317858307 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 635044346) (x1 := 635716612) (lo := 635044415) (W := 787415)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 317858307`: its covering offset `1668413` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1668413 = 637385027` by `minFac`. -/
private theorem cu_p1_18 :
    ∀ j : ℕ, 317858307 ≤ j → j < 317858308 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 317858307 := by omega
  subst hj
  refine ⟨1668413, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `317858308 ≤ j < 318140391`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`664209` bits from `635716685`), the offsets being the
first `155` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_19 :
    ∀ j : ℕ, 317858308 ≤ j → j < 318140391 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 635716616) (x1 := 636280780) (lo := 635716685) (W := 664209)
    (Ds := offsets.take 155) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 318140391`: its covering offset `122411` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 122411 = 636403193` by `minFac`. -/
private theorem cu_p1_20 :
    ∀ j : ℕ, 318140391 ≤ j → j < 318140392 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 318140391 := by omega
  subst hj
  refine ⟨122411, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `318140392 ≤ j < 318147687`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`109703` bits from `636280853`), the offsets being the
first `144` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_21 :
    ∀ j : ℕ, 318140392 ≤ j → j < 318147687 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 636280784) (x1 := 636295372) (lo := 636280853) (W := 109703)
    (Ds := offsets.take 144) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 318147687`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 637629563` by `minFac`. -/
private theorem cu_p1_22 :
    ∀ j : ℕ, 318147687 ≤ j → j < 318147688 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 318147687 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `318147688 ≤ j < 318647688`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1112909` bits from `636295445`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_23 :
    ∀ j : ℕ, 318147688 ≤ j → j < 318647688 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 636295376) (x1 := 637295374) (lo := 636295445) (W := 1112909)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `318647688 ≤ j < 319147688`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `637295445`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_24 :
    ∀ j : ℕ, 318647688 ≤ j → j < 319147688 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 637295376) (x1 := 638295374) (lo := 637295445) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `319147688 ≤ j < 319647688`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `638295445`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_25 :
    ∀ j : ℕ, 319147688 ≤ j → j < 319647688 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 638295376) (x1 := 639295374) (lo := 638295445) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `319647688 ≤ j < 320147688`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116953` bits from `639295445`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_26 :
    ∀ j : ℕ, 319647688 ≤ j → j < 320147688 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 639295376) (x1 := 640295374) (lo := 639295445) (W := 1116953)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `320147688 ≤ j < 320647688`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `640295445`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_27 :
    ∀ j : ℕ, 320147688 ≤ j → j < 320647688 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 640295376) (x1 := 641295374) (lo := 640295445) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `320647688 ≤ j < 320832147`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`486955` bits from `641295445`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_28 :
    ∀ j : ℕ, 320647688 ≤ j → j < 320832147 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 641295376) (x1 := 641664292) (lo := 641295445) (W := 486955)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 320832147`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 641787827` by `minFac`. -/
private theorem cu_p1_29 :
    ∀ j : ℕ, 320832147 ≤ j → j < 320832148 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 320832147 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `320832148 ≤ j < 321174324`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`799499` bits from `641664365`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_30 :
    ∀ j : ℕ, 320832148 ≤ j → j < 321174324 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 641664296) (x1 := 642348646) (lo := 641664365) (W := 799499)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 321174324`: its covering offset `131189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131189 = 642479837` by `minFac`. -/
private theorem cu_p1_31 :
    ∀ j : ℕ, 321174324 ≤ j → j < 321174325 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 321174324 := by omega
  subst hj
  refine ⟨131189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `321174325 ≤ j < 321674325`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1110357` bits from `642348719`), the offsets being the
first `169` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_32 :
    ∀ j : ℕ, 321174325 ≤ j → j < 321674325 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 642348650) (x1 := 643348648) (lo := 642348719) (W := 1110357)
    (Ds := offsets.take 169) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `321674325 ≤ j < 322046337`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`853723` bits from `643348719`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_33 :
    ∀ j : ℕ, 321674325 ≤ j → j < 322046337 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 643348650) (x1 := 644092672) (lo := 643348719) (W := 853723)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 322046337`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 645426863` by `minFac`. -/
private theorem cu_p1_34 :
    ∀ j : ℕ, 322046337 ≤ j → j < 322046338 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 322046337 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `322046338 ≤ j < 322131927`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`281535` bits from `644092745`), the offsets being the
first `169` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_35 :
    ∀ j : ℕ, 322046338 ≤ j → j < 322131927 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 644092676) (x1 := 644263852) (lo := 644092745) (W := 281535)
    (Ds := offsets.take 169) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 322131927`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 645598043` by `minFac`. -/
private theorem cu_p1_36 :
    ∀ j : ℕ, 322131927 ≤ j → j < 322131928 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 322131927 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `322131928 ≤ j < 322631928`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1100363` bits from `644263925`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_37 :
    ∀ j : ℕ, 322131928 ≤ j → j < 322631928 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 644263856) (x1 := 645263854) (lo := 644263925) (W := 1100363)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `322631928 ≤ j < 322694166`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`234175` bits from `645263925`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_38 :
    ∀ j : ℕ, 322631928 ≤ j → j < 322694166 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 645263856) (x1 := 645388330) (lo := 645263925) (W := 234175)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 322694166`: its covering offset `125219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125219 = 645513551` by `minFac`. -/
private theorem cu_p1_39 :
    ∀ j : ℕ, 322694166 ≤ j → j < 322694167 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 322694166 := by omega
  subst hj
  refine ⟨125219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `322694167 ≤ j < 323000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`724575` bits from `645388403`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p1_40 :
    ∀ j : ℕ, 322694167 ≤ j → j < 323000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 645388334) (x1 := 645999998) (lo := 645388403) (W := 724575)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- LEAF: Step 1 of 6 of the index cut, the indices 312500000 up to 323000000. Some
offset of the fixed list makes 2 * j + a prime. The leaf claims nothing about an index
outside this subrange and nothing about the size of the offset, so it is strictly
weaker than the target. -/
theorem cover_upper_part1 :
    ∀ j : ℕ, 312500000 ≤ j → j < 323000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  by_cases h0 : j < 313000000
  · exact cu_p1_0 j (by omega) h0
  by_cases h1 : j < 313500000
  · exact cu_p1_1 j (by omega) h1
  by_cases h2 : j < 314000000
  · exact cu_p1_2 j (by omega) h2
  by_cases h3 : j < 314316972
  · exact cu_p1_3 j (by omega) h3
  by_cases h4 : j < 314316973
  · exact cu_p1_4 j (by omega) h4
  by_cases h5 : j < 314658572
  · exact cu_p1_5 j (by omega) h5
  by_cases h6 : j < 314658573
  · exact cu_p1_6 j (by omega) h6
  by_cases h7 : j < 315158573
  · exact cu_p1_7 j (by omega) h7
  by_cases h8 : j < 315549939
  · exact cu_p1_8 j (by omega) h8
  by_cases h9 : j < 315549940
  · exact cu_p1_9 j (by omega) h9
  by_cases h10 : j < 315849609
  · exact cu_p1_10 j (by omega) h10
  by_cases h11 : j < 315849610
  · exact cu_p1_11 j (by omega) h11
  by_cases h12 : j < 316349610
  · exact cu_p1_12 j (by omega) h12
  by_cases h13 : j < 316522172
  · exact cu_p1_13 j (by omega) h13
  by_cases h14 : j < 316522173
  · exact cu_p1_14 j (by omega) h14
  by_cases h15 : j < 317022173
  · exact cu_p1_15 j (by omega) h15
  by_cases h16 : j < 317522173
  · exact cu_p1_16 j (by omega) h16
  by_cases h17 : j < 317858307
  · exact cu_p1_17 j (by omega) h17
  by_cases h18 : j < 317858308
  · exact cu_p1_18 j (by omega) h18
  by_cases h19 : j < 318140391
  · exact cu_p1_19 j (by omega) h19
  by_cases h20 : j < 318140392
  · exact cu_p1_20 j (by omega) h20
  by_cases h21 : j < 318147687
  · exact cu_p1_21 j (by omega) h21
  by_cases h22 : j < 318147688
  · exact cu_p1_22 j (by omega) h22
  by_cases h23 : j < 318647688
  · exact cu_p1_23 j (by omega) h23
  by_cases h24 : j < 319147688
  · exact cu_p1_24 j (by omega) h24
  by_cases h25 : j < 319647688
  · exact cu_p1_25 j (by omega) h25
  by_cases h26 : j < 320147688
  · exact cu_p1_26 j (by omega) h26
  by_cases h27 : j < 320647688
  · exact cu_p1_27 j (by omega) h27
  by_cases h28 : j < 320832147
  · exact cu_p1_28 j (by omega) h28
  by_cases h29 : j < 320832148
  · exact cu_p1_29 j (by omega) h29
  by_cases h30 : j < 321174324
  · exact cu_p1_30 j (by omega) h30
  by_cases h31 : j < 321174325
  · exact cu_p1_31 j (by omega) h31
  by_cases h32 : j < 321674325
  · exact cu_p1_32 j (by omega) h32
  by_cases h33 : j < 322046337
  · exact cu_p1_33 j (by omega) h33
  by_cases h34 : j < 322046338
  · exact cu_p1_34 j (by omega) h34
  by_cases h35 : j < 322131927
  · exact cu_p1_35 j (by omega) h35
  by_cases h36 : j < 322131928
  · exact cu_p1_36 j (by omega) h36
  by_cases h37 : j < 322631928
  · exact cu_p1_37 j (by omega) h37
  by_cases h38 : j < 322694166
  · exact cu_p1_38 j (by omega) h38
  by_cases h39 : j < 322694167
  · exact cu_p1_39 j (by omega) h39
  exact cu_p1_40 j (by omega) h1

/-- Certificate window: the indices `323000000 ≤ j < 323500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118037` bits from `646000069`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_0 :
    ∀ j : ℕ, 323000000 ≤ j → j < 323500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 646000000) (x1 := 646999998) (lo := 646000069) (W := 1118037)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `323500000 ≤ j < 323601443`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`294157` bits from `647000069`), the offsets being the
first `140` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_1 :
    ∀ j : ℕ, 323500000 ≤ j → j < 323601443 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 647000000) (x1 := 647202884) (lo := 647000069) (W := 294157)
    (Ds := offsets.take 140) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 323601443`: its covering offset `2240913` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 2240913 = 649443799` by `minFac`. -/
private theorem cu_p2_2 :
    ∀ j : ℕ, 323601443 ≤ j → j < 323601444 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 323601443 := by omega
  subst hj
  refine ⟨2240913, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `323601444 ≤ j < 324038184`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`988627` bits from `647202957`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_3 :
    ∀ j : ℕ, 323601444 ≤ j → j < 324038184 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 647202888) (x1 := 648076366) (lo := 647202957) (W := 988627)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 324038184`: its covering offset `122411` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 122411 = 648198779` by `minFac`. -/
private theorem cu_p2_4 :
    ∀ j : ℕ, 324038184 ≤ j → j < 324038185 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 324038184 := by omega
  subst hj
  refine ⟨122411, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `324038185 ≤ j < 324286212`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`609767` bits from `648076439`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_5 :
    ∀ j : ℕ, 324038185 ≤ j → j < 324286212 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 648076370) (x1 := 648572422) (lo := 648076439) (W := 609767)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 324286212`: its covering offset `3166973` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3166973 = 651739397` by `minFac`. -/
private theorem cu_p2_6 :
    ∀ j : ℕ, 324286212 ≤ j → j < 324286213 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 324286212 := by omega
  subst hj
  refine ⟨3166973, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `324286213 ≤ j < 324339222`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`200187` bits from `648572495`), the offsets being the
first `143` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_7 :
    ∀ j : ℕ, 324286213 ≤ j → j < 324339222 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 648572426) (x1 := 648678442) (lo := 648572495) (W := 200187)
    (Ds := offsets.take 143) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 324339222`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 648801977` by `minFac`. -/
private theorem cu_p2_8 :
    ∀ j : ℕ, 324339222 ≤ j → j < 324339223 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 324339222 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `324339223 ≤ j < 324405789`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`223185` bits from `648678515`), the offsets being the
first `138` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_9 :
    ∀ j : ℕ, 324339223 ≤ j → j < 324405789 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 648678446) (x1 := 648811576) (lo := 648678515) (W := 223185)
    (Ds := offsets.take 138) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 324405789`: its covering offset `125771` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125771 = 648937349` by `minFac`. -/
private theorem cu_p2_10 :
    ∀ j : ℕ, 324405789 ≤ j → j < 324405790 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 324405789 := by omega
  subst hj
  refine ⟨125771, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `324405790 ≤ j < 324673236`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`639663` bits from `648811649`), the offsets being the
first `162` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_11 :
    ∀ j : ℕ, 324405790 ≤ j → j < 324673236 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 648811580) (x1 := 649346470) (lo := 648811649) (W := 639663)
    (Ds := offsets.take 162) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 324673236`: its covering offset `336179` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 336179 = 649682651` by `minFac`. -/
private theorem cu_p2_12 :
    ∀ j : ℕ, 324673236 ≤ j → j < 324673237 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 324673236 := by omega
  subst hj
  refine ⟨336179, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `324673237 ≤ j < 324780234`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`304047` bits from `649346543`), the offsets being the
first `138` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_13 :
    ∀ j : ℕ, 324673237 ≤ j → j < 324780234 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 649346474) (x1 := 649560466) (lo := 649346543) (W := 304047)
    (Ds := offsets.take 138) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 324780234`: its covering offset `125771` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125771 = 649686239` by `minFac`. -/
private theorem cu_p2_14 :
    ∀ j : ℕ, 324780234 ≤ j → j < 324780235 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 324780234 := by omega
  subst hj
  refine ⟨125771, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `324780235 ≤ j < 325280235`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `649560539`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_15 :
    ∀ j : ℕ, 324780235 ≤ j → j < 325280235 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 649560470) (x1 := 650560468) (lo := 649560539) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `325280235 ≤ j < 325481874`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`501679` bits from `650560539`), the offsets being the
first `150` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_16 :
    ∀ j : ℕ, 325280235 ≤ j → j < 325481874 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 650560470) (x1 := 650963746) (lo := 650560539) (W := 501679)
    (Ds := offsets.take 150) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 325481874`: its covering offset `1668413` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1668413 = 652632161` by `minFac`. -/
private theorem cu_p2_17 :
    ∀ j : ℕ, 325481874 ≤ j → j < 325481875 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 325481874 := by omega
  subst hj
  refine ⟨1668413, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `325481875 ≤ j < 325981875`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1112909` bits from `650963819`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_18 :
    ∀ j : ℕ, 325481875 ≤ j → j < 325981875 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 650963750) (x1 := 651963748) (lo := 650963819) (W := 1112909)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `325981875 ≤ j < 326100828`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`329707` bits from `651963819`), the offsets being the
first `141` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_19 :
    ∀ j : ℕ, 325981875 ≤ j → j < 326100828 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 651963750) (x1 := 652201654) (lo := 651963819) (W := 329707)
    (Ds := offsets.take 141) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 326100828`: its covering offset `122411` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 122411 = 652324067` by `minFac`. -/
private theorem cu_p2_20 :
    ∀ j : ℕ, 326100828 ≤ j → j < 326100829 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 326100828 := by omega
  subst hj
  refine ⟨122411, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `326100829 ≤ j < 326600829`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116647` bits from `652201727`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_21 :
    ∀ j : ℕ, 326100829 ≤ j → j < 326600829 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 652201658) (x1 := 653201656) (lo := 652201727) (W := 1116647)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `326600829 ≤ j < 326844939`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`584237` bits from `653201727`), the offsets being the
first `145` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_22 :
    ∀ j : ℕ, 326600829 ≤ j → j < 326844939 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 653201658) (x1 := 653689876) (lo := 653201727) (W := 584237)
    (Ds := offsets.take 145) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 326844939`: its covering offset `127301` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 127301 = 653817179` by `minFac`. -/
private theorem cu_p2_23 :
    ∀ j : ℕ, 326844939 ≤ j → j < 326844940 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 326844939 := by omega
  subst hj
  refine ⟨127301, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `326844940 ≤ j < 327076397`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`576627` bits from `653689949`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_24 :
    ∀ j : ℕ, 326844940 ≤ j → j < 327076397 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 653689880) (x1 := 654152792) (lo := 653689949) (W := 576627)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 327076397`: its covering offset `124449` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 124449 = 654277243` by `minFac`. -/
private theorem cu_p2_25 :
    ∀ j : ℕ, 327076397 ≤ j → j < 327076398 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 327076397 := by omega
  subst hj
  refine ⟨124449, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `327076398 ≤ j < 327576398`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `654152865`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_26 :
    ∀ j : ℕ, 327076398 ≤ j → j < 327576398 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 654152796) (x1 := 655152794) (lo := 654152865) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `327576398 ≤ j < 328076398`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1111143` bits from `655152865`), the offsets being the
first `171` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_27 :
    ∀ j : ℕ, 327576398 ≤ j → j < 328076398 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 655152796) (x1 := 656152794) (lo := 655152865) (W := 1111143)
    (Ds := offsets.take 171) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `328076398 ≤ j < 328576398`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `656152865`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_28 :
    ∀ j : ℕ, 328076398 ≤ j → j < 328576398 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 656152796) (x1 := 657152794) (lo := 656152865) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `328576398 ≤ j < 329076398`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `657152865`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_29 :
    ∀ j : ℕ, 328576398 ≤ j → j < 329076398 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 657152796) (x1 := 658152794) (lo := 657152865) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `329076398 ≤ j < 329314437`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`591225` bits from `658152865`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_30 :
    ∀ j : ℕ, 329076398 ≤ j → j < 329314437 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 658152796) (x1 := 658628872) (lo := 658152865) (W := 591225)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 329314437`: its covering offset `336179` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 336179 = 658965053` by `minFac`. -/
private theorem cu_p2_31 :
    ∀ j : ℕ, 329314437 ≤ j → j < 329314438 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 329314437 := by omega
  subst hj
  refine ⟨336179, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `329314438 ≤ j < 329814438`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `658628945`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_32 :
    ∀ j : ℕ, 329314438 ≤ j → j < 329814438 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 658628876) (x1 := 659628874) (lo := 658628945) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `329814438 ≤ j < 330314438`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116953` bits from `659628945`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_33 :
    ∀ j : ℕ, 329814438 ≤ j → j < 330314438 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 659628876) (x1 := 660628874) (lo := 659628945) (W := 1116953)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `330314438 ≤ j < 330814438`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `660628945`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_34 :
    ∀ j : ℕ, 330314438 ≤ j → j < 330814438 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 660628876) (x1 := 661628874) (lo := 660628945) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `330814438 ≤ j < 331134648`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`756707` bits from `661628945`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_35 :
    ∀ j : ℕ, 330814438 ≤ j → j < 331134648 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 661628876) (x1 := 662269294) (lo := 661628945) (W := 756707)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 331134648`: its covering offset `131207` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131207 = 662400503` by `minFac`. -/
private theorem cu_p2_36 :
    ∀ j : ℕ, 331134648 ≤ j → j < 331134649 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 331134648 := by omega
  subst hj
  refine ⟨131207, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `331134649 ≤ j < 331634649`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `662269367`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_37 :
    ∀ j : ℕ, 331134649 ≤ j → j < 331634649 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 662269298) (x1 := 663269296) (lo := 662269367) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `331634649 ≤ j < 332134649`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1112909` bits from `663269367`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_38 :
    ∀ j : ℕ, 331634649 ≤ j → j < 332134649 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 663269298) (x1 := 664269296) (lo := 663269367) (W := 1112909)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `332134649 ≤ j < 332589453`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1027645` bits from `664269367`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_39 :
    ∀ j : ℕ, 332134649 ≤ j → j < 332589453 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 664269298) (x1 := 665178904) (lo := 664269367) (W := 1027645)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 332589453`: its covering offset `969173` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 969173 = 666148079` by `minFac`. -/
private theorem cu_p2_40 :
    ∀ j : ℕ, 332589453 ≤ j → j < 332589454 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 332589453 := by omega
  subst hj
  refine ⟨969173, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `332589454 ≤ j < 333089454`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `665178977`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_41 :
    ∀ j : ℕ, 332589454 ≤ j → j < 333089454 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 665178908) (x1 := 666178906) (lo := 665178977) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `333089454 ≤ j < 333500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`930731` bits from `666178977`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p2_42 :
    ∀ j : ℕ, 333089454 ≤ j → j < 333500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 666178908) (x1 := 666999998) (lo := 666178977) (W := 930731)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- LEAF: Step 2 of 6 of the index cut, the indices 323000000 up to 333500000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part2 :
    ∀ j : ℕ, 323000000 ≤ j → j < 333500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  by_cases h0 : j < 323500000
  · exact cu_p2_0 j (by omega) h0
  by_cases h1 : j < 323601443
  · exact cu_p2_1 j (by omega) h1
  by_cases h2 : j < 323601444
  · exact cu_p2_2 j (by omega) h2
  by_cases h3 : j < 324038184
  · exact cu_p2_3 j (by omega) h3
  by_cases h4 : j < 324038185
  · exact cu_p2_4 j (by omega) h4
  by_cases h5 : j < 324286212
  · exact cu_p2_5 j (by omega) h5
  by_cases h6 : j < 324286213
  · exact cu_p2_6 j (by omega) h6
  by_cases h7 : j < 324339222
  · exact cu_p2_7 j (by omega) h7
  by_cases h8 : j < 324339223
  · exact cu_p2_8 j (by omega) h8
  by_cases h9 : j < 324405789
  · exact cu_p2_9 j (by omega) h9
  by_cases h10 : j < 324405790
  · exact cu_p2_10 j (by omega) h10
  by_cases h11 : j < 324673236
  · exact cu_p2_11 j (by omega) h11
  by_cases h12 : j < 324673237
  · exact cu_p2_12 j (by omega) h12
  by_cases h13 : j < 324780234
  · exact cu_p2_13 j (by omega) h13
  by_cases h14 : j < 324780235
  · exact cu_p2_14 j (by omega) h14
  by_cases h15 : j < 325280235
  · exact cu_p2_15 j (by omega) h15
  by_cases h16 : j < 325481874
  · exact cu_p2_16 j (by omega) h16
  by_cases h17 : j < 325481875
  · exact cu_p2_17 j (by omega) h17
  by_cases h18 : j < 325981875
  · exact cu_p2_18 j (by omega) h18
  by_cases h19 : j < 326100828
  · exact cu_p2_19 j (by omega) h19
  by_cases h20 : j < 326100829
  · exact cu_p2_20 j (by omega) h20
  by_cases h21 : j < 326600829
  · exact cu_p2_21 j (by omega) h21
  by_cases h22 : j < 326844939
  · exact cu_p2_22 j (by omega) h22
  by_cases h23 : j < 326844940
  · exact cu_p2_23 j (by omega) h23
  by_cases h24 : j < 327076397
  · exact cu_p2_24 j (by omega) h24
  by_cases h25 : j < 327076398
  · exact cu_p2_25 j (by omega) h25
  by_cases h26 : j < 327576398
  · exact cu_p2_26 j (by omega) h26
  by_cases h27 : j < 328076398
  · exact cu_p2_27 j (by omega) h27
  by_cases h28 : j < 328576398
  · exact cu_p2_28 j (by omega) h28
  by_cases h29 : j < 329076398
  · exact cu_p2_29 j (by omega) h29
  by_cases h30 : j < 329314437
  · exact cu_p2_30 j (by omega) h30
  by_cases h31 : j < 329314438
  · exact cu_p2_31 j (by omega) h31
  by_cases h32 : j < 329814438
  · exact cu_p2_32 j (by omega) h32
  by_cases h33 : j < 330314438
  · exact cu_p2_33 j (by omega) h33
  by_cases h34 : j < 330814438
  · exact cu_p2_34 j (by omega) h34
  by_cases h35 : j < 331134648
  · exact cu_p2_35 j (by omega) h35
  by_cases h36 : j < 331134649
  · exact cu_p2_36 j (by omega) h36
  by_cases h37 : j < 331634649
  · exact cu_p2_37 j (by omega) h37
  by_cases h38 : j < 332134649
  · exact cu_p2_38 j (by omega) h38
  by_cases h39 : j < 332589453
  · exact cu_p2_39 j (by omega) h39
  by_cases h40 : j < 332589454
  · exact cu_p2_40 j (by omega) h40
  by_cases h41 : j < 333089454
  · exact cu_p2_41 j (by omega) h41
  exact cu_p2_42 j (by omega) h1

/-- Certificate window: the indices `333500000 ≤ j < 333524694`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`132841` bits from `667000069`), the offsets being the
first `127` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_0 :
    ∀ j : ℕ, 333500000 ≤ j → j < 333524694 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 667000000) (x1 := 667049386) (lo := 667000069) (W := 132841)
    (Ds := offsets.take 127) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 333524694`: its covering offset `3361883` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3361883 = 670411271` by `minFac`. -/
private theorem cu_p3_1 :
    ∀ j : ℕ, 333524694 ≤ j → j < 333524695 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 333524694 := by omega
  subst hj
  refine ⟨3361883, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `333524695 ≤ j < 334024695`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1104771` bits from `667049459`), the offsets being the
first `162` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_2 :
    ∀ j : ℕ, 333524695 ≤ j → j < 334024695 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 667049390) (x1 := 668049388) (lo := 667049459) (W := 1104771)
    (Ds := offsets.take 162) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `334024695 ≤ j < 334192494`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`440345` bits from `668049459`), the offsets being the
first `161` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_3 :
    ∀ j : ℕ, 334024695 ≤ j → j < 334192494 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 668049390) (x1 := 668384986) (lo := 668049459) (W := 440345)
    (Ds := offsets.take 161) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 334192494`: its covering offset `127301` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 127301 = 668512289` by `minFac`. -/
private theorem cu_p3_4 :
    ∀ j : ℕ, 334192494 ≤ j → j < 334192495 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 334192494 := by omega
  subst hj
  refine ⟨127301, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `334192495 ≤ j < 334692495`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115331` bits from `668385059`), the offsets being the
first `176` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_5 :
    ∀ j : ℕ, 334192495 ≤ j → j < 334692495 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 668384990) (x1 := 669384988) (lo := 668385059) (W := 1115331)
    (Ds := offsets.take 176) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `334692495 ≤ j < 335192495`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `669385059`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_6 :
    ∀ j : ℕ, 334692495 ≤ j → j < 335192495 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 669384990) (x1 := 670384988) (lo := 669385059) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `335192495 ≤ j < 335692495`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `670385059`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_7 :
    ∀ j : ℕ, 335192495 ≤ j → j < 335692495 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 670384990) (x1 := 671384988) (lo := 670385059) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `335692495 ≤ j < 336192495`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118349` bits from `671385059`), the offsets being the
first `182` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_8 :
    ∀ j : ℕ, 335692495 ≤ j → j < 336192495 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 671384990) (x1 := 672384988) (lo := 671385059) (W := 1118349)
    (Ds := offsets.take 182) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `336192495 ≤ j < 336557079`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`838867` bits from `672385059`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_9 :
    ∀ j : ℕ, 336192495 ≤ j → j < 336557079 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 672384990) (x1 := 673114156) (lo := 672385059) (W := 838867)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 336557079`: its covering offset `125771` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125771 = 673239929` by `minFac`. -/
private theorem cu_p3_10 :
    ∀ j : ℕ, 336557079 ≤ j → j < 336557080 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 336557079 := by omega
  subst hj
  refine ⟨125771, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `336557080 ≤ j < 337057080`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `673114229`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_11 :
    ∀ j : ℕ, 336557080 ≤ j → j < 337057080 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 673114160) (x1 := 674114158) (lo := 673114229) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `337057080 ≤ j < 337088049`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`171577` bits from `674114229`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_12 :
    ∀ j : ℕ, 337057080 ≤ j → j < 337088049 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 674114160) (x1 := 674176096) (lo := 674114229) (W := 171577)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 337088049`: its covering offset `336179` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 336179 = 674512277` by `minFac`. -/
private theorem cu_p3_13 :
    ∀ j : ℕ, 337088049 ≤ j → j < 337088050 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 337088049 := by omega
  subst hj
  refine ⟨336179, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `337088050 ≤ j < 337588050`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `674176169`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_14 :
    ∀ j : ℕ, 337088050 ≤ j → j < 337588050 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 674176100) (x1 := 675176098) (lo := 674176169) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `337588050 ≤ j < 337605783`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`135829` bits from `675176169`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_15 :
    ∀ j : ℕ, 337588050 ≤ j → j < 337605783 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 675176100) (x1 := 675211564) (lo := 675176169) (W := 135829)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 337605783`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 675335099` by `minFac`. -/
private theorem cu_p3_16 :
    ∀ j : ℕ, 337605783 ≤ j → j < 337605784 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 337605783 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `337605784 ≤ j < 338105784`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `675211637`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_17 :
    ∀ j : ℕ, 337605784 ≤ j → j < 338105784 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 675211568) (x1 := 676211566) (lo := 675211637) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `338105784 ≤ j < 338605784`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `676211637`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_18 :
    ∀ j : ℕ, 338105784 ≤ j → j < 338605784 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 676211568) (x1 := 677211566) (lo := 676211637) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `338605784 ≤ j < 338766068`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`437537` bits from `677211637`), the offsets being the
first `180` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_19 :
    ∀ j : ℕ, 338605784 ≤ j → j < 338766068 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 677211568) (x1 := 677532134) (lo := 677211637) (W := 437537)
    (Ds := offsets.take 180) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 338766068`: its covering offset `2240913` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 2240913 = 679773049` by `minFac`. -/
private theorem cu_p3_20 :
    ∀ j : ℕ, 338766068 ≤ j → j < 338766069 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 338766068 := by omega
  subst hj
  refine ⟨2240913, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `338766069 ≤ j < 339266069`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `677532207`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_21 :
    ∀ j : ℕ, 338766069 ≤ j → j < 339266069 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 677532138) (x1 := 678532136) (lo := 677532207) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `339266069 ≤ j < 339540369`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`658239` bits from `678532207`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_22 :
    ∀ j : ℕ, 339266069 ≤ j → j < 339540369 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 678532138) (x1 := 679080736) (lo := 678532207) (W := 658239)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 339540369`: its covering offset `3166973` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3166973 = 682247711` by `minFac`. -/
private theorem cu_p3_23 :
    ∀ j : ℕ, 339540369 ≤ j → j < 339540370 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 339540369 := by omega
  subst hj
  refine ⟨3166973, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `339540370 ≤ j < 340040370`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116647` bits from `679080809`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_24 :
    ∀ j : ℕ, 339540370 ≤ j → j < 340040370 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 679080740) (x1 := 680080738) (lo := 679080809) (W := 1116647)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `340040370 ≤ j < 340322478`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`680863` bits from `680080809`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_25 :
    ∀ j : ℕ, 340040370 ≤ j → j < 340322478 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 680080740) (x1 := 680644954) (lo := 680080809) (W := 680863)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 340322478`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 680768489` by `minFac`. -/
private theorem cu_p3_26 :
    ∀ j : ℕ, 340322478 ≤ j → j < 340322479 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 340322478 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `340322479 ≤ j < 340355721`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`150593` bits from `680645027`), the offsets being the
first `130` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_27 :
    ∀ j : ℕ, 340322479 ≤ j → j < 340355721 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 680644958) (x1 := 680711440) (lo := 680645027) (W := 150593)
    (Ds := offsets.take 130) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 340355721`: its covering offset `133391` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 133391 = 680844833` by `minFac`. -/
private theorem cu_p3_28 :
    ∀ j : ℕ, 340355721 ≤ j → j < 340355722 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 340355721 := by omega
  subst hj
  refine ⟨133391, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `340355722 ≤ j < 340367634`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`139155` bits from `680711513`), the offsets being the
first `176` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_29 :
    ∀ j : ℕ, 340355722 ≤ j → j < 340367634 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 680711444) (x1 := 680735266) (lo := 680711513) (W := 139155)
    (Ds := offsets.take 176) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 340367634`: its covering offset `123923` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123923 = 680859191` by `minFac`. -/
private theorem cu_p3_30 :
    ∀ j : ℕ, 340367634 ≤ j → j < 340367635 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 340367634 := by omega
  subst hj
  refine ⟨123923, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `340367635 ≤ j < 340867635`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1102227` bits from `680735339`), the offsets being the
first `160` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_31 :
    ∀ j : ℕ, 340367635 ≤ j → j < 340867635 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 680735270) (x1 := 681735268) (lo := 680735339) (W := 1102227)
    (Ds := offsets.take 160) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `340867635 ≤ j < 341367635`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1102227` bits from `681735339`), the offsets being the
first `160` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_32 :
    ∀ j : ℕ, 340867635 ≤ j → j < 341367635 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 681735270) (x1 := 682735268) (lo := 681735339) (W := 1102227)
    (Ds := offsets.take 160) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `341367635 ≤ j < 341484933`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`329709` bits from `682735339`), the offsets being the
first `144` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_33 :
    ∀ j : ℕ, 341367635 ≤ j → j < 341484933 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 682735270) (x1 := 682969864) (lo := 682735339) (W := 329709)
    (Ds := offsets.take 144) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 341484933`: its covering offset `3697757` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3697757 = 686667623` by `minFac`. -/
private theorem cu_p3_34 :
    ∀ j : ℕ, 341484933 ≤ j → j < 341484934 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 341484933 := by omega
  subst hj
  refine ⟨3697757, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `341484934 ≤ j < 341691998`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`523767` bits from `682969937`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_35 :
    ∀ j : ℕ, 341484934 ≤ j → j < 341691998 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 682969868) (x1 := 683383994) (lo := 682969937) (W := 523767)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 341691998`: its covering offset `123351` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123351 = 683507347` by `minFac`. -/
private theorem cu_p3_36 :
    ∀ j : ℕ, 341691998 ≤ j → j < 341691999 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 341691998 := by omega
  subst hj
  refine ⟨123351, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `341691999 ≤ j < 341732619`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`178241` bits from `683384067`), the offsets being the
first `146` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_37 :
    ∀ j : ℕ, 341691999 ≤ j → j < 341732619 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 683383998) (x1 := 683465236) (lo := 683384067) (W := 178241)
    (Ds := offsets.take 146) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 341732619`: its covering offset `122411` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 122411 = 683587649` by `minFac`. -/
private theorem cu_p3_38 :
    ∀ j : ℕ, 341732619 ≤ j → j < 341732620 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 341732619 := by omega
  subst hj
  refine ⟨122411, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `341732620 ≤ j < 342232620`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1112909` bits from `683465309`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_39 :
    ∀ j : ℕ, 341732620 ≤ j → j < 342232620 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 683465240) (x1 := 684465238) (lo := 683465309) (W := 1112909)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `342232620 ≤ j < 342732620`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `684465309`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_40 :
    ∀ j : ℕ, 342232620 ≤ j → j < 342732620 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 684465240) (x1 := 685465238) (lo := 684465309) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `342732620 ≤ j < 343232620`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `685465309`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_41 :
    ∀ j : ℕ, 342732620 ≤ j → j < 343232620 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 685465240) (x1 := 686465238) (lo := 685465309) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `343232620 ≤ j < 343328544`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`286961` bits from `686465309`), the offsets being the
first `144` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_42 :
    ∀ j : ℕ, 343232620 ≤ j → j < 343328544 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 686465240) (x1 := 686657086) (lo := 686465309) (W := 286961)
    (Ds := offsets.take 144) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 343328544`: its covering offset `133391` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 133391 = 686790479` by `minFac`. -/
private theorem cu_p3_43 :
    ∀ j : ℕ, 343328544 ≤ j → j < 343328545 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 343328544 := by omega
  subst hj
  refine ⟨133391, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `343328545 ≤ j < 343665539`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`790275` bits from `686657159`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_44 :
    ∀ j : ℕ, 343328545 ≤ j → j < 343665539 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 686657090) (x1 := 687331076) (lo := 686657159) (W := 790275)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 343665539`: its covering offset `132219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 132219 = 687463297` by `minFac`. -/
private theorem cu_p3_45 :
    ∀ j : ℕ, 343665539 ≤ j → j < 343665540 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 343665539 := by omega
  subst hj
  refine ⟨132219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `343665540 ≤ j < 344000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`771147` bits from `687331149`), the offsets being the
first `160` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p3_46 :
    ∀ j : ℕ, 343665540 ≤ j → j < 344000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 687331080) (x1 := 687999998) (lo := 687331149) (W := 771147)
    (Ds := offsets.take 160) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- LEAF: Step 3 of 6 of the index cut, the indices 333500000 up to 344000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part3 :
    ∀ j : ℕ, 333500000 ≤ j → j < 344000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  by_cases h0 : j < 333524694
  · exact cu_p3_0 j (by omega) h0
  by_cases h1 : j < 333524695
  · exact cu_p3_1 j (by omega) h1
  by_cases h2 : j < 334024695
  · exact cu_p3_2 j (by omega) h2
  by_cases h3 : j < 334192494
  · exact cu_p3_3 j (by omega) h3
  by_cases h4 : j < 334192495
  · exact cu_p3_4 j (by omega) h4
  by_cases h5 : j < 334692495
  · exact cu_p3_5 j (by omega) h5
  by_cases h6 : j < 335192495
  · exact cu_p3_6 j (by omega) h6
  by_cases h7 : j < 335692495
  · exact cu_p3_7 j (by omega) h7
  by_cases h8 : j < 336192495
  · exact cu_p3_8 j (by omega) h8
  by_cases h9 : j < 336557079
  · exact cu_p3_9 j (by omega) h9
  by_cases h10 : j < 336557080
  · exact cu_p3_10 j (by omega) h10
  by_cases h11 : j < 337057080
  · exact cu_p3_11 j (by omega) h11
  by_cases h12 : j < 337088049
  · exact cu_p3_12 j (by omega) h12
  by_cases h13 : j < 337088050
  · exact cu_p3_13 j (by omega) h13
  by_cases h14 : j < 337588050
  · exact cu_p3_14 j (by omega) h14
  by_cases h15 : j < 337605783
  · exact cu_p3_15 j (by omega) h15
  by_cases h16 : j < 337605784
  · exact cu_p3_16 j (by omega) h16
  by_cases h17 : j < 338105784
  · exact cu_p3_17 j (by omega) h17
  by_cases h18 : j < 338605784
  · exact cu_p3_18 j (by omega) h18
  by_cases h19 : j < 338766068
  · exact cu_p3_19 j (by omega) h19
  by_cases h20 : j < 338766069
  · exact cu_p3_20 j (by omega) h20
  by_cases h21 : j < 339266069
  · exact cu_p3_21 j (by omega) h21
  by_cases h22 : j < 339540369
  · exact cu_p3_22 j (by omega) h22
  by_cases h23 : j < 339540370
  · exact cu_p3_23 j (by omega) h23
  by_cases h24 : j < 340040370
  · exact cu_p3_24 j (by omega) h24
  by_cases h25 : j < 340322478
  · exact cu_p3_25 j (by omega) h25
  by_cases h26 : j < 340322479
  · exact cu_p3_26 j (by omega) h26
  by_cases h27 : j < 340355721
  · exact cu_p3_27 j (by omega) h27
  by_cases h28 : j < 340355722
  · exact cu_p3_28 j (by omega) h28
  by_cases h29 : j < 340367634
  · exact cu_p3_29 j (by omega) h29
  by_cases h30 : j < 340367635
  · exact cu_p3_30 j (by omega) h30
  by_cases h31 : j < 340867635
  · exact cu_p3_31 j (by omega) h31
  by_cases h32 : j < 341367635
  · exact cu_p3_32 j (by omega) h32
  by_cases h33 : j < 341484933
  · exact cu_p3_33 j (by omega) h33
  by_cases h34 : j < 341484934
  · exact cu_p3_34 j (by omega) h34
  by_cases h35 : j < 341691998
  · exact cu_p3_35 j (by omega) h35
  by_cases h36 : j < 341691999
  · exact cu_p3_36 j (by omega) h36
  by_cases h37 : j < 341732619
  · exact cu_p3_37 j (by omega) h37
  by_cases h38 : j < 341732620
  · exact cu_p3_38 j (by omega) h38
  by_cases h39 : j < 342232620
  · exact cu_p3_39 j (by omega) h39
  by_cases h40 : j < 342732620
  · exact cu_p3_40 j (by omega) h40
  by_cases h41 : j < 343232620
  · exact cu_p3_41 j (by omega) h41
  by_cases h42 : j < 343328544
  · exact cu_p3_42 j (by omega) h42
  by_cases h43 : j < 343328545
  · exact cu_p3_43 j (by omega) h43
  by_cases h44 : j < 343665539
  · exact cu_p3_44 j (by omega) h44
  by_cases h45 : j < 343665540
  · exact cu_p3_45 j (by omega) h45
  exact cu_p3_46 j (by omega) h1

/-- Certificate window: the indices `344000000 ≤ j < 344500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `688000069`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_0 :
    ∀ j : ℕ, 344000000 ≤ j → j < 344500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 688000000) (x1 := 688999998) (lo := 688000069) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `344500000 ≤ j < 345000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1100043` bits from `689000069`), the offsets being the
first `155` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_1 :
    ∀ j : ℕ, 344500000 ≤ j → j < 345000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 689000000) (x1 := 689999998) (lo := 689000069) (W := 1100043)
    (Ds := offsets.take 155) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `345000000 ≤ j < 345493047`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1083917` bits from `690000069`), the offsets being the
first `147` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_2 :
    ∀ j : ℕ, 345000000 ≤ j → j < 345493047 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 690000000) (x1 := 690986092) (lo := 690000069) (W := 1083917)
    (Ds := offsets.take 147) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 345493047`: its covering offset `125219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125219 = 691111313` by `minFac`. -/
private theorem cu_p4_3 :
    ∀ j : ℕ, 345493047 ≤ j → j < 345493048 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 345493047 := by omega
  subst hj
  refine ⟨125219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `345493048 ≤ j < 345512531`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`130767` bits from `690986165`), the offsets being the
first `141` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_4 :
    ∀ j : ℕ, 345493048 ≤ j → j < 345512531 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 690986096) (x1 := 691025060) (lo := 690986165) (W := 130767)
    (Ds := offsets.take 141) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 345512531`: its covering offset `126219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 126219 = 691151281` by `minFac`. -/
private theorem cu_p4_5 :
    ∀ j : ℕ, 345512531 ≤ j → j < 345512532 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 345512531 := by omega
  subst hj
  refine ⟨126219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `345512532 ≤ j < 346012532`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116953` bits from `691025133`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_6 :
    ∀ j : ℕ, 345512532 ≤ j → j < 346012532 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 691025064) (x1 := 692025062) (lo := 691025133) (W := 1116953)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `346012532 ≤ j < 346512532`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `692025133`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_7 :
    ∀ j : ℕ, 346012532 ≤ j → j < 346512532 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 692025064) (x1 := 693025062) (lo := 692025133) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `346512532 ≤ j < 346627713`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`331311` bits from `693025133`), the offsets being the
first `158` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_8 :
    ∀ j : ℕ, 346512532 ≤ j → j < 346627713 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 693025064) (x1 := 693255424) (lo := 693025133) (W := 331311)
    (Ds := offsets.take 158) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 346627713`: its covering offset `3361883` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3361883 = 696617309` by `minFac`. -/
private theorem cu_p4_9 :
    ∀ j : ℕ, 346627713 ≤ j → j < 346627714 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 346627713 := by omega
  subst hj
  refine ⟨3361883, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `346627714 ≤ j < 347127714`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `693255497`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_10 :
    ∀ j : ℕ, 346627714 ≤ j → j < 347127714 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 693255428) (x1 := 694255426) (lo := 693255497) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `347127714 ≤ j < 347627714`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1104771` bits from `694255497`), the offsets being the
first `162` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_11 :
    ∀ j : ℕ, 347127714 ≤ j → j < 347627714 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 694255428) (x1 := 695255426) (lo := 694255497) (W := 1104771)
    (Ds := offsets.take 162) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `347627714 ≤ j < 348127714`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1112909` bits from `695255497`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_12 :
    ∀ j : ℕ, 347627714 ≤ j → j < 348127714 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 695255428) (x1 := 696255426) (lo := 695255497) (W := 1112909)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `348127714 ≤ j < 348627714`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `696255497`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_13 :
    ∀ j : ℕ, 348127714 ≤ j → j < 348627714 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 696255428) (x1 := 697255426) (lo := 696255497) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `348627714 ≤ j < 349127714`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118037` bits from `697255497`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_14 :
    ∀ j : ℕ, 348627714 ≤ j → j < 349127714 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 697255428) (x1 := 698255426) (lo := 697255497) (W := 1118037)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `349127714 ≤ j < 349455987`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`756909` bits from `698255497`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_15 :
    ∀ j : ℕ, 349127714 ≤ j → j < 349455987 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 698255428) (x1 := 698911972) (lo := 698255497) (W := 756909)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 349455987`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 700246163` by `minFac`. -/
private theorem cu_p4_16 :
    ∀ j : ℕ, 349455987 ≤ j → j < 349455988 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 349455987 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `349455988 ≤ j < 349566627`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`336609` bits from `698912045`), the offsets being the
first `176` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_17 :
    ∀ j : ℕ, 349455988 ≤ j → j < 349566627 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 698911976) (x1 := 699133252) (lo := 698912045) (W := 336609)
    (Ds := offsets.take 176) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 349566627`: its covering offset `125219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125219 = 699258473` by `minFac`. -/
private theorem cu_p4_18 :
    ∀ j : ℕ, 349566627 ≤ j → j < 349566628 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 349566627 := by omega
  subst hj
  refine ⟨125219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `349566628 ≤ j < 350066628`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1100949` bits from `699133325`), the offsets being the
first `158` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_19 :
    ∀ j : ℕ, 349566628 ≤ j → j < 350066628 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 699133256) (x1 := 700133254) (lo := 699133325) (W := 1100949)
    (Ds := offsets.take 158) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `350066628 ≤ j < 350566628`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116969` bits from `700133325`), the offsets being the
first `180` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_20 :
    ∀ j : ℕ, 350066628 ≤ j → j < 350566628 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 700133256) (x1 := 701133254) (lo := 700133325) (W := 1116969)
    (Ds := offsets.take 180) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `350566628 ≤ j < 351066628`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116953` bits from `701133325`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_21 :
    ∀ j : ℕ, 350566628 ≤ j → j < 351066628 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 701133256) (x1 := 702133254) (lo := 701133325) (W := 1116953)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `351066628 ≤ j < 351566628`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116647` bits from `702133325`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_22 :
    ∀ j : ℕ, 351066628 ≤ j → j < 351566628 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 702133256) (x1 := 703133254) (lo := 702133325) (W := 1116647)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `351566628 ≤ j < 352066628`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `703133325`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_23 :
    ∀ j : ℕ, 351566628 ≤ j → j < 352066628 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 703133256) (x1 := 704133254) (lo := 703133325) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `352066628 ≤ j < 352146954`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`275899` bits from `704133325`), the offsets being the
first `175` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_24 :
    ∀ j : ℕ, 352066628 ≤ j → j < 352146954 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 704133256) (x1 := 704293906) (lo := 704133325) (W := 275899)
    (Ds := offsets.take 175) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 352146954`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 705628097` by `minFac`. -/
private theorem cu_p4_25 :
    ∀ j : ℕ, 352146954 ≤ j → j < 352146955 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 352146954 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `352146955 ≤ j < 352646955`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `704293979`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_26 :
    ∀ j : ℕ, 352146955 ≤ j → j < 352646955 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 704293910) (x1 := 705293908) (lo := 704293979) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `352646955 ≤ j < 353146955`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `705293979`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_27 :
    ∀ j : ℕ, 352646955 ≤ j → j < 353146955 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 705293910) (x1 := 706293908) (lo := 705293979) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `353146955 ≤ j < 353394141`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`595851` bits from `706293979`), the offsets being the
first `159` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_28 :
    ∀ j : ℕ, 353146955 ≤ j → j < 353394141 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 706293910) (x1 := 706788280) (lo := 706293979) (W := 595851)
    (Ds := offsets.take 159) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 353394141`: its covering offset `131189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131189 = 706919471` by `minFac`. -/
private theorem cu_p4_29 :
    ∀ j : ℕ, 353394141 ≤ j → j < 353394142 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 353394141 := by omega
  subst hj
  refine ⟨131189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `353394142 ≤ j < 353694888`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`715205` bits from `706788353`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_30 :
    ∀ j : ℕ, 353394142 ≤ j → j < 353694888 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 706788284) (x1 := 707389774) (lo := 706788353) (W := 715205)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 353694888`: its covering offset `123923` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123923 = 707513699` by `minFac`. -/
private theorem cu_p4_31 :
    ∀ j : ℕ, 353694888 ≤ j → j < 353694889 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 353694888 := by omega
  subst hj
  refine ⟨123923, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `353694889 ≤ j < 353812529`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`351567` bits from `707389847`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_32 :
    ∀ j : ℕ, 353694889 ≤ j → j < 353812529 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 707389778) (x1 := 707625056) (lo := 707389847) (W := 351567)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 353812529`: its covering offset `126429` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 126429 = 707751487` by `minFac`. -/
private theorem cu_p4_33 :
    ∀ j : ℕ, 353812529 ≤ j → j < 353812530 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 353812529 := by omega
  subst hj
  refine ⟨126429, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `353812530 ≤ j < 354312530`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116647` bits from `707625129`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_34 :
    ∀ j : ℕ, 353812530 ≤ j → j < 354312530 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 707625060) (x1 := 708625058) (lo := 707625129) (W := 1116647)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `354312530 ≤ j < 354500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`486011` bits from `708625129`), the offsets being the
first `170` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p4_35 :
    ∀ j : ℕ, 354312530 ≤ j → j < 354500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 708625060) (x1 := 708999998) (lo := 708625129) (W := 486011)
    (Ds := offsets.take 170) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- LEAF: Step 4 of 6 of the index cut, the indices 344000000 up to 354500000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part4 :
    ∀ j : ℕ, 344000000 ≤ j → j < 354500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  by_cases h0 : j < 344500000
  · exact cu_p4_0 j (by omega) h0
  by_cases h1 : j < 345000000
  · exact cu_p4_1 j (by omega) h1
  by_cases h2 : j < 345493047
  · exact cu_p4_2 j (by omega) h2
  by_cases h3 : j < 345493048
  · exact cu_p4_3 j (by omega) h3
  by_cases h4 : j < 345512531
  · exact cu_p4_4 j (by omega) h4
  by_cases h5 : j < 345512532
  · exact cu_p4_5 j (by omega) h5
  by_cases h6 : j < 346012532
  · exact cu_p4_6 j (by omega) h6
  by_cases h7 : j < 346512532
  · exact cu_p4_7 j (by omega) h7
  by_cases h8 : j < 346627713
  · exact cu_p4_8 j (by omega) h8
  by_cases h9 : j < 346627714
  · exact cu_p4_9 j (by omega) h9
  by_cases h10 : j < 347127714
  · exact cu_p4_10 j (by omega) h10
  by_cases h11 : j < 347627714
  · exact cu_p4_11 j (by omega) h11
  by_cases h12 : j < 348127714
  · exact cu_p4_12 j (by omega) h12
  by_cases h13 : j < 348627714
  · exact cu_p4_13 j (by omega) h13
  by_cases h14 : j < 349127714
  · exact cu_p4_14 j (by omega) h14
  by_cases h15 : j < 349455987
  · exact cu_p4_15 j (by omega) h15
  by_cases h16 : j < 349455988
  · exact cu_p4_16 j (by omega) h16
  by_cases h17 : j < 349566627
  · exact cu_p4_17 j (by omega) h17
  by_cases h18 : j < 349566628
  · exact cu_p4_18 j (by omega) h18
  by_cases h19 : j < 350066628
  · exact cu_p4_19 j (by omega) h19
  by_cases h20 : j < 350566628
  · exact cu_p4_20 j (by omega) h20
  by_cases h21 : j < 351066628
  · exact cu_p4_21 j (by omega) h21
  by_cases h22 : j < 351566628
  · exact cu_p4_22 j (by omega) h22
  by_cases h23 : j < 352066628
  · exact cu_p4_23 j (by omega) h23
  by_cases h24 : j < 352146954
  · exact cu_p4_24 j (by omega) h24
  by_cases h25 : j < 352146955
  · exact cu_p4_25 j (by omega) h25
  by_cases h26 : j < 352646955
  · exact cu_p4_26 j (by omega) h26
  by_cases h27 : j < 353146955
  · exact cu_p4_27 j (by omega) h27
  by_cases h28 : j < 353394141
  · exact cu_p4_28 j (by omega) h28
  by_cases h29 : j < 353394142
  · exact cu_p4_29 j (by omega) h29
  by_cases h30 : j < 353694888
  · exact cu_p4_30 j (by omega) h30
  by_cases h31 : j < 353694889
  · exact cu_p4_31 j (by omega) h31
  by_cases h32 : j < 353812529
  · exact cu_p4_32 j (by omega) h32
  by_cases h33 : j < 353812530
  · exact cu_p4_33 j (by omega) h33
  by_cases h34 : j < 354312530
  · exact cu_p4_34 j (by omega) h34
  exact cu_p4_35 j (by omega) h1

/-- Certificate window: the indices `354500000 ≤ j < 355000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109163` bits from `709000069`), the offsets being the
first `164` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_0 :
    ∀ j : ℕ, 354500000 ≤ j → j < 355000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 709000000) (x1 := 709999998) (lo := 709000069) (W := 1109163)
    (Ds := offsets.take 164) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `355000000 ≤ j < 355500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1101479` bits from `710000069`), the offsets being the
first `159` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_1 :
    ∀ j : ℕ, 355000000 ≤ j → j < 355500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 710000000) (x1 := 710999998) (lo := 710000069) (W := 1101479)
    (Ds := offsets.take 159) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `355500000 ≤ j < 356000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116953` bits from `711000069`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_2 :
    ∀ j : ℕ, 355500000 ≤ j → j < 356000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 711000000) (x1 := 711999998) (lo := 711000069) (W := 1116953)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `356000000 ≤ j < 356500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `712000069`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_3 :
    ∀ j : ℕ, 356000000 ≤ j → j < 356500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 712000000) (x1 := 712999998) (lo := 712000069) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `356500000 ≤ j < 357000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `713000069`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_4 :
    ∀ j : ℕ, 356500000 ≤ j → j < 357000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 713000000) (x1 := 713999998) (lo := 713000069) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `357000000 ≤ j < 357462207`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1038127` bits from `714000069`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_5 :
    ∀ j : ℕ, 357000000 ≤ j → j < 357462207 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 714000000) (x1 := 714924412) (lo := 714000069) (W := 1038127)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 357462207`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 715047947` by `minFac`. -/
private theorem cu_p5_6 :
    ∀ j : ℕ, 357462207 ≤ j → j < 357462208 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 357462207 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `357462208 ≤ j < 357962208`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `714924485`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_7 :
    ∀ j : ℕ, 357462208 ≤ j → j < 357962208 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 714924416) (x1 := 715924414) (lo := 714924485) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `357962208 ≤ j < 358317504`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`811541` bits from `715924485`), the offsets being the
first `158` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_8 :
    ∀ j : ℕ, 357962208 ≤ j → j < 358317504 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 715924416) (x1 := 716635006) (lo := 715924485) (W := 811541)
    (Ds := offsets.take 158) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 358317504`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 716758541` by `minFac`. -/
private theorem cu_p5_9 :
    ∀ j : ℕ, 358317504 ≤ j → j < 358317505 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 358317504 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `358317505 ≤ j < 358817505`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1101479` bits from `716635079`), the offsets being the
first `159` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_10 :
    ∀ j : ℕ, 358317505 ≤ j → j < 358817505 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 716635010) (x1 := 717635008) (lo := 716635079) (W := 1101479)
    (Ds := offsets.take 159) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `358817505 ≤ j < 359317505`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109639` bits from `717635079`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_11 :
    ∀ j : ℕ, 358817505 ≤ j → j < 359317505 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 717635010) (x1 := 718635008) (lo := 717635079) (W := 1109639)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `359317505 ≤ j < 359391954`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`248307` bits from `718635079`), the offsets being the
first `154` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_12 :
    ∀ j : ℕ, 359317505 ≤ j → j < 359391954 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 718635010) (x1 := 718783906) (lo := 718635079) (W := 248307)
    (Ds := offsets.take 154) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 359391954`: its covering offset `123923` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123923 = 718907831` by `minFac`. -/
private theorem cu_p5_13 :
    ∀ j : ℕ, 359391954 ≤ j → j < 359391955 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 359391954 := by omega
  subst hj
  refine ⟨123923, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `359391955 ≤ j < 359588094`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`492641` bits from `718783979`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_14 :
    ∀ j : ℕ, 359391955 ≤ j → j < 359588094 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 718783910) (x1 := 719176186) (lo := 718783979) (W := 492641)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 359588094`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 720510377` by `minFac`. -/
private theorem cu_p5_15 :
    ∀ j : ℕ, 359588094 ≤ j → j < 359588095 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 359588094 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `359588095 ≤ j < 360088095`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118037` bits from `719176259`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_16 :
    ∀ j : ℕ, 359588095 ≤ j → j < 360088095 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 719176190) (x1 := 720176188) (lo := 719176259) (W := 1118037)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `360088095 ≤ j < 360588095`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `720176259`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_17 :
    ∀ j : ℕ, 360088095 ≤ j → j < 360588095 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 720176190) (x1 := 721176188) (lo := 720176259) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `360588095 ≤ j < 360743409`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`415375` bits from `721176259`), the offsets being the
first `161` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_18 :
    ∀ j : ℕ, 360588095 ≤ j → j < 360743409 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 721176190) (x1 := 721486816) (lo := 721176259) (W := 415375)
    (Ds := offsets.take 161) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 360743409`: its covering offset `127301` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 127301 = 721614119` by `minFac`. -/
private theorem cu_p5_19 :
    ∀ j : ℕ, 360743409 ≤ j → j < 360743410 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 360743409 := by omega
  subst hj
  refine ⟨127301, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `360743410 ≤ j < 360824412`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`271643` bits from `721486889`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_20 :
    ∀ j : ℕ, 360743410 ≤ j → j < 360824412 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 721486820) (x1 := 721648822) (lo := 721486889) (W := 271643)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 360824412`: its covering offset `131189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131189 = 721780013` by `minFac`. -/
private theorem cu_p5_21 :
    ∀ j : ℕ, 360824412 ≤ j → j < 360824413 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 360824412 := by omega
  subst hj
  refine ⟨131189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `360824413 ≤ j < 360864942`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`180467` bits from `721648895`), the offsets being the
first `154` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_22 :
    ∀ j : ℕ, 360824413 ≤ j → j < 360864942 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 721648826) (x1 := 721729882) (lo := 721648895) (W := 180467)
    (Ds := offsets.take 154) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 360864942`: its covering offset `699059` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 699059 = 722428943` by `minFac`. -/
private theorem cu_p5_23 :
    ∀ j : ℕ, 360864942 ≤ j → j < 360864943 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 360864942 := by omega
  subst hj
  refine ⟨699059, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `360864943 ≤ j < 360990312`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`348561` bits from `721729955`), the offsets being the
first `147` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_24 :
    ∀ j : ℕ, 360864943 ≤ j → j < 360990312 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 721729886) (x1 := 721980622) (lo := 721729955) (W := 348561)
    (Ds := offsets.take 147) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 360990312`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 722104157` by `minFac`. -/
private theorem cu_p5_25 :
    ∀ j : ℕ, 360990312 ≤ j → j < 360990313 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 360990312 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `360990313 ≤ j < 361301931`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`732875` bits from `721980695`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_26 :
    ∀ j : ℕ, 360990313 ≤ j → j < 361301931 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 721980626) (x1 := 722603860) (lo := 721980695) (W := 732875)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 361301931`: its covering offset `125219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 125219 = 722729081` by `minFac`. -/
private theorem cu_p5_27 :
    ∀ j : ℕ, 361301931 ≤ j → j < 361301932 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 361301931 := by omega
  subst hj
  refine ⟨125219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `361301932 ≤ j < 361509321`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`512805` bits from `722603933`), the offsets being the
first `149` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_28 :
    ∀ j : ℕ, 361301932 ≤ j → j < 361509321 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 722603864) (x1 := 723018640) (lo := 722603933) (W := 512805)
    (Ds := offsets.take 149) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 361509321`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 724352831` by `minFac`. -/
private theorem cu_p5_29 :
    ∀ j : ℕ, 361509321 ≤ j → j < 361509322 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 361509321 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `361509322 ≤ j < 362001462`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1099427` bits from `723018713`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_30 :
    ∀ j : ℕ, 361509322 ≤ j → j < 362001462 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 723018644) (x1 := 724002922) (lo := 723018713) (W := 1099427)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 362001462`: its covering offset `123923` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123923 = 724126847` by `minFac`. -/
private theorem cu_p5_31 :
    ∀ j : ℕ, 362001462 ≤ j → j < 362001463 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 362001462 := by omega
  subst hj
  refine ⟨123923, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `362001463 ≤ j < 362044779`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`188111` bits from `724002995`), the offsets being the
first `159` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_32 :
    ∀ j : ℕ, 362001463 ≤ j → j < 362044779 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 724002926) (x1 := 724089556) (lo := 724002995) (W := 188111)
    (Ds := offsets.take 159) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 362044779`: its covering offset `3166973` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3166973 = 727256531` by `minFac`. -/
private theorem cu_p5_33 :
    ∀ j : ℕ, 362044779 ≤ j → j < 362044780 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 362044779 := by omega
  subst hj
  refine ⟨3166973, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `362044780 ≤ j < 362544780`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118037` bits from `724089629`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_34 :
    ∀ j : ℕ, 362044780 ≤ j → j < 362544780 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 724089560) (x1 := 725089558) (lo := 724089629) (W := 1118037)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `362544780 ≤ j < 362835407`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`697901` bits from `725089629`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_35 :
    ∀ j : ℕ, 362544780 ≤ j → j < 362835407 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 725089560) (x1 := 725670812) (lo := 725089629) (W := 697901)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 362835407`: its covering offset `126429` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 126429 = 725797243` by `minFac`. -/
private theorem cu_p5_36 :
    ∀ j : ℕ, 362835407 ≤ j → j < 362835408 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 362835407 := by omega
  subst hj
  refine ⟨126429, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `362835408 ≤ j < 363307872`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1061575` bits from `725670885`), the offsets being the
first `178` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_37 :
    ∀ j : ℕ, 362835408 ≤ j → j < 363307872 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 725670816) (x1 := 726615742) (lo := 725670885) (W := 1061575)
    (Ds := offsets.take 178) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 363307872`: its covering offset `699059` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 699059 = 727314803` by `minFac`. -/
private theorem cu_p5_38 :
    ∀ j : ℕ, 363307872 ≤ j → j < 363307873 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 363307872 := by omega
  subst hj
  refine ⟨699059, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `363307873 ≤ j < 363519972`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`533897` bits from `726615815`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_39 :
    ∀ j : ℕ, 363307873 ≤ j → j < 363519972 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 726615746) (x1 := 727039942) (lo := 726615815) (W := 533897)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 363519972`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 727163477` by `minFac`. -/
private theorem cu_p5_40 :
    ∀ j : ℕ, 363519972 ≤ j → j < 363519973 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 363519972 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `363519973 ≤ j < 363929721`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`933209` bits from `727040015`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_41 :
    ∀ j : ℕ, 363519973 ≤ j → j < 363929721 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 727039946) (x1 := 727859440) (lo := 727040015) (W := 933209)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 363929721`: its covering offset `3697757` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3697757 = 731557199` by `minFac`. -/
private theorem cu_p5_42 :
    ∀ j : ℕ, 363929721 ≤ j → j < 363929722 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 363929721 := by omega
  subst hj
  refine ⟨3697757, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `363929722 ≤ j < 364072113`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`381783` bits from `727859513`), the offsets being the
first `146` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_43 :
    ∀ j : ℕ, 363929722 ≤ j → j < 364072113 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 727859444) (x1 := 728144224) (lo := 727859513) (W := 381783)
    (Ds := offsets.take 146) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 364072113`: its covering offset `127301` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 127301 = 728271527` by `minFac`. -/
private theorem cu_p5_44 :
    ∀ j : ℕ, 364072113 ≤ j → j < 364072114 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 364072113 := by omega
  subst hj
  refine ⟨127301, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `364072114 ≤ j < 364304186`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`563553` bits from `728144297`), the offsets being the
first `154` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_45 :
    ∀ j : ℕ, 364072114 ≤ j → j < 364304186 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 728144228) (x1 := 728608370) (lo := 728144297) (W := 563553)
    (Ds := offsets.take 154) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 364304186`: its covering offset `131889` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131889 = 728740261` by `minFac`. -/
private theorem cu_p5_46 :
    ∀ j : ℕ, 364304186 ≤ j → j < 364304187 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 364304186 := by omega
  subst hj
  refine ⟨131889, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `364304187 ≤ j < 364804187`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1110357` bits from `728608443`), the offsets being the
first `169` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_47 :
    ∀ j : ℕ, 364304187 ≤ j → j < 364804187 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 728608374) (x1 := 729608372) (lo := 728608443) (W := 1110357)
    (Ds := offsets.take 169) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `364804187 ≤ j < 365000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`501265` bits from `729608443`), the offsets being the
first `167` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p5_48 :
    ∀ j : ℕ, 364804187 ≤ j → j < 365000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 729608374) (x1 := 729999998) (lo := 729608443) (W := 501265)
    (Ds := offsets.take 167) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- LEAF: Step 5 of 6 of the index cut, the indices 354500000 up to 365000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part5 :
    ∀ j : ℕ, 354500000 ≤ j → j < 365000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  by_cases h0 : j < 355000000
  · exact cu_p5_0 j (by omega) h0
  by_cases h1 : j < 355500000
  · exact cu_p5_1 j (by omega) h1
  by_cases h2 : j < 356000000
  · exact cu_p5_2 j (by omega) h2
  by_cases h3 : j < 356500000
  · exact cu_p5_3 j (by omega) h3
  by_cases h4 : j < 357000000
  · exact cu_p5_4 j (by omega) h4
  by_cases h5 : j < 357462207
  · exact cu_p5_5 j (by omega) h5
  by_cases h6 : j < 357462208
  · exact cu_p5_6 j (by omega) h6
  by_cases h7 : j < 357962208
  · exact cu_p5_7 j (by omega) h7
  by_cases h8 : j < 358317504
  · exact cu_p5_8 j (by omega) h8
  by_cases h9 : j < 358317505
  · exact cu_p5_9 j (by omega) h9
  by_cases h10 : j < 358817505
  · exact cu_p5_10 j (by omega) h10
  by_cases h11 : j < 359317505
  · exact cu_p5_11 j (by omega) h11
  by_cases h12 : j < 359391954
  · exact cu_p5_12 j (by omega) h12
  by_cases h13 : j < 359391955
  · exact cu_p5_13 j (by omega) h13
  by_cases h14 : j < 359588094
  · exact cu_p5_14 j (by omega) h14
  by_cases h15 : j < 359588095
  · exact cu_p5_15 j (by omega) h15
  by_cases h16 : j < 360088095
  · exact cu_p5_16 j (by omega) h16
  by_cases h17 : j < 360588095
  · exact cu_p5_17 j (by omega) h17
  by_cases h18 : j < 360743409
  · exact cu_p5_18 j (by omega) h18
  by_cases h19 : j < 360743410
  · exact cu_p5_19 j (by omega) h19
  by_cases h20 : j < 360824412
  · exact cu_p5_20 j (by omega) h20
  by_cases h21 : j < 360824413
  · exact cu_p5_21 j (by omega) h21
  by_cases h22 : j < 360864942
  · exact cu_p5_22 j (by omega) h22
  by_cases h23 : j < 360864943
  · exact cu_p5_23 j (by omega) h23
  by_cases h24 : j < 360990312
  · exact cu_p5_24 j (by omega) h24
  by_cases h25 : j < 360990313
  · exact cu_p5_25 j (by omega) h25
  by_cases h26 : j < 361301931
  · exact cu_p5_26 j (by omega) h26
  by_cases h27 : j < 361301932
  · exact cu_p5_27 j (by omega) h27
  by_cases h28 : j < 361509321
  · exact cu_p5_28 j (by omega) h28
  by_cases h29 : j < 361509322
  · exact cu_p5_29 j (by omega) h29
  by_cases h30 : j < 362001462
  · exact cu_p5_30 j (by omega) h30
  by_cases h31 : j < 362001463
  · exact cu_p5_31 j (by omega) h31
  by_cases h32 : j < 362044779
  · exact cu_p5_32 j (by omega) h32
  by_cases h33 : j < 362044780
  · exact cu_p5_33 j (by omega) h33
  by_cases h34 : j < 362544780
  · exact cu_p5_34 j (by omega) h34
  by_cases h35 : j < 362835407
  · exact cu_p5_35 j (by omega) h35
  by_cases h36 : j < 362835408
  · exact cu_p5_36 j (by omega) h36
  by_cases h37 : j < 363307872
  · exact cu_p5_37 j (by omega) h37
  by_cases h38 : j < 363307873
  · exact cu_p5_38 j (by omega) h38
  by_cases h39 : j < 363519972
  · exact cu_p5_39 j (by omega) h39
  by_cases h40 : j < 363519973
  · exact cu_p5_40 j (by omega) h40
  by_cases h41 : j < 363929721
  · exact cu_p5_41 j (by omega) h41
  by_cases h42 : j < 363929722
  · exact cu_p5_42 j (by omega) h42
  by_cases h43 : j < 364072113
  · exact cu_p5_43 j (by omega) h43
  by_cases h44 : j < 364072114
  · exact cu_p5_44 j (by omega) h44
  by_cases h45 : j < 364304186
  · exact cu_p5_45 j (by omega) h45
  by_cases h46 : j < 364304187
  · exact cu_p5_46 j (by omega) h46
  by_cases h47 : j < 364804187
  · exact cu_p5_47 j (by omega) h47
  exact cu_p5_48 j (by omega) h1

/-- Certificate window: the indices `365000000 ≤ j < 365500000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `730000069`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_0 :
    ∀ j : ℕ, 365000000 ≤ j → j < 365500000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 730000000) (x1 := 730999998) (lo := 730000069) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `365500000 ≤ j < 366000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `731000069`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_1 :
    ∀ j : ℕ, 365500000 ≤ j → j < 366000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 731000000) (x1 := 731999998) (lo := 731000069) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `366000000 ≤ j < 366097631`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`287063` bits from `732000069`), the offsets being the
first `141` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_2 :
    ∀ j : ℕ, 366000000 ≤ j → j < 366097631 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 732000000) (x1 := 732195260) (lo := 732000069) (W := 287063)
    (Ds := offsets.take 141) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 366097631`: its covering offset `131889` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131889 = 732327151` by `minFac`. -/
private theorem cu_p6_3 :
    ∀ j : ℕ, 366097631 ≤ j → j < 366097632 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 366097631 := by omega
  subst hj
  refine ⟨131889, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `366097632 ≤ j < 366597632`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1109699` bits from `732195333`), the offsets being the
first `168` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_4 :
    ∀ j : ℕ, 366097632 ≤ j → j < 366597632 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 732195264) (x1 := 733195262) (lo := 732195333) (W := 1109699)
    (Ds := offsets.take 168) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `366597632 ≤ j < 366899388`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`718659` bits from `733195333`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_5 :
    ∀ j : ℕ, 366597632 ≤ j → j < 366899388 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 733195264) (x1 := 733798774) (lo := 733195333) (W := 718659)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 366899388`: its covering offset `131207` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131207 = 733929983` by `minFac`. -/
private theorem cu_p6_6 :
    ∀ j : ℕ, 366899388 ≤ j → j < 366899389 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 366899388 := by omega
  subst hj
  refine ⟨131207, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `366899389 ≤ j < 367399389`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118349` bits from `733798847`), the offsets being the
first `182` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_7 :
    ∀ j : ℕ, 366899389 ≤ j → j < 367399389 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 733798778) (x1 := 734798776) (lo := 733798847) (W := 1118349)
    (Ds := offsets.take 182) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `367399389 ≤ j < 367899389`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `734798847`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_8 :
    ∀ j : ℕ, 367399389 ≤ j → j < 367899389 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 734798778) (x1 := 735798776) (lo := 734798847) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `367899389 ≤ j < 368052738`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`422985` bits from `735798847`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_9 :
    ∀ j : ℕ, 367899389 ≤ j → j < 368052738 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 735798778) (x1 := 736105474) (lo := 735798847) (W := 422985)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 368052738`: its covering offset `1668413` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1668413 = 737773889` by `minFac`. -/
private theorem cu_p6_10 :
    ∀ j : ℕ, 368052738 ≤ j → j < 368052739 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 368052738 := by omega
  subst hj
  refine ⟨1668413, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `368052739 ≤ j < 368552739`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1112909` bits from `736105547`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_11 :
    ∀ j : ℕ, 368052739 ≤ j → j < 368552739 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 736105478) (x1 := 737105476) (lo := 736105547) (W := 1112909)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `368552739 ≤ j < 368706636`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`424747` bits from `737105547`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_12 :
    ∀ j : ℕ, 368552739 ≤ j → j < 368706636 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 737105478) (x1 := 737413270) (lo := 737105547) (W := 424747)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 368706636`: its covering offset `3697757` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3697757 = 741111029` by `minFac`. -/
private theorem cu_p6_13 :
    ∀ j : ℕ, 368706636 ≤ j → j < 368706637 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 368706636 := by omega
  subst hj
  refine ⟨3697757, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `368706637 ≤ j < 368896868`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`480825` bits from `737413343`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_14 :
    ∀ j : ℕ, 368706637 ≤ j → j < 368896868 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 737413274) (x1 := 737793734) (lo := 737413343) (W := 480825)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 368896868`: its covering offset `505017` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 505017 = 738298753` by `minFac`. -/
private theorem cu_p6_15 :
    ∀ j : ℕ, 368896868 ≤ j → j < 368896869 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 368896868 := by omega
  subst hj
  refine ⟨505017, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `368896869 ≤ j < 369396869`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1118037` bits from `737793807`), the offsets being the
first `181` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_16 :
    ∀ j : ℕ, 368896869 ≤ j → j < 369396869 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 737793738) (x1 := 738793736) (lo := 737793807) (W := 1118037)
    (Ds := offsets.take 181) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `369396869 ≤ j < 369896869`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1116287` bits from `738793807`), the offsets being the
first `177` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_17 :
    ∀ j : ℕ, 369396869 ≤ j → j < 369896869 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 738793738) (x1 := 739793736) (lo := 738793807) (W := 1116287)
    (Ds := offsets.take 177) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `369896869 ≤ j < 370221216`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`759765` bits from `739793807`), the offsets being the
first `170` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_18 :
    ∀ j : ℕ, 369896869 ≤ j → j < 370221216 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 739793738) (x1 := 740442430) (lo := 739793807) (W := 759765)
    (Ds := offsets.take 170) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 370221216`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 741776621` by `minFac`. -/
private theorem cu_p6_19 :
    ∀ j : ℕ, 370221216 ≤ j → j < 370221217 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 370221216 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `370221217 ≤ j < 370717827`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1110173` bits from `740442503`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_20 :
    ∀ j : ℕ, 370221217 ≤ j → j < 370717827 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 740442434) (x1 := 741435652) (lo := 740442503) (W := 1110173)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 370717827`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 741559187` by `minFac`. -/
private theorem cu_p6_21 :
    ∀ j : ℕ, 370717827 ≤ j → j < 370717828 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 370717827 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `370717828 ≤ j < 370980726`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`642749` bits from `741435725`), the offsets being the
first `179` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_22 :
    ∀ j : ℕ, 370717828 ≤ j → j < 370980726 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 741435656) (x1 := 741961450) (lo := 741435725) (W := 642749)
    (Ds := offsets.take 179) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 370980726`: its covering offset `131189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 131189 = 742092641` by `minFac`. -/
private theorem cu_p6_23 :
    ∀ j : ℕ, 370980726 ≤ j → j < 370980727 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 370980726 := by omega
  subst hj
  refine ⟨131189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `370980727 ≤ j < 371430063`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1011581` bits from `741961523`), the offsets being the
first `172` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_24 :
    ∀ j : ℕ, 370980727 ≤ j → j < 371430063 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 741961454) (x1 := 742860124) (lo := 741961523) (W := 1011581)
    (Ds := offsets.take 172) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 371430063`: its covering offset `123923` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123923 = 742984049` by `minFac`. -/
private theorem cu_p6_25 :
    ∀ j : ℕ, 371430063 ≤ j → j < 371430064 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 371430063 := by omega
  subst hj
  refine ⟨123923, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `371430064 ≤ j < 371732439`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`719897` bits from `742860197`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_26 :
    ∀ j : ℕ, 371430064 ≤ j → j < 371732439 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 742860128) (x1 := 743464876) (lo := 742860197) (W := 719897)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 371732439`: its covering offset `123533` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123533 = 743588411` by `minFac`. -/
private theorem cu_p6_27 :
    ∀ j : ℕ, 371732439 ≤ j → j < 371732440 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 371732439 := by omega
  subst hj
  refine ⟨123533, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `371732440 ≤ j < 372232440`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1115147` bits from `743464949`), the offsets being the
first `174` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_28 :
    ∀ j : ℕ, 371732440 ≤ j → j < 372232440 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 743464880) (x1 := 744464878) (lo := 743464949) (W := 1115147)
    (Ds := offsets.take 174) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `372232440 ≤ j < 372732440`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1113713` bits from `744464949`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_29 :
    ∀ j : ℕ, 372232440 ≤ j → j < 372732440 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 744464880) (x1 := 745464878) (lo := 744464949) (W := 1113713)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `372732440 ≤ j < 372806904`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`233037` bits from `745464949`), the offsets being the
first `130` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_30 :
    ∀ j : ℕ, 372732440 ≤ j → j < 372806904 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 745464880) (x1 := 745613806) (lo := 745464949) (W := 233037)
    (Ds := offsets.take 130) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 372806904`: its covering offset `127301` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 127301 = 745741109` by `minFac`. -/
private theorem cu_p6_31 :
    ∀ j : ℕ, 372806904 ≤ j → j < 372806905 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 372806904 := by omega
  subst hj
  refine ⟨127301, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `372806905 ≤ j < 373306905`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1111143` bits from `745613879`), the offsets being the
first `171` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_32 :
    ∀ j : ℕ, 372806905 ≤ j → j < 373306905 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 745613810) (x1 := 746613808) (lo := 745613879) (W := 1111143)
    (Ds := offsets.take 171) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `373306905 ≤ j < 373647957`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`782467` bits from `746613879`), the offsets being the
first `157` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_33 :
    ∀ j : ℕ, 373306905 ≤ j → j < 373647957 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 746613810) (x1 := 747295912) (lo := 746613879) (W := 782467)
    (Ds := offsets.take 157) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 373647957`: its covering offset `1668413` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1668413 = 748964327` by `minFac`. -/
private theorem cu_p6_34 :
    ∀ j : ℕ, 373647957 ≤ j → j < 373647958 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 373647957 := by omega
  subst hj
  refine ⟨1668413, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `373647958 ≤ j < 373682922`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`153641` bits from `747295985`), the offsets being the
first `129` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_35 :
    ∀ j : ℕ, 373647958 ≤ j → j < 373682922 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 747295916) (x1 := 747365842) (lo := 747295985) (W := 153641)
    (Ds := offsets.take 129) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 373682922`: its covering offset `123923` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 123923 = 747489767` by `minFac`. -/
private theorem cu_p6_36 :
    ∀ j : ℕ, 373682922 ≤ j → j < 373682923 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 373682922 := by omega
  subst hj
  refine ⟨123923, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `373682923 ≤ j < 373765382`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`278631` bits from `747365915`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_37 :
    ∀ j : ℕ, 373682923 ≤ j → j < 373765382 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 747365846) (x1 := 747530762) (lo := 747365915) (W := 278631)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 373765382`: its covering offset `126219` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 126219 = 747656983` by `minFac`. -/
private theorem cu_p6_38 :
    ∀ j : ℕ, 373765382 ≤ j → j < 373765383 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 373765382 := by omega
  subst hj
  refine ⟨126219, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `373765383 ≤ j < 374265383`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1101479` bits from `747530835`), the offsets being the
first `159` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_39 :
    ∀ j : ℕ, 373765383 ≤ j → j < 374265383 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 747530766) (x1 := 748530764) (lo := 747530835) (W := 1101479)
    (Ds := offsets.take 159) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- Certificate window: the indices `374265383 ≤ j < 374732334`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`1047615` bits from `748530835`), the offsets being the
first `173` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_40 :
    ∀ j : ℕ, 374265383 ≤ j → j < 374732334 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 748530766) (x1 := 749464666) (lo := 748530835) (W := 1047615)
    (Ds := offsets.take 173) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 374732334`: its covering offset `3361883` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 3361883 = 752826551` by `minFac`. -/
private theorem cu_p6_41 :
    ∀ j : ℕ, 374732334 ≤ j → j < 374732335 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 374732334 := by omega
  subst hj
  refine ⟨3361883, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `374732335 ≤ j < 374917002`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`479691` bits from `749464739`), the offsets being the
first `169` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_42 :
    ∀ j : ℕ, 374732335 ≤ j → j < 374917002 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 749464670) (x1 := 749834002) (lo := 749464739) (W := 479691)
    (Ds := offsets.take 169) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩
/-- The single index `j = 374917002`: its covering offset `1334189` is outside the `take K` prefix, so it
is certified on its own, `2 * j + 1334189 = 751168193` by `minFac`. -/
private theorem cu_p6_43 :
    ∀ j : ℕ, 374917002 ≤ j → j < 374917003 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  have hj : j = 374917002 := by omega
  subst hj
  refine ⟨1334189, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
/-- Certificate window: the indices `374917003 ≤ j < 375000000`, checked as one equality of
naturals over the shifted prime bitmap `wpm2` (`255225` bits from `749834075`), the offsets being the
first `137` of the fixed list. No large prime is asserted; the kernel evaluates the bitmap. -/
private theorem cu_p6_44 :
    ∀ j : ℕ, 374917003 ≤ j → j < 375000000 → ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  obtain ⟨a, ha, hp⟩ := LeanLab.DtRS1998.Certificate294.offset_window
    (x0 := 749834006) (x1 := 749999998) (lo := 749834075) (W := 255225)
    (Ds := offsets.take 137) (by decide) (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- LEAF: Step 6 of 6 of the index cut, the last indices 365000000 up to 375000000; this
one is shorter than ten and a half million indices because the target range stops at
375000000. Some offset of the fixed list makes 2 * j + a prime. Strictly weaker than the
target: one subrange only, and no size bound on the offset. -/
theorem cover_upper_part6 :
    ∀ j : ℕ, 365000000 ≤ j → j < 375000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j h0 h1
  by_cases h0 : j < 365500000
  · exact cu_p6_0 j (by omega) h0
  by_cases h1 : j < 366000000
  · exact cu_p6_1 j (by omega) h1
  by_cases h2 : j < 366097631
  · exact cu_p6_2 j (by omega) h2
  by_cases h3 : j < 366097632
  · exact cu_p6_3 j (by omega) h3
  by_cases h4 : j < 366597632
  · exact cu_p6_4 j (by omega) h4
  by_cases h5 : j < 366899388
  · exact cu_p6_5 j (by omega) h5
  by_cases h6 : j < 366899389
  · exact cu_p6_6 j (by omega) h6
  by_cases h7 : j < 367399389
  · exact cu_p6_7 j (by omega) h7
  by_cases h8 : j < 367899389
  · exact cu_p6_8 j (by omega) h8
  by_cases h9 : j < 368052738
  · exact cu_p6_9 j (by omega) h9
  by_cases h10 : j < 368052739
  · exact cu_p6_10 j (by omega) h10
  by_cases h11 : j < 368552739
  · exact cu_p6_11 j (by omega) h11
  by_cases h12 : j < 368706636
  · exact cu_p6_12 j (by omega) h12
  by_cases h13 : j < 368706637
  · exact cu_p6_13 j (by omega) h13
  by_cases h14 : j < 368896868
  · exact cu_p6_14 j (by omega) h14
  by_cases h15 : j < 368896869
  · exact cu_p6_15 j (by omega) h15
  by_cases h16 : j < 369396869
  · exact cu_p6_16 j (by omega) h16
  by_cases h17 : j < 369896869
  · exact cu_p6_17 j (by omega) h17
  by_cases h18 : j < 370221216
  · exact cu_p6_18 j (by omega) h18
  by_cases h19 : j < 370221217
  · exact cu_p6_19 j (by omega) h19
  by_cases h20 : j < 370717827
  · exact cu_p6_20 j (by omega) h20
  by_cases h21 : j < 370717828
  · exact cu_p6_21 j (by omega) h21
  by_cases h22 : j < 370980726
  · exact cu_p6_22 j (by omega) h22
  by_cases h23 : j < 370980727
  · exact cu_p6_23 j (by omega) h23
  by_cases h24 : j < 371430063
  · exact cu_p6_24 j (by omega) h24
  by_cases h25 : j < 371430064
  · exact cu_p6_25 j (by omega) h25
  by_cases h26 : j < 371732439
  · exact cu_p6_26 j (by omega) h26
  by_cases h27 : j < 371732440
  · exact cu_p6_27 j (by omega) h27
  by_cases h28 : j < 372232440
  · exact cu_p6_28 j (by omega) h28
  by_cases h29 : j < 372732440
  · exact cu_p6_29 j (by omega) h29
  by_cases h30 : j < 372806904
  · exact cu_p6_30 j (by omega) h30
  by_cases h31 : j < 372806905
  · exact cu_p6_31 j (by omega) h31
  by_cases h32 : j < 373306905
  · exact cu_p6_32 j (by omega) h32
  by_cases h33 : j < 373647957
  · exact cu_p6_33 j (by omega) h33
  by_cases h34 : j < 373647958
  · exact cu_p6_34 j (by omega) h34
  by_cases h35 : j < 373682922
  · exact cu_p6_35 j (by omega) h35
  by_cases h36 : j < 373682923
  · exact cu_p6_36 j (by omega) h36
  by_cases h37 : j < 373765382
  · exact cu_p6_37 j (by omega) h37
  by_cases h38 : j < 373765383
  · exact cu_p6_38 j (by omega) h38
  by_cases h39 : j < 374265383
  · exact cu_p6_39 j (by omega) h39
  by_cases h40 : j < 374732334
  · exact cu_p6_40 j (by omega) h40
  by_cases h41 : j < 374732335
  · exact cu_p6_41 j (by omega) h41
  by_cases h42 : j < 374917002
  · exact cu_p6_42 j (by omega) h42
  by_cases h43 : j < 374917003
  · exact cu_p6_43 j (by omega) h43
  exact cu_p6_44 j (by omega) h1

/-- The integer bookkeeping of the cut: every index of the target range lies in one of
the six subranges above. Arithmetic only, no prime is mentioned. -/
private theorem cover_upper_partition (j : ℕ)
    (hlo : 312500000 ≤ j) (hj : j < 375000000) :
    j < 323000000 ∨ (323000000 ≤ j ∧ j < 333500000) ∨
      (333500000 ≤ j ∧ j < 344000000) ∨ (344000000 ≤ j ∧ j < 354500000) ∨
      (354500000 ≤ j ∧ j < 365000000) ∨ (365000000 ≤ j ∧ j < 375000000) := by
  omega

/-- The offset size estimate of the target, discharged by the whole-list bound of the
certificate data rather than by any new work in this file. -/
private theorem cover_upper_mem_le (a : ℕ) (ha : a ∈ offsets) : a ≤ 10 ^ 300 :=
  offsets_le a ha

/-- The target statement of `cover_upper`, cut into the six index subranges above and
regrouped: each index picks the leaf of its subrange for the prime companion, and the
size of that offset comes from the whole-list estimate. No sorry of its own. -/
theorem cover_upper_split :
    ∀ j : ℕ, 312500000 ≤ j → j < 375000000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hlo hj
  rcases cover_upper_partition j hlo hj with h1 | ⟨h2, h3⟩ | ⟨h4, h5⟩ | ⟨h6, h7⟩ |
    ⟨h8, h9⟩ | ⟨h10, h11⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part1 j hlo h1
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part2 j h2 h3
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part3 j h4 h5
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part4 j h6 h7
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part5 j h8 h9
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩
  · obtain ⟨a, ha, hp⟩ := cover_upper_part6 j h10 h11
    exact ⟨a, ha, cover_upper_mem_le a ha, hp⟩

#print axioms cover_upper_split

end LeanLab.DtRS1998.Decomp455d
