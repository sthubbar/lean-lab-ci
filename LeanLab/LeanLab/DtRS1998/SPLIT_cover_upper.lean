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

All six leaves are proved here from the shifted window sieve `Certificate294.offset_window`, which
is in this file's import closure, one kernel-checked window per 500000 indices. A sieve of the
real integers finds no index of `[312500000, 375000000)` without a prime complement, so no leaf is
vacuous. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455d

namespace LeanLab.DtRS1998.Decomp455d

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-! ### Kernel-checked windows for the six leaves

Each leaf below asks, for one subrange of `[312500000, 375000000)`, that every index have a
prime complement among the fixed 213 offsets.  The proofs below run the shifted window
sieve `Certificate294.offset_window` on windows of 500000 indices, using the first 200
offsets, whose largest member is 133391; the 31 indices that no one of those 200 offsets
covers get their own complement from the tail of the list, checked by the one-bit window
`prime_of_bit`.  Nothing here is asserted without a kernel check. -/

/-- A number whose own bit is set in the one-bit window sieve at `n` is prime: this is
`prime_of_wpm2` read at a window of length one.  It needs no window sieve of its own, so a
single exceptional index costs one tiny kernel check rather than a whole window. -/
private theorem prime_of_bit (n : ℕ) (h2 : 2 ≤ n)
    (hn : n + 1 ≤ LeanLab.Verifications.Top50.Bits.B2)
    (h : (LeanLab.Verifications.Top50.Bits.wpm2 n 1).testBit 0 = true) : n.Prime :=
  by simpa using LeanLab.Verifications.Top50.Bits.prime_of_wpm2 (lo := n) (W := 1) (i := 0) h2 hn h

/-- The single index `317858307` has no complement among the first 200 offsets; `1668413`, the
`208`-th offset of the list, makes `2 * 317858307 + 1668413` prime. -/
private theorem resid_317858307 : ∃ a ∈ offsets, (2 * 317858307 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `318147687` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 318147687 + 1334189` prime. -/
private theorem resid_318147687 : ∃ a ∈ offsets, (2 * 318147687 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `322046337` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 322046337 + 1334189` prime. -/
private theorem resid_322046337 : ∃ a ∈ offsets, (2 * 322046337 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `322131927` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 322131927 + 1334189` prime. -/
private theorem resid_322131927 : ∃ a ∈ offsets, (2 * 322131927 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `323601443` has no complement among the first 200 offsets; `2240913`, the
`209`-th offset of the list, makes `2 * 323601443 + 2240913` prime. -/
private theorem resid_323601443 : ∃ a ∈ offsets, (2 * 323601443 + a).Prime := by
  refine ⟨2240913, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `324286212` has no complement among the first 200 offsets; `3166973`, the
`210`-th offset of the list, makes `2 * 324286212 + 3166973` prime. -/
private theorem resid_324286212 : ∃ a ∈ offsets, (2 * 324286212 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `324673236` has no complement among the first 200 offsets; `336179`, the
`202`-th offset of the list, makes `2 * 324673236 + 336179` prime. -/
private theorem resid_324673236 : ∃ a ∈ offsets, (2 * 324673236 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `325481874` has no complement among the first 200 offsets; `1668413`, the
`208`-th offset of the list, makes `2 * 325481874 + 1668413` prime. -/
private theorem resid_325481874 : ∃ a ∈ offsets, (2 * 325481874 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `329314437` has no complement among the first 200 offsets; `336179`, the
`202`-th offset of the list, makes `2 * 329314437 + 336179` prime. -/
private theorem resid_329314437 : ∃ a ∈ offsets, (2 * 329314437 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `332589453` has no complement among the first 200 offsets; `969173`, the
`206`-th offset of the list, makes `2 * 332589453 + 969173` prime. -/
private theorem resid_332589453 : ∃ a ∈ offsets, (2 * 332589453 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `333524694` has no complement among the first 200 offsets; `3361883`, the
`211`-th offset of the list, makes `2 * 333524694 + 3361883` prime. -/
private theorem resid_333524694 : ∃ a ∈ offsets, (2 * 333524694 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `337088049` has no complement among the first 200 offsets; `336179`, the
`202`-th offset of the list, makes `2 * 337088049 + 336179` prime. -/
private theorem resid_337088049 : ∃ a ∈ offsets, (2 * 337088049 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `338766068` has no complement among the first 200 offsets; `2240913`, the
`209`-th offset of the list, makes `2 * 338766068 + 2240913` prime. -/
private theorem resid_338766068 : ∃ a ∈ offsets, (2 * 338766068 + a).Prime := by
  refine ⟨2240913, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `339540369` has no complement among the first 200 offsets; `3166973`, the
`210`-th offset of the list, makes `2 * 339540369 + 3166973` prime. -/
private theorem resid_339540369 : ∃ a ∈ offsets, (2 * 339540369 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `341484933` has no complement among the first 200 offsets; `3697757`, the
`212`-th offset of the list, makes `2 * 341484933 + 3697757` prime. -/
private theorem resid_341484933 : ∃ a ∈ offsets, (2 * 341484933 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `346627713` has no complement among the first 200 offsets; `3361883`, the
`211`-th offset of the list, makes `2 * 346627713 + 3361883` prime. -/
private theorem resid_346627713 : ∃ a ∈ offsets, (2 * 346627713 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `349455987` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 349455987 + 1334189` prime. -/
private theorem resid_349455987 : ∃ a ∈ offsets, (2 * 349455987 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `352146954` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 352146954 + 1334189` prime. -/
private theorem resid_352146954 : ∃ a ∈ offsets, (2 * 352146954 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `359588094` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 359588094 + 1334189` prime. -/
private theorem resid_359588094 : ∃ a ∈ offsets, (2 * 359588094 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `360864942` has no complement among the first 200 offsets; `699059`, the
`205`-th offset of the list, makes `2 * 360864942 + 699059` prime. -/
private theorem resid_360864942 : ∃ a ∈ offsets, (2 * 360864942 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `361509321` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 361509321 + 1334189` prime. -/
private theorem resid_361509321 : ∃ a ∈ offsets, (2 * 361509321 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `362044779` has no complement among the first 200 offsets; `3166973`, the
`210`-th offset of the list, makes `2 * 362044779 + 3166973` prime. -/
private theorem resid_362044779 : ∃ a ∈ offsets, (2 * 362044779 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `363307872` has no complement among the first 200 offsets; `699059`, the
`205`-th offset of the list, makes `2 * 363307872 + 699059` prime. -/
private theorem resid_363307872 : ∃ a ∈ offsets, (2 * 363307872 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `363929721` has no complement among the first 200 offsets; `3697757`, the
`212`-th offset of the list, makes `2 * 363929721 + 3697757` prime. -/
private theorem resid_363929721 : ∃ a ∈ offsets, (2 * 363929721 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `368052738` has no complement among the first 200 offsets; `1668413`, the
`208`-th offset of the list, makes `2 * 368052738 + 1668413` prime. -/
private theorem resid_368052738 : ∃ a ∈ offsets, (2 * 368052738 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `368706636` has no complement among the first 200 offsets; `3697757`, the
`212`-th offset of the list, makes `2 * 368706636 + 3697757` prime. -/
private theorem resid_368706636 : ∃ a ∈ offsets, (2 * 368706636 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `368896868` has no complement among the first 200 offsets; `505017`, the
`204`-th offset of the list, makes `2 * 368896868 + 505017` prime. -/
private theorem resid_368896868 : ∃ a ∈ offsets, (2 * 368896868 + a).Prime := by
  refine ⟨505017, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `370221216` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 370221216 + 1334189` prime. -/
private theorem resid_370221216 : ∃ a ∈ offsets, (2 * 370221216 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `373647957` has no complement among the first 200 offsets; `1668413`, the
`208`-th offset of the list, makes `2 * 373647957 + 1668413` prime. -/
private theorem resid_373647957 : ∃ a ∈ offsets, (2 * 373647957 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `374732334` has no complement among the first 200 offsets; `3361883`, the
`211`-th offset of the list, makes `2 * 374732334 + 3361883` prime. -/
private theorem resid_374732334 : ∃ a ∈ offsets, (2 * 374732334 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- The single index `374917002` has no complement among the first 200 offsets; `1334189`, the
`207`-th offset of the list, makes `2 * 374917002 + 1334189` prime. -/
private theorem resid_374917002 : ∃ a ∈ offsets, (2 * 374917002 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact prime_of_bit _ (by norm_num)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2]) (by decide +kernel)

/-- Every `j` from 312500000 through 312999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[625000000, 625999998]`. -/
private theorem w1_1 : ∀ j : ℕ, 312500000 ≤ j → j < 313000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 625000000) (x1 := 625999998) (lo := 625000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 313000000 through 313499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[626000000, 626999998]`. -/
private theorem w1_2 : ∀ j : ℕ, 313000000 ≤ j → j < 313500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 626000000) (x1 := 626999998) (lo := 626000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 313500000 through 313999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[627000000, 627999998]`. -/
private theorem w1_3 : ∀ j : ℕ, 313500000 ≤ j → j < 314000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 627000000) (x1 := 627999998) (lo := 627000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 314000000 through 314499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[628000000, 628999998]`. -/
private theorem w1_4 : ∀ j : ℕ, 314000000 ≤ j → j < 314500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 628000000) (x1 := 628999998) (lo := 628000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 314500000 through 314999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[629000000, 629999998]`. -/
private theorem w1_5 : ∀ j : ℕ, 314500000 ≤ j → j < 315000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 629000000) (x1 := 629999998) (lo := 629000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 315000000 through 315499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[630000000, 630999998]`. -/
private theorem w1_6 : ∀ j : ℕ, 315000000 ≤ j → j < 315500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 630000000) (x1 := 630999998) (lo := 630000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 315500000 through 315999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[631000000, 631999998]`. -/
private theorem w1_7 : ∀ j : ℕ, 315500000 ≤ j → j < 316000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 631000000) (x1 := 631999998) (lo := 631000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 316000000 through 316499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[632000000, 632999998]`. -/
private theorem w1_8 : ∀ j : ℕ, 316000000 ≤ j → j < 316500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 632000000) (x1 := 632999998) (lo := 632000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 316500000 through 316999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[633000000, 633999998]`. -/
private theorem w1_9 : ∀ j : ℕ, 316500000 ≤ j → j < 317000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 633000000) (x1 := 633999998) (lo := 633000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 317000000 through 317499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[634000000, 634999998]`. -/
private theorem w1_10 : ∀ j : ℕ, 317000000 ≤ j → j < 317500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 634000000) (x1 := 634999998) (lo := 634000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 317500000 through 317858306 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[635000000, 635716612]`. -/
private theorem w1_11 : ∀ j : ℕ, 317500000 ≤ j → j < 317858307 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 635000000) (x1 := 635716612) (lo := 635000069) (W := 849935)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 317858308 through 317999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[635716616, 635999998]`. -/
private theorem w1_12 : ∀ j : ℕ, 317858308 ≤ j → j < 318000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 635716616) (x1 := 635999998) (lo := 635716685) (W := 416705)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 318000000 through 318147686 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[636000000, 636295372]`. -/
private theorem w1_13 : ∀ j : ℕ, 318000000 ≤ j → j < 318147687 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 636000000) (x1 := 636295372) (lo := 636000069) (W := 428695)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 318147688 through 318499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[636295376, 636999998]`. -/
private theorem w1_14 : ∀ j : ℕ, 318147688 ≤ j → j < 318500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 636295376) (x1 := 636999998) (lo := 636295445) (W := 837945)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 318500000 through 318999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[637000000, 637999998]`. -/
private theorem w1_15 : ∀ j : ℕ, 318500000 ≤ j → j < 319000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 637000000) (x1 := 637999998) (lo := 637000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 319000000 through 319499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[638000000, 638999998]`. -/
private theorem w1_16 : ∀ j : ℕ, 319000000 ≤ j → j < 319500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 638000000) (x1 := 638999998) (lo := 638000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 319500000 through 319999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[639000000, 639999998]`. -/
private theorem w1_17 : ∀ j : ℕ, 319500000 ≤ j → j < 320000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 639000000) (x1 := 639999998) (lo := 639000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 320000000 through 320499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[640000000, 640999998]`. -/
private theorem w1_18 : ∀ j : ℕ, 320000000 ≤ j → j < 320500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 640000000) (x1 := 640999998) (lo := 640000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 320500000 through 320999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[641000000, 641999998]`. -/
private theorem w1_19 : ∀ j : ℕ, 320500000 ≤ j → j < 321000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 641000000) (x1 := 641999998) (lo := 641000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 321000000 through 321499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[642000000, 642999998]`. -/
private theorem w1_20 : ∀ j : ℕ, 321000000 ≤ j → j < 321500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 642000000) (x1 := 642999998) (lo := 642000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 321500000 through 321999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[643000000, 643999998]`. -/
private theorem w1_21 : ∀ j : ℕ, 321500000 ≤ j → j < 322000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 643000000) (x1 := 643999998) (lo := 643000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 322000000 through 322046336 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[644000000, 644092672]`. -/
private theorem w1_22 : ∀ j : ℕ, 322000000 ≤ j → j < 322046337 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 644000000) (x1 := 644092672) (lo := 644000069) (W := 225995)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 322046338 through 322131926 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[644092676, 644263852]`. -/
private theorem w1_23 : ∀ j : ℕ, 322046338 ≤ j → j < 322131927 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 644092676) (x1 := 644263852) (lo := 644092745) (W := 304499)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 322131928 through 322499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[644263856, 644999998]`. -/
private theorem w1_24 : ∀ j : ℕ, 322131928 ≤ j → j < 322500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 644263856) (x1 := 644999998) (lo := 644263925) (W := 869465)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 322500000 through 322999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[645000000, 645999998]`. -/
private theorem w1_25 : ∀ j : ℕ, 322500000 ≤ j → j < 323000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 645000000) (x1 := 645999998) (lo := 645000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 323000000 through 323499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[646000000, 646999998]`. -/
private theorem w2_1 : ∀ j : ℕ, 323000000 ≤ j → j < 323500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 646000000) (x1 := 646999998) (lo := 646000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 323500000 through 323601442 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[647000000, 647202884]`. -/
private theorem w2_2 : ∀ j : ℕ, 323500000 ≤ j → j < 323601443 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 647000000) (x1 := 647202884) (lo := 647000069) (W := 336207)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 323601444 through 323999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[647202888, 647999998]`. -/
private theorem w2_3 : ∀ j : ℕ, 323601444 ≤ j → j < 324000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 647202888) (x1 := 647999998) (lo := 647202957) (W := 930433)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 324000000 through 324286211 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[648000000, 648572422]`. -/
private theorem w2_4 : ∀ j : ℕ, 324000000 ≤ j → j < 324286212 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 648000000) (x1 := 648572422) (lo := 648000069) (W := 705745)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 324286213 through 324499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[648572426, 648999998]`. -/
private theorem w2_5 : ∀ j : ℕ, 324286213 ≤ j → j < 324500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 648572426) (x1 := 648999998) (lo := 648572495) (W := 560895)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 324500000 through 324673235 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[649000000, 649346470]`. -/
private theorem w2_6 : ∀ j : ℕ, 324500000 ≤ j → j < 324673236 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 649000000) (x1 := 649346470) (lo := 649000069) (W := 479793)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 324673237 through 324999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[649346474, 649999998]`. -/
private theorem w2_7 : ∀ j : ℕ, 324673237 ≤ j → j < 325000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 649346474) (x1 := 649999998) (lo := 649346543) (W := 786847)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 325000000 through 325481873 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[650000000, 650963746]`. -/
private theorem w2_8 : ∀ j : ℕ, 325000000 ≤ j → j < 325481874 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 650000000) (x1 := 650963746) (lo := 650000069) (W := 1097069)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 325481875 through 325499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[650963750, 650999998]`. -/
private theorem w2_9 : ∀ j : ℕ, 325481875 ≤ j → j < 325500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 650963750) (x1 := 650999998) (lo := 650963819) (W := 169571)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 325500000 through 325999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[651000000, 651999998]`. -/
private theorem w2_10 : ∀ j : ℕ, 325500000 ≤ j → j < 326000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 651000000) (x1 := 651999998) (lo := 651000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 326000000 through 326499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[652000000, 652999998]`. -/
private theorem w2_11 : ∀ j : ℕ, 326000000 ≤ j → j < 326500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 652000000) (x1 := 652999998) (lo := 652000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 326500000 through 326999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[653000000, 653999998]`. -/
private theorem w2_12 : ∀ j : ℕ, 326500000 ≤ j → j < 327000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 653000000) (x1 := 653999998) (lo := 653000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 327000000 through 327499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[654000000, 654999998]`. -/
private theorem w2_13 : ∀ j : ℕ, 327000000 ≤ j → j < 327500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 654000000) (x1 := 654999998) (lo := 654000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 327500000 through 327999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[655000000, 655999998]`. -/
private theorem w2_14 : ∀ j : ℕ, 327500000 ≤ j → j < 328000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 655000000) (x1 := 655999998) (lo := 655000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 328000000 through 328499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[656000000, 656999998]`. -/
private theorem w2_15 : ∀ j : ℕ, 328000000 ≤ j → j < 328500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 656000000) (x1 := 656999998) (lo := 656000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 328500000 through 328999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[657000000, 657999998]`. -/
private theorem w2_16 : ∀ j : ℕ, 328500000 ≤ j → j < 329000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 657000000) (x1 := 657999998) (lo := 657000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 329000000 through 329314436 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[658000000, 658628872]`. -/
private theorem w2_17 : ∀ j : ℕ, 329000000 ≤ j → j < 329314437 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 658000000) (x1 := 658628872) (lo := 658000069) (W := 762195)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 329314438 through 329499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[658628876, 658999998]`. -/
private theorem w2_18 : ∀ j : ℕ, 329314438 ≤ j → j < 329500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 658628876) (x1 := 658999998) (lo := 658628945) (W := 504445)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 329500000 through 329999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[659000000, 659999998]`. -/
private theorem w2_19 : ∀ j : ℕ, 329500000 ≤ j → j < 330000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 659000000) (x1 := 659999998) (lo := 659000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 330000000 through 330499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[660000000, 660999998]`. -/
private theorem w2_20 : ∀ j : ℕ, 330000000 ≤ j → j < 330500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 660000000) (x1 := 660999998) (lo := 660000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 330500000 through 330999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[661000000, 661999998]`. -/
private theorem w2_21 : ∀ j : ℕ, 330500000 ≤ j → j < 331000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 661000000) (x1 := 661999998) (lo := 661000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 331000000 through 331499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[662000000, 662999998]`. -/
private theorem w2_22 : ∀ j : ℕ, 331000000 ≤ j → j < 331500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 662000000) (x1 := 662999998) (lo := 662000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 331500000 through 331999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[663000000, 663999998]`. -/
private theorem w2_23 : ∀ j : ℕ, 331500000 ≤ j → j < 332000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 663000000) (x1 := 663999998) (lo := 663000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 332000000 through 332499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[664000000, 664999998]`. -/
private theorem w2_24 : ∀ j : ℕ, 332000000 ≤ j → j < 332500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 664000000) (x1 := 664999998) (lo := 664000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 332500000 through 332589452 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[665000000, 665178904]`. -/
private theorem w2_25 : ∀ j : ℕ, 332500000 ≤ j → j < 332589453 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 665000000) (x1 := 665178904) (lo := 665000069) (W := 312227)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 332589454 through 332999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[665178908, 665999998]`. -/
private theorem w2_26 : ∀ j : ℕ, 332589454 ≤ j → j < 333000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 665178908) (x1 := 665999998) (lo := 665178977) (W := 954413)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 333000000 through 333499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[666000000, 666999998]`. -/
private theorem w2_27 : ∀ j : ℕ, 333000000 ≤ j → j < 333500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 666000000) (x1 := 666999998) (lo := 666000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 333500000 through 333524693 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[667000000, 667049386]`. -/
private theorem w3_1 : ∀ j : ℕ, 333500000 ≤ j → j < 333524694 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 667000000) (x1 := 667049386) (lo := 667000069) (W := 182709)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 333524695 through 333999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[667049390, 667999998]`. -/
private theorem w3_2 : ∀ j : ℕ, 333524695 ≤ j → j < 334000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 667049390) (x1 := 667999998) (lo := 667049459) (W := 1083931)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 334000000 through 334499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[668000000, 668999998]`. -/
private theorem w3_3 : ∀ j : ℕ, 334000000 ≤ j → j < 334500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 668000000) (x1 := 668999998) (lo := 668000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 334500000 through 334999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[669000000, 669999998]`. -/
private theorem w3_4 : ∀ j : ℕ, 334500000 ≤ j → j < 335000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 669000000) (x1 := 669999998) (lo := 669000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 335000000 through 335499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[670000000, 670999998]`. -/
private theorem w3_5 : ∀ j : ℕ, 335000000 ≤ j → j < 335500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 670000000) (x1 := 670999998) (lo := 670000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 335500000 through 335999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[671000000, 671999998]`. -/
private theorem w3_6 : ∀ j : ℕ, 335500000 ≤ j → j < 336000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 671000000) (x1 := 671999998) (lo := 671000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 336000000 through 336499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[672000000, 672999998]`. -/
private theorem w3_7 : ∀ j : ℕ, 336000000 ≤ j → j < 336500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 672000000) (x1 := 672999998) (lo := 672000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 336500000 through 336999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[673000000, 673999998]`. -/
private theorem w3_8 : ∀ j : ℕ, 336500000 ≤ j → j < 337000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 673000000) (x1 := 673999998) (lo := 673000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 337000000 through 337088048 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[674000000, 674176096]`. -/
private theorem w3_9 : ∀ j : ℕ, 337000000 ≤ j → j < 337088049 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 674000000) (x1 := 674176096) (lo := 674000069) (W := 309419)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 337088050 through 337499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[674176100, 674999998]`. -/
private theorem w3_10 : ∀ j : ℕ, 337088050 ≤ j → j < 337500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 674176100) (x1 := 674999998) (lo := 674176169) (W := 957221)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 337500000 through 337999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[675000000, 675999998]`. -/
private theorem w3_11 : ∀ j : ℕ, 337500000 ≤ j → j < 338000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 675000000) (x1 := 675999998) (lo := 675000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 338000000 through 338499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[676000000, 676999998]`. -/
private theorem w3_12 : ∀ j : ℕ, 338000000 ≤ j → j < 338500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 676000000) (x1 := 676999998) (lo := 676000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 338500000 through 338766067 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[677000000, 677532134]`. -/
private theorem w3_13 : ∀ j : ℕ, 338500000 ≤ j → j < 338766068 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 677000000) (x1 := 677532134) (lo := 677000069) (W := 665457)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 338766069 through 338999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[677532138, 677999998]`. -/
private theorem w3_14 : ∀ j : ℕ, 338766069 ≤ j → j < 339000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 677532138) (x1 := 677999998) (lo := 677532207) (W := 601183)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 339000000 through 339499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[678000000, 678999998]`. -/
private theorem w3_15 : ∀ j : ℕ, 339000000 ≤ j → j < 339500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 678000000) (x1 := 678999998) (lo := 678000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 339500000 through 339540368 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[679000000, 679080736]`. -/
private theorem w3_16 : ∀ j : ℕ, 339500000 ≤ j → j < 339540369 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 679000000) (x1 := 679080736) (lo := 679000069) (W := 214059)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 339540370 through 339999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[679080740, 679999998]`. -/
private theorem w3_17 : ∀ j : ℕ, 339540370 ≤ j → j < 340000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 679080740) (x1 := 679999998) (lo := 679080809) (W := 1052581)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 340000000 through 340499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[680000000, 680999998]`. -/
private theorem w3_18 : ∀ j : ℕ, 340000000 ≤ j → j < 340500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 680000000) (x1 := 680999998) (lo := 680000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 340500000 through 340999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[681000000, 681999998]`. -/
private theorem w3_19 : ∀ j : ℕ, 340500000 ≤ j → j < 341000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 681000000) (x1 := 681999998) (lo := 681000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 341000000 through 341484932 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[682000000, 682969864]`. -/
private theorem w3_20 : ∀ j : ℕ, 341000000 ≤ j → j < 341484933 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 682000000) (x1 := 682969864) (lo := 682000069) (W := 1103187)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 341484934 through 341499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[682969868, 682999998]`. -/
private theorem w3_21 : ∀ j : ℕ, 341484934 ≤ j → j < 341500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 682969868) (x1 := 682999998) (lo := 682969937) (W := 163453)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 341500000 through 341999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[683000000, 683999998]`. -/
private theorem w3_22 : ∀ j : ℕ, 341500000 ≤ j → j < 342000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 683000000) (x1 := 683999998) (lo := 683000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 342000000 through 342499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[684000000, 684999998]`. -/
private theorem w3_23 : ∀ j : ℕ, 342000000 ≤ j → j < 342500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 684000000) (x1 := 684999998) (lo := 684000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 342500000 through 342999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[685000000, 685999998]`. -/
private theorem w3_24 : ∀ j : ℕ, 342500000 ≤ j → j < 343000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 685000000) (x1 := 685999998) (lo := 685000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 343000000 through 343499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[686000000, 686999998]`. -/
private theorem w3_25 : ∀ j : ℕ, 343000000 ≤ j → j < 343500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 686000000) (x1 := 686999998) (lo := 686000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 343500000 through 343999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[687000000, 687999998]`. -/
private theorem w3_26 : ∀ j : ℕ, 343500000 ≤ j → j < 344000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 687000000) (x1 := 687999998) (lo := 687000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 344000000 through 344499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[688000000, 688999998]`. -/
private theorem w4_1 : ∀ j : ℕ, 344000000 ≤ j → j < 344500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 688000000) (x1 := 688999998) (lo := 688000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 344500000 through 344999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[689000000, 689999998]`. -/
private theorem w4_2 : ∀ j : ℕ, 344500000 ≤ j → j < 345000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 689000000) (x1 := 689999998) (lo := 689000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 345000000 through 345499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[690000000, 690999998]`. -/
private theorem w4_3 : ∀ j : ℕ, 345000000 ≤ j → j < 345500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 690000000) (x1 := 690999998) (lo := 690000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 345500000 through 345999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[691000000, 691999998]`. -/
private theorem w4_4 : ∀ j : ℕ, 345500000 ≤ j → j < 346000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 691000000) (x1 := 691999998) (lo := 691000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 346000000 through 346499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[692000000, 692999998]`. -/
private theorem w4_5 : ∀ j : ℕ, 346000000 ≤ j → j < 346500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 692000000) (x1 := 692999998) (lo := 692000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 346500000 through 346627712 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[693000000, 693255424]`. -/
private theorem w4_6 : ∀ j : ℕ, 346500000 ≤ j → j < 346627713 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 693000000) (x1 := 693255424) (lo := 693000069) (W := 388747)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 346627714 through 346999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[693255428, 693999998]`. -/
private theorem w4_7 : ∀ j : ℕ, 346627714 ≤ j → j < 347000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 693255428) (x1 := 693999998) (lo := 693255497) (W := 877893)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 347000000 through 347499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[694000000, 694999998]`. -/
private theorem w4_8 : ∀ j : ℕ, 347000000 ≤ j → j < 347500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 694000000) (x1 := 694999998) (lo := 694000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 347500000 through 347999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[695000000, 695999998]`. -/
private theorem w4_9 : ∀ j : ℕ, 347500000 ≤ j → j < 348000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 695000000) (x1 := 695999998) (lo := 695000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 348000000 through 348499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[696000000, 696999998]`. -/
private theorem w4_10 : ∀ j : ℕ, 348000000 ≤ j → j < 348500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 696000000) (x1 := 696999998) (lo := 696000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 348500000 through 348999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[697000000, 697999998]`. -/
private theorem w4_11 : ∀ j : ℕ, 348500000 ≤ j → j < 349000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 697000000) (x1 := 697999998) (lo := 697000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 349000000 through 349455986 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[698000000, 698911972]`. -/
private theorem w4_12 : ∀ j : ℕ, 349000000 ≤ j → j < 349455987 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 698000000) (x1 := 698911972) (lo := 698000069) (W := 1045295)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 349455988 through 349499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[698911976, 698999998]`. -/
private theorem w4_13 : ∀ j : ℕ, 349455988 ≤ j → j < 349500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 698911976) (x1 := 698999998) (lo := 698912045) (W := 221345)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 349500000 through 349999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[699000000, 699999998]`. -/
private theorem w4_14 : ∀ j : ℕ, 349500000 ≤ j → j < 350000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 699000000) (x1 := 699999998) (lo := 699000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 350000000 through 350499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[700000000, 700999998]`. -/
private theorem w4_15 : ∀ j : ℕ, 350000000 ≤ j → j < 350500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 700000000) (x1 := 700999998) (lo := 700000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 350500000 through 350999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[701000000, 701999998]`. -/
private theorem w4_16 : ∀ j : ℕ, 350500000 ≤ j → j < 351000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 701000000) (x1 := 701999998) (lo := 701000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 351000000 through 351499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[702000000, 702999998]`. -/
private theorem w4_17 : ∀ j : ℕ, 351000000 ≤ j → j < 351500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 702000000) (x1 := 702999998) (lo := 702000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 351500000 through 351999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[703000000, 703999998]`. -/
private theorem w4_18 : ∀ j : ℕ, 351500000 ≤ j → j < 352000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 703000000) (x1 := 703999998) (lo := 703000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 352000000 through 352146953 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[704000000, 704293906]`. -/
private theorem w4_19 : ∀ j : ℕ, 352000000 ≤ j → j < 352146954 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 704000000) (x1 := 704293906) (lo := 704000069) (W := 427229)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 352146955 through 352499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[704293910, 704999998]`. -/
private theorem w4_20 : ∀ j : ℕ, 352146955 ≤ j → j < 352500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 704293910) (x1 := 704999998) (lo := 704293979) (W := 839411)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 352500000 through 352999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[705000000, 705999998]`. -/
private theorem w4_21 : ∀ j : ℕ, 352500000 ≤ j → j < 353000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 705000000) (x1 := 705999998) (lo := 705000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 353000000 through 353499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[706000000, 706999998]`. -/
private theorem w4_22 : ∀ j : ℕ, 353000000 ≤ j → j < 353500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 706000000) (x1 := 706999998) (lo := 706000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 353500000 through 353999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[707000000, 707999998]`. -/
private theorem w4_23 : ∀ j : ℕ, 353500000 ≤ j → j < 354000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 707000000) (x1 := 707999998) (lo := 707000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 354000000 through 354499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[708000000, 708999998]`. -/
private theorem w4_24 : ∀ j : ℕ, 354000000 ≤ j → j < 354500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 708000000) (x1 := 708999998) (lo := 708000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 354500000 through 354999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[709000000, 709999998]`. -/
private theorem w5_1 : ∀ j : ℕ, 354500000 ≤ j → j < 355000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 709000000) (x1 := 709999998) (lo := 709000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 355000000 through 355499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[710000000, 710999998]`. -/
private theorem w5_2 : ∀ j : ℕ, 355000000 ≤ j → j < 355500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 710000000) (x1 := 710999998) (lo := 710000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 355500000 through 355999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[711000000, 711999998]`. -/
private theorem w5_3 : ∀ j : ℕ, 355500000 ≤ j → j < 356000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 711000000) (x1 := 711999998) (lo := 711000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 356000000 through 356499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[712000000, 712999998]`. -/
private theorem w5_4 : ∀ j : ℕ, 356000000 ≤ j → j < 356500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 712000000) (x1 := 712999998) (lo := 712000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 356500000 through 356999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[713000000, 713999998]`. -/
private theorem w5_5 : ∀ j : ℕ, 356500000 ≤ j → j < 357000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 713000000) (x1 := 713999998) (lo := 713000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 357000000 through 357499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[714000000, 714999998]`. -/
private theorem w5_6 : ∀ j : ℕ, 357000000 ≤ j → j < 357500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 714000000) (x1 := 714999998) (lo := 714000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 357500000 through 357999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[715000000, 715999998]`. -/
private theorem w5_7 : ∀ j : ℕ, 357500000 ≤ j → j < 358000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 715000000) (x1 := 715999998) (lo := 715000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 358000000 through 358499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[716000000, 716999998]`. -/
private theorem w5_8 : ∀ j : ℕ, 358000000 ≤ j → j < 358500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 716000000) (x1 := 716999998) (lo := 716000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 358500000 through 358999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[717000000, 717999998]`. -/
private theorem w5_9 : ∀ j : ℕ, 358500000 ≤ j → j < 359000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 717000000) (x1 := 717999998) (lo := 717000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 359000000 through 359499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[718000000, 718999998]`. -/
private theorem w5_10 : ∀ j : ℕ, 359000000 ≤ j → j < 359500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 718000000) (x1 := 718999998) (lo := 718000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 359500000 through 359588093 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[719000000, 719176186]`. -/
private theorem w5_11 : ∀ j : ℕ, 359500000 ≤ j → j < 359588094 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 719000000) (x1 := 719176186) (lo := 719000069) (W := 309509)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 359588095 through 359999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[719176190, 719999998]`. -/
private theorem w5_12 : ∀ j : ℕ, 359588095 ≤ j → j < 360000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 719176190) (x1 := 719999998) (lo := 719176259) (W := 957131)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 360000000 through 360499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[720000000, 720999998]`. -/
private theorem w5_13 : ∀ j : ℕ, 360000000 ≤ j → j < 360500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 720000000) (x1 := 720999998) (lo := 720000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 360500000 through 360864941 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[721000000, 721729882]`. -/
private theorem w5_14 : ∀ j : ℕ, 360500000 ≤ j → j < 360864942 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 721000000) (x1 := 721729882) (lo := 721000069) (W := 863205)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 360864943 through 360999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[721729886, 721999998]`. -/
private theorem w5_15 : ∀ j : ℕ, 360864943 ≤ j → j < 361000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 721729886) (x1 := 721999998) (lo := 721729955) (W := 403435)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 361000000 through 361499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[722000000, 722999998]`. -/
private theorem w5_16 : ∀ j : ℕ, 361000000 ≤ j → j < 361500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 722000000) (x1 := 722999998) (lo := 722000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 361500000 through 361509320 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[723000000, 723018640]`. -/
private theorem w5_17 : ∀ j : ℕ, 361500000 ≤ j → j < 361509321 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 723000000) (x1 := 723018640) (lo := 723000069) (W := 151963)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 361509322 through 361999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[723018644, 723999998]`. -/
private theorem w5_18 : ∀ j : ℕ, 361509322 ≤ j → j < 362000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 723018644) (x1 := 723999998) (lo := 723018713) (W := 1114677)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 362000000 through 362044778 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[724000000, 724089556]`. -/
private theorem w5_19 : ∀ j : ℕ, 362000000 ≤ j → j < 362044779 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 724000000) (x1 := 724089556) (lo := 724000069) (W := 222879)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 362044780 through 362499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[724089560, 724999998]`. -/
private theorem w5_20 : ∀ j : ℕ, 362044780 ≤ j → j < 362500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 724089560) (x1 := 724999998) (lo := 724089629) (W := 1043761)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 362500000 through 362999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[725000000, 725999998]`. -/
private theorem w5_21 : ∀ j : ℕ, 362500000 ≤ j → j < 363000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 725000000) (x1 := 725999998) (lo := 725000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 363000000 through 363307871 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[726000000, 726615742]`. -/
private theorem w5_22 : ∀ j : ℕ, 363000000 ≤ j → j < 363307872 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 726000000) (x1 := 726615742) (lo := 726000069) (W := 749065)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 363307873 through 363499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[726615746, 726999998]`. -/
private theorem w5_23 : ∀ j : ℕ, 363307873 ≤ j → j < 363500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 726615746) (x1 := 726999998) (lo := 726615815) (W := 517575)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 363500000 through 363929720 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[727000000, 727859440]`. -/
private theorem w5_24 : ∀ j : ℕ, 363500000 ≤ j → j < 363929721 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 727000000) (x1 := 727859440) (lo := 727000069) (W := 992763)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 363929722 through 363999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[727859444, 727999998]`. -/
private theorem w5_25 : ∀ j : ℕ, 363929722 ≤ j → j < 364000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 727859444) (x1 := 727999998) (lo := 727859513) (W := 273877)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 364000000 through 364499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[728000000, 728999998]`. -/
private theorem w5_26 : ∀ j : ℕ, 364000000 ≤ j → j < 364500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 728000000) (x1 := 728999998) (lo := 728000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 364500000 through 364999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[729000000, 729999998]`. -/
private theorem w5_27 : ∀ j : ℕ, 364500000 ≤ j → j < 365000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 729000000) (x1 := 729999998) (lo := 729000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 365000000 through 365499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[730000000, 730999998]`. -/
private theorem w6_1 : ∀ j : ℕ, 365000000 ≤ j → j < 365500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 730000000) (x1 := 730999998) (lo := 730000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 365500000 through 365999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[731000000, 731999998]`. -/
private theorem w6_2 : ∀ j : ℕ, 365500000 ≤ j → j < 366000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 731000000) (x1 := 731999998) (lo := 731000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 366000000 through 366499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[732000000, 732999998]`. -/
private theorem w6_3 : ∀ j : ℕ, 366000000 ≤ j → j < 366500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 732000000) (x1 := 732999998) (lo := 732000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 366500000 through 366999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[733000000, 733999998]`. -/
private theorem w6_4 : ∀ j : ℕ, 366500000 ≤ j → j < 367000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 733000000) (x1 := 733999998) (lo := 733000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 367000000 through 367499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[734000000, 734999998]`. -/
private theorem w6_5 : ∀ j : ℕ, 367000000 ≤ j → j < 367500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 734000000) (x1 := 734999998) (lo := 734000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 367500000 through 367999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[735000000, 735999998]`. -/
private theorem w6_6 : ∀ j : ℕ, 367500000 ≤ j → j < 368000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 735000000) (x1 := 735999998) (lo := 735000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 368000000 through 368052737 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[736000000, 736105474]`. -/
private theorem w6_7 : ∀ j : ℕ, 368000000 ≤ j → j < 368052738 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 736000000) (x1 := 736105474) (lo := 736000069) (W := 238797)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 368052739 through 368499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[736105478, 736999998]`. -/
private theorem w6_8 : ∀ j : ℕ, 368052739 ≤ j → j < 368500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 736105478) (x1 := 736999998) (lo := 736105547) (W := 1027843)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 368500000 through 368706635 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[737000000, 737413270]`. -/
private theorem w6_9 : ∀ j : ℕ, 368500000 ≤ j → j < 368706636 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 737000000) (x1 := 737413270) (lo := 737000069) (W := 546593)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 368706637 through 368896867 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[737413274, 737793734]`. -/
private theorem w6_10 : ∀ j : ℕ, 368706637 ≤ j → j < 368896868 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 737413274) (x1 := 737793734) (lo := 737413343) (W := 513783)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 368896869 through 368999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[737793738, 737999998]`. -/
private theorem w6_11 : ∀ j : ℕ, 368896869 ≤ j → j < 369000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 737793738) (x1 := 737999998) (lo := 737793807) (W := 339583)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 369000000 through 369499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[738000000, 738999998]`. -/
private theorem w6_12 : ∀ j : ℕ, 369000000 ≤ j → j < 369500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 738000000) (x1 := 738999998) (lo := 738000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 369500000 through 369999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[739000000, 739999998]`. -/
private theorem w6_13 : ∀ j : ℕ, 369500000 ≤ j → j < 370000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 739000000) (x1 := 739999998) (lo := 739000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 370000000 through 370221215 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[740000000, 740442430]`. -/
private theorem w6_14 : ∀ j : ℕ, 370000000 ≤ j → j < 370221216 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 740000000) (x1 := 740442430) (lo := 740000069) (W := 575753)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 370221217 through 370499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[740442434, 740999998]`. -/
private theorem w6_15 : ∀ j : ℕ, 370221217 ≤ j → j < 370500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 740442434) (x1 := 740999998) (lo := 740442503) (W := 690887)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 370500000 through 370999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[741000000, 741999998]`. -/
private theorem w6_16 : ∀ j : ℕ, 370500000 ≤ j → j < 371000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 741000000) (x1 := 741999998) (lo := 741000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 371000000 through 371499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[742000000, 742999998]`. -/
private theorem w6_17 : ∀ j : ℕ, 371000000 ≤ j → j < 371500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 742000000) (x1 := 742999998) (lo := 742000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 371500000 through 371999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[743000000, 743999998]`. -/
private theorem w6_18 : ∀ j : ℕ, 371500000 ≤ j → j < 372000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 743000000) (x1 := 743999998) (lo := 743000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 372000000 through 372499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[744000000, 744999998]`. -/
private theorem w6_19 : ∀ j : ℕ, 372000000 ≤ j → j < 372500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 744000000) (x1 := 744999998) (lo := 744000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 372500000 through 372999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[745000000, 745999998]`. -/
private theorem w6_20 : ∀ j : ℕ, 372500000 ≤ j → j < 373000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 745000000) (x1 := 745999998) (lo := 745000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 373000000 through 373499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[746000000, 746999998]`. -/
private theorem w6_21 : ∀ j : ℕ, 373000000 ≤ j → j < 373500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 746000000) (x1 := 746999998) (lo := 746000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 373500000 through 373647956 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[747000000, 747295912]`. -/
private theorem w6_22 : ∀ j : ℕ, 373500000 ≤ j → j < 373647957 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 747000000) (x1 := 747295912) (lo := 747000069) (W := 429235)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 373647958 through 373999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[747295916, 747999998]`. -/
private theorem w6_23 : ∀ j : ℕ, 373647958 ≤ j → j < 374000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 747295916) (x1 := 747999998) (lo := 747295985) (W := 837405)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 374000000 through 374499999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[748000000, 748999998]`. -/
private theorem w6_24 : ∀ j : ℕ, 374000000 ≤ j → j < 374500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 748000000) (x1 := 748999998) (lo := 748000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 374500000 through 374732333 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[749000000, 749464666]`. -/
private theorem w6_25 : ∀ j : ℕ, 374500000 ≤ j → j < 374732334 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 749000000) (x1 := 749464666) (lo := 749000069) (W := 597989)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 374732335 through 374917001 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[749464670, 749834002]`. -/
private theorem w6_26 : ∀ j : ℕ, 374732335 ≤ j → j < 374917002 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 749464670) (x1 := 749834002) (lo := 749464739) (W := 502655)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

/-- Every `j` from 374917003 through 374999999 has a prime complement among the first 200 offsets.
Kernel-checked shifted window sieve over the even `2 * j` in `[749834006, 749999998]`. -/
private theorem w6_27 : ∀ j : ℕ, 374917003 ≤ j → j < 375000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 749834006) (x1 := 749999998) (lo := 749834075) (W := 299315)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
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
  intro j hlo hhi
  by_cases c0 : j < 313000000
  · exact w1_1 j (by omega) c0
  by_cases c1 : j < 313500000
  · exact w1_2 j (by omega) c1
  by_cases c2 : j < 314000000
  · exact w1_3 j (by omega) c2
  by_cases c3 : j < 314500000
  · exact w1_4 j (by omega) c3
  by_cases c4 : j < 315000000
  · exact w1_5 j (by omega) c4
  by_cases c5 : j < 315500000
  · exact w1_6 j (by omega) c5
  by_cases c6 : j < 316000000
  · exact w1_7 j (by omega) c6
  by_cases c7 : j < 316500000
  · exact w1_8 j (by omega) c7
  by_cases c8 : j < 317000000
  · exact w1_9 j (by omega) c8
  by_cases c9 : j < 317500000
  · exact w1_10 j (by omega) c9
  by_cases c10 : j < 317858307
  · exact w1_11 j (by omega) c10
  by_cases c11 : j < 317858308
  · obtain rfl : j = 317858307 := by omega
    exact resid_317858307
  by_cases c12 : j < 318000000
  · exact w1_12 j (by omega) c12
  by_cases c13 : j < 318147687
  · exact w1_13 j (by omega) c13
  by_cases c14 : j < 318147688
  · obtain rfl : j = 318147687 := by omega
    exact resid_318147687
  by_cases c15 : j < 318500000
  · exact w1_14 j (by omega) c15
  by_cases c16 : j < 319000000
  · exact w1_15 j (by omega) c16
  by_cases c17 : j < 319500000
  · exact w1_16 j (by omega) c17
  by_cases c18 : j < 320000000
  · exact w1_17 j (by omega) c18
  by_cases c19 : j < 320500000
  · exact w1_18 j (by omega) c19
  by_cases c20 : j < 321000000
  · exact w1_19 j (by omega) c20
  by_cases c21 : j < 321500000
  · exact w1_20 j (by omega) c21
  by_cases c22 : j < 322000000
  · exact w1_21 j (by omega) c22
  by_cases c23 : j < 322046337
  · exact w1_22 j (by omega) c23
  by_cases c24 : j < 322046338
  · obtain rfl : j = 322046337 := by omega
    exact resid_322046337
  by_cases c25 : j < 322131927
  · exact w1_23 j (by omega) c25
  by_cases c26 : j < 322131928
  · obtain rfl : j = 322131927 := by omega
    exact resid_322131927
  by_cases c27 : j < 322500000
  · exact w1_24 j (by omega) c27
  · exact w1_25 j (by omega) hhi

/-- LEAF: Step 2 of 6 of the index cut, the indices 323000000 up to 333500000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part2 :
    ∀ j : ℕ, 323000000 ≤ j → j < 333500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  by_cases c0 : j < 323500000
  · exact w2_1 j (by omega) c0
  by_cases c1 : j < 323601443
  · exact w2_2 j (by omega) c1
  by_cases c2 : j < 323601444
  · obtain rfl : j = 323601443 := by omega
    exact resid_323601443
  by_cases c3 : j < 324000000
  · exact w2_3 j (by omega) c3
  by_cases c4 : j < 324286212
  · exact w2_4 j (by omega) c4
  by_cases c5 : j < 324286213
  · obtain rfl : j = 324286212 := by omega
    exact resid_324286212
  by_cases c6 : j < 324500000
  · exact w2_5 j (by omega) c6
  by_cases c7 : j < 324673236
  · exact w2_6 j (by omega) c7
  by_cases c8 : j < 324673237
  · obtain rfl : j = 324673236 := by omega
    exact resid_324673236
  by_cases c9 : j < 325000000
  · exact w2_7 j (by omega) c9
  by_cases c10 : j < 325481874
  · exact w2_8 j (by omega) c10
  by_cases c11 : j < 325481875
  · obtain rfl : j = 325481874 := by omega
    exact resid_325481874
  by_cases c12 : j < 325500000
  · exact w2_9 j (by omega) c12
  by_cases c13 : j < 326000000
  · exact w2_10 j (by omega) c13
  by_cases c14 : j < 326500000
  · exact w2_11 j (by omega) c14
  by_cases c15 : j < 327000000
  · exact w2_12 j (by omega) c15
  by_cases c16 : j < 327500000
  · exact w2_13 j (by omega) c16
  by_cases c17 : j < 328000000
  · exact w2_14 j (by omega) c17
  by_cases c18 : j < 328500000
  · exact w2_15 j (by omega) c18
  by_cases c19 : j < 329000000
  · exact w2_16 j (by omega) c19
  by_cases c20 : j < 329314437
  · exact w2_17 j (by omega) c20
  by_cases c21 : j < 329314438
  · obtain rfl : j = 329314437 := by omega
    exact resid_329314437
  by_cases c22 : j < 329500000
  · exact w2_18 j (by omega) c22
  by_cases c23 : j < 330000000
  · exact w2_19 j (by omega) c23
  by_cases c24 : j < 330500000
  · exact w2_20 j (by omega) c24
  by_cases c25 : j < 331000000
  · exact w2_21 j (by omega) c25
  by_cases c26 : j < 331500000
  · exact w2_22 j (by omega) c26
  by_cases c27 : j < 332000000
  · exact w2_23 j (by omega) c27
  by_cases c28 : j < 332500000
  · exact w2_24 j (by omega) c28
  by_cases c29 : j < 332589453
  · exact w2_25 j (by omega) c29
  by_cases c30 : j < 332589454
  · obtain rfl : j = 332589453 := by omega
    exact resid_332589453
  by_cases c31 : j < 333000000
  · exact w2_26 j (by omega) c31
  · exact w2_27 j (by omega) hhi

/-- LEAF: Step 3 of 6 of the index cut, the indices 333500000 up to 344000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part3 :
    ∀ j : ℕ, 333500000 ≤ j → j < 344000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  by_cases c0 : j < 333524694
  · exact w3_1 j (by omega) c0
  by_cases c1 : j < 333524695
  · obtain rfl : j = 333524694 := by omega
    exact resid_333524694
  by_cases c2 : j < 334000000
  · exact w3_2 j (by omega) c2
  by_cases c3 : j < 334500000
  · exact w3_3 j (by omega) c3
  by_cases c4 : j < 335000000
  · exact w3_4 j (by omega) c4
  by_cases c5 : j < 335500000
  · exact w3_5 j (by omega) c5
  by_cases c6 : j < 336000000
  · exact w3_6 j (by omega) c6
  by_cases c7 : j < 336500000
  · exact w3_7 j (by omega) c7
  by_cases c8 : j < 337000000
  · exact w3_8 j (by omega) c8
  by_cases c9 : j < 337088049
  · exact w3_9 j (by omega) c9
  by_cases c10 : j < 337088050
  · obtain rfl : j = 337088049 := by omega
    exact resid_337088049
  by_cases c11 : j < 337500000
  · exact w3_10 j (by omega) c11
  by_cases c12 : j < 338000000
  · exact w3_11 j (by omega) c12
  by_cases c13 : j < 338500000
  · exact w3_12 j (by omega) c13
  by_cases c14 : j < 338766068
  · exact w3_13 j (by omega) c14
  by_cases c15 : j < 338766069
  · obtain rfl : j = 338766068 := by omega
    exact resid_338766068
  by_cases c16 : j < 339000000
  · exact w3_14 j (by omega) c16
  by_cases c17 : j < 339500000
  · exact w3_15 j (by omega) c17
  by_cases c18 : j < 339540369
  · exact w3_16 j (by omega) c18
  by_cases c19 : j < 339540370
  · obtain rfl : j = 339540369 := by omega
    exact resid_339540369
  by_cases c20 : j < 340000000
  · exact w3_17 j (by omega) c20
  by_cases c21 : j < 340500000
  · exact w3_18 j (by omega) c21
  by_cases c22 : j < 341000000
  · exact w3_19 j (by omega) c22
  by_cases c23 : j < 341484933
  · exact w3_20 j (by omega) c23
  by_cases c24 : j < 341484934
  · obtain rfl : j = 341484933 := by omega
    exact resid_341484933
  by_cases c25 : j < 341500000
  · exact w3_21 j (by omega) c25
  by_cases c26 : j < 342000000
  · exact w3_22 j (by omega) c26
  by_cases c27 : j < 342500000
  · exact w3_23 j (by omega) c27
  by_cases c28 : j < 343000000
  · exact w3_24 j (by omega) c28
  by_cases c29 : j < 343500000
  · exact w3_25 j (by omega) c29
  · exact w3_26 j (by omega) hhi

/-- LEAF: Step 4 of 6 of the index cut, the indices 344000000 up to 354500000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part4 :
    ∀ j : ℕ, 344000000 ≤ j → j < 354500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  by_cases c0 : j < 344500000
  · exact w4_1 j (by omega) c0
  by_cases c1 : j < 345000000
  · exact w4_2 j (by omega) c1
  by_cases c2 : j < 345500000
  · exact w4_3 j (by omega) c2
  by_cases c3 : j < 346000000
  · exact w4_4 j (by omega) c3
  by_cases c4 : j < 346500000
  · exact w4_5 j (by omega) c4
  by_cases c5 : j < 346627713
  · exact w4_6 j (by omega) c5
  by_cases c6 : j < 346627714
  · obtain rfl : j = 346627713 := by omega
    exact resid_346627713
  by_cases c7 : j < 347000000
  · exact w4_7 j (by omega) c7
  by_cases c8 : j < 347500000
  · exact w4_8 j (by omega) c8
  by_cases c9 : j < 348000000
  · exact w4_9 j (by omega) c9
  by_cases c10 : j < 348500000
  · exact w4_10 j (by omega) c10
  by_cases c11 : j < 349000000
  · exact w4_11 j (by omega) c11
  by_cases c12 : j < 349455987
  · exact w4_12 j (by omega) c12
  by_cases c13 : j < 349455988
  · obtain rfl : j = 349455987 := by omega
    exact resid_349455987
  by_cases c14 : j < 349500000
  · exact w4_13 j (by omega) c14
  by_cases c15 : j < 350000000
  · exact w4_14 j (by omega) c15
  by_cases c16 : j < 350500000
  · exact w4_15 j (by omega) c16
  by_cases c17 : j < 351000000
  · exact w4_16 j (by omega) c17
  by_cases c18 : j < 351500000
  · exact w4_17 j (by omega) c18
  by_cases c19 : j < 352000000
  · exact w4_18 j (by omega) c19
  by_cases c20 : j < 352146954
  · exact w4_19 j (by omega) c20
  by_cases c21 : j < 352146955
  · obtain rfl : j = 352146954 := by omega
    exact resid_352146954
  by_cases c22 : j < 352500000
  · exact w4_20 j (by omega) c22
  by_cases c23 : j < 353000000
  · exact w4_21 j (by omega) c23
  by_cases c24 : j < 353500000
  · exact w4_22 j (by omega) c24
  by_cases c25 : j < 354000000
  · exact w4_23 j (by omega) c25
  · exact w4_24 j (by omega) hhi

/-- LEAF: Step 5 of 6 of the index cut, the indices 354500000 up to 365000000. Some
offset of the fixed list makes 2 * j + a prime. Strictly weaker than the target: one
subrange only, and no size bound on the offset. -/
theorem cover_upper_part5 :
    ∀ j : ℕ, 354500000 ≤ j → j < 365000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  by_cases c0 : j < 355000000
  · exact w5_1 j (by omega) c0
  by_cases c1 : j < 355500000
  · exact w5_2 j (by omega) c1
  by_cases c2 : j < 356000000
  · exact w5_3 j (by omega) c2
  by_cases c3 : j < 356500000
  · exact w5_4 j (by omega) c3
  by_cases c4 : j < 357000000
  · exact w5_5 j (by omega) c4
  by_cases c5 : j < 357500000
  · exact w5_6 j (by omega) c5
  by_cases c6 : j < 358000000
  · exact w5_7 j (by omega) c6
  by_cases c7 : j < 358500000
  · exact w5_8 j (by omega) c7
  by_cases c8 : j < 359000000
  · exact w5_9 j (by omega) c8
  by_cases c9 : j < 359500000
  · exact w5_10 j (by omega) c9
  by_cases c10 : j < 359588094
  · exact w5_11 j (by omega) c10
  by_cases c11 : j < 359588095
  · obtain rfl : j = 359588094 := by omega
    exact resid_359588094
  by_cases c12 : j < 360000000
  · exact w5_12 j (by omega) c12
  by_cases c13 : j < 360500000
  · exact w5_13 j (by omega) c13
  by_cases c14 : j < 360864942
  · exact w5_14 j (by omega) c14
  by_cases c15 : j < 360864943
  · obtain rfl : j = 360864942 := by omega
    exact resid_360864942
  by_cases c16 : j < 361000000
  · exact w5_15 j (by omega) c16
  by_cases c17 : j < 361500000
  · exact w5_16 j (by omega) c17
  by_cases c18 : j < 361509321
  · exact w5_17 j (by omega) c18
  by_cases c19 : j < 361509322
  · obtain rfl : j = 361509321 := by omega
    exact resid_361509321
  by_cases c20 : j < 362000000
  · exact w5_18 j (by omega) c20
  by_cases c21 : j < 362044779
  · exact w5_19 j (by omega) c21
  by_cases c22 : j < 362044780
  · obtain rfl : j = 362044779 := by omega
    exact resid_362044779
  by_cases c23 : j < 362500000
  · exact w5_20 j (by omega) c23
  by_cases c24 : j < 363000000
  · exact w5_21 j (by omega) c24
  by_cases c25 : j < 363307872
  · exact w5_22 j (by omega) c25
  by_cases c26 : j < 363307873
  · obtain rfl : j = 363307872 := by omega
    exact resid_363307872
  by_cases c27 : j < 363500000
  · exact w5_23 j (by omega) c27
  by_cases c28 : j < 363929721
  · exact w5_24 j (by omega) c28
  by_cases c29 : j < 363929722
  · obtain rfl : j = 363929721 := by omega
    exact resid_363929721
  by_cases c30 : j < 364000000
  · exact w5_25 j (by omega) c30
  by_cases c31 : j < 364500000
  · exact w5_26 j (by omega) c31
  · exact w5_27 j (by omega) hhi

/-- LEAF: Step 6 of 6 of the index cut, the last indices 365000000 up to 375000000; this
one is shorter than ten and a half million indices because the target range stops at
375000000. Some offset of the fixed list makes 2 * j + a prime. Strictly weaker than the
target: one subrange only, and no size bound on the offset. -/
theorem cover_upper_part6 :
    ∀ j : ℕ, 365000000 ≤ j → j < 375000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hhi
  by_cases c0 : j < 365500000
  · exact w6_1 j (by omega) c0
  by_cases c1 : j < 366000000
  · exact w6_2 j (by omega) c1
  by_cases c2 : j < 366500000
  · exact w6_3 j (by omega) c2
  by_cases c3 : j < 367000000
  · exact w6_4 j (by omega) c3
  by_cases c4 : j < 367500000
  · exact w6_5 j (by omega) c4
  by_cases c5 : j < 368000000
  · exact w6_6 j (by omega) c5
  by_cases c6 : j < 368052738
  · exact w6_7 j (by omega) c6
  by_cases c7 : j < 368052739
  · obtain rfl : j = 368052738 := by omega
    exact resid_368052738
  by_cases c8 : j < 368500000
  · exact w6_8 j (by omega) c8
  by_cases c9 : j < 368706636
  · exact w6_9 j (by omega) c9
  by_cases c10 : j < 368706637
  · obtain rfl : j = 368706636 := by omega
    exact resid_368706636
  by_cases c11 : j < 368896868
  · exact w6_10 j (by omega) c11
  by_cases c12 : j < 368896869
  · obtain rfl : j = 368896868 := by omega
    exact resid_368896868
  by_cases c13 : j < 369000000
  · exact w6_11 j (by omega) c13
  by_cases c14 : j < 369500000
  · exact w6_12 j (by omega) c14
  by_cases c15 : j < 370000000
  · exact w6_13 j (by omega) c15
  by_cases c16 : j < 370221216
  · exact w6_14 j (by omega) c16
  by_cases c17 : j < 370221217
  · obtain rfl : j = 370221216 := by omega
    exact resid_370221216
  by_cases c18 : j < 370500000
  · exact w6_15 j (by omega) c18
  by_cases c19 : j < 371000000
  · exact w6_16 j (by omega) c19
  by_cases c20 : j < 371500000
  · exact w6_17 j (by omega) c20
  by_cases c21 : j < 372000000
  · exact w6_18 j (by omega) c21
  by_cases c22 : j < 372500000
  · exact w6_19 j (by omega) c22
  by_cases c23 : j < 373000000
  · exact w6_20 j (by omega) c23
  by_cases c24 : j < 373500000
  · exact w6_21 j (by omega) c24
  by_cases c25 : j < 373647957
  · exact w6_22 j (by omega) c25
  by_cases c26 : j < 373647958
  · obtain rfl : j = 373647957 := by omega
    exact resid_373647957
  by_cases c27 : j < 374000000
  · exact w6_23 j (by omega) c27
  by_cases c28 : j < 374500000
  · exact w6_24 j (by omega) c28
  by_cases c29 : j < 374732334
  · exact w6_25 j (by omega) c29
  by_cases c30 : j < 374732335
  · obtain rfl : j = 374732334 := by omega
    exact resid_374732334
  by_cases c31 : j < 374917002
  · exact w6_26 j (by omega) c31
  by_cases c32 : j < 374917003
  · obtain rfl : j = 374917002 := by omega
    exact resid_374917002
  · exact w6_27 j (by omega) hhi

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
