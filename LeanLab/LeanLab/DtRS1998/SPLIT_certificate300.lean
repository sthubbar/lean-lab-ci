/-
Split of certificate300 in LeanLab.DtRS1998.Decomp270c.

The row at 10 ^ 300 asks for at most 227 primes whose shifts land on a prime at
every even offset through 10 ^ 9.  Written with the shift set explicit, the task
separates into one primality job on the 213 large numbers 10 ^ 300 - a, and four
coverage jobs on small numbers, one per block of the offset range.  Both jobs are
strictly easier than the row: the primality job never checks coverage, and a
coverage block checks only its own quarter of the offsets, with no number larger
than 10 ^ 9 + 4000000 in sight.

The split set is 213 offsets, each with 10 ^ 300 - a prime and every even offset
j through 500000000 met by some a at which 2 * j + a is prime.  The primality leaf below is open;
the two coverage blocks are kernel-checked here and the assembly is complete.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270c
import LeanLab.DtRS1998.Decomp455k

namespace LeanLab.DtRS1998.SPLITcertificate300

open LeanLab Task71.Paper Decomp270a
open LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Bookkeeping: the small number left after the shift is 2 * j + a. -/
private lemma sub_sub (B a j : ℕ) (h : a ≤ B) : B + 2 * j - (B - a) = 2 * j + a := by
  omega

/-- Bookkeeping: the shifted entry never exceeds B + 2 * j. -/
private lemma sub_le (B a j : ℕ) : B - a ≤ B + 2 * j := by
  omega

/-- LEAF. Step 1 of 5, the primality job.  For each of the 213 listed offsets a,
the large number 10 ^ 300 - a is prime.  This leaf asks nothing about coverage,
so it is the certificate work on the 213 large numbers alone. -/
theorem prime_offsets :
    ∀ a ∈ ([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ), (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. Step 2 of 5, the coverage job on the lowest block.  For every
j < 125000000 some listed offset a, itself below 10 ^ 300, makes the small number
2 * j + a prime.  Only small numbers occur here and only the first quarter of the
offset range. -/
theorem cover_block1 :
    ∀ j : ℕ, j < 125000000 →
      ∃ a ∈ ([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ), a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  exact _root_.LeanLab.DtRS1998.Decomp455b.cover_block1

/-- LEAF. Step 3 of 5, the coverage job on the second block.  For every j with
125000000 ≤ j < 250000000 some listed offset a below 10 ^ 300 makes 2 * j + a
prime. -/
theorem cover_block2 :
    ∀ j : ℕ, 125000000 ≤ j → j < 250000000 →
      ∃ a ∈ ([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ), a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  exact _root_.LeanLab.DtRS1998.Decomp455c.cover_block2

/-! ### Kernel-checked window certificates for the third and fourth blocks

Each of the two blocks (125 million indices) is covered by shifted window sieves
`Certificate294.offset_window`, one window per 500000 indices over the first 200
offsets; an index that none of those 200 offsets reaches is closed by its own
one-bit primality certificate (`Nat.minFac`).  Every declaration below is a kernel
check: nothing is assumed and no statement is restated.  -/

private theorem resid_256264271 : ∃ a ∈ offsets, (2 * 256264271 + a).Prime := by
  refine ⟨421491, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_263513682 : ∃ a ∈ offsets, (2 * 263513682 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_265573404 : ∃ a ∈ offsets, (2 * 265573404 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_269338358 : ∃ a ∈ offsets, (2 * 269338358 + a).Prime := by
  refine ⟨158457, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_271560938 : ∃ a ∈ offsets, (2 * 271560938 + a).Prime := by
  refine ⟨291297, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_271861224 : ∃ a ∈ offsets, (2 * 271861224 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_272175399 : ∃ a ∈ offsets, (2 * 272175399 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_272354738 : ∃ a ∈ offsets, (2 * 272354738 + a).Prime := by
  refine ⟨158457, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_280647912 : ∃ a ∈ offsets, (2 * 280647912 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_281971479 : ∃ a ∈ offsets, (2 * 281971479 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_284199837 : ∃ a ∈ offsets, (2 * 284199837 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_293187012 : ∃ a ∈ offsets, (2 * 293187012 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_293495298 : ∃ a ∈ offsets, (2 * 293495298 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_293799606 : ∃ a ∈ offsets, (2 * 293799606 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_297598662 : ∃ a ∈ offsets, (2 * 297598662 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_306886241 : ∃ a ∈ offsets, (2 * 306886241 + a).Prime := by
  refine ⟨158457, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_308391528 : ∃ a ∈ offsets, (2 * 308391528 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_309928518 : ∃ a ∈ offsets, (2 * 309928518 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_310067844 : ∃ a ∈ offsets, (2 * 310067844 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_310559547 : ∃ a ∈ offsets, (2 * 310559547 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_317858307 : ∃ a ∈ offsets, (2 * 317858307 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_318147687 : ∃ a ∈ offsets, (2 * 318147687 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_322046337 : ∃ a ∈ offsets, (2 * 322046337 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_322131927 : ∃ a ∈ offsets, (2 * 322131927 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_323601443 : ∃ a ∈ offsets, (2 * 323601443 + a).Prime := by
  refine ⟨2240913, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_324286212 : ∃ a ∈ offsets, (2 * 324286212 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_324673236 : ∃ a ∈ offsets, (2 * 324673236 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_325481874 : ∃ a ∈ offsets, (2 * 325481874 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_329314437 : ∃ a ∈ offsets, (2 * 329314437 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_332589453 : ∃ a ∈ offsets, (2 * 332589453 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_333524694 : ∃ a ∈ offsets, (2 * 333524694 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_337088049 : ∃ a ∈ offsets, (2 * 337088049 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_338766068 : ∃ a ∈ offsets, (2 * 338766068 + a).Prime := by
  refine ⟨2240913, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_339540369 : ∃ a ∈ offsets, (2 * 339540369 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_341484933 : ∃ a ∈ offsets, (2 * 341484933 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_346627713 : ∃ a ∈ offsets, (2 * 346627713 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_349455987 : ∃ a ∈ offsets, (2 * 349455987 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_352146954 : ∃ a ∈ offsets, (2 * 352146954 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_359588094 : ∃ a ∈ offsets, (2 * 359588094 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_360864942 : ∃ a ∈ offsets, (2 * 360864942 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_361509321 : ∃ a ∈ offsets, (2 * 361509321 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_362044779 : ∃ a ∈ offsets, (2 * 362044779 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_363307872 : ∃ a ∈ offsets, (2 * 363307872 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_363929721 : ∃ a ∈ offsets, (2 * 363929721 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_368052738 : ∃ a ∈ offsets, (2 * 368052738 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_368706636 : ∃ a ∈ offsets, (2 * 368706636 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_368896868 : ∃ a ∈ offsets, (2 * 368896868 + a).Prime := by
  refine ⟨505017, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_370221216 : ∃ a ∈ offsets, (2 * 370221216 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_373647957 : ∃ a ∈ offsets, (2 * 373647957 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_374732334 : ∃ a ∈ offsets, (2 * 374732334 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_374917002 : ∃ a ∈ offsets, (2 * 374917002 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem b3w0 : ∀ j : ℕ, 250000000 ≤ j → j < 250500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 500000000) (x1 := 500999998) (lo := 500000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w1 : ∀ j : ℕ, 250500000 ≤ j → j < 251000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 501000000) (x1 := 501999998) (lo := 501000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w2 : ∀ j : ℕ, 251000000 ≤ j → j < 251500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 502000000) (x1 := 502999998) (lo := 502000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w3 : ∀ j : ℕ, 251500000 ≤ j → j < 252000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 503000000) (x1 := 503999998) (lo := 503000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w4 : ∀ j : ℕ, 252000000 ≤ j → j < 252500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 504000000) (x1 := 504999998) (lo := 504000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w5 : ∀ j : ℕ, 252500000 ≤ j → j < 253000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 505000000) (x1 := 505999998) (lo := 505000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w6 : ∀ j : ℕ, 253000000 ≤ j → j < 253500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 506000000) (x1 := 506999998) (lo := 506000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w7 : ∀ j : ℕ, 253500000 ≤ j → j < 254000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 507000000) (x1 := 507999998) (lo := 507000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w8 : ∀ j : ℕ, 254000000 ≤ j → j < 254500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 508000000) (x1 := 508999998) (lo := 508000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w9 : ∀ j : ℕ, 254500000 ≤ j → j < 255000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 509000000) (x1 := 509999998) (lo := 509000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w10 : ∀ j : ℕ, 255000000 ≤ j → j < 255500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 510000000) (x1 := 510999998) (lo := 510000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w11 : ∀ j : ℕ, 255500000 ≤ j → j < 256000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 511000000) (x1 := 511999998) (lo := 511000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w12 : ∀ j : ℕ, 256000000 ≤ j → j < 256264271 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512000000) (x1 := 512528540) (lo := 512000069) (W := 661863)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w13 : ∀ j : ℕ, 256264272 ≤ j → j < 256764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512528544) (x1 := 513528542) (lo := 512528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w14 : ∀ j : ℕ, 256764272 ≤ j → j < 257264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 513528544) (x1 := 514528542) (lo := 513528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w15 : ∀ j : ℕ, 257264272 ≤ j → j < 257764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 514528544) (x1 := 515528542) (lo := 514528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w16 : ∀ j : ℕ, 257764272 ≤ j → j < 258264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 515528544) (x1 := 516528542) (lo := 515528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w17 : ∀ j : ℕ, 258264272 ≤ j → j < 258764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 516528544) (x1 := 517528542) (lo := 516528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w18 : ∀ j : ℕ, 258764272 ≤ j → j < 259264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 517528544) (x1 := 518528542) (lo := 517528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w19 : ∀ j : ℕ, 259264272 ≤ j → j < 259764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 518528544) (x1 := 519528542) (lo := 518528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w20 : ∀ j : ℕ, 259764272 ≤ j → j < 260264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 519528544) (x1 := 520528542) (lo := 519528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w21 : ∀ j : ℕ, 260264272 ≤ j → j < 260764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 520528544) (x1 := 521528542) (lo := 520528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w22 : ∀ j : ℕ, 260764272 ≤ j → j < 261264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 521528544) (x1 := 522528542) (lo := 521528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w23 : ∀ j : ℕ, 261264272 ≤ j → j < 261764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 522528544) (x1 := 523528542) (lo := 522528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w24 : ∀ j : ℕ, 261764272 ≤ j → j < 262264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 523528544) (x1 := 524528542) (lo := 523528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w25 : ∀ j : ℕ, 262264272 ≤ j → j < 262764272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 524528544) (x1 := 525528542) (lo := 524528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w26 : ∀ j : ℕ, 262764272 ≤ j → j < 263264272 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 525528544) (x1 := 526528542) (lo := 525528613) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w27 : ∀ j : ℕ, 263264272 ≤ j → j < 263513682 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 526528544) (x1 := 527027362) (lo := 526528613) (W := 632141)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w28 : ∀ j : ℕ, 263513683 ≤ j → j < 264013683 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 527027366) (x1 := 528027364) (lo := 527027435) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w29 : ∀ j : ℕ, 264013683 ≤ j → j < 264513683 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 528027366) (x1 := 529027364) (lo := 528027435) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w30 : ∀ j : ℕ, 264513683 ≤ j → j < 265013683 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 529027366) (x1 := 530027364) (lo := 529027435) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w31 : ∀ j : ℕ, 265013683 ≤ j → j < 265513683 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 530027366) (x1 := 531027364) (lo := 530027435) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w32 : ∀ j : ℕ, 265513683 ≤ j → j < 265573404 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531027366) (x1 := 531146806) (lo := 531027435) (W := 252763)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w33 : ∀ j : ℕ, 265573405 ≤ j → j < 266073405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531146810) (x1 := 532146808) (lo := 531146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w34 : ∀ j : ℕ, 266073405 ≤ j → j < 266573405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 532146810) (x1 := 533146808) (lo := 532146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w35 : ∀ j : ℕ, 266573405 ≤ j → j < 267073405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 533146810) (x1 := 534146808) (lo := 533146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w36 : ∀ j : ℕ, 267073405 ≤ j → j < 267573405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 534146810) (x1 := 535146808) (lo := 534146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w37 : ∀ j : ℕ, 267573405 ≤ j → j < 268073405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 535146810) (x1 := 536146808) (lo := 535146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w38 : ∀ j : ℕ, 268073405 ≤ j → j < 268573405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 536146810) (x1 := 537146808) (lo := 536146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w39 : ∀ j : ℕ, 268573405 ≤ j → j < 269073405 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 537146810) (x1 := 538146808) (lo := 537146879) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w40 : ∀ j : ℕ, 269073405 ≤ j → j < 269338358 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538146810) (x1 := 538676714) (lo := 538146879) (W := 663227)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w41 : ∀ j : ℕ, 269338359 ≤ j → j < 269838359 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538676718) (x1 := 539676716) (lo := 538676787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w42 : ∀ j : ℕ, 269838359 ≤ j → j < 270338359 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 539676718) (x1 := 540676716) (lo := 539676787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w43 : ∀ j : ℕ, 270338359 ≤ j → j < 270838359 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 540676718) (x1 := 541676716) (lo := 540676787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w44 : ∀ j : ℕ, 270838359 ≤ j → j < 271338359 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 541676718) (x1 := 542676716) (lo := 541676787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w45 : ∀ j : ℕ, 271338359 ≤ j → j < 271560938 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 542676718) (x1 := 543121874) (lo := 542676787) (W := 578479)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w46 : ∀ j : ℕ, 271560939 ≤ j → j < 271861224 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543121878) (x1 := 543722446) (lo := 543121947) (W := 733891)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w47 : ∀ j : ℕ, 271861225 ≤ j → j < 272175399 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543722450) (x1 := 544350796) (lo := 543722519) (W := 761669)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w48 : ∀ j : ℕ, 272175400 ≤ j → j < 272354738 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544350800) (x1 := 544709474) (lo := 544350869) (W := 491997)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w49 : ∀ j : ℕ, 272354739 ≤ j → j < 272854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544709478) (x1 := 545709476) (lo := 544709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w50 : ∀ j : ℕ, 272854739 ≤ j → j < 273354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 545709478) (x1 := 546709476) (lo := 545709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w51 : ∀ j : ℕ, 273354739 ≤ j → j < 273854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 546709478) (x1 := 547709476) (lo := 546709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w52 : ∀ j : ℕ, 273854739 ≤ j → j < 274354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 547709478) (x1 := 548709476) (lo := 547709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w53 : ∀ j : ℕ, 274354739 ≤ j → j < 274854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 548709478) (x1 := 549709476) (lo := 548709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w54 : ∀ j : ℕ, 274854739 ≤ j → j < 275354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 549709478) (x1 := 550709476) (lo := 549709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w55 : ∀ j : ℕ, 275354739 ≤ j → j < 275854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 550709478) (x1 := 551709476) (lo := 550709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w56 : ∀ j : ℕ, 275854739 ≤ j → j < 276354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 551709478) (x1 := 552709476) (lo := 551709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w57 : ∀ j : ℕ, 276354739 ≤ j → j < 276854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 552709478) (x1 := 553709476) (lo := 552709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w58 : ∀ j : ℕ, 276854739 ≤ j → j < 277354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 553709478) (x1 := 554709476) (lo := 553709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w59 : ∀ j : ℕ, 277354739 ≤ j → j < 277854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 554709478) (x1 := 555709476) (lo := 554709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w60 : ∀ j : ℕ, 277854739 ≤ j → j < 278354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 555709478) (x1 := 556709476) (lo := 555709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w61 : ∀ j : ℕ, 278354739 ≤ j → j < 278854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 556709478) (x1 := 557709476) (lo := 556709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w62 : ∀ j : ℕ, 278854739 ≤ j → j < 279354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 557709478) (x1 := 558709476) (lo := 557709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w63 : ∀ j : ℕ, 279354739 ≤ j → j < 279854739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 558709478) (x1 := 559709476) (lo := 558709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w64 : ∀ j : ℕ, 279854739 ≤ j → j < 280354739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 559709478) (x1 := 560709476) (lo := 559709547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w65 : ∀ j : ℕ, 280354739 ≤ j → j < 280647912 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 560709478) (x1 := 561295822) (lo := 560709547) (W := 719667)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w66 : ∀ j : ℕ, 280647913 ≤ j → j < 281147913 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 561295826) (x1 := 562295824) (lo := 561295895) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w67 : ∀ j : ℕ, 281147913 ≤ j → j < 281647913 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 562295826) (x1 := 563295824) (lo := 562295895) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w68 : ∀ j : ℕ, 281647913 ≤ j → j < 281971479 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563295826) (x1 := 563942956) (lo := 563295895) (W := 780453)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w69 : ∀ j : ℕ, 281971480 ≤ j → j < 282471480 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563942960) (x1 := 564942958) (lo := 563943029) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w70 : ∀ j : ℕ, 282471480 ≤ j → j < 282971480 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 564942960) (x1 := 565942958) (lo := 564943029) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w71 : ∀ j : ℕ, 282971480 ≤ j → j < 283471480 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 565942960) (x1 := 566942958) (lo := 565943029) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w72 : ∀ j : ℕ, 283471480 ≤ j → j < 283971480 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 566942960) (x1 := 567942958) (lo := 566943029) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w73 : ∀ j : ℕ, 283971480 ≤ j → j < 284199837 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 567942960) (x1 := 568399672) (lo := 567943029) (W := 590035)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w74 : ∀ j : ℕ, 284199838 ≤ j → j < 284699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568399676) (x1 := 569399674) (lo := 568399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w75 : ∀ j : ℕ, 284699838 ≤ j → j < 285199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 569399676) (x1 := 570399674) (lo := 569399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w76 : ∀ j : ℕ, 285199838 ≤ j → j < 285699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 570399676) (x1 := 571399674) (lo := 570399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w77 : ∀ j : ℕ, 285699838 ≤ j → j < 286199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 571399676) (x1 := 572399674) (lo := 571399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w78 : ∀ j : ℕ, 286199838 ≤ j → j < 286699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 572399676) (x1 := 573399674) (lo := 572399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w79 : ∀ j : ℕ, 286699838 ≤ j → j < 287199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 573399676) (x1 := 574399674) (lo := 573399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w80 : ∀ j : ℕ, 287199838 ≤ j → j < 287699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 574399676) (x1 := 575399674) (lo := 574399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w81 : ∀ j : ℕ, 287699838 ≤ j → j < 288199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 575399676) (x1 := 576399674) (lo := 575399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w82 : ∀ j : ℕ, 288199838 ≤ j → j < 288699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 576399676) (x1 := 577399674) (lo := 576399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w83 : ∀ j : ℕ, 288699838 ≤ j → j < 289199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 577399676) (x1 := 578399674) (lo := 577399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w84 : ∀ j : ℕ, 289199838 ≤ j → j < 289699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 578399676) (x1 := 579399674) (lo := 578399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w85 : ∀ j : ℕ, 289699838 ≤ j → j < 290199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 579399676) (x1 := 580399674) (lo := 579399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w86 : ∀ j : ℕ, 290199838 ≤ j → j < 290699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 580399676) (x1 := 581399674) (lo := 580399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w87 : ∀ j : ℕ, 290699838 ≤ j → j < 291199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 581399676) (x1 := 582399674) (lo := 581399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w88 : ∀ j : ℕ, 291199838 ≤ j → j < 291699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 582399676) (x1 := 583399674) (lo := 582399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w89 : ∀ j : ℕ, 291699838 ≤ j → j < 292199838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 583399676) (x1 := 584399674) (lo := 583399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w90 : ∀ j : ℕ, 292199838 ≤ j → j < 292699838 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 584399676) (x1 := 585399674) (lo := 584399745) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w91 : ∀ j : ℕ, 292699838 ≤ j → j < 293187012 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 585399676) (x1 := 586374022) (lo := 585399745) (W := 1107669)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w92 : ∀ j : ℕ, 293187013 ≤ j → j < 293495298 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586374026) (x1 := 586990594) (lo := 586374095) (W := 749891)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w93 : ∀ j : ℕ, 293495299 ≤ j → j < 293799606 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586990598) (x1 := 587599210) (lo := 586990667) (W := 741935)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w94 : ∀ j : ℕ, 293799607 ≤ j → j < 294299607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 587599214) (x1 := 588599212) (lo := 587599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w95 : ∀ j : ℕ, 294299607 ≤ j → j < 294799607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 588599214) (x1 := 589599212) (lo := 588599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w96 : ∀ j : ℕ, 294799607 ≤ j → j < 295299607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 589599214) (x1 := 590599212) (lo := 589599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w97 : ∀ j : ℕ, 295299607 ≤ j → j < 295799607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 590599214) (x1 := 591599212) (lo := 590599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w98 : ∀ j : ℕ, 295799607 ≤ j → j < 296299607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 591599214) (x1 := 592599212) (lo := 591599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w99 : ∀ j : ℕ, 296299607 ≤ j → j < 296799607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592599214) (x1 := 593599212) (lo := 592599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w100 : ∀ j : ℕ, 296799607 ≤ j → j < 297299607 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 593599214) (x1 := 594599212) (lo := 593599283) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w101 : ∀ j : ℕ, 297299607 ≤ j → j < 297598662 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 594599214) (x1 := 595197322) (lo := 594599283) (W := 731431)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w102 : ∀ j : ℕ, 297598663 ≤ j → j < 298098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595197326) (x1 := 596197324) (lo := 595197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w103 : ∀ j : ℕ, 298098663 ≤ j → j < 298598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 596197326) (x1 := 597197324) (lo := 596197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w104 : ∀ j : ℕ, 298598663 ≤ j → j < 299098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 597197326) (x1 := 598197324) (lo := 597197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w105 : ∀ j : ℕ, 299098663 ≤ j → j < 299598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 598197326) (x1 := 599197324) (lo := 598197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w106 : ∀ j : ℕ, 299598663 ≤ j → j < 300098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 599197326) (x1 := 600197324) (lo := 599197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w107 : ∀ j : ℕ, 300098663 ≤ j → j < 300598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600197326) (x1 := 601197324) (lo := 600197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w108 : ∀ j : ℕ, 300598663 ≤ j → j < 301098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 601197326) (x1 := 602197324) (lo := 601197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w109 : ∀ j : ℕ, 301098663 ≤ j → j < 301598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 602197326) (x1 := 603197324) (lo := 602197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w110 : ∀ j : ℕ, 301598663 ≤ j → j < 302098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 603197326) (x1 := 604197324) (lo := 603197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w111 : ∀ j : ℕ, 302098663 ≤ j → j < 302598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 604197326) (x1 := 605197324) (lo := 604197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w112 : ∀ j : ℕ, 302598663 ≤ j → j < 303098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 605197326) (x1 := 606197324) (lo := 605197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w113 : ∀ j : ℕ, 303098663 ≤ j → j < 303598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 606197326) (x1 := 607197324) (lo := 606197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w114 : ∀ j : ℕ, 303598663 ≤ j → j < 304098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 607197326) (x1 := 608197324) (lo := 607197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w115 : ∀ j : ℕ, 304098663 ≤ j → j < 304598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 608197326) (x1 := 609197324) (lo := 608197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w116 : ∀ j : ℕ, 304598663 ≤ j → j < 305098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 609197326) (x1 := 610197324) (lo := 609197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w117 : ∀ j : ℕ, 305098663 ≤ j → j < 305598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 610197326) (x1 := 611197324) (lo := 610197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w118 : ∀ j : ℕ, 305598663 ≤ j → j < 306098663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 611197326) (x1 := 612197324) (lo := 611197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w119 : ∀ j : ℕ, 306098663 ≤ j → j < 306598663 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 612197326) (x1 := 613197324) (lo := 612197395) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w120 : ∀ j : ℕ, 306598663 ≤ j → j < 306886241 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613197326) (x1 := 613772480) (lo := 613197395) (W := 708477)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w121 : ∀ j : ℕ, 306886242 ≤ j → j < 307386242 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613772484) (x1 := 614772482) (lo := 613772553) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w122 : ∀ j : ℕ, 307386242 ≤ j → j < 307886242 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 614772484) (x1 := 615772482) (lo := 614772553) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w123 : ∀ j : ℕ, 307886242 ≤ j → j < 308386242 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 615772484) (x1 := 616772482) (lo := 615772553) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w124 : ∀ j : ℕ, 308386242 ≤ j → j < 308391528 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616772484) (x1 := 616783054) (lo := 616772553) (W := 143893)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w125 : ∀ j : ℕ, 308391529 ≤ j → j < 308891529 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616783058) (x1 := 617783056) (lo := 616783127) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w126 : ∀ j : ℕ, 308891529 ≤ j → j < 309391529 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 617783058) (x1 := 618783056) (lo := 617783127) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w127 : ∀ j : ℕ, 309391529 ≤ j → j < 309891529 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 618783058) (x1 := 619783056) (lo := 618783127) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w128 : ∀ j : ℕ, 309891529 ≤ j → j < 309928518 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619783058) (x1 := 619857034) (lo := 619783127) (W := 207299)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w129 : ∀ j : ℕ, 309928519 ≤ j → j < 310067844 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619857038) (x1 := 620135686) (lo := 619857107) (W := 411971)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w130 : ∀ j : ℕ, 310067845 ≤ j → j < 310559547 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 620135690) (x1 := 621119092) (lo := 620135759) (W := 1116725)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w131 : ∀ j : ℕ, 310559548 ≤ j → j < 311059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 621119096) (x1 := 622119094) (lo := 621119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w132 : ∀ j : ℕ, 311059548 ≤ j → j < 311559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622119096) (x1 := 623119094) (lo := 622119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w133 : ∀ j : ℕ, 311559548 ≤ j → j < 312059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 623119096) (x1 := 624119094) (lo := 623119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w134 : ∀ j : ℕ, 312059548 ≤ j → j < 312559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 624119096) (x1 := 625119094) (lo := 624119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w135 : ∀ j : ℕ, 312559548 ≤ j → j < 313059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 625119096) (x1 := 626119094) (lo := 625119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w136 : ∀ j : ℕ, 313059548 ≤ j → j < 313559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 626119096) (x1 := 627119094) (lo := 626119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w137 : ∀ j : ℕ, 313559548 ≤ j → j < 314059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 627119096) (x1 := 628119094) (lo := 627119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w138 : ∀ j : ℕ, 314059548 ≤ j → j < 314559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 628119096) (x1 := 629119094) (lo := 628119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w139 : ∀ j : ℕ, 314559548 ≤ j → j < 315059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 629119096) (x1 := 630119094) (lo := 629119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w140 : ∀ j : ℕ, 315059548 ≤ j → j < 315559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 630119096) (x1 := 631119094) (lo := 630119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w141 : ∀ j : ℕ, 315559548 ≤ j → j < 316059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 631119096) (x1 := 632119094) (lo := 631119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w142 : ∀ j : ℕ, 316059548 ≤ j → j < 316559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 632119096) (x1 := 633119094) (lo := 632119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w143 : ∀ j : ℕ, 316559548 ≤ j → j < 317059548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 633119096) (x1 := 634119094) (lo := 633119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w144 : ∀ j : ℕ, 317059548 ≤ j → j < 317559548 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 634119096) (x1 := 635119094) (lo := 634119165) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w145 : ∀ j : ℕ, 317559548 ≤ j → j < 317858307 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 635119096) (x1 := 635716612) (lo := 635119165) (W := 730839)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w146 : ∀ j : ℕ, 317858308 ≤ j → j < 318147687 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 635716616) (x1 := 636295372) (lo := 635716685) (W := 712079)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w147 : ∀ j : ℕ, 318147688 ≤ j → j < 318647688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 636295376) (x1 := 637295374) (lo := 636295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w148 : ∀ j : ℕ, 318647688 ≤ j → j < 319147688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 637295376) (x1 := 638295374) (lo := 637295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w149 : ∀ j : ℕ, 319147688 ≤ j → j < 319647688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 638295376) (x1 := 639295374) (lo := 638295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w150 : ∀ j : ℕ, 319647688 ≤ j → j < 320147688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 639295376) (x1 := 640295374) (lo := 639295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w151 : ∀ j : ℕ, 320147688 ≤ j → j < 320647688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 640295376) (x1 := 641295374) (lo := 640295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w152 : ∀ j : ℕ, 320647688 ≤ j → j < 321147688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 641295376) (x1 := 642295374) (lo := 641295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w153 : ∀ j : ℕ, 321147688 ≤ j → j < 321647688 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 642295376) (x1 := 643295374) (lo := 642295445) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w154 : ∀ j : ℕ, 321647688 ≤ j → j < 322046337 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 643295376) (x1 := 644092672) (lo := 643295445) (W := 930619)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w155 : ∀ j : ℕ, 322046338 ≤ j → j < 322131927 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 644092676) (x1 := 644263852) (lo := 644092745) (W := 304499)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w156 : ∀ j : ℕ, 322131928 ≤ j → j < 322631928 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 644263856) (x1 := 645263854) (lo := 644263925) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w157 : ∀ j : ℕ, 322631928 ≤ j → j < 323131928 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 645263856) (x1 := 646263854) (lo := 645263925) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w158 : ∀ j : ℕ, 323131928 ≤ j → j < 323601443 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 646263856) (x1 := 647202884) (lo := 646263925) (W := 1072351)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w159 : ∀ j : ℕ, 323601444 ≤ j → j < 324101444 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 647202888) (x1 := 648202886) (lo := 647202957) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w160 : ∀ j : ℕ, 324101444 ≤ j → j < 324286212 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 648202888) (x1 := 648572422) (lo := 648202957) (W := 502857)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w161 : ∀ j : ℕ, 324286213 ≤ j → j < 324673236 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 648572426) (x1 := 649346470) (lo := 648572495) (W := 907367)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w162 : ∀ j : ℕ, 324673237 ≤ j → j < 325173237 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 649346474) (x1 := 650346472) (lo := 649346543) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w163 : ∀ j : ℕ, 325173237 ≤ j → j < 325481874 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 650346474) (x1 := 650963746) (lo := 650346543) (W := 750595)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w164 : ∀ j : ℕ, 325481875 ≤ j → j < 325981875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 650963750) (x1 := 651963748) (lo := 650963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w165 : ∀ j : ℕ, 325981875 ≤ j → j < 326481875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 651963750) (x1 := 652963748) (lo := 651963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w166 : ∀ j : ℕ, 326481875 ≤ j → j < 326981875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 652963750) (x1 := 653963748) (lo := 652963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w167 : ∀ j : ℕ, 326981875 ≤ j → j < 327481875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 653963750) (x1 := 654963748) (lo := 653963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w168 : ∀ j : ℕ, 327481875 ≤ j → j < 327981875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 654963750) (x1 := 655963748) (lo := 654963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w169 : ∀ j : ℕ, 327981875 ≤ j → j < 328481875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 655963750) (x1 := 656963748) (lo := 655963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w170 : ∀ j : ℕ, 328481875 ≤ j → j < 328981875 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 656963750) (x1 := 657963748) (lo := 656963819) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w171 : ∀ j : ℕ, 328981875 ≤ j → j < 329314437 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 657963750) (x1 := 658628872) (lo := 657963819) (W := 798445)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w172 : ∀ j : ℕ, 329314438 ≤ j → j < 329814438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 658628876) (x1 := 659628874) (lo := 658628945) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w173 : ∀ j : ℕ, 329814438 ≤ j → j < 330314438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 659628876) (x1 := 660628874) (lo := 659628945) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w174 : ∀ j : ℕ, 330314438 ≤ j → j < 330814438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 660628876) (x1 := 661628874) (lo := 660628945) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w175 : ∀ j : ℕ, 330814438 ≤ j → j < 331314438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 661628876) (x1 := 662628874) (lo := 661628945) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w176 : ∀ j : ℕ, 331314438 ≤ j → j < 331814438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 662628876) (x1 := 663628874) (lo := 662628945) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w177 : ∀ j : ℕ, 331814438 ≤ j → j < 332314438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 663628876) (x1 := 664628874) (lo := 663628945) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w178 : ∀ j : ℕ, 332314438 ≤ j → j < 332589453 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 664628876) (x1 := 665178904) (lo := 664628945) (W := 683351)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w179 : ∀ j : ℕ, 332589454 ≤ j → j < 333089454 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 665178908) (x1 := 666178906) (lo := 665178977) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w180 : ∀ j : ℕ, 333089454 ≤ j → j < 333524694 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 666178908) (x1 := 667049386) (lo := 666178977) (W := 1003801)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w181 : ∀ j : ℕ, 333524695 ≤ j → j < 334024695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 667049390) (x1 := 668049388) (lo := 667049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w182 : ∀ j : ℕ, 334024695 ≤ j → j < 334524695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 668049390) (x1 := 669049388) (lo := 668049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w183 : ∀ j : ℕ, 334524695 ≤ j → j < 335024695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 669049390) (x1 := 670049388) (lo := 669049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w184 : ∀ j : ℕ, 335024695 ≤ j → j < 335524695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 670049390) (x1 := 671049388) (lo := 670049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w185 : ∀ j : ℕ, 335524695 ≤ j → j < 336024695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 671049390) (x1 := 672049388) (lo := 671049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w186 : ∀ j : ℕ, 336024695 ≤ j → j < 336524695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 672049390) (x1 := 673049388) (lo := 672049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w187 : ∀ j : ℕ, 336524695 ≤ j → j < 337024695 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 673049390) (x1 := 674049388) (lo := 673049459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w188 : ∀ j : ℕ, 337024695 ≤ j → j < 337088049 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 674049390) (x1 := 674176096) (lo := 674049459) (W := 260029)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w189 : ∀ j : ℕ, 337088050 ≤ j → j < 337588050 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 674176100) (x1 := 675176098) (lo := 674176169) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w190 : ∀ j : ℕ, 337588050 ≤ j → j < 338088050 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 675176100) (x1 := 676176098) (lo := 675176169) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w191 : ∀ j : ℕ, 338088050 ≤ j → j < 338588050 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 676176100) (x1 := 677176098) (lo := 676176169) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w192 : ∀ j : ℕ, 338588050 ≤ j → j < 338766068 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 677176100) (x1 := 677532134) (lo := 677176169) (W := 489357)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w193 : ∀ j : ℕ, 338766069 ≤ j → j < 339266069 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 677532138) (x1 := 678532136) (lo := 677532207) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w194 : ∀ j : ℕ, 339266069 ≤ j → j < 339540369 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 678532138) (x1 := 679080736) (lo := 678532207) (W := 681921)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w195 : ∀ j : ℕ, 339540370 ≤ j → j < 340040370 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 679080740) (x1 := 680080738) (lo := 679080809) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w196 : ∀ j : ℕ, 340040370 ≤ j → j < 340540370 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 680080740) (x1 := 681080738) (lo := 680080809) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w197 : ∀ j : ℕ, 340540370 ≤ j → j < 341040370 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 681080740) (x1 := 682080738) (lo := 681080809) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w198 : ∀ j : ℕ, 341040370 ≤ j → j < 341484933 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 682080740) (x1 := 682969864) (lo := 682080809) (W := 1022447)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w199 : ∀ j : ℕ, 341484934 ≤ j → j < 341984934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 682969868) (x1 := 683969866) (lo := 682969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w200 : ∀ j : ℕ, 341984934 ≤ j → j < 342484934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 683969868) (x1 := 684969866) (lo := 683969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w201 : ∀ j : ℕ, 342484934 ≤ j → j < 342984934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 684969868) (x1 := 685969866) (lo := 684969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w202 : ∀ j : ℕ, 342984934 ≤ j → j < 343484934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 685969868) (x1 := 686969866) (lo := 685969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w203 : ∀ j : ℕ, 343484934 ≤ j → j < 343984934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 686969868) (x1 := 687969866) (lo := 686969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w204 : ∀ j : ℕ, 343984934 ≤ j → j < 344484934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 687969868) (x1 := 688969866) (lo := 687969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w205 : ∀ j : ℕ, 344484934 ≤ j → j < 344984934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 688969868) (x1 := 689969866) (lo := 688969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w206 : ∀ j : ℕ, 344984934 ≤ j → j < 345484934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 689969868) (x1 := 690969866) (lo := 689969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w207 : ∀ j : ℕ, 345484934 ≤ j → j < 345984934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 690969868) (x1 := 691969866) (lo := 690969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w208 : ∀ j : ℕ, 345984934 ≤ j → j < 346484934 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 691969868) (x1 := 692969866) (lo := 691969937) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w209 : ∀ j : ℕ, 346484934 ≤ j → j < 346627713 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 692969868) (x1 := 693255424) (lo := 692969937) (W := 418879)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w210 : ∀ j : ℕ, 346627714 ≤ j → j < 347127714 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 693255428) (x1 := 694255426) (lo := 693255497) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w211 : ∀ j : ℕ, 347127714 ≤ j → j < 347627714 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 694255428) (x1 := 695255426) (lo := 694255497) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w212 : ∀ j : ℕ, 347627714 ≤ j → j < 348127714 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 695255428) (x1 := 696255426) (lo := 695255497) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w213 : ∀ j : ℕ, 348127714 ≤ j → j < 348627714 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 696255428) (x1 := 697255426) (lo := 696255497) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w214 : ∀ j : ℕ, 348627714 ≤ j → j < 349127714 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 697255428) (x1 := 698255426) (lo := 697255497) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w215 : ∀ j : ℕ, 349127714 ≤ j → j < 349455987 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 698255428) (x1 := 698911972) (lo := 698255497) (W := 789867)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w216 : ∀ j : ℕ, 349455988 ≤ j → j < 349955988 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 698911976) (x1 := 699911974) (lo := 698912045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w217 : ∀ j : ℕ, 349955988 ≤ j → j < 350455988 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 699911976) (x1 := 700911974) (lo := 699912045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w218 : ∀ j : ℕ, 350455988 ≤ j → j < 350955988 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 700911976) (x1 := 701911974) (lo := 700912045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w219 : ∀ j : ℕ, 350955988 ≤ j → j < 351455988 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 701911976) (x1 := 702911974) (lo := 701912045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w220 : ∀ j : ℕ, 351455988 ≤ j → j < 351955988 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 702911976) (x1 := 703911974) (lo := 702912045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w221 : ∀ j : ℕ, 351955988 ≤ j → j < 352146954 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 703911976) (x1 := 704293906) (lo := 703912045) (W := 515253)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w222 : ∀ j : ℕ, 352146955 ≤ j → j < 352646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 704293910) (x1 := 705293908) (lo := 704293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w223 : ∀ j : ℕ, 352646955 ≤ j → j < 353146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 705293910) (x1 := 706293908) (lo := 705293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w224 : ∀ j : ℕ, 353146955 ≤ j → j < 353646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 706293910) (x1 := 707293908) (lo := 706293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w225 : ∀ j : ℕ, 353646955 ≤ j → j < 354146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 707293910) (x1 := 708293908) (lo := 707293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w226 : ∀ j : ℕ, 354146955 ≤ j → j < 354646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 708293910) (x1 := 709293908) (lo := 708293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w227 : ∀ j : ℕ, 354646955 ≤ j → j < 355146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 709293910) (x1 := 710293908) (lo := 709293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w228 : ∀ j : ℕ, 355146955 ≤ j → j < 355646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 710293910) (x1 := 711293908) (lo := 710293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w229 : ∀ j : ℕ, 355646955 ≤ j → j < 356146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 711293910) (x1 := 712293908) (lo := 711293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w230 : ∀ j : ℕ, 356146955 ≤ j → j < 356646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 712293910) (x1 := 713293908) (lo := 712293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w231 : ∀ j : ℕ, 356646955 ≤ j → j < 357146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 713293910) (x1 := 714293908) (lo := 713293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w232 : ∀ j : ℕ, 357146955 ≤ j → j < 357646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 714293910) (x1 := 715293908) (lo := 714293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w233 : ∀ j : ℕ, 357646955 ≤ j → j < 358146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 715293910) (x1 := 716293908) (lo := 715293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w234 : ∀ j : ℕ, 358146955 ≤ j → j < 358646955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 716293910) (x1 := 717293908) (lo := 716293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w235 : ∀ j : ℕ, 358646955 ≤ j → j < 359146955 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 717293910) (x1 := 718293908) (lo := 717293979) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w236 : ∀ j : ℕ, 359146955 ≤ j → j < 359588094 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 718293910) (x1 := 719176186) (lo := 718293979) (W := 1015599)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w237 : ∀ j : ℕ, 359588095 ≤ j → j < 360088095 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 719176190) (x1 := 720176188) (lo := 719176259) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w238 : ∀ j : ℕ, 360088095 ≤ j → j < 360588095 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 720176190) (x1 := 721176188) (lo := 720176259) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w239 : ∀ j : ℕ, 360588095 ≤ j → j < 360864942 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 721176190) (x1 := 721729882) (lo := 721176259) (W := 687015)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w240 : ∀ j : ℕ, 360864943 ≤ j → j < 361364943 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 721729886) (x1 := 722729884) (lo := 721729955) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w241 : ∀ j : ℕ, 361364943 ≤ j → j < 361509321 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 722729886) (x1 := 723018640) (lo := 722729955) (W := 422077)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w242 : ∀ j : ℕ, 361509322 ≤ j → j < 362009322 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 723018644) (x1 := 724018642) (lo := 723018713) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w243 : ∀ j : ℕ, 362009322 ≤ j → j < 362044779 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 724018644) (x1 := 724089556) (lo := 724018713) (W := 204235)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w244 : ∀ j : ℕ, 362044780 ≤ j → j < 362544780 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 724089560) (x1 := 725089558) (lo := 724089629) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w245 : ∀ j : ℕ, 362544780 ≤ j → j < 363044780 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 725089560) (x1 := 726089558) (lo := 725089629) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w246 : ∀ j : ℕ, 363044780 ≤ j → j < 363307872 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 726089560) (x1 := 726615742) (lo := 726089629) (W := 659505)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w247 : ∀ j : ℕ, 363307873 ≤ j → j < 363807873 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 726615746) (x1 := 727615744) (lo := 726615815) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w248 : ∀ j : ℕ, 363807873 ≤ j → j < 363929721 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 727615746) (x1 := 727859440) (lo := 727615815) (W := 377017)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w249 : ∀ j : ℕ, 363929722 ≤ j → j < 364429722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 727859444) (x1 := 728859442) (lo := 727859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w250 : ∀ j : ℕ, 364429722 ≤ j → j < 364929722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 728859444) (x1 := 729859442) (lo := 728859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w251 : ∀ j : ℕ, 364929722 ≤ j → j < 365429722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 729859444) (x1 := 730859442) (lo := 729859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w252 : ∀ j : ℕ, 365429722 ≤ j → j < 365929722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 730859444) (x1 := 731859442) (lo := 730859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w253 : ∀ j : ℕ, 365929722 ≤ j → j < 366429722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 731859444) (x1 := 732859442) (lo := 731859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w254 : ∀ j : ℕ, 366429722 ≤ j → j < 366929722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 732859444) (x1 := 733859442) (lo := 732859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w255 : ∀ j : ℕ, 366929722 ≤ j → j < 367429722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 733859444) (x1 := 734859442) (lo := 733859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w256 : ∀ j : ℕ, 367429722 ≤ j → j < 367929722 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 734859444) (x1 := 735859442) (lo := 734859513) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w257 : ∀ j : ℕ, 367929722 ≤ j → j < 368052738 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 735859444) (x1 := 736105474) (lo := 735859513) (W := 379353)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w258 : ∀ j : ℕ, 368052739 ≤ j → j < 368552739 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 736105478) (x1 := 737105476) (lo := 736105547) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w259 : ∀ j : ℕ, 368552739 ≤ j → j < 368706636 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 737105478) (x1 := 737413270) (lo := 737105547) (W := 441115)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w260 : ∀ j : ℕ, 368706637 ≤ j → j < 368896868 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 737413274) (x1 := 737793734) (lo := 737413343) (W := 513783)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w261 : ∀ j : ℕ, 368896869 ≤ j → j < 369396869 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 737793738) (x1 := 738793736) (lo := 737793807) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w262 : ∀ j : ℕ, 369396869 ≤ j → j < 369896869 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 738793738) (x1 := 739793736) (lo := 738793807) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w263 : ∀ j : ℕ, 369896869 ≤ j → j < 370221216 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 739793738) (x1 := 740442430) (lo := 739793807) (W := 782015)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w264 : ∀ j : ℕ, 370221217 ≤ j → j < 370721217 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 740442434) (x1 := 741442432) (lo := 740442503) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w265 : ∀ j : ℕ, 370721217 ≤ j → j < 371221217 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 741442434) (x1 := 742442432) (lo := 741442503) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w266 : ∀ j : ℕ, 371221217 ≤ j → j < 371721217 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 742442434) (x1 := 743442432) (lo := 742442503) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w267 : ∀ j : ℕ, 371721217 ≤ j → j < 372221217 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 743442434) (x1 := 744442432) (lo := 743442503) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w268 : ∀ j : ℕ, 372221217 ≤ j → j < 372721217 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 744442434) (x1 := 745442432) (lo := 744442503) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w269 : ∀ j : ℕ, 372721217 ≤ j → j < 373221217 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 745442434) (x1 := 746442432) (lo := 745442503) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w270 : ∀ j : ℕ, 373221217 ≤ j → j < 373647957 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 746442434) (x1 := 747295912) (lo := 746442503) (W := 986801)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w271 : ∀ j : ℕ, 373647958 ≤ j → j < 374147958 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 747295916) (x1 := 748295914) (lo := 747295985) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w272 : ∀ j : ℕ, 374147958 ≤ j → j < 374647958 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 748295916) (x1 := 749295914) (lo := 748295985) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w273 : ∀ j : ℕ, 374647958 ≤ j → j < 374732334 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 749295916) (x1 := 749464666) (lo := 749295985) (W := 302073)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w274 : ∀ j : ℕ, 374732335 ≤ j → j < 374917002 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 749464670) (x1 := 749834002) (lo := 749464739) (W := 502655)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3w275 : ∀ j : ℕ, 374917003 ≤ j → j < 375000000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 749834006) (x1 := 749999998) (lo := 749834075) (W := 299315)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem resid_375844802 : ∃ a ∈ offsets, (2 * 375844802 + a).Prime := by
  refine ⟨505017, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_376494336 : ∃ a ∈ offsets, (2 * 376494336 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_376763487 : ∃ a ∈ offsets, (2 * 376763487 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_380755164 : ∃ a ∈ offsets, (2 * 380755164 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_383260149 : ∃ a ∈ offsets, (2 * 383260149 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_384927662 : ∃ a ∈ offsets, (2 * 384927662 + a).Prime := by
  refine ⟨505017, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_385289202 : ∃ a ∈ offsets, (2 * 385289202 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_386290587 : ∃ a ∈ offsets, (2 * 386290587 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_392883824 : ∃ a ∈ offsets, (2 * 392883824 + a).Prime := by
  refine ⟨421491, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_393826194 : ∃ a ∈ offsets, (2 * 393826194 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_402158154 : ∃ a ∈ offsets, (2 * 402158154 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_409477073 : ∃ a ∈ offsets, (2 * 409477073 + a).Prime := by
  refine ⟨291297, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_418414569 : ∃ a ∈ offsets, (2 * 418414569 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_427005129 : ∃ a ∈ offsets, (2 * 427005129 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_428476626 : ∃ a ∈ offsets, (2 * 428476626 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_429503382 : ∃ a ∈ offsets, (2 * 429503382 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_432132324 : ∃ a ∈ offsets, (2 * 432132324 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_433857234 : ∃ a ∈ offsets, (2 * 433857234 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_434110376 : ∃ a ∈ offsets, (2 * 434110376 + a).Prime := by
  refine ⟨291297, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_434939817 : ∃ a ∈ offsets, (2 * 434939817 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_437558202 : ∃ a ∈ offsets, (2 * 437558202 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_440617812 : ∃ a ∈ offsets, (2 * 440617812 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_442815867 : ∃ a ∈ offsets, (2 * 442815867 + a).Prime := by
  refine ⟨336179, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_443135727 : ∃ a ∈ offsets, (2 * 443135727 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_443564657 : ∃ a ∈ offsets, (2 * 443564657 + a).Prime := by
  refine ⟨2240913, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_444544959 : ∃ a ∈ offsets, (2 * 444544959 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_445298228 : ∃ a ∈ offsets, (2 * 445298228 + a).Prime := by
  refine ⟨421491, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_448700172 : ∃ a ∈ offsets, (2 * 448700172 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_450309858 : ∃ a ∈ offsets, (2 * 450309858 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_452113443 : ∃ a ∈ offsets, (2 * 452113443 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_452219238 : ∃ a ∈ offsets, (2 * 452219238 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_452348712 : ∃ a ∈ offsets, (2 * 452348712 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_454198914 : ∃ a ∈ offsets, (2 * 454198914 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_455036418 : ∃ a ∈ offsets, (2 * 455036418 + a).Prime := by
  refine ⟨3697757, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_460346637 : ∃ a ∈ offsets, (2 * 460346637 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_462826328 : ∃ a ∈ offsets, (2 * 462826328 + a).Prime := by
  refine ⟨2240913, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_463453197 : ∃ a ∈ offsets, (2 * 463453197 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_464697132 : ∃ a ∈ offsets, (2 * 464697132 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_466084287 : ∃ a ∈ offsets, (2 * 466084287 + a).Prime := by
  refine ⟨699059, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_466500438 : ∃ a ∈ offsets, (2 * 466500438 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_467546748 : ∃ a ∈ offsets, (2 * 467546748 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_468543507 : ∃ a ∈ offsets, (2 * 468543507 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_471117882 : ∃ a ∈ offsets, (2 * 471117882 + a).Prime := by
  refine ⟨3166973, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_472622646 : ∃ a ∈ offsets, (2 * 472622646 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_475309014 : ∃ a ∈ offsets, (2 * 475309014 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_477358826 : ∃ a ∈ offsets, (2 * 477358826 + a).Prime := by
  refine ⟨505017, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_479397246 : ∃ a ∈ offsets, (2 * 479397246 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_480975129 : ∃ a ∈ offsets, (2 * 480975129 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_481464827 : ∃ a ∈ offsets, (2 * 481464827 + a).Prime := by
  refine ⟨158457, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_481828008 : ∃ a ∈ offsets, (2 * 481828008 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_489950633 : ∃ a ∈ offsets, (2 * 489950633 + a).Prime := by
  refine ⟨505017, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_490860984 : ∃ a ∈ offsets, (2 * 490860984 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_491382483 : ∃ a ∈ offsets, (2 * 491382483 + a).Prime := by
  refine ⟨1668413, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_496245639 : ∃ a ∈ offsets, (2 * 496245639 + a).Prime := by
  refine ⟨1334189, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_499098783 : ∃ a ∈ offsets, (2 * 499098783 + a).Prime := by
  refine ⟨969173, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem resid_499800309 : ∃ a ∈ offsets, (2 * 499800309 + a).Prime := by
  refine ⟨3361883, by decide, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

private theorem b4w0 : ∀ j : ℕ, 375000000 ≤ j → j < 375500000 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 750000000) (x1 := 750999998) (lo := 750000069) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w1 : ∀ j : ℕ, 375500000 ≤ j → j < 375844802 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 751000000) (x1 := 751689602) (lo := 751000069) (W := 822925)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w2 : ∀ j : ℕ, 375844803 ≤ j → j < 376344803 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 751689606) (x1 := 752689604) (lo := 751689675) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w3 : ∀ j : ℕ, 376344803 ≤ j → j < 376494336 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 752689606) (x1 := 752988670) (lo := 752689675) (W := 432387)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w4 : ∀ j : ℕ, 376494337 ≤ j → j < 376763487 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 752988674) (x1 := 753526972) (lo := 752988743) (W := 671621)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w5 : ∀ j : ℕ, 376763488 ≤ j → j < 377263488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 753526976) (x1 := 754526974) (lo := 753527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w6 : ∀ j : ℕ, 377263488 ≤ j → j < 377763488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 754526976) (x1 := 755526974) (lo := 754527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w7 : ∀ j : ℕ, 377763488 ≤ j → j < 378263488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 755526976) (x1 := 756526974) (lo := 755527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w8 : ∀ j : ℕ, 378263488 ≤ j → j < 378763488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 756526976) (x1 := 757526974) (lo := 756527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w9 : ∀ j : ℕ, 378763488 ≤ j → j < 379263488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 757526976) (x1 := 758526974) (lo := 757527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w10 : ∀ j : ℕ, 379263488 ≤ j → j < 379763488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 758526976) (x1 := 759526974) (lo := 758527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w11 : ∀ j : ℕ, 379763488 ≤ j → j < 380263488 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 759526976) (x1 := 760526974) (lo := 759527045) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w12 : ∀ j : ℕ, 380263488 ≤ j → j < 380755164 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 760526976) (x1 := 761510326) (lo := 760527045) (W := 1116673)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w13 : ∀ j : ℕ, 380755165 ≤ j → j < 381255165 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 761510330) (x1 := 762510328) (lo := 761510399) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w14 : ∀ j : ℕ, 381255165 ≤ j → j < 381755165 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 762510330) (x1 := 763510328) (lo := 762510399) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w15 : ∀ j : ℕ, 381755165 ≤ j → j < 382255165 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 763510330) (x1 := 764510328) (lo := 763510399) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w16 : ∀ j : ℕ, 382255165 ≤ j → j < 382755165 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 764510330) (x1 := 765510328) (lo := 764510399) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w17 : ∀ j : ℕ, 382755165 ≤ j → j < 383255165 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 765510330) (x1 := 766510328) (lo := 765510399) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w18 : ∀ j : ℕ, 383255165 ≤ j → j < 383260149 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 766510330) (x1 := 766520296) (lo := 766510399) (W := 143289)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w19 : ∀ j : ℕ, 383260150 ≤ j → j < 383760150 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 766520300) (x1 := 767520298) (lo := 766520369) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w20 : ∀ j : ℕ, 383760150 ≤ j → j < 384260150 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 767520300) (x1 := 768520298) (lo := 767520369) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w21 : ∀ j : ℕ, 384260150 ≤ j → j < 384760150 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 768520300) (x1 := 769520298) (lo := 768520369) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w22 : ∀ j : ℕ, 384760150 ≤ j → j < 384927662 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 769520300) (x1 := 769855322) (lo := 769520369) (W := 468345)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w23 : ∀ j : ℕ, 384927663 ≤ j → j < 385289202 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 769855326) (x1 := 770578402) (lo := 769855395) (W := 856399)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w24 : ∀ j : ℕ, 385289203 ≤ j → j < 385789203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 770578406) (x1 := 771578404) (lo := 770578475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w25 : ∀ j : ℕ, 385789203 ≤ j → j < 386289203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 771578406) (x1 := 772578404) (lo := 771578475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w26 : ∀ j : ℕ, 386289203 ≤ j → j < 386290587 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 772578406) (x1 := 772581172) (lo := 772578475) (W := 136089)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w27 : ∀ j : ℕ, 386290588 ≤ j → j < 386790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 772581176) (x1 := 773581174) (lo := 772581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w28 : ∀ j : ℕ, 386790588 ≤ j → j < 387290588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 773581176) (x1 := 774581174) (lo := 773581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w29 : ∀ j : ℕ, 387290588 ≤ j → j < 387790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 774581176) (x1 := 775581174) (lo := 774581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w30 : ∀ j : ℕ, 387790588 ≤ j → j < 388290588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 775581176) (x1 := 776581174) (lo := 775581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w31 : ∀ j : ℕ, 388290588 ≤ j → j < 388790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 776581176) (x1 := 777581174) (lo := 776581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w32 : ∀ j : ℕ, 388790588 ≤ j → j < 389290588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 777581176) (x1 := 778581174) (lo := 777581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w33 : ∀ j : ℕ, 389290588 ≤ j → j < 389790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 778581176) (x1 := 779581174) (lo := 778581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w34 : ∀ j : ℕ, 389790588 ≤ j → j < 390290588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 779581176) (x1 := 780581174) (lo := 779581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w35 : ∀ j : ℕ, 390290588 ≤ j → j < 390790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 780581176) (x1 := 781581174) (lo := 780581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w36 : ∀ j : ℕ, 390790588 ≤ j → j < 391290588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 781581176) (x1 := 782581174) (lo := 781581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w37 : ∀ j : ℕ, 391290588 ≤ j → j < 391790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 782581176) (x1 := 783581174) (lo := 782581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w38 : ∀ j : ℕ, 391790588 ≤ j → j < 392290588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 783581176) (x1 := 784581174) (lo := 783581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w39 : ∀ j : ℕ, 392290588 ≤ j → j < 392790588 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 784581176) (x1 := 785581174) (lo := 784581245) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w40 : ∀ j : ℕ, 392790588 ≤ j → j < 392883824 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 785581176) (x1 := 785767646) (lo := 785581245) (W := 319793)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w41 : ∀ j : ℕ, 392883825 ≤ j → j < 393383825 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 785767650) (x1 := 786767648) (lo := 785767719) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w42 : ∀ j : ℕ, 393383825 ≤ j → j < 393826194 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 786767650) (x1 := 787652386) (lo := 786767719) (W := 1018059)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w43 : ∀ j : ℕ, 393826195 ≤ j → j < 394326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 787652390) (x1 := 788652388) (lo := 787652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w44 : ∀ j : ℕ, 394326195 ≤ j → j < 394826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 788652390) (x1 := 789652388) (lo := 788652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w45 : ∀ j : ℕ, 394826195 ≤ j → j < 395326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 789652390) (x1 := 790652388) (lo := 789652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w46 : ∀ j : ℕ, 395326195 ≤ j → j < 395826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 790652390) (x1 := 791652388) (lo := 790652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w47 : ∀ j : ℕ, 395826195 ≤ j → j < 396326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 791652390) (x1 := 792652388) (lo := 791652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w48 : ∀ j : ℕ, 396326195 ≤ j → j < 396826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 792652390) (x1 := 793652388) (lo := 792652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w49 : ∀ j : ℕ, 396826195 ≤ j → j < 397326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 793652390) (x1 := 794652388) (lo := 793652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w50 : ∀ j : ℕ, 397326195 ≤ j → j < 397826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 794652390) (x1 := 795652388) (lo := 794652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w51 : ∀ j : ℕ, 397826195 ≤ j → j < 398326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 795652390) (x1 := 796652388) (lo := 795652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w52 : ∀ j : ℕ, 398326195 ≤ j → j < 398826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 796652390) (x1 := 797652388) (lo := 796652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w53 : ∀ j : ℕ, 398826195 ≤ j → j < 399326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 797652390) (x1 := 798652388) (lo := 797652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w54 : ∀ j : ℕ, 399326195 ≤ j → j < 399826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 798652390) (x1 := 799652388) (lo := 798652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w55 : ∀ j : ℕ, 399826195 ≤ j → j < 400326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 799652390) (x1 := 800652388) (lo := 799652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w56 : ∀ j : ℕ, 400326195 ≤ j → j < 400826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 800652390) (x1 := 801652388) (lo := 800652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w57 : ∀ j : ℕ, 400826195 ≤ j → j < 401326195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 801652390) (x1 := 802652388) (lo := 801652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w58 : ∀ j : ℕ, 401326195 ≤ j → j < 401826195 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 802652390) (x1 := 803652388) (lo := 802652459) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w59 : ∀ j : ℕ, 401826195 ≤ j → j < 402158154 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 803652390) (x1 := 804316306) (lo := 803652459) (W := 797239)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w60 : ∀ j : ℕ, 402158155 ≤ j → j < 402658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 804316310) (x1 := 805316308) (lo := 804316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w61 : ∀ j : ℕ, 402658155 ≤ j → j < 403158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 805316310) (x1 := 806316308) (lo := 805316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w62 : ∀ j : ℕ, 403158155 ≤ j → j < 403658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 806316310) (x1 := 807316308) (lo := 806316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w63 : ∀ j : ℕ, 403658155 ≤ j → j < 404158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 807316310) (x1 := 808316308) (lo := 807316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w64 : ∀ j : ℕ, 404158155 ≤ j → j < 404658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 808316310) (x1 := 809316308) (lo := 808316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w65 : ∀ j : ℕ, 404658155 ≤ j → j < 405158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 809316310) (x1 := 810316308) (lo := 809316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w66 : ∀ j : ℕ, 405158155 ≤ j → j < 405658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 810316310) (x1 := 811316308) (lo := 810316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w67 : ∀ j : ℕ, 405658155 ≤ j → j < 406158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 811316310) (x1 := 812316308) (lo := 811316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w68 : ∀ j : ℕ, 406158155 ≤ j → j < 406658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 812316310) (x1 := 813316308) (lo := 812316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w69 : ∀ j : ℕ, 406658155 ≤ j → j < 407158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 813316310) (x1 := 814316308) (lo := 813316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w70 : ∀ j : ℕ, 407158155 ≤ j → j < 407658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 814316310) (x1 := 815316308) (lo := 814316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w71 : ∀ j : ℕ, 407658155 ≤ j → j < 408158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 815316310) (x1 := 816316308) (lo := 815316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w72 : ∀ j : ℕ, 408158155 ≤ j → j < 408658155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 816316310) (x1 := 817316308) (lo := 816316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w73 : ∀ j : ℕ, 408658155 ≤ j → j < 409158155 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 817316310) (x1 := 818316308) (lo := 817316379) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w74 : ∀ j : ℕ, 409158155 ≤ j → j < 409477073 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 818316310) (x1 := 818954144) (lo := 818316379) (W := 771157)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w75 : ∀ j : ℕ, 409477074 ≤ j → j < 409977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 818954148) (x1 := 819954146) (lo := 818954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w76 : ∀ j : ℕ, 409977074 ≤ j → j < 410477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 819954148) (x1 := 820954146) (lo := 819954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w77 : ∀ j : ℕ, 410477074 ≤ j → j < 410977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 820954148) (x1 := 821954146) (lo := 820954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w78 : ∀ j : ℕ, 410977074 ≤ j → j < 411477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 821954148) (x1 := 822954146) (lo := 821954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w79 : ∀ j : ℕ, 411477074 ≤ j → j < 411977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 822954148) (x1 := 823954146) (lo := 822954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w80 : ∀ j : ℕ, 411977074 ≤ j → j < 412477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 823954148) (x1 := 824954146) (lo := 823954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w81 : ∀ j : ℕ, 412477074 ≤ j → j < 412977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 824954148) (x1 := 825954146) (lo := 824954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w82 : ∀ j : ℕ, 412977074 ≤ j → j < 413477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 825954148) (x1 := 826954146) (lo := 825954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w83 : ∀ j : ℕ, 413477074 ≤ j → j < 413977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 826954148) (x1 := 827954146) (lo := 826954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w84 : ∀ j : ℕ, 413977074 ≤ j → j < 414477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 827954148) (x1 := 828954146) (lo := 827954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w85 : ∀ j : ℕ, 414477074 ≤ j → j < 414977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 828954148) (x1 := 829954146) (lo := 828954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w86 : ∀ j : ℕ, 414977074 ≤ j → j < 415477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 829954148) (x1 := 830954146) (lo := 829954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w87 : ∀ j : ℕ, 415477074 ≤ j → j < 415977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 830954148) (x1 := 831954146) (lo := 830954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w88 : ∀ j : ℕ, 415977074 ≤ j → j < 416477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 831954148) (x1 := 832954146) (lo := 831954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w89 : ∀ j : ℕ, 416477074 ≤ j → j < 416977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 832954148) (x1 := 833954146) (lo := 832954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w90 : ∀ j : ℕ, 416977074 ≤ j → j < 417477074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 833954148) (x1 := 834954146) (lo := 833954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w91 : ∀ j : ℕ, 417477074 ≤ j → j < 417977074 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 834954148) (x1 := 835954146) (lo := 834954217) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w92 : ∀ j : ℕ, 417977074 ≤ j → j < 418414569 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 835954148) (x1 := 836829136) (lo := 835954217) (W := 1008311)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w93 : ∀ j : ℕ, 418414570 ≤ j → j < 418914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 836829140) (x1 := 837829138) (lo := 836829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w94 : ∀ j : ℕ, 418914570 ≤ j → j < 419414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 837829140) (x1 := 838829138) (lo := 837829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w95 : ∀ j : ℕ, 419414570 ≤ j → j < 419914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 838829140) (x1 := 839829138) (lo := 838829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w96 : ∀ j : ℕ, 419914570 ≤ j → j < 420414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 839829140) (x1 := 840829138) (lo := 839829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w97 : ∀ j : ℕ, 420414570 ≤ j → j < 420914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 840829140) (x1 := 841829138) (lo := 840829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w98 : ∀ j : ℕ, 420914570 ≤ j → j < 421414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 841829140) (x1 := 842829138) (lo := 841829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w99 : ∀ j : ℕ, 421414570 ≤ j → j < 421914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 842829140) (x1 := 843829138) (lo := 842829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w100 : ∀ j : ℕ, 421914570 ≤ j → j < 422414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 843829140) (x1 := 844829138) (lo := 843829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w101 : ∀ j : ℕ, 422414570 ≤ j → j < 422914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 844829140) (x1 := 845829138) (lo := 844829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w102 : ∀ j : ℕ, 422914570 ≤ j → j < 423414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 845829140) (x1 := 846829138) (lo := 845829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w103 : ∀ j : ℕ, 423414570 ≤ j → j < 423914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 846829140) (x1 := 847829138) (lo := 846829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w104 : ∀ j : ℕ, 423914570 ≤ j → j < 424414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 847829140) (x1 := 848829138) (lo := 847829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w105 : ∀ j : ℕ, 424414570 ≤ j → j < 424914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 848829140) (x1 := 849829138) (lo := 848829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w106 : ∀ j : ℕ, 424914570 ≤ j → j < 425414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 849829140) (x1 := 850829138) (lo := 849829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w107 : ∀ j : ℕ, 425414570 ≤ j → j < 425914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 850829140) (x1 := 851829138) (lo := 850829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w108 : ∀ j : ℕ, 425914570 ≤ j → j < 426414570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 851829140) (x1 := 852829138) (lo := 851829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w109 : ∀ j : ℕ, 426414570 ≤ j → j < 426914570 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 852829140) (x1 := 853829138) (lo := 852829209) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w110 : ∀ j : ℕ, 426914570 ≤ j → j < 427005129 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 853829140) (x1 := 854010256) (lo := 853829209) (W := 314439)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w111 : ∀ j : ℕ, 427005130 ≤ j → j < 427505130 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 854010260) (x1 := 855010258) (lo := 854010329) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w112 : ∀ j : ℕ, 427505130 ≤ j → j < 428005130 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 855010260) (x1 := 856010258) (lo := 855010329) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w113 : ∀ j : ℕ, 428005130 ≤ j → j < 428476626 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 856010260) (x1 := 856953250) (lo := 856010329) (W := 1076313)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w114 : ∀ j : ℕ, 428476627 ≤ j → j < 428976627 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 856953254) (x1 := 857953252) (lo := 856953323) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w115 : ∀ j : ℕ, 428976627 ≤ j → j < 429476627 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 857953254) (x1 := 858953252) (lo := 857953323) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w116 : ∀ j : ℕ, 429476627 ≤ j → j < 429503382 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 858953254) (x1 := 859006762) (lo := 858953323) (W := 186831)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w117 : ∀ j : ℕ, 429503383 ≤ j → j < 430003383 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 859006766) (x1 := 860006764) (lo := 859006835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w118 : ∀ j : ℕ, 430003383 ≤ j → j < 430503383 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 860006766) (x1 := 861006764) (lo := 860006835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w119 : ∀ j : ℕ, 430503383 ≤ j → j < 431003383 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 861006766) (x1 := 862006764) (lo := 861006835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w120 : ∀ j : ℕ, 431003383 ≤ j → j < 431503383 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 862006766) (x1 := 863006764) (lo := 862006835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w121 : ∀ j : ℕ, 431503383 ≤ j → j < 432003383 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 863006766) (x1 := 864006764) (lo := 863006835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w122 : ∀ j : ℕ, 432003383 ≤ j → j < 432132324 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 864006766) (x1 := 864264646) (lo := 864006835) (W := 391203)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w123 : ∀ j : ℕ, 432132325 ≤ j → j < 432632325 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 864264650) (x1 := 865264648) (lo := 864264719) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w124 : ∀ j : ℕ, 432632325 ≤ j → j < 433132325 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 865264650) (x1 := 866264648) (lo := 865264719) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w125 : ∀ j : ℕ, 433132325 ≤ j → j < 433632325 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 866264650) (x1 := 867264648) (lo := 866264719) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w126 : ∀ j : ℕ, 433632325 ≤ j → j < 433857234 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 867264650) (x1 := 867714466) (lo := 867264719) (W := 583139)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w127 : ∀ j : ℕ, 433857235 ≤ j → j < 434110376 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 867714470) (x1 := 868220750) (lo := 867714539) (W := 639603)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w128 : ∀ j : ℕ, 434110377 ≤ j → j < 434610377 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 868220754) (x1 := 869220752) (lo := 868220823) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w129 : ∀ j : ℕ, 434610377 ≤ j → j < 434939817 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 869220754) (x1 := 869879632) (lo := 869220823) (W := 792201)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w130 : ∀ j : ℕ, 434939818 ≤ j → j < 435439818 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 869879636) (x1 := 870879634) (lo := 869879705) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w131 : ∀ j : ℕ, 435439818 ≤ j → j < 435939818 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 870879636) (x1 := 871879634) (lo := 870879705) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w132 : ∀ j : ℕ, 435939818 ≤ j → j < 436439818 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 871879636) (x1 := 872879634) (lo := 871879705) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w133 : ∀ j : ℕ, 436439818 ≤ j → j < 436939818 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 872879636) (x1 := 873879634) (lo := 872879705) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w134 : ∀ j : ℕ, 436939818 ≤ j → j < 437439818 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 873879636) (x1 := 874879634) (lo := 873879705) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w135 : ∀ j : ℕ, 437439818 ≤ j → j < 437558202 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 874879636) (x1 := 875116402) (lo := 874879705) (W := 370089)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w136 : ∀ j : ℕ, 437558203 ≤ j → j < 438058203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 875116406) (x1 := 876116404) (lo := 875116475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w137 : ∀ j : ℕ, 438058203 ≤ j → j < 438558203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 876116406) (x1 := 877116404) (lo := 876116475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w138 : ∀ j : ℕ, 438558203 ≤ j → j < 439058203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 877116406) (x1 := 878116404) (lo := 877116475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w139 : ∀ j : ℕ, 439058203 ≤ j → j < 439558203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 878116406) (x1 := 879116404) (lo := 878116475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w140 : ∀ j : ℕ, 439558203 ≤ j → j < 440058203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 879116406) (x1 := 880116404) (lo := 879116475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w141 : ∀ j : ℕ, 440058203 ≤ j → j < 440558203 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 880116406) (x1 := 881116404) (lo := 880116475) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w142 : ∀ j : ℕ, 440558203 ≤ j → j < 440617812 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 881116406) (x1 := 881235622) (lo := 881116475) (W := 252539)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w143 : ∀ j : ℕ, 440617813 ≤ j → j < 441117813 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 881235626) (x1 := 882235624) (lo := 881235695) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w144 : ∀ j : ℕ, 441117813 ≤ j → j < 441617813 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 882235626) (x1 := 883235624) (lo := 882235695) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w145 : ∀ j : ℕ, 441617813 ≤ j → j < 442117813 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 883235626) (x1 := 884235624) (lo := 883235695) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w146 : ∀ j : ℕ, 442117813 ≤ j → j < 442617813 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 884235626) (x1 := 885235624) (lo := 884235695) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w147 : ∀ j : ℕ, 442617813 ≤ j → j < 442815867 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 885235626) (x1 := 885631732) (lo := 885235695) (W := 529429)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w148 : ∀ j : ℕ, 442815868 ≤ j → j < 443135727 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 885631736) (x1 := 886271452) (lo := 885631805) (W := 773039)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w149 : ∀ j : ℕ, 443135728 ≤ j → j < 443564657 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 886271456) (x1 := 887129312) (lo := 886271525) (W := 991179)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w150 : ∀ j : ℕ, 443564658 ≤ j → j < 444064658 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 887129316) (x1 := 888129314) (lo := 887129385) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w151 : ∀ j : ℕ, 444064658 ≤ j → j < 444544959 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 888129316) (x1 := 889089916) (lo := 888129385) (W := 1093923)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w152 : ∀ j : ℕ, 444544960 ≤ j → j < 445044960 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 889089920) (x1 := 890089918) (lo := 889089989) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w153 : ∀ j : ℕ, 445044960 ≤ j → j < 445298228 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 890089920) (x1 := 890596454) (lo := 890089989) (W := 639857)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w154 : ∀ j : ℕ, 445298229 ≤ j → j < 445798229 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 890596458) (x1 := 891596456) (lo := 890596527) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w155 : ∀ j : ℕ, 445798229 ≤ j → j < 446298229 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 891596458) (x1 := 892596456) (lo := 891596527) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w156 : ∀ j : ℕ, 446298229 ≤ j → j < 446798229 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 892596458) (x1 := 893596456) (lo := 892596527) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w157 : ∀ j : ℕ, 446798229 ≤ j → j < 447298229 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 893596458) (x1 := 894596456) (lo := 893596527) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w158 : ∀ j : ℕ, 447298229 ≤ j → j < 447798229 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 894596458) (x1 := 895596456) (lo := 894596527) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w159 : ∀ j : ℕ, 447798229 ≤ j → j < 448298229 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 895596458) (x1 := 896596456) (lo := 895596527) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w160 : ∀ j : ℕ, 448298229 ≤ j → j < 448700172 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 896596458) (x1 := 897400342) (lo := 896596527) (W := 937207)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w161 : ∀ j : ℕ, 448700173 ≤ j → j < 449200173 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 897400346) (x1 := 898400344) (lo := 897400415) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w162 : ∀ j : ℕ, 449200173 ≤ j → j < 449700173 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 898400346) (x1 := 899400344) (lo := 898400415) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w163 : ∀ j : ℕ, 449700173 ≤ j → j < 450200173 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 899400346) (x1 := 900400344) (lo := 899400415) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w164 : ∀ j : ℕ, 450200173 ≤ j → j < 450309858 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 900400346) (x1 := 900619714) (lo := 900400415) (W := 352691)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w165 : ∀ j : ℕ, 450309859 ≤ j → j < 450809859 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 900619718) (x1 := 901619716) (lo := 900619787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w166 : ∀ j : ℕ, 450809859 ≤ j → j < 451309859 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 901619718) (x1 := 902619716) (lo := 901619787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w167 : ∀ j : ℕ, 451309859 ≤ j → j < 451809859 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 902619718) (x1 := 903619716) (lo := 902619787) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w168 : ∀ j : ℕ, 451809859 ≤ j → j < 452113443 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 903619718) (x1 := 904226884) (lo := 903619787) (W := 740489)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w169 : ∀ j : ℕ, 452113444 ≤ j → j < 452219238 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 904226888) (x1 := 904438474) (lo := 904226957) (W := 344909)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w170 : ∀ j : ℕ, 452219239 ≤ j → j < 452348712 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 904438478) (x1 := 904697422) (lo := 904438547) (W := 392267)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w171 : ∀ j : ℕ, 452348713 ≤ j → j < 452848713 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 904697426) (x1 := 905697424) (lo := 904697495) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w172 : ∀ j : ℕ, 452848713 ≤ j → j < 453348713 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 905697426) (x1 := 906697424) (lo := 905697495) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w173 : ∀ j : ℕ, 453348713 ≤ j → j < 453848713 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 906697426) (x1 := 907697424) (lo := 906697495) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w174 : ∀ j : ℕ, 453848713 ≤ j → j < 454198914 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 907697426) (x1 := 908397826) (lo := 907697495) (W := 833723)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w175 : ∀ j : ℕ, 454198915 ≤ j → j < 454698915 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 908397830) (x1 := 909397828) (lo := 908397899) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w176 : ∀ j : ℕ, 454698915 ≤ j → j < 455036418 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 909397830) (x1 := 910072834) (lo := 909397899) (W := 808327)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w177 : ∀ j : ℕ, 455036419 ≤ j → j < 455536419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 910072838) (x1 := 911072836) (lo := 910072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w178 : ∀ j : ℕ, 455536419 ≤ j → j < 456036419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 911072838) (x1 := 912072836) (lo := 911072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w179 : ∀ j : ℕ, 456036419 ≤ j → j < 456536419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 912072838) (x1 := 913072836) (lo := 912072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w180 : ∀ j : ℕ, 456536419 ≤ j → j < 457036419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 913072838) (x1 := 914072836) (lo := 913072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w181 : ∀ j : ℕ, 457036419 ≤ j → j < 457536419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 914072838) (x1 := 915072836) (lo := 914072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w182 : ∀ j : ℕ, 457536419 ≤ j → j < 458036419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 915072838) (x1 := 916072836) (lo := 915072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w183 : ∀ j : ℕ, 458036419 ≤ j → j < 458536419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 916072838) (x1 := 917072836) (lo := 916072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w184 : ∀ j : ℕ, 458536419 ≤ j → j < 459036419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 917072838) (x1 := 918072836) (lo := 917072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w185 : ∀ j : ℕ, 459036419 ≤ j → j < 459536419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 918072838) (x1 := 919072836) (lo := 918072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w186 : ∀ j : ℕ, 459536419 ≤ j → j < 460036419 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 919072838) (x1 := 920072836) (lo := 919072907) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w187 : ∀ j : ℕ, 460036419 ≤ j → j < 460346637 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 920072838) (x1 := 920693272) (lo := 920072907) (W := 753757)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w188 : ∀ j : ℕ, 460346638 ≤ j → j < 460846638 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 920693276) (x1 := 921693274) (lo := 920693345) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w189 : ∀ j : ℕ, 460846638 ≤ j → j < 461346638 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 921693276) (x1 := 922693274) (lo := 921693345) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w190 : ∀ j : ℕ, 461346638 ≤ j → j < 461846638 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 922693276) (x1 := 923693274) (lo := 922693345) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w191 : ∀ j : ℕ, 461846638 ≤ j → j < 462346638 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 923693276) (x1 := 924693274) (lo := 923693345) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w192 : ∀ j : ℕ, 462346638 ≤ j → j < 462826328 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 924693276) (x1 := 925652654) (lo := 924693345) (W := 1092701)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w193 : ∀ j : ℕ, 462826329 ≤ j → j < 463326329 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 925652658) (x1 := 926652656) (lo := 925652727) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w194 : ∀ j : ℕ, 463326329 ≤ j → j < 463453197 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 926652658) (x1 := 926906392) (lo := 926652727) (W := 387057)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w195 : ∀ j : ℕ, 463453198 ≤ j → j < 463953198 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 926906396) (x1 := 927906394) (lo := 926906465) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w196 : ∀ j : ℕ, 463953198 ≤ j → j < 464453198 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 927906396) (x1 := 928906394) (lo := 927906465) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w197 : ∀ j : ℕ, 464453198 ≤ j → j < 464697132 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 928906396) (x1 := 929394262) (lo := 928906465) (W := 621189)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w198 : ∀ j : ℕ, 464697133 ≤ j → j < 465197133 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 929394266) (x1 := 930394264) (lo := 929394335) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w199 : ∀ j : ℕ, 465197133 ≤ j → j < 465697133 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 930394266) (x1 := 931394264) (lo := 930394335) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w200 : ∀ j : ℕ, 465697133 ≤ j → j < 466084287 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 931394266) (x1 := 932168572) (lo := 931394335) (W := 907629)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w201 : ∀ j : ℕ, 466084288 ≤ j → j < 466500438 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 932168576) (x1 := 933000874) (lo := 932168645) (W := 965621)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w202 : ∀ j : ℕ, 466500439 ≤ j → j < 467000439 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 933000878) (x1 := 934000876) (lo := 933000947) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w203 : ∀ j : ℕ, 467000439 ≤ j → j < 467500439 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 934000878) (x1 := 935000876) (lo := 934000947) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w204 : ∀ j : ℕ, 467500439 ≤ j → j < 467546748 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 935000878) (x1 := 935093494) (lo := 935000947) (W := 225939)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w205 : ∀ j : ℕ, 467546749 ≤ j → j < 468046749 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 935093498) (x1 := 936093496) (lo := 935093567) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w206 : ∀ j : ℕ, 468046749 ≤ j → j < 468543507 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 936093498) (x1 := 937087012) (lo := 936093567) (W := 1126837)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w207 : ∀ j : ℕ, 468543508 ≤ j → j < 469043508 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 937087016) (x1 := 938087014) (lo := 937087085) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w208 : ∀ j : ℕ, 469043508 ≤ j → j < 469543508 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 938087016) (x1 := 939087014) (lo := 938087085) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w209 : ∀ j : ℕ, 469543508 ≤ j → j < 470043508 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 939087016) (x1 := 940087014) (lo := 939087085) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w210 : ∀ j : ℕ, 470043508 ≤ j → j < 470543508 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 940087016) (x1 := 941087014) (lo := 940087085) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w211 : ∀ j : ℕ, 470543508 ≤ j → j < 471043508 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 941087016) (x1 := 942087014) (lo := 941087085) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w212 : ∀ j : ℕ, 471043508 ≤ j → j < 471117882 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 942087016) (x1 := 942235762) (lo := 942087085) (W := 282069)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w213 : ∀ j : ℕ, 471117883 ≤ j → j < 471617883 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 942235766) (x1 := 943235764) (lo := 942235835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w214 : ∀ j : ℕ, 471617883 ≤ j → j < 472117883 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 943235766) (x1 := 944235764) (lo := 943235835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w215 : ∀ j : ℕ, 472117883 ≤ j → j < 472617883 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 944235766) (x1 := 945235764) (lo := 944235835) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w216 : ∀ j : ℕ, 472617883 ≤ j → j < 472622646 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 945235766) (x1 := 945245290) (lo := 945235835) (W := 142847)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w217 : ∀ j : ℕ, 472622647 ≤ j → j < 473122647 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 945245294) (x1 := 946245292) (lo := 945245363) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w218 : ∀ j : ℕ, 473122647 ≤ j → j < 473622647 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 946245294) (x1 := 947245292) (lo := 946245363) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w219 : ∀ j : ℕ, 473622647 ≤ j → j < 474122647 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 947245294) (x1 := 948245292) (lo := 947245363) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w220 : ∀ j : ℕ, 474122647 ≤ j → j < 474622647 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 948245294) (x1 := 949245292) (lo := 948245363) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w221 : ∀ j : ℕ, 474622647 ≤ j → j < 475122647 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 949245294) (x1 := 950245292) (lo := 949245363) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w222 : ∀ j : ℕ, 475122647 ≤ j → j < 475309014 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 950245294) (x1 := 950618026) (lo := 950245363) (W := 506055)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w223 : ∀ j : ℕ, 475309015 ≤ j → j < 475809015 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 950618030) (x1 := 951618028) (lo := 950618099) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w224 : ∀ j : ℕ, 475809015 ≤ j → j < 476309015 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 951618030) (x1 := 952618028) (lo := 951618099) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w225 : ∀ j : ℕ, 476309015 ≤ j → j < 476809015 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 952618030) (x1 := 953618028) (lo := 952618099) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w226 : ∀ j : ℕ, 476809015 ≤ j → j < 477309015 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 953618030) (x1 := 954618028) (lo := 953618099) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w227 : ∀ j : ℕ, 477309015 ≤ j → j < 477358826 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 954618030) (x1 := 954717650) (lo := 954618099) (W := 232943)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w228 : ∀ j : ℕ, 477358827 ≤ j → j < 477858827 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 954717654) (x1 := 955717652) (lo := 954717723) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w229 : ∀ j : ℕ, 477858827 ≤ j → j < 478358827 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 955717654) (x1 := 956717652) (lo := 955717723) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w230 : ∀ j : ℕ, 478358827 ≤ j → j < 478858827 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 956717654) (x1 := 957717652) (lo := 956717723) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w231 : ∀ j : ℕ, 478858827 ≤ j → j < 479358827 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 957717654) (x1 := 958717652) (lo := 957717723) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w232 : ∀ j : ℕ, 479358827 ≤ j → j < 479397246 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 958717654) (x1 := 958794490) (lo := 958717723) (W := 210159)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w233 : ∀ j : ℕ, 479397247 ≤ j → j < 479897247 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 958794494) (x1 := 959794492) (lo := 958794563) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w234 : ∀ j : ℕ, 479897247 ≤ j → j < 480397247 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 959794494) (x1 := 960794492) (lo := 959794563) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w235 : ∀ j : ℕ, 480397247 ≤ j → j < 480897247 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 960794494) (x1 := 961794492) (lo := 960794563) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w236 : ∀ j : ℕ, 480897247 ≤ j → j < 480975129 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 961794494) (x1 := 961950256) (lo := 961794563) (W := 289085)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w237 : ∀ j : ℕ, 480975130 ≤ j → j < 481464827 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 961950260) (x1 := 962929652) (lo := 961950329) (W := 1112715)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w238 : ∀ j : ℕ, 481464828 ≤ j → j < 481828008 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 962929656) (x1 := 963656014) (lo := 962929725) (W := 859681)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w239 : ∀ j : ℕ, 481828009 ≤ j → j < 482328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 963656018) (x1 := 964656016) (lo := 963656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w240 : ∀ j : ℕ, 482328009 ≤ j → j < 482828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 964656018) (x1 := 965656016) (lo := 964656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w241 : ∀ j : ℕ, 482828009 ≤ j → j < 483328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 965656018) (x1 := 966656016) (lo := 965656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w242 : ∀ j : ℕ, 483328009 ≤ j → j < 483828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 966656018) (x1 := 967656016) (lo := 966656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w243 : ∀ j : ℕ, 483828009 ≤ j → j < 484328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 967656018) (x1 := 968656016) (lo := 967656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w244 : ∀ j : ℕ, 484328009 ≤ j → j < 484828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 968656018) (x1 := 969656016) (lo := 968656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w245 : ∀ j : ℕ, 484828009 ≤ j → j < 485328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 969656018) (x1 := 970656016) (lo := 969656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w246 : ∀ j : ℕ, 485328009 ≤ j → j < 485828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 970656018) (x1 := 971656016) (lo := 970656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w247 : ∀ j : ℕ, 485828009 ≤ j → j < 486328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 971656018) (x1 := 972656016) (lo := 971656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w248 : ∀ j : ℕ, 486328009 ≤ j → j < 486828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 972656018) (x1 := 973656016) (lo := 972656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w249 : ∀ j : ℕ, 486828009 ≤ j → j < 487328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 973656018) (x1 := 974656016) (lo := 973656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w250 : ∀ j : ℕ, 487328009 ≤ j → j < 487828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 974656018) (x1 := 975656016) (lo := 974656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w251 : ∀ j : ℕ, 487828009 ≤ j → j < 488328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 975656018) (x1 := 976656016) (lo := 975656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w252 : ∀ j : ℕ, 488328009 ≤ j → j < 488828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 976656018) (x1 := 977656016) (lo := 976656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w253 : ∀ j : ℕ, 488828009 ≤ j → j < 489328009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 977656018) (x1 := 978656016) (lo := 977656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w254 : ∀ j : ℕ, 489328009 ≤ j → j < 489828009 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 978656018) (x1 := 979656016) (lo := 978656087) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w255 : ∀ j : ℕ, 489828009 ≤ j → j < 489950633 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 979656018) (x1 := 979901264) (lo := 979656087) (W := 378569)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w256 : ∀ j : ℕ, 489950634 ≤ j → j < 490450634 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 979901268) (x1 := 980901266) (lo := 979901337) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w257 : ∀ j : ℕ, 490450634 ≤ j → j < 490860984 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 980901268) (x1 := 981721966) (lo := 980901337) (W := 954021)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w258 : ∀ j : ℕ, 490860985 ≤ j → j < 491360985 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 981721970) (x1 := 982721968) (lo := 981722039) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w259 : ∀ j : ℕ, 491360985 ≤ j → j < 491382483 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 982721970) (x1 := 982764964) (lo := 982722039) (W := 176317)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w260 : ∀ j : ℕ, 491382484 ≤ j → j < 491882484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 982764968) (x1 := 983764966) (lo := 982765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w261 : ∀ j : ℕ, 491882484 ≤ j → j < 492382484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 983764968) (x1 := 984764966) (lo := 983765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w262 : ∀ j : ℕ, 492382484 ≤ j → j < 492882484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 984764968) (x1 := 985764966) (lo := 984765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w263 : ∀ j : ℕ, 492882484 ≤ j → j < 493382484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 985764968) (x1 := 986764966) (lo := 985765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w264 : ∀ j : ℕ, 493382484 ≤ j → j < 493882484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 986764968) (x1 := 987764966) (lo := 986765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w265 : ∀ j : ℕ, 493882484 ≤ j → j < 494382484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 987764968) (x1 := 988764966) (lo := 987765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w266 : ∀ j : ℕ, 494382484 ≤ j → j < 494882484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 988764968) (x1 := 989764966) (lo := 988765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w267 : ∀ j : ℕ, 494882484 ≤ j → j < 495382484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 989764968) (x1 := 990764966) (lo := 989765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w268 : ∀ j : ℕ, 495382484 ≤ j → j < 495882484 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 990764968) (x1 := 991764966) (lo := 990765037) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w269 : ∀ j : ℕ, 495882484 ≤ j → j < 496245639 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 991764968) (x1 := 992491276) (lo := 991765037) (W := 859631)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w270 : ∀ j : ℕ, 496245640 ≤ j → j < 496745640 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 992491280) (x1 := 993491278) (lo := 992491349) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w271 : ∀ j : ℕ, 496745640 ≤ j → j < 497245640 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 993491280) (x1 := 994491278) (lo := 993491349) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w272 : ∀ j : ℕ, 497245640 ≤ j → j < 497745640 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 994491280) (x1 := 995491278) (lo := 994491349) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w273 : ∀ j : ℕ, 497745640 ≤ j → j < 498245640 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 995491280) (x1 := 996491278) (lo := 995491349) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w274 : ∀ j : ℕ, 498245640 ≤ j → j < 498745640 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 996491280) (x1 := 997491278) (lo := 996491349) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w275 : ∀ j : ℕ, 498745640 ≤ j → j < 499098783 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 997491280) (x1 := 998197564) (lo := 997491349) (W := 839607)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w276 : ∀ j : ℕ, 499098784 ≤ j → j < 499598784 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 998197568) (x1 := 999197566) (lo := 998197637) (W := 1133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w277 : ∀ j : ℕ, 499598784 ≤ j → j < 499800309 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 999197568) (x1 := 999600616) (lo := 999197637) (W := 536371)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b4w278 : ∀ j : ℕ, 499800310 ≤ j → j < 500000001 →
    ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 999600620) (x1 := 1000000000) (lo := 999600689) (W := 532703)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

private theorem b3all :
    ∀ j : ℕ, 250000000 ≤ j → j < 375000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases c0 : j < 250500000
  · exact b3w0 j (by omega) c0
  by_cases c1 : j < 251000000
  · exact b3w1 j (by omega) c1
  by_cases c2 : j < 251500000
  · exact b3w2 j (by omega) c2
  by_cases c3 : j < 252000000
  · exact b3w3 j (by omega) c3
  by_cases c4 : j < 252500000
  · exact b3w4 j (by omega) c4
  by_cases c5 : j < 253000000
  · exact b3w5 j (by omega) c5
  by_cases c6 : j < 253500000
  · exact b3w6 j (by omega) c6
  by_cases c7 : j < 254000000
  · exact b3w7 j (by omega) c7
  by_cases c8 : j < 254500000
  · exact b3w8 j (by omega) c8
  by_cases c9 : j < 255000000
  · exact b3w9 j (by omega) c9
  by_cases c10 : j < 255500000
  · exact b3w10 j (by omega) c10
  by_cases c11 : j < 256000000
  · exact b3w11 j (by omega) c11
  by_cases c12 : j < 256264271
  · exact b3w12 j (by omega) c12
  by_cases c13 : j < 256264272
  · obtain rfl : j = 256264271 := by omega
    exact resid_256264271
  by_cases c14 : j < 256764272
  · exact b3w13 j (by omega) c14
  by_cases c15 : j < 257264272
  · exact b3w14 j (by omega) c15
  by_cases c16 : j < 257764272
  · exact b3w15 j (by omega) c16
  by_cases c17 : j < 258264272
  · exact b3w16 j (by omega) c17
  by_cases c18 : j < 258764272
  · exact b3w17 j (by omega) c18
  by_cases c19 : j < 259264272
  · exact b3w18 j (by omega) c19
  by_cases c20 : j < 259764272
  · exact b3w19 j (by omega) c20
  by_cases c21 : j < 260264272
  · exact b3w20 j (by omega) c21
  by_cases c22 : j < 260764272
  · exact b3w21 j (by omega) c22
  by_cases c23 : j < 261264272
  · exact b3w22 j (by omega) c23
  by_cases c24 : j < 261764272
  · exact b3w23 j (by omega) c24
  by_cases c25 : j < 262264272
  · exact b3w24 j (by omega) c25
  by_cases c26 : j < 262764272
  · exact b3w25 j (by omega) c26
  by_cases c27 : j < 263264272
  · exact b3w26 j (by omega) c27
  by_cases c28 : j < 263513682
  · exact b3w27 j (by omega) c28
  by_cases c29 : j < 263513683
  · obtain rfl : j = 263513682 := by omega
    exact resid_263513682
  by_cases c30 : j < 264013683
  · exact b3w28 j (by omega) c30
  by_cases c31 : j < 264513683
  · exact b3w29 j (by omega) c31
  by_cases c32 : j < 265013683
  · exact b3w30 j (by omega) c32
  by_cases c33 : j < 265513683
  · exact b3w31 j (by omega) c33
  by_cases c34 : j < 265573404
  · exact b3w32 j (by omega) c34
  by_cases c35 : j < 265573405
  · obtain rfl : j = 265573404 := by omega
    exact resid_265573404
  by_cases c36 : j < 266073405
  · exact b3w33 j (by omega) c36
  by_cases c37 : j < 266573405
  · exact b3w34 j (by omega) c37
  by_cases c38 : j < 267073405
  · exact b3w35 j (by omega) c38
  by_cases c39 : j < 267573405
  · exact b3w36 j (by omega) c39
  by_cases c40 : j < 268073405
  · exact b3w37 j (by omega) c40
  by_cases c41 : j < 268573405
  · exact b3w38 j (by omega) c41
  by_cases c42 : j < 269073405
  · exact b3w39 j (by omega) c42
  by_cases c43 : j < 269338358
  · exact b3w40 j (by omega) c43
  by_cases c44 : j < 269338359
  · obtain rfl : j = 269338358 := by omega
    exact resid_269338358
  by_cases c45 : j < 269838359
  · exact b3w41 j (by omega) c45
  by_cases c46 : j < 270338359
  · exact b3w42 j (by omega) c46
  by_cases c47 : j < 270838359
  · exact b3w43 j (by omega) c47
  by_cases c48 : j < 271338359
  · exact b3w44 j (by omega) c48
  by_cases c49 : j < 271560938
  · exact b3w45 j (by omega) c49
  by_cases c50 : j < 271560939
  · obtain rfl : j = 271560938 := by omega
    exact resid_271560938
  by_cases c51 : j < 271861224
  · exact b3w46 j (by omega) c51
  by_cases c52 : j < 271861225
  · obtain rfl : j = 271861224 := by omega
    exact resid_271861224
  by_cases c53 : j < 272175399
  · exact b3w47 j (by omega) c53
  by_cases c54 : j < 272175400
  · obtain rfl : j = 272175399 := by omega
    exact resid_272175399
  by_cases c55 : j < 272354738
  · exact b3w48 j (by omega) c55
  by_cases c56 : j < 272354739
  · obtain rfl : j = 272354738 := by omega
    exact resid_272354738
  by_cases c57 : j < 272854739
  · exact b3w49 j (by omega) c57
  by_cases c58 : j < 273354739
  · exact b3w50 j (by omega) c58
  by_cases c59 : j < 273854739
  · exact b3w51 j (by omega) c59
  by_cases c60 : j < 274354739
  · exact b3w52 j (by omega) c60
  by_cases c61 : j < 274854739
  · exact b3w53 j (by omega) c61
  by_cases c62 : j < 275354739
  · exact b3w54 j (by omega) c62
  by_cases c63 : j < 275854739
  · exact b3w55 j (by omega) c63
  by_cases c64 : j < 276354739
  · exact b3w56 j (by omega) c64
  by_cases c65 : j < 276854739
  · exact b3w57 j (by omega) c65
  by_cases c66 : j < 277354739
  · exact b3w58 j (by omega) c66
  by_cases c67 : j < 277854739
  · exact b3w59 j (by omega) c67
  by_cases c68 : j < 278354739
  · exact b3w60 j (by omega) c68
  by_cases c69 : j < 278854739
  · exact b3w61 j (by omega) c69
  by_cases c70 : j < 279354739
  · exact b3w62 j (by omega) c70
  by_cases c71 : j < 279854739
  · exact b3w63 j (by omega) c71
  by_cases c72 : j < 280354739
  · exact b3w64 j (by omega) c72
  by_cases c73 : j < 280647912
  · exact b3w65 j (by omega) c73
  by_cases c74 : j < 280647913
  · obtain rfl : j = 280647912 := by omega
    exact resid_280647912
  by_cases c75 : j < 281147913
  · exact b3w66 j (by omega) c75
  by_cases c76 : j < 281647913
  · exact b3w67 j (by omega) c76
  by_cases c77 : j < 281971479
  · exact b3w68 j (by omega) c77
  by_cases c78 : j < 281971480
  · obtain rfl : j = 281971479 := by omega
    exact resid_281971479
  by_cases c79 : j < 282471480
  · exact b3w69 j (by omega) c79
  by_cases c80 : j < 282971480
  · exact b3w70 j (by omega) c80
  by_cases c81 : j < 283471480
  · exact b3w71 j (by omega) c81
  by_cases c82 : j < 283971480
  · exact b3w72 j (by omega) c82
  by_cases c83 : j < 284199837
  · exact b3w73 j (by omega) c83
  by_cases c84 : j < 284199838
  · obtain rfl : j = 284199837 := by omega
    exact resid_284199837
  by_cases c85 : j < 284699838
  · exact b3w74 j (by omega) c85
  by_cases c86 : j < 285199838
  · exact b3w75 j (by omega) c86
  by_cases c87 : j < 285699838
  · exact b3w76 j (by omega) c87
  by_cases c88 : j < 286199838
  · exact b3w77 j (by omega) c88
  by_cases c89 : j < 286699838
  · exact b3w78 j (by omega) c89
  by_cases c90 : j < 287199838
  · exact b3w79 j (by omega) c90
  by_cases c91 : j < 287699838
  · exact b3w80 j (by omega) c91
  by_cases c92 : j < 288199838
  · exact b3w81 j (by omega) c92
  by_cases c93 : j < 288699838
  · exact b3w82 j (by omega) c93
  by_cases c94 : j < 289199838
  · exact b3w83 j (by omega) c94
  by_cases c95 : j < 289699838
  · exact b3w84 j (by omega) c95
  by_cases c96 : j < 290199838
  · exact b3w85 j (by omega) c96
  by_cases c97 : j < 290699838
  · exact b3w86 j (by omega) c97
  by_cases c98 : j < 291199838
  · exact b3w87 j (by omega) c98
  by_cases c99 : j < 291699838
  · exact b3w88 j (by omega) c99
  by_cases c100 : j < 292199838
  · exact b3w89 j (by omega) c100
  by_cases c101 : j < 292699838
  · exact b3w90 j (by omega) c101
  by_cases c102 : j < 293187012
  · exact b3w91 j (by omega) c102
  by_cases c103 : j < 293187013
  · obtain rfl : j = 293187012 := by omega
    exact resid_293187012
  by_cases c104 : j < 293495298
  · exact b3w92 j (by omega) c104
  by_cases c105 : j < 293495299
  · obtain rfl : j = 293495298 := by omega
    exact resid_293495298
  by_cases c106 : j < 293799606
  · exact b3w93 j (by omega) c106
  by_cases c107 : j < 293799607
  · obtain rfl : j = 293799606 := by omega
    exact resid_293799606
  by_cases c108 : j < 294299607
  · exact b3w94 j (by omega) c108
  by_cases c109 : j < 294799607
  · exact b3w95 j (by omega) c109
  by_cases c110 : j < 295299607
  · exact b3w96 j (by omega) c110
  by_cases c111 : j < 295799607
  · exact b3w97 j (by omega) c111
  by_cases c112 : j < 296299607
  · exact b3w98 j (by omega) c112
  by_cases c113 : j < 296799607
  · exact b3w99 j (by omega) c113
  by_cases c114 : j < 297299607
  · exact b3w100 j (by omega) c114
  by_cases c115 : j < 297598662
  · exact b3w101 j (by omega) c115
  by_cases c116 : j < 297598663
  · obtain rfl : j = 297598662 := by omega
    exact resid_297598662
  by_cases c117 : j < 298098663
  · exact b3w102 j (by omega) c117
  by_cases c118 : j < 298598663
  · exact b3w103 j (by omega) c118
  by_cases c119 : j < 299098663
  · exact b3w104 j (by omega) c119
  by_cases c120 : j < 299598663
  · exact b3w105 j (by omega) c120
  by_cases c121 : j < 300098663
  · exact b3w106 j (by omega) c121
  by_cases c122 : j < 300598663
  · exact b3w107 j (by omega) c122
  by_cases c123 : j < 301098663
  · exact b3w108 j (by omega) c123
  by_cases c124 : j < 301598663
  · exact b3w109 j (by omega) c124
  by_cases c125 : j < 302098663
  · exact b3w110 j (by omega) c125
  by_cases c126 : j < 302598663
  · exact b3w111 j (by omega) c126
  by_cases c127 : j < 303098663
  · exact b3w112 j (by omega) c127
  by_cases c128 : j < 303598663
  · exact b3w113 j (by omega) c128
  by_cases c129 : j < 304098663
  · exact b3w114 j (by omega) c129
  by_cases c130 : j < 304598663
  · exact b3w115 j (by omega) c130
  by_cases c131 : j < 305098663
  · exact b3w116 j (by omega) c131
  by_cases c132 : j < 305598663
  · exact b3w117 j (by omega) c132
  by_cases c133 : j < 306098663
  · exact b3w118 j (by omega) c133
  by_cases c134 : j < 306598663
  · exact b3w119 j (by omega) c134
  by_cases c135 : j < 306886241
  · exact b3w120 j (by omega) c135
  by_cases c136 : j < 306886242
  · obtain rfl : j = 306886241 := by omega
    exact resid_306886241
  by_cases c137 : j < 307386242
  · exact b3w121 j (by omega) c137
  by_cases c138 : j < 307886242
  · exact b3w122 j (by omega) c138
  by_cases c139 : j < 308386242
  · exact b3w123 j (by omega) c139
  by_cases c140 : j < 308391528
  · exact b3w124 j (by omega) c140
  by_cases c141 : j < 308391529
  · obtain rfl : j = 308391528 := by omega
    exact resid_308391528
  by_cases c142 : j < 308891529
  · exact b3w125 j (by omega) c142
  by_cases c143 : j < 309391529
  · exact b3w126 j (by omega) c143
  by_cases c144 : j < 309891529
  · exact b3w127 j (by omega) c144
  by_cases c145 : j < 309928518
  · exact b3w128 j (by omega) c145
  by_cases c146 : j < 309928519
  · obtain rfl : j = 309928518 := by omega
    exact resid_309928518
  by_cases c147 : j < 310067844
  · exact b3w129 j (by omega) c147
  by_cases c148 : j < 310067845
  · obtain rfl : j = 310067844 := by omega
    exact resid_310067844
  by_cases c149 : j < 310559547
  · exact b3w130 j (by omega) c149
  by_cases c150 : j < 310559548
  · obtain rfl : j = 310559547 := by omega
    exact resid_310559547
  by_cases c151 : j < 311059548
  · exact b3w131 j (by omega) c151
  by_cases c152 : j < 311559548
  · exact b3w132 j (by omega) c152
  by_cases c153 : j < 312059548
  · exact b3w133 j (by omega) c153
  by_cases c154 : j < 312559548
  · exact b3w134 j (by omega) c154
  by_cases c155 : j < 313059548
  · exact b3w135 j (by omega) c155
  by_cases c156 : j < 313559548
  · exact b3w136 j (by omega) c156
  by_cases c157 : j < 314059548
  · exact b3w137 j (by omega) c157
  by_cases c158 : j < 314559548
  · exact b3w138 j (by omega) c158
  by_cases c159 : j < 315059548
  · exact b3w139 j (by omega) c159
  by_cases c160 : j < 315559548
  · exact b3w140 j (by omega) c160
  by_cases c161 : j < 316059548
  · exact b3w141 j (by omega) c161
  by_cases c162 : j < 316559548
  · exact b3w142 j (by omega) c162
  by_cases c163 : j < 317059548
  · exact b3w143 j (by omega) c163
  by_cases c164 : j < 317559548
  · exact b3w144 j (by omega) c164
  by_cases c165 : j < 317858307
  · exact b3w145 j (by omega) c165
  by_cases c166 : j < 317858308
  · obtain rfl : j = 317858307 := by omega
    exact resid_317858307
  by_cases c167 : j < 318147687
  · exact b3w146 j (by omega) c167
  by_cases c168 : j < 318147688
  · obtain rfl : j = 318147687 := by omega
    exact resid_318147687
  by_cases c169 : j < 318647688
  · exact b3w147 j (by omega) c169
  by_cases c170 : j < 319147688
  · exact b3w148 j (by omega) c170
  by_cases c171 : j < 319647688
  · exact b3w149 j (by omega) c171
  by_cases c172 : j < 320147688
  · exact b3w150 j (by omega) c172
  by_cases c173 : j < 320647688
  · exact b3w151 j (by omega) c173
  by_cases c174 : j < 321147688
  · exact b3w152 j (by omega) c174
  by_cases c175 : j < 321647688
  · exact b3w153 j (by omega) c175
  by_cases c176 : j < 322046337
  · exact b3w154 j (by omega) c176
  by_cases c177 : j < 322046338
  · obtain rfl : j = 322046337 := by omega
    exact resid_322046337
  by_cases c178 : j < 322131927
  · exact b3w155 j (by omega) c178
  by_cases c179 : j < 322131928
  · obtain rfl : j = 322131927 := by omega
    exact resid_322131927
  by_cases c180 : j < 322631928
  · exact b3w156 j (by omega) c180
  by_cases c181 : j < 323131928
  · exact b3w157 j (by omega) c181
  by_cases c182 : j < 323601443
  · exact b3w158 j (by omega) c182
  by_cases c183 : j < 323601444
  · obtain rfl : j = 323601443 := by omega
    exact resid_323601443
  by_cases c184 : j < 324101444
  · exact b3w159 j (by omega) c184
  by_cases c185 : j < 324286212
  · exact b3w160 j (by omega) c185
  by_cases c186 : j < 324286213
  · obtain rfl : j = 324286212 := by omega
    exact resid_324286212
  by_cases c187 : j < 324673236
  · exact b3w161 j (by omega) c187
  by_cases c188 : j < 324673237
  · obtain rfl : j = 324673236 := by omega
    exact resid_324673236
  by_cases c189 : j < 325173237
  · exact b3w162 j (by omega) c189
  by_cases c190 : j < 325481874
  · exact b3w163 j (by omega) c190
  by_cases c191 : j < 325481875
  · obtain rfl : j = 325481874 := by omega
    exact resid_325481874
  by_cases c192 : j < 325981875
  · exact b3w164 j (by omega) c192
  by_cases c193 : j < 326481875
  · exact b3w165 j (by omega) c193
  by_cases c194 : j < 326981875
  · exact b3w166 j (by omega) c194
  by_cases c195 : j < 327481875
  · exact b3w167 j (by omega) c195
  by_cases c196 : j < 327981875
  · exact b3w168 j (by omega) c196
  by_cases c197 : j < 328481875
  · exact b3w169 j (by omega) c197
  by_cases c198 : j < 328981875
  · exact b3w170 j (by omega) c198
  by_cases c199 : j < 329314437
  · exact b3w171 j (by omega) c199
  by_cases c200 : j < 329314438
  · obtain rfl : j = 329314437 := by omega
    exact resid_329314437
  by_cases c201 : j < 329814438
  · exact b3w172 j (by omega) c201
  by_cases c202 : j < 330314438
  · exact b3w173 j (by omega) c202
  by_cases c203 : j < 330814438
  · exact b3w174 j (by omega) c203
  by_cases c204 : j < 331314438
  · exact b3w175 j (by omega) c204
  by_cases c205 : j < 331814438
  · exact b3w176 j (by omega) c205
  by_cases c206 : j < 332314438
  · exact b3w177 j (by omega) c206
  by_cases c207 : j < 332589453
  · exact b3w178 j (by omega) c207
  by_cases c208 : j < 332589454
  · obtain rfl : j = 332589453 := by omega
    exact resid_332589453
  by_cases c209 : j < 333089454
  · exact b3w179 j (by omega) c209
  by_cases c210 : j < 333524694
  · exact b3w180 j (by omega) c210
  by_cases c211 : j < 333524695
  · obtain rfl : j = 333524694 := by omega
    exact resid_333524694
  by_cases c212 : j < 334024695
  · exact b3w181 j (by omega) c212
  by_cases c213 : j < 334524695
  · exact b3w182 j (by omega) c213
  by_cases c214 : j < 335024695
  · exact b3w183 j (by omega) c214
  by_cases c215 : j < 335524695
  · exact b3w184 j (by omega) c215
  by_cases c216 : j < 336024695
  · exact b3w185 j (by omega) c216
  by_cases c217 : j < 336524695
  · exact b3w186 j (by omega) c217
  by_cases c218 : j < 337024695
  · exact b3w187 j (by omega) c218
  by_cases c219 : j < 337088049
  · exact b3w188 j (by omega) c219
  by_cases c220 : j < 337088050
  · obtain rfl : j = 337088049 := by omega
    exact resid_337088049
  by_cases c221 : j < 337588050
  · exact b3w189 j (by omega) c221
  by_cases c222 : j < 338088050
  · exact b3w190 j (by omega) c222
  by_cases c223 : j < 338588050
  · exact b3w191 j (by omega) c223
  by_cases c224 : j < 338766068
  · exact b3w192 j (by omega) c224
  by_cases c225 : j < 338766069
  · obtain rfl : j = 338766068 := by omega
    exact resid_338766068
  by_cases c226 : j < 339266069
  · exact b3w193 j (by omega) c226
  by_cases c227 : j < 339540369
  · exact b3w194 j (by omega) c227
  by_cases c228 : j < 339540370
  · obtain rfl : j = 339540369 := by omega
    exact resid_339540369
  by_cases c229 : j < 340040370
  · exact b3w195 j (by omega) c229
  by_cases c230 : j < 340540370
  · exact b3w196 j (by omega) c230
  by_cases c231 : j < 341040370
  · exact b3w197 j (by omega) c231
  by_cases c232 : j < 341484933
  · exact b3w198 j (by omega) c232
  by_cases c233 : j < 341484934
  · obtain rfl : j = 341484933 := by omega
    exact resid_341484933
  by_cases c234 : j < 341984934
  · exact b3w199 j (by omega) c234
  by_cases c235 : j < 342484934
  · exact b3w200 j (by omega) c235
  by_cases c236 : j < 342984934
  · exact b3w201 j (by omega) c236
  by_cases c237 : j < 343484934
  · exact b3w202 j (by omega) c237
  by_cases c238 : j < 343984934
  · exact b3w203 j (by omega) c238
  by_cases c239 : j < 344484934
  · exact b3w204 j (by omega) c239
  by_cases c240 : j < 344984934
  · exact b3w205 j (by omega) c240
  by_cases c241 : j < 345484934
  · exact b3w206 j (by omega) c241
  by_cases c242 : j < 345984934
  · exact b3w207 j (by omega) c242
  by_cases c243 : j < 346484934
  · exact b3w208 j (by omega) c243
  by_cases c244 : j < 346627713
  · exact b3w209 j (by omega) c244
  by_cases c245 : j < 346627714
  · obtain rfl : j = 346627713 := by omega
    exact resid_346627713
  by_cases c246 : j < 347127714
  · exact b3w210 j (by omega) c246
  by_cases c247 : j < 347627714
  · exact b3w211 j (by omega) c247
  by_cases c248 : j < 348127714
  · exact b3w212 j (by omega) c248
  by_cases c249 : j < 348627714
  · exact b3w213 j (by omega) c249
  by_cases c250 : j < 349127714
  · exact b3w214 j (by omega) c250
  by_cases c251 : j < 349455987
  · exact b3w215 j (by omega) c251
  by_cases c252 : j < 349455988
  · obtain rfl : j = 349455987 := by omega
    exact resid_349455987
  by_cases c253 : j < 349955988
  · exact b3w216 j (by omega) c253
  by_cases c254 : j < 350455988
  · exact b3w217 j (by omega) c254
  by_cases c255 : j < 350955988
  · exact b3w218 j (by omega) c255
  by_cases c256 : j < 351455988
  · exact b3w219 j (by omega) c256
  by_cases c257 : j < 351955988
  · exact b3w220 j (by omega) c257
  by_cases c258 : j < 352146954
  · exact b3w221 j (by omega) c258
  by_cases c259 : j < 352146955
  · obtain rfl : j = 352146954 := by omega
    exact resid_352146954
  by_cases c260 : j < 352646955
  · exact b3w222 j (by omega) c260
  by_cases c261 : j < 353146955
  · exact b3w223 j (by omega) c261
  by_cases c262 : j < 353646955
  · exact b3w224 j (by omega) c262
  by_cases c263 : j < 354146955
  · exact b3w225 j (by omega) c263
  by_cases c264 : j < 354646955
  · exact b3w226 j (by omega) c264
  by_cases c265 : j < 355146955
  · exact b3w227 j (by omega) c265
  by_cases c266 : j < 355646955
  · exact b3w228 j (by omega) c266
  by_cases c267 : j < 356146955
  · exact b3w229 j (by omega) c267
  by_cases c268 : j < 356646955
  · exact b3w230 j (by omega) c268
  by_cases c269 : j < 357146955
  · exact b3w231 j (by omega) c269
  by_cases c270 : j < 357646955
  · exact b3w232 j (by omega) c270
  by_cases c271 : j < 358146955
  · exact b3w233 j (by omega) c271
  by_cases c272 : j < 358646955
  · exact b3w234 j (by omega) c272
  by_cases c273 : j < 359146955
  · exact b3w235 j (by omega) c273
  by_cases c274 : j < 359588094
  · exact b3w236 j (by omega) c274
  by_cases c275 : j < 359588095
  · obtain rfl : j = 359588094 := by omega
    exact resid_359588094
  by_cases c276 : j < 360088095
  · exact b3w237 j (by omega) c276
  by_cases c277 : j < 360588095
  · exact b3w238 j (by omega) c277
  by_cases c278 : j < 360864942
  · exact b3w239 j (by omega) c278
  by_cases c279 : j < 360864943
  · obtain rfl : j = 360864942 := by omega
    exact resid_360864942
  by_cases c280 : j < 361364943
  · exact b3w240 j (by omega) c280
  by_cases c281 : j < 361509321
  · exact b3w241 j (by omega) c281
  by_cases c282 : j < 361509322
  · obtain rfl : j = 361509321 := by omega
    exact resid_361509321
  by_cases c283 : j < 362009322
  · exact b3w242 j (by omega) c283
  by_cases c284 : j < 362044779
  · exact b3w243 j (by omega) c284
  by_cases c285 : j < 362044780
  · obtain rfl : j = 362044779 := by omega
    exact resid_362044779
  by_cases c286 : j < 362544780
  · exact b3w244 j (by omega) c286
  by_cases c287 : j < 363044780
  · exact b3w245 j (by omega) c287
  by_cases c288 : j < 363307872
  · exact b3w246 j (by omega) c288
  by_cases c289 : j < 363307873
  · obtain rfl : j = 363307872 := by omega
    exact resid_363307872
  by_cases c290 : j < 363807873
  · exact b3w247 j (by omega) c290
  by_cases c291 : j < 363929721
  · exact b3w248 j (by omega) c291
  by_cases c292 : j < 363929722
  · obtain rfl : j = 363929721 := by omega
    exact resid_363929721
  by_cases c293 : j < 364429722
  · exact b3w249 j (by omega) c293
  by_cases c294 : j < 364929722
  · exact b3w250 j (by omega) c294
  by_cases c295 : j < 365429722
  · exact b3w251 j (by omega) c295
  by_cases c296 : j < 365929722
  · exact b3w252 j (by omega) c296
  by_cases c297 : j < 366429722
  · exact b3w253 j (by omega) c297
  by_cases c298 : j < 366929722
  · exact b3w254 j (by omega) c298
  by_cases c299 : j < 367429722
  · exact b3w255 j (by omega) c299
  by_cases c300 : j < 367929722
  · exact b3w256 j (by omega) c300
  by_cases c301 : j < 368052738
  · exact b3w257 j (by omega) c301
  by_cases c302 : j < 368052739
  · obtain rfl : j = 368052738 := by omega
    exact resid_368052738
  by_cases c303 : j < 368552739
  · exact b3w258 j (by omega) c303
  by_cases c304 : j < 368706636
  · exact b3w259 j (by omega) c304
  by_cases c305 : j < 368706637
  · obtain rfl : j = 368706636 := by omega
    exact resid_368706636
  by_cases c306 : j < 368896868
  · exact b3w260 j (by omega) c306
  by_cases c307 : j < 368896869
  · obtain rfl : j = 368896868 := by omega
    exact resid_368896868
  by_cases c308 : j < 369396869
  · exact b3w261 j (by omega) c308
  by_cases c309 : j < 369896869
  · exact b3w262 j (by omega) c309
  by_cases c310 : j < 370221216
  · exact b3w263 j (by omega) c310
  by_cases c311 : j < 370221217
  · obtain rfl : j = 370221216 := by omega
    exact resid_370221216
  by_cases c312 : j < 370721217
  · exact b3w264 j (by omega) c312
  by_cases c313 : j < 371221217
  · exact b3w265 j (by omega) c313
  by_cases c314 : j < 371721217
  · exact b3w266 j (by omega) c314
  by_cases c315 : j < 372221217
  · exact b3w267 j (by omega) c315
  by_cases c316 : j < 372721217
  · exact b3w268 j (by omega) c316
  by_cases c317 : j < 373221217
  · exact b3w269 j (by omega) c317
  by_cases c318 : j < 373647957
  · exact b3w270 j (by omega) c318
  by_cases c319 : j < 373647958
  · obtain rfl : j = 373647957 := by omega
    exact resid_373647957
  by_cases c320 : j < 374147958
  · exact b3w271 j (by omega) c320
  by_cases c321 : j < 374647958
  · exact b3w272 j (by omega) c321
  by_cases c322 : j < 374732334
  · exact b3w273 j (by omega) c322
  by_cases c323 : j < 374732335
  · obtain rfl : j = 374732334 := by omega
    exact resid_374732334
  by_cases c324 : j < 374917002
  · exact b3w274 j (by omega) c324
  by_cases c325 : j < 374917003
  · obtain rfl : j = 374917002 := by omega
    exact resid_374917002
  · exact b3w275 j (by omega) hj1

private theorem b4all :
    ∀ j : ℕ, 375000000 ≤ j → j < 500000001 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases c0 : j < 375500000
  · exact b4w0 j (by omega) c0
  by_cases c1 : j < 375844802
  · exact b4w1 j (by omega) c1
  by_cases c2 : j < 375844803
  · obtain rfl : j = 375844802 := by omega
    exact resid_375844802
  by_cases c3 : j < 376344803
  · exact b4w2 j (by omega) c3
  by_cases c4 : j < 376494336
  · exact b4w3 j (by omega) c4
  by_cases c5 : j < 376494337
  · obtain rfl : j = 376494336 := by omega
    exact resid_376494336
  by_cases c6 : j < 376763487
  · exact b4w4 j (by omega) c6
  by_cases c7 : j < 376763488
  · obtain rfl : j = 376763487 := by omega
    exact resid_376763487
  by_cases c8 : j < 377263488
  · exact b4w5 j (by omega) c8
  by_cases c9 : j < 377763488
  · exact b4w6 j (by omega) c9
  by_cases c10 : j < 378263488
  · exact b4w7 j (by omega) c10
  by_cases c11 : j < 378763488
  · exact b4w8 j (by omega) c11
  by_cases c12 : j < 379263488
  · exact b4w9 j (by omega) c12
  by_cases c13 : j < 379763488
  · exact b4w10 j (by omega) c13
  by_cases c14 : j < 380263488
  · exact b4w11 j (by omega) c14
  by_cases c15 : j < 380755164
  · exact b4w12 j (by omega) c15
  by_cases c16 : j < 380755165
  · obtain rfl : j = 380755164 := by omega
    exact resid_380755164
  by_cases c17 : j < 381255165
  · exact b4w13 j (by omega) c17
  by_cases c18 : j < 381755165
  · exact b4w14 j (by omega) c18
  by_cases c19 : j < 382255165
  · exact b4w15 j (by omega) c19
  by_cases c20 : j < 382755165
  · exact b4w16 j (by omega) c20
  by_cases c21 : j < 383255165
  · exact b4w17 j (by omega) c21
  by_cases c22 : j < 383260149
  · exact b4w18 j (by omega) c22
  by_cases c23 : j < 383260150
  · obtain rfl : j = 383260149 := by omega
    exact resid_383260149
  by_cases c24 : j < 383760150
  · exact b4w19 j (by omega) c24
  by_cases c25 : j < 384260150
  · exact b4w20 j (by omega) c25
  by_cases c26 : j < 384760150
  · exact b4w21 j (by omega) c26
  by_cases c27 : j < 384927662
  · exact b4w22 j (by omega) c27
  by_cases c28 : j < 384927663
  · obtain rfl : j = 384927662 := by omega
    exact resid_384927662
  by_cases c29 : j < 385289202
  · exact b4w23 j (by omega) c29
  by_cases c30 : j < 385289203
  · obtain rfl : j = 385289202 := by omega
    exact resid_385289202
  by_cases c31 : j < 385789203
  · exact b4w24 j (by omega) c31
  by_cases c32 : j < 386289203
  · exact b4w25 j (by omega) c32
  by_cases c33 : j < 386290587
  · exact b4w26 j (by omega) c33
  by_cases c34 : j < 386290588
  · obtain rfl : j = 386290587 := by omega
    exact resid_386290587
  by_cases c35 : j < 386790588
  · exact b4w27 j (by omega) c35
  by_cases c36 : j < 387290588
  · exact b4w28 j (by omega) c36
  by_cases c37 : j < 387790588
  · exact b4w29 j (by omega) c37
  by_cases c38 : j < 388290588
  · exact b4w30 j (by omega) c38
  by_cases c39 : j < 388790588
  · exact b4w31 j (by omega) c39
  by_cases c40 : j < 389290588
  · exact b4w32 j (by omega) c40
  by_cases c41 : j < 389790588
  · exact b4w33 j (by omega) c41
  by_cases c42 : j < 390290588
  · exact b4w34 j (by omega) c42
  by_cases c43 : j < 390790588
  · exact b4w35 j (by omega) c43
  by_cases c44 : j < 391290588
  · exact b4w36 j (by omega) c44
  by_cases c45 : j < 391790588
  · exact b4w37 j (by omega) c45
  by_cases c46 : j < 392290588
  · exact b4w38 j (by omega) c46
  by_cases c47 : j < 392790588
  · exact b4w39 j (by omega) c47
  by_cases c48 : j < 392883824
  · exact b4w40 j (by omega) c48
  by_cases c49 : j < 392883825
  · obtain rfl : j = 392883824 := by omega
    exact resid_392883824
  by_cases c50 : j < 393383825
  · exact b4w41 j (by omega) c50
  by_cases c51 : j < 393826194
  · exact b4w42 j (by omega) c51
  by_cases c52 : j < 393826195
  · obtain rfl : j = 393826194 := by omega
    exact resid_393826194
  by_cases c53 : j < 394326195
  · exact b4w43 j (by omega) c53
  by_cases c54 : j < 394826195
  · exact b4w44 j (by omega) c54
  by_cases c55 : j < 395326195
  · exact b4w45 j (by omega) c55
  by_cases c56 : j < 395826195
  · exact b4w46 j (by omega) c56
  by_cases c57 : j < 396326195
  · exact b4w47 j (by omega) c57
  by_cases c58 : j < 396826195
  · exact b4w48 j (by omega) c58
  by_cases c59 : j < 397326195
  · exact b4w49 j (by omega) c59
  by_cases c60 : j < 397826195
  · exact b4w50 j (by omega) c60
  by_cases c61 : j < 398326195
  · exact b4w51 j (by omega) c61
  by_cases c62 : j < 398826195
  · exact b4w52 j (by omega) c62
  by_cases c63 : j < 399326195
  · exact b4w53 j (by omega) c63
  by_cases c64 : j < 399826195
  · exact b4w54 j (by omega) c64
  by_cases c65 : j < 400326195
  · exact b4w55 j (by omega) c65
  by_cases c66 : j < 400826195
  · exact b4w56 j (by omega) c66
  by_cases c67 : j < 401326195
  · exact b4w57 j (by omega) c67
  by_cases c68 : j < 401826195
  · exact b4w58 j (by omega) c68
  by_cases c69 : j < 402158154
  · exact b4w59 j (by omega) c69
  by_cases c70 : j < 402158155
  · obtain rfl : j = 402158154 := by omega
    exact resid_402158154
  by_cases c71 : j < 402658155
  · exact b4w60 j (by omega) c71
  by_cases c72 : j < 403158155
  · exact b4w61 j (by omega) c72
  by_cases c73 : j < 403658155
  · exact b4w62 j (by omega) c73
  by_cases c74 : j < 404158155
  · exact b4w63 j (by omega) c74
  by_cases c75 : j < 404658155
  · exact b4w64 j (by omega) c75
  by_cases c76 : j < 405158155
  · exact b4w65 j (by omega) c76
  by_cases c77 : j < 405658155
  · exact b4w66 j (by omega) c77
  by_cases c78 : j < 406158155
  · exact b4w67 j (by omega) c78
  by_cases c79 : j < 406658155
  · exact b4w68 j (by omega) c79
  by_cases c80 : j < 407158155
  · exact b4w69 j (by omega) c80
  by_cases c81 : j < 407658155
  · exact b4w70 j (by omega) c81
  by_cases c82 : j < 408158155
  · exact b4w71 j (by omega) c82
  by_cases c83 : j < 408658155
  · exact b4w72 j (by omega) c83
  by_cases c84 : j < 409158155
  · exact b4w73 j (by omega) c84
  by_cases c85 : j < 409477073
  · exact b4w74 j (by omega) c85
  by_cases c86 : j < 409477074
  · obtain rfl : j = 409477073 := by omega
    exact resid_409477073
  by_cases c87 : j < 409977074
  · exact b4w75 j (by omega) c87
  by_cases c88 : j < 410477074
  · exact b4w76 j (by omega) c88
  by_cases c89 : j < 410977074
  · exact b4w77 j (by omega) c89
  by_cases c90 : j < 411477074
  · exact b4w78 j (by omega) c90
  by_cases c91 : j < 411977074
  · exact b4w79 j (by omega) c91
  by_cases c92 : j < 412477074
  · exact b4w80 j (by omega) c92
  by_cases c93 : j < 412977074
  · exact b4w81 j (by omega) c93
  by_cases c94 : j < 413477074
  · exact b4w82 j (by omega) c94
  by_cases c95 : j < 413977074
  · exact b4w83 j (by omega) c95
  by_cases c96 : j < 414477074
  · exact b4w84 j (by omega) c96
  by_cases c97 : j < 414977074
  · exact b4w85 j (by omega) c97
  by_cases c98 : j < 415477074
  · exact b4w86 j (by omega) c98
  by_cases c99 : j < 415977074
  · exact b4w87 j (by omega) c99
  by_cases c100 : j < 416477074
  · exact b4w88 j (by omega) c100
  by_cases c101 : j < 416977074
  · exact b4w89 j (by omega) c101
  by_cases c102 : j < 417477074
  · exact b4w90 j (by omega) c102
  by_cases c103 : j < 417977074
  · exact b4w91 j (by omega) c103
  by_cases c104 : j < 418414569
  · exact b4w92 j (by omega) c104
  by_cases c105 : j < 418414570
  · obtain rfl : j = 418414569 := by omega
    exact resid_418414569
  by_cases c106 : j < 418914570
  · exact b4w93 j (by omega) c106
  by_cases c107 : j < 419414570
  · exact b4w94 j (by omega) c107
  by_cases c108 : j < 419914570
  · exact b4w95 j (by omega) c108
  by_cases c109 : j < 420414570
  · exact b4w96 j (by omega) c109
  by_cases c110 : j < 420914570
  · exact b4w97 j (by omega) c110
  by_cases c111 : j < 421414570
  · exact b4w98 j (by omega) c111
  by_cases c112 : j < 421914570
  · exact b4w99 j (by omega) c112
  by_cases c113 : j < 422414570
  · exact b4w100 j (by omega) c113
  by_cases c114 : j < 422914570
  · exact b4w101 j (by omega) c114
  by_cases c115 : j < 423414570
  · exact b4w102 j (by omega) c115
  by_cases c116 : j < 423914570
  · exact b4w103 j (by omega) c116
  by_cases c117 : j < 424414570
  · exact b4w104 j (by omega) c117
  by_cases c118 : j < 424914570
  · exact b4w105 j (by omega) c118
  by_cases c119 : j < 425414570
  · exact b4w106 j (by omega) c119
  by_cases c120 : j < 425914570
  · exact b4w107 j (by omega) c120
  by_cases c121 : j < 426414570
  · exact b4w108 j (by omega) c121
  by_cases c122 : j < 426914570
  · exact b4w109 j (by omega) c122
  by_cases c123 : j < 427005129
  · exact b4w110 j (by omega) c123
  by_cases c124 : j < 427005130
  · obtain rfl : j = 427005129 := by omega
    exact resid_427005129
  by_cases c125 : j < 427505130
  · exact b4w111 j (by omega) c125
  by_cases c126 : j < 428005130
  · exact b4w112 j (by omega) c126
  by_cases c127 : j < 428476626
  · exact b4w113 j (by omega) c127
  by_cases c128 : j < 428476627
  · obtain rfl : j = 428476626 := by omega
    exact resid_428476626
  by_cases c129 : j < 428976627
  · exact b4w114 j (by omega) c129
  by_cases c130 : j < 429476627
  · exact b4w115 j (by omega) c130
  by_cases c131 : j < 429503382
  · exact b4w116 j (by omega) c131
  by_cases c132 : j < 429503383
  · obtain rfl : j = 429503382 := by omega
    exact resid_429503382
  by_cases c133 : j < 430003383
  · exact b4w117 j (by omega) c133
  by_cases c134 : j < 430503383
  · exact b4w118 j (by omega) c134
  by_cases c135 : j < 431003383
  · exact b4w119 j (by omega) c135
  by_cases c136 : j < 431503383
  · exact b4w120 j (by omega) c136
  by_cases c137 : j < 432003383
  · exact b4w121 j (by omega) c137
  by_cases c138 : j < 432132324
  · exact b4w122 j (by omega) c138
  by_cases c139 : j < 432132325
  · obtain rfl : j = 432132324 := by omega
    exact resid_432132324
  by_cases c140 : j < 432632325
  · exact b4w123 j (by omega) c140
  by_cases c141 : j < 433132325
  · exact b4w124 j (by omega) c141
  by_cases c142 : j < 433632325
  · exact b4w125 j (by omega) c142
  by_cases c143 : j < 433857234
  · exact b4w126 j (by omega) c143
  by_cases c144 : j < 433857235
  · obtain rfl : j = 433857234 := by omega
    exact resid_433857234
  by_cases c145 : j < 434110376
  · exact b4w127 j (by omega) c145
  by_cases c146 : j < 434110377
  · obtain rfl : j = 434110376 := by omega
    exact resid_434110376
  by_cases c147 : j < 434610377
  · exact b4w128 j (by omega) c147
  by_cases c148 : j < 434939817
  · exact b4w129 j (by omega) c148
  by_cases c149 : j < 434939818
  · obtain rfl : j = 434939817 := by omega
    exact resid_434939817
  by_cases c150 : j < 435439818
  · exact b4w130 j (by omega) c150
  by_cases c151 : j < 435939818
  · exact b4w131 j (by omega) c151
  by_cases c152 : j < 436439818
  · exact b4w132 j (by omega) c152
  by_cases c153 : j < 436939818
  · exact b4w133 j (by omega) c153
  by_cases c154 : j < 437439818
  · exact b4w134 j (by omega) c154
  by_cases c155 : j < 437558202
  · exact b4w135 j (by omega) c155
  by_cases c156 : j < 437558203
  · obtain rfl : j = 437558202 := by omega
    exact resid_437558202
  by_cases c157 : j < 438058203
  · exact b4w136 j (by omega) c157
  by_cases c158 : j < 438558203
  · exact b4w137 j (by omega) c158
  by_cases c159 : j < 439058203
  · exact b4w138 j (by omega) c159
  by_cases c160 : j < 439558203
  · exact b4w139 j (by omega) c160
  by_cases c161 : j < 440058203
  · exact b4w140 j (by omega) c161
  by_cases c162 : j < 440558203
  · exact b4w141 j (by omega) c162
  by_cases c163 : j < 440617812
  · exact b4w142 j (by omega) c163
  by_cases c164 : j < 440617813
  · obtain rfl : j = 440617812 := by omega
    exact resid_440617812
  by_cases c165 : j < 441117813
  · exact b4w143 j (by omega) c165
  by_cases c166 : j < 441617813
  · exact b4w144 j (by omega) c166
  by_cases c167 : j < 442117813
  · exact b4w145 j (by omega) c167
  by_cases c168 : j < 442617813
  · exact b4w146 j (by omega) c168
  by_cases c169 : j < 442815867
  · exact b4w147 j (by omega) c169
  by_cases c170 : j < 442815868
  · obtain rfl : j = 442815867 := by omega
    exact resid_442815867
  by_cases c171 : j < 443135727
  · exact b4w148 j (by omega) c171
  by_cases c172 : j < 443135728
  · obtain rfl : j = 443135727 := by omega
    exact resid_443135727
  by_cases c173 : j < 443564657
  · exact b4w149 j (by omega) c173
  by_cases c174 : j < 443564658
  · obtain rfl : j = 443564657 := by omega
    exact resid_443564657
  by_cases c175 : j < 444064658
  · exact b4w150 j (by omega) c175
  by_cases c176 : j < 444544959
  · exact b4w151 j (by omega) c176
  by_cases c177 : j < 444544960
  · obtain rfl : j = 444544959 := by omega
    exact resid_444544959
  by_cases c178 : j < 445044960
  · exact b4w152 j (by omega) c178
  by_cases c179 : j < 445298228
  · exact b4w153 j (by omega) c179
  by_cases c180 : j < 445298229
  · obtain rfl : j = 445298228 := by omega
    exact resid_445298228
  by_cases c181 : j < 445798229
  · exact b4w154 j (by omega) c181
  by_cases c182 : j < 446298229
  · exact b4w155 j (by omega) c182
  by_cases c183 : j < 446798229
  · exact b4w156 j (by omega) c183
  by_cases c184 : j < 447298229
  · exact b4w157 j (by omega) c184
  by_cases c185 : j < 447798229
  · exact b4w158 j (by omega) c185
  by_cases c186 : j < 448298229
  · exact b4w159 j (by omega) c186
  by_cases c187 : j < 448700172
  · exact b4w160 j (by omega) c187
  by_cases c188 : j < 448700173
  · obtain rfl : j = 448700172 := by omega
    exact resid_448700172
  by_cases c189 : j < 449200173
  · exact b4w161 j (by omega) c189
  by_cases c190 : j < 449700173
  · exact b4w162 j (by omega) c190
  by_cases c191 : j < 450200173
  · exact b4w163 j (by omega) c191
  by_cases c192 : j < 450309858
  · exact b4w164 j (by omega) c192
  by_cases c193 : j < 450309859
  · obtain rfl : j = 450309858 := by omega
    exact resid_450309858
  by_cases c194 : j < 450809859
  · exact b4w165 j (by omega) c194
  by_cases c195 : j < 451309859
  · exact b4w166 j (by omega) c195
  by_cases c196 : j < 451809859
  · exact b4w167 j (by omega) c196
  by_cases c197 : j < 452113443
  · exact b4w168 j (by omega) c197
  by_cases c198 : j < 452113444
  · obtain rfl : j = 452113443 := by omega
    exact resid_452113443
  by_cases c199 : j < 452219238
  · exact b4w169 j (by omega) c199
  by_cases c200 : j < 452219239
  · obtain rfl : j = 452219238 := by omega
    exact resid_452219238
  by_cases c201 : j < 452348712
  · exact b4w170 j (by omega) c201
  by_cases c202 : j < 452348713
  · obtain rfl : j = 452348712 := by omega
    exact resid_452348712
  by_cases c203 : j < 452848713
  · exact b4w171 j (by omega) c203
  by_cases c204 : j < 453348713
  · exact b4w172 j (by omega) c204
  by_cases c205 : j < 453848713
  · exact b4w173 j (by omega) c205
  by_cases c206 : j < 454198914
  · exact b4w174 j (by omega) c206
  by_cases c207 : j < 454198915
  · obtain rfl : j = 454198914 := by omega
    exact resid_454198914
  by_cases c208 : j < 454698915
  · exact b4w175 j (by omega) c208
  by_cases c209 : j < 455036418
  · exact b4w176 j (by omega) c209
  by_cases c210 : j < 455036419
  · obtain rfl : j = 455036418 := by omega
    exact resid_455036418
  by_cases c211 : j < 455536419
  · exact b4w177 j (by omega) c211
  by_cases c212 : j < 456036419
  · exact b4w178 j (by omega) c212
  by_cases c213 : j < 456536419
  · exact b4w179 j (by omega) c213
  by_cases c214 : j < 457036419
  · exact b4w180 j (by omega) c214
  by_cases c215 : j < 457536419
  · exact b4w181 j (by omega) c215
  by_cases c216 : j < 458036419
  · exact b4w182 j (by omega) c216
  by_cases c217 : j < 458536419
  · exact b4w183 j (by omega) c217
  by_cases c218 : j < 459036419
  · exact b4w184 j (by omega) c218
  by_cases c219 : j < 459536419
  · exact b4w185 j (by omega) c219
  by_cases c220 : j < 460036419
  · exact b4w186 j (by omega) c220
  by_cases c221 : j < 460346637
  · exact b4w187 j (by omega) c221
  by_cases c222 : j < 460346638
  · obtain rfl : j = 460346637 := by omega
    exact resid_460346637
  by_cases c223 : j < 460846638
  · exact b4w188 j (by omega) c223
  by_cases c224 : j < 461346638
  · exact b4w189 j (by omega) c224
  by_cases c225 : j < 461846638
  · exact b4w190 j (by omega) c225
  by_cases c226 : j < 462346638
  · exact b4w191 j (by omega) c226
  by_cases c227 : j < 462826328
  · exact b4w192 j (by omega) c227
  by_cases c228 : j < 462826329
  · obtain rfl : j = 462826328 := by omega
    exact resid_462826328
  by_cases c229 : j < 463326329
  · exact b4w193 j (by omega) c229
  by_cases c230 : j < 463453197
  · exact b4w194 j (by omega) c230
  by_cases c231 : j < 463453198
  · obtain rfl : j = 463453197 := by omega
    exact resid_463453197
  by_cases c232 : j < 463953198
  · exact b4w195 j (by omega) c232
  by_cases c233 : j < 464453198
  · exact b4w196 j (by omega) c233
  by_cases c234 : j < 464697132
  · exact b4w197 j (by omega) c234
  by_cases c235 : j < 464697133
  · obtain rfl : j = 464697132 := by omega
    exact resid_464697132
  by_cases c236 : j < 465197133
  · exact b4w198 j (by omega) c236
  by_cases c237 : j < 465697133
  · exact b4w199 j (by omega) c237
  by_cases c238 : j < 466084287
  · exact b4w200 j (by omega) c238
  by_cases c239 : j < 466084288
  · obtain rfl : j = 466084287 := by omega
    exact resid_466084287
  by_cases c240 : j < 466500438
  · exact b4w201 j (by omega) c240
  by_cases c241 : j < 466500439
  · obtain rfl : j = 466500438 := by omega
    exact resid_466500438
  by_cases c242 : j < 467000439
  · exact b4w202 j (by omega) c242
  by_cases c243 : j < 467500439
  · exact b4w203 j (by omega) c243
  by_cases c244 : j < 467546748
  · exact b4w204 j (by omega) c244
  by_cases c245 : j < 467546749
  · obtain rfl : j = 467546748 := by omega
    exact resid_467546748
  by_cases c246 : j < 468046749
  · exact b4w205 j (by omega) c246
  by_cases c247 : j < 468543507
  · exact b4w206 j (by omega) c247
  by_cases c248 : j < 468543508
  · obtain rfl : j = 468543507 := by omega
    exact resid_468543507
  by_cases c249 : j < 469043508
  · exact b4w207 j (by omega) c249
  by_cases c250 : j < 469543508
  · exact b4w208 j (by omega) c250
  by_cases c251 : j < 470043508
  · exact b4w209 j (by omega) c251
  by_cases c252 : j < 470543508
  · exact b4w210 j (by omega) c252
  by_cases c253 : j < 471043508
  · exact b4w211 j (by omega) c253
  by_cases c254 : j < 471117882
  · exact b4w212 j (by omega) c254
  by_cases c255 : j < 471117883
  · obtain rfl : j = 471117882 := by omega
    exact resid_471117882
  by_cases c256 : j < 471617883
  · exact b4w213 j (by omega) c256
  by_cases c257 : j < 472117883
  · exact b4w214 j (by omega) c257
  by_cases c258 : j < 472617883
  · exact b4w215 j (by omega) c258
  by_cases c259 : j < 472622646
  · exact b4w216 j (by omega) c259
  by_cases c260 : j < 472622647
  · obtain rfl : j = 472622646 := by omega
    exact resid_472622646
  by_cases c261 : j < 473122647
  · exact b4w217 j (by omega) c261
  by_cases c262 : j < 473622647
  · exact b4w218 j (by omega) c262
  by_cases c263 : j < 474122647
  · exact b4w219 j (by omega) c263
  by_cases c264 : j < 474622647
  · exact b4w220 j (by omega) c264
  by_cases c265 : j < 475122647
  · exact b4w221 j (by omega) c265
  by_cases c266 : j < 475309014
  · exact b4w222 j (by omega) c266
  by_cases c267 : j < 475309015
  · obtain rfl : j = 475309014 := by omega
    exact resid_475309014
  by_cases c268 : j < 475809015
  · exact b4w223 j (by omega) c268
  by_cases c269 : j < 476309015
  · exact b4w224 j (by omega) c269
  by_cases c270 : j < 476809015
  · exact b4w225 j (by omega) c270
  by_cases c271 : j < 477309015
  · exact b4w226 j (by omega) c271
  by_cases c272 : j < 477358826
  · exact b4w227 j (by omega) c272
  by_cases c273 : j < 477358827
  · obtain rfl : j = 477358826 := by omega
    exact resid_477358826
  by_cases c274 : j < 477858827
  · exact b4w228 j (by omega) c274
  by_cases c275 : j < 478358827
  · exact b4w229 j (by omega) c275
  by_cases c276 : j < 478858827
  · exact b4w230 j (by omega) c276
  by_cases c277 : j < 479358827
  · exact b4w231 j (by omega) c277
  by_cases c278 : j < 479397246
  · exact b4w232 j (by omega) c278
  by_cases c279 : j < 479397247
  · obtain rfl : j = 479397246 := by omega
    exact resid_479397246
  by_cases c280 : j < 479897247
  · exact b4w233 j (by omega) c280
  by_cases c281 : j < 480397247
  · exact b4w234 j (by omega) c281
  by_cases c282 : j < 480897247
  · exact b4w235 j (by omega) c282
  by_cases c283 : j < 480975129
  · exact b4w236 j (by omega) c283
  by_cases c284 : j < 480975130
  · obtain rfl : j = 480975129 := by omega
    exact resid_480975129
  by_cases c285 : j < 481464827
  · exact b4w237 j (by omega) c285
  by_cases c286 : j < 481464828
  · obtain rfl : j = 481464827 := by omega
    exact resid_481464827
  by_cases c287 : j < 481828008
  · exact b4w238 j (by omega) c287
  by_cases c288 : j < 481828009
  · obtain rfl : j = 481828008 := by omega
    exact resid_481828008
  by_cases c289 : j < 482328009
  · exact b4w239 j (by omega) c289
  by_cases c290 : j < 482828009
  · exact b4w240 j (by omega) c290
  by_cases c291 : j < 483328009
  · exact b4w241 j (by omega) c291
  by_cases c292 : j < 483828009
  · exact b4w242 j (by omega) c292
  by_cases c293 : j < 484328009
  · exact b4w243 j (by omega) c293
  by_cases c294 : j < 484828009
  · exact b4w244 j (by omega) c294
  by_cases c295 : j < 485328009
  · exact b4w245 j (by omega) c295
  by_cases c296 : j < 485828009
  · exact b4w246 j (by omega) c296
  by_cases c297 : j < 486328009
  · exact b4w247 j (by omega) c297
  by_cases c298 : j < 486828009
  · exact b4w248 j (by omega) c298
  by_cases c299 : j < 487328009
  · exact b4w249 j (by omega) c299
  by_cases c300 : j < 487828009
  · exact b4w250 j (by omega) c300
  by_cases c301 : j < 488328009
  · exact b4w251 j (by omega) c301
  by_cases c302 : j < 488828009
  · exact b4w252 j (by omega) c302
  by_cases c303 : j < 489328009
  · exact b4w253 j (by omega) c303
  by_cases c304 : j < 489828009
  · exact b4w254 j (by omega) c304
  by_cases c305 : j < 489950633
  · exact b4w255 j (by omega) c305
  by_cases c306 : j < 489950634
  · obtain rfl : j = 489950633 := by omega
    exact resid_489950633
  by_cases c307 : j < 490450634
  · exact b4w256 j (by omega) c307
  by_cases c308 : j < 490860984
  · exact b4w257 j (by omega) c308
  by_cases c309 : j < 490860985
  · obtain rfl : j = 490860984 := by omega
    exact resid_490860984
  by_cases c310 : j < 491360985
  · exact b4w258 j (by omega) c310
  by_cases c311 : j < 491382483
  · exact b4w259 j (by omega) c311
  by_cases c312 : j < 491382484
  · obtain rfl : j = 491382483 := by omega
    exact resid_491382483
  by_cases c313 : j < 491882484
  · exact b4w260 j (by omega) c313
  by_cases c314 : j < 492382484
  · exact b4w261 j (by omega) c314
  by_cases c315 : j < 492882484
  · exact b4w262 j (by omega) c315
  by_cases c316 : j < 493382484
  · exact b4w263 j (by omega) c316
  by_cases c317 : j < 493882484
  · exact b4w264 j (by omega) c317
  by_cases c318 : j < 494382484
  · exact b4w265 j (by omega) c318
  by_cases c319 : j < 494882484
  · exact b4w266 j (by omega) c319
  by_cases c320 : j < 495382484
  · exact b4w267 j (by omega) c320
  by_cases c321 : j < 495882484
  · exact b4w268 j (by omega) c321
  by_cases c322 : j < 496245639
  · exact b4w269 j (by omega) c322
  by_cases c323 : j < 496245640
  · obtain rfl : j = 496245639 := by omega
    exact resid_496245639
  by_cases c324 : j < 496745640
  · exact b4w270 j (by omega) c324
  by_cases c325 : j < 497245640
  · exact b4w271 j (by omega) c325
  by_cases c326 : j < 497745640
  · exact b4w272 j (by omega) c326
  by_cases c327 : j < 498245640
  · exact b4w273 j (by omega) c327
  by_cases c328 : j < 498745640
  · exact b4w274 j (by omega) c328
  by_cases c329 : j < 499098783
  · exact b4w275 j (by omega) c329
  by_cases c330 : j < 499098784
  · obtain rfl : j = 499098783 := by omega
    exact resid_499098783
  by_cases c331 : j < 499598784
  · exact b4w276 j (by omega) c331
  by_cases c332 : j < 499800309
  · exact b4w277 j (by omega) c332
  by_cases c333 : j < 499800310
  · obtain rfl : j = 499800309 := by omega
    exact resid_499800309
  · exact b4w278 j (by omega) hj1

/-- LEAF. Step 4 of 5, the coverage job on the third block.  For every j with
250000000 ≤ j < 375000000 some listed offset a below 10 ^ 300 makes 2 * j + a
prime. -/
theorem cover_block3 :
    ∀ j : ℕ, 250000000 ≤ j → j < 375000000 →
      ∃ a ∈ ([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ), a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j h0 h1
  obtain ⟨a, ha, hp⟩ := b3all j h0 h1
  exact ⟨a, ha, _root_.LeanLab.DtRS1998.Decomp455a.offsets_le a ha, hp⟩

/-- LEAF. Step 5 of 5, the coverage job on the top block.  For every j with
375000000 ≤ j < 500000001, which is the whole remaining range of the list, some
listed offset a below 10 ^ 300 makes 2 * j + a prime. -/
theorem cover_block4 :
    ∀ j : ℕ, 375000000 ≤ j → j < 500000001 →
      ∃ a ∈ ([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ), a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j h0 h1
  obtain ⟨a, ha, hp⟩ := b4all j h0 h1
  exact ⟨a, ha, _root_.LeanLab.DtRS1998.Decomp455a.offsets_le a ha, hp⟩

/-- The row at 10 ^ 300, assembled from the five leaves: the list is the shift
set, so it has 213 entries, each entry is prime by step 1, and an even offset is
met by its block's witness from steps 2 to 5. -/
theorem certificate300_split :
    ∃ qs : List ℕ, qs.length ≤ 227 ∧ (∀ q ∈ qs, q.Prime) ∧ (List.range (10 ^ 9 / 2 + 1)).all (fun j => qs.any (fun q => decide (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime))) = true := by
  refine ⟨([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ).map (fun a => 10 ^ 300 - a), ?_, ?_, ?_⟩
  · have hlen : ([69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531, 8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857, 13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733, 24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949, 30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369, 33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679, 39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347, 47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617, 51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097, 58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159, 67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387, 72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411, 77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179, 84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341, 91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471, 98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297, 104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141, 111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039, 118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219, 126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391, 158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913, 3166973, 3361883, 3697757].map (fun a => 10 ^ 300 - a)).length = 213 := rfl
    omega
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact prime_offsets a ha
  · exact List.all_eq_true.mpr (fun j hj => by
      have hjr : j < 10 ^ 9 / 2 + 1 := List.mem_range.mp hj
      have hjt : j < 500000001 := by
        have h9 : 10 ^ 9 / 2 + 1 = 500000001 := by norm_num
        omega
      have hwit : ∃ a ∈ ([
    69, 347, 3759, 4191, 6257, 6393, 6411, 7451, 7971, 8531,
    8883, 8903, 9929, 10029, 10161, 10643, 11741, 12131, 12789, 12857,
    13397, 14817, 15431, 15893, 18017, 20871, 21327, 21927, 22433, 23733,
    24371, 25227, 25617, 25791, 25833, 26373, 27527, 27887, 29259, 29949,
    30063, 30831, 30959, 31169, 31961, 32751, 32771, 33101, 33263, 33369,
    33611, 33779, 34107, 34733, 34977, 35321, 35627, 37383, 37491, 38679,
    39933, 40757, 42821, 43203, 44559, 44589, 44709, 45257, 45971, 46347,
    47777, 48737, 49121, 49299, 50483, 50627, 50771, 50973, 51077, 51617,
    51881, 52049, 53237, 53267, 55113, 55509, 56091, 57497, 57689, 58097,
    58571, 59259, 61779, 62337, 62363, 62579, 64623, 65133, 65967, 66159,
    67841, 68429, 68637, 69227, 69423, 70713, 71091, 71103, 72261, 72387,
    72503, 73619, 73647, 75693, 76019, 76641, 77003, 77213, 77259, 77411,
    77579, 77957, 80709, 81857, 82401, 82557, 83523, 83729, 83783, 84179,
    84341, 85049, 85479, 87323, 87651, 88577, 89301, 90123, 90743, 91341,
    91871, 93429, 94239, 95183, 96087, 97071, 97893, 97983, 98097, 98471,
    98657, 98661, 98937, 99479, 100113, 100221, 100433, 101019, 101549, 102297,
    104817, 104841, 107331, 109233, 109263, 109281, 109709, 109769, 110427, 111141,
    111213, 112979, 113783, 115217, 115317, 115401, 116357, 116717, 117023, 117039,
    118107, 118419, 122411, 123351, 123533, 123923, 124449, 125219, 125771, 126219,
    126429, 127301, 131189, 131207, 131337, 131889, 132219, 132729, 133377, 133391,
    158457, 291297, 336179, 421491, 505017, 699059, 969173, 1334189, 1668413, 2240913,
    3166973, 3361883, 3697757 ] : List ℕ), a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
        by_cases h1 : j < 125000000
        · exact cover_block1 j h1
        by_cases h2 : j < 250000000
        · exact cover_block2 j (by omega) h2
        by_cases h3 : j < 375000000
        · exact cover_block3 j (by omega) h3
        · exact cover_block4 j (by omega) hjt
      obtain ⟨a, ha, hle, hp⟩ := hwit
      refine List.any_eq_true.mpr ⟨10 ^ 300 - a, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨a, ha, rfl⟩
      · rw [decide_eq_true_eq]
        exact ⟨sub_le (10 ^ 300) a j, by rw [sub_sub (10 ^ 300) a j hle]; exact hp⟩)

#print axioms certificate300_split
