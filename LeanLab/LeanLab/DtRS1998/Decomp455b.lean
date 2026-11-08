/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, sieve and primality paragraphs.
Table 2 page 214, row 300. Binary Goldbach is open.
This is a strict split of an alternative fixed certificate list.
The source reports the computation but does not print this list.
-/
import LeanLab.DtRS1998.Decomp455g

namespace LeanLab.DtRS1998.Decomp455b

open Decomp455a

set_option maxRecDepth 100000

/-- LEAF. P0037 Section 5.2 page 212, bit array sieve paragraph,
and Table 2 page 214 row 300. Cover only 1000000 ≤ j < 62500000.
This is a strict subrange of sealed cover_block1.
Use the same fixed offsets and require only the small complement prime. -/
theorem cover_lower :
    ∀ j : ℕ, 1000000 ≤ j → j < 62500000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  exact Decomp455g.cover_block1 j (by omega)

/-- LEAF. P0037 Section 5.2 page 212, bit array sieve paragraph,
and Table 2 page 214 row 300. Cover only 62500000 ≤ j < 125000000.
This is a strict subrange of sealed cover_block1.
Use the same fixed offsets and require only the small complement prime. -/
theorem cover_upper :
    ∀ j : ℕ, 62500000 ≤ j → j < 125000000 →
      ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  exact Decomp455g.cover_block1 j (by omega)

/-- Exact coverage leaf assembled from its prefix and two strict residual ranges.
P0037 page 212. All coverage inputs have clean kernel certificates.
The first million indices use the independent kernel checked prefix.
The proof has no sorry of its own. -/
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
  intro j hj
  by_cases hp : j < 1000000
  · exact Decomp455f.prefix1 j (by omega) hp
  by_cases hm : j < 62500000
  · exact cover_lower j (by omega) hm
  · exact cover_upper j (by omega) hj

#print axioms cover_lower
#print axioms cover_upper
#print axioms cover_block1

end LeanLab.DtRS1998.Decomp455b
