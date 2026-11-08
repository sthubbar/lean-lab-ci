/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, sieve and primality paragraphs.
Table 2 page 214, row 300. Binary Goldbach is open.
This is a strict split of an alternative fixed certificate list.
The source reports the computation but does not print this list.
-/
import Mathlib

namespace LeanLab.DtRS1998.Decomp455a

set_option maxRecDepth 100000

/-- The 213 offsets in the sealed certificate300 target.
P0037 page 212, supporting certificate data rather than a printed table list. -/
def offsets : List ℕ := [
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
    3166973, 3361883, 3697757 ]

/-- Each primality batch has 71 entries, strictly fewer than 213.
P0037 page 212, separate certification of candidate numbers. -/
theorem batch_lengths :
    offsets.length = 213 ∧ (offsets.take 71).length = 71 ∧
    ((offsets.drop 71).take 71).length = 71 ∧ (offsets.drop 142).length = 71 := by
  decide +kernel

/-- All three membership premises have explicit instances.
P0037 page 212, supporting certificate partition. -/
theorem batch_members :
    69 ∈ offsets.take 71 ∧ 48737 ∈ (offsets.drop 71).take 71 ∧
    94239 ∈ offsets.drop 142 := by
  decide +kernel

/-- Every batch omits a member of the full fixed list.
P0037 page 212, strictness of the candidate partition. -/
theorem batch_omissions :
    48737 ∈ offsets ∧ 48737 ∉ offsets.take 71 ∧
    69 ∈ offsets ∧ 69 ∉ (offsets.drop 71).take 71 ∧ 69 ∉ offsets.drop 142 := by
  decide +kernel

/-- Every fixed offset is below the base.
P0037 page 212, arithmetic support for the shifted sieve. -/
theorem offsets_le : ∀ a ∈ offsets, a ≤ 10 ^ 300 := by
  have h : ∀ a ∈ offsets, a ≤ 3697757 := by decide +kernel
  intro a ha
  exact (h a ha).trans (by decide +kernel)

/-- LEAF. P0037 Section 5.2 page 212, primality certification paragraph,
and Table 2 page 214 row 300. Certify only offsets 1 through 71
of the alternative fixed list. No coverage obligation occurs here.
The individual large prime certificates remain OPEN. -/
theorem prime_batch0 : ∀ a ∈ offsets.take 71, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, primality certification paragraph,
and Table 2 page 214 row 300. Certify only offsets 72 through 142
of the alternative fixed list. No coverage obligation occurs here.
The individual large prime certificates remain OPEN. -/
theorem prime_batch1 : ∀ a ∈ (offsets.drop 71).take 71, (10 ^ 300 - a).Prime := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, primality certification paragraph,
and Table 2 page 214 row 300. Certify only offsets 143 through 213
of the alternative fixed list. No coverage obligation occurs here.
The individual large prime certificates remain OPEN. -/
theorem prime_batch2 : ∀ a ∈ offsets.drop 142, (10 ^ 300 - a).Prime := by
  sorry

/-- Exact primality leaf assembled from three strict batches.
P0037 page 212. CONDITIONAL ON the three OPEN prime batches.
The proof has no sorry of its own. -/
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
  change ∀ a ∈ offsets, (10 ^ 300 - a).Prime
  intro a ha
  rw [← List.take_append_drop 71 offsets, List.mem_append] at ha
  rcases ha with ha | ha
  · exact prime_batch0 a ha
  rw [← List.take_append_drop 71 (offsets.drop 71), List.mem_append] at ha
  rcases ha with ha | ha
  · exact prime_batch1 a ha
  simp only [List.drop_drop] at ha
  exact prime_batch2 a ha

#print axioms batch_lengths
#print axioms batch_members
#print axioms batch_omissions
#print axioms offsets_le
#print axioms prime_batch0
#print axioms prime_batch1
#print axioms prime_batch2
#print axioms prime_offsets

end LeanLab.DtRS1998.Decomp455a
