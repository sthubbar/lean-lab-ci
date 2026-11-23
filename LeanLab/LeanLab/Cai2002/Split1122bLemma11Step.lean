/-
Split1122bLemma11Step: candidate counterexample to `leaf306_lemma11_step` of `Split306Theorem6.lean`,
BJS Lemma 11 for n ≥ 2, Bordignon Johnston Starichkova arXiv 2207.09452v6, pages 11 to 13,
displays 34 to 39, through Nathanson Lemma 9.8 and Theorem 9.5 with BJS Lemmas 9 and 10.

OUTCOME of burst-20261122 unit lemma11stepsplit: the statement is SUSPECTED FALSE, so it is
not split. Candidate counterexample, computed numerically, not yet proved in Lean:
n = 3, z = D = 10 ^ 12, so s = 1; P = {47, 967, 9973}; g multiplicative with
g 9973 = 1 - log 9973 / log z, g 967 = 1 - log 967 / log 9973, g 47 = 1 - log 47 / log 967,
and g p = 0 at other primes. The one parameter display 29 holds with K = 1, hence with any
K > 1, because the tail products are exactly log z / log q at the three atoms q.
Then T_3 = g 47 * g 967 * g 9973 ≈ 0.5335 * V z, while f_3 1 ≈ 0.2936, and
ε τ_3 e ^ 2 h 1 = ε τ_3 → 0 as ε → 0 for any fixed c, for example ε τ_3 ≈ 0.129 at ε = 0.01
with c = bjsC306. The atom 2/3 just below z ^ (1/3) is allowed only because display 29 is
stated with the single upper end z; the two parameter form of Nathanson Theorem 9.5,
for all u < w ≤ z, rules it out. See notes/burst-20261122/Cai2002-lemma11stepsplit.md.

The proved helpers below check the elementary side conditions of the candidate.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- Side condition of the candidate counterexample: the largest atom 9973 satisfies
9973 ^ 3 < D = 10 ^ 12, the Rosser condition at p = p_1 for n = 3, display 34. -/
theorem lemma11step_cex_top_cube : (9973 : ℕ) ^ 3 < 10 ^ 12 := by norm_num

/-- Side condition of the candidate counterexample: d * p_3 ^ 2 = 47 ^ 3 * 967 * 9973 ≥ D,
the condition D ≤ d * minFac d ^ 2 of `rosserT306`. -/
theorem lemma11step_cex_lower : (10 : ℕ) ^ 12 ≤ 47 ^ 3 * 967 * 9973 := by norm_num

/-- At s = 1 the error factor e ^ 2 h 1 equals 1, so the right side of the twin at the
candidate is V z * (f_3 1 + ε τ_3). -/
theorem lemma11step_exp_hSieve_one : exp 2 * LeanLab.ChenExplicit.hSieve 1 = 1 := by
  unfold LeanLab.ChenExplicit.hSieve
  simp only [show (1 : ℝ) ≤ 2 by norm_num, ↓reduceIte, ← exp_add]
  norm_num

/-! The statement `leaf306_lemma11_step` is not restated here: it is suspected false, see the
header, so no twin and no LEAF is made. The QUESTION for the coordinator is whether
`leaf306_lemma11_step` and `leaf306_lemma11` should carry display 29 for every upper end
w ≤ z, as Nathanson Theorem 9.5 does. -/

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.lemma11step_cex_top_cube
#print axioms LeanLab.Cai2002.lemma11step_cex_lower
#print axioms LeanLab.Cai2002.lemma11step_exp_hSieve_one
