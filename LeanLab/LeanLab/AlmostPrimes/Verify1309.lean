/-
AI-written Lean code, Claude, 2026-10-21, run 20261021T0103Z-19411, unit U-1309 VERIFY.
Fresh-workspace axiom audit of the P0048 Dudek-Dunn modules DDCase4, DDCase2, DDMain,
DDNathanson, RSRecip from run 20261020T2303Z-14596. No new mathematics. Goldbach is open.
-/
import LeanLab.AlmostPrimes.DDCase4
import LeanLab.AlmostPrimes.DDCase2
import LeanLab.AlmostPrimes.DDMain
import LeanLab.AlmostPrimes.DDNathanson
import LeanLab.AlmostPrimes.RSRecip

-- DDCase4
#print axioms LeanLab.AlmostPrimes.DDCase4.logCheck_ok
#print axioms LeanLab.AlmostPrimes.DDCase4.pairCheck_ok
#print axioms LeanLab.AlmostPrimes.DDCase4.pair_bound
#print axioms LeanLab.AlmostPrimes.DDCase4.case4
#print axioms LeanLab.AlmostPrimes.DDCase4.lemma2_1_of_case2
-- DDCase2
#print axioms LeanLab.AlmostPrimes.DDCase2.tabCheck_ok
#print axioms LeanLab.AlmostPrimes.DDCase2.finCheck_ok
#print axioms LeanLab.AlmostPrimes.DDCase2.fin_bound
#print axioms LeanLab.AlmostPrimes.DDCase2.head_bound
#print axioms LeanLab.AlmostPrimes.DDCase2.case2
#print axioms LeanLab.AlmostPrimes.DDCase2.lemma2_1_of_RS
-- DDMain
#print axioms LeanLab.AlmostPrimes.DDMain.dimCond_of_RS
#print axioms LeanLab.AlmostPrimes.DDMain.lemma2_2_of
#print axioms LeanLab.AlmostPrimes.DDMain.lemma2_3_of
#print axioms LeanLab.AlmostPrimes.DDMain.sifted_large
#print axioms LeanLab.AlmostPrimes.DDMain.sifted_all
#print axioms LeanLab.AlmostPrimes.DDMain.theorem3_3_large
#print axioms LeanLab.AlmostPrimes.DDMain.theorem3_3
#print axioms LeanLab.AlmostPrimes.DDMain.theorem1_2
#print axioms LeanLab.AlmostPrimes.DDMain.premise_fires
#print axioms LeanLab.AlmostPrimes.DDMain.selberg_at_two
#print axioms LeanLab.AlmostPrimes.DDMain.sifted_not_trivial
#print axioms LeanLab.AlmostPrimes.DDMain.trivial_split_fails
-- DDNathanson
#print axioms LeanLab.AlmostPrimes.DDNathanson.periodic_Icc
#print axioms LeanLab.AlmostPrimes.DDNathanson.crt_count
#print axioms LeanLab.AlmostPrimes.DDNathanson.dvd_aSeq_iff
#print axioms LeanLab.AlmostPrimes.DDNathanson.count_Ps
#print axioms LeanLab.AlmostPrimes.DDNathanson.nathansonRd
#print axioms LeanLab.AlmostPrimes.DDNathanson.theorem3_3_large_of_RS
#print axioms LeanLab.AlmostPrimes.DDNathanson.theorem3_3_of_RS
#print axioms LeanLab.AlmostPrimes.DDNathanson.theorem1_2_of_RS
#print axioms LeanLab.AlmostPrimes.DDNathanson.rd_example
-- RSRecip
#print axioms LeanLab.AlmostPrimes.RSRecipRed.seventeen_le_log
#print axioms LeanLab.AlmostPrimes.RSRecipRed.primesIn_subset
#print axioms LeanLab.AlmostPrimes.RSRecipRed.RSRecip_of_RS320
#print axioms LeanLab.AlmostPrimes.RSRecipRed.theorem3_3_large_of_RS2
#print axioms LeanLab.AlmostPrimes.RSRecipRed.theorem1_2_of_RS2

-- The hypothesis Props are definitions; print their statements for the record.
#check @LeanLab.AlmostPrimes.DDLemma21All.RSHyp
#print LeanLab.AlmostPrimes.DDMain.RSRecip
#print LeanLab.AlmostPrimes.RSRecipRed.RS320
#print LeanLab.AlmostPrimes.DDMain.VerifySScript
#print LeanLab.AlmostPrimes.DudekDunn2026.GapTable1476

/-- Vacuity: `RSHyp`'s hypotheses are satisfiable, `w = 286 < z = 287`. -/
example : (286 : ℝ) ≤ 286 ∧ (286 : ℝ) < 287 := by norm_num

/-- Vacuity: `GapTable1476` holds at `q = 2`, next prime `3`. -/
example : ∃ q' : ℕ, q'.Prime ∧ 2 < q' ∧ q' - 2 ≤ 1476 := ⟨3, Nat.prime_three, by norm_num, by norm_num⟩
