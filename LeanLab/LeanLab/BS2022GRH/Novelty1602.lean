/-
AI wrote the Lean code, Claude, unit U-1602, run 20261102T0813Z-2382, track T2, NOVELTY triage.
Tag: IMPROVEMENT. Not original. Status of the mathematical question: QUESTION, not a claimed error.
Binary Goldbach is OPEN.

Source of the work: research/novelty/BS2022GRH-deepseek-20261102T0036Z.md section 6 item 2 claims a
threshold exp exp 13 from sharper Mertens bounds. That route FAILS, see the triage. While testing it
this unit found the following about P0021, Bordignon and Starichkova, Ramanujan J. 64 (2024).

Hypothesis (2), Theorem 4 p. 1218, asks that the product over p in P minus Q with u ≤ p < z of
(1 - g(p))⁻¹ be at most (1 + ε) log z / log u for all n and 1 < u < z.
Lemma 7 p. 1221 verifies it only for z > exp 2753, with Q the primes below u₀.
The proof of Theorem 4 is BJS arXiv 2207.09452, Lemma 11 p. 10, an induction on n, which by the cited
Nathanson Theorem 9.5 applies the n - 1 case at the smaller sifting level p. Friedlander and Iwaniec
Theorem 11.12, as quoted in Maynard arXiv 1504.00533 equation 7, asks the bound for all z ≥ w ≥ 2.
Nathanson's book is NOT FOUND IN EITHER, so the reading that all levels are needed is not settled here.

What is PROVED here, with no cited input:
* `hyp2_fails_1628`: the bound with ε = 1/1000 fails at u = 1543, level z = 1628. The true ratio is
  1.0028183, research/novelty/triage-scripts-U1602/bs_witness_and_scan.out.
* `journal_eps1500_fails`, `journal_eps1000_fails`: so ε = 1/8349 and ε = 1/5235 of Section 5.4 do not
  verify (2) at that level. Lemma 7 itself is NOT contradicted: `level_below_lemma7_range`.

Named sorry `lemma7_sharp`, a true looking sharpening at one fixed large z, see its doc comment. It only
helps if the sieve needs one fixed z, the reading the sealed `LinearSieveT4` of ChenThresholdGRH.lean uses.
-/
import Mathlib

namespace LeanLab.BS2022GRH.Novelty1602

open Real Finset

/-- The product of (1 - 1/(p-1))⁻¹ over primes u ≤ p < z, display (2) with g(p) = 1/(p-1),
journal p. 1219, for N with no prime factor in the range and Q the primes below u. -/
noncomputable def prod2 (u z : ℝ) : ℝ :=
  ∏ p ∈ (Finset.Ico ⌈u⌉₊ ⌈z⌉₊).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1))⁻¹

/-- Display (2) of Theorem 4 at the level `z`, for all `u₀ ≤ u < z`. -/
def Hyp2AtLevel (ε u₀ z : ℝ) : Prop :=
  ∀ u : ℝ, u₀ ≤ u → u < z → prod2 u z ≤ (1 + ε) * (Real.log z / Real.log u)

/-- Lowering `u₀` strengthens the hypothesis. -/
theorem Hyp2AtLevel.mono_u {ε u₀ u₁ z : ℝ} (h : Hyp2AtLevel ε u₀ z) (hu : u₀ ≤ u₁) :
    Hyp2AtLevel ε u₁ z :=
  fun u h1 h2 => h u (hu.trans h1) h2

/-- Lowering `ε` strengthens the hypothesis, for levels and `u` above one. -/
theorem Hyp2AtLevel.mono_eps {ε ε' u₀ z : ℝ} (h : Hyp2AtLevel ε u₀ z) (hε : ε ≤ ε') (hu : 1 < u₀) :
    Hyp2AtLevel ε' u₀ z := by
  intro u h1 h2
  refine (h u h1 h2).trans ?_
  have hu1 : 1 < u := lt_of_lt_of_le hu h1
  have hq : 0 ≤ Real.log z / Real.log u :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg hu1.le)
  exact mul_le_mul_of_nonneg_right (by linarith) hq

/-- Sixteen primes in `[1543, 1628)`. -/
def witnessPrimes : Finset ℕ :=
  {1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627}

theorem witnessPrimes_card : witnessPrimes.card = 16 := by decide

theorem witnessPrimes_subset : witnessPrimes ⊆ (Finset.Ico 1543 1628).filter Nat.Prime := by
  intro p hp
  simp only [witnessPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (by norm_num), by norm_num⟩

/-- Each factor is at least `1 + 1/1626` for a prime `p` in the window. -/
theorem factor_ge {p : ℕ} (h1 : 3 ≤ p) (h2 : p ≤ 1627) :
    (1 + 1 / 1626 : ℝ) ≤ (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h1
  have h4 : (p : ℝ) ≤ 1627 := by exact_mod_cast h2
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hb : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hl : 1 / 1626 ≤ 1 / ((p : ℝ) - 1) :=
    one_div_le_one_div_of_le hq (by linarith)
  have hpos : (0 : ℝ) < 1 - 1 / ((p : ℝ) - 1) := by linarith
  rw [← one_div, le_div_iff₀ hpos]
  nlinarith

/-- The product at the witness is at least `(1 + 1/1626)^16 ≥ 1.0098`; the true value is 1.0101431. -/
theorem prod2_witness : (1.0098 : ℝ) ≤ prod2 1543 1628 := by
  have h1 : ⌈(1543 : ℝ)⌉₊ = 1543 := by exact_mod_cast Nat.ceil_natCast 1543
  have h2 : ⌈(1628 : ℝ)⌉₊ = 1628 := by exact_mod_cast Nat.ceil_natCast 1628
  unfold prod2
  rw [h1, h2]
  have hcard : 16 ≤ ((Finset.Ico 1543 1628).filter Nat.Prime).card := by
    rw [← witnessPrimes_card]
    exact Finset.card_le_card witnessPrimes_subset
  have hle : ∏ _p ∈ (Finset.Ico 1543 1628).filter Nat.Prime, (1 + 1 / 1626 : ℝ) ≤
      ∏ p ∈ (Finset.Ico 1543 1628).filter Nat.Prime, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro _ _; norm_num
    · intro p hp
      have hI := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
      exact factor_ge (by omega) (by omega)
  rw [Finset.prod_const] at hle
  have hpow : ((1 : ℝ) + 1 / 1626) ^ 16 ≤
      (1 + 1 / 1626) ^ ((Finset.Ico 1543 1628).filter Nat.Prime).card :=
    pow_le_pow_right₀ (by norm_num) hcard
  have hnum : (1.0098 : ℝ) ≤ (1 + 1 / 1626) ^ 16 := by norm_num
  exact hnum.trans (hpow.trans hle)

theorem log1543_ge : (7 : ℝ) ≤ Real.log 1543 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h3 : Real.exp 1 ^ 7 ≤ 2.7182818286 ^ 7 := by
    gcongr; exact Real.exp_one_lt_d9.le
  exact h3.trans (by norm_num)

theorem log1628_le : Real.log 1628 ≤ Real.log 1543 + 85 / 1543 := by
  have h : Real.log (1628 / 1543) ≤ 1628 / 1543 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  norm_num at h ⊢
  linarith

/-- **PROVED**: display (2) with `ε = 1/1000` fails at the level `z = 1628`, at `u = 1543`. -/
theorem hyp2_fails_1628 : ¬ Hyp2AtLevel (1 / 1000) 1500 1628 := by
  intro h
  have h0 := h 1543 (by norm_num) (by norm_num)
  have hP := prod2_witness
  have hA := log1543_ge
  have hB := log1628_le
  have hApos : 0 < Real.log 1543 := by linarith
  have h1 : (1.0098 : ℝ) ≤ (1 + 1 / 1000) * (Real.log 1628 / Real.log 1543) := hP.trans h0
  rw [← mul_div_assoc, le_div_iff₀ hApos] at h1
  nlinarith

/-- **PROVED**: the `ε(1500) < 1/8349` of the lab's 13.375 parameters does not verify (2) at `z = 1628`. -/
theorem journal_eps1500_fails : ¬ Hyp2AtLevel (1 / 8349) 1500 1628 := fun h =>
  hyp2_fails_1628 (h.mono_eps (by norm_num) (by norm_num))

/-- **PROVED**: the `ε(1000) < 1/5235` of the journal's Section 5.4 does not verify (2) at `z = 1628`. -/
theorem journal_eps1000_fails : ¬ Hyp2AtLevel (1 / 5235) 1000 1628 := fun h =>
  hyp2_fails_1628 ((h.mono_u (by norm_num)).mono_eps (by norm_num) (by norm_num))

/-- Lemma 7 p. 1221 is not contradicted: its range is `z > exp 2753`, and `1628` is far below that. -/
theorem level_below_lemma7_range : (1628 : ℝ) < Real.exp 2753 := by
  have h := Real.add_one_le_exp (2753 : ℝ)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : Real.exp 11 ≤ Real.exp 2753 := Real.exp_le_exp.mpr (by norm_num)
  have h4 : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  have h5 : (2 : ℝ) ^ 11 ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) h2 11
  have h6 : (1628 : ℝ) < 2 ^ 11 := by norm_num
  linarith

/-- Sealed target, the sharpening of Lemma 7 at one fixed large `z`:
for every `z > exp 2753` and every `400 ≤ u < z`, the product is at most `(1 + 1/39500) log z / log u`.
Journal p. 1221 display (6) gives only `1/1852` at `u₀ = 400`. `1/39500` is the last row of Table 1 p. 1218.
Python, bs_lemma7_sup.out: the sup over primes of H(u) - E(u) on `[13, 3·10⁸]` is `-1.29·10⁻⁶`, where
`E(u) = Σ_{p<u} 1/p - log log u - M`, `H(u) = Σ_{p≥u} (-log(1 - 1/(p-1)) - 1/p)`. Display (6) has the
structural term H(u) and drops E(u) ≥ 0. -/
def Lemma7Sharp : Prop :=
  ∀ z : ℝ, Real.exp 2753 < z → Hyp2AtLevel (1 / 39500) 400 z

/-- OPEN, named sorry. Route: `prod2 u z` has logarithm at most H(u) + Σ_{u≤p<z} 1/p. By journal
Lemma 6 display (3) p. 1219 the sum is at most log log z - log log u + 2.29·10⁻⁹/log z - E(u), and
E(u) ≥ -1.1075·10⁻⁷. So for u ≥ 10000, where H(u) ≤ 1.5·10⁻⁵, the claim follows from Lemma 6 alone,
which the folder has as the inputs of `DecompC169c.lemma7J`. For 400 ≤ u < 10000, 1151 primes, one needs
E(u) ≥ H(u) - 2·10⁻⁵, a finite check, with M bounded above by the partial sum at x = 88789 through the
first line of Lemma 6, where E is 1.2·10⁻⁴, see bs_route_numbers.out.
Do not use this to lower the threshold unless the sieve is shown to need only one fixed `z`:
see `hyp2_fails_1628` and the triage. -/
theorem lemma7_sharp : Lemma7Sharp := by
  sorry

/-- Vacuity for `Hyp2AtLevel`: it holds at `z = 1501`, `u₀ = 1500`, `ε = 1`, where no prime qualifies. -/
theorem hyp2_instance : Hyp2AtLevel 1 1500 1501 := by
  intro u hu huz
  have hz : ⌈(1501 : ℝ)⌉₊ = 1501 := by exact_mod_cast Nat.ceil_natCast 1501
  have hc : 1500 ≤ ⌈u⌉₊ := by
    have : (1500 : ℝ) ≤ (⌈u⌉₊ : ℝ) := hu.trans (Nat.le_ceil u)
    exact_mod_cast this
  have hempty : (Finset.Ico ⌈u⌉₊ 1501).filter Nat.Prime = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hp
    have hp' : p = 1500 := by omega
    subst hp'
    norm_num
  have hprod : prod2 u 1501 = 1 := by
    unfold prod2
    rw [hz, hempty, Finset.prod_empty]
  rw [hprod]
  have hu1 : 1 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hle : Real.log u ≤ Real.log 1501 := Real.log_le_log (by linarith) huz.le
  have hq : 1 ≤ Real.log 1501 / Real.log u := (one_le_div hlogu).mpr hle
  norm_num
  linarith

/-- Vacuity for `Lemma7Sharp`: an admissible `z` exists, and so does `u` with `400 ≤ u < z`. -/
theorem lemma7Sharp_range_nonempty : ∃ z u : ℝ, Real.exp 2753 < z ∧ 400 ≤ u ∧ u < z := by
  refine ⟨Real.exp 2754, 400, Real.exp_lt_exp.mpr (by norm_num), le_rfl, ?_⟩
  have h := Real.add_one_le_exp (2754 : ℝ)
  linarith

end LeanLab.BS2022GRH.Novelty1602

#print axioms LeanLab.BS2022GRH.Novelty1602.hyp2_fails_1628
#print axioms LeanLab.BS2022GRH.Novelty1602.journal_eps1500_fails
#print axioms LeanLab.BS2022GRH.Novelty1602.journal_eps1000_fails
#print axioms LeanLab.BS2022GRH.Novelty1602.level_below_lemma7_range
#print axioms LeanLab.BS2022GRH.Novelty1602.hyp2_instance
#print axioms LeanLab.BS2022GRH.Novelty1602.lemma7Sharp_range_nonempty
#print axioms LeanLab.BS2022GRH.Novelty1602.lemma7_sharp
