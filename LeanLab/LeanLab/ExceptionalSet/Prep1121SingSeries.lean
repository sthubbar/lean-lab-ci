import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions
import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions

/-!
Prep 2026-11-21, ExceptionalSet route step ES-cited. In place split of the singular series
lower bound `𝔖(m) ≫ m / φ(m)` for even `m`, P0082 page 358 display 11 and page 362 Lemma 7
case i, Brüdern and Perelli, Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621.

This bound is the named hypothesis `SingularSeriesEvenLowerBP` of
`UpJ200.DQLeafAbsentSelectedDecisions` and, in integer form, `SingSeriesLowerHyp` of
`UpJ200.DQLeafCoprimeSelectedDecisions`. The paper states it without proof; it is elementary,
so it is NOT a citation wall and is split here. The written argument: for even `m` the factor
at a prime `p ∣ m` is `p / (p - 1)`, whose product is `m / φ(m)`, and the remaining factors
`1 - (p - 1)⁻²` over odd `p ∤ m` have product at least the twin prime constant
`∏_{p > 2} (1 - (p - 1)⁻²) > 0`.

The final theorems `singularSeriesEvenLowerBP_split` and `singSeriesLowerHyp_split` PROVE the
two named Props outright: every step below is closed, no sorry, no axiom. So these two named
hypotheses can be discharged from the conditional leaf theorems of the two decision files.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries

open Real
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected (singularSeries SingularSeriesEvenLowerBP)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries SingSeriesLowerHyp)

/-- P0082 page 358 display 11. The factor of the singular series at a prime `p` splits as
the local factor `p / (p - 1)` of `m / φ(m)` times `1 - (p - 1)⁻²` restricted to `p ∤ m`,
since `1 + 1/(p - 1) = p / (p - 1)`. PROVED. -/
theorem factor_split (m : ℕ) (p : Nat.Primes) :
    (if (p : ℕ) ∣ m then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2) =
      (if (p : ℕ) ∣ m then (p : ℝ) / ((p : ℝ) - 1) else 1) *
        (1 - (if (p : ℕ) ∣ m then 0 else 1 / ((p : ℝ) - 1) ^ 2)) := by
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  split_ifs
  · field_simp; ring
  · ring

/-- P0082 page 358 display 11 and page 362 case i, PROVED, the identity
`∏_{p ∣ m} p / (p - 1) = m / φ(m)` for `m ≥ 1`, written as a product over all primes with
factor one at `p ∤ m`. A Mathlib lookup around `Nat.totient_mul_prod_primeFactors`. -/
theorem leaf_prod_primeFactors_ratio (m : ℕ) (hm : 1 ≤ m) :
    Multipliable (fun p : Nat.Primes =>
        if (p : ℕ) ∣ m then (p : ℝ) / ((p : ℝ) - 1) else 1) ∧
      ∏' p : Nat.Primes, (if (p : ℕ) ∣ m then (p : ℝ) / ((p : ℝ) - 1) else 1) =
        (m : ℝ) / (m.totient : ℝ) := by
  classical
  set s : Finset Nat.Primes := m.primeFactors.subtype Nat.Prime with hsdef
  have hsupp : ∀ p ∉ s, (if (p : ℕ) ∣ m then (p : ℝ) / ((p : ℝ) - 1) else 1) = 1 := by
    intro p hp
    have hnd : ¬ (p : ℕ) ∣ m := by
      intro hd
      apply hp
      rw [hsdef]
      exact (Finset.mem_subtype (p := Nat.Prime) (s := m.primeFactors)
        (a := (p : Subtype Nat.Prime))).mpr (Nat.mem_primeFactors.mpr ⟨p.2, hd, by omega⟩)
    simp [hnd]
  refine ⟨multipliable_of_ne_finset_one hsupp, ?_⟩
  rw [tprod_eq_prod hsupp, hsdef]
  refine Eq.trans (Finset.prod_subtype_eq_prod_filter (s := m.primeFactors) (p := Nat.Prime)
    (fun q : ℕ => if q ∣ m then (q : ℝ) / ((q : ℝ) - 1) else 1)) ?_
  rw [Finset.filter_true_of_mem (fun q hq => Nat.prime_of_mem_primeFactors hq)]
  rw [Finset.prod_congr rfl (fun q hq => ite_eq_left_of_eq_true _ _ (eq_true (Nat.dvd_of_mem_primeFactors hq)))]
  rw [Finset.prod_div_distrib]
  have hkey := Nat.totient_mul_prod_primeFactors m
  have hcast : ((m.totient : ℝ)) * ∏ q ∈ m.primeFactors, (q : ℝ) =
      (m : ℝ) * ∏ q ∈ m.primeFactors, ((q : ℝ) - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hkey
    simp only [Nat.cast_mul, Nat.cast_prod] at h
    rw [h]
    congr 1
    refine Finset.prod_congr rfl (fun q hq => ?_)
    have := (Nat.prime_of_mem_primeFactors hq).one_le
    rw [Nat.cast_sub this, Nat.cast_one]
  have hφ : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  have hden : ∏ q ∈ m.primeFactors, ((q : ℝ) - 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
    linarith
  rw [div_eq_div_iff hden hφ]
  linarith [hcast]

/-- PROVED. The elementary Euler product lower bound behind page 362 case i. For a summable
family `0 ≤ a i ≤ 1/2`, the product of `1 - a i` converges and is at least
`exp(-2 Σ a i)`, from `log(1 - x) ≥ -2x` on `[0, 1/2]`. -/
theorem leaf_tprod_one_sub_ge {ι : Type*} (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1 / 2) (hs : Summable a) :
    Multipliable (fun i => 1 - a i) ∧
      Real.exp (-2 * ∑' i, a i) ≤ ∏' i, (1 - a i) := by
  have hpos : ∀ i, 0 < 1 - a i := fun i => by linarith [ha1 i]
  have hlog_lb : ∀ i, -2 * a i ≤ Real.log (1 - a i) := by
    intro i
    have hl := Real.one_sub_inv_le_log_of_pos (hpos i)
    have hinv : 1 / (1 - a i) ≤ 1 + 2 * a i := by
      rw [div_le_iff₀ (hpos i)]
      nlinarith [ha0 i, ha1 i]
    rw [inv_eq_one_div] at hl
    linarith
  have hlog_ub : ∀ i, Real.log (1 - a i) ≤ 0 :=
    fun i => Real.log_nonpos (hpos i).le (by linarith [ha0 i])
  have hsl : Summable (fun i => Real.log (1 - a i)) := by
    refine Summable.of_norm_bounded (hs.mul_left 2) (fun i => ?_)
    rw [Real.norm_eq_abs, abs_of_nonpos (hlog_ub i)]
    linarith [hlog_lb i]
  refine ⟨Real.multipliable_of_summable_log hpos hsl, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hpos hsl]
  apply Real.exp_le_exp.mpr
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hlog_lb (hs.mul_left _) hsl

/-- PROVED. The twin prime series `Σ_{p > 2} (p - 1)⁻²` converges, page 362 case i.
A comparison with `Σ n⁻²`. -/
theorem leaf_summable_odd_prime_inv_sq :
    Summable (fun p : Nat.Primes =>
      if (p : ℕ) = 2 then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun p : Nat.Primes => 4 * (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Subtype.val_injective).mul_left 4
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hs
  · split_ifs
    · exact le_rfl
    · positivity
  · have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have h1 : 0 < (p : ℝ) - 1 := by linarith
    split_ifs
    · positivity
    · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- For even `m`, the remaining defect `(p - 1)⁻²` at `p ∤ m` lives on odd primes, so it is
at most `1/4` and at most the twin prime term. PROVED. -/
theorem defect_bounds (m : ℕ) (hm : Even m) (p : Nat.Primes) :
    0 ≤ (if (p : ℕ) ∣ m then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2) ∧
    (if (p : ℕ) ∣ m then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 / 2 ∧
    (if (p : ℕ) ∣ m then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2) ≤
      (if (p : ℕ) = 2 then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2) := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  by_cases hd : (p : ℕ) ∣ m
  · simp only [hd, ite_true]
    refine ⟨le_rfl, by norm_num, ?_⟩
    split_ifs
    · exact le_rfl
    · have : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        linarith
      positivity
  · have hne : (p : ℕ) ≠ 2 := by
      rintro h
      exact hd (h ▸ even_iff_two_dvd.mp hm)
    have hp3 : 3 ≤ (p : ℕ) := by omega
    have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    simp only [hd, hne, ite_false]
    refine ⟨by positivity, ?_, le_rfl⟩
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith

/-- P0082 page 362 Lemma 7 case i: `𝔖(m) ≫ m / φ(m)` for even `m`, with the explicit
constant `exp(-2 Σ_{p > 2} (p - 1)⁻²)`. The named Prop `SingularSeriesEvenLowerBP`.
PROVED, no sorry and no named hypothesis. -/
theorem singularSeriesEvenLowerBP_split : SingularSeriesEvenLowerBP := by
  set b : Nat.Primes → ℝ := fun p =>
    if (p : ℕ) = 2 then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2 with hb
  have hbs : Summable b := leaf_summable_odd_prime_inv_sq
  refine ⟨Real.exp (-2 * ∑' p, b p), Real.exp_pos _, ?_⟩
  intro m hm hev
  set a : Nat.Primes → ℝ := fun p =>
    if (p : ℕ) ∣ m then (0 : ℝ) else 1 / ((p : ℝ) - 1) ^ 2 with ha
  set u : Nat.Primes → ℝ := fun p =>
    if (p : ℕ) ∣ m then (p : ℝ) / ((p : ℝ) - 1) else 1 with hu
  have hab := defect_bounds m hev
  have ha0 : ∀ p, 0 ≤ a p := fun p => (hab p).1
  have ha1 : ∀ p, a p ≤ 1 / 2 := fun p => (hab p).2.1
  have hle : ∀ p, a p ≤ b p := fun p => (hab p).2.2
  have has : Summable a := Summable.of_nonneg_of_le ha0 hle hbs
  obtain ⟨hmv, hv⟩ := leaf_tprod_one_sub_ge a ha0 ha1 has
  obtain ⟨hmu, hu'⟩ := leaf_prod_primeFactors_ratio m hm
  have hsplit : singularSeries m = (∏' p, u p) * ∏' p, (1 - a p) := by
    unfold singularSeries
    rw [← hmu.tprod_mul hmv]
    exact tprod_congr (fun p => factor_split m p)
  have hsum : ∑' p, a p ≤ ∑' p, b p := Summable.tsum_le_tsum hle has hbs
  have hexp : Real.exp (-2 * ∑' p, b p) ≤ Real.exp (-2 * ∑' p, a p) :=
    Real.exp_le_exp.mpr (by linarith)
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ : 0 ≤ (m : ℝ) / (m.totient : ℝ) := by positivity
  rw [hsplit, hu']
  calc Real.exp (-2 * ∑' p, b p) * ((m : ℝ) / (m.totient : ℝ))
      = ((m : ℝ) / (m.totient : ℝ)) * Real.exp (-2 * ∑' p, b p) := by ring
    _ ≤ ((m : ℝ) / (m.totient : ℝ)) * ∏' p, (1 - a p) :=
        mul_le_mul_of_nonneg_left (hexp.trans hv) hρ

/-- The integer form `SingSeriesLowerHyp` of `DQLeafCoprimeSelectedDecisions`, the same
bound on page 362 case i, from the natural form. PROVED. -/
theorem singSeriesLowerHyp_split : SingSeriesLowerHyp := by
  obtain ⟨C, hC, h⟩ := singularSeriesEvenLowerBP_split
  refine ⟨C, hC, ?_⟩
  intro m hm hev
  have hnn : 0 ≤ m := by omega
  have hk : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hnn
  have hk1 : 1 ≤ m.toNat := by omega
  have hkev : Even m.toNat := by
    rw [← hk] at hev; exact (Int.even_coe_nat _).mp hev
  have heq : singSeries m = singularSeries m.toNat := by
    unfold singSeries singularSeries
    refine tprod_congr (fun p => ?_)
    have hd : (((p : ℕ) : ℤ) ∣ m) ↔ (p : ℕ) ∣ m.toNat := by
      conv_lhs => rw [← hk]
      exact Int.natCast_dvd_natCast
    simp only [hd]
  rw [heq]
  exact h m.toNat hk1 hkev

/-- P0082 page 362 Lemma 7 case i, the exact type of `Decomp559b.leaf_absent_selected`,
CONDITIONAL ON the cited `Lemma2NoExcBP` only, Montgomery and Vaughan 1975 through
P0082 Lemma 2. The second named hypothesis is discharged by the proof above. -/
theorem leaf_absent_selected_of_lemma2_only
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected :=
  LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.leaf_absent_selected_of_lemma2 hL
    singularSeriesEvenLowerBP_split

/-- P0082 page 363 case ii a, the exact type of `Decomp559b.leaf_coprime_selected`,
CONDITIONAL ON the cited `BPLemma3CoprimeHyp` and `LandauRealZeroHyp` only. -/
theorem leaf_coprime_selected_of_two_hyps
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hLa : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.LandauRealZeroHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected :=
  LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.leaf_coprime_selected_of_hyps hL3
    singSeriesLowerHyp_split hLa

#print axioms singularSeriesEvenLowerBP_split
#print axioms singSeriesLowerHyp_split

end LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries
