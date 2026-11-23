import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions

/-!
Proof of the named hypothesis `SingSeriesLowerHyp` of
`LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions`, burst-20261122 feed1122,
session S89. Source P0082, Brudern and Perelli 1998, page 362 case i: for even `m ≥ 1` the
singular series of display 11 is at least a constant times `m / φ(m)`.

This is the leaf `leaf_even_sing_series_lower` of the feed1122 split of
`leaf_even_index_coefficient_domination`, on the branch
`claude/ExceptionalSet-feed1122-SPLIT_leaf_coprime_even_index`; this file closes it once both are
merged.

The Euler product factors as `g * h` with `g p = 1 + 1/(p-1)` on primes dividing `m` and `1`
otherwise, and `h p = 1 - 1/(p-1)^2` on primes not dividing `m` and `1` otherwise. The finite
product of `g` is `m / φ(m)` by Euler's product formula `Nat.totient_mul_prod_primeFactors`.
Since `m` is even, every prime not dividing `m` is at least `3`, so `h ≥ h₀` with `h₀ 2 = 1` and
`h₀ p = 1 - 1/(p-1)^2` otherwise, and the product of `h` is at least the absolute constant
`exp (∑ log h₀)`, by comparing logarithms.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected

open Real Finset

/-- `1/(p-1)^2` is summable over the primes. -/
theorem summable_inv_pred_sq_primes :
    Summable (fun p : Nat.Primes => 1 / (((p : ℕ) : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun n : ℕ => 4 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hs.subtype (fun n => n.Prime))
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have ha : 0 < ((p : ℕ) : ℝ) ^ 2 / 4 := by positivity
  have hle : ((p : ℕ) : ℝ) ^ 2 / 4 ≤ (((p : ℕ) : ℝ) - 1) ^ 2 := by nlinarith
  have h1 := one_div_le_one_div_of_le ha hle
  have h2 : 4 * (1 / ((p : ℕ) : ℝ) ^ 2) = 1 / (((p : ℕ) : ℝ) ^ 2 / 4) := by
    field_simp
  show 1 / (((p : ℕ) : ℝ) - 1) ^ 2 ≤ 4 * (1 / ((p : ℕ) : ℝ) ^ 2)
  rw [h2]
  exact h1

/-- Euler's product formula in the form `∏_{p ∣ M} (1 + 1/(p-1)) = M / φ(M)`. -/
theorem prod_primeFactors_one_add_inv_pred (M : ℕ) (hM : 1 ≤ M) :
    ∏ p ∈ M.primeFactors, (1 + 1 / ((p : ℝ) - 1)) = (M : ℝ) / (M.totient : ℝ) := by
  have hE := Nat.totient_mul_prod_primeFactors M
  have hER : (M.totient : ℝ) * ∏ p ∈ M.primeFactors, (p : ℝ) =
      (M : ℝ) * ∏ p ∈ M.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hE
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub this, Nat.cast_one]
  have hpos : ∀ p ∈ M.primeFactors, 0 < (p : ℝ) - 1 := by
    intro p hp
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hstep : ∏ p ∈ M.primeFactors, (1 + 1 / ((p : ℝ) - 1)) =
      ∏ p ∈ M.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have := hpos p hp
    field_simp
    ring
  have hφ : 0 < (M.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hQ : 0 < ∏ p ∈ M.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  rw [hstep, Finset.prod_div_distrib, div_eq_div_iff hQ.ne' hφ.ne']
  linarith [hER]

/-- P0082 page 362 case i, proved: the singular series of display 11 is at least a constant times
`m / φ(m)` for even `m ≥ 1`. -/
theorem singSeriesLowerHyp_proved : SingSeriesLowerHyp := by
  classical
  let h₀ : Nat.Primes → ℝ := fun p =>
    1 + (if (p : ℕ) = 2 then 0 else -(1 / (((p : ℕ) : ℝ) - 1) ^ 2))
  have hu₀ : Summable (fun p : Nat.Primes =>
      (if (p : ℕ) = 2 then (0 : ℝ) else -(1 / (((p : ℕ) : ℝ) - 1) ^ 2))) := by
    refine Summable.of_norm_bounded summable_inv_pred_sq_primes (fun p => ?_)
    split_ifs
    · simp only [norm_zero]; positivity
    · rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  have hlog₀ : Summable (fun p => Real.log (h₀ p)) := Real.summable_log_one_add_of_summable hu₀
  refine ⟨Real.exp (∑' p, Real.log (h₀ p)), Real.exp_pos _, ?_⟩
  intro m hm hev
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  rw [Int.toNat_natCast]
  have hM : 1 ≤ M := by exact_mod_cast hm
  have h2M : 2 ∣ M := even_iff_two_dvd.mp (Int.even_coe_nat M |>.mp hev)
  let g : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ M then 1 + 1 / (((p : ℕ) : ℝ) - 1) else 1
  let u : Nat.Primes → ℝ := fun p => if (p : ℕ) ∣ M then 0 else -(1 / (((p : ℕ) : ℝ) - 1) ^ 2)
  let h : Nat.Primes → ℝ := fun p => 1 + u p
  have hfac : singSeries (M : ℤ) = ∏' p, g p * h p := by
    unfold singSeries
    congr 1
    funext p
    simp only [g, h, u, Int.natCast_dvd_natCast]
    split_ifs <;> ring
  have hu : Summable u := by
    refine Summable.of_norm_bounded summable_inv_pred_sq_primes (fun p => ?_)
    simp only [u]
    split_ifs
    · simp only [norm_zero]; positivity
    · rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  have hmh : Multipliable h := Real.multipliable_one_add_of_summable hu
  let e : M.primeFactors → Nat.Primes := fun x => ⟨x.1, Nat.prime_of_mem_primeFactors x.2⟩
  have he : Set.InjOn e (M.primeFactors.attach : Set M.primeFactors) := by
    intro x _ y _ hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    exact this
  let S : Finset Nat.Primes := M.primeFactors.attach.image e
  have hgS : ∀ p ∉ S, g p = 1 := by
    intro p hp
    simp only [g]
    split_ifs with hd
    · exfalso
      apply hp
      have hmem : (p : ℕ) ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨p.2, hd, by omega⟩
      exact Finset.mem_image.mpr ⟨⟨(p : ℕ), hmem⟩, Finset.mem_attach _ _, rfl⟩
    · rfl
  have hmg : Multipliable g := multipliable_of_ne_finset_one hgS
  have hg : ∏' p, g p = (M : ℝ) / (M.totient : ℝ) := by
    rw [tprod_eq_prod hgS, ← prod_primeFactors_one_add_inv_pred M hM]
    simp only [S]
    rw [Finset.prod_image he]
    rw [← Finset.prod_attach M.primeFactors (fun p : ℕ => 1 + 1 / ((p : ℝ) - 1))]
    refine Finset.prod_congr rfl (fun x _ => ?_)
    simp only [g]
    rw [if_pos (Nat.dvd_of_mem_primeFactors x.2)]
  have hhpos : ∀ p, 0 < h p := by
    intro p
    simp only [h, u]
    split_ifs with hd
    · norm_num
    · have hp2 : (p : ℕ) ≠ 2 := fun h2 => hd (h2 ▸ h2M)
      have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by
        have := p.2.two_le
        exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
      have hq : (4 : ℝ) ≤ (((p : ℕ) : ℝ) - 1) ^ 2 := by nlinarith
      have : 1 / (((p : ℕ) : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq
      linarith
  have hh₀pos : ∀ p, 0 < h₀ p := by
    intro p
    simp only [h₀]
    split_ifs with hd
    · norm_num
    · have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by
        have := p.2.two_le
        exact_mod_cast (show 3 ≤ (p : ℕ) by omega)
      have hq : (4 : ℝ) ≤ (((p : ℕ) : ℝ) - 1) ^ 2 := by nlinarith
      have : 1 / (((p : ℕ) : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq
      linarith
  have hlog : Summable (fun p => Real.log (h p)) := Real.summable_log_one_add_of_summable hu
  have hcmp : ∀ p, Real.log (h₀ p) ≤ Real.log (h p) := by
    intro p
    apply Real.log_le_log (hh₀pos p)
    simp only [h₀, h, u]
    by_cases hd : (p : ℕ) ∣ M
    · rw [if_pos hd]
      split_ifs
      · norm_num
      · have : 0 ≤ 1 / (((p : ℕ) : ℝ) - 1) ^ 2 := by positivity
        linarith
    · have hp2 : (p : ℕ) ≠ 2 := fun h2 => hd (h2 ▸ h2M)
      rw [if_neg hd, if_neg hp2]
  have hh : Real.exp (∑' p, Real.log (h₀ p)) ≤ ∏' p, h p := by
    rw [← Real.rexp_tsum_eq_tprod hhpos hlog]
    exact Real.exp_le_exp.mpr (Summable.tsum_le_tsum hcmp hlog₀ hlog)
  rw [hfac, hmg.tprod_mul hmh, hg]
  have hr : 0 ≤ (M : ℝ) / (M.totient : ℝ) := by positivity
  calc Real.exp (∑' p, Real.log (h₀ p)) * ((M : ℝ) / (M.totient : ℝ))
      ≤ (∏' p, h p) * ((M : ℝ) / (M.totient : ℝ)) := mul_le_mul_of_nonneg_right hh hr
    _ = (M : ℝ) / (M.totient : ℝ) * ∏' p, h p := by ring

end LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected
