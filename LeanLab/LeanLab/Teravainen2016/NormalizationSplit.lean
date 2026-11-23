/-
P0076, Section 4, page 15, the lower bound for G_1 after display 4.3.
Split of the uniform normalization leaf paper_enveloping_normalization_input in
MainInputsRestriction.lean into two cited LEAF pieces, a proved Mertens step and a proved assembly.
The paper chain is G_1 of z at least 10^-10 times the product over w < p < z of
the inverse of 1 - omega p / p, which is at least 10^-20 times log N to the 3/2
times log w to the -3/2. The assembly also uses phi W / W at most 1 / log w.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputsRestriction
import LeanLab.AlmostPrimes.Decomp1528b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: page 15, first inequality of the display after display 4.3,
G_1 of z is at least 10^-10 times the product over w < p < z of the inverse of 1 - omega p / p.
Class HARD. It is the Selberg sieve lower bound for the truncated sum G_1 of the
dimension 3/2 multiplicative weight h, as in reference 18 Section 4 and reference 10 Chapter 7.
The prime range uses the inclusive endpoint p at most z of envelopingPrimeProduct, see the
endpoint QUESTION in PROGRESS.md; any positive constant is allowed. -/
theorem leaf_G1_ge_euler_product :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ≤ envelopingG w 1 z := by
  sorry

/-- LEAF: page 15, second inequality of the display after display 4.3,
the product over w < p < z of the inverse of 1 - omega p / p is at least a constant times
log z to the 3/2 times log w to the -3/2, with log N equal to 10 log z.
Class MEDIUM. It is the Mertens estimate for primes in the classes 1 and 3 mod 4, where
omega p is 1 and 2, so the sum of omega p / p over w < p at most z is 3/2 log log z
minus 3/2 log log w up to a bounded error. For z below w the product is empty and the
left side is below one. -/
theorem leaf_euler_product_ge_log_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) ≤
        C * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ := by
  sorry

/-- Display 3.3 and display 3.4, the normalization phi W / W of the weight f
compared with log w, as used on page 15 to match the lower bound of G_1.
PROVED: every prime p at most w divides W = 2^J 3^3 times the primes 5 to w, so
phi W / W is at most the product over p at most w of 1 - 1/p, which is at most 1 / log w
by the lab's elementary Mertens bound mertens_prod_upper in AlmostPrimes/Decomp1528b. -/
theorem totient_ratio_le_inv_log :
    ∀ J w : ℕ, 5 ≤ J → wBig ≤ w →
      (Nat.totient (WW J w).toNat : ℝ) / WW J w ≤ 1 / Real.log w := by
  intro J w hJ hw
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  set n : ℕ := 2 ^ J * 27 * ∏ p ∈ Sw w, p with hn
  have hWn : WW J w = (n : ℤ) := by
    simp only [WW, Wmod, hn]; push_cast; ring
  have hn0 : n ≠ 0 := by
    rw [hn]
    refine mul_ne_zero (by positivity) ?_
    exact prod_ne_zero_iff.mpr fun p hp => (Sw_spec w p hp).1.ne_zero
  rw [hWn, Int.toNat_natCast]
  push_cast
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hφ : (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    exact h
  rw [hφ, mul_div_cancel_left₀ _ hnr.ne']
  have hsub : Nat.primesLE w ⊆ n.primeFactors := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hpw : p ≤ w := Nat.le_of_mem_primesLE hp
    rw [Nat.mem_primeFactors]
    refine ⟨hpp, ?_, hn0⟩
    rw [hn]
    by_cases h2 : p = 2
    · subst h2
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _
    by_cases h3 : p = 3
    · subst h3
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by norm_num) _) _
    have h5 : 5 ≤ p := by
      have := hpp.two_le
      rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h4
      · subst h4; exact absurd hpp (by decide)
      · exact h4
    apply Dvd.dvd.mul_left
    apply dvd_prod_of_mem
    simp only [Sw, mem_filter, mem_Icc]
    exact ⟨⟨h5, hpw⟩, hpp⟩
  have hfac : ∀ p ∈ n.primeFactors, 0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    intro p hp
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    constructor
    · rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1
    · have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      linarith
  have hle : ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) ≤
      ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) := by
    rw [← prod_sdiff hsub]
    have h1 : ∏ p ∈ n.primeFactors \ Nat.primesLE w, (1 - (p : ℝ)⁻¹) ≤ 1 :=
      prod_le_one₀ (fun p hp => (hfac p (sdiff_subset hp)).1)
        (fun p hp => (hfac p (sdiff_subset hp)).2)
    have h2 : 0 ≤ ∏ p ∈ Nat.primesLE w, (1 - (p : ℝ)⁻¹) :=
      prod_nonneg fun p hp => (hfac p (hsub hp)).1
    nlinarith
  have hm := LeanLab.AlmostPrimes.Decomp1528b.mertens_prod_upper (x := (w : ℝ)) (by linarith)
  rw [Nat.floor_natCast] at hm
  simp only [one_div] at hm ⊢
  exact hle.trans hm


/-- The uniform normalization comparison, exactly the statement of
paper_enveloping_normalization_input, CONDITIONAL ON the two LEAFs above.
Page 15: log L at most log M = 10 log z, then the two inequalities of the display. -/
theorem paper_enveloping_normalization_input_of_leaves :
    ∃ c : ℝ, 0 < c ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w →
      ∀ L M : ℕ, 1 ≤ L → L ≤ M → M ≤ 2 * L →
        Real.log L ^ ((3 : ℝ) / 2) *
          ((Nat.totient (WW J w).toNat : ℝ) / WW J w) ^ ((3 : ℝ) / 2) ≤
            c * envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c₀, hc₀, HA⟩ := leaf_G1_ge_euler_product
  obtain ⟨CB, hCB, HB⟩ := leaf_euler_product_ge_log_ratio
  refine ⟨(10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀, by positivity, ?_⟩
  intro J w hJ hw L M hL hLM hML
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw10 : (10 : ℝ) ≤ w := hwBig1.trans hw
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (hL.trans hLM)
  have hMpos : (0 : ℝ) < M := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set z : ℝ := (M : ℝ) ^ ((1 : ℝ) / 10) with hz
  have hz1 : 1 ≤ z := Real.one_le_rpow hM1 (by norm_num)
  have hlogz : Real.log z = Real.log M / 10 := by
    rw [hz, Real.log_rpow hMpos]; ring
  set r : ℝ := (Nat.totient (WW J w).toNat : ℝ) / WW J w with hr
  have hW0 : (0 : ℤ) < WW J w := by
    unfold WW Wmod
    apply mul_pos (by positivity)
    apply prod_pos
    intro p hp
    exact_mod_cast (Sw_spec w p hp).1.pos
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hW0.le)
  have hrle : r ≤ 1 / Real.log w := totient_ratio_le_inv_log J w hJ hw
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hlogLM : Real.log L ≤ Real.log M :=
    Real.log_le_log hLpos (by exact_mod_cast hLM)
  have hbase : Real.log L * r ≤ 10 * (Real.log z / Real.log w) := by
    calc Real.log L * r ≤ Real.log M * (1 / Real.log w) :=
          mul_le_mul hlogLM hrle hr0 (Real.log_nonneg hM1)
      _ = 10 * (Real.log z / Real.log w) := by rw [hlogz]; field_simp
  have hratio0 : 0 ≤ Real.log z / Real.log w :=
    div_nonneg (Real.log_nonneg hz1) hlogw.le
  have hB := HB w hw z hz1
  have hA := HA w hw z hz1
  calc Real.log L ^ ((3 : ℝ) / 2) * r ^ ((3 : ℝ) / 2)
      = (Real.log L * r) ^ ((3 : ℝ) / 2) := (Real.mul_rpow hlogL0 hr0).symm
    _ ≤ (10 * (Real.log z / Real.log w)) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (mul_nonneg hlogL0 hr0) hbase (by norm_num)
    _ = (10 : ℝ) ^ ((3 : ℝ) / 2) * (Real.log z / Real.log w) ^ ((3 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) hratio0
    _ ≤ (10 : ℝ) ^ ((3 : ℝ) / 2) * (CB * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), (1 - (envelopingOmega w p : ℝ) / p)⁻¹) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀ * (c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter
          (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z), (1 - (envelopingOmega w p : ℝ) / p)⁻¹) := by
        field_simp
    _ ≤ (10 : ℝ) ^ ((3 : ℝ) / 2) * CB / c₀ * envelopingG w 1 z :=
        mul_le_mul_of_nonneg_left hA (by positivity)

end LeanLab.Teravainen2016
