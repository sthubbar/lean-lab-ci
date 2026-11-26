import LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP3
import LeanLab.AlmostPrimes.Decomp1528b

/-!
AI wrote this Lean code, burst S117 burst-20261122 final round. Binary Goldbach is open.
Split of `Decomp243aFeed1122LowerP3.leaf_linearDensity_totient`, the density condition of
Iwaniec Kowalski 6.34 for `g(p) = 1/(p-1)` on the odd sifting primes of BJS
https://arxiv.org/abs/2207.09452 p. 43 equation 142, into Mertens' product theorem in block
form and the convergent extra factor `∏ (1 + 1/(p(p-2)))`, via the exact identity
`(1 - 1/(p-1))⁻¹ = (1 - 1/p)⁻¹ (1 + 1/(p(p-2)))` for `p ≥ 3`.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP4

open Finset Real
open LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower

noncomputable section

/-- Helper, AI wrote it in S146: a local Mertens factor at a prime is at least one. -/
lemma s146_fac_ge_one {p : ℝ} (hp : 2 ≤ p) : 1 ≤ (1 - 1 / p)⁻¹ := by
  have h1 : 0 < 1 - 1 / p := by
    have : 1 / p ≤ 1 / 2 := by gcongr
    linarith
  have h2 : 1 - 1 / p ≤ 1 := by
    have : 0 ≤ 1 / p := by positivity
    linarith
  exact one_le_inv₀ h1 |>.mpr h2

/-- Helper, AI wrote it in S146: `(1 - 1/q)⁻¹ ≤ exp(2/log w)` for `2 ≤ w ≤ q`. -/
lemma s146_fac_le_exp {q w : ℝ} (hw : 2 ≤ w) (hq : w ≤ q) : (1 - 1 / q)⁻¹ ≤ exp (2 / log w) := by
  have hq2 : 2 ≤ q := le_trans hw hq
  have hqp : 0 < q - 1 := by linarith
  have heq : (1 - 1 / q)⁻¹ = 1 + 1 / (q - 1) := by
    field_simp
    ring
  rw [heq]
  have hx := add_one_le_exp (1 / (q - 1))
  refine le_trans (by rw [add_comm]; exact hx) (exp_le_exp.mpr ?_)
  have hlw : 0 < log w := log_pos (by linarith)
  have hlw2 : log w ≤ w - 1 := by
    have := log_le_sub_one_of_pos (show 0 < w by linarith); linarith
  rw [div_le_div_iff₀ hqp hlw]
  nlinarith

/-- Helper, AI wrote it in S146: `exp t ≤ 1 + exp c * t` for `0 ≤ t ≤ c`. -/
lemma s146_exp_le_one_add {t c : ℝ} (ht : 0 ≤ t) (htc : t ≤ c) : exp t ≤ 1 + exp c * t := by
  have h1 := add_one_le_exp (-t)
  have h2 : exp (-t) * exp t = 1 := by rw [← exp_add]; simp
  have h3 : exp t ≤ exp c := exp_le_exp.mpr htc
  have h4 : 0 < exp t := exp_pos t
  nlinarith

/-- LEAF: Mertens' third theorem in block form, Iwaniec Kowalski equation 6.34 with
`g(p) = 1/p`, Mertens 1874, restricted to any finite set of primes in `[w, w')`; the local
factors are at least `1`, so it follows from the full block, compare the PROVED
`LeanLab.AlmostPrimes.Decomp1528b.mertens3_block` up to endpoint conventions and the bound
`exp(c/log w) ≤ 1 + K/log w`. Class MEDIUM. -/
theorem leaf_mertens_block_subset :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset ℕ) (w w' : ℝ), 2 ≤ w → w < w' →
      (∀ p ∈ S, p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < w') →
      ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ log w' / log w * (1 + K / log w) := by
  have hL2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨exp (7 / log 2) * 7, by positivity, fun S w w' hw hww' hS => ?_⟩
  have hw0 : 0 < w := by linarith
  have hlw : 0 < log w := log_pos (by linarith)
  have hlw' : 0 < log w' := log_pos (by linarith)
  set T := (Ioc ⌊w⌋₊ ⌊w'⌋₊).filter Nat.Prime with hT
  set q : ℕ := ⌈w⌉₊ with hq
  have hwq : w ≤ (q : ℝ) := Nat.le_ceil w
  have hq2 : (2 : ℝ) ≤ q := le_trans hw hwq
  -- S ⊆ insert q T
  have hsub : S ⊆ insert q T := by
    intro p hp
    obtain ⟨hpp, hwp, hpw'⟩ := hS p hp
    rcases eq_or_ne p q with h | h
    · rw [h]; exact mem_insert_self _ _
    · apply mem_insert_of_mem
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, hpp⟩
      · have hqp : q ≤ p := Nat.ceil_le.mpr hwp
        have hqp' : q < p := lt_of_le_of_ne hqp (Ne.symm h)
        have : ⌊w⌋₊ ≤ q := Nat.floor_le_ceil w
        omega
      · exact Nat.le_floor hpw'.le
  have hge : ∀ p ∈ insert q T, 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    rcases mem_insert.mp hp with h | h
    · rw [h]; exact s146_fac_ge_one hq2
    · exact s146_fac_ge_one (by exact_mod_cast (mem_filter.mp h).2.two_le)
  have h1 : ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ ∏ p ∈ insert q T, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => le_trans zero_le_one (hge p (hsub hp))) (fun p hp _ => hge p hp)
  have hTnn : 0 ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_nonneg fun p hp => le_trans zero_le_one (hge p (mem_insert_of_mem hp))
  have h2 : ∏ p ∈ insert q T, (1 - 1 / (p : ℝ))⁻¹ ≤
      (1 - 1 / (q : ℝ))⁻¹ * ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ := by
    by_cases hqT : q ∈ T
    · rw [insert_eq_of_mem hqT]
      exact le_mul_of_one_le_left hTnn (s146_fac_ge_one hq2)
    · rw [prod_insert hqT]
  -- Mertens block
  have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens3_block hw hww'.le
  set A := ∏ p ∈ T, (1 - (1 : ℝ) / p) with hA
  have hApos : 0 < A := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    linarith
  have hfl : (w / 2) ≤ (⌊w⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one w
    have : (1 : ℝ) ≤ ⌊w⌋₊ := by exact_mod_cast Nat.le_floor (by norm_num; linarith)
    linarith
  have hE : 4 / log w + 1 / (2 * (⌊w⌋₊ : ℝ)) ≤ 5 / log w := by
    have hlw2 : log w ≤ w - 1 := by
      have := log_le_sub_one_of_pos hw0; linarith
    have : 1 / (2 * (⌊w⌋₊ : ℝ)) ≤ 1 / log w := by
      apply one_div_le_one_div_of_le hlw; linarith
    have e : 5 / log w = 4 / log w + 1 / log w := by ring
    linarith
  have hlogA : -(log (log w') - log (log w)) - 5 / log w ≤ log A := by
    have := (abs_le.mp hM).1; linarith
  have hTinv : ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ = A⁻¹ := by
    rw [hA, prod_inv_distrib]
  have h3 : A⁻¹ ≤ log w' / log w * exp (5 / log w) := by
    rw [← exp_log hApos, ← exp_neg]
    calc exp (-log A) ≤ exp (log (log w') - log (log w) + 5 / log w) := exp_le_exp.mpr (by linarith)
      _ = log w' / log w * exp (5 / log w) := by
        rw [exp_add, exp_sub, exp_log hlw', exp_log hlw]
  have hq3 := s146_fac_le_exp hw hwq
  have ht0 : 0 ≤ 7 / log w := by positivity
  have htc : 7 / log w ≤ 7 / log 2 := by
    gcongr
  have h4 := s146_exp_le_one_add ht0 htc
  have hratio : 0 ≤ log w' / log w := by positivity
  calc ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ (1 - 1 / (q : ℝ))⁻¹ * ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ :=
        h1.trans h2
    _ ≤ exp (2 / log w) * (log w' / log w * exp (5 / log w)) := by
        rw [hTinv]
        exact mul_le_mul hq3 h3 (inv_nonneg.mpr hApos.le) (exp_pos _).le
    _ = log w' / log w * exp (7 / log w) := by
        rw [mul_left_comm, ← exp_add]; congr 2; ring
    _ ≤ log w' / log w * (1 + exp (7 / log 2) * 7 / log w) := by
        apply mul_le_mul_of_nonneg_left _ hratio
        calc exp (7 / log w) ≤ 1 + exp (7 / log 2) * (7 / log w) := h4
          _ = 1 + exp (7 / log 2) * 7 / log w := by ring

/-- LEAF: the tail of the convergent product `∏_{p ≥ w, p > 2} (1 + 1/(p(p-2)))` is
`1 + O(1/w)`, hence `1 + O(1/log w)`, Halberstam Richert p. 142 remark on `Ω₂(1)`, for any
finite set of odd primes at least `w`. Class EASY. -/
theorem leaf_extra_factor_tail :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (S : Finset ℕ) (w : ℝ), 2 ≤ w →
      (∀ p ∈ S, p.Prime ∧ 2 < p ∧ w ≤ (p : ℝ)) →
      ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤ 1 + K / log w := by
  refine ⟨6, by norm_num, fun S w hw hS => ?_⟩
  set a : ℕ := max 3 ⌈w⌉₊ with ha
  have ha3 : 3 ≤ a := le_max_left _ _
  have hwa : w ≤ (a : ℝ) := le_trans (Nat.le_ceil w) (by exact_mod_cast le_max_right _ _)
  set b : ℕ := S.sup id + 1 with hb
  -- each element lies in Ico a (a + b)
  have hsub : S ⊆ Finset.image (fun i => a + i) (range b) := by
    intro p hp
    obtain ⟨hpp, h2p, hwp⟩ := hS p hp
    have hap : a ≤ p := by
      apply max_le (by omega)
      exact Nat.ceil_le.mpr hwp
    have hpb : p ≤ S.sup id := Finset.le_sup (f := id) hp
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨p - a, by omega, by omega⟩
  set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 2) with hg
  have hterm : ∀ n : ℕ, 3 ≤ n → 1 / ((n : ℝ) * ((n : ℝ) - 2)) ≤ g n - g (n + 1) := by
    intro n hn
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hg]; push_cast
    have h1 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have h2 : (0 : ℝ) < (n : ℝ) + 1 - 2 := by linarith
    rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hnn : ∀ p ∈ S, 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
    intro p hp
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
    have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  set T := ∑ p ∈ S, 1 / ((p : ℝ) * ((p : ℝ) - 2)) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg hnn
  have hTle : T ≤ g a := by
    have e1 : T ≤ ∑ n ∈ Finset.image (fun i => a + i) (range b), 1 / ((n : ℝ) * ((n : ℝ) - 2)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn _
      simp only [Finset.mem_image, Finset.mem_range] at hn
      obtain ⟨i, _, rfl⟩ := hn
      have h3 : (3 : ℝ) ≤ ((a + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ a + i)
      have : (0 : ℝ) < ((a + i : ℕ) : ℝ) - 2 := by linarith
      positivity
    rw [Finset.sum_image (fun x _ y _ h => by simpa using h)] at e1
    have e2 : ∑ i ∈ range b, 1 / (((a + i : ℕ) : ℝ) * (((a + i : ℕ) : ℝ) - 2)) ≤
        ∑ i ∈ range b, (g (a + i) - g (a + (i + 1))) :=
      Finset.sum_le_sum fun i _ => by
        have := hterm (a + i) (by omega); simpa [add_assoc] using this
    rw [Finset.sum_range_sub' (fun i => g (a + i))] at e2
    have hgpos : 0 ≤ g (a + b) := by
      simp only [hg]
      have : (3 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ a + b)
      apply div_nonneg zero_le_one; linarith
    simp only [add_zero] at e2
    linarith
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha3
  have hga1 : g a ≤ 1 := by
    simp only [hg]; rw [div_le_one (by linarith)]; linarith
  have hga3 : g a ≤ 3 / w := by
    simp only [hg]
    have hw0 : 0 < w := by linarith
    rw [div_le_div_iff₀ (by linarith) hw0]; nlinarith
  have hlog : 0 < log w := log_pos (by linarith)
  have hlogw : log w ≤ w := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  have h3w : 3 / w ≤ 3 / log w := div_le_div_of_nonneg_left (by norm_num) hlog hlogw
  have hprod : ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) ≤ exp T := by
    rw [hT, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun p hp => by linarith [hnn p hp])
      (fun p _ => by rw [add_comm]; exact Real.add_one_le_exp _)
  have hexp : exp T ≤ 1 + 2 * T := by
    have h := Real.abs_exp_sub_one_le (x := T) (by rw [abs_of_nonneg hT0]; linarith)
    rw [abs_of_nonneg hT0] at h
    linarith [le_abs_self (exp T - 1)]
  have : 2 * T ≤ 6 / log w := by
    have : T ≤ 3 / log w := by linarith
    calc 2 * T ≤ 2 * (3 / log w) := by linarith
      _ = 6 / log w := by ring
  linarith

/-- The local identity `(1 - 1/(p-1))⁻¹ = (1 - 1/p)⁻¹ (1 + 1/(p(p-2)))` for `p ≥ 3`. -/
theorem local_factor_split {p : ℝ} (hp : 3 ≤ p) :
    (1 - 1 / (p - 1))⁻¹ = (1 - 1 / p)⁻¹ * (1 + 1 / (p * (p - 2))) := by
  have h1 : p - 1 ≠ 0 := by intro h; linarith
  have h2 : p - 2 ≠ 0 := by intro h; linarith
  have h0 : p ≠ 0 := by intro h; linarith
  have h3 : 1 - 1 / (p - 1) = (p - 2) / (p - 1) := by field_simp; ring
  have h4 : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [h3, h4, inv_div, inv_div]
  field_simp
  ring

/-- Every prime factor of the sifting primorial is odd. -/
theorem two_lt_of_mem_primeFactors {N : ℕ} {θ : ℝ} {p : ℕ}
    (hp : p ∈ (sievePrimorial N θ).primeFactors) : 2 < p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  unfold sievePrimorial at hd
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).mp hd
  obtain ⟨-, hq1, hq2, -⟩ := mem_filter.mp hq
  rw [(Nat.prime_dvd_prime_iff_eq hpp hq1).mp hpq]
  exact hq2

/-- `leaf_linearDensity_totient` with the same statement, from the two leaves. -/
theorem leaf_linearDensity_totient_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (w w' : ℝ), 2 ≤ w → w < w' →
      ∏ p ∈ (sievePrimorial N ((1 : ℝ) / 8)).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ log w' / log w * (1 + K / log w) := by
  obtain ⟨K1, hK1, hM⟩ := leaf_mertens_block_subset
  obtain ⟨K2, hK2, hE⟩ := leaf_extra_factor_tail
  refine ⟨K1 + K2 + K1 * K2 / log 2, by positivity, fun N w w' hw hww' => ?_⟩
  set S := (sievePrimorial N ((1 : ℝ) / 8)).primeFactors.filter
    (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w')
  have hmem : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < w' := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hp1, two_lt_of_mem_primeFactors hp1, hp2, hp3⟩
  have hsplit : ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))⁻¹ =
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by
      have := (hmem p hp).2.1; exact_mod_cast this
    exact local_factor_split h3
  have hA := hM S w w' hw hww' (fun p hp => ⟨(hmem p hp).1, (hmem p hp).2.2⟩)
  have hB := hE S w hw (fun p hp => ⟨(hmem p hp).1, (hmem p hp).2.1, (hmem p hp).2.2.1⟩)
  have hBnn : 0 ≤ ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    refine prod_nonneg fun p hp => ?_
    have h3 : (3 : ℝ) ≤ p := by
      have := (hmem p hp).2.1; exact_mod_cast this
    have : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
      apply div_nonneg zero_le_one; nlinarith
    linarith
  have hL2 : 0 < log 2 := log_pos (by norm_num)
  have hLw : log 2 ≤ log w := log_le_log (by norm_num) hw
  have hL : 0 < log w := lt_of_lt_of_le hL2 hLw
  have hL' : 0 < log w' := log_pos (by linarith)
  have hR1 : 0 ≤ log w' / log w * (1 + K1 / log w) := by positivity
  rw [hsplit]
  calc (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ S, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))
      ≤ (log w' / log w * (1 + K1 / log w)) * (1 + K2 / log w) :=
        mul_le_mul hA hB hBnn hR1
    _ ≤ log w' / log w * (1 + (K1 + K2 + K1 * K2 / log 2) / log w) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hq : K1 * K2 / log w / log w ≤ K1 * K2 / log 2 / log w := by
          apply div_le_div_of_nonneg_right _ hL.le
          exact div_le_div_of_nonneg_left (by positivity) hL2 hLw
        have : (1 + K1 / log w) * (1 + K2 / log w) =
            1 + (K1 + K2) / log w + K1 * K2 / log w / log w := by
          field_simp; ring
        rw [this]
        have : 1 + (K1 + K2 + K1 * K2 / log 2) / log w =
            1 + (K1 + K2) / log w + K1 * K2 / log 2 / log w := by
          field_simp; ring
        rw [this]; linarith

end

end LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP4
