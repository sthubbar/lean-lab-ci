/-
P0044, Cai 2002, Lemma 5, p. 599-600: the pointwise weight inequality
`λ(a) ≥ 1 - ρ₁(a)/2 - ρ₂(a)/2 - ρ₃(a)` for squarefree `a ≤ N` whose prime factors are all at
least `z₁`, whenever `N < z₁ z₂³`. The paper's cutoffs `z₁ = N^{1/11}`, `z₂ = N^{1/3.29}` meet
this because `1/11 + 3/3.29 > 1`, see `cutoffs_ok`.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Cai2002.Statements

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

namespace LeanLab.Cai2002

lemma card_primeFactors_eq_Omega {a : ℕ} (ha : a ≠ 0) (hsq : Squarefree a) :
    a.primeFactors.card = Ω a := by
  rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree ha).mpr hsq,
    ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

lemma prod_sub_le {a : ℕ} (ha : a ≠ 0) (hsq : Squarefree a) {T : Finset ℕ}
    (hT : T ⊆ a.primeFactors) : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ a := by
  have h1 : (∏ p ∈ T, p) ∣ a := by
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hT
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ha) h1

lemma pow_le_prod_real {T : Finset ℕ} {z : ℝ} (hz : 0 ≤ z) (h : ∀ p ∈ T, z ≤ (p : ℝ)) :
    z ^ T.card ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by
  push_cast
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hz) h

lemma sort2 {x y : ℕ} (hxy : x ≠ y) : ∃ q r : ℕ, q < r ∧ ({q, r} : Finset ℕ) = {x, y} := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, y, h, rfl⟩
  · exact ⟨y, x, h, Finset.pair_comm _ _⟩

lemma sort3 {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ p q r : ℕ, p < q ∧ q < r ∧ ({p, q, r} : Finset ℕ) = {x, y, z} := by
  have key : ∀ p q r : ℕ, ({p, q, r} : Finset ℕ) = {x, y, z} ↔
      (∀ t, (t = p ∨ t = q ∨ t = r) ↔ (t = x ∨ t = y ∨ t = z)) := by
    intro p q r; constructor
    · intro h t; have := congrArg (t ∈ ·) h; simpa using this
    · intro h; ext t; simpa using h t
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, rfl⟩
  · exact ⟨x, z, y, h2, h3, (key _ _ _).2 fun t => by omega⟩
  · omega
  · exact ⟨z, x, y, h2, h1, (key _ _ _).2 fun t => by omega⟩
  · exact ⟨y, x, z, h1, h2, (key _ _ _).2 fun t => by omega⟩
  · omega
  · exact ⟨y, z, x, h3, h2, (key _ _ _).2 fun t => by omega⟩
  · exact ⟨z, y, x, h3, h1, (key _ _ _).2 fun t => by omega⟩

/-- Lemma 5 of Cai 2002, the pointwise inequality behind it, for general cutoffs. -/
theorem lemma5_pointwise (z1 z2 : ℝ) (N a : ℕ) (hz1 : 0 < z1) (hz : z1 ≤ z2)
    (hN : (N : ℝ) < z1 * z2 ^ 3) (ha0 : a ≠ 0) (haN : a ≤ N) (hsq : Squarefree a)
    (hlow : ∀ p ∈ a.primeFactors, z1 ≤ (p : ℝ)) :
    1 - (rho1 z1 z2 a : ℝ) / 2 - (rho2 z1 z2 a : ℝ) / 2 - (rho3 z2 a : ℝ) ≤ (lam a : ℝ) := by
  classical
  set P := a.primeFactors with hP
  set sm := P.filter (fun p : ℕ => ((p : ℕ) : ℝ) < z2) with hsm
  set bg := P.filter (fun p : ℕ => ¬ ((p : ℕ) : ℝ) < z2) with hbg
  have hcard : sm.card + bg.card = P.card := by
    convert card_filter_add_card_filter_not (s := P) (p := fun p : ℕ => (p : ℝ) < z2)
  have haR : (a : ℝ) ≤ N := by exact_mod_cast haN
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha0
  have hz2pos : 0 < z2 := lt_of_lt_of_le hz1 hz
  have hbgz : ∀ p : ℕ, p ∈ bg → z2 ≤ (p : ℝ) := fun p hp => not_lt.mp (mem_filter.1 hp).2
  have hsmP : sm ⊆ P := filter_subset _ _
  have hbgP : bg ⊆ P := filter_subset _ _
  have hz2one : 1 ≤ z2 := by
    by_contra h
    push Not at h
    have h4 : z2 ^ 4 ≤ 1 := pow_le_one₀ hz2pos.le h.le
    have : z1 * z2 ^ 3 ≤ z2 ^ 4 := by
      have := mul_le_mul_of_nonneg_right hz (pow_nonneg hz2pos.le 3)
      calc z1 * z2 ^ 3 ≤ z2 * z2 ^ 3 := this
        _ = z2 ^ 4 := by ring
    linarith
  -- at most three big primes
  have hbg3 : bg.card ≤ 3 := by
    by_contra h
    push Not at h
    have e1 : z2 ^ 4 ≤ z2 ^ bg.card := pow_le_pow_right₀ hz2one h
    have e2 := pow_le_prod_real hz2pos.le hbgz
    have e3 := prod_sub_le ha0 hsq hbgP
    have : z1 * z2 ^ 3 ≤ z2 ^ 4 := by
      have := mul_le_mul_of_nonneg_right hz (pow_nonneg hz2pos.le 3)
      calc z1 * z2 ^ 3 ≤ z2 * z2 ^ 3 := this
        _ = z2 ^ 4 := by ring
    linarith
  -- with a small prime, at most two big primes
  have hbg2 : 1 ≤ sm.card → bg.card ≤ 2 := by
    intro hs
    obtain ⟨p, hp⟩ := card_pos.mp (by omega : 0 < sm.card)
    have hpP : p ∈ P := hsmP hp
    have hpnot : p ∉ bg := fun h => (mem_filter.1 h).2 (mem_filter.1 hp).2
    by_contra h
    push Not at h
    have hsub : insert p bg ⊆ P := insert_subset hpP hbgP
    have e3 := prod_sub_le ha0 hsq hsub
    rw [prod_insert hpnot] at e3
    push_cast at e3
    have e2 := pow_le_prod_real hz2pos.le hbgz
    push_cast at e2
    have e1 : z2 ^ 3 ≤ z2 ^ bg.card := pow_le_pow_right₀ hz2one h
    have hp1 : z1 ≤ (p : ℝ) := hlow p hpP
    have : z1 * z2 ^ 3 ≤ (p : ℝ) * ∏ q ∈ bg, (q : ℝ) :=
      mul_le_mul hp1 (e1.trans e2) (pow_nonneg hz2pos.le 3) (Nat.cast_nonneg _)
    linarith
  have hprod : sm.prod id * bg.prod id = a := by
    have := prod_filter_mul_prod_filter_not (s := P) (f := id) (p := fun p : ℕ => (p : ℝ) < z2)
    rw [← hsm, ← hbg] at this
    rw [this]
    exact Nat.prod_primeFactors_of_squarefree hsq
  have hr1 : (rho1 z1 z2 a : ℝ) = sm.card := by
    have : rho1 z1 z2 a = sm.card := by
      unfold rho1
      rw [hsm]
      apply congrArg Finset.card
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hlow p h1, h3⟩
    exact_mod_cast this
  have h2nn : (0 : ℝ) ≤ rho2 z1 z2 a := Nat.cast_nonneg _
  have h3nn : (0 : ℝ) ≤ rho3 z2 a := Nat.cast_nonneg _
  have hlnn : (0 : ℝ) ≤ lam a := Nat.cast_nonneg _
  have hOm : P.card = Ω a := card_primeFactors_eq_Omega ha0 hsq
  by_cases hP2 : P.card ≤ 2
  · have : lam a = 1 := by
      unfold lam
      rw [if_pos ⟨ha0, by omega⟩]
    rw [this]
    have : (0 : ℝ) ≤ sm.card := Nat.cast_nonneg _
    push_cast
    linarith
  push Not at hP2
  rcases (by omega : 2 ≤ sm.card ∨ sm.card = 1 ∨ sm.card = 0) with hs | hs | hs
  · have : (2 : ℝ) ≤ sm.card := by exact_mod_cast hs
    linarith
  · -- one small prime and exactly two big ones: ρ₂ = 1
    have hb : bg.card = 2 := by have := hbg2 (by omega); omega
    obtain ⟨p1, hsm1⟩ := card_eq_one.mp hs
    obtain ⟨x, y, hxy, hbgxy⟩ := card_eq_two.mp hb
    obtain ⟨q, r, hqr, hqrxy⟩ := sort2 hxy
    have hp1 : p1 ∈ sm := by rw [hsm1]; exact mem_singleton_self _
    have hq : q ∈ bg := by rw [hbgxy, ← hqrxy]; simp
    have hr : r ∈ bg := by rw [hbgxy, ← hqrxy]; simp
    have : rho2 z1 z2 a = 1 := by
      unfold rho2
      rw [if_pos]
      refine ⟨p1, q, r, Nat.prime_of_mem_primeFactors (hsmP hp1),
        Nat.prime_of_mem_primeFactors (hbgP hq), Nat.prime_of_mem_primeFactors (hbgP hr),
        ?_, hlow p1 (hsmP hp1), (mem_filter.1 hp1).2, hbgz q hq, hqr⟩
      rw [← hprod, hsm1, hbgxy, ← hqrxy, prod_singleton, prod_pair hqr.ne, id, id, id, mul_assoc]
    have h2 : (rho2 z1 z2 a : ℝ) = 1 := by exact_mod_cast this
    have h1 : (sm.card : ℝ) = 1 := by exact_mod_cast hs
    linarith
  · -- three big primes: ρ₃ = 1
    have hb : bg.card = 3 := by omega
    obtain ⟨x, y, z, hxy, hxz, hyz, hbgxyz⟩ := card_eq_three.mp hb
    obtain ⟨p, q, r, hpq, hqr, hpqr⟩ := sort3 hxy hxz hyz
    have hp : p ∈ bg := by rw [hbgxyz, ← hpqr]; simp
    have hq : q ∈ bg := by rw [hbgxyz, ← hpqr]; simp
    have hr : r ∈ bg := by rw [hbgxyz, ← hpqr]; simp
    have hsm0 : sm = ∅ := card_eq_zero.mp hs
    have : rho3 z2 a = 1 := by
      unfold rho3
      rw [if_pos]
      refine ⟨p, q, r, Nat.prime_of_mem_primeFactors (hbgP hp),
        Nat.prime_of_mem_primeFactors (hbgP hq), Nat.prime_of_mem_primeFactors (hbgP hr),
        ?_, hbgz p hp, hpq, hqr⟩
      have hpn : p ∉ ({q, r} : Finset ℕ) := by simp; omega
      rw [← hprod, hsm0, hbgxyz, ← hpqr, prod_empty, one_mul, prod_insert hpn,
        prod_pair hqr.ne, id, id, id, mul_assoc]
    have h3 : (rho3 z2 a : ℝ) = 1 := by exact_mod_cast this
    have h1 : (sm.card : ℝ) = 0 := by exact_mod_cast hs
    linarith

/-- The paper's cutoffs satisfy the hypothesis: `N^{1/11} (N^{1/3.29})³ > N` for `N > 1`,
since `1/11 + 3/3.29 = 1.00276… > 1`. -/
theorem cutoffs_ok (N : ℝ) (hN : 1 < N) :
    N < N ^ (1 / 11 : ℝ) * (N ^ (1 / 3.29 : ℝ)) ^ 3 ∧ N ^ (1 / 11 : ℝ) ≤ N ^ (1 / 3.29 : ℝ) := by
  have hN0 : 0 < N := by linarith
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ < N ^ (1 / 11 + 1 / 3.29 * ((3 : ℕ) : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num)
  · exact Real.rpow_le_rpow_of_exponent_le hN.le (by norm_num)

/-- Lemma 5 at the paper's cutoffs: for `N > 1`, squarefree `a ≤ N` with every prime factor at
least `N^{1/11}`, `λ(a) ≥ 1 - ρ₁/2 - ρ₂/2 - ρ₃`. -/
theorem lemma5_cai (N a : ℕ) (hN : 1 < N) (ha0 : a ≠ 0) (haN : a ≤ N) (hsq : Squarefree a)
    (hlow : ∀ p ∈ a.primeFactors, (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ)) :
    1 - (rho1 ((N : ℝ) ^ (1 / 11 : ℝ)) ((N : ℝ) ^ (1 / 3.29 : ℝ)) a : ℝ) / 2
      - (rho2 ((N : ℝ) ^ (1 / 11 : ℝ)) ((N : ℝ) ^ (1 / 3.29 : ℝ)) a : ℝ) / 2
      - (rho3 ((N : ℝ) ^ (1 / 3.29 : ℝ)) a : ℝ) ≤ (lam a : ℝ) := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := cutoffs_ok (N : ℝ) hNR
  exact lemma5_pointwise _ _ N a (Real.rpow_pos_of_pos (by linarith) _) h2 h1 ha0 haN hsq hlow

end LeanLab.Cai2002
