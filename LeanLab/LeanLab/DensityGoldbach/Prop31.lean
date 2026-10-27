/-
P0038 Shao 2012, Proposition 3.1 in full: m squarefree with gcd(m, 30) = 1, f from the
reduced residues mod m to [0, 1] with average above 5/8; every x mod m is a + b + c with
reduced a, b, c and h(f a, f b, f c) > 0. Hence Proposition 1.4 for every such m.
Induction over the prime factors: base 1 or 7, then `prop31_step` for each prime ≥ 11.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0111.
-/
import LeanLab.DensityGoldbach.Prop31Step
import LeanLab.DensityGoldbach.Local

open Finset

namespace LeanLab.DensityGoldbach

/-- `Prop31` does not depend on how the modulus is written. -/
lemma prop31_congr {m n : ℕ} (h : m = n) {_ : NeZero m} {_ : NeZero n} (hm : Prop31 m) :
    Prop31 n := by
  subst h; exact hm

/-- The trivial modulus. -/
lemma prop31_one : Prop31 1 := by
  intro f hf hsum x
  have hU : (0 : ZMod 1) ∈ unitsMod 1 := mem_filter.2 ⟨mem_univ _, isUnit_of_subsingleton _⟩
  have hUe : unitsMod 1 = {0} := by
    ext u; rw [mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ hU⟩
  rw [hUe, sum_singleton, Nat.totient_one, Nat.cast_one] at hsum
  refine ⟨0, hU, 0, hU, 0, hU, Subsingleton.elim _ _, ?_⟩
  unfold hfun
  nlinarith [(hf 0).1]

/-- Induction over a finset of primes `≥ 11` coprime to the base modulus. -/
theorem prop31_prod (m₀ : ℕ) [NeZero m₀] (h₀ : Prop31 m₀) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 11 ≤ p) (hcop : ∀ p ∈ S, m₀.Coprime p) :
    ∀ n (_ : n = m₀ * ∏ p ∈ S, p) (_ : NeZero n), Prop31 n := by
  induction S using Finset.induction_on with
  | empty =>
    intro n hn _
    exact prop31_congr (by simp [hn]) h₀
  | insert a s ha ih =>
    intro n hn _
    have hpos : ∀ p ∈ s, 0 < p := fun p hp => (hS p (mem_insert_of_mem hp)).1.pos
    have hprod : 0 < ∏ p ∈ s, p := prod_pos hpos
    have hm0 : 0 < m₀ := Nat.pos_of_ne_zero (NeZero.ne m₀)
    set k := m₀ * ∏ p ∈ s, p with hk
    have hk0 : NeZero k := ⟨(Nat.mul_pos hm0 hprod).ne'⟩
    have ih' : Prop31 k := ih (fun p hp => hS p (mem_insert_of_mem hp))
      (fun p hp => hcop p (mem_insert_of_mem hp)) k rfl hk0
    obtain ⟨hap, ha11⟩ := hS a (mem_insert_self a s)
    have : Fact a.Prime := ⟨hap⟩
    have hka : NeZero (k * a) := ⟨(Nat.mul_pos (Nat.mul_pos hm0 hprod) hap.pos).ne'⟩
    have hc : k.Coprime a := by
      refine Nat.coprime_mul_iff_left.2 ⟨hcop a (mem_insert_self a s), ?_⟩
      refine Nat.Coprime.prod_left fun p hp => ?_
      obtain ⟨hpp, _⟩ := hS p (mem_insert_of_mem hp)
      exact (Nat.coprime_primes hpp hap).2 (fun h => ha (h ▸ hp))
    have step : Prop31 (k * a) := prop31_step k a ha11 hc ih'
    have heq : k * a = n := by rw [hn, prod_insert ha, hk]; ring
    exact prop31_congr heq step

lemma prime_ge_eleven {p : ℕ} (hp : p.Prime) (h30 : p.Coprime 30) (h7 : p ≠ 7) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  have h2 := hp.two_le
  interval_cases p <;> revert hp h30 h7 <;> decide

/-- **Shao Proposition 3.1**: every squarefree `m` coprime to `30`. -/
theorem prop31 (m : ℕ) [NeZero m] (hsq : Squarefree m) (h30 : m.Coprime 30) : Prop31 m := by
  have hm : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsq
  have hfac : ∀ p ∈ m.primeFactors, p.Prime ∧ p.Coprime 30 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp,
      Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) h30⟩
  by_cases h7 : 7 ∈ m.primeFactors
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hS : ∀ p ∈ m.primeFactors.erase 7, p.Prime ∧ 11 ≤ p := fun p hp => by
      obtain ⟨hne, hp'⟩ := mem_erase.1 hp
      exact ⟨(hfac p hp').1, prime_ge_eleven (hfac p hp').1 (hfac p hp').2 hne⟩
    have hc : ∀ p ∈ m.primeFactors.erase 7, (7 : ℕ).Coprime p := fun p hp =>
      (Nat.coprime_primes (by norm_num) (hS p hp).1).2 (fun h => (mem_erase.1 hp).1 h.symm)
    have he : 7 * ∏ p ∈ m.primeFactors.erase 7, p = m := by rw [mul_prod_erase m.primeFactors (fun p => p) h7, hm]
    exact prop31_prod 7 (prop31_prime 7 le_rfl) _ hS hc m he.symm inferInstance
  · have hS : ∀ p ∈ m.primeFactors, p.Prime ∧ 11 ≤ p := fun p hp =>
      ⟨(hfac p hp).1, prime_ge_eleven (hfac p hp).1 (hfac p hp).2 (fun h => h7 (h ▸ hp))⟩
    have he : 1 * ∏ p ∈ m.primeFactors, p = m := by rw [one_mul, hm]
    exact prop31_prod 1 prop31_one _ hS (fun p _ => Nat.coprime_one_left p) m he.symm inferInstance

/-- **Shao Proposition 1.4 for every squarefree `m` coprime to `30`.** -/
theorem prop14_coprime30 (m : ℕ) [NeZero m] (hsq : Squarefree m) (h30 : m.Coprime 30) :
    Prop14 m :=
  prop14_of_prop31 m (prop31 m hsq h30)

/-- **Shao Corollary 1.5 for every squarefree `m` coprime to `30`.** -/
theorem cor15_coprime30 (m : ℕ) [NeZero m] (hsq : Squarefree m) (h30 : m.Coprime 30) :
    Cor15 m :=
  cor15_of_prop14 m (prop14_coprime30 m hsq h30)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.prop14_coprime30
#print axioms LeanLab.DensityGoldbach.cor15_coprime30
