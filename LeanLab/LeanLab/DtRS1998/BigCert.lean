/-
P0037, unit U-0938, run 20261018T1002Z-987. A Lucas certificate chain checker with no 2^64 cap:
the modular power runs with fuel equal to the bit length of p, and a factor of p - 1 is accepted
when trial division proves it prime or when an earlier certificate in the chain did.
Soundness proved once from Mathlib's `lucas_primality`.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Verifications.Pratt

namespace LeanLab.DtRS1998.Big

open LeanLab.Verifications.Pratt

/-- Lucas' test with fuel `F`, `p < 2 ^ F`. -/
theorem prattF (p a F : ℕ) (L : List (ℕ × ℕ)) (hp : p < 2 ^ F)
    (hprod : (L.map fun x => x.1 ^ x.2).prod = p - 1) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : pm F a (p - 1) p = 1 % p)
    (hnot : ∀ x ∈ L, pm F a ((p - 1) / x.1) p % p ≠ 1 % p) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · rw [← pm_cast F a (p - 1) p (by omega), hpow]
    simp
  · intro q hq hqd heq
    rw [← hprod] at hqd
    obtain ⟨y, hy, hyd⟩ := (Nat.prime_iff.mp hq).dvd_prod_iff.mp hqd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hqx : q = x.1 :=
      (Nat.prime_dvd_prime_iff_eq hq (hprimes x hx)).mp (hq.dvd_of_dvd_pow hyd)
    subst hqx
    apply hnot x hx
    have h2 : (p - 1) / x.1 < 2 ^ F := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [← pm_cast F a _ p h2] at heq
    have := (ZMod.natCast_eq_natCast_iff' _ 1 p).mp (by rw [heq]; simp)
    simpa using this

abbrev Cert := ℕ × ℕ × List (ℕ × ℕ)

/-- One certificate, with the primes already known. -/
def certK (known : List ℕ) : Cert → Bool
  | (p, a, L) =>
    let F := p.log2 + 1
    decide (2 ≤ p) && ((L.map fun x => x.1 ^ x.2).prod == p - 1) &&
      L.all (fun x => known.contains x.1 || primeB x.1) && (pm F a (p - 1) p == 1 % p) &&
      L.all (fun x => pm F a ((p - 1) / x.1) p % p != 1 % p)

theorem prime_of_certK {known : List ℕ} (hk : ∀ k ∈ known, k.Prime) {c : Cert}
    (h : certK known c = true) : c.1.Prime := by
  obtain ⟨p, a, L⟩ := c
  simp only [certK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h2, hprod⟩, hfac⟩, hpow⟩, hnot⟩ := h
  refine prattF p a (p.log2 + 1) L Nat.lt_log2_self hprod ?_ hpow hnot
  intro x hx
  rcases hfac x hx with h | h
  · exact hk _ h
  · exact primeB_sound h

/-- A chain: each certificate may use the primes of the earlier ones. -/
def chainB : List ℕ → List Cert → Bool
  | _, [] => true
  | known, c :: t => certK known c && chainB (c.1 :: known) t

theorem chain_sound : ∀ (C : List Cert) (known : List ℕ), (∀ k ∈ known, k.Prime) →
    chainB known C = true → ∀ c ∈ C, c.1.Prime := by
  intro C
  induction C with
  | nil => intro _ _ _ c hc; simp at hc
  | cons c t ih =>
    intro known hk h c' hc'
    simp only [chainB, Bool.and_eq_true] at h
    have hc : c.1.Prime := prime_of_certK hk h.1
    have hk' : ∀ k ∈ c.1 :: known, k.Prime := by
      intro k hk2
      rcases List.mem_cons.mp hk2 with rfl | hk2
      · exact hc
      · exact hk k hk2
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact hc
    · exact ih _ hk' h.2 c' hc'

theorem all_prime {C : List Cert} (h : chainB [] C = true) : ∀ p ∈ C.map Prod.fst, p.Prime := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact chain_sound C [] (by simp) h c hc

/-- Certificates that use only the primes of a proved chain `S`. -/
theorem all_prime_over {S C : List Cert} (hS : chainB [] S = true)
    (hC : C.all (certK (S.map Prod.fst)) = true) : ∀ p ∈ C.map Prod.fst, p.Prime := by
  have hk : ∀ k ∈ S.map Prod.fst, k.Prime := all_prime hS
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact prime_of_certK hk (List.all_eq_true.mp hC c hc)

end LeanLab.DtRS1998.Big
