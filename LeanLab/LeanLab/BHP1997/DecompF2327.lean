/-
Split of `leaf_vaughan_326_512`, Vaughan 1981 displays 3.24 and 3.26.
For even N at least 2, the series Σ_q μ(q)²/φ(q)² c_q(-N) converges to the
singular series 𝔖(N/2). The proof: the terms are multiplicative and vanish
for non-squarefree q, so the sum equals the Euler product over primes of
(1 + μ(p)²/φ(p)² c_p(-N)); at each prime p this local factor is p/(p-1)
if p divides N and 1 - 1/(p-1)² otherwise; for even N the factor at 2 is 2,
and the product telescopes to sing(N/2). AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2
open scoped ComplexConjugate

/-- LEAF step 1: the q = 0 term vanishes because μ(0) = 0. -/
theorem leaf_vaughan_326_512_q0 (N : ℕ) :
    (ArithmeticFunction.moebius 0 : ℂ) ^ 2 / (Nat.totient 0 : ℂ) ^ 2 *
      ramanujan512 0 N = 0 := by
  sorry

/-- LEAF step 2: the Ramanujan sum c_p(-N) at a prime p equals p - 1 when p divides N,
and -1 otherwise. -/
theorem leaf_vaughan_326_512_prime_val (p N : ℕ) (hp : p.Prime) :
    ramanujan512 p N = if p ∣ N then ((p : ℂ) - 1) else -1 := by
  sorry

/-- LEAF step 3: for a prime p, the local Euler factor 1 + μ(p)²/φ(p)² c_p(-N)
equals p/(p-1) when p divides N, and 1 - 1/(p-1)² otherwise. -/
theorem leaf_vaughan_326_512_local_factor (p N : ℕ) (hp : p.Prime) :
    (1 : ℂ) + (ArithmeticFunction.moebius p : ℂ) ^ 2 / (Nat.totient p : ℂ) ^ 2 *
      ramanujan512 p N =
    if p ∣ N then (p : ℂ) / ((p : ℂ) - 1) else 1 - 1 / (((p : ℂ) - 1) ^ 2) := by
  sorry

/-- LEAF step 4: the infinite Euler product over all primes of the local factors
equals the singular series sing(N/2) when N is even. -/
theorem leaf_vaughan_326_512_euler_product (N : ℕ) (hE : Even N) :
    (∏' pp : {q : ℕ // q.Prime},
      (1 : ℂ) + (ArithmeticFunction.moebius (pp : ℕ) : ℂ) ^ 2 /
        (Nat.totient (pp : ℕ) : ℂ) ^ 2 * ramanujan512 (pp : ℕ) N) =
    (sing (N / 2) : ℂ) := by
  sorry

/-- LEAF step 5: the series Σ_q μ(q)²/φ(q)² c_q(-N) converges (HasSum) to the
Euler product over primes. -/
theorem leaf_vaughan_326_512_hasSum_euler (N : ℕ) :
    HasSum (fun q : ℕ => (ArithmeticFunction.moebius q : ℂ) ^ 2 /
      (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N)
      (∏' pp : {q : ℕ // q.Prime},
        (1 : ℂ) + (ArithmeticFunction.moebius (pp : ℕ) : ℂ) ^ 2 /
          (Nat.totient (pp : ℕ) : ℂ) ^ 2 * ramanujan512 (pp : ℕ) N) := by
  sorry

/-- Assembly: leaf_vaughan_326_512 from the five LEAF lemmas above.
The statement is copied character for character from Decomp512a.lean. -/
theorem leaf_vaughan_326_512_F2327 (N : ℕ) (hN : 2 ≤ N) (hE : Even N) :
    HasSum (fun q : ℕ => (ArithmeticFunction.moebius q : ℂ) ^ 2 /
      (Nat.totient q : ℂ) ^ 2 * ramanujan512 q N) (sing (N / 2) : ℂ) := by
  have h := leaf_vaughan_326_512_hasSum_euler N
  rw [leaf_vaughan_326_512_euler_product N hE] at h
  exact h

end LeanLab.BHP1997.Section2MS
