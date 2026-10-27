/-
R-0025, T3 MOONSHOT: Goldbach on the 3-sphere. A prime is a sum of two squares exactly when it
is 2 or 1 mod 4, so binary Goldbach with both primes in {2} ∪ {1 mod 4} is the statement that the
3-sphere x² + y² + z² + w² = N carries an integer point whose two partial norms x² + y² and
z² + w² are both prime. The sphere has a multiplicative structure, the norm of the integer
quaternion x + yi + zj + wk, but that structure multiplies the TOTAL norm N; the partial norms,
the only place primality is asked, are not multiplicative. So the quaternion factorization gives
no Type II information on the parts, and the parity barrier stands. Barrier map, not progress.
Run 20261020T1003Z-31988, unit U-1203. AI-written Lean code, Claude. Checked only by the Lean
kernel. KNOWN mathematics: Fermat two squares, Euler four squares. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Routes.R0025

/-- A sum of two squares is never 3 mod 4. -/
theorem sq_add_sq_mod_four (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  have ha : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
    rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
  have hb : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
    rcases Nat.even_or_odd b with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
  omega

/-- **Fermat, both directions.** A prime is a sum of two squares iff it is not 3 mod 4. -/
theorem prime_sq_add_sq_iff {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · rintro ⟨a, b, rfl⟩; exact sq_add_sq_mod_four a b
  · intro h
    haveI := Fact.mk hp
    exact Nat.Prime.sq_add_sq h

/-- **Goldbach on the sphere.** An integer point on x² + y² + z² + w² = N with both partial
norms prime exists iff N = p + q with p, q prime and neither 3 mod 4. -/
theorem sphere_iff (N : ℕ) :
    (∃ x y z w : ℕ, (x ^ 2 + y ^ 2).Prime ∧ (z ^ 2 + w ^ 2).Prime ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = N) ↔
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 ≠ 3 ∧ q % 4 ≠ 3 ∧ p + q = N) := by
  constructor
  · rintro ⟨x, y, z, w, hp, hq, hN⟩
    exact ⟨_, _, hp, hq, sq_add_sq_mod_four x y, sq_add_sq_mod_four z w, by omega⟩
  · rintro ⟨p, q, hp, hq, hp4, hq4, hN⟩
    obtain ⟨x, y, hxy⟩ := (prime_sq_add_sq_iff hp).2 hp4
    obtain ⟨z, w, hzw⟩ := (prime_sq_add_sq_iff hq).2 hq4
    exact ⟨x, y, z, w, hxy ▸ hp, hzw ▸ hq, by omega⟩

/-- A prime not 3 mod 4 is 2 or 1 mod 4. -/
theorem prime_mod_four {p : ℕ} (hp : p.Prime) (h : p % 4 ≠ 3) : p = 2 ∨ p % 4 = 1 := by
  rcases hp.eq_two_or_odd with h2 | h2
  · exact Or.inl h2
  · right; omega

/-- **The local obstruction.** For N ≡ 0 mod 4 the sphere route only reaches N = 4. -/
theorem mod4_obstruction (N : ℕ) (h0 : N % 4 = 0) (h4 : N ≠ 4) :
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 ≠ 3 ∧ q % 4 ≠ 3 ∧ p + q = N := by
  rintro ⟨p, q, hp, hq, hp4, hq4, hN⟩
  rcases prime_mod_four hp hp4 with rfl | h1 <;> rcases prime_mod_four hq hq4 with rfl | h2 <;>
    omega

/-- Representation as a decidable bounded search. -/
def hasRep (N : ℕ) : Bool :=
  (List.range (N + 1)).any fun p =>
    Nat.Prime p && Nat.Prime (N - p) && p % 4 != 3 && (N - p) % 4 != 3

theorem hasRep_iff (N : ℕ) : hasRep N = true ↔
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 ≠ 3 ∧ q % 4 ≠ 3 ∧ p + q = N := by
  simp only [hasRep, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨p, hp, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩
    exact ⟨p, N - p, h1, h2, h3, h4, by omega⟩
  · rintro ⟨p, q, h1, h2, h3, h4, rfl⟩
    exact ⟨p, by omega, ⟨⟨⟨h1, by simpa using h2⟩, h3⟩, by simpa using h4⟩⟩

/-- **The small exceptions.** N = 6, 14, 38, 62 are 2 mod 4 and have no point on their sphere
with both partial norms prime; numerics to 10⁷ find no other, file numerics/r0025_sphere.out. -/
theorem exceptions :
    hasRep 6 = false ∧ hasRep 14 = false ∧ hasRep 38 = false ∧ hasRep 62 = false := by
  decide +kernel

theorem exception_62 :
    ¬ ∃ x y z w : ℕ, (x ^ 2 + y ^ 2).Prime ∧ (z ^ 2 + w ^ 2).Prime ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 62 := by
  rw [sphere_iff, ← hasRep_iff]; simp [exceptions.2.2.2]

/-- Vacuity: the hypotheses can hold, 10 = (1² + 2²) + (1² + 2²). -/
theorem vacuity : ∃ x y z w : ℕ, (x ^ 2 + y ^ 2).Prime ∧ (z ^ 2 + w ^ 2).Prime ∧
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 10 := ⟨1, 2, 1, 2, by norm_num, by norm_num, by norm_num⟩

/-! ### The quaternion structure acts on the total norm, not on the parts -/

/-- Partial norms of an integer quaternion a + bi + cj + dk. -/
def part1 (q : Quaternion ℤ) : ℤ := q.re ^ 2 + q.imI ^ 2
def part2 (q : Quaternion ℤ) : ℤ := q.imJ ^ 2 + q.imK ^ 2

theorem normSq_eq_parts (q : Quaternion ℤ) : Quaternion.normSq q = part1 q + part2 q := by
  rw [Quaternion.normSq_def']; simp [part1, part2]; ring

/-- **Euler's four squares.** The total norm is multiplicative. -/
theorem total_mul (q r : Quaternion ℤ) :
    part1 (q * r) + part2 (q * r) = (part1 q + part2 q) * (part1 r + part2 r) := by
  rw [← normSq_eq_parts, ← normSq_eq_parts, ← normSq_eq_parts, map_mul]

/-- **The parts are not.** q = 1 + 2i + j + k and r = 2 + i + j + k both have partial norms
5 and 2, both prime, total norm 7; their product has partial norms 29 and 20. -/
theorem parts_not_mul : ∃ q r : Quaternion ℤ, part1 q = 5 ∧ part2 q = 2 ∧ part1 r = 5 ∧ part2 r = 2 ∧
    part1 (q * r) = 29 ∧ part2 (q * r) = 20 := by
  refine ⟨⟨1, 2, 1, 1⟩, ⟨2, 1, 1, 1⟩, ?_⟩
  simp only [part1, part2, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul]
  norm_num

end LeanLab.Routes.R0025
