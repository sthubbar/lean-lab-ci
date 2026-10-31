/-
R-5300, CLOUD 20261020T2317Z-cloud53, unit U-6763, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The Hasse principle, or profinite, route.  Plain math twins:
* `LocalSol m`: every x, even when m is even, is a + b mod m with a and b
  prime to m, the local solubility of p + q = x at the modulus m.
* `localSol`: `LocalSol m` for every m ≠ 0, by the odd prime case, prime
  powers and the Chinese remainder theorem.
* `profinite_goldbach`: for every even N, every modulus m ≠ 0 and every bound B
  there are primes p, q > B with p + q ≡ N mod m.  With Dirichlet's theorem from
  Mathlib this says N lies in the closure of P + P in the profinite completion.
* `profinite_blind`: the set A_N of primes above N satisfies the same for N,
  yet N is not a sum of two members of A_N.  So no argument that only uses the
  profinite closure, that is congruence data, can prove binary Goldbach.
* `local_obstruction_two`: the parity condition is exact: for m even and x odd
  no a, b prime to m have a + b ≡ x mod m.
-/
import Mathlib

namespace LeanLab.Routes.R5300

/-- Local solubility of `a + b = x` in units modulo `m`, for every admissible `x`. -/
def LocalSol (m : ℕ) : Prop :=
  ∀ x : ℤ, ((2 : ℤ) ∣ (m : ℤ) → (2 : ℤ) ∣ x) →
    ∃ a : ℤ, IsCoprime a (m : ℤ) ∧ IsCoprime (x - a) (m : ℤ)

lemma isCoprime_prime_iff {p : ℕ} (hp : p.Prime) (a : ℤ) :
    IsCoprime a (p : ℤ) ↔ ¬ (p : ℤ) ∣ a := by
  rw [isCoprime_comm]
  exact (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd

lemma localSol_prime {p : ℕ} (hp : p.Prime) : LocalSol p := by
  intro x hx
  by_cases h1 : (p : ℤ) ∣ x - 1
  · refine ⟨2, ?_, ?_⟩
    · rw [isCoprime_prime_iff hp]
      intro h2
      have h2' : p ∣ 2 := by exact_mod_cast h2
      rcases Nat.prime_two.eq_one_or_self_of_dvd p h2' with h | h
      · exact hp.one_lt.ne' h
      · subst h
        have := hx (by norm_num)
        push_cast at h1
        omega
    · rw [isCoprime_prime_iff hp]
      intro h3
      have : (p : ℤ) ∣ 1 := by
        have := dvd_sub h1 h3
        simpa using this
      have : p ∣ 1 := by exact_mod_cast this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · refine ⟨1, ?_, ?_⟩
    · exact isCoprime_one_left
    · rwa [isCoprime_prime_iff hp]

lemma localSol_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : LocalSol (p ^ k) := by
  intro x hx
  have hx' : (2 : ℤ) ∣ (p : ℤ) → (2 : ℤ) ∣ x := fun h =>
    hx (by push_cast; exact dvd_pow h hk.ne')
  obtain ⟨a, ha, hb⟩ := localSol_prime hp x hx'
  refine ⟨a, ?_, ?_⟩
  · push_cast; exact (IsCoprime.pow_right_iff hk).mpr ha
  · push_cast; exact (IsCoprime.pow_right_iff hk).mpr hb

lemma localSol_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : LocalSol m) (hn : LocalSol n) :
    LocalSol (m * n) := by
  intro x hx
  have hxm : (2 : ℤ) ∣ (m : ℤ) → (2 : ℤ) ∣ x := fun h =>
    hx (by push_cast; exact dvd_mul_of_dvd_left h _)
  have hxn : (2 : ℤ) ∣ (n : ℤ) → (2 : ℤ) ∣ x := fun h =>
    hx (by push_cast; exact dvd_mul_of_dvd_right h _)
  obtain ⟨a1, h1a, h1b⟩ := hm x hxm
  obtain ⟨a2, h2a, h2b⟩ := hn x hxn
  obtain ⟨u, v, huv⟩ : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr hmn
  refine ⟨a1 * (v * n) + a2 * (u * m), ?_, ?_⟩
  · push_cast
    refine IsCoprime.mul_right ?_ ?_
    · have e : a1 * (v * n) + a2 * (u * m) = a1 + (m : ℤ) * (u * (a2 - a1)) := by
        linear_combination a1 * huv
      rw [e]; exact h1a.add_mul_left_left _
    · have e : a1 * (v * n) + a2 * (u * m) = a2 + (n : ℤ) * (v * (a1 - a2)) := by
        linear_combination a2 * huv
      rw [e]; exact h2a.add_mul_left_left _
  · push_cast
    refine IsCoprime.mul_right ?_ ?_
    · have e : x - (a1 * (v * n) + a2 * (u * m)) = (x - a1) + (m : ℤ) * (u * (a1 - a2)) := by
        linear_combination (-a1) * huv
      rw [e]; exact h1b.add_mul_left_left _
    · have e : x - (a1 * (v * n) + a2 * (u * m)) = (x - a2) + (n : ℤ) * (v * (a2 - a1)) := by
        linear_combination (-a2) * huv
      rw [e]; exact h2b.add_mul_left_left _

/-- Local Goldbach at every nonzero modulus. -/
theorem localSol (m : ℕ) (hm : m ≠ 0) : LocalSol m := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => exact localSol_pow hp hk
  | zero => exact absurd rfl hm
  | one => intro x _; exact ⟨0, by simpa using isCoprime_one_right, by simpa using isCoprime_one_right⟩
  | coprime a b ha hb hab iha ihb => exact localSol_mul hab (iha (by omega)) (ihb (by omega))

/-- Profinite Goldbach: every even `N` is `p + q` modulo every `m`, with `p, q` primes
beyond any bound `B`.  Uses Dirichlet's theorem from Mathlib. -/
theorem profinite_goldbach (m : ℕ) (hm : m ≠ 0) (N : ℕ) (hN : Even N) (B : ℕ) :
    ∃ p q : ℕ, B < p ∧ B < q ∧ p.Prime ∧ q.Prime ∧ ((p + q : ℕ) : ℤ) ≡ N [ZMOD m] := by
  have h2 : (2 : ℤ) ∣ (N : ℤ) := by
    obtain ⟨k, hk⟩ := hN; exact ⟨k, by push_cast [hk]; ring⟩
  obtain ⟨a, ha, hb⟩ := localSol m hm N (fun _ => h2)
  obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_zmodEq B hm ha
  obtain ⟨q, hqB, hq, hqb⟩ := Nat.forall_exists_prime_gt_and_zmodEq B hm hb
  refine ⟨p, q, hpB, hqB, hp, hq, ?_⟩
  have := hpa.add hqb
  push_cast
  simpa using this

/-- The profinite closure is blind: the primes above `N` satisfy every local condition
for `N`, but `N` is not a sum of two of them. -/
theorem profinite_blind (N : ℕ) (hN : Even N) :
    (∀ m : ℕ, m ≠ 0 → ∃ p q : ℕ, (p.Prime ∧ N < p) ∧ (q.Prime ∧ N < q) ∧
        ((p + q : ℕ) : ℤ) ≡ N [ZMOD m]) ∧
    ¬ ∃ p q : ℕ, (p.Prime ∧ N < p) ∧ (q.Prime ∧ N < q) ∧ p + q = N := by
  refine ⟨fun m hm => ?_, ?_⟩
  · obtain ⟨p, q, hp, hq, hpp, hqp, h⟩ := profinite_goldbach m hm N hN N
    exact ⟨p, q, ⟨hpp, hp⟩, ⟨hqp, hq⟩, h⟩
  · rintro ⟨p, q, ⟨_, hp⟩, ⟨_, hq⟩, h⟩
    omega

/-- The parity condition in `LocalSol` is exact. -/
theorem local_obstruction_two (m : ℕ) (hm : 2 ∣ m) (x : ℤ) (hx : ¬ (2 : ℤ) ∣ x)
    (a b : ℤ) (ha : IsCoprime a (m : ℤ)) (hb : IsCoprime b (m : ℤ)) :
    ¬ (a + b ≡ x [ZMOD m]) := by
  have hm' : (2 : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
  have ha2 : IsCoprime a 2 := ha.of_isCoprime_of_dvd_right hm'
  have hb2 : IsCoprime b 2 := hb.of_isCoprime_of_dvd_right hm'
  have ha2' : ¬ (2 : ℤ) ∣ a := by
    have := (isCoprime_prime_iff Nat.prime_two a).mp (by simpa using ha2)
    simpa using this
  have hb2' : ¬ (2 : ℤ) ∣ b := by
    have := (isCoprime_prime_iff Nat.prime_two b).mp (by simpa using hb2)
    simpa using this
  intro h
  have h2 : (2 : ℤ) ∣ x - (a + b) :=
    dvd_trans hm' (Int.ModEq.dvd h)
  omega

/-! Non-vacuity checks. -/

-- The hypotheses of `profinite_goldbach` hold: N = 100, m = 2310.
example : ∃ p q : ℕ, 100 < p ∧ 100 < q ∧ p.Prime ∧ q.Prime ∧
    ((p + q : ℕ) : ℤ) ≡ 100 [ZMOD 2310] :=
  profinite_goldbach 2310 (by norm_num) 100 (by decide) 100

-- An explicit witness, independent of the proof: 11 + 23 ≡ 4 mod 30 with 11, 23 > 4.
example : (Nat.Prime 11 ∧ 4 < 11) ∧ (Nat.Prime 23 ∧ 4 < 23) ∧
    ((11 + 23 : ℕ) : ℤ) ≡ 4 [ZMOD 30] := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  decide

-- `profinite_blind` at N = 4: both halves are instantiated.
example := profinite_blind 4 (by decide)

-- `local_obstruction_two` is not vacuous: 1 and 1 are prime to 2, and 1 + 1 ≢ 1 mod 2.
example : ¬ ((1 : ℤ) + 1 ≡ 1 [ZMOD (2 : ℕ)]) :=
  local_obstruction_two 2 (by norm_num) 1 (by decide) 1 1 (by simp) (by simp)

#print axioms localSol
#print axioms profinite_goldbach
#print axioms profinite_blind
#print axioms local_obstruction_two

end LeanLab.Routes.R5300
