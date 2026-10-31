/-
U-1564, T3 MOONSHOT, route R-0056: binary Goldbach with the second prime taken from the
Friedlander-Iwaniec family q = a² + b⁴, the thinnest classical prime family for which a
parity-breaking Type II input is PROVED, Friedlander and Iwaniec, Annals 148, 1998.

The route asks for N = p + q with q a Friedlander-Iwaniec prime. The statement is stronger
than binary Goldbach. The hope is to borrow the Type II information of the family. The
smallest lemma the parity question needs is the finite rearrangement `twisted_typeII`:
a bilinear sum of the family twisted by f(N - ·) is a sum over k = N - mn in the classes
k ≡ N mod m. With f = 1_P it is a Type II sum for the shifted primes {N - p}, the sum that
R-0008 and R-0045 already found as hard as the target.

AI wrote this Lean code, Claude, for the Lean Lab. Binary Goldbach is OPEN; nothing here is
progress on it.
-/
import Mathlib
import LeanLab.Common.Goldbach

open Finset

namespace LeanLab.Routes.U1564

/-! ### Local structure of the family -/

/-- `a² + b⁴` is never `3 mod 5`. PROVED. -/
theorem fi_mod_five (a b : ℕ) : (a ^ 2 + b ^ 4) % 5 ≠ 3 := by
  have h : (a ^ 2 + b ^ 4) % 5 = ((a % 5) ^ 2 % 5 + (b % 5) ^ 4 % 5) % 5 := by
    simp [Nat.add_mod, Nat.pow_mod]
  rw [h]
  have ha : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hb : b % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 5) <;> interval_cases (b % 5) <;> decide

/-- An odd prime of the form `a² + b⁴` is `1 mod 4`. PROVED. -/
theorem fi_prime_mod_four {a b : ℕ} (hp : (a ^ 2 + b ^ 4).Prime) (h2 : a ^ 2 + b ^ 4 ≠ 2) :
    (a ^ 2 + b ^ 4) % 4 = 1 := by
  have hodd : (a ^ 2 + b ^ 4) % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have h4 : (a ^ 2 + b ^ 4) % 4 = ((a % 4) ^ 2 % 4 + (b % 4) ^ 4 % 4) % 4 := by
    simp [Nat.add_mod, Nat.pow_mod]
  have h42 : (a ^ 2 + b ^ 4) % 2 = ((a ^ 2 + b ^ 4) % 4) % 2 :=
    (Nat.mod_mod_of_dvd _ (by norm_num)).symm
  rw [h42, h4] at hodd
  rw [h4]
  have ha : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> simp_all

/-! ### The sealed target and its reduction -/

/-- `q` is a Friedlander-Iwaniec prime: a prime `a² + b⁴` with `a, b ≥ 1`. -/
def IsFIPrime (q : ℕ) : Prop := q.Prime ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ q = a ^ 2 + b ^ 4

/-- Sealed target, OPEN: every even `N > 2162` is `p + q` with `p` prime and `q` a
Friedlander-Iwaniec prime. Checked numerically for all even `N ≤ 3·10⁷` only. -/
def FIGoldbach : Prop :=
  ∀ N : ℕ, 2162 < N → Even N → ∃ p q : ℕ, p.Prime ∧ IsFIPrime q ∧ p + q = N

/-- The target implies binary Goldbach above 2162. PROVED as an implication. -/
theorem goldbach_of_fiGoldbach (h : FIGoldbach) (N : ℕ) (hN : 2162 < N) (he : Even N) :
    IsGoldbachSum N := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h N hN he
  exact ⟨p, q, hp, hq.1, hpq⟩

/-- Vacuity: `2164 = 2063 + 101` with `101 = 10² + 1⁴`. PROVED. -/
theorem fi_vacuity : ∃ p q : ℕ, p.Prime ∧ IsFIPrime q ∧ p + q = 2164 :=
  ⟨2063, 101, by norm_num, ⟨by norm_num, 10, 1, by norm_num, by norm_num, by norm_num⟩,
    by norm_num⟩

/-! ### The parity lemma: the twisted Type II sum is a sum over the classes `N mod m` -/

/-- For `m ≥ 1`, the sum over `n ∈ K`, `mn ≤ N`, of `β n · f (N - mn)` equals the sum over
`k ≤ N` with `m ∣ N - k` and `(N - k)/m ∈ K` of `β ((N - k)/m) · f k`. PROVED. -/
theorem twisted_typeII {R : Type*} [AddCommMonoid R] (N m : ℕ) (hm : 0 < m) (K : Finset ℕ)
    (g : ℕ → ℕ → R) :
    ∑ n ∈ K.filter (fun n => m * n ≤ N), g n (N - m * n) =
      ∑ k ∈ (range (N + 1)).filter (fun k => m ∣ N - k ∧ (N - k) / m ∈ K),
        g ((N - k) / m) k := by
  refine Finset.sum_nbij' (fun n => N - m * n) (fun k => (N - k) / m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [Nat.sub_sub_self hn.2, Nat.mul_div_cancel_left _ hm]
    exact ⟨by omega, dvd_mul_right m n, hn.1⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter]
    refine ⟨hk.2.2, ?_⟩
    rw [Nat.mul_div_cancel' hk.2.1]
    omega
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.sub_sub_self hn.2, Nat.mul_div_cancel_left _ hm]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [Nat.mul_div_cancel' hk.2.1]
    omega
  · intro n hn
    simp only [Finset.mem_filter] at hn
    rw [Nat.sub_sub_self hn.2, Nat.mul_div_cancel_left _ hm]

/-- The bilinear form: with `g n k = α m · β n · 1_P k` this is the Type II sum
`Σ_m α_m Σ_{p ≡ N mod m} β_{(N-p)/m}` for the shifted primes. PROVED. -/
theorem twisted_typeII_bilinear {R : Type*} [CommSemiring R] (N : ℕ) (M K : Finset ℕ)
    (hM : ∀ m ∈ M, 0 < m) (α β f : ℕ → R) :
    ∑ m ∈ M, ∑ n ∈ K.filter (fun n => m * n ≤ N), α m * β n * f (N - m * n) =
      ∑ m ∈ M, ∑ k ∈ (range (N + 1)).filter (fun k => m ∣ N - k ∧ (N - k) / m ∈ K),
        α m * β ((N - k) / m) * f k := by
  refine Finset.sum_congr rfl fun m hm => ?_
  exact twisted_typeII N m (hM m hm) K (fun n k => α m * β n * f k)

/-- Vacuity: `N = 10`, `m = 2`, `K = {1, 2, 3}`, `g n k = k`; both sides are `18`. PROVED. -/
theorem twisted_typeII_vacuity :
    ∑ n ∈ ({1, 2, 3} : Finset ℕ).filter (fun n => 2 * n ≤ 10), (10 - 2 * n) = 18 ∧
    ∑ k ∈ (range 11).filter (fun k => 2 ∣ 10 - k ∧ (10 - k) / 2 ∈ ({1, 2, 3} : Finset ℕ)),
      k = 18 := by
  decide

end LeanLab.Routes.U1564

#print axioms LeanLab.Routes.U1564.fi_mod_five
#print axioms LeanLab.Routes.U1564.fi_prime_mod_four
#print axioms LeanLab.Routes.U1564.goldbach_of_fiGoldbach
#print axioms LeanLab.Routes.U1564.fi_vacuity
#print axioms LeanLab.Routes.U1564.twisted_typeII
#print axioms LeanLab.Routes.U1564.twisted_typeII_bilinear
#print axioms LeanLab.Routes.U1564.twisted_typeII_vacuity
