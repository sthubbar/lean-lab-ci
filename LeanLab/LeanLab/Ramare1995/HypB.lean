/-
Ramaré 1995, P0008, Section 9, hypothesis (b): the even numbers from 2n₀ + 6 to 2n₀ + 84,
2n₀ = 1.002 · 10^30, are sums of two primes. Page 704 says "a direct computation shows that the
assumption (b) holds"; this file redoes that computation with kernel-checked certificates.
For each even g, a prime p < 3000 with g - p prime; primality of g - p by Lucas' test,
Mathlib's `lucas_primality`, with factorizations of q - 1 found by Python (sympy) and checked by
the kernel, recursively; primes below 10^4 by the lab's `primeB`. No native_decide.
The binary modular power `pm` and its correctness proof are copied from
Verifications/Pratt.lean, with fuel 128 in place of 64, to avoid importing that heavier module.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0803Z-2223. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ramare1995.Section9

namespace LeanLab.Ramare1995.HypB
open LeanLab LeanLab.Ramare1995.Section9

/-- Binary modular power with fuel. -/
def pm : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m else
      let h := pm fuel a (e / 2) m
      if e % 2 = 1 then h * h % m * a % m else h * h % m

theorem pm_cast : ∀ fuel a e m, e < 2 ^ fuel → ((pm fuel a e m : ℕ) : ZMod m) = (a : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero => intro a e m he; simp at he; subst he; simp [pm]
  | succ k ih =>
    intro a e m he
    simp only [pm]
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0]
      have hlt : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
      have IH := ih a (e / 2) m hlt
      have he2 : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1, pow_add, pow_mul, pow_one]
        ring
      · rw [if_neg h1]
        have h1' : e % 2 = 0 := by omega
        simp only [Nat.cast_mul, ZMod.natCast_mod, IH]
        conv_rhs => rw [he2, h1', add_zero, pow_mul]
        ring

/-- Lucas' test with a listed factorization of `p - 1`, for `p < 2^128`. -/
theorem pratt (p a : ℕ) (L : List (ℕ × ℕ)) (hp : p < 2 ^ 128)
    (hprod : (L.map fun x => x.1 ^ x.2).prod = p - 1) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : pm 128 a (p - 1) p = 1 % p)
    (hnot : ∀ x ∈ L, pm 128 a ((p - 1) / x.1) p % p ≠ 1 % p) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · rw [← pm_cast 128 a (p - 1) p (by omega), hpow]
    simp
  · intro q hq hqd heq
    rw [← hprod] at hqd
    obtain ⟨y, hy, hyd⟩ := (Nat.prime_iff.mp hq).dvd_prod_iff.mp hqd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hqx : q = x.1 :=
      (Nat.prime_dvd_prime_iff_eq hq (hprimes x hx)).mp (hq.dvd_of_dvd_pow hyd)
    subst hqx
    apply hnot x hx
    have h2 : (p - 1) / x.1 < 2 ^ 128 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [← pm_cast 128 a _ p h2] at heq
    have := (ZMod.natCast_eq_natCast_iff' _ 1 p).mp (by rw [heq]; simp)
    simpa using this

theorem pB {n : ℕ} (h : primeB n = true) : n.Prime := primeB_sound h

theorem c11411 : Nat.Prime 11411 := by
  refine pratt 11411 7 [(2, 1), (5, 1), (7, 1), (163, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c14783 : Nat.Prime 14783 := by
  refine pratt 14783 5 [(2, 1), (19, 1), (389, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c16477 : Nat.Prime 16477 := by
  refine pratt 16477 2 [(2, 2), (3, 1), (1373, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c18059 : Nat.Prime 18059 := by
  refine pratt 18059 2 [(2, 1), (9029, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c19813 : Nat.Prime 19813 := by
  refine pratt 19813 2 [(2, 2), (3, 1), (13, 1), (127, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c20641 : Nat.Prime 20641 := by
  refine pratt 20641 7 [(2, 5), (3, 1), (5, 1), (43, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c33619 : Nat.Prime 33619 := by
  refine pratt 33619 2 [(2, 1), (3, 1), (13, 1), (431, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c36373 : Nat.Prime 36373 := by
  refine pratt 36373 2 [(2, 2), (3, 1), (7, 1), (433, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c53381 : Nat.Prime 53381 := by
  refine pratt 53381 2 [(2, 2), (5, 1), (17, 1), (157, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c59243 : Nat.Prime 59243 := by
  refine pratt 59243 2 [(2, 1), (19, 1), (1559, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c93283 : Nat.Prime 93283 := by
  refine pratt 93283 2 [(2, 1), (3, 1), (7, 1), (2221, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c118361 : Nat.Prime 118361 := by
  refine pratt 118361 6 [(2, 3), (5, 1), (11, 1), (269, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c143519 : Nat.Prime 143519 := by
  refine pratt 143519 17 [(2, 1), (73, 1), (983, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c151523 : Nat.Prime 151523 := by
  refine pratt 151523 2 [(2, 1), (7, 1), (79, 1), (137, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c397543 : Nat.Prime 397543 := by
  refine pratt 397543 3 [(2, 1), (3, 1), (59, 1), (1123, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c553699 : Nat.Prime 553699 := by
  refine pratt 553699 2 [(2, 1), (3, 2), (19, 1), (1619, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c1992803 : Nat.Prime 1992803 := by
  refine pratt 1992803 2 [(2, 1), (7, 1), (137, 1), (1039, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c2086339 : Nat.Prime 2086339 := by
  refine pratt 2086339 2 [(2, 1), (3, 1), (89, 1), (3907, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c3501601 : Nat.Prime 3501601 := by
  refine pratt 3501601 19 [(2, 5), (3, 1), (5, 2), (1459, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c4770517 : Nat.Prime 4770517 := by
  refine pratt 4770517 2 [(2, 2), (3, 1), (397543, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c397543

theorem c6380629 : Nat.Prime 6380629 := by
  refine pratt 6380629 2 [(2, 2), (3, 1), (71, 1), (7489, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c6644389 : Nat.Prime 6644389 := by
  refine pratt 6644389 6 [(2, 2), (3, 1), (553699, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c553699

theorem c8898179 : Nat.Prime 8898179 := by
  refine pratt 8898179 2 [(2, 1), (31, 1), (143519, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c143519

theorem c15623653 : Nat.Prime 15623653 := by
  refine pratt 15623653 2 [(2, 2), (3, 1), (11, 1), (118361, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c118361

theorem c28347197 : Nat.Prime 28347197 := by
  refine pratt 28347197 2 [(2, 2), (1979, 1), (3581, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c33913493 : Nat.Prime 33913493 := by
  refine pratt 33913493 2 [(2, 2), (743, 1), (11411, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c11411

theorem c42604141 : Nat.Prime 42604141 := by
  refine pratt 42604141 2 [(2, 2), (3, 1), (5, 1), (239, 1), (2971, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c63864907 : Nat.Prime 63864907 := by
  refine pratt 63864907 2 [(2, 1), (3, 1), (7, 1), (349, 1), (4357, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c70721873 : Nat.Prime 70721873 := by
  refine pratt 70721873 3 [(2, 4), (13, 1), (23, 1), (14783, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c14783

theorem c98484251 : Nat.Prime 98484251 := by
  refine pratt 98484251 6 [(2, 1), (5, 3), (211, 1), (1867, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c430325321 : Nat.Prime 430325321 := by
  refine pratt 430325321 3 [(2, 3), (5, 1), (71, 1), (151523, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c151523

theorem c1149568327 : Nat.Prime 1149568327 := by
  refine pratt 1149568327 5 [(2, 1), (3, 2), (63864907, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c63864907

theorem c2139400409 : Nat.Prime 2139400409 := by
  refine pratt 2139400409 3 [(2, 3), (149, 1), (233, 1), (7703, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem c4136338543 : Nat.Prime 4136338543 := by
  refine pratt 4136338543 3 [(2, 1), (3, 1), (7, 1), (98484251, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c98484251

theorem c7030104857 : Nat.Prime 7030104857 := by
  refine pratt 7030104857 3 [(2, 3), (31, 1), (28347197, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c28347197

theorem c29951605727 : Nat.Prime 29951605727 := by
  refine pratt 29951605727 5 [(2, 1), (7, 1), (2139400409, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c2139400409

theorem c60071838811 : Nat.Prime 60071838811 := by
  refine pratt 60071838811 3 [(2, 1), (3, 1), (5, 1), (47, 1), (42604141, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c42604141

theorem c62827496867 : Nat.Prime 62827496867 := by
  refine pratt 62827496867 2 [(2, 1), (73, 1), (430325321, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c430325321

theorem c215353900681 : Nat.Prime 215353900681 := by
  refine pratt 215353900681 11 [(2, 3), (3, 1), (5, 1), (33619, 1), (53381, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c33619
  · exact c53381

theorem c347452437613 : Nat.Prime 347452437613 := by
  refine pratt 347452437613 2 [(2, 2), (3, 1), (7, 1), (4136338543, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c4136338543

theorem c933537212653 : Nat.Prime 933537212653 := by
  refine pratt 933537212653 2 [(2, 2), (3, 1), (11, 1), (19, 1), (61, 1), (103, 1), (59243, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c59243

theorem c967742486783 : Nat.Prime 967742486783 := by
  refine pratt 967742486783 5 [(2, 1), (2557, 1), (9551, 1), (19813, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c19813

theorem c8689209603253 : Nat.Prime 8689209603253 := by
  refine pratt 8689209603253 2 [(2, 2), (3, 1), (103, 1), (7030104857, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c7030104857

theorem c11894224084579 : Nat.Prime 11894224084579 := by
  refine pratt 11894224084579 3 [(2, 1), (3, 2), (11, 1), (60071838811, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c60071838811

theorem c6463455365299081 : Nat.Prime 6463455365299081 := by
  refine pratt 6463455365299081 13 [(2, 3), (3, 1), (5, 1), (547, 1), (20641, 1), (4770517, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c20641
  · exact c4770517

theorem c111558964748779703 : Nat.Prime 111558964748779703 := by
  refine pratt 111558964748779703 5 [(2, 1), (7, 1), (11, 1), (23, 2), (149, 1), (271, 1), (33913493, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c33913493

theorem c13390799421436895681 : Nat.Prime 13390799421436895681 := by
  refine pratt 13390799421436895681 6 [(2, 6), (5, 1), (17, 1), (179, 1), (223, 1), (3947, 1), (15623653, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c15623653

theorem c21642439161263262383 : Nat.Prime 21642439161263262383 := by
  refine pratt 21642439161263262383 5 [(2, 1), (97, 1), (111558964748779703, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c111558964748779703

theorem c37698058573685827337 : Nat.Prime 37698058573685827337 := by
  refine pratt 37698058573685827337 3 [(2, 3), (751, 1), (18059, 1), (347452437613, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c18059
  · exact c347452437613

theorem c98238023015827578881 : Nat.Prime 98238023015827578881 := by
  refine pratt 98238023015827578881 3 [(2, 13), (5, 1), (2086339, 1), (1149568327, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c2086339
  · exact c1149568327

theorem c139337444909332565579 : Nat.Prime 139337444909332565579 := by
  refine pratt 139337444909332565579 2 [(2, 1), (23, 1), (67, 1), (1451, 1), (3501601, 1), (8898179, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c3501601
  · exact c8898179

theorem c519418539870318297193 : Nat.Prime 519418539870318297193 := by
  refine pratt 519418539870318297193 5 [(2, 3), (3, 1), (21642439161263262383, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c21642439161263262383

theorem c24244715414223866410747 : Nat.Prime 24244715414223866410747 := by
  refine pratt 24244715414223866410747 2 [(2, 1), (3, 1), (29, 1), (139337444909332565579, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c139337444909332565579

theorem c2997917614112353096053041 : Nat.Prime 2997917614112353096053041 := by
  refine pratt 2997917614112353096053041 7 [(2, 4), (5, 1), (1049, 1), (5527, 1), (6463455365299081, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c6463455365299081

theorem c7146423222309393053277227 : Nat.Prime 7146423222309393053277227 := by
  refine pratt 7146423222309393053277227 2 [(2, 1), (36373, 1), (98238023015827578881, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact c36373
  · exact c98238023015827578881

theorem c8442444770234062989737627 : Nat.Prime 8442444770234062989737627 := by
  refine pratt 8442444770234062989737627 2 [(2, 1), (1992803, 1), (70721873, 1), (29951605727, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact c1992803
  · exact c70721873
  · exact c29951605727

theorem c10210528461083824158803269 : Nat.Prime 10210528461083824158803269 := by
  refine pratt 10210528461083824158803269 6 [(2, 2), (3, 1), (593, 1), (16477, 1), (93283, 1), (933537212653, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c16477
  · exact c93283
  · exact c933537212653

theorem c131911532385466034755134281 : Nat.Prime 131911532385466034755134281 := by
  refine pratt 131911532385466034755134281 3 [(2, 3), (5, 1), (7, 1), (907, 1), (519418539870318297193, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c519418539870318297193

theorem c1473529411764705882352941173 : Nat.Prime 1473529411764705882352941173 := by
  refine pratt 1473529411764705882352941173 2 [(2, 2), (6380629, 1), (6644389, 1), (8689209603253, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact c6380629
  · exact c6644389
  · exact c8689209603253

theorem c7952380952380952380952380951 : Nat.Prime 7952380952380952380952380951 := by
  refine pratt 7952380952380952380952380951 3 [(2, 1), (3, 1), (5, 2), (277, 1), (5077, 1), (37698058573685827337, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c37698058573685827337

theorem c1001999999999999999999999997217 : Nat.Prime 1001999999999999999999999997217 := by
  refine pratt 1001999999999999999999999997217 10 [(2, 5), (3, 4), (41, 1), (151, 1), (4663, 1), (13390799421436895681, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c13390799421436895681

theorem c1001999999999999999999999997641 : Nat.Prime 1001999999999999999999999997641 := by
  refine pratt 1001999999999999999999999997641 3 [(2, 3), (5, 1), (17, 1), (1473529411764705882352941173, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c1473529411764705882352941173

theorem c1001999999999999999999999997671 : Nat.Prime 1001999999999999999999999997671 := by
  refine pratt 1001999999999999999999999997671 7 [(2, 1), (5, 1), (7, 1), (2003, 1), (7146423222309393053277227, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c7146423222309393053277227

theorem c1001999999999999999999999998123 : Nat.Prime 1001999999999999999999999998123 := by
  refine pratt 1001999999999999999999999998123 2 [(2, 1), (3, 1), (131, 1), (151, 1), (8442444770234062989737627, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c8442444770234062989737627

theorem c1001999999999999999999999998477 : Nat.Prime 1001999999999999999999999998477 := by
  refine pratt 1001999999999999999999999998477 5 [(2, 2), (3, 2), (211, 1), (131911532385466034755134281, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c131911532385466034755134281

theorem c1001999999999999999999999998997 : Nat.Prime 1001999999999999999999999998997 := by
  refine pratt 1001999999999999999999999998997 2 [(2, 2), (977, 1), (4217, 1), (62827496867, 1), (967742486783, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c62827496867
  · exact c967742486783

theorem c1001999999999999999999999999419 : Nat.Prime 1001999999999999999999999999419 := by
  refine pratt 1001999999999999999999999999419 3 [(2, 1), (3, 1), (11, 1), (5927, 1), (215353900681, 1), (11894224084579, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c215353900681
  · exact c11894224084579

theorem c1001999999999999999999999999513 : Nat.Prime 1001999999999999999999999999513 := by
  refine pratt 1001999999999999999999999999513 3 [(2, 3), (41, 1), (1019, 1), (2997917614112353096053041, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c2997917614112353096053041

theorem c1001999999999999999999999999719 : Nat.Prime 1001999999999999999999999999719 := by
  refine pratt 1001999999999999999999999999719 11 [(2, 1), (3, 2), (101, 1), (127, 1), (179, 1), (24244715414223866410747, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c24244715414223866410747

theorem c1001999999999999999999999999827 : Nat.Prime 1001999999999999999999999999827 := by
  refine pratt 1001999999999999999999999999827 3 [(2, 1), (3, 2), (7, 1), (7952380952380952380952380951, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c7952380952380952380952380951

theorem c1002000000000000000000000000047 : Nat.Prime 1002000000000000000000000000047 := by
  refine pratt 1002000000000000000000000000047 5 [(2, 1), (139, 1), (353, 1), (10210528461083824158803269, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact c10210528461083824158803269

/-- **Hypothesis (b), second half, PROVED**: `{n₀, …, n₀ + 39} ⊆ 𝒜`. -/
theorem hypBHigh : HypBHigh := by
  intro i hi
  interval_cases i
  · exact ⟨2789, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨2791, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨2339, 1001999999999999999999999997671, pB (by decide +kernel), c1001999999999999999999999997671, by unfold n₀; norm_num⟩
  · exact ⟨293, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨2797, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨503, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩
  · exact ⟨2801, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨2803, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨509, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩
  · exact ⟨1901, 1001999999999999999999999998123, pB (by decide +kernel), c1001999999999999999999999998123, by unfold n₀; norm_num⟩
  · exact ⟨307, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨2357, 1001999999999999999999999997671, pB (by decide +kernel), c1001999999999999999999999997671, by unfold n₀; norm_num⟩
  · exact ⟨311, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨313, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨521, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩
  · exact ⟨2819, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨211, 1001999999999999999999999999827, pB (by decide +kernel), c1001999999999999999999999999827, by unfold n₀; norm_num⟩
  · exact ⟨2399, 1001999999999999999999999997641, pB (by decide +kernel), c1001999999999999999999999997641, by unfold n₀; norm_num⟩
  · exact ⟨2371, 1001999999999999999999999997671, pB (by decide +kernel), c1001999999999999999999999997671, by unfold n₀; norm_num⟩
  · exact ⟨1567, 1001999999999999999999999998477, pB (by decide +kernel), c1001999999999999999999999998477, by unfold n₀; norm_num⟩
  · exact ⟨1049, 1001999999999999999999999998997, pB (by decide +kernel), c1001999999999999999999999998997, by unfold n₀; norm_num⟩
  · exact ⟨2377, 1001999999999999999999999997671, pB (by decide +kernel), c1001999999999999999999999997671, by unfold n₀; norm_num⟩
  · exact ⟨2833, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨2381, 1001999999999999999999999997671, pB (by decide +kernel), c1001999999999999999999999997671, by unfold n₀; norm_num⟩
  · exact ⟨2837, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨337, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨11, 1002000000000000000000000000047, pB (by decide +kernel), c1002000000000000000000000000047, by unfold n₀; norm_num⟩
  · exact ⟨2843, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨643, 1001999999999999999999999999419, pB (by decide +kernel), c1001999999999999999999999999419, by unfold n₀; norm_num⟩
  · exact ⟨2393, 1001999999999999999999999997671, pB (by decide +kernel), c1001999999999999999999999997671, by unfold n₀; norm_num⟩
  · exact ⟨347, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨2851, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨557, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩
  · exact ⟨353, 1001999999999999999999999999719, pB (by decide +kernel), c1001999999999999999999999999719, by unfold n₀; norm_num⟩
  · exact ⟨2857, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨563, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩
  · exact ⟨2861, 1001999999999999999999999997217, pB (by decide +kernel), c1001999999999999999999999997217, by unfold n₀; norm_num⟩
  · exact ⟨661, 1001999999999999999999999999419, pB (by decide +kernel), c1001999999999999999999999999419, by unfold n₀; norm_num⟩
  · exact ⟨569, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩
  · exact ⟨571, 1001999999999999999999999999513, pB (by decide +kernel), c1001999999999999999999999999513, by unfold n₀; norm_num⟩

/-- **Section 9, large range, with hypothesis (b) proved**: Theorem 2, Theorem 9.1 and even
Goldbach up to `2 · 10^10` imply that every even `N ≥ 6 n₀ + 18` is a sum of at most 6 primes. -/
theorem large_even_of' (h2 : Theorem2) (h91 : Theorem91) (hG : EvenGoldbachUpTo (2 * 10 ^ 10)) :
    ∀ N : ℕ, Even N → 6 * n₀ + 18 ≤ N → LeanLab.SchnirelmannConstant.AtMostPrimes 6 N :=
  large_even_of h2 h91 hG hypBHigh

end LeanLab.Ramare1995.HypB
