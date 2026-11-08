/-
Split of component3 into four block-wise sub-domains of the fixed candidate
batch of the 10 ^ 90 row.

The statement asks, for every candidate q among the first 64 entries of the
fixed candidate list, and for every prime divisor p of q, for a residue i
below 9 with p ^ 560 congruent to q ^ (560 * i) modulo the sealed modulus
15321986788854443284662612735663611380010431225771200.

The proof route has two phases. Phase one is the finite primality
certification: each of the 64 candidates of this batch is a prime number.
Phase two is algebraic and costs nothing: if q is prime and p is a prime
divisor of q, then p equals q, so the witness i = 1 is immediate and no
residue computation is required. The four smaller primary components 2, 5
and 7 share this shape and are handled elsewhere.

This file therefore leaves the congruence arithmetic alone and splits the
batch by the size of the offset 10 ^ 90 - q into four consecutive blocks,

  block one    the offset is at least 60000
  block two    57000 <= offset < 60000
  block three  55000 <= offset < 57000
  block four   the offset is below 55000

and asks for the congruence for the candidates of one block at a time. The
four blocks partition the batch, all four are inhabited, and each block is a
proper sub-domain of the batch, so each leaf is strictly easier than the
whole statement and no leaf has a hypothesis that can never hold.

component3_split has no sorry of its own. The four block leaves are the only
open obligations this file adds.
-/
import LeanLab.DtRS1998.Decomp445a

namespace LeanLab.DtRS1998.Decomp445a

open Decomp372a

set_option maxRecDepth 100000

/-- Cast a modular power at modulus `p` down to a divisor `q ∣ p`. -/
private theorem pm_cast_dvd_q (fuel a e p q : ℕ) (hq : q ∣ p) (he : e < 2 ^ fuel) :
    ((LeanLab.Verifications.Pratt.pm fuel a e p : ℕ) : ZMod q) = (a : ZMod q) ^ e := by
  have h := congrArg (ZMod.castHom hq (ZMod q))
    (LeanLab.Verifications.Pratt.pm_cast fuel a e p he)
  simp only [map_pow, map_natCast] at h
  exact h

/-- If `o ∣ n` and `o ∤ n / r` for every prime `r ∣ F`, where `F ∣ n`, then `F ∣ o`. -/
private theorem dvd_of_order_helper (o n F : ℕ) (hn : n ≠ 0) (hon : o ∣ n) (hF : F ∣ n)
    (hr : ∀ r, r.Prime → r ∣ F → ¬ o ∣ n / r) : F ∣ o := by
  have ho : o ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hon)
  have hF0 : F ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hF)
  rw [← Nat.factorization_prime_le_iff_dvd hF0 ho]
  intro r hrp
  by_contra hlt
  push Not at hlt
  have hrF : r ∣ F := by
    by_contra h
    rw [Nat.factorization_eq_zero_of_not_dvd h] at hlt
    omega
  apply hr r hrp hrF
  have hrn : r ∣ n := dvd_trans hrF hF
  have hnr : n / r ≠ 0 := by
    have hpos := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hrn) hrp.pos
    omega
  rw [← Nat.factorization_prime_le_iff_dvd ho hnr]
  intro s hs
  rw [Nat.factorization_div hrn]
  have h1 := (Nat.factorization_prime_le_iff_dvd ho hn).mpr hon s hs
  have h2 := (Nat.factorization_prime_le_iff_dvd hF0 hn).mpr hF r hrp
  rw [hrp.factorization]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  by_cases hsr : s = r
  · subst hsr; simp; omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hsr)]; omega

/-- Pocklington: `p` is prime when `F ∣ p - 1`, `p < (F + 1) ^ 2`, `F` is a product of
certified primes `r`, `a ^ (p - 1) = 1 mod p` and `gcd (a ^ ((p - 1) / r) - 1) p = 1`
for each `r`. Only part of `p - 1` needs factoring. -/
private theorem pock_helper (p a Fu : ℕ) (L : List (ℕ × ℕ)) (hp2 : 2 ≤ p) (hp : p < 2 ^ Fu)
    (hFd : (p - 1) % (L.map fun x => x.1 ^ x.2).prod = 0)
    (hbig : p < ((L.map fun x => x.1 ^ x.2).prod + 1) ^ 2)
    (hprimes : ∀ x ∈ L, x.1.Prime)
    (hpow : LeanLab.Verifications.Pratt.pm Fu a (p - 1) p = 1 % p)
    (hg : ∀ x ∈ L,
      Nat.gcd ((LeanLab.Verifications.Pratt.pm Fu a ((p - 1) / x.1) p + p - 1) % p) p = 1) :
    p.Prime := by
  set F := (L.map fun x => x.1 ^ x.2).prod with hFval
  have hn : p - 1 ≠ 0 := by omega
  have hFn : F ∣ p - 1 := Nat.dvd_of_mod_eq_zero hFd
  have key : ∀ q, q.Prime → q ∣ p → F ∣ q - 1 := by
    intro q hq hqp
    haveI := Fact.mk hq
    set x : ZMod q := (a : ZMod q) with hx
    have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    have hx1 : x ^ (p - 1) = 1 := by
      rw [hx, ← pm_cast_dvd_q Fu a (p - 1) p q hqp (by omega),
        hpow, h1p]
      simp
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at hx1; exact zero_ne_one hx1
    have ho1 : orderOf x ∣ p - 1 := orderOf_dvd_of_pow_eq_one hx1
    have ho2 : orderOf x ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hx0
    refine dvd_trans (dvd_of_order_helper (orderOf x) (p - 1) F hn ho1 hFn ?_) ho2
    intro r hr hrF hod
    obtain ⟨y, hy, hyd⟩ := (Nat.prime_iff.mp hr).dvd_prod_iff.mp hrF
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    have hre : r = e.1 :=
      (Nat.prime_dvd_prime_iff_eq hr (hprimes e he)).mp (hr.dvd_of_dvd_pow hyd)
    subst hre
    have hxr : x ^ ((p - 1) / e.1) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hod
    have hlt : (p - 1) / e.1 < 2 ^ Fu := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hc := pm_cast_dvd_q Fu a ((p - 1) / e.1) p q hqp hlt
    rw [← hx, hxr] at hc
    set t := LeanLab.Verifications.Pratt.pm Fu a ((p - 1) / e.1) p
    have hz : (((t + p - 1) % p : ℕ) : ZMod q) = 0 := by
      have hm : (t + p - 1) % p % q = (t + p - 1) % q := Nat.mod_mod_of_dvd _ hqp
      rw [(ZMod.natCast_eq_natCast_iff' _ _ q).mpr hm]
      have hp0 : ((p : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff p q).mpr hqp
      have hsplit : t + p - 1 = t + (p - 1) := by omega
      rw [hsplit, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ p), hp0, hc]
      simp
    have hqd : q ∣ (t + p - 1) % p := (ZMod.natCast_eq_zero_iff _ q).mp hz
    have hg1 := hg e he
    have hone : q ∣ 1 := by
      rw [← hg1]; exact Nat.dvd_gcd hqd hqp
    exact hq.one_lt.ne' (Nat.dvd_one.mp hone)
  by_contra hnp
  have hmf : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hFq := key _ hmf (Nat.minFac_dvd p)
  have hle : F + 1 ≤ p.minFac := by
    have h2 := hmf.two_le
    have h3 := Nat.le_of_dvd (by omega) hFq
    omega
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < p) hnp
  have hmono : (F + 1) ^ 2 ≤ p.minFac ^ 2 := Nat.pow_le_pow_left hle 2
  omega



/-- Pocklington certificate: 10 digits. -/
private theorem cert_0 : (1379826499 : ℕ).Prime :=
  pock_helper 1379826499 3 31 [(1201, 1), (457, 1), (419, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_1 : (4462783807057408057 : ℕ).Prime :=
  pock_helper 4462783807057408057 19 62 [(1379826499, 1), (601, 1), (311, 1), (103, 1), (7, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_0
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_2 : (925106424198984623 : ℕ).Prime :=
  pock_helper 925106424198984623 5 60 [(6256091, 1), (50593, 1), (313, 1), (29, 1), (23, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_3 : (18989807 : ℕ).Prime :=
  pock_helper 18989807 5 25 [(569, 1), (41, 1), (37, 1), (11, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_4 : (6440317084823 : ℕ).Prime :=
  pock_helper 6440317084823 5 43 [(18989807, 1), (1123, 1), (151, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_3
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 58 digits. -/
private theorem cert_5 : (1062885674841072459489414818970827139736118824610593743247 : ℕ).Prime :=
  pock_helper 1062885674841072459489414818970827139736118824610593743247 3 190 [(4462783807057408057, 1), (925106424198984623, 1), (6440317084823, 1), (317257, 1), (7, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_1
      · exact cert_2
      · exact cert_4
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_6 : (28705493 : ℕ).Prime :=
  pock_helper 28705493 2 25 [(6907, 1), (1039, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_7 : (633184884311351663 : ℕ).Prime :=
  pock_helper 633184884311351663 5 60 [(28705493, 1), (9199, 1), (4457, 1), (269, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_6
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_8 : (29060653450353795925049 : ℕ).Prime :=
  pock_helper 29060653450353795925049 3 75 [(633184884311351663, 1), (5737, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_7
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_9 : (449651011 : ℕ).Prime :=
  pock_helper 449651011 3 29 [(405091, 1), (37, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_10 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577 5 299 [(1062885674841072459489414818970827139736118824610593743247, 1), (29060653450353795925049, 1), (449651011, 1), (3, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_5
      · exact cert_8
      · exact cert_9
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_11 : (14738407 : ℕ).Prime :=
  pock_helper 14738407 3 24 [(2456401, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_12 : (12291831439 : ℕ).Prime :=
  pock_helper 12291831439 29 34 [(14738407, 1), (139, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_11
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_13 : (9440126545153 : ℕ).Prime :=
  pock_helper 9440126545153 7 44 [(12291831439, 1), (3, 1), (2, 8)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_12
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_14 : (147344524868721931584433 : ℕ).Prime :=
  pock_helper 147344524868721931584433 7 77 [(9440126545153, 1), (347, 1), (43, 1), (37, 1), (31, 1), (19, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_13
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_15 : (946874521071922737507641579447 : ℕ).Prime :=
  pock_helper 946874521071922737507641579447 5 100 [(147344524868721931584433, 1), (3213131, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_14
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_16 : (64531875143 : ℕ).Prime :=
  pock_helper 64531875143 5 36 [(6994567, 1), (659, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 43 digits. -/
private theorem cert_17 : (1099864590658222331156146009438844141746579 : ℕ).Prime :=
  pock_helper 1099864590658222331156146009438844141746579 2 140 [(946874521071922737507641579447, 1), (64531875143, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_15
      · exact cert_16
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_18 : (259960231 : ℕ).Prime :=
  pock_helper 259960231 17 28 [(54499, 1), (53, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_19 : (43934838800387 : ℕ).Prime :=
  pock_helper 43934838800387 2 46 [(259960231, 1), (84503, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_18
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_20 : (37776756054769556533 : ℕ).Prime :=
  pock_helper 37776756054769556533 19 66 [(43934838800387, 1), (907, 1), (79, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_19
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_21 : (60581077 : ℕ).Prime :=
  pock_helper 60581077 2 26 [(5048423, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_22 : (58344908285777 : ℕ).Prime :=
  pock_helper 58344908285777 3 46 [(60581077, 1), (8599, 1), (7, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_21
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_23 : (293824958127172973 : ℕ).Prime :=
  pock_helper 293824958127172973 2 59 [(58344908285777, 1), (1259, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_22
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_24 : (125247679 : ℕ).Prime :=
  pock_helper 125247679 3 27 [(353807, 1), (59, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_25 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327 5 299 [(1099864590658222331156146009438844141746579, 1), (37776756054769556533, 1), (293824958127172973, 1), (125247679, 1), (109, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_17
      · exact cert_20
      · exact cert_23
      · exact cert_24
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_26 : (13762226441 : ℕ).Prime :=
  pock_helper 13762226441 3 34 [(76781, 1), (4481, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_27 : (72730695219214984781741 : ℕ).Prime :=
  pock_helper 72730695219214984781741 2 76 [(13762226441, 1), (34157, 1), (10301, 1), (751, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_26
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_28 : (70578419 : ℕ).Prime :=
  pock_helper 70578419 2 27 [(7727, 1), (4567, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_29 : (53325101004937 : ℕ).Prime :=
  pock_helper 53325101004937 5 46 [(70578419, 1), (31481, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_28
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 42 digits. -/
private theorem cert_30 : (678195340223078331832355971258444747462523 : ℕ).Prime :=
  pock_helper 678195340223078331832355971258444747462523 2 139 [(72730695219214984781741, 1), (53325101004937, 1), (87433, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_27
      · exact cert_29
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_31 : (212160521 : ℕ).Prime :=
  pock_helper 212160521 3 28 [(1279, 1), (29, 1), (13, 1), (11, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_32 : (1452875247809 : ℕ).Prime :=
  pock_helper 1452875247809 3 41 [(212160521, 1), (107, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_31
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_33 : (11724703249818631 : ℕ).Prime :=
  pock_helper 11724703249818631 13 54 [(1452875247809, 1), (269, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_32
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_34 : (92681997034922305623089 : ℕ).Prime :=
  pock_helper 92681997034922305623089 3 77 [(11724703249818631, 1), (433, 1), (163, 1), (7, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_33
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_35 : (24226529 : ℕ).Prime :=
  pock_helper 24226529 3 25 [(1907, 1), (397, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_36 : (60178698037 : ℕ).Prime :=
  pock_helper 60178698037 2 36 [(24226529, 1), (23, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_35
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_37 : (4923460001199119 : ℕ).Prime :=
  pock_helper 4923460001199119 7 53 [(60178698037, 1), (2153, 1), (19, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_36
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_38 : (503935824962734626127 : ℕ).Prime :=
  pock_helper 503935824962734626127 3 69 [(4923460001199119, 1), (2437, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_37
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_39 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331 2 299 [(678195340223078331832355971258444747462523, 1), (92681997034922305623089, 1), (503935824962734626127, 1), (41, 1), (11, 1), (7, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_30
      · exact cert_34
      · exact cert_38
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_40 : (37558613 : ℕ).Prime :=
  pock_helper 37558613 2 26 [(103183, 1), (13, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_41 : (75117227 : ℕ).Prime :=
  pock_helper 75117227 2 27 [(37558613, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_40
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_42 : (14291269 : ℕ).Prime :=
  pock_helper 14291269 2 24 [(3299, 1), (19, 2), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_43 : (79440516821738663 : ℕ).Prime :=
  pock_helper 79440516821738663 5 57 [(75117227, 1), (14291269, 1), (37, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_41
      · exact cert_42
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_44 : (51900396212045590265813 : ℕ).Prime :=
  pock_helper 51900396212045590265813 2 76 [(79440516821738663, 1), (23333, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_43
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 27 digits. -/
private theorem cert_45 : (153832774372503129547869733 : ℕ).Prime :=
  pock_helper 153832774372503129547869733 5 87 [(51900396212045590265813, 1), (19, 1), (13, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_44
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_46 : (199105289309 : ℕ).Prime :=
  pock_helper 199105289309 2 38 [(45077, 1), (199, 1), (179, 1), (31, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_47 : (25417220552692245857 : ℕ).Prime :=
  pock_helper 25417220552692245857 3 65 [(199105289309, 1), (3989287, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_46
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_48 : (21724613 : ℕ).Prime :=
  pock_helper 21724613 2 25 [(4591, 1), (13, 2), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_49 : (43449227 : ℕ).Prime :=
  pock_helper 43449227 2 26 [(21724613, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_48
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_50 : (347593817 : ℕ).Prime :=
  pock_helper 347593817 3 29 [(43449227, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_49
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 63 digits. -/
private theorem cert_51 : (488584990641815147167821406930488475169798294444325086198732677 : ℕ).Prime :=
  pock_helper 488584990641815147167821406930488475169798294444325086198732677 2 209 [(153832774372503129547869733, 1), (25417220552692245857, 1), (347593817, 1), (439, 1), (43, 1), (23, 2), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_45
      · exact cert_47
      · exact cert_50
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_52 : (37895703403 : ℕ).Prime :=
  pock_helper 37895703403 2 36 [(375257, 1), (16831, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_53 : (35243004164791 : ℕ).Prime :=
  pock_helper 35243004164791 31 46 [(37895703403, 1), (31, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_52
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_54 : (1518054623 : ℕ).Prime :=
  pock_helper 1518054623 5 31 [(853799, 1), (127, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_55 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417 7 299 [(488584990641815147167821406930488475169798294444325086198732677, 1), (35243004164791, 1), (1518054623, 1), (797, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_51
      · exact cert_53
      · exact cert_54
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_56 : (58735241 : ℕ).Prime :=
  pock_helper 58735241 3 26 [(4783, 1), (307, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_57 : (34863181 : ℕ).Prime :=
  pock_helper 34863181 2 26 [(523, 1), (101, 1), (11, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_58 : (16994801 : ℕ).Prime :=
  pock_helper 16994801 3 25 [(42487, 1), (5, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_59 : (334260459649000270477156654889 : ℕ).Prime :=
  pock_helper 334260459649000270477156654889 3 99 [(58735241, 1), (34863181, 1), (16994801, 1), (92357, 1), (13, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_56
      · exact cert_57
      · exact cert_58
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_60 : (30372020233 : ℕ).Prime :=
  pock_helper 30372020233 5 35 [(96581, 1), (13103, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_61 : (451388964702847 : ℕ).Prime :=
  pock_helper 451388964702847 3 49 [(30372020233, 1), (2477, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_60
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_62 : (107558835773597899975051 : ℕ).Prime :=
  pock_helper 107558835773597899975051 3 77 [(451388964702847, 1), (1373, 1), (89, 1), (13, 1), (5, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_61
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 58 digits. -/
private theorem cert_63 : (1873565324598816063866500205904094545270190991085389153969 : ℕ).Prime :=
  pock_helper 1873565324598816063866500205904094545270190991085389153969 3 191 [(334260459649000270477156654889, 1), (107558835773597899975051, 1), (3257, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_59
      · exact cert_62
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_64 : (499843579 : ℕ).Prime :=
  pock_helper 499843579 2 29 [(2857, 1), (2243, 1), (13, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_65 : (56609284696067 : ℕ).Prime :=
  pock_helper 56609284696067 2 46 [(499843579, 1), (3331, 1), (17, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_64
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_66 : (167563482700358321 : ℕ).Prime :=
  pock_helper 167563482700358321 3 58 [(56609284696067, 1), (37, 1), (5, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_65
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_67 : (49374739 : ℕ).Prime :=
  pock_helper 49374739 3 26 [(130621, 1), (7, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 83 digits. -/
private theorem cert_68 : (93004568384399041680927367152274519724408862963348759691076025654380143152631657267 : ℕ).Prime :=
  pock_helper 93004568384399041680927367152274519724408862963348759691076025654380143152631657267 3 276 [(1873565324598816063866500205904094545270190991085389153969, 1), (167563482700358321, 1), (49374739, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_63
      · exact cert_66
      · exact cert_67
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_69 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721 3 299 [(93004568384399041680927367152274519724408862963348759691076025654380143152631657267, 1), (67, 1), (59, 1), (17, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_68
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_70 : (28808371 : ℕ).Prime :=
  pock_helper 28808371 2 25 [(991, 1), (19, 1), (17, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_71 : (818100119659 : ℕ).Prime :=
  pock_helper 818100119659 2 40 [(28808371, 1), (4733, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_70
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_72 : (42541206222269 : ℕ).Prime :=
  pock_helper 42541206222269 2 46 [(818100119659, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_71
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_73 : (9784477431121871 : ℕ).Prime :=
  pock_helper 9784477431121871 11 54 [(42541206222269, 1), (23, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_72
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_74 : (166965747451764499398851 : ℕ).Prime :=
  pock_helper 166965747451764499398851 2 78 [(9784477431121871, 1), (341287, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_73
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_75 : (301491416153 : ℕ).Prime :=
  pock_helper 301491416153 3 39 [(4716109, 1), (131, 1), (61, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_76 : (51062736476452083197 : ℕ).Prime :=
  pock_helper 51062736476452083197 2 66 [(301491416153, 1), (81899, 1), (47, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_75
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 56 digits. -/
private theorem cert_77 : (12278220695869799283902702923485903093158153845103172551 : ℕ).Prime :=
  pock_helper 12278220695869799283902702923485903093158153845103172551 19 184 [(166965747451764499398851, 1), (51062736476452083197, 1), (123449, 1), (33331, 1), (7, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_74
      · exact cert_76
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_78 : (54254393867 : ℕ).Prime :=
  pock_helper 54254393867 2 36 [(199657, 1), (7151, 1), (19, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_79 : (30010776026931432629789 : ℕ).Prime :=
  pock_helper 30010776026931432629789 2 75 [(54254393867, 1), (47659, 1), (10253, 1), (283, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_78
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_80 : (47848291 : ℕ).Prime :=
  pock_helper 47848291 2 26 [(227849, 1), (7, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_81 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183 3 299 [(12278220695869799283902702923485903093158153845103172551, 1), (30010776026931432629789, 1), (47848291, 1), (137, 1), (23, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_77
      · exact cert_79
      · exact cert_80
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_82 : (6298302738844988441 : ℕ).Prime :=
  pock_helper 6298302738844988441 3 63 [(2880739, 1), (3517, 1), (1607, 1), (509, 1), (19, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_83 : (134399917 : ℕ).Prime :=
  pock_helper 134399917 2 28 [(2213, 1), (241, 1), (7, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 33 digits. -/
private theorem cert_84 : (230651967228289828054211208494561 : ℕ).Prime :=
  pock_helper 230651967228289828054211208494561 3 108 [(6298302738844988441, 1), (134399917, 1), (131, 1), (13, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_82
      · exact cert_83
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_85 : (1158991654867 : ℕ).Prime :=
  pock_helper 1158991654867 2 41 [(138163, 1), (82241, 1), (17, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_86 : (769570458831689 : ℕ).Prime :=
  pock_helper 769570458831689 3 50 [(1158991654867, 1), (83, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_85
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_87 : (13648559 : ℕ).Prime :=
  pock_helper 13648559 7 24 [(1151, 1), (11, 2), (7, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_88 : (483162279352983405762947 : ℕ).Prime :=
  pock_helper 483162279352983405762947 2 79 [(769570458831689, 1), (13648559, 1), (23, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_86
      · exact cert_87
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_89 : (2322190373 : ℕ).Prime :=
  pock_helper 2322190373 2 32 [(979001, 1), (593, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_90 : (1964573055559 : ℕ).Prime :=
  pock_helper 1964573055559 3 41 [(2322190373, 1), (47, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_89
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_91 : (673215965532847003 : ℕ).Prime :=
  pock_helper 673215965532847003 2 60 [(1964573055559, 1), (199, 1), (41, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_90
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_92 : (2692863862131388013 : ℕ).Prime :=
  pock_helper 2692863862131388013 2 62 [(673215965532847003, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_91
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_93 : (118486009933781072573 : ℕ).Prime :=
  pock_helper 118486009933781072573 2 67 [(2692863862131388013, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_92
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_94 : (11226959 : ℕ).Prime :=
  pock_helper 11226959 7 24 [(55579, 1), (101, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_95 : (22453919 : ℕ).Prime :=
  pock_helper 22453919 11 25 [(11226959, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_94
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_96 : (24429863873 : ℕ).Prime :=
  pock_helper 24429863873 3 35 [(22453919, 1), (17, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_95
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_97 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301 2 299 [(230651967228289828054211208494561, 1), (483162279352983405762947, 1), (118486009933781072573, 1), (24429863873, 1), (31, 1), (5, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_84
      · exact cert_88
      · exact cert_93
      · exact cert_96
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_98 : (248381291 : ℕ).Prime :=
  pock_helper 248381291 2 28 [(143573, 1), (173, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_99 : (496762583 : ℕ).Prime :=
  pock_helper 496762583 5 29 [(248381291, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_98
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_100 : (12578714787664099229 : ℕ).Prime :=
  pock_helper 12578714787664099229 2 64 [(496762583, 1), (13331, 1), (881, 1), (11, 1), (7, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_99
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_101 : (52350417608590745085532820483581 : ℕ).Prime :=
  pock_helper 52350417608590745085532820483581 2 106 [(12578714787664099229, 1), (439771, 1), (3847, 1), (41, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_100
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_102 : (17318281 : ℕ).Prime :=
  pock_helper 17318281 11 25 [(389, 1), (53, 1), (7, 1), (5, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_103 : (39589590367 : ℕ).Prime :=
  pock_helper 39589590367 5 36 [(17318281, 1), (127, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_102
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_104 : (950150168809 : ℕ).Prime :=
  pock_helper 950150168809 11 40 [(39589590367, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_103
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_105 : (5220125027436647 : ℕ).Prime :=
  pock_helper 5220125027436647 5 53 [(950150168809, 1), (67, 1), (41, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_104
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 62 digits. -/
private theorem cert_106 : (23745962129962148394257714789277705957807205236868975737393319 : ℕ).Prime :=
  pock_helper 23745962129962148394257714789277705957807205236868975737393319 3 204 [(52350417608590745085532820483581, 1), (5220125027436647, 1), (231559, 1), (16963, 1), (1229, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_101
      · exact cert_105
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_107 : (20949707179589 : ℕ).Prime :=
  pock_helper 20949707179589 2 45 [(90017, 1), (49433, 1), (107, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_108 : (11689936606210663 : ℕ).Prime :=
  pock_helper 11689936606210663 11 54 [(20949707179589, 1), (31, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_107
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_109 : (280558478549055913 : ℕ).Prime :=
  pock_helper 280558478549055913 7 58 [(11689936606210663, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_108
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_110 : (40400420911064051473 : ℕ).Prime :=
  pock_helper 40400420911064051473 5 66 [(280558478549055913, 1), (3, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_109
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_111 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403 2 299 [(23745962129962148394257714789277705957807205236868975737393319, 1), (40400420911064051473, 1), (80567, 1), (6469, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_106
      · exact cert_110
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_112 : (212391143 : ℕ).Prime :=
  pock_helper 212391143 5 28 [(1740911, 1), (61, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_113 : (335578005941 : ℕ).Prime :=
  pock_helper 335578005941 2 39 [(212391143, 1), (79, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_112
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_114 : (28801627 : ℕ).Prime :=
  pock_helper 28801627 3 25 [(685753, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_115 : (460826033 : ℕ).Prime :=
  pock_helper 460826033 3 29 [(28801627, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_114
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_116 : (24884605783 : ℕ).Prime :=
  pock_helper 24884605783 3 35 [(460826033, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_115
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_117 : (78338063445872011517474274387791 : ℕ).Prime :=
  pock_helper 78338063445872011517474274387791 17 106 [(335578005941, 1), (24884605783, 1), (6491, 1), (3361, 1), (43, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_113
      · exact cert_116
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_118 : (18678731 : ℕ).Prime :=
  pock_helper 18678731 2 25 [(266839, 1), (7, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_119 : (22630926334829 : ℕ).Prime :=
  pock_helper 22630926334829 3 45 [(18678731, 1), (43271, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_118
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_120 : (265826870599 : ℕ).Prime :=
  pock_helper 265826870599 19 38 [(37339, 1), (2243, 1), (23, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_121 : (1063307482397 : ℕ).Prime :=
  pock_helper 1063307482397 2 40 [(265826870599, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_120
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_122 : (96254533221595962582020453 : ℕ).Prime :=
  pock_helper 96254533221595962582020453 2 87 [(22630926334829, 1), (1063307482397, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_119
      · exact cert_121
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_123 : (102414823347778104187269761993 : ℕ).Prime :=
  pock_helper 102414823347778104187269761993 3 97 [(96254533221595962582020453, 1), (19, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_122
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 68 digits. -/
private theorem cert_124 : (21611626709292047953692709004258975803177567316341638237479157522509 : ℕ).Prime :=
  pock_helper 21611626709292047953692709004258975803177567316341638237479157522509 2 224 [(78338063445872011517474274387791, 1), (102414823347778104187269761993, 1), (673429, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_117
      · exact cert_123
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_125 : (60463226503 : ℕ).Prime :=
  pock_helper 60463226503 3 36 [(301993, 1), (227, 1), (7, 2), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_126 : (64288855770297817 : ℕ).Prime :=
  pock_helper 64288855770297817 5 56 [(60463226503, 1), (6329, 1), (7, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_125
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_127 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927 3 299 [(21611626709292047953692709004258975803177567316341638237479157522509, 1), (64288855770297817, 1), (863, 1), (139, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_124
      · exact cert_126
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_128 : (7080939533 : ℕ).Prime :=
  pock_helper 7080939533 2 33 [(1427, 1), (599, 1), (109, 1), (19, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_129 : (22474902077743 : ℕ).Prime :=
  pock_helper 22474902077743 3 45 [(7080939533, 1), (23, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_128
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_130 : (9978856522517893 : ℕ).Prime :=
  pock_helper 9978856522517893 7 54 [(22474902077743, 1), (37, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_129
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 29 digits. -/
private theorem cert_131 : (66283874023533288977181798301 : ℕ).Prime :=
  pock_helper 66283874023533288977181798301 7 96 [(9978856522517893, 1), (2212153, 1), (10009, 1), (5, 2), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_130
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_132 : (1596505387 : ℕ).Prime :=
  pock_helper 1596505387 3 31 [(108917, 1), (349, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_133 : (51902017 : ℕ).Prime :=
  pock_helper 51902017 5 26 [(270323, 1), (3, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_134 : (828618497366655791 : ℕ).Prime :=
  pock_helper 828618497366655791 11 60 [(1596505387, 1), (51902017, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_132
      · exact cert_133
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_135 : (2026106462258046807233143 : ℕ).Prime :=
  pock_helper 2026106462258046807233143 3 81 [(828618497366655791, 1), (407527, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_134
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_136 : (25155511 : ℕ).Prime :=
  pock_helper 25155511 3 25 [(838517, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_137 : (58722424903363122961 : ℕ).Prime :=
  pock_helper 58722424903363122961 7 66 [(25155511, 1), (29567, 1), (523, 1), (37, 1), (17, 1), (5, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_136
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_138 : (21658163 : ℕ).Prime :=
  pock_helper 21658163 2 25 [(3331, 1), (3251, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_139 : (5717755033 : ℕ).Prime :=
  pock_helper 5717755033 5 33 [(21658163, 1), (11, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_138
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_140 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967 5 299 [(66283874023533288977181798301, 1), (2026106462258046807233143, 1), (58722424903363122961, 1), (5717755033, 1), (652261, 1), (17, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_131
      · exact cert_135
      · exact cert_137
      · exact cert_139
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_141 : (302314004851 : ℕ).Prime :=
  pock_helper 302314004851 11 39 [(1281263, 1), (13, 1), (11, 2), (5, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_142 : (885598448701788237149 : ℕ).Prime :=
  pock_helper 885598448701788237149 2 70 [(302314004851, 1), (12157, 1), (563, 1), (107, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_141
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 33 digits. -/
private theorem cert_143 : (267566513611201937534627046321373 : ℕ).Prime :=
  pock_helper 267566513611201937534627046321373 2 108 [(885598448701788237149, 1), (1109, 1), (863, 1), (79, 1), (37, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_142
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_144 : (416115499 : ℕ).Prime :=
  pock_helper 416115499 3 29 [(96457, 1), (719, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_145 : (188916436547 : ℕ).Prime :=
  pock_helper 188916436547 2 38 [(416115499, 1), (227, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_144
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_146 : (165561626209896455053 : ℕ).Prime :=
  pock_helper 165561626209896455053 2 68 [(188916436547, 1), (1373, 1), (1237, 1), (43, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_145
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_147 : (72940141 : ℕ).Prime :=
  pock_helper 72940141 31 27 [(73, 1), (61, 1), (13, 1), (7, 1), (5, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_148 : (127383622947208730741 : ℕ).Prime :=
  pock_helper 127383622947208730741 13 67 [(72940141, 1), (132421, 1), (397, 1), (151, 1), (11, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_147
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_149 : (1279808347 : ℕ).Prime :=
  pock_helper 1279808347 3 31 [(6199, 1), (1811, 1), (19, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_150 : (5119233389 : ℕ).Prime :=
  pock_helper 5119233389 2 33 [(1279808347, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_149
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_151 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089 23 299 [(267566513611201937534627046321373, 1), (165561626209896455053, 1), (127383622947208730741, 1), (5119233389, 1), (1442377, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_143
      · exact cert_146
      · exact cert_148
      · exact cert_150
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_152 : (6456531973 : ℕ).Prime :=
  pock_helper 6456531973 2 33 [(63277, 1), (773, 1), (11, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_153 : (18358313616119304019 : ℕ).Prime :=
  pock_helper 18358313616119304019 2 64 [(6456531973, 1), (15461, 1), (601, 1), (17, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_152
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_154 : (9436173198685322265767 : ℕ).Prime :=
  pock_helper 9436173198685322265767 5 73 [(18358313616119304019, 1), (257, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_153
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_155 : (18325387 : ℕ).Prime :=
  pock_helper 18325387 2 25 [(337, 1), (53, 1), (19, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_156 : (7262704077927329713075679326819 : ℕ).Prime :=
  pock_helper 7262704077927329713075679326819 3 103 [(9436173198685322265767, 1), (18325387, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_154
      · exact cert_155
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_157 : (99766057 : ℕ).Prime :=
  pock_helper 99766057 19 27 [(319763, 1), (13, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_158 : (598596343 : ℕ).Prime :=
  pock_helper 598596343 5 30 [(99766057, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_157
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_159 : (31738775298547 : ℕ).Prime :=
  pock_helper 31738775298547 2 45 [(598596343, 1), (8837, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_158
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_160 : (2420281450523 : ℕ).Prime :=
  pock_helper 2420281450523 2 42 [(1569803, 1), (3121, 1), (19, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 27 digits. -/
private theorem cert_161 : (153633538234781791068580163 : ℕ).Prime :=
  pock_helper 153633538234781791068580163 2 87 [(31738775298547, 1), (2420281450523, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_159
      · exact cert_160
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 29 digits. -/
private theorem cert_162 : (69135092205651805980861073351 : ℕ).Prime :=
  pock_helper 69135092205651805980861073351 3 96 [(153633538234781791068580163, 1), (5, 2), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_161
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 66 digits. -/
private theorem cert_163 : (537603718971126540592567204047301612088726211624567805565089155487 : ℕ).Prime :=
  pock_helper 537603718971126540592567204047301612088726211624567805565089155487 3 219 [(7262704077927329713075679326819, 1), (69135092205651805980861073351, 1), (3499, 1), (17, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_156
      · exact cert_162
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_164 : (6329005313 : ℕ).Prime :=
  pock_helper 6329005313 3 33 [(153557, 1), (23, 1), (7, 1), (2, 8)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 76 digits. -/
private theorem cert_165 : (6804993587313637538011336005449854012446026441548504005500400464791812204863 : ℕ).Prime :=
  pock_helper 6804993587313637538011336005449854012446026441548504005500400464791812204863 5 252 [(537603718971126540592567204047301612088726211624567805565089155487, 1), (6329005313, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_163
      · exact cert_164
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_166 : (11052637 : ℕ).Prime :=
  pock_helper 11052637 2 24 [(18797, 1), (7, 2), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_167 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513 3 299 [(6804993587313637538011336005449854012446026441548504005500400464791812204863, 1), (11052637, 1), (207743, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_165
      · exact cert_166
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_168 : (108708092417 : ℕ).Prime :=
  pock_helper 108708092417 3 37 [(13997, 1), (197, 1), (11, 1), (7, 1), (2, 9)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_169 : (48266393033149 : ℕ).Prime :=
  pock_helper 48266393033149 2 46 [(108708092417, 1), (37, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_168
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_170 : (2509852437723749 : ℕ).Prime :=
  pock_helper 2509852437723749 2 52 [(48266393033149, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_169
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_171 : (5019704875447499 : ℕ).Prime :=
  pock_helper 5019704875447499 2 53 [(2509852437723749, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_170
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_172 : (22438080793250320531 : ℕ).Prime :=
  pock_helper 22438080793250320531 11 65 [(5019704875447499, 1), (149, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_171
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_173 : (2917682857 : ℕ).Prime :=
  pock_helper 2917682857 7 32 [(409327, 1), (11, 1), (3, 4), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 33 digits. -/
private theorem cert_174 : (734411090819951174645617944217607 : ℕ).Prime :=
  pock_helper 734411090819951174645617944217607 5 110 [(22438080793250320531, 1), (2917682857, 1), (79, 1), (71, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_172
      · exact cert_173
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_175 : (257027429 : ℕ).Prime :=
  pock_helper 257027429 2 28 [(110597, 1), (83, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_176 : (4088792340533 : ℕ).Prime :=
  pock_helper 4088792340533 2 42 [(257027429, 1), (97, 1), (41, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_175
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_177 : (2141710841057818288204801 : ℕ).Prime :=
  pock_helper 2141710841057818288204801 23 81 [(4088792340533, 1), (1483, 1), (73, 1), (7, 1), (5, 2), (3, 3), (2, 10)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_176
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_178 : (1895821019395970170536007797191 : ℕ).Prime :=
  pock_helper 1895821019395970170536007797191 13 101 [(2141710841057818288204801, 1), (127, 1), (41, 1), (17, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_177
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_179 : (108150937 : ℕ).Prime :=
  pock_helper 108150937 5 27 [(4506289, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_180 : (15138241 : ℕ).Prime :=
  pock_helper 15138241 11 24 [(1213, 1), (13, 1), (5, 1), (3, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_181 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611 3 299 [(734411090819951174645617944217607, 1), (1895821019395970170536007797191, 1), (108150937, 1), (15138241, 1), (391691, 1), (1009, 1), (37, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_174
      · exact cert_178
      · exact cert_179
      · exact cert_180
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_182 : (7832642975302929485459 : ℕ).Prime :=
  pock_helper 7832642975302929485459 2 73 [(427181, 1), (11239, 1), (7933, 1), (593, 1), (547, 1), (317, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_183 : (6197759341 : ℕ).Prime :=
  pock_helper 6197759341 2 33 [(883, 1), (131, 1), (47, 1), (19, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_184 : (1405019647086019 : ℕ).Prime :=
  pock_helper 1405019647086019 2 51 [(6197759341, 1), (37783, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_183
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_185 : (2956634677 : ℕ).Prime :=
  pock_helper 2956634677 2 32 [(1373, 1), (157, 1), (127, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 55 digits. -/
private theorem cert_186 : (7794040558759131236694046107932833803593974496156372173 : ℕ).Prime :=
  pock_helper 7794040558759131236694046107932833803593974496156372173 2 183 [(7832642975302929485459, 1), (1405019647086019, 1), (2956634677, 1), (289297, 1), (23, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_182
      · exact cert_184
      · exact cert_185
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 60 digits. -/
private theorem cert_187 : (240446151237719198652011322429727922840874113206424081537051 : ℕ).Prime :=
  pock_helper 240446151237719198652011322429727922840874113206424081537051 7 198 [(7794040558759131236694046107932833803593974496156372173, 1), (617, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_186
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_188 : (211426697 : ℕ).Prime :=
  pock_helper 211426697 3 28 [(65579, 1), (31, 1), (13, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_189 : (112733560547189 : ℕ).Prime :=
  pock_helper 112733560547189 2 47 [(211426697, 1), (139, 1), (137, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_188
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_190 : (1571782070172867986209191007 : ℕ).Prime :=
  pock_helper 1571782070172867986209191007 3 91 [(112733560547189, 1), (963943, 1), (1787, 1), (71, 1), (19, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_189
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_191 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623 3 299 [(240446151237719198652011322429727922840874113206424081537051, 1), (1571782070172867986209191007, 1), (7, 2), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_187
      · exact cert_190
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_192 : (72734635214027 : ℕ).Prime :=
  pock_helper 72734635214027 2 47 [(47981, 1), (45259, 1), (16747, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_193 : (57669660497 : ℕ).Prime :=
  pock_helper 57669660497 3 36 [(3930593, 1), (131, 1), (7, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 36 digits. -/
private theorem cert_194 : (412114970424412329181892219789694751 : ℕ).Prime :=
  pock_helper 412114970424412329181892219789694751 13 119 [(72734635214027, 1), (57669660497, 1), (2147527, 1), (61, 1), (5, 3), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_192
      · exact cert_193
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_195 : (760880252327401 : ℕ).Prime :=
  pock_helper 760880252327401 7 50 [(2929331, 1), (467, 1), (103, 1), (5, 2), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_196 : (18372083701294024233029 : ℕ).Prime :=
  pock_helper 18372083701294024233029 2 74 [(760880252327401, 1), (17599, 1), (7, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_195
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_197 : (890952973 : ℕ).Prime :=
  pock_helper 890952973 2 30 [(815891, 1), (13, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_198 : (315397352443 : ℕ).Prime :=
  pock_helper 315397352443 2 39 [(890952973, 1), (59, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_197
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_199 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687 5 299 [(412114970424412329181892219789694751, 1), (18372083701294024233029, 1), (315397352443, 1), (3928049, 1), (2532637, 1), (17351, 1), (1213, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_194
      · exact cert_196
      · exact cert_198
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_200 : (35420031197 : ℕ).Prime :=
  pock_helper 35420031197 2 36 [(713021, 1), (1129, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_201 : (1669983630876157 : ℕ).Prime :=
  pock_helper 1669983630876157 2 51 [(35420031197, 1), (3929, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_200
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_202 : (4549543085530438019729 : ℕ).Prime :=
  pock_helper 4549543085530438019729 3 72 [(1669983630876157, 1), (673, 1), (23, 1), (11, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_201
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_203 : (67738679 : ℕ).Prime :=
  pock_helper 67738679 7 27 [(4639, 1), (149, 1), (7, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_204 : (330022844089 : ℕ).Prime :=
  pock_helper 330022844089 19 39 [(67738679, 1), (29, 1), (7, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_203
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 34 digits. -/
private theorem cert_205 : (3002906296784399476897803346063763 : ℕ).Prime :=
  pock_helper 3002906296784399476897803346063763 2 112 [(4549543085530438019729, 1), (330022844089, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_202
      · exact cert_204
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_206 : (9766125793 : ℕ).Prime :=
  pock_helper 9766125793 5 34 [(14387, 1), (2357, 1), (3, 2), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_207 : (39064503173 : ℕ).Prime :=
  pock_helper 39064503173 2 36 [(9766125793, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_206
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_208 : (4765869387107 : ℕ).Prime :=
  pock_helper 4765869387107 2 43 [(39064503173, 1), (61, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_207
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_209 : (359033310256530805319 : ℕ).Prime :=
  pock_helper 359033310256530805319 7 69 [(4765869387107, 1), (673, 1), (577, 1), (97, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_208
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_210 : (718066620513061610639 : ℕ).Prime :=
  pock_helper 718066620513061610639 7 70 [(359033310256530805319, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_209
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_211 : (39872850421944789941639158909903 : ℕ).Prime :=
  pock_helper 39872850421944789941639158909903 5 105 [(718066620513061610639, 1), (9127, 1), (3583, 1), (283, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_210
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_212 : (57833987 : ℕ).Prime :=
  pock_helper 57833987 2 26 [(217421, 1), (19, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_213 : (186419181996451 : ℕ).Prime :=
  pock_helper 186419181996451 3 48 [(57833987, 1), (29, 1), (19, 1), (13, 1), (5, 2), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_212
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 82 digits. -/
private theorem cert_214 : (9419375561335912358362027106137052856354993658405403330597004732765250793229164459 : ℕ).Prime :=
  pock_helper 9419375561335912358362027106137052856354993658405403330597004732765250793229164459 2 273 [(3002906296784399476897803346063763, 1), (39872850421944789941639158909903, 1), (186419181996451, 1), (211, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_205
      · exact cert_211
      · exact cert_213
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_215 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851 2 299 [(9419375561335912358362027106137052856354993658405403330597004732765250793229164459, 1), (79, 1), (31, 1), (17, 2), (5, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_214
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_216 : (8326536867006979 : ℕ).Prime :=
  pock_helper 8326536867006979 2 53 [(6900877, 1), (6487049, 1), (31, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_217 : (23430874743757638907 : ℕ).Prime :=
  pock_helper 23430874743757638907 3 65 [(8326536867006979, 1), (67, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_216
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_218 : (153910062411705601645112038051 : ℕ).Prime :=
  pock_helper 153910062411705601645112038051 2 97 [(23430874743757638907, 1), (877, 1), (167, 1), (23, 1), (13, 1), (5, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_217
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_219 : (51944569 : ℕ).Prime :=
  pock_helper 51944569 11 26 [(5741, 1), (29, 1), (13, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 40 digits. -/
private theorem cert_220 : (3533698000678703430294737811785691398399 : ℕ).Prime :=
  pock_helper 3533698000678703430294737811785691398399 29 132 [(153910062411705601645112038051, 1), (51944569, 1), (17, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_218
      · exact cert_219
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 59 digits. -/
private theorem cert_221 : (15201432905196083562906601602721786837858186072775135552603 : ℕ).Prime :=
  pock_helper 15201432905196083562906601602721786837858186072775135552603 2 194 [(3533698000678703430294737811785691398399, 1), (304063, 1), (7207, 1), (229, 1), (67, 1), (37, 1), (19, 1), (13, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_220
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 67 digits. -/
private theorem cert_222 : (7201436315176075089609839897367476691048104462476615413533065021739 : ℕ).Prime :=
  pock_helper 7201436315176075089609839897367476691048104462476615413533065021739 2 223 [(15201432905196083562906601602721786837858186072775135552603, 1), (225373, 1), (1051, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_221
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_223 : (11467184916715951 : ℕ).Prime :=
  pock_helper 11467184916715951 3 54 [(32573, 1), (11813, 1), (3257, 1), (61, 1), (5, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_224 : (1215521601171890807 : ℕ).Prime :=
  pock_helper 1215521601171890807 5 61 [(11467184916715951, 1), (53, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_223
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_225 : (206638672199221437191 : ℕ).Prime :=
  pock_helper 206638672199221437191 7 68 [(1215521601171890807, 1), (17, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_224
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_226 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129 13 299 [(7201436315176075089609839897367476691048104462476615413533065021739, 1), (206638672199221437191, 1), (7, 1), (3, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_222
      · exact cert_225
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_227 : (299016581 : ℕ).Prime :=
  pock_helper 299016581 2 29 [(189251, 1), (79, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_228 : (14220029 : ℕ).Prime :=
  pock_helper 14220029 2 24 [(3555007, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_229 : (4974868610361993331 : ℕ).Prime :=
  pock_helper 4974868610361993331 2 63 [(299016581, 1), (14220029, 1), (13, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_227
      · exact cert_228
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_230 : (11499543953 : ℕ).Prime :=
  pock_helper 11499543953 3 34 [(305449, 1), (181, 1), (13, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_231 : (22999087907 : ℕ).Prime :=
  pock_helper 22999087907 2 35 [(11499543953, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_230
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_232 : (53864553850831211 : ℕ).Prime :=
  pock_helper 53864553850831211 2 56 [(22999087907, 1), (234203, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_231
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 43 digits. -/
private theorem cert_233 : (4418904424034158555949547628088872244242033 : ℕ).Prime :=
  pock_helper 4418904424034158555949547628088872244242033 7 142 [(4974868610361993331, 1), (53864553850831211, 1), (683, 1), (503, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_229
      · exact cert_232
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_234 : (402585761 : ℕ).Prime :=
  pock_helper 402585761 3 29 [(2999, 1), (839, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_235 : (120959307407017 : ℕ).Prime :=
  pock_helper 120959307407017 11 47 [(402585761, 1), (107, 1), (13, 1), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_234
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_236 : (2366710855645183442959 : ℕ).Prime :=
  pock_helper 2366710855645183442959 3 72 [(120959307407017, 1), (3261029, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_235
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_237 : (7732828661 : ℕ).Prime :=
  pock_helper 7732828661 2 33 [(3828133, 1), (101, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_238 : (4407712336771 : ℕ).Prime :=
  pock_helper 4407712336771 3 43 [(7732828661, 1), (19, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_237
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_239 : (169114769 : ℕ).Prime :=
  pock_helper 169114769 3 28 [(7789, 1), (59, 1), (23, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_240 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229 2 299 [(4418904424034158555949547628088872244242033, 1), (2366710855645183442959, 1), (4407712336771, 1), (169114769, 1), (32069, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_233
      · exact cert_236
      · exact cert_238
      · exact cert_239
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_241 : (51962785915753 : ℕ).Prime :=
  pock_helper 51962785915753 13 46 [(110933, 1), (13931, 1), (467, 1), (3, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_242 : (2078511436630121 : ℕ).Prime :=
  pock_helper 2078511436630121 3 51 [(51962785915753, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_241
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_243 : (34158031 : ℕ).Prime :=
  pock_helper 34158031 13 26 [(30773, 1), (37, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_244 : (204948187 : ℕ).Prime :=
  pock_helper 204948187 2 28 [(34158031, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_243
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 34 digits. -/
private theorem cert_245 : (6477226743683174716571913068507497 : ℕ).Prime :=
  pock_helper 6477226743683174716571913068507497 5 113 [(2078511436630121, 1), (204948187, 1), (720763, 1), (293, 1), (3, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_242
      · exact cert_244
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_246 : (160866779 : ℕ).Prime :=
  pock_helper 160866779 2 28 [(737921, 1), (109, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_247 : (69901770934033393 : ℕ).Prime :=
  pock_helper 69901770934033393 5 56 [(160866779, 1), (9052751, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_246
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 57 digits. -/
private theorem cert_248 : (116537466984665627953034708176397463390432869374874257549 : ℕ).Prime :=
  pock_helper 116537466984665627953034708176397463390432869374874257549 2 187 [(6477226743683174716571913068507497, 1), (69901770934033393, 1), (241, 1), (89, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_245
      · exact cert_247
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_249 : (52181629 : ℕ).Prime :=
  pock_helper 52181629 2 26 [(7333, 1), (593, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_250 : (176695608476229709 : ℕ).Prime :=
  pock_helper 176695608476229709 7 58 [(52181629, 1), (4782719, 1), (59, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_249
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_251 : (2120347301714756509 : ℕ).Prime :=
  pock_helper 2120347301714756509 2 61 [(176695608476229709, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_250
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_252 : (20150267 : ℕ).Prime :=
  pock_helper 20150267 2 25 [(10639, 1), (947, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_253 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487 5 299 [(116537466984665627953034708176397463390432869374874257549, 1), (2120347301714756509, 1), (20150267, 1), (217829, 1), (461, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_248
      · exact cert_251
      · exact cert_252
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_254 : (4147260437 : ℕ).Prime :=
  pock_helper 4147260437 2 32 [(1545179, 1), (61, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_255 : (34227293 : ℕ).Prime :=
  pock_helper 34227293 2 26 [(18973, 1), (41, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_256 : (164945316820677181643 : ℕ).Prime :=
  pock_helper 164945316820677181643 2 68 [(4147260437, 1), (34227293, 1), (83, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_254
      · exact cert_255
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_257 : (329890633641354363287 : ℕ).Prime :=
  pock_helper 329890633641354363287 5 69 [(164945316820677181643, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_256
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_258 : (1655061418833311493209534308533518401 : ℕ).Prime :=
  pock_helper 1655061418833311493209534308533518401 11 121 [(329890633641354363287, 1), (59377, 1), (25183, 1), (233, 1), (5, 2), (3, 2), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_257
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 42 digits. -/
private theorem cert_259 : (744747847369451172337412667222529677118783 : ℕ).Prime :=
  pock_helper 744747847369451172337412667222529677118783 3 140 [(1655061418833311493209534308533518401, 1), (641, 1), (13, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_258
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 44 digits. -/
private theorem cert_260 : (38726888063211460961545458695571543210176717 : ℕ).Prime :=
  pock_helper 38726888063211460961545458695571543210176717 2 145 [(744747847369451172337412667222529677118783, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_259
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_261 : (111931372219 : ℕ).Prime :=
  pock_helper 111931372219 2 37 [(285113, 1), (1109, 1), (59, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_262 : (245129705159611 : ℕ).Prime :=
  pock_helper 245129705159611 23 48 [(111931372219, 1), (73, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_261
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_263 : (14217522899257439 : ℕ).Prime :=
  pock_helper 14217522899257439 11 54 [(245129705159611, 1), (29, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_262
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_264 : (115483099 : ℕ).Prime :=
  pock_helper 115483099 2 27 [(8581, 1), (2243, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_265 : (113635369417 : ℕ).Prime :=
  pock_helper 113635369417 5 37 [(115483099, 1), (41, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_264
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_266 : (28489727874464217203701549572943 : ℕ).Prime :=
  pock_helper 28489727874464217203701549572943 3 105 [(14217522899257439, 1), (113635369417, 1), (2939, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_263
      · exact cert_265
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_267 : (11283761 : ℕ).Prime :=
  pock_helper 11283761 3 24 [(3001, 1), (47, 1), (5, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_268 : (744728227 : ℕ).Prime :=
  pock_helper 744728227 2 30 [(11283761, 1), (11, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_267
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_269 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111 29 299 [(38726888063211460961545458695571543210176717, 1), (28489727874464217203701549572943, 1), (744728227, 1), (7159, 1), (17, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_260
      · exact cert_266
      · exact cert_268
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_270 : (1052173501 : ℕ).Prime :=
  pock_helper 1052173501 2 30 [(100207, 1), (7, 1), (5, 3), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_271 : (189168169397789 : ℕ).Prime :=
  pock_helper 189168169397789 2 48 [(1052173501, 1), (6421, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_270
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_272 : (2831405074683436646283538151531 : ℕ).Prime :=
  pock_helper 2831405074683436646283538151531 7 102 [(189168169397789, 1), (484327, 1), (69427, 1), (6359, 1), (7, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_271
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_273 : (4764733763 : ℕ).Prime :=
  pock_helper 4764733763 2 33 [(3716641, 1), (641, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_274 : (9529467527 : ℕ).Prime :=
  pock_helper 9529467527 5 34 [(4764733763, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_273
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_275 : (482438575255746299 : ℕ).Prime :=
  pock_helper 482438575255746299 2 59 [(9529467527, 1), (59281, 1), (61, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_274
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_276 : (76465413523 : ℕ).Prime :=
  pock_helper 76465413523 2 37 [(23159, 1), (3109, 1), (59, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_277 : (305861654093 : ℕ).Prime :=
  pock_helper 305861654093 2 39 [(76465413523, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_276
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 76 digits. -/
private theorem cert_278 : (1076816245108724712233609143583394882224298942700903835752063578872374793467 : ℕ).Prime :=
  pock_helper 1076816245108724712233609143583394882224298942700903835752063578872374793467 3 250 [(2831405074683436646283538151531, 1), (482438575255746299, 1), (305861654093, 1), (1996343, 1), (7331, 1), (599, 1), (7, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_272
      · exact cert_275
      · exact cert_277
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_279 : (890015519 : ℕ).Prime :=
  pock_helper 890015519 7 30 [(907, 1), (31, 1), (19, 1), (17, 1), (7, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_280 : (19347157352023 : ℕ).Prime :=
  pock_helper 19347157352023 3 45 [(890015519, 1), (3623, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_279
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_281 : (77388629408093 : ℕ).Prime :=
  pock_helper 77388629408093 2 47 [(19347157352023, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_280
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_282 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173 2 299 [(1076816245108724712233609143583394882224298942700903835752063578872374793467, 1), (77388629408093, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_278
      · exact cert_281
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_283 : (31230853553 : ℕ).Prime :=
  pock_helper 31230853553 3 35 [(219787, 1), (107, 1), (83, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_284 : (80363534630770482953137 : ℕ).Prime :=
  pock_helper 80363534630770482953137 7 77 [(31230853553, 1), (456791, 1), (227, 1), (47, 1), (11, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_283
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_285 : (10447259502000162783907811 : ℕ).Prime :=
  pock_helper 10447259502000162783907811 2 84 [(80363534630770482953137, 1), (13, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_284
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_286 : (372626521 : ℕ).Prime :=
  pock_helper 372626521 13 29 [(443603, 1), (7, 1), (5, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_287 : (9895156140145319 : ℕ).Prime :=
  pock_helper 9895156140145319 7 54 [(372626521, 1), (8741, 1), (31, 1), (7, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_286
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 44 digits. -/
private theorem cert_288 : (47760295972115698520359286260186358504259559 : ℕ).Prime :=
  pock_helper 47760295972115698520359286260186358504259559 3 146 [(10447259502000162783907811, 1), (9895156140145319, 1), (11, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_285
      · exact cert_287
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_289 : (43877959031 : ℕ).Prime :=
  pock_helper 43877959031 7 36 [(2351, 1), (463, 1), (139, 1), (29, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 57 digits. -/
private theorem cert_290 : (402359867514801972109108239729572783015996038808088447169 : ℕ).Prime :=
  pock_helper 402359867514801972109108239729572783015996038808088447169 7 189 [(47760295972115698520359286260186358504259559, 1), (43877959031, 1), (3, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_288
      · exact cert_289
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_291 : (2871144517 : ℕ).Prime :=
  pock_helper 2871144517 2 32 [(2466619, 1), (97, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_292 : (477660828715223 : ℕ).Prime :=
  pock_helper 477660828715223 5 49 [(2871144517, 1), (431, 1), (193, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_291
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_293 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191 11 299 [(402359867514801972109108239729572783015996038808088447169, 1), (477660828715223, 1), (3583793, 1), (1444501, 1), (33503, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_290
      · exact cert_292
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_294 : (1077166219 : ℕ).Prime :=
  pock_helper 1077166219 2 31 [(2659, 1), (631, 1), (107, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_295 : (34124345809441049514408541 : ℕ).Prime :=
  pock_helper 34124345809441049514408541 2 85 [(1077166219, 1), (1914179, 1), (293, 1), (61, 2), (23, 1), (11, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_294
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_296 : (10365220559 : ℕ).Prime :=
  pock_helper 10365220559 7 34 [(348739, 1), (193, 1), (11, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_297 : (73266769 : ℕ).Prime :=
  pock_helper 73266769 19 27 [(56533, 1), (3, 4), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_298 : (6594009211 : ℕ).Prime :=
  pock_helper 6594009211 11 33 [(73266769, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_297
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 47 digits. -/
private theorem cert_299 : (69970292000742953289148342118051975969909802271 : ℕ).Prime :=
  pock_helper 69970292000742953289148342118051975969909802271 3 156 [(34124345809441049514408541, 1), (10365220559, 1), (6594009211, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_295
      · exact cert_296
      · exact cert_298
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 61 digits. -/
private theorem cert_300 : (4759585072922070618447077672994894518946958652763505407657947 : ℕ).Prime :=
  pock_helper 4759585072922070618447077672994894518946958652763505407657947 2 202 [(69970292000742953289148342118051975969909802271, 1), (12547, 1), (2879, 1), (67, 1), (47, 1), (23, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_299
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_301 : (53834370553 : ℕ).Prime :=
  pock_helper 53834370553 5 36 [(2800373, 1), (89, 1), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_302 : (416539151747554478703059 : ℕ).Prime :=
  pock_helper 416539151747554478703059 2 79 [(53834370553, 1), (4598999, 1), (841207, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_301
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_303 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201 37 299 [(4759585072922070618447077672994894518946958652763505407657947, 1), (416539151747554478703059, 1), (97, 1), (13, 1), (5, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_300
      · exact cert_302
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_304 : (2086523903 : ℕ).Prime :=
  pock_helper 2086523903 5 31 [(75659, 1), (13789, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_305 : (689490569 : ℕ).Prime :=
  pock_helper 689490569 3 30 [(1867, 1), (67, 1), (53, 1), (13, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_306 : (1378981139 : ℕ).Prime :=
  pock_helper 1378981139 2 31 [(689490569, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_305
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_307 : (11509108433238662069 : ℕ).Prime :=
  pock_helper 11509108433238662069 2 64 [(2086523903, 1), (1378981139, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_304
      · exact cert_306
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 27 digits. -/
private theorem cert_308 : (789812704340304383349069829 : ℕ).Prime :=
  pock_helper 789812704340304383349069829 11 90 [(11509108433238662069, 1), (3137, 1), (1823, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_307
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_309 : (6738816244215335354992736689219393763 : ℕ).Prime :=
  pock_helper 6738816244215335354992736689219393763 2 123 [(789812704340304383349069829, 1), (3388471, 1), (1259, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_308
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 43 digits. -/
private theorem cert_310 : (3024542461993703675369260051802205186284713 : ℕ).Prime :=
  pock_helper 3024542461993703675369260051802205186284713 5 142 [(6738816244215335354992736689219393763, 1), (18701, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_309
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_311 : (12603847 : ℕ).Prime :=
  pock_helper 12603847 5 24 [(1583, 1), (1327, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_312 : (212196228946492474003 : ℕ).Prime :=
  pock_helper 212196228946492474003 2 68 [(12603847, 1), (16139, 1), (15511, 1), (1019, 1), (11, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_311
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_313 : (115434748546891905857633 : ℕ).Prime :=
  pock_helper 115434748546891905857633 3 77 [(212196228946492474003, 1), (17, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_312
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_314 : (436993708880564593139454644323 : ℕ).Prime :=
  pock_helper 436993708880564593139454644323 2 99 [(115434748546891905857633, 1), (73, 1), (67, 1), (43, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_313
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_315 : (33238997579 : ℕ).Prime :=
  pock_helper 33238997579 2 35 [(430769, 1), (941, 1), (41, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_316 : (66477995159 : ℕ).Prime :=
  pock_helper 66477995159 7 36 [(33238997579, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_315
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_317 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299 7 299 [(3024542461993703675369260051802205186284713, 1), (436993708880564593139454644323, 1), (66477995159, 1), (10597, 1), (179, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_310
      · exact cert_314
      · exact cert_316
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_318 : (240723731 : ℕ).Prime :=
  pock_helper 240723731 2 28 [(97459, 1), (19, 1), (13, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_319 : (91250311 : ℕ).Prime :=
  pock_helper 91250311 17 27 [(5011, 1), (607, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_320 : (62416232677071478843766407 : ℕ).Prime :=
  pock_helper 62416232677071478843766407 5 86 [(240723731, 1), (91250311, 1), (55061, 1), (61, 1), (47, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_318
      · exact cert_319
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_321 : (71580407 : ℕ).Prime :=
  pock_helper 71580407 5 27 [(47279, 1), (757, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_322 : (974925143341 : ℕ).Prime :=
  pock_helper 974925143341 2 40 [(71580407, 1), (227, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_321
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_323 : (569406979818597733 : ℕ).Prime :=
  pock_helper 569406979818597733 11 59 [(974925143341, 1), (409, 1), (17, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_322
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_324 : (84951613 : ℕ).Prime :=
  pock_helper 84951613 2 27 [(786589, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_325 : (365291935901 : ℕ).Prime :=
  pock_helper 365291935901 2 39 [(84951613, 1), (43, 1), (5, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_324
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 60 digits. -/
private theorem cert_326 : (362706832208205438254228368220240087421270981908773674097679 : ℕ).Prime :=
  pock_helper 362706832208205438254228368220240087421270981908773674097679 7 198 [(62416232677071478843766407, 1), (569406979818597733, 1), (365291935901, 1), (229, 1), (61, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_320
      · exact cert_323
      · exact cert_325
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_327 : (6434988877 : ℕ).Prime :=
  pock_helper 6434988877 5 33 [(1285969, 1), (139, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_328 : (566279021177 : ℕ).Prime :=
  pock_helper 566279021177 3 40 [(6434988877, 1), (11, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_327
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_329 : (147282413 : ℕ).Prime :=
  pock_helper 147282413 2 28 [(46199, 1), (797, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_330 : (294564827 : ℕ).Prime :=
  pock_helper 294564827 2 29 [(147282413, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_329
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_331 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363 2 299 [(362706832208205438254228368220240087421270981908773674097679, 1), (566279021177, 1), (294564827, 1), (8819893, 1), (937, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_326
      · exact cert_328
      · exact cert_330
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_332 : (38865359569567 : ℕ).Prime :=
  pock_helper 38865359569567 3 46 [(9113171, 1), (710791, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_333 : (41192624063165237064659 : ℕ).Prime :=
  pock_helper 41192624063165237064659 2 76 [(38865359569567, 1), (839, 1), (151, 1), (89, 1), (47, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_332
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_334 : (20080234442654907302619100313719 : ℕ).Prime :=
  pock_helper 20080234442654907302619100313719 11 104 [(41192624063165237064659, 1), (788789, 1), (103, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_333
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_335 : (80320937770619629210476401254877 : ℕ).Prime :=
  pock_helper 80320937770619629210476401254877 2 106 [(20080234442654907302619100313719, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_334
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_336 : (346124421605093 : ℕ).Prime :=
  pock_helper 346124421605093 2 49 [(842623, 1), (13883, 1), (569, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_337 : (692248843210187 : ℕ).Prime :=
  pock_helper 692248843210187 2 50 [(346124421605093, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_336
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_338 : (3702146813488080077 : ℕ).Prime :=
  pock_helper 3702146813488080077 2 62 [(692248843210187, 1), (191, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_337
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_339 : (4938663849193098822719 : ℕ).Prime :=
  pock_helper 4938663849193098822719 31 73 [(3702146813488080077, 1), (29, 1), (23, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_338
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_340 : (8619557693 : ℕ).Prime :=
  pock_helper 8619557693 2 34 [(34721, 1), (1171, 1), (53, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 82 digits. -/
private theorem cert_341 : (1413702781295101713257352953733477645621197570697664471397360264047107833843960893 : ℕ).Prime :=
  pock_helper 1413702781295101713257352953733477645621197570697664471397360264047107833843960893 5 270 [(80320937770619629210476401254877, 1), (4938663849193098822719, 1), (8619557693, 1), (12503, 1), (8539, 1), (307, 1), (281, 1), (43, 1), (29, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_335
      · exact cert_339
      · exact cert_340
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_342 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753 3 299 [(1413702781295101713257352953733477645621197570697664471397360264047107833843960893, 1), (6481, 1), (1949, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_341
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_343 : (53318180099 : ℕ).Prime :=
  pock_helper 53318180099 2 36 [(1646741, 1), (16189, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_344 : (106636360199 : ℕ).Prime :=
  pock_helper 106636360199 13 37 [(53318180099, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_343
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_345 : (5376337334771671650313 : ℕ).Prime :=
  pock_helper 5376337334771671650313 11 73 [(106636360199, 1), (4763557, 1), (7, 2), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_344
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_346 : (36347681 : ℕ).Prime :=
  pock_helper 36347681 3 26 [(619, 1), (367, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_347 : (51904488469 : ℕ).Prime :=
  pock_helper 51904488469 31 36 [(36347681, 1), (17, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_346
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_348 : (519044884691 : ℕ).Prime :=
  pock_helper 519044884691 2 39 [(51904488469, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_347
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 39 digits. -/
private theorem cert_349 : (425939975991248449282289579123620083989 : ℕ).Prime :=
  pock_helper 425939975991248449282289579123620083989 3 129 [(5376337334771671650313, 1), (519044884691, 1), (3469, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_345
      · exact cert_348
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_350 : (44085822541603 : ℕ).Prime :=
  pock_helper 44085822541603 13 46 [(118661, 1), (3989, 1), (43, 1), (19, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_351 : (902701302361863029 : ℕ).Prime :=
  pock_helper 902701302361863029 2 60 [(44085822541603, 1), (5119, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_350
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_352 : (1805402604723726059 : ℕ).Prime :=
  pock_helper 1805402604723726059 2 61 [(902701302361863029, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_351
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_353 : (14735696059755052093559 : ℕ).Prime :=
  pock_helper 14735696059755052093559 7 74 [(1805402604723726059, 1), (53, 1), (11, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_352
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_354 : (348513479 : ℕ).Prime :=
  pock_helper 348513479 13 29 [(233, 1), (137, 1), (103, 1), (53, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_355 : (697026959 : ℕ).Prime :=
  pock_helper 697026959 13 30 [(348513479, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_354
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 33 digits. -/
private theorem cert_356 : (924405967195141162109401193137291 : ℕ).Prime :=
  pock_helper 924405967195141162109401193137291 2 110 [(14735696059755052093559, 1), (697026959, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_353
      · exact cert_355
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_357 : (21647877547 : ℕ).Prime :=
  pock_helper 21647877547 3 35 [(4962833, 1), (727, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_358 : (779323591693 : ℕ).Prime :=
  pock_helper 779323591693 2 40 [(21647877547, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_357
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_359 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301 7 299 [(425939975991248449282289579123620083989, 1), (924405967195141162109401193137291, 1), (779323591693, 1), (71, 1), (17, 1), (5, 2), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_349
      · exact cert_356
      · exact cert_358
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_360 : (53302431541 : ℕ).Prime :=
  pock_helper 53302431541 2 36 [(891047, 1), (997, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_361 : (319814589247 : ℕ).Prime :=
  pock_helper 319814589247 3 39 [(53302431541, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_360
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_362 : (5117033427953 : ℕ).Prime :=
  pock_helper 5117033427953 3 43 [(319814589247, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_361
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_363 : (26721148560770567 : ℕ).Prime :=
  pock_helper 26721148560770567 5 55 [(5117033427953, 1), (373, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_362
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_364 : (6681461160575807765631713 : ℕ).Prime :=
  pock_helper 6681461160575807765631713 3 83 [(26721148560770567, 1), (7813873, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_363
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_365 : (229147553 : ℕ).Prime :=
  pock_helper 229147553 3 28 [(7160861, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_366 : (23831345513 : ℕ).Prime :=
  pock_helper 23831345513 3 35 [(229147553, 1), (13, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_365
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_367 : (160441153 : ℕ).Prime :=
  pock_helper 160441153 5 28 [(11447, 1), (73, 1), (3, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 47 digits. -/
private theorem cert_368 : (10729638155956753593075113484607173326729375941 : ℕ).Prime :=
  pock_helper 10729638155956753593075113484607173326729375941 43 153 [(6681461160575807765631713, 1), (23831345513, 1), (160441153, 1), (7, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_364
      · exact cert_366
      · exact cert_367
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_369 : (10601509 : ℕ).Prime :=
  pock_helper 10601509 11 24 [(18797, 1), (47, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_370 : (99684099323208679 : ℕ).Prime :=
  pock_helper 99684099323208679 3 57 [(10601509, 1), (1225283, 1), (1279, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_369
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_371 : (200969125281548089384741 : ℕ).Prime :=
  pock_helper 200969125281548089384741 17 78 [(99684099323208679, 1), (33601, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_370
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_372 : (144661193821913382604745497139 : ℕ).Prime :=
  pock_helper 144661193821913382604745497139 2 97 [(200969125281548089384741, 1), (32719, 1), (11, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_371
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_373 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421 37 299 [(10729638155956753593075113484607173326729375941, 1), (144661193821913382604745497139, 1), (5921891, 1), (1813223, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_368
      · exact cert_372
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_374 : (425051407483 : ℕ).Prime :=
  pock_helper 425051407483 3 39 [(1063, 1), (701, 1), (103, 1), (71, 1), (13, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_375 : (254522831 : ℕ).Prime :=
  pock_helper 254522831 19 28 [(1106621, 1), (23, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_376 : (1527136987 : ℕ).Prime :=
  pock_helper 1527136987 2 31 [(254522831, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_375
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_377 : (105156099570479055542803 : ℕ).Prime :=
  pock_helper 105156099570479055542803 2 77 [(425051407483, 1), (1527136987, 1), (3, 4), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_374
      · exact cert_376
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_378 : (6460576870103706818150842258699 : ℕ).Prime :=
  pock_helper 6460576870103706818150842258699 3 103 [(105156099570479055542803, 1), (602333, 1), (17, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_377
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 33 digits. -/
private theorem cert_379 : (193817306103111204544525267760971 : ℕ).Prime :=
  pock_helper 193817306103111204544525267760971 7 108 [(6460576870103706818150842258699, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_378
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_380 : (3581599039 : ℕ).Prime :=
  pock_helper 3581599039 3 32 [(25169, 1), (641, 1), (37, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_381 : (14326396157 : ℕ).Prime :=
  pock_helper 14326396157 2 34 [(3581599039, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_380
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_382 : (85958376943 : ℕ).Prime :=
  pock_helper 85958376943 3 37 [(14326396157, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_381
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_383 : (75641996375808912001 : ℕ).Prime :=
  pock_helper 75641996375808912001 17 67 [(85958376943, 1), (97, 1), (7, 1), (5, 3), (3, 4), (2, 7)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_382
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 61 digits. -/
private theorem cert_384 : (2700367107603035640685154938861980817357334646492113611234921 : ℕ).Prime :=
  pock_helper 2700367107603035640685154938861980817357334646492113611234921 7 201 [(193817306103111204544525267760971, 1), (75641996375808912001, 1), (1534921, 1), (5, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_379
      · exact cert_383
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_385 : (336271517 : ℕ).Prime :=
  pock_helper 336271517 2 29 [(16657, 1), (103, 1), (7, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_386 : (1088174629013 : ℕ).Prime :=
  pock_helper 1088174629013 2 40 [(336271517, 1), (809, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_385
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_387 : (1986415282087976566499 : ℕ).Prime :=
  pock_helper 1986415282087976566499 2 71 [(1088174629013, 1), (3524047, 1), (37, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_386
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_388 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437 2 299 [(2700367107603035640685154938861980817357334646492113611234921, 1), (1986415282087976566499, 1), (249233, 1), (17, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_384
      · exact cert_387
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_389 : (43280257 : ℕ).Prime :=
  pock_helper 43280257 13 26 [(2749, 1), (41, 1), (3, 1), (2, 7)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_390 : (110643065903853667 : ℕ).Prime :=
  pock_helper 110643065903853667 2 57 [(43280257, 1), (384889, 1), (41, 1), (3, 4), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_389
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_391 : (89130709 : ℕ).Prime :=
  pock_helper 89130709 2 27 [(3583, 1), (691, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_392 : (92874198779 : ℕ).Prime :=
  pock_helper 92874198779 2 37 [(89130709, 1), (521, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_391
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_393 : (4643709938951 : ℕ).Prime :=
  pock_helper 4643709938951 13 43 [(92874198779, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_392
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_394 : (184124021 : ℕ).Prime :=
  pock_helper 184124021 2 28 [(3371, 1), (2731, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_395 : (368248043 : ℕ).Prime :=
  pock_helper 368248043 2 29 [(184124021, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_394
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 41 digits. -/
private theorem cert_396 : (52977049230617030708200696995923311616681 : ℕ).Prime :=
  pock_helper 52977049230617030708200696995923311616681 29 136 [(110643065903853667, 1), (4643709938951, 1), (368248043, 1), (7, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_390
      · exact cert_393
      · exact cert_395
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 43 digits. -/
private theorem cert_397 : (1377403279996042798413218121894006102033707 : ℕ).Prime :=
  pock_helper 1377403279996042798413218121894006102033707 2 140 [(52977049230617030708200696995923311616681, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_396
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_398 : (87562141 : ℕ).Prime :=
  pock_helper 87562141 11 27 [(1459369, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_399 : (157632868713841 : ℕ).Prime :=
  pock_helper 157632868713841 41 48 [(87562141, 1), (577, 1), (13, 1), (5, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_398
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 29 digits. -/
private theorem cert_400 : (73377284623470428818606905343 : ℕ).Prime :=
  pock_helper 73377284623470428818606905343 3 96 [(157632868713841, 1), (1850789, 1), (8627, 1), (113, 1), (43, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_399
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_401 : (532542343 : ℕ).Prime :=
  pock_helper 532542343 5 29 [(861719, 1), (103, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_402 : (134248599246871 : ℕ).Prime :=
  pock_helper 134248599246871 23 47 [(532542343, 1), (2801, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_401
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_403 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701 2 299 [(1377403279996042798413218121894006102033707, 1), (73377284623470428818606905343, 1), (134248599246871, 1), (67, 1), (11, 1), (5, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_397
      · exact cert_400
      · exact cert_402
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_404 : (60259961959 : ℕ).Prime :=
  pock_helper 60259961959 23 36 [(3797, 1), (2347, 1), (23, 1), (7, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_405 : (79181590014127 : ℕ).Prime :=
  pock_helper 79181590014127 3 47 [(60259961959, 1), (73, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_404
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_406 : (50780083 : ℕ).Prime :=
  pock_helper 50780083 2 26 [(87251, 1), (97, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_407 : (37780381753 : ℕ).Prime :=
  pock_helper 37780381753 5 36 [(50780083, 1), (31, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_406
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_408 : (453364581037 : ℕ).Prime :=
  pock_helper 453364581037 2 39 [(37780381753, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_407
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 42 digits. -/
private theorem cert_409 : (116203633402513533635693201606757936604699 : ℕ).Prime :=
  pock_helper 116203633402513533635693201606757936604699 2 137 [(79181590014127, 1), (453364581037, 1), (2245057, 1), (242491, 1), (991, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_405
      · exact cert_408
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_410 : (2993641507 : ℕ).Prime :=
  pock_helper 2993641507 2 32 [(29327, 1), (107, 1), (53, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_411 : (162995029 : ℕ).Prime :=
  pock_helper 162995029 2 28 [(18839, 1), (103, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_412 : (1951794736996274813 : ℕ).Prime :=
  pock_helper 1951794736996274813 2 61 [(2993641507, 1), (162995029, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_410
      · exact cert_411
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_413 : (6524021120954317 : ℕ).Prime :=
  pock_helper 6524021120954317 2 53 [(466579, 1), (292549, 1), (569, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_414 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731 2 299 [(116203633402513533635693201606757936604699, 1), (1951794736996274813, 1), (6524021120954317, 1), (15731, 1), (6599, 1), (3637, 1), (179, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_409
      · exact cert_412
      · exact cert_413
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_415 : (100440719 : ℕ).Prime :=
  pock_helper 100440719 7 27 [(2731, 1), (71, 1), (37, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_416 : (883518765367127393929 : ℕ).Prime :=
  pock_helper 883518765367127393929 11 70 [(100440719, 1), (130699, 1), (311, 1), (127, 1), (71, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_415
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_417 : (21529427 : ℕ).Prime :=
  pock_helper 21529427 2 25 [(16139, 1), (29, 1), (23, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_418 : (2396728248024813875839125734059 : ℕ).Prime :=
  pock_helper 2396728248024813875839125734059 2 101 [(883518765367127393929, 1), (21529427, 1), (7, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_416
      · exact cert_417
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 43 digits. -/
private theorem cert_419 : (2346340945937504799853769135456785605975491 : ℕ).Prime :=
  pock_helper 2346340945937504799853769135456785605975491 2 141 [(2396728248024813875839125734059, 1), (176017, 1), (6701, 1), (83, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_418
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_420 : (74825443409 : ℕ).Prime :=
  pock_helper 74825443409 3 37 [(1084301, 1), (227, 1), (19, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_421 : (912271806042529 : ℕ).Prime :=
  pock_helper 912271806042529 17 50 [(74825443409, 1), (127, 1), (3, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_420
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_422 : (58385395586721857 : ℕ).Prime :=
  pock_helper 58385395586721857 3 56 [(912271806042529, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_421
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_423 : (445947651491381543767 : ℕ).Prime :=
  pock_helper 445947651491381543767 3 69 [(58385395586721857, 1), (67, 1), (19, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_422
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_424 : (1818320332620503848001878811 : ℕ).Prime :=
  pock_helper 1818320332620503848001878811 2 91 [(445947651491381543767, 1), (1879, 1), (31, 1), (7, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_423
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_425 : (670429151471 : ℕ).Prime :=
  pock_helper 670429151471 19 40 [(132299, 1), (2293, 1), (17, 1), (13, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_426 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769 17 299 [(2346340945937504799853769135456785605975491, 1), (1818320332620503848001878811, 1), (670429151471, 1), (373, 1), (283, 1), (23, 1), (3, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_419
      · exact cert_424
      · exact cert_425
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_427 : (15748433761 : ℕ).Prime :=
  pock_helper 15748433761 19 34 [(1131353, 1), (29, 1), (5, 1), (3, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_428 : (3748127235119 : ℕ).Prime :=
  pock_helper 3748127235119 13 42 [(15748433761, 1), (17, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_427
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_429 : (9619000479999082942481892337 : ℕ).Prime :=
  pock_helper 9619000479999082942481892337 5 93 [(3748127235119, 1), (3253231, 1), (13033, 1), (97, 1), (13, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_428
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_430 : (2722122253 : ℕ).Prime :=
  pock_helper 2722122253 5 32 [(779531, 1), (97, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 51 digits. -/
private theorem cert_431 : (299557821746197994748460882884788253840787746091079 : ℕ).Prime :=
  pock_helper 299557821746197994748460882884788253840787746091079 11 168 [(9619000479999082942481892337, 1), (2722122253, 1), (5178919, 1), (100411, 1), (11, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_429
      · exact cert_430
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_432 : (4126526573127359 : ℕ).Prime :=
  pock_helper 4126526573127359 7 52 [(398669, 1), (1429, 1), (307, 1), (251, 1), (47, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_433 : (30098239 : ℕ).Prime :=
  pock_helper 30098239 3 25 [(39499, 1), (127, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_434 : (745207098227029371724807 : ℕ).Prime :=
  pock_helper 745207098227029371724807 3 80 [(4126526573127359, 1), (30098239, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_432
      · exact cert_433
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_435 : (13644391 : ℕ).Prime :=
  pock_helper 13644391 3 24 [(11093, 1), (41, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_436 : (491198077 : ℕ).Prime :=
  pock_helper 491198077 2 29 [(13644391, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_435
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_437 : (15554278306283 : ℕ).Prime :=
  pock_helper 15554278306283 2 44 [(491198077, 1), (223, 1), (71, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_436
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_438 : (2239816076104753 : ℕ).Prime :=
  pock_helper 2239816076104753 5 51 [(15554278306283, 1), (3, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_437
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_439 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019 2 299 [(299557821746197994748460882884788253840787746091079, 1), (745207098227029371724807, 1), (2239816076104753, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_431
      · exact cert_434
      · exact cert_438
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_440 : (294842999443 : ℕ).Prime :=
  pock_helper 294842999443 2 39 [(1494859, 1), (463, 1), (71, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_441 : (91401329827331 : ℕ).Prime :=
  pock_helper 91401329827331 2 47 [(294842999443, 1), (31, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_440
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_442 : (5118474470330537 : ℕ).Prime :=
  pock_helper 5118474470330537 3 53 [(91401329827331, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_441
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_443 : (10245363712690297402829 : ℕ).Prime :=
  pock_helper 10245363712690297402829 2 74 [(5118474470330537, 1), (21757, 1), (23, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_442
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_444 : (30203332225010996743539893 : ℕ).Prime :=
  pock_helper 30203332225010996743539893 2 85 [(10245363712690297402829, 1), (67, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_443
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_445 : (282401156303852819552097999551 : ℕ).Prime :=
  pock_helper 282401156303852819552097999551 7 98 [(30203332225010996743539893, 1), (17, 1), (11, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_444
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_446 : (47595099254663 : ℕ).Prime :=
  pock_helper 47595099254663 5 46 [(2240023, 1), (4889, 1), (53, 1), (41, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 45 digits. -/
private theorem cert_447 : (940863774473943228707351737234941338605941911 : ℕ).Prime :=
  pock_helper 940863774473943228707351737234941338605941911 7 150 [(282401156303852819552097999551, 1), (47595099254663, 1), (7, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_445
      · exact cert_446
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 56 digits. -/
private theorem cert_448 : (47076173808161801279262577811156570674228344243298411301 : ℕ).Prime :=
  pock_helper 47076173808161801279262577811156570674228344243298411301 3 185 [(940863774473943228707351737234941338605941911, 1), (335131, 1), (1493, 1), (5, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_447
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_449 : (548634678168341 : ℕ).Prime :=
  pock_helper 548634678168341 2 49 [(22717, 1), (4721, 1), (223, 1), (37, 1), (31, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_450 : (240373607 : ℕ).Prime :=
  pock_helper 240373607 5 28 [(13709, 1), (797, 1), (11, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_451 : (20191382989 : ℕ).Prime :=
  pock_helper 20191382989 11 35 [(240373607, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_450
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_452 : (11148619 : ℕ).Prime :=
  pock_helper 11148619 2 24 [(3863, 1), (37, 1), (13, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_453 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133 2 299 [(47076173808161801279262577811156570674228344243298411301, 1), (548634678168341, 1), (20191382989, 1), (11148619, 1), (43, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_448
      · exact cert_449
      · exact cert_451
      · exact cert_452
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_454 : (214700357 : ℕ).Prime :=
  pock_helper 214700357 2 28 [(2711, 1), (1523, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_455 : (1288202143 : ℕ).Prime :=
  pock_helper 1288202143 3 31 [(214700357, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_454
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_456 : (42409307 : ℕ).Prime :=
  pock_helper 42409307 2 26 [(16349, 1), (1297, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_457 : (13439412999494045647 : ℕ).Prime :=
  pock_helper 13439412999494045647 3 64 [(1288202143, 1), (42409307, 1), (41, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_455
      · exact cert_456
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_458 : (1007204273 : ℕ).Prime :=
  pock_helper 1007204273 3 30 [(2309, 1), (199, 1), (137, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_459 : (104277872792237 : ℕ).Prime :=
  pock_helper 104277872792237 2 47 [(1007204273, 1), (181, 1), (13, 1), (11, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_458
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_460 : (1336633773450893867 : ℕ).Prime :=
  pock_helper 1336633773450893867 2 61 [(104277872792237, 1), (29, 1), (17, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_459
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_461 : (2387351023727 : ℕ).Prime :=
  pock_helper 2387351023727 5 42 [(32411, 1), (577, 1), (71, 1), (31, 1), (29, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 58 digits. -/
private theorem cert_462 : (9339595112696398295496174845486309314598256949990725815653 : ℕ).Prime :=
  pock_helper 9339595112696398295496174845486309314598256949990725815653 2 193 [(13439412999494045647, 1), (1336633773450893867, 1), (2387351023727, 1), (4349, 1), (107, 1), (13, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_457
      · exact cert_460
      · exact cert_461
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 70 digits. -/
private theorem cert_463 : (3728235385612593906219464253122105959350970167631344433874698554925829 : ℕ).Prime :=
  pock_helper 3728235385612593906219464253122105959350970167631344433874698554925829 3 232 [(9339595112696398295496174845486309314598256949990725815653, 1), (49831, 1), (479, 1), (113, 1), (37, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_462
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_464 : (262375903 : ℕ).Prime :=
  pock_helper 262375903 11 28 [(5441, 1), (47, 1), (19, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_465 : (2623759031 : ℕ).Prime :=
  pock_helper 2623759031 11 32 [(262375903, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_464
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_466 : (5247518063 : ℕ).Prime :=
  pock_helper 5247518063 5 33 [(2623759031, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_465
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_467 : (31485108379 : ℕ).Prime :=
  pock_helper 31485108379 2 35 [(5247518063, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_466
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_468 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201 31 299 [(3728235385612593906219464253122105959350970167631344433874698554925829, 1), (31485108379, 1), (21611, 1), (73, 1), (5, 2), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_463
      · exact cert_467
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_469 : (910234681 : ℕ).Prime :=
  pock_helper 910234681 7 30 [(124349, 1), (61, 1), (5, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_470 : (9102346811 : ℕ).Prime :=
  pock_helper 9102346811 2 34 [(910234681, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_469
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_471 : (18204693623 : ℕ).Prime :=
  pock_helper 18204693623 5 35 [(9102346811, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_470
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_472 : (1716771031 : ℕ).Prime :=
  pock_helper 1716771031 29 31 [(1213, 1), (191, 1), (19, 1), (13, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_473 : (1004233205235910075995966480773 : ℕ).Prime :=
  pock_helper 1004233205235910075995966480773 3 100 [(18204693623, 1), (1716771031, 1), (63697, 1), (109, 1), (89, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_471
      · exact cert_472
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_474 : (17818878313 : ℕ).Prime :=
  pock_helper 17818878313 5 35 [(6029, 1), (4561, 1), (3, 4), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_475 : (748392889147 : ℕ).Prime :=
  pock_helper 748392889147 3 40 [(17818878313, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_474
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_476 : (22451786674411 : ℕ).Prime :=
  pock_helper 22451786674411 2 45 [(748392889147, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_475
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_477 : (45534680017 : ℕ).Prime :=
  pock_helper 45534680017 5 36 [(1861, 1), (103, 1), (101, 1), (7, 2), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 71 digits. -/
private theorem cert_478 : (84473155511516801699753296603537882978672072906944063728424320294815297 : ℕ).Prime :=
  pock_helper 84473155511516801699753296603537882978672072906944063728424320294815297 7 236 [(1004233205235910075995966480773, 1), (22451786674411, 1), (45534680017, 1), (154459, 1), (71693, 1), (38699, 1), (3, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_473
      · exact cert_476
      · exact cert_477
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_479 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369 11 299 [(84473155511516801699753296603537882978672072906944063728424320294815297, 1), (6521923, 1), (939317, 1), (20129, 1), (3, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_478
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_480 : (115839677230721 : ℕ).Prime :=
  pock_helper 115839677230721 3 47 [(2673197, 1), (67709, 1), (5, 1), (2, 7)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_481 : (74219785556488562618461 : ℕ).Prime :=
  pock_helper 74219785556488562618461 2 76 [(115839677230721, 1), (72643, 1), (7, 2), (5, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_480
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_482 : (861650429 : ℕ).Prime :=
  pock_helper 861650429 2 30 [(95021, 1), (2267, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_483 : (610048503733 : ℕ).Prime :=
  pock_helper 610048503733 13 40 [(861650429, 1), (59, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_482
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_484 : (32482216254667088931641 : ℕ).Prime :=
  pock_helper 32482216254667088931641 19 75 [(610048503733, 1), (1783, 1), (139, 1), (131, 1), (41, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_483
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_485 : (10389832997 : ℕ).Prime :=
  pock_helper 10389832997 2 34 [(74509, 1), (491, 1), (71, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_486 : (4826688001 : ℕ).Prime :=
  pock_helper 4826688001 17 33 [(1093, 1), (23, 1), (5, 3), (3, 1), (2, 9)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 70 digits. -/
private theorem cert_487 : (1679046988346873026146887221139362418417358968325633914812660916662337 : ℕ).Prime :=
  pock_helper 1679046988346873026146887221139362418417358968325633914812660916662337 3 230 [(74219785556488562618461, 1), (32482216254667088931641, 1), (10389832997, 1), (4826688001, 1), (31, 1), (7, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_481
      · exact cert_484
      · exact cert_485
      · exact cert_486
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_488 : (21585785531 : ℕ).Prime :=
  pock_helper 21585785531 2 35 [(23747, 1), (5347, 1), (17, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_489 : (43171571063 : ℕ).Prime :=
  pock_helper 43171571063 5 36 [(21585785531, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_488
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_490 : (72614582527967 : ℕ).Prime :=
  pock_helper 72614582527967 5 47 [(43171571063, 1), (29, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_489
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_491 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763 2 299 [(1679046988346873026146887221139362418417358968325633914812660916662337, 1), (72614582527967, 1), (4100939, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_487
      · exact cert_490
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_492 : (16291813 : ℕ).Prime :=
  pock_helper 16291813 2 24 [(1357651, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_493 : (22580452819 : ℕ).Prime :=
  pock_helper 22580452819 3 35 [(16291813, 1), (11, 1), (7, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_492
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_494 : (16212765124043 : ℕ).Prime :=
  pock_helper 16212765124043 2 44 [(22580452819, 1), (359, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_493
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_495 : (52141693 : ℕ).Prime :=
  pock_helper 52141693 5 26 [(10321, 1), (421, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 35 digits. -/
private theorem cert_496 : (37721461748156171027981431724172919 : ℕ).Prime :=
  pock_helper 37721461748156171027981431724172919 29 115 [(16212765124043, 1), (52141693, 1), (4229971, 1), (103421, 1), (17, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_494
      · exact cert_495
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 52 digits. -/
private theorem cert_497 : (2466389430424272624575924487811306129214143786281097 : ℕ).Prime :=
  pock_helper 2466389430424272624575924487811306129214143786281097 17 171 [(37721461748156171027981431724172919, 1), (2221159, 1), (457153, 1), (2683, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_496
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_498 : (135259027 : ℕ).Prime :=
  pock_helper 135259027 2 28 [(3220453, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_499 : (292615042094260586161777 : ℕ).Prime :=
  pock_helper 292615042094260586161777 11 78 [(135259027, 1), (251033, 1), (75659, 1), (113, 1), (7, 1), (3, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_498
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 77 digits. -/
private theorem cert_500 : (21651079410133137758242128758752980815211510601393464207301965097681170881071 : ℕ).Prime :=
  pock_helper 21651079410133137758242128758752980815211510601393464207301965097681170881071 3 254 [(2466389430424272624575924487811306129214143786281097, 1), (292615042094260586161777, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_497
      · exact cert_499
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_501 : (11546768420377 : ℕ).Prime :=
  pock_helper 11546768420377 13 44 [(805121, 1), (4493, 1), (19, 1), (7, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_502 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069 2 299 [(21651079410133137758242128758752980815211510601393464207301965097681170881071, 1), (11546768420377, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_500
      · exact cert_501
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_503 : (95781885718202172715249 : ℕ).Prime :=
  pock_helper 95781885718202172715249 37 77 [(555421, 1), (32257, 1), (4903, 1), (173, 2), (23, 1), (11, 1), (3, 2), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_504 : (59540059 : ℕ).Prime :=
  pock_helper 59540059 3 26 [(3307781, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_505 : (5001364957 : ℕ).Prime :=
  pock_helper 5001364957 2 33 [(59540059, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_504
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_506 : (6704479765807211 : ℕ).Prime :=
  pock_helper 6704479765807211 2 53 [(5001364957, 1), (134053, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_505
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 46 digits. -/
private theorem cert_507 : (1154982302343889994965525813119887125281908153 : ℕ).Prime :=
  pock_helper 1154982302343889994965525813119887125281908153 3 150 [(95781885718202172715249, 1), (6704479765807211, 1), (587, 1), (383, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_503
      · exact cert_506
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_508 : (273493673 : ℕ).Prime :=
  pock_helper 273493673 3 29 [(479, 2), (149, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_509 : (7110835499 : ℕ).Prime :=
  pock_helper 7110835499 2 33 [(273493673, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_508
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_510 : (220251018746027 : ℕ).Prime :=
  pock_helper 220251018746027 2 48 [(7110835499, 1), (911, 1), (17, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_509
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 62 digits. -/
private theorem cert_511 : (22894742585238618558768944086717129905554145608409226289231791 : ℕ).Prime :=
  pock_helper 22894742585238618558768944086717129905554145608409226289231791 7 204 [(1154982302343889994965525813119887125281908153, 1), (220251018746027, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_507
      · exact cert_510
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_512 : (451762270279 : ℕ).Prime :=
  pock_helper 451762270279 11 39 [(440497, 1), (379, 1), (41, 1), (11, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_513 : (60004887147455085487 : ℕ).Prime :=
  pock_helper 60004887147455085487 3 66 [(451762270279, 1), (45833, 1), (23, 1), (7, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_512
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_514 : (10704557 : ℕ).Prime :=
  pock_helper 10704557 2 24 [(2676139, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_515 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093 2 299 [(22894742585238618558768944086717129905554145608409226289231791, 1), (60004887147455085487, 1), (10704557, 1), (17, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_511
      · exact cert_513
      · exact cert_514
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_516 : (3552152101 : ℕ).Prime :=
  pock_helper 3552152101 2 32 [(241643, 1), (7, 2), (5, 2), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_517 : (1259307407003899763 : ℕ).Prime :=
  pock_helper 1259307407003899763 2 61 [(3552152101, 1), (12491, 1), (617, 1), (23, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_516
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_518 : (17630303698054596683 : ℕ).Prime :=
  pock_helper 17630303698054596683 2 64 [(1259307407003899763, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_517
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_519 : (3669106119155315242775835456613 : ℕ).Prime :=
  pock_helper 3669106119155315242775835456613 5 102 [(17630303698054596683, 1), (3784159, 1), (4583, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_518
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_520 : (113248351080743 : ℕ).Prime :=
  pock_helper 113248351080743 5 47 [(61543, 1), (6871, 1), (373, 1), (359, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_521 : (2717960425937833 : ℕ).Prime :=
  pock_helper 2717960425937833 5 52 [(113248351080743, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_520
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_522 : (10871841703751333 : ℕ).Prime :=
  pock_helper 10871841703751333 2 54 [(2717960425937833, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_521
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_523 : (136224176548004202491 : ℕ).Prime :=
  pock_helper 136224176548004202491 2 67 [(10871841703751333, 1), (179, 1), (7, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_522
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_524 : (65351641560433344086222377 : ℕ).Prime :=
  pock_helper 65351641560433344086222377 7 86 [(136224176548004202491, 1), (2221, 1), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_523
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 58 digits. -/
private theorem cert_525 : (2877385295354769565837788842129924060314261381224638749213 : ℕ).Prime :=
  pock_helper 2877385295354769565837788842129924060314261381224638749213 2 191 [(3669106119155315242775835456613, 1), (65351641560433344086222377, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_519
      · exact cert_524
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_526 : (311133343753 : ℕ).Prime :=
  pock_helper 311133343753 5 39 [(32309, 1), (193, 1), (11, 1), (7, 1), (3, 4), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_527 : (4233477553 : ℕ).Prime :=
  pock_helper 4233477553 5 32 [(1093, 1), (137, 1), (31, 1), (19, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 84 digits. -/
private theorem cert_528 : (706331413524551373602699881195056245170458960025879982991539562328802923646986860823 : ℕ).Prime :=
  pock_helper 706331413524551373602699881195056245170458960025879982991539562328802923646986860823 3 279 [(2877385295354769565837788842129924060314261381224638749213, 1), (311133343753, 1), (4233477553, 1), (349, 1), (89, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_525
      · exact cert_526
      · exact cert_527
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_529 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419 2 299 [(706331413524551373602699881195056245170458960025879982991539562328802923646986860823, 1), (1129, 1), (19, 1), (11, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_528
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_530 : (12034594001 : ℕ).Prime :=
  pock_helper 12034594001 7 34 [(1451, 1), (29, 1), (13, 1), (11, 1), (5, 3), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_531 : (312899444027 : ℕ).Prime :=
  pock_helper 312899444027 2 39 [(12034594001, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_530
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_532 : (12595123 : ℕ).Prime :=
  pock_helper 12595123 2 24 [(10141, 1), (23, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_533 : (1057990333 : ℕ).Prime :=
  pock_helper 1057990333 5 30 [(12595123, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_532
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_534 : (11027369909708954800354643881351 : ℕ).Prime :=
  pock_helper 11027369909708954800354643881351 3 104 [(312899444027, 1), (1057990333, 1), (9743, 1), (991, 1), (23, 1), (5, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_531
      · exact cert_533
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_535 : (2685385120412324672982362877986595521 : ℕ).Prime :=
  pock_helper 2685385120412324672982362877986595521 3 122 [(11027369909708954800354643881351, 1), (761, 1), (5, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_534
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_536 : (5370770240824649345964725755973191043 : ℕ).Prime :=
  pock_helper 5370770240824649345964725755973191043 2 123 [(2685385120412324672982362877986595521, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_535
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_537 : (1267234094133083 : ℕ).Prime :=
  pock_helper 1267234094133083 2 51 [(378223, 1), (809, 1), (439, 1), (89, 1), (53, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_538 : (1203758338357956872531 : ℕ).Prime :=
  pock_helper 1203758338357956872531 23 71 [(1267234094133083, 1), (7307, 1), (13, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_537
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_539 : (16771119123133 : ℕ).Prime :=
  pock_helper 16771119123133 2 44 [(578167, 1), (2713, 1), (11, 1), (3, 5), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_540 : (22083617 : ℕ).Prime :=
  pock_helper 22083617 3 25 [(449, 1), (53, 1), (29, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_541 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591 17 299 [(5370770240824649345964725755973191043, 1), (1203758338357956872531, 1), (16771119123133, 1), (22083617, 1), (2625449, 1), (15907, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_536
      · exact cert_538
      · exact cert_539
      · exact cert_540
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_542 : (242025323723 : ℕ).Prime :=
  pock_helper 242025323723 2 38 [(53507, 1), (857, 1), (29, 1), (13, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_543 : (2013180202438700904799 : ℕ).Prime :=
  pock_helper 2013180202438700904799 11 71 [(242025323723, 1), (224291, 1), (883, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_542
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_544 : (156999499 : ℕ).Prime :=
  pock_helper 156999499 2 28 [(10853, 1), (2411, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 38 digits. -/
private theorem cert_545 : (50238507445403230551505030439079778673 : ℕ).Prime :=
  pock_helper 50238507445403230551505030439079778673 3 126 [(2013180202438700904799, 1), (156999499, 1), (26777, 1), (53, 1), (7, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_543
      · exact cert_544
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 39 digits. -/
private theorem cert_546 : (100477014890806461103010060878159557347 : ℕ).Prime :=
  pock_helper 100477014890806461103010060878159557347 2 127 [(50238507445403230551505030439079778673, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_545
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 43 digits. -/
private theorem cert_547 : (5880919681558902168359178863198678891519911 : ℕ).Prime :=
  pock_helper 5880919681558902168359178863198678891519911 17 143 [(100477014890806461103010060878159557347, 1), (1951, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_546
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_548 : (11899086257609 : ℕ).Prime :=
  pock_helper 11899086257609 3 44 [(7349, 1), (1361, 1), (1229, 1), (11, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_549 : (656843935516215991673 : ℕ).Prime :=
  pock_helper 656843935516215991673 3 70 [(11899086257609, 1), (6900151, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_548
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_550 : (1027602571 : ℕ).Prime :=
  pock_helper 1027602571 3 30 [(64997, 1), (31, 1), (17, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 73 digits. -/
private theorem cert_551 : (7938941841766738918493466332180163194506386206940387117250400242128671627 : ℕ).Prime :=
  pock_helper 7938941841766738918493466332180163194506386206940387117250400242128671627 2 243 [(5880919681558902168359178863198678891519911, 1), (656843935516215991673, 1), (1027602571, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_547
      · exact cert_549
      · exact cert_550
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 74 digits. -/
private theorem cert_552 : (47633651050600433510960797993080979167038317241642322703502401452772029763 : ℕ).Prime :=
  pock_helper 47633651050600433510960797993080979167038317241642322703502401452772029763 5 245 [(7938941841766738918493466332180163194506386206940387117250400242128671627, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_551
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_553 : (365105423671 : ℕ).Prime :=
  pock_helper 365105423671 3 39 [(44111, 1), (1117, 1), (19, 1), (13, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_554 : (419871237221651 : ℕ).Prime :=
  pock_helper 419871237221651 2 49 [(365105423671, 1), (23, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_553
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_555 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651 2 299 [(47633651050600433510960797993080979167038317241642322703502401452772029763, 1), (419871237221651, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_552
      · exact cert_554
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_556 : (2790406819 : ℕ).Prime :=
  pock_helper 2790406819 2 32 [(74209, 1), (2089, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_557 : (844714314516799947193 : ℕ).Prime :=
  pock_helper 844714314516799947193 31 70 [(2790406819, 1), (408689, 1), (4409, 1), (7, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_556
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_558 : (45614572983907197148423 : ℕ).Prime :=
  pock_helper 45614572983907197148423 3 76 [(844714314516799947193, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_557
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_559 : (142282195240429 : ℕ).Prime :=
  pock_helper 142282195240429 17 48 [(34721, 1), (15031, 1), (7573, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_560 : (3040619457363130437577 : ℕ).Prime :=
  pock_helper 3040619457363130437577 11 72 [(142282195240429, 1), (5147, 1), (173, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_559
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 49 digits. -/
private theorem cert_561 : (6902650306217171084728193212909805761734079621529 : ℕ).Prime :=
  pock_helper 6902650306217171084728193212909805761734079621529 3 163 [(45614572983907197148423, 1), (3040619457363130437577, 1), (6221, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_558
      · exact cert_560
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_562 : (124597685867 : ℕ).Prime :=
  pock_helper 124597685867 2 37 [(2723923, 1), (22871, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_563 : (3175247426634629 : ℕ).Prime :=
  pock_helper 3175247426634629 2 52 [(124597685867, 1), (277, 1), (23, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_562
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_564 : (38102969119615549 : ℕ).Prime :=
  pock_helper 38102969119615549 11 56 [(3175247426634629, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_563
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_565 : (6935507071 : ℕ).Prime :=
  pock_helper 6935507071 3 33 [(565241, 1), (409, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 81 digits. -/
private theorem cert_566 : (155309047950935806763197823001019084235723449740190964048085928878151671716881523 : ℕ).Prime :=
  pock_helper 155309047950935806763197823001019084235723449740190964048085928878151671716881523 2 267 [(6902650306217171084728193212909805761734079621529, 1), (38102969119615549, 1), (6935507071, 1), (42571, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_561
      · exact cert_564
      · exact cert_565
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_567 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747 2 299 [(155309047950935806763197823001019084235723449740190964048085928878151671716881523, 1), (43067, 1), (181, 1), (59, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_566
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_568 : (3507526212259 : ℕ).Prime :=
  pock_helper 3507526212259 3 42 [(5411897, 1), (991, 1), (109, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_569 : (10667309 : ℕ).Prime :=
  pock_helper 10667309 2 24 [(2467, 1), (47, 1), (23, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_570 : (748317318635326820621 : ℕ).Prime :=
  pock_helper 748317318635326820621 2 70 [(3507526212259, 1), (10667309, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_568
      · exact cert_569
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_571 : (290243930833 : ℕ).Prime :=
  pock_helper 290243930833 5 39 [(293261, 1), (79, 1), (29, 1), (3, 3), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_572 : (1226271900451500011 : ℕ).Prime :=
  pock_helper 1226271900451500011 2 61 [(290243930833, 1), (1033, 1), (409, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_571
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 47 digits. -/
private theorem cert_573 : (52544935615250625703566376027972985388841637197 : ℕ).Prime :=
  pock_helper 52544935615250625703566376027972985388841637197 2 156 [(748317318635326820621, 1), (1226271900451500011, 1), (26959, 1), (59, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_570
      · exact cert_572
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_574 : (11316666059 : ℕ).Prime :=
  pock_helper 11316666059 2 34 [(447193, 1), (12653, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 71 digits. -/
private theorem cert_575 : (10621128142373409499195583622724658327733520284359846116039668724274497 : ℕ).Prime :=
  pock_helper 10621128142373409499195583622724658327733520284359846116039668724274497 5 233 [(52544935615250625703566376027972985388841637197, 1), (11316666059, 1), (507301, 1), (5557, 1), (11, 1), (3, 2), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_573
      · exact cert_574
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_576 : (482874187 : ℕ).Prime :=
  pock_helper 482874187 3 29 [(14087, 1), (197, 1), (29, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_577 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161 3 299 [(10621128142373409499195583622724658327733520284359846116039668724274497, 1), (482874187, 1), (103529, 1), (149, 1), (79, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_575
      · exact cert_576
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_578 : (16937681 : ℕ).Prime :=
  pock_helper 16937681 3 25 [(1097, 1), (193, 1), (5, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_579 : (94430879944479007 : ℕ).Prime :=
  pock_helper 94430879944479007 3 57 [(16937681, 1), (446087, 1), (2083, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_578
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_580 : (1495933181 : ℕ).Prime :=
  pock_helper 1495933181 3 31 [(71713, 1), (149, 1), (7, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_581 : (10384319362547701 : ℕ).Prime :=
  pock_helper 10384319362547701 11 54 [(1495933181, 1), (857, 1), (5, 2), (3, 4), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_580
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_582 : (421359165309683 : ℕ).Prime :=
  pock_helper 421359165309683 2 49 [(40153, 1), (32381, 1), (5227, 1), (31, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_583 : (997295941 : ℕ).Prime :=
  pock_helper 997295941 2 30 [(1789, 1), (163, 1), (19, 1), (5, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_584 : (15956735057 : ℕ).Prime :=
  pock_helper 15956735057 3 34 [(997295941, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_583
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_585 : (230096119521941 : ℕ).Prime :=
  pock_helper 230096119521941 2 48 [(15956735057, 1), (103, 1), (7, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_584
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 65 digits. -/
private theorem cert_586 : (31373845400456053491709001473732135590986614506854673896933034931 : ℕ).Prime :=
  pock_helper 31373845400456053491709001473732135590986614506854673896933034931 17 215 [(94430879944479007, 1), (10384319362547701, 1), (421359165309683, 1), (230096119521941, 1), (11, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_579
      · exact cert_581
      · exact cert_582
      · exact cert_585
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 75 digits. -/
private theorem cert_587 : (287133344003252864260928865034032319529444417564748776037457268398692795961 : ℕ).Prime :=
  pock_helper 287133344003252864260928865034032319529444417564748776037457268398692795961 7 248 [(31373845400456053491709001473732135590986614506854673896933034931, 1), (1831, 1), (1811, 1), (23, 1), (5, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_586
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_588 : (250954577 : ℕ).Prime :=
  pock_helper 250954577 3 28 [(295937, 1), (53, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_589 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541 2 299 [(287133344003252864260928865034032319529444417564748776037457268398692795961, 1), (250954577, 1), (163, 1), (43, 1), (11, 1), (5, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_587
      · exact cert_588
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_590 : (502389653 : ℕ).Prime :=
  pock_helper 502389653 2 29 [(11579, 1), (10847, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_591 : (1513992919016165401019 : ℕ).Prime :=
  pock_helper 1513992919016165401019 2 71 [(502389653, 1), (238531, 1), (203773, 1), (31, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_590
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_592 : (12465797 : ℕ).Prime :=
  pock_helper 12465797 2 24 [(63601, 1), (7, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_593 : (698084633 : ℕ).Prime :=
  pock_helper 698084633 3 30 [(12465797, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_592
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_594 : (2472615770087 : ℕ).Prime :=
  pock_helper 2472615770087 7 42 [(698084633, 1), (23, 1), (11, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_593
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 49 digits. -/
private theorem cert_595 : (3449187430720993974895674156987305660643816469163 : ℕ).Prime :=
  pock_helper 3449187430720993974895674156987305660643816469163 2 162 [(1513992919016165401019, 1), (2472615770087, 1), (4784467, 1), (2348491, 1), (41, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_591
      · exact cert_594
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_596 : (8333956667 : ℕ).Prime :=
  pock_helper 8333956667 2 33 [(171403, 1), (151, 1), (23, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_597 : (7908849942063650934920749 : ℕ).Prime :=
  pock_helper 7908849942063650934920749 23 83 [(8333956667, 1), (8963, 1), (251, 2), (19, 1), (13, 1), (7, 1), (3, 5), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_596
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_598 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739 3 299 [(3449187430720993974895674156987305660643816469163, 1), (7908849942063650934920749, 1), (1228547, 1), (5231, 1), (97, 1), (11, 2), (3, 5), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_595
      · exact cert_597
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_599 : (1938780795079 : ℕ).Prime :=
  pock_helper 1938780795079 3 41 [(3733321, 1), (163, 1), (59, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_600 : (3280193627 : ℕ).Prime :=
  pock_helper 3280193627 2 32 [(1229, 1), (167, 1), (131, 1), (61, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 30 digits. -/
private theorem cert_601 : (110795687999866444754173880579 : ℕ).Prime :=
  pock_helper 110795687999866444754173880579 2 97 [(1938780795079, 1), (3280193627, 1), (83, 1), (47, 1), (29, 1), (11, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_599
      · exact cert_600
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 35 digits. -/
private theorem cert_602 : (15499430385677316689550892501957469 : ℕ).Prime :=
  pock_helper 15499430385677316689550892501957469 2 114 [(110795687999866444754173880579, 1), (853, 1), (41, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_601
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 39 digits. -/
private theorem cert_603 : (312778505182968250795137010689501724421 : ℕ).Prime :=
  pock_helper 312778505182968250795137010689501724421 3 128 [(15499430385677316689550892501957469, 1), (1009, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_602
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_604 : (27675032667859 : ℕ).Prime :=
  pock_helper 27675032667859 11 45 [(26701, 1), (6211, 1), (127, 1), (73, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_605 : (113746859 : ℕ).Prime :=
  pock_helper 113746859 2 27 [(141829, 1), (401, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 27 digits. -/
private theorem cert_606 : (451925716330607804743726123 : ℕ).Prime :=
  pock_helper 451925716330607804743726123 2 89 [(27675032667859, 1), (113746859, 1), (337, 1), (71, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_604
      · exact cert_605
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_607 : (85692346627744529504286372538769 : ℕ).Prime :=
  pock_helper 85692346627744529504286372538769 3 107 [(451925716330607804743726123, 1), (1693, 1), (7, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_606
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 77 digits. -/
private theorem cert_608 : (17952410985912354799368682030333023617030357390433258217612699495181423124703 : ℕ).Prime :=
  pock_helper 17952410985912354799368682030333023617030357390433258217612699495181423124703 5 254 [(312778505182968250795137010689501724421, 1), (85692346627744529504286372538769, 1), (293, 1), (127, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_603
      · exact cert_607
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_609 : (54809323 : ℕ).Prime :=
  pock_helper 54809323 2 26 [(1021, 1), (389, 1), (23, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_610 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839 7 299 [(17952410985912354799368682030333023617030357390433258217612699495181423124703, 1), (54809323, 1), (317, 1), (229, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_608
      · exact cert_609
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_611 : (222944156490058331 : ℕ).Prime :=
  pock_helper 222944156490058331 2 58 [(1399817, 1), (4231, 1), (257, 1), (151, 1), (97, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_612 : (10200497 : ℕ).Prime :=
  pock_helper 10200497 3 24 [(637531, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_613 : (87887482153 : ℕ).Prime :=
  pock_helper 87887482153 17 37 [(10200497, 1), (359, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_612
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_614 : (31229592833 : ℕ).Prime :=
  pock_helper 31229592833 3 35 [(4999, 1), (1061, 1), (23, 1), (2, 8)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_615 : (51270409 : ℕ).Prime :=
  pock_helper 51270409 13 26 [(127, 1), (89, 1), (7, 1), (3, 4), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 56 digits. -/
private theorem cert_616 : (72956515876193792964056335658305728277140981281451136601 : ℕ).Prime :=
  pock_helper 72956515876193792964056335658305728277140981281451136601 13 186 [(222944156490058331, 1), (87887482153, 1), (31229592833, 1), (51270409, 1), (2909, 1), (571, 1), (7, 1), (5, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_611
      · exact cert_613
      · exact cert_614
      · exact cert_615
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 65 digits. -/
private theorem cert_617 : (16128507032749352725307363163755968196418058977345819608639920939 : ℕ).Prime :=
  pock_helper 16128507032749352725307363163755968196418058977345819608639920939 3 214 [(72956515876193792964056335658305728277140981281451136601, 1), (19927, 1), (43, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_616
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_618 : (385726793 : ℕ).Prime :=
  pock_helper 385726793 3 29 [(433, 1), (191, 1), (53, 1), (11, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_619 : (78211655574940513 : ℕ).Prime :=
  pock_helper 78211655574940513 5 57 [(385726793, 1), (571, 1), (137, 1), (3, 4), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_618
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_620 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953 3 299 [(16128507032749352725307363163755968196418058977345819608639920939, 1), (78211655574940513, 1), (909113, 1), (109, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_617
      · exact cert_619
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_621 : (2451732109 : ℕ).Prime :=
  pock_helper 2451732109 11 32 [(1536173, 1), (19, 1), (7, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_622 : (24517321091 : ℕ).Prime :=
  pock_helper 24517321091 2 35 [(2451732109, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_621
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_623 : (13301377811 : ℕ).Prime :=
  pock_helper 13301377811 2 34 [(677, 1), (397, 1), (101, 1), (7, 2), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 29 digits. -/
private theorem cert_624 : (52751610625449532220312726917 : ℕ).Prime :=
  pock_helper 52751610625449532220312726917 5 96 [(24517321091, 1), (13301377811, 1), (345637, 1), (13, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_622
      · exact cert_623
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_625 : (234702103 : ℕ).Prime :=
  pock_helper 234702103 3 28 [(135353, 1), (17, 2), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 53 digits. -/
private theorem cert_626 : (14469354272753159238990461610612005872345071289912781 : ℕ).Prime :=
  pock_helper 14469354272753159238990461610612005872345071289912781 2 174 [(52751610625449532220312726917, 1), (234702103, 1), (107123, 1), (8761, 1), (113, 1), (29, 1), (19, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_624
      · exact cert_625
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 53 digits. -/
private theorem cert_627 : (28938708545506318477980923221224011744690142579825563 : ℕ).Prime :=
  pock_helper 28938708545506318477980923221224011744690142579825563 2 175 [(14469354272753159238990461610612005872345071289912781, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_626
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_628 : (11775978961 : ℕ).Prime :=
  pock_helper 11775978961 7 34 [(25253, 1), (67, 1), (29, 1), (5, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_629 : (7042035418679 : ℕ).Prime :=
  pock_helper 7042035418679 7 43 [(11775978961, 1), (23, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_628
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_630 : (16866853 : ℕ).Prime :=
  pock_helper 16866853 2 25 [(45341, 1), (31, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_631 : (39095441725331704246601051 : ℕ).Prime :=
  pock_helper 39095441725331704246601051 17 86 [(7042035418679, 1), (16866853, 1), (227, 1), (29, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_629
      · exact cert_630
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 27 digits. -/
private theorem cert_632 : (234572650351990225479606307 : ℕ).Prime :=
  pock_helper 234572650351990225479606307 2 88 [(39095441725331704246601051, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_631
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_633 : (792009763 : ℕ).Prime :=
  pock_helper 792009763 5 30 [(4258117, 1), (31, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_634 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039 3 299 [(28938708545506318477980923221224011744690142579825563, 1), (234572650351990225479606307, 1), (792009763, 1), (31, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_627
      · exact cert_632
      · exact cert_633
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_635 : (40666679681 : ℕ).Prime :=
  pock_helper 40666679681 7 36 [(337, 1), (281, 1), (61, 1), (11, 1), (5, 1), (2, 7)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_636 : (65722234366057721 : ℕ).Prime :=
  pock_helper 65722234366057721 3 56 [(40666679681, 1), (3673, 1), (11, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_635
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_637 : (10984123 : ℕ).Prime :=
  pock_helper 10984123 2 24 [(610229, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_638 : (23310564992523328982518387439893 : ℕ).Prime :=
  pock_helper 23310564992523328982518387439893 2 105 [(65722234366057721, 1), (10984123, 1), (1321, 1), (97, 1), (7, 1), (3, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_636
      · exact cert_637
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 45 digits. -/
private theorem cert_639 : (105013669757419869852725226123205617502082861 : ℕ).Prime :=
  pock_helper 105013669757419869852725226123205617502082861 2 147 [(23310564992523328982518387439893, 1), (83207, 1), (34267, 1), (79, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_638
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 48 digits. -/
private theorem cert_640 : (242581577139639899359795272344604976429811408911 : ℕ).Prime :=
  pock_helper 242581577139639899359795272344604976429811408911 11 158 [(105013669757419869852725226123205617502082861, 1), (11, 1), (7, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_639
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_641 : (1742133817 : ℕ).Prime :=
  pock_helper 1742133817 5 31 [(340793, 1), (71, 1), (3, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_642 : (6968535269 : ℕ).Prime :=
  pock_helper 6968535269 2 33 [(1742133817, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_641
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_643 : (408734203 : ℕ).Prime :=
  pock_helper 408734203 3 29 [(253243, 1), (269, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_644 : (7366400106656330968152704173 : ℕ).Prime :=
  pock_helper 7366400106656330968152704173 5 93 [(6968535269, 1), (408734203, 1), (1041169, 1), (23, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_642
      · exact cert_643
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 33 digits. -/
private theorem cert_645 : (161500955938333400145779886288853 : ℕ).Prime :=
  pock_helper 161500955938333400145779886288853 5 107 [(7366400106656330968152704173, 1), (29, 1), (7, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_644
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_646 : (3959357435784181637973939692257520149 : ℕ).Prime :=
  pock_helper 3959357435784181637973939692257520149 7 122 [(161500955938333400145779886288853, 1), (227, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_645
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_647 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241 3 299 [(242581577139639899359795272344604976429811408911, 1), (3959357435784181637973939692257520149, 1), (26029, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_640
      · exact cert_646
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_648 : (108822127027 : ℕ).Prime :=
  pock_helper 108822127027 3 37 [(314513, 1), (57667, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_649 : (23807031864678216915161 : ℕ).Prime :=
  pock_helper 23807031864678216915161 3 75 [(108822127027, 1), (1822477, 1), (3001, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_648
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_650 : (16018181 : ℕ).Prime :=
  pock_helper 16018181 2 24 [(800909, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_651 : (32036363 : ℕ).Prime :=
  pock_helper 32036363 2 25 [(16018181, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_650
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_652 : (14931700285219 : ℕ).Prime :=
  pock_helper 14931700285219 2 44 [(32036363, 1), (77681, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_651
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_653 : (86603861654270201 : ℕ).Prime :=
  pock_helper 86603861654270201 3 57 [(14931700285219, 1), (29, 1), (5, 2), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_652
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_654 : (9339993463 : ℕ).Prime :=
  pock_helper 9339993463 13 34 [(3333331, 1), (467, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 55 digits. -/
private theorem cert_655 : (4862667166503269178627968161051346822600953985461563503 : ℕ).Prime :=
  pock_helper 4862667166503269178627968161051346822600953985461563503 5 182 [(23807031864678216915161, 1), (86603861654270201, 1), (9339993463, 1), (126257, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_649
      · exact cert_653
      · exact cert_654
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_656 : (10337339 : ℕ).Prime :=
  pock_helper 10337339 2 24 [(469879, 1), (11, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_657 : (828206926003 : ℕ).Prime :=
  pock_helper 828206926003 2 40 [(10337339, 1), (4451, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_656
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 75 digits. -/
private theorem cert_658 : (632990951087576550218441577609987341766987146003149705045875451683776895053 : ℕ).Prime :=
  pock_helper 632990951087576550218441577609987341766987146003149705045875451683776895053 2 249 [(4862667166503269178627968161051346822600953985461563503, 1), (828206926003, 1), (11719, 1), (479, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_655
      · exact cert_657
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_659 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571 2 299 [(632990951087576550218441577609987341766987146003149705045875451683776895053, 1), (8618747, 1), (27481, 1), (29, 1), (23, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_658
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_660 : (374713697 : ℕ).Prime :=
  pock_helper 374713697 5 29 [(38903, 1), (43, 1), (7, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_661 : (12162998469897001351 : ℕ).Prime :=
  pock_helper 12162998469897001351 3 64 [(374713697, 1), (34897, 1), (53, 1), (13, 1), (5, 2), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_660
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 22 digits. -/
private theorem cert_662 : (1362255828628464151313 : ℕ).Prime :=
  pock_helper 1362255828628464151313 3 71 [(12162998469897001351, 1), (7, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_661
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_663 : (8835549007 : ℕ).Prime :=
  pock_helper 8835549007 41 34 [(58369, 1), (25229, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_664 : (45538419582079 : ℕ).Prime :=
  pock_helper 45538419582079 3 46 [(8835549007, 1), (859, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_663
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 40 digits. -/
private theorem cert_665 : (1564149922740866819182700967858124796579 : ℕ).Prime :=
  pock_helper 1564149922740866819182700967858124796579 2 131 [(1362255828628464151313, 1), (45538419582079, 1), (1801, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_662
      · exact cert_664
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_666 : (2125520100343 : ℕ).Prime :=
  pock_helper 2125520100343 3 41 [(3460553, 1), (34123, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_667 : (28873065043059313 : ℕ).Prime :=
  pock_helper 28873065043059313 5 55 [(2125520100343, 1), (283, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_666
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 60 digits. -/
private theorem cert_668 : (733608319101651903111917349364209992100685813385229227247389 : ℕ).Prime :=
  pock_helper 733608319101651903111917349364209992100685813385229227247389 2 199 [(1564149922740866819182700967858124796579, 1), (28873065043059313, 1), (131, 1), (31, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_665
      · exact cert_667
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_669 : (123801541 : ℕ).Prime :=
  pock_helper 123801541 2 27 [(2063359, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_670 : (136207621785848300351 : ℕ).Prime :=
  pock_helper 136207621785848300351 11 67 [(123801541, 1), (6857, 1), (1279, 1), (193, 1), (13, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_669
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_671 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721 13 299 [(733608319101651903111917349364209992100685813385229227247389, 1), (136207621785848300351, 1), (461, 1), (61, 1), (41, 1), (31, 1), (7, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_668
      · exact cert_670
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_672 : (180686711 : ℕ).Prime :=
  pock_helper 180686711 7 28 [(8369, 1), (127, 1), (17, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_673 : (1084120267 : ℕ).Prime :=
  pock_helper 1084120267 2 31 [(180686711, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_672
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_674 : (2523831981577 : ℕ).Prime :=
  pock_helper 2523831981577 5 42 [(1084120267, 1), (97, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_673
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_675 : (3923732503437934896722585503 : ℕ).Prime :=
  pock_helper 3923732503437934896722585503 17 92 [(2523831981577, 1), (432167, 1), (3067, 1), (107, 1), (29, 1), (7, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_674
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_676 : (3769344263 : ℕ).Prime :=
  pock_helper 3769344263 5 32 [(693149, 1), (2719, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_677 : (572940327977 : ℕ).Prime :=
  pock_helper 572940327977 3 40 [(3769344263, 1), (19, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_676
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_678 : (21771732463127 : ℕ).Prime :=
  pock_helper 21771732463127 5 45 [(572940327977, 1), (19, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_677
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_679 : (48863821 : ℕ).Prime :=
  pock_helper 48863821 2 26 [(42863, 1), (19, 1), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_680 : (1610668957438324017996239 : ℕ).Prime :=
  pock_helper 1610668957438324017996239 7 81 [(21771732463127, 1), (48863821, 1), (757, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_678
      · exact cert_679
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 64 digits. -/
private theorem cert_681 : (7038294985091189274108843635204547554077540708191839200002594979 : ℕ).Prime :=
  pock_helper 7038294985091189274108843635204547554077540708191839200002594979 3 213 [(3923732503437934896722585503, 1), (1610668957438324017996239, 1), (28961, 1), (4751, 1), (71, 1), (19, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_675
      · exact cert_680
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_682 : (31479206387 : ℕ).Prime :=
  pock_helper 31479206387 2 35 [(45289, 1), (1531, 1), (227, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_683 : (13236432347084098236031 : ℕ).Prime :=
  pock_helper 13236432347084098236031 19 74 [(31479206387, 1), (263941, 1), (571, 1), (31, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_682
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_684 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167 5 299 [(7038294985091189274108843635204547554077540708191839200002594979, 1), (13236432347084098236031, 1), (1789, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_681
      · exact cert_683
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_685 : (28768823 : ℕ).Prime :=
  pock_helper 28768823 5 25 [(95261, 1), (151, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_686 : (402763523 : ℕ).Prime :=
  pock_helper 402763523 2 29 [(28768823, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_685
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_687 : (5638689323 : ℕ).Prime :=
  pock_helper 5638689323 2 33 [(402763523, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_686
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_688 : (4033171858149485323 : ℕ).Prime :=
  pock_helper 4033171858149485323 2 62 [(5638689323, 1), (244787, 1), (487, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_687
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_689 : (46387923041 : ℕ).Prime :=
  pock_helper 46387923041 3 36 [(304223, 1), (953, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 35 digits. -/
private theorem cert_690 : (16113353454645652897012612804330619 : ℕ).Prime :=
  pock_helper 16113353454645652897012612804330619 2 114 [(4033171858149485323, 1), (46387923041, 1), (43063, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_688
      · exact cert_689
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_691 : (4576192381119365422751582036429895797 : ℕ).Prime :=
  pock_helper 4576192381119365422751582036429895797 2 122 [(16113353454645652897012612804330619, 1), (71, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_690
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_692 : (345267379 : ℕ).Prime :=
  pock_helper 345267379 2 29 [(8707, 1), (2203, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_693 : (191285033313581 : ℕ).Prime :=
  pock_helper 191285033313581 2 48 [(345267379, 1), (27701, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_692
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_694 : (4731360071 : ℕ).Prime :=
  pock_helper 4731360071 7 33 [(23753, 1), (19919, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_695 : (3663362741 : ℕ).Prime :=
  pock_helper 3663362741 2 32 [(112997, 1), (1621, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_696 : (30956819 : ℕ).Prime :=
  pock_helper 30956819 2 25 [(4931, 1), (73, 1), (43, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_697 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219 2 299 [(4576192381119365422751582036429895797, 1), (191285033313581, 1), (4731360071, 1), (3663362741, 1), (30956819, 1), (1909241, 1), (557573, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_691
      · exact cert_693
      · exact cert_694
      · exact cert_695
      · exact cert_696
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_698 : (951529557611071 : ℕ).Prime :=
  pock_helper 951529557611071 3 50 [(25841, 1), (6661, 1), (257, 1), (239, 1), (5, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_699 : (45142465272184430383 : ℕ).Prime :=
  pock_helper 45142465272184430383 3 66 [(951529557611071, 1), (7907, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_698
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_700 : (6871766633593002730621793 : ℕ).Prime :=
  pock_helper 6871766633593002730621793 3 83 [(45142465272184430383, 1), (71, 1), (67, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_699
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_701 : (42584560313 : ℕ).Prime :=
  pock_helper 42584560313 3 36 [(2354299, 1), (19, 1), (17, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_702 : (73213589 : ℕ).Prime :=
  pock_helper 73213589 2 27 [(2614771, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_703 : (146427179 : ℕ).Prime :=
  pock_helper 146427179 2 28 [(73213589, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_702
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_704 : (299305777708221457297 : ℕ).Prime :=
  pock_helper 299305777708221457297 13 69 [(42584560313, 1), (146427179, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_701
      · exact cert_703
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_705 : (6213907913 : ℕ).Prime :=
  pock_helper 6213907913 3 33 [(53899, 1), (14411, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_706 : (37283447479 : ℕ).Prime :=
  pock_helper 37283447479 3 36 [(6213907913, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_705
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_707 : (257556785377223992213 : ℕ).Prime :=
  pock_helper 257556785377223992213 2 68 [(37283447479, 1), (12569, 1), (727, 1), (7, 1), (3, 3), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_706
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_708 : (1325436053 : ℕ).Prime :=
  pock_helper 1325436053 2 31 [(14951, 1), (599, 1), (37, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_709 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521 7 299 [(6871766633593002730621793, 1), (299305777708221457297, 1), (257556785377223992213, 1), (1325436053, 1), (36629, 1), (6949, 1), (157, 1), (11, 1), (5, 1), (3, 4), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_700
      · exact cert_704
      · exact cert_707
      · exact cert_708
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_710 : (2092467329 : ℕ).Prime :=
  pock_helper 2092467329 3 31 [(31991, 1), (73, 1), (7, 1), (2, 7)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_711 : (1862295922811 : ℕ).Prime :=
  pock_helper 1862295922811 2 41 [(2092467329, 1), (89, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_710
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 24 digits. -/
private theorem cert_712 : (146245767985201734471473 : ℕ).Prime :=
  pock_helper 146245767985201734471473 3 77 [(1862295922811, 1), (9384539, 1), (523, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_711
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_713 : (945070436021 : ℕ).Prime :=
  pock_helper 945070436021 2 40 [(597367, 1), (79103, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_714 : (4664162059 : ℕ).Prime :=
  pock_helper 4664162059 2 33 [(1235867, 1), (37, 1), (17, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 54 digits. -/
private theorem cert_715 : (502611116708176508031701956834201288749493791116306597 : ℕ).Prime :=
  pock_helper 502611116708176508031701956834201288749493791116306597 2 179 [(146245767985201734471473, 1), (945070436021, 1), (4664162059, 1), (365699, 1), (41, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_712
      · exact cert_713
      · exact cert_714
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_716 : (2634324435601 : ℕ).Prime :=
  pock_helper 2634324435601 47 42 [(495211, 1), (31, 1), (13, 1), (11, 1), (5, 2), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_717 : (15805946613607 : ℕ).Prime :=
  pock_helper 15805946613607 3 44 [(2634324435601, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_716
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_718 : (21181301 : ℕ).Prime :=
  pock_helper 21181301 2 25 [(30259, 1), (7, 1), (5, 2), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_719 : (97453457741583820275695295256043 : ℕ).Prime :=
  pock_helper 97453457741583820275695295256043 2 107 [(15805946613607, 1), (21181301, 1), (7901837, 1), (163, 1), (113, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_717
      · exact cert_718
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_720 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137 3 299 [(502611116708176508031701956834201288749493791116306597, 1), (97453457741583820275695295256043, 1), (29, 1), (11, 1), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_715
      · exact cert_719
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_721 : (414587743 : ℕ).Prime :=
  pock_helper 414587743 3 29 [(6691, 1), (449, 1), (23, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_722 : (59412081922873 : ℕ).Prime :=
  pock_helper 59412081922873 5 46 [(414587743, 1), (853, 1), (7, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_721
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_723 : (40194649904100499421 : ℕ).Prime :=
  pock_helper 40194649904100499421 2 66 [(59412081922873, 1), (33827, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_722
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_724 : (458861069 : ℕ).Prime :=
  pock_helper 458861069 2 29 [(10987, 1), (197, 1), (53, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 32 digits. -/
private theorem cert_725 : (10697380813384255535697285808421 : ℕ).Prime :=
  pock_helper 10697380813384255535697285808421 2 104 [(40194649904100499421, 1), (458861069, 1), (29, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_723
      · exact cert_724
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_726 : (1722927221 : ℕ).Prime :=
  pock_helper 1722927221 13 31 [(5443, 1), (19, 1), (17, 1), (7, 2), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_727 : (44575573061713 : ℕ).Prime :=
  pock_helper 44575573061713 5 46 [(1722927221, 1), (11, 1), (7, 2), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_726
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 45 digits. -/
private theorem cert_728 : (953683760031953443637022062659241798656170347 : ℕ).Prime :=
  pock_helper 953683760031953443637022062659241798656170347 2 150 [(10697380813384255535697285808421, 1), (44575573061713, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_725
      · exact cert_727
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 53 digits. -/
private theorem cert_729 : (35372683796165971757494457776827620672400578749031261 : ℕ).Prime :=
  pock_helper 35372683796165971757494457776827620672400578749031261 2 175 [(953683760031953443637022062659241798656170347, 1), (1854529, 1), (5, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_728
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_730 : (2095965547883 : ℕ).Prime :=
  pock_helper 2095965547883 2 41 [(416503, 1), (3461, 1), (727, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 17 digits. -/
private theorem cert_731 : (17291715770034751 : ℕ).Prime :=
  pock_helper 17291715770034751 23 54 [(2095965547883, 1), (11, 1), (5, 3), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_730
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 19 digits. -/
private theorem cert_732 : (9510443673519113051 : ℕ).Prime :=
  pock_helper 9510443673519113051 11 64 [(17291715770034751, 1), (11, 1), (5, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_731
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 20 digits. -/
private theorem cert_733 : (19020887347038226103 : ℕ).Prime :=
  pock_helper 19020887347038226103 5 65 [(9510443673519113051, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_732
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_734 : (109169849 : ℕ).Prime :=
  pock_helper 109169849 3 27 [(919, 1), (479, 1), (31, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_735 : (218339699 : ℕ).Prime :=
  pock_helper 218339699 2 28 [(109169849, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_734
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_736 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151 19 299 [(35372683796165971757494457776827620672400578749031261, 1), (19020887347038226103, 1), (218339699, 1), (84509, 1), (179, 1), (5, 2), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_729
      · exact cert_733
      · exact cert_735
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_737 : (191250847 : ℕ).Prime :=
  pock_helper 191250847 7 28 [(559213, 1), (19, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_738 : (412818817755914888561 : ℕ).Prime :=
  pock_helper 412818817755914888561 23 69 [(191250847, 1), (1683503, 1), (47, 1), (31, 1), (11, 1), (5, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_737
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_739 : (1245634339 : ℕ).Prime :=
  pock_helper 1245634339 2 31 [(5641, 1), (149, 1), (19, 1), (13, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_740 : (916054440512669 : ℕ).Prime :=
  pock_helper 916054440512669 2 50 [(1245634339, 1), (4969, 1), (37, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_739
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_741 : (243595889 : ℕ).Prime :=
  pock_helper 243595889 3 28 [(214433, 1), (71, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_742 : (487191779 : ℕ).Prime :=
  pock_helper 487191779 2 29 [(243595889, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_741
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_743 : (525372998720231 : ℕ).Prime :=
  pock_helper 525372998720231 7 49 [(487191779, 1), (107837, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_742
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_744 : (216508183 : ℕ).Prime :=
  pock_helper 216508183 5 28 [(76289, 1), (43, 1), (11, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_745 : (3177474093709 : ℕ).Prime :=
  pock_helper 3177474093709 7 42 [(216508183, 1), (1223, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_744
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 70 digits. -/
private theorem cert_746 : (9312212619263090917897138723002602408981303378170047237550347786432331 : ℕ).Prime :=
  pock_helper 9312212619263090917897138723002602408981303378170047237550347786432331 2 233 [(412818817755914888561, 1), (916054440512669, 1), (525372998720231, 1), (3177474093709, 1), (3697, 1), (19, 1), (7, 1), (5, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_738
      · exact cert_740
      · exact cert_743
      · exact cert_745
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 73 digits. -/
private theorem cert_747 : (3240649991503555639428204275604905638325493575603176438667521029678451189 : ℕ).Prime :=
  pock_helper 3240649991503555639428204275604905638325493575603176438667521029678451189 2 241 [(9312212619263090917897138723002602408981303378170047237550347786432331, 1), (29, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_746
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_748 : (75454081 : ℕ).Prime :=
  pock_helper 75454081 11 27 [(3023, 1), (13, 1), (5, 1), (3, 1), (2, 7)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_749 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187 3 299 [(3240649991503555639428204275604905638325493575603176438667521029678451189, 1), (75454081, 1), (30097, 1), (7549, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_747
      · exact cert_748
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_750 : (215400961 : ℕ).Prime :=
  pock_helper 215400961 7 28 [(9349, 1), (5, 1), (3, 2), (2, 9)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_751 : (114079279 : ℕ).Prime :=
  pock_helper 114079279 3 27 [(78893, 1), (241, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_752 : (28329326463708373030007 : ℕ).Prime :=
  pock_helper 28329326463708373030007 5 75 [(215400961, 1), (114079279, 1), (2081, 1), (277, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_750
      · exact cert_751
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_753 : (14957884372838020959843697 : ℕ).Prime :=
  pock_helper 14957884372838020959843697 5 84 [(28329326463708373030007, 1), (11, 1), (3, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_752
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 36 digits. -/
private theorem cert_754 : (108933064718755665533009062543512967 : ℕ).Prime :=
  pock_helper 108933064718755665533009062543512967 7 117 [(14957884372838020959843697, 1), (7633807, 1), (53, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_753
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_755 : (697205147 : ℕ).Prime :=
  pock_helper 697205147 5 30 [(337, 1), (103, 1), (83, 1), (11, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_756 : (5577641177 : ℕ).Prime :=
  pock_helper 5577641177 3 33 [(697205147, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_755
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_757 : (24590825361407890472118479 : ℕ).Prime :=
  pock_helper 24590825361407890472118479 19 85 [(5577641177, 1), (57457, 1), (34757, 1), (109, 1), (41, 1), (19, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_756
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 34 digits. -/
private theorem cert_758 : (1824753539972745296906105548490393 : ℕ).Prime :=
  pock_helper 1824753539972745296906105548490393 3 111 [(24590825361407890472118479, 1), (1325083, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_757
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_759 : (13833119 : ℕ).Prime :=
  pock_helper 13833119 11 24 [(1201, 1), (443, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_760 : (193663667 : ℕ).Prime :=
  pock_helper 193663667 2 28 [(13833119, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_759
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_761 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251 17 299 [(108933064718755665533009062543512967, 1), (1824753539972745296906105548490393, 1), (193663667, 1), (1478251, 1), (5407, 1), (13, 1), (5, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_754
      · exact cert_758
      · exact cert_760
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_762 : (338452553 : ℕ).Prime :=
  pock_helper 338452553 3 29 [(164617, 1), (257, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_763 : (20813983 : ℕ).Prime :=
  pock_helper 20813983 3 25 [(495571, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_764 : (43945623026920103814553 : ℕ).Prime :=
  pock_helper 43945623026920103814553 5 76 [(338452553, 1), (20813983, 1), (8963, 1), (29, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_762
      · exact cert_763
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_765 : (1981508142283827480998194771 : ℕ).Prime :=
  pock_helper 1981508142283827480998194771 2 91 [(43945623026920103814553, 1), (167, 1), (5, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_764
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_766 : (94106167 : ℕ).Prime :=
  pock_helper 94106167 5 27 [(4157, 1), (11, 1), (7, 3), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_767 : (65309679899 : ℕ).Prime :=
  pock_helper 65309679899 2 36 [(94106167, 1), (347, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_766
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_768 : (130619359799 : ℕ).Prime :=
  pock_helper 130619359799 11 37 [(65309679899, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_767
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_769 : (1567432317589 : ℕ).Prime :=
  pock_helper 1567432317589 2 41 [(130619359799, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_768
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_770 : (62697292703561 : ℕ).Prime :=
  pock_helper 62697292703561 3 46 [(1567432317589, 1), (5, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_769
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 25 digits. -/
private theorem cert_771 : (1287753136009443753814303 : ℕ).Prime :=
  pock_helper 1287753136009443753814303 3 81 [(62697292703561, 1), (315881, 1), (10837, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_770
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 56 digits. -/
private theorem cert_772 : (98888323088149046221501139805879066026526921639110942203 : ℕ).Prime :=
  pock_helper 98888323088149046221501139805879066026526921639110942203 2 187 [(1981508142283827480998194771, 1), (1287753136009443753814303, 1), (2153, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_765
      · exact cert_771
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_773 : (20246808290977 : ℕ).Prime :=
  pock_helper 20246808290977 13 45 [(470593, 1), (79, 1), (61, 1), (31, 1), (3, 2), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_774 : (37482791 : ℕ).Prime :=
  pock_helper 37482791 13 26 [(7603, 1), (29, 1), (17, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_775 : (18863753 : ℕ).Prime :=
  pock_helper 18863753 3 25 [(2357969, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 88 digits. -/
private theorem cert_776 : (2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091 : ℕ).Prime :=
  pock_helper 2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091 2 291 [(98888323088149046221501139805879066026526921639110942203, 1), (20246808290977, 1), (37482791, 1), (18863753, 1), (193, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_772
      · exact cert_773
      · exact cert_774
      · exact cert_775
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_777 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307 2 299 [(2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091, 1), (61, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_776
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_778 : (1155716269053257 : ℕ).Prime :=
  pock_helper 1155716269053257 3 51 [(4398949, 1), (395671, 1), (83, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_779 : (5440143870742166955326084591 : ℕ).Prime :=
  pock_helper 5440143870742166955326084591 7 93 [(1155716269053257, 1), (6386143, 1), (73709, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_778
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_780 : (36432751309 : ℕ).Prime :=
  pock_helper 36432751309 2 36 [(550111, 1), (5519, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_781 : (13052601752489221206953 : ℕ).Prime :=
  pock_helper 13052601752489221206953 3 74 [(36432751309, 1), (6121, 1), (743, 1), (229, 1), (43, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_780
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_782 : (191509382975357539 : ℕ).Prime :=
  pock_helper 191509382975357539 71 58 [(999959, 1), (19259, 1), (467, 1), (13, 2), (7, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_783 : (902160289 : ℕ).Prime :=
  pock_helper 902160289 11 30 [(1044167, 1), (3, 3), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_784 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331 23 299 [(5440143870742166955326084591, 1), (13052601752489221206953, 1), (191509382975357539, 1), (902160289, 1), (111053, 1), (18493, 1), (7, 2), (5, 1), (3, 4), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_779
      · exact cert_781
      · exact cert_782
      · exact cert_783
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_785 : (12909593 : ℕ).Prime :=
  pock_helper 12909593 3 24 [(4397, 1), (367, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_786 : (24477388722767 : ℕ).Prime :=
  pock_helper 24477388722767 7 45 [(12909593, 1), (135433, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_785
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_787 : (33324234421 : ℕ).Prime :=
  pock_helper 33324234421 2 35 [(1327, 1), (149, 1), (53, 2), (5, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 28 digits. -/
private theorem cert_788 : (9514210957160511212466547249 : ℕ).Prime :=
  pock_helper 9514210957160511212466547249 7 93 [(24477388722767, 1), (33324234421, 1), (3, 6), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_786
      · exact cert_787
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_789 : (51086952937 : ℕ).Prime :=
  pock_helper 51086952937 5 36 [(50077, 1), (4723, 1), (3, 3), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_790 : (17261227208636271758719 : ℕ).Prime :=
  pock_helper 17261227208636271758719 3 74 [(51086952937, 1), (15137, 1), (1447, 1), (857, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_789
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 16 digits. -/
private theorem cert_791 : (1860868258313677 : ℕ).Prime :=
  pock_helper 1860868258313677 2 51 [(634709, 1), (7057, 1), (389, 1), (89, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_792 : (145147724148466807 : ℕ).Prime :=
  pock_helper 145147724148466807 5 58 [(1860868258313677, 1), (13, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_791
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_793 : (5320918487 : ℕ).Prime :=
  pock_helper 5320918487 11 33 [(8897857, 1), (23, 1), (13, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 14 digits. -/
private theorem cert_794 : (71800474063579 : ℕ).Prime :=
  pock_helper 71800474063579 7 47 [(5320918487, 1), (173, 1), (13, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_793
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_795 : (499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769 : ℕ).Prime :=
  pock_helper 499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769 3 298 [(9514210957160511212466547249, 1), (17261227208636271758719, 1), (145147724148466807, 1), (71800474063579, 1), (2809019, 1), (13, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_788
      · exact cert_790
      · exact cert_792
      · exact cert_794
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_796 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539 2 299 [(499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_795
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_797 : (56971643 : ℕ).Prime :=
  pock_helper 56971643 2 26 [(313031, 1), (13, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 11 digits. -/
private theorem cert_798 : (92635891519 : ℕ).Prime :=
  pock_helper 92635891519 13 37 [(56971643, 1), (271, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_797
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 23 digits. -/
private theorem cert_799 : (27551705196575769604487 : ℕ).Prime :=
  pock_helper 27551705196575769604487 5 75 [(92635891519, 1), (7136123, 1), (229, 1), (13, 1), (7, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_798
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_800 : (19828649 : ℕ).Prime :=
  pock_helper 19828649 3 25 [(883, 1), (401, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_801 : (2185252366777507749568966192253 : ℕ).Prime :=
  pock_helper 2185252366777507749568966192253 2 101 [(27551705196575769604487, 1), (19828649, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_799
      · exact cert_800
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 37 digits. -/
private theorem cert_802 : (3915570154829806825801666726738001449 : ℕ).Prime :=
  pock_helper 3915570154829806825801666726738001449 11 122 [(2185252366777507749568966192253, 1), (5743, 1), (13, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_801
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_803 : (7027267483 : ℕ).Prime :=
  pock_helper 7027267483 2 33 [(779249, 1), (167, 1), (3, 3), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 15 digits. -/
private theorem cert_804 : (622334808294481 : ℕ).Prime :=
  pock_helper 622334808294481 53 50 [(7027267483, 1), (41, 1), (5, 1), (3, 3), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_803
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 21 digits. -/
private theorem cert_805 : (281846721989254322167 : ℕ).Prime :=
  pock_helper 281846721989254322167 3 68 [(622334808294481, 1), (263, 1), (41, 1), (7, 1), (3, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_804
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_806 : (861591053 : ℕ).Prime :=
  pock_helper 861591053 2 30 [(49711, 1), (619, 1), (7, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 31 digits. -/
private theorem cert_807 : (2914039367799838633448001262213 : ℕ).Prime :=
  pock_helper 2914039367799838633448001262213 2 102 [(281846721989254322167, 1), (861591053, 1), (3, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cert_805
      · exact cert_806
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_808 : (12334241 : ℕ).Prime :=
  pock_helper 12334241 3 24 [(607, 1), (127, 1), (5, 1), (2, 5)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_809 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907 2 299 [(3915570154829806825801666726738001449, 1), (2914039367799838633448001262213, 1), (12334241, 1), (949153, 1), (374347, 1), (101, 1), (11, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_802
      · exact cert_807
      · exact cert_808
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_810 : (9345527687 : ℕ).Prime :=
  pock_helper 9345527687 5 34 [(294793, 1), (131, 1), (11, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 13 digits. -/
private theorem cert_811 : (5383023947713 : ℕ).Prime :=
  pock_helper 5383023947713 5 43 [(9345527687, 1), (3, 2), (2, 6)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_810
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_812 : (1657267373 : ℕ).Prime :=
  pock_helper 1657267373 2 31 [(308501, 1), (79, 1), (17, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 41 digits. -/
private theorem cert_813 : (65730830630574893677578879383078345920777 : ℕ).Prime :=
  pock_helper 65730830630574893677578879383078345920777 53 136 [(5383023947713, 1), (1657267373, 1), (811627, 1), (8447, 1), (883, 1), (83, 1), (47, 1), (13, 1), (3, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_811
      · exact cert_812
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_814 : (49767413 : ℕ).Prime :=
  pock_helper 49767413 2 26 [(116279, 1), (107, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 18 digits. -/
private theorem cert_815 : (946812652780551077 : ℕ).Prime :=
  pock_helper 946812652780551077 2 60 [(49767413, 1), (31321, 1), (11681, 1), (13, 1), (2, 2)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact cert_814
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 26 digits. -/
private theorem cert_816 : (78666368577342976408244729 : ℕ).Prime :=
  pock_helper 78666368577342976408244729 17 87 [(946812652780551077, 1), (4651, 1), (29, 1), (11, 1), (7, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_815
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 9 digits. -/
private theorem cert_817 : (300345371 : ℕ).Prime :=
  pock_helper 300345371 2 29 [(2310349, 1), (13, 1), (5, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 10 digits. -/
private theorem cert_818 : (2402762969 : ℕ).Prime :=
  pock_helper 2402762969 3 32 [(300345371, 1), (2, 3)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact cert_817
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 12 digits. -/
private theorem cert_819 : (192221037521 : ℕ).Prime :=
  pock_helper 192221037521 3 38 [(2402762969, 1), (5, 1), (2, 4)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact cert_818
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 8 digits. -/
private theorem cert_820 : (80320879 : ℕ).Prime :=
  pock_helper 80320879 13 27 [(5557, 1), (73, 1), (11, 1), (3, 2), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- Pocklington certificate: 90 digits. -/
private theorem cert_821 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923 : ℕ).Prime :=
  pock_helper 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923 2 299 [(65730830630574893677578879383078345920777, 1), (78666368577342976408244729, 1), (192221037521, 1), (80320879, 1), (6263, 1), (2, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact cert_813
      · exact cert_816
      · exact cert_819
      · exact cert_820
      · exact primeB_sound (by decide +kernel)
      · exact primeB_sound (by decide +kernel))
    (by decide +kernel)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)

/-- LEAF. First block of the candidate batch: every candidate whose offset
10 ^ 90 - q is at least 60000, and every prime divisor of such a candidate,
with a residue witness below 9. This is the congruence step for 32 of the 64
candidates only, so it is strictly less than the whole statement. The closure
route is the finite primality phase: each candidate of this block is prime,
so a prime divisor p of q is q itself and the witness i = 1 works without any
residue computation. -/
theorem leaf_block_one :
    ∀ q ∈ qs.take 64, 60000 ≤ 10 ^ 90 - q → ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq h1 p hp hpd
  have hmem : (qs.take 64).all (fun q => decide (60000 ≤ 10 ^ 90 - q →
      q = 10 ^ 90 - 65981 ∨
      q = 10 ^ 90 - 65867 ∨
      q = 10 ^ 90 - 65799 ∨
      q = 10 ^ 90 - 65631 ∨
      q = 10 ^ 90 - 65237 ∨
      q = 10 ^ 90 - 64931 ∨
      q = 10 ^ 90 - 64907 ∨
      q = 10 ^ 90 - 64581 ∨
      q = 10 ^ 90 - 64409 ∨
      q = 10 ^ 90 - 64349 ∨
      q = 10 ^ 90 - 64253 ∨
      q = 10 ^ 90 - 63839 ∨
      q = 10 ^ 90 - 63459 ∨
      q = 10 ^ 90 - 63261 ∨
      q = 10 ^ 90 - 63161 ∨
      q = 10 ^ 90 - 63047 ∨
      q = 10 ^ 90 - 62961 ∨
      q = 10 ^ 90 - 62759 ∨
      q = 10 ^ 90 - 62429 ∨
      q = 10 ^ 90 - 62279 ∨
      q = 10 ^ 90 - 61833 ∨
      q = 10 ^ 90 - 61781 ∨
      q = 10 ^ 90 - 61479 ∨
      q = 10 ^ 90 - 60863 ∨
      q = 10 ^ 90 - 60849 ∨
      q = 10 ^ 90 - 60813 ∨
      q = 10 ^ 90 - 60749 ∨
      q = 10 ^ 90 - 60693 ∨
      q = 10 ^ 90 - 60669 ∨
      q = 10 ^ 90 - 60461 ∨
      q = 10 ^ 90 - 60093 ∨
      q = 10 ^ 90 - 60077)) = true :=
    by decide +kernel
  have hcase := of_decide_eq_true (List.all_eq_true.mp hmem q hq) h1
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hpq : p = 10 ^ 90 - 65981 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_439).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 65867 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_453).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 65799 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_468).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 65631 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_479).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 65237 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_491).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 64931 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_502).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 64907 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_515).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 64581 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_529).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 64409 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_541).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 64349 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_555).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 64253 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_567).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 63839 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_577).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 63459 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_589).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 63261 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_598).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 63161 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_610).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 63047 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_620).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 62961 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_634).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 62759 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_647).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 62429 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_659).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 62279 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_671).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 61833 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_684).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 61781 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_697).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 61479 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_709).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60863 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_720).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60849 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_736).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60813 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_749).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60749 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_761).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60693 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_777).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60669 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_784).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60461 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_796).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60093 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_809).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 60077 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_821).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩

/-- LEAF. Second block of the candidate batch: every candidate whose offset
10 ^ 90 - q lies in the half-open range from 57000 to 60000, and every prime
divisor of it, with a residue witness below 9. This is the congruence step
for the 16 candidates of that range only. The closure route is again the
finite primality phase, after which the witness is i = 1. -/
theorem leaf_block_two :
    ∀ q ∈ qs.take 64, 57000 ≤ 10 ^ 90 - q → 10 ^ 90 - q < 60000 →
      ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq h1 h2 p hp hpd
  have hmem : (qs.take 64).all (fun q => decide (57000 ≤ 10 ^ 90 - q →
      10 ^ 90 - q < 60000 →
      q = 10 ^ 90 - 59871 ∨
      q = 10 ^ 90 - 59771 ∨
      q = 10 ^ 90 - 59513 ∨
      q = 10 ^ 90 - 58889 ∨
      q = 10 ^ 90 - 58827 ∨
      q = 10 ^ 90 - 58809 ∨
      q = 10 ^ 90 - 58799 ∨
      q = 10 ^ 90 - 58701 ∨
      q = 10 ^ 90 - 58637 ∨
      q = 10 ^ 90 - 58247 ∨
      q = 10 ^ 90 - 57699 ∨
      q = 10 ^ 90 - 57579 ∨
      q = 10 ^ 90 - 57563 ∨
      q = 10 ^ 90 - 57299 ∨
      q = 10 ^ 90 - 57269 ∨
      q = 10 ^ 90 - 57231)) = true :=
    by decide +kernel
  have hcase := of_decide_eq_true (List.all_eq_true.mp hmem q hq) h1 h2
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hpq : p = 10 ^ 90 - 59871 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_226).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 59771 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_240).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 59513 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_253).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58889 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_269).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58827 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_282).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58809 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_293).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58799 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_303).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58701 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_317).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58637 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_331).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 58247 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_342).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 57699 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_359).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 57579 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_373).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 57563 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_388).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 57299 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_403).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 57269 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_414).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 57231 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_426).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩

/-- LEAF. Third block of the candidate batch: every candidate whose offset
10 ^ 90 - q lies in the half-open range from 55000 to 57000, and every prime
divisor of it, with a residue witness below 9. This is the congruence step
for the 11 candidates of that range only. The closure route is again the
finite primality phase, after which the witness is i = 1. -/
theorem leaf_block_three :
    ∀ q ∈ qs.take 64, 55000 ≤ 10 ^ 90 - q → 10 ^ 90 - q < 57000 →
      ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq h1 h2 p hp hpd
  have hmem : (qs.take 64).all (fun q => decide (55000 ≤ 10 ^ 90 - q →
      10 ^ 90 - q < 57000 →
      q = 10 ^ 90 - 56817 ∨
      q = 10 ^ 90 - 56699 ∨
      q = 10 ^ 90 - 56597 ∨
      q = 10 ^ 90 - 56073 ∨
      q = 10 ^ 90 - 56033 ∨
      q = 10 ^ 90 - 55911 ∨
      q = 10 ^ 90 - 55487 ∨
      q = 10 ^ 90 - 55389 ∨
      q = 10 ^ 90 - 55377 ∨
      q = 10 ^ 90 - 55313 ∨
      q = 10 ^ 90 - 55149)) = true :=
    by decide +kernel
  have hcase := of_decide_eq_true (List.all_eq_true.mp hmem q hq) h1 h2
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hpq : p = 10 ^ 90 - 56817 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_81).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 56699 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_97).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 56597 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_111).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 56073 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_127).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 56033 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_140).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 55911 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_151).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 55487 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_167).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 55389 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_181).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 55377 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_191).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 55313 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_199).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 55149 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_215).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩

/-- LEAF. Fourth block of the candidate batch: every candidate whose offset
10 ^ 90 - q is below 55000, and every prime divisor of it, with a residue
witness below 9. This is the congruence step for the last 5 candidates of the
batch only, the smallest offset range of the four blocks. The closure route
is again the finite primality phase, after which the witness is i = 1. -/
theorem leaf_block_four :
    ∀ q ∈ qs.take 64, 10 ^ 90 - q < 55000 → ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq h1 p hp hpd
  have hmem : (qs.take 64).all (fun q => decide (10 ^ 90 - q < 55000 →
      q = 10 ^ 90 - 54423 ∨
      q = 10 ^ 90 - 53673 ∨
      q = 10 ^ 90 - 53669 ∨
      q = 10 ^ 90 - 53583 ∨
      q = 10 ^ 90 - 53279)) = true :=
    by decide +kernel
  have hcase := of_decide_eq_true (List.all_eq_true.mp hmem q hq) h1
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · have hpq : p = 10 ^ 90 - 54423 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_10).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 53673 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_25).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 53669 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_39).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 53583 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_55).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩
  · have hpq : p = 10 ^ 90 - 53279 :=
      (Nat.prime_dvd_prime_iff_eq hp cert_69).mp hpd
    rw [hpq]
    exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩

/-- The exact component3 statement, proved from the four block leaves. The
four offset ranges partition the batch, so an arbitrary member q of the batch
falls into exactly one block and the corresponding block leaf supplies the
witness. No residue is computed here and the component3 statement itself is
not used. -/
theorem component3_split :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  by_cases h1 : 60000 ≤ 10 ^ 90 - q
  · exact leaf_block_one q hq h1 p hp hd
  · by_cases h2 : 57000 ≤ 10 ^ 90 - q
    · exact leaf_block_two q hq h2 (Nat.not_le.mp h1) p hp hd
    · by_cases h3 : 55000 ≤ 10 ^ 90 - q
      · exact leaf_block_three q hq h3 (Nat.not_le.mp h2) p hp hd
      · exact leaf_block_four q hq (Nat.not_le.mp h3) p hp hd

#print axioms leaf_block_one
#print axioms leaf_block_two
#print axioms leaf_block_three
#print axioms leaf_block_four
#print axioms component3_split

end LeanLab.DtRS1998.Decomp445a
