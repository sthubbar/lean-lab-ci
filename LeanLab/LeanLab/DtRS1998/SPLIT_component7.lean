/-
Split of the exponent-720 primary component of Decomp445a, `component7`.

The target is a congruence obligation on the first 64 candidates of the fixed
row 10^90 candidate list: for every candidate q in that block and every prime
p dividing q, the 720th power of p is a power of the 720th power of q modulo
the fixed modulus, with an exponent i below 7.

The eight leaves below cut the block `qs.take 64` into eight consecutive windows
of eight candidates each, and `component7_split` reassembles the block from them
by splitting the list once per window. Each leaf asserts the same congruence
obligation on eight candidates, a strictly smaller finite claim than the whole
block; none of them assumes the block statement, and the assembly has no sorry
of its own. The list-splitting identity used in the assembly is proved here.

The route that closes a window, recorded so that the next worker does not
re-walk a longer one: a window closes as soon as its eight candidates are
certified prime, because a prime divisor of a prime candidate is the candidate
itself, and then the witness is i = 1 and the congruence is reflexivity. No
character value, no p-adic input and no orbit computation is needed for this one
projection.

Each window is now closed by a Lucas primality certificate for its eight
candidates, and recursively for the 822 primes those certificates need: the
factorisation of every prime minus one is written out, and each exponentiation
is a `ZMod` computation the kernel evaluates.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp445a

namespace LeanLab.DtRS1998.Decomp445a

open Decomp372a

set_option maxRecDepth 100000

/-! ## Finite primality machinery.

`lucas_of_list` is Mathlib's Lucas criterion, with the prime factorisation of
`p - 1` supplied as a list of its prime factors; each exponentiation in it is a
`ZMod p` computation the kernel evaluates directly. -/

private lemma prime_mem_of_dvd_prod : ∀ (L : List ℕ), (∀ r ∈ L, r.Prime) →
    ∀ q : ℕ, q.Prime → q ∣ L.prod → q ∈ L
  | [], _, q, hq, h => by
    rw [List.prod_nil] at h
    exact absurd (Nat.dvd_one.mp h) hq.ne_one
  | r :: t, hL, q, hq, h => by
    rw [List.prod_cons] at h
    rcases hq.dvd_mul.mp h with h1 | h1
    · have hrp : r.Prime := hL r (by simp)
      have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq hrp).mp h1
      simp [hqr]
    · exact List.mem_cons_of_mem r
        (prime_mem_of_dvd_prod t (fun x hx => hL x (by simp [hx])) q hq h1)

private theorem lucas_of_list (p a : ℕ) (L : List ℕ) :
    (∀ r ∈ L, r.Prime) → L.prod = p - 1 →
    (a : ZMod p) ^ (p - 1) = 1 →
    (∀ r ∈ L, (a : ZMod p) ^ ((p - 1) / r) ≠ 1) → p.Prime := by
  intro hL hprod hpow hd
  refine lucas_primality p (a : ZMod p) hpow ?_
  intro q hq hqd
  exact hd q (prime_mem_of_dvd_prod L hL q hq (by rw [hprod]; exact hqd))

/-- A window of prime candidates is closed: a prime divisor of a prime candidate
is the candidate itself, so the witness is `i = 1` and the congruence is
reflexivity. -/
private lemma closes_of_prime (q : ℕ) (hq : q.Prime) :
    ∀ p : ℕ, p.Prime → p ∣ q → ∃ i : ℕ, i < 7 ∧
      p ^ 720 % 15321986788854443284662612735663611380010431225771200 =
        q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro p hp hpq
  have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  subst hpq'
  exact ⟨1, by norm_num, by rw [Nat.mul_one]⟩

/-- `10200497` is prime. -/
private theorem pr10200497 : (10200497).Prime := by
  refine lucas_of_list 10200497 3 [2, 2, 2, 2, 637531] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10337339` is prime. -/
private theorem pr10337339 : (10337339).Prime := by
  refine lucas_of_list 10337339 2 [2, 11, 469879] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `10601509` is prime. -/
private theorem pr10601509 : (10601509).Prime := by
  refine lucas_of_list 10601509 6 [2, 2, 3, 47, 18797] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10667309` is prime. -/
private theorem pr10667309 : (10667309).Prime := by
  refine lucas_of_list 10667309 2 [2, 2, 23, 47, 2467] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10704557` is prime. -/
private theorem pr10704557 : (10704557).Prime := by
  refine lucas_of_list 10704557 2 [2, 2, 2676139] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `10984123` is prime. -/
private theorem pr10984123 : (10984123).Prime := by
  refine lucas_of_list 10984123 2 [2, 3, 3, 610229] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `11052637` is prime. -/
private theorem pr11052637 : (11052637).Prime := by
  refine lucas_of_list 11052637 2 [2, 2, 3, 7, 7, 18797] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11148619` is prime. -/
private theorem pr11148619 : (11148619).Prime := by
  refine lucas_of_list 11148619 2 [2, 3, 13, 37, 3863] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11226959` is prime. -/
private theorem pr11226959 : (11226959).Prime := by
  refine lucas_of_list 11226959 7 [2, 101, 55579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `11283761` is prime. -/
private theorem pr11283761 : (11283761).Prime := by
  refine lucas_of_list 11283761 3 [2, 2, 2, 2, 5, 47, 3001] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12334241` is prime. -/
private theorem pr12334241 : (12334241).Prime := by
  refine lucas_of_list 12334241 3 [2, 2, 2, 2, 2, 5, 127, 607] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12465797` is prime. -/
private theorem pr12465797 : (12465797).Prime := by
  refine lucas_of_list 12465797 2 [2, 2, 7, 7, 63601] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12595123` is prime. -/
private theorem pr12595123 : (12595123).Prime := by
  refine lucas_of_list 12595123 2 [2, 3, 3, 3, 23, 10141] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12603847` is prime. -/
private theorem pr12603847 : (12603847).Prime := by
  refine lucas_of_list 12603847 5 [2, 3, 1327, 1583] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `12909593` is prime. -/
private theorem pr12909593 : (12909593).Prime := by
  refine lucas_of_list 12909593 3 [2, 2, 2, 367, 4397] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13644391` is prime. -/
private theorem pr13644391 : (13644391).Prime := by
  refine lucas_of_list 13644391 3 [2, 3, 5, 41, 11093] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13648559` is prime. -/
private theorem pr13648559 : (13648559).Prime := by
  refine lucas_of_list 13648559 7 [2, 7, 7, 11, 11, 1151] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13833119` is prime. -/
private theorem pr13833119 : (13833119).Prime := by
  refine lucas_of_list 13833119 11 [2, 13, 443, 1201] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `14220029` is prime. -/
private theorem pr14220029 : (14220029).Prime := by
  refine lucas_of_list 14220029 2 [2, 2, 3555007] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `14291269` is prime. -/
private theorem pr14291269 : (14291269).Prime := by
  refine lucas_of_list 14291269 2 [2, 2, 3, 19, 19, 3299] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `14738407` is prime. -/
private theorem pr14738407 : (14738407).Prime := by
  refine lucas_of_list 14738407 3 [2, 3, 2456401] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `15138241` is prime. -/
private theorem pr15138241 : (15138241).Prime := by
  refine lucas_of_list 15138241 11 [2, 2, 2, 2, 2, 2, 3, 5, 13, 1213] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `16018181` is prime. -/
private theorem pr16018181 : (16018181).Prime := by
  refine lucas_of_list 16018181 2 [2, 2, 5, 800909] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `16291813` is prime. -/
private theorem pr16291813 : (16291813).Prime := by
  refine lucas_of_list 16291813 2 [2, 2, 3, 1357651] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `16866853` is prime. -/
private theorem pr16866853 : (16866853).Prime := by
  refine lucas_of_list 16866853 2 [2, 2, 3, 31, 45341] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `16937681` is prime. -/
private theorem pr16937681 : (16937681).Prime := by
  refine lucas_of_list 16937681 3 [2, 2, 2, 2, 5, 193, 1097] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `16994801` is prime. -/
private theorem pr16994801 : (16994801).Prime := by
  refine lucas_of_list 16994801 3 [2, 2, 2, 2, 5, 5, 42487] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `17318281` is prime. -/
private theorem pr17318281 : (17318281).Prime := by
  refine lucas_of_list 17318281 11 [2, 2, 2, 3, 5, 7, 53, 389] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `18325387` is prime. -/
private theorem pr18325387 : (18325387).Prime := by
  refine lucas_of_list 18325387 2 [2, 3, 3, 3, 19, 53, 337] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `18678731` is prime. -/
private theorem pr18678731 : (18678731).Prime := by
  refine lucas_of_list 18678731 2 [2, 5, 7, 266839] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `18863753` is prime. -/
private theorem pr18863753 : (18863753).Prime := by
  refine lucas_of_list 18863753 3 [2, 2, 2, 2357969] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `18989807` is prime. -/
private theorem pr18989807 : (18989807).Prime := by
  refine lucas_of_list 18989807 5 [2, 11, 37, 41, 569] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `19828649` is prime. -/
private theorem pr19828649 : (19828649).Prime := by
  refine lucas_of_list 19828649 3 [2, 2, 2, 7, 401, 883] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `20150267` is prime. -/
private theorem pr20150267 : (20150267).Prime := by
  refine lucas_of_list 20150267 2 [2, 947, 10639] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `20813983` is prime. -/
private theorem pr20813983 : (20813983).Prime := by
  refine lucas_of_list 20813983 3 [2, 3, 7, 495571] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `21181301` is prime. -/
private theorem pr21181301 : (21181301).Prime := by
  refine lucas_of_list 21181301 2 [2, 2, 5, 5, 7, 30259] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `21529427` is prime. -/
private theorem pr21529427 : (21529427).Prime := by
  refine lucas_of_list 21529427 2 [2, 23, 29, 16139] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `21658163` is prime. -/
private theorem pr21658163 : (21658163).Prime := by
  refine lucas_of_list 21658163 2 [2, 3251, 3331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `21724613` is prime. -/
private theorem pr21724613 : (21724613).Prime := by
  refine lucas_of_list 21724613 2 [2, 2, 7, 13, 13, 4591] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `22083617` is prime. -/
private theorem pr22083617 : (22083617).Prime := by
  refine lucas_of_list 22083617 3 [2, 2, 2, 2, 2, 29, 53, 449] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `22453919` is prime. -/
private theorem pr22453919 : (22453919).Prime := by
  refine lucas_of_list 22453919 11 [2, 11226959] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr11226959
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `24226529` is prime. -/
private theorem pr24226529 : (24226529).Prime := by
  refine lucas_of_list 24226529 3 [2, 2, 2, 2, 2, 397, 1907] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `25155511` is prime. -/
private theorem pr25155511 : (25155511).Prime := by
  refine lucas_of_list 25155511 3 [2, 3, 5, 838517] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `28705493` is prime. -/
private theorem pr28705493 : (28705493).Prime := by
  refine lucas_of_list 28705493 2 [2, 2, 1039, 6907] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `28768823` is prime. -/
private theorem pr28768823 : (28768823).Prime := by
  refine lucas_of_list 28768823 5 [2, 151, 95261] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `28801627` is prime. -/
private theorem pr28801627 : (28801627).Prime := by
  refine lucas_of_list 28801627 3 [2, 3, 7, 685753] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `28808371` is prime. -/
private theorem pr28808371 : (28808371).Prime := by
  refine lucas_of_list 28808371 2 [2, 3, 3, 5, 17, 19, 991] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `30098239` is prime. -/
private theorem pr30098239 : (30098239).Prime := by
  refine lucas_of_list 30098239 3 [2, 3, 127, 39499] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `30956819` is prime. -/
private theorem pr30956819 : (30956819).Prime := by
  refine lucas_of_list 30956819 2 [2, 43, 73, 4931] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `32036363` is prime. -/
private theorem pr32036363 : (32036363).Prime := by
  refine lucas_of_list 32036363 2 [2, 16018181] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr16018181
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `34158031` is prime. -/
private theorem pr34158031 : (34158031).Prime := by
  refine lucas_of_list 34158031 12 [2, 3, 5, 37, 30773] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `34227293` is prime. -/
private theorem pr34227293 : (34227293).Prime := by
  refine lucas_of_list 34227293 2 [2, 2, 11, 41, 18973] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `34863181` is prime. -/
private theorem pr34863181 : (34863181).Prime := by
  refine lucas_of_list 34863181 2 [2, 2, 3, 5, 11, 101, 523] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `36347681` is prime. -/
private theorem pr36347681 : (36347681).Prime := by
  refine lucas_of_list 36347681 3 [2, 2, 2, 2, 2, 5, 367, 619] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `37482791` is prime. -/
private theorem pr37482791 : (37482791).Prime := by
  refine lucas_of_list 37482791 13 [2, 5, 17, 29, 7603] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `37558613` is prime. -/
private theorem pr37558613 : (37558613).Prime := by
  refine lucas_of_list 37558613 2 [2, 2, 7, 13, 103183] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `42409307` is prime. -/
private theorem pr42409307 : (42409307).Prime := by
  refine lucas_of_list 42409307 2 [2, 1297, 16349] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `43280257` is prime. -/
private theorem pr43280257 : (43280257).Prime := by
  refine lucas_of_list 43280257 10 [2, 2, 2, 2, 2, 2, 2, 3, 41, 2749] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `43449227` is prime. -/
private theorem pr43449227 : (43449227).Prime := by
  refine lucas_of_list 43449227 2 [2, 21724613] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr21724613
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `47848291` is prime. -/
private theorem pr47848291 : (47848291).Prime := by
  refine lucas_of_list 47848291 2 [2, 3, 5, 7, 227849] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `48863821` is prime. -/
private theorem pr48863821 : (48863821).Prime := by
  refine lucas_of_list 48863821 2 [2, 2, 3, 5, 19, 42863] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `49374739` is prime. -/
private theorem pr49374739 : (49374739).Prime := by
  refine lucas_of_list 49374739 3 [2, 3, 3, 3, 7, 130621] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `49767413` is prime. -/
private theorem pr49767413 : (49767413).Prime := by
  refine lucas_of_list 49767413 2 [2, 2, 107, 116279] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `50780083` is prime. -/
private theorem pr50780083 : (50780083).Prime := by
  refine lucas_of_list 50780083 2 [2, 3, 97, 87251] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `51270409` is prime. -/
private theorem pr51270409 : (51270409).Prime := by
  refine lucas_of_list 51270409 13 [2, 2, 2, 3, 3, 3, 3, 7, 89, 127] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `51902017` is prime. -/
private theorem pr51902017 : (51902017).Prime := by
  refine lucas_of_list 51902017 5 [2, 2, 2, 2, 2, 2, 3, 270323] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `51944569` is prime. -/
private theorem pr51944569 : (51944569).Prime := by
  refine lucas_of_list 51944569 11 [2, 2, 2, 3, 13, 29, 5741] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `52141693` is prime. -/
private theorem pr52141693 : (52141693).Prime := by
  refine lucas_of_list 52141693 5 [2, 2, 3, 421, 10321] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `52181629` is prime. -/
private theorem pr52181629 : (52181629).Prime := by
  refine lucas_of_list 52181629 2 [2, 2, 3, 593, 7333] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `54809323` is prime. -/
private theorem pr54809323 : (54809323).Prime := by
  refine lucas_of_list 54809323 2 [2, 3, 23, 389, 1021] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `56971643` is prime. -/
private theorem pr56971643 : (56971643).Prime := by
  refine lucas_of_list 56971643 2 [2, 7, 13, 313031] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `57833987` is prime. -/
private theorem pr57833987 : (57833987).Prime := by
  refine lucas_of_list 57833987 2 [2, 7, 19, 217421] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `58735241` is prime. -/
private theorem pr58735241 : (58735241).Prime := by
  refine lucas_of_list 58735241 3 [2, 2, 2, 5, 307, 4783] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `59540059` is prime. -/
private theorem pr59540059 : (59540059).Prime := by
  refine lucas_of_list 59540059 3 [2, 3, 3, 3307781] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `60581077` is prime. -/
private theorem pr60581077 : (60581077).Prime := by
  refine lucas_of_list 60581077 2 [2, 2, 3, 5048423] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `67738679` is prime. -/
private theorem pr67738679 : (67738679).Prime := by
  refine lucas_of_list 67738679 7 [2, 7, 7, 149, 4639] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `70578419` is prime. -/
private theorem pr70578419 : (70578419).Prime := by
  refine lucas_of_list 70578419 2 [2, 4567, 7727] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `71580407` is prime. -/
private theorem pr71580407 : (71580407).Prime := by
  refine lucas_of_list 71580407 5 [2, 757, 47279] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `72940141` is prime. -/
private theorem pr72940141 : (72940141).Prime := by
  refine lucas_of_list 72940141 18 [2, 2, 3, 3, 5, 7, 13, 61, 73] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `73213589` is prime. -/
private theorem pr73213589 : (73213589).Prime := by
  refine lucas_of_list 73213589 2 [2, 2, 7, 2614771] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `73266769` is prime. -/
private theorem pr73266769 : (73266769).Prime := by
  refine lucas_of_list 73266769 19 [2, 2, 2, 2, 3, 3, 3, 3, 56533] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `75117227` is prime. -/
private theorem pr75117227 : (75117227).Prime := by
  refine lucas_of_list 75117227 2 [2, 37558613] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr37558613
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `75454081` is prime. -/
private theorem pr75454081 : (75454081).Prime := by
  refine lucas_of_list 75454081 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 13, 3023] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `80320879` is prime. -/
private theorem pr80320879 : (80320879).Prime := by
  refine lucas_of_list 80320879 6 [2, 3, 3, 11, 73, 5557] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `84951613` is prime. -/
private theorem pr84951613 : (84951613).Prime := by
  refine lucas_of_list 84951613 2 [2, 2, 3, 3, 3, 786589] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `87562141` is prime. -/
private theorem pr87562141 : (87562141).Prime := by
  refine lucas_of_list 87562141 11 [2, 2, 3, 5, 1459369] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `89130709` is prime. -/
private theorem pr89130709 : (89130709).Prime := by
  refine lucas_of_list 89130709 2 [2, 2, 3, 3, 691, 3583] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `91250311` is prime. -/
private theorem pr91250311 : (91250311).Prime := by
  refine lucas_of_list 91250311 6 [2, 3, 5, 607, 5011] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `94106167` is prime. -/
private theorem pr94106167 : (94106167).Prime := by
  refine lucas_of_list 94106167 5 [2, 3, 7, 7, 7, 11, 4157] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `99766057` is prime. -/
private theorem pr99766057 : (99766057).Prime := by
  refine lucas_of_list 99766057 19 [2, 2, 2, 3, 13, 319763] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `100440719` is prime. -/
private theorem pr100440719 : (100440719).Prime := by
  refine lucas_of_list 100440719 7 [2, 7, 37, 71, 2731] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `108150937` is prime. -/
private theorem pr108150937 : (108150937).Prime := by
  refine lucas_of_list 108150937 5 [2, 2, 2, 3, 4506289] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `109169849` is prime. -/
private theorem pr109169849 : (109169849).Prime := by
  refine lucas_of_list 109169849 3 [2, 2, 2, 31, 479, 919] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `113746859` is prime. -/
private theorem pr113746859 : (113746859).Prime := by
  refine lucas_of_list 113746859 2 [2, 401, 141829] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `114079279` is prime. -/
private theorem pr114079279 : (114079279).Prime := by
  refine lucas_of_list 114079279 3 [2, 3, 241, 78893] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `115483099` is prime. -/
private theorem pr115483099 : (115483099).Prime := by
  refine lucas_of_list 115483099 2 [2, 3, 2243, 8581] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `123801541` is prime. -/
private theorem pr123801541 : (123801541).Prime := by
  refine lucas_of_list 123801541 2 [2, 2, 3, 5, 2063359] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `125247679` is prime. -/
private theorem pr125247679 : (125247679).Prime := by
  refine lucas_of_list 125247679 3 [2, 3, 59, 353807] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `134399917` is prime. -/
private theorem pr134399917 : (134399917).Prime := by
  refine lucas_of_list 134399917 2 [2, 2, 3, 3, 7, 241, 2213] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `135259027` is prime. -/
private theorem pr135259027 : (135259027).Prime := by
  refine lucas_of_list 135259027 2 [2, 3, 7, 3220453] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `146427179` is prime. -/
private theorem pr146427179 : (146427179).Prime := by
  refine lucas_of_list 146427179 2 [2, 73213589] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr73213589
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `147282413` is prime. -/
private theorem pr147282413 : (147282413).Prime := by
  refine lucas_of_list 147282413 2 [2, 2, 797, 46199] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `156999499` is prime. -/
private theorem pr156999499 : (156999499).Prime := by
  refine lucas_of_list 156999499 2 [2, 3, 2411, 10853] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `160441153` is prime. -/
private theorem pr160441153 : (160441153).Prime := by
  refine lucas_of_list 160441153 5 [2, 2, 2, 2, 2, 2, 3, 73, 11447] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `160866779` is prime. -/
private theorem pr160866779 : (160866779).Prime := by
  refine lucas_of_list 160866779 2 [2, 109, 737921] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `162995029` is prime. -/
private theorem pr162995029 : (162995029).Prime := by
  refine lucas_of_list 162995029 2 [2, 2, 3, 7, 103, 18839] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `169114769` is prime. -/
private theorem pr169114769 : (169114769).Prime := by
  refine lucas_of_list 169114769 3 [2, 2, 2, 2, 23, 59, 7789] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `180686711` is prime. -/
private theorem pr180686711 : (180686711).Prime := by
  refine lucas_of_list 180686711 7 [2, 5, 17, 127, 8369] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `184124021` is prime. -/
private theorem pr184124021 : (184124021).Prime := by
  refine lucas_of_list 184124021 2 [2, 2, 5, 2731, 3371] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `191250847` is prime. -/
private theorem pr191250847 : (191250847).Prime := by
  refine lucas_of_list 191250847 7 [2, 3, 3, 19, 559213] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `193663667` is prime. -/
private theorem pr193663667 : (193663667).Prime := by
  refine lucas_of_list 193663667 2 [2, 7, 13833119] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr13833119
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `204948187` is prime. -/
private theorem pr204948187 : (204948187).Prime := by
  refine lucas_of_list 204948187 2 [2, 3, 34158031] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr34158031
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `211426697` is prime. -/
private theorem pr211426697 : (211426697).Prime := by
  refine lucas_of_list 211426697 3 [2, 2, 2, 13, 31, 65579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `212160521` is prime. -/
private theorem pr212160521 : (212160521).Prime := by
  refine lucas_of_list 212160521 3 [2, 2, 2, 5, 11, 13, 29, 1279] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `212391143` is prime. -/
private theorem pr212391143 : (212391143).Prime := by
  refine lucas_of_list 212391143 5 [2, 61, 1740911] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `214700357` is prime. -/
private theorem pr214700357 : (214700357).Prime := by
  refine lucas_of_list 214700357 2 [2, 2, 13, 1523, 2711] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `215400961` is prime. -/
private theorem pr215400961 : (215400961).Prime := by
  refine lucas_of_list 215400961 7 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 9349] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `216508183` is prime. -/
private theorem pr216508183 : (216508183).Prime := by
  refine lucas_of_list 216508183 5 [2, 3, 11, 43, 76289] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `218339699` is prime. -/
private theorem pr218339699 : (218339699).Prime := by
  refine lucas_of_list 218339699 2 [2, 109169849] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr109169849
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `229147553` is prime. -/
private theorem pr229147553 : (229147553).Prime := by
  refine lucas_of_list 229147553 3 [2, 2, 2, 2, 2, 7160861] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `234702103` is prime. -/
private theorem pr234702103 : (234702103).Prime := by
  refine lucas_of_list 234702103 3 [2, 3, 17, 17, 135353] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `240373607` is prime. -/
private theorem pr240373607 : (240373607).Prime := by
  refine lucas_of_list 240373607 5 [2, 11, 797, 13709] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `240723731` is prime. -/
private theorem pr240723731 : (240723731).Prime := by
  refine lucas_of_list 240723731 2 [2, 5, 13, 19, 97459] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `243595889` is prime. -/
private theorem pr243595889 : (243595889).Prime := by
  refine lucas_of_list 243595889 3 [2, 2, 2, 2, 71, 214433] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `248381291` is prime. -/
private theorem pr248381291 : (248381291).Prime := by
  refine lucas_of_list 248381291 2 [2, 5, 173, 143573] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `250954577` is prime. -/
private theorem pr250954577 : (250954577).Prime := by
  refine lucas_of_list 250954577 3 [2, 2, 2, 2, 53, 295937] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `254522831` is prime. -/
private theorem pr254522831 : (254522831).Prime := by
  refine lucas_of_list 254522831 19 [2, 5, 23, 1106621] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `257027429` is prime. -/
private theorem pr257027429 : (257027429).Prime := by
  refine lucas_of_list 257027429 2 [2, 2, 7, 83, 110597] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `259960231` is prime. -/
private theorem pr259960231 : (259960231).Prime := by
  refine lucas_of_list 259960231 6 [2, 3, 3, 5, 53, 54499] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `262375903` is prime. -/
private theorem pr262375903 : (262375903).Prime := by
  refine lucas_of_list 262375903 6 [2, 3, 3, 3, 19, 47, 5441] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `273493673` is prime. -/
private theorem pr273493673 : (273493673).Prime := by
  refine lucas_of_list 273493673 3 [2, 2, 2, 149, 479, 479] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `294564827` is prime. -/
private theorem pr294564827 : (294564827).Prime := by
  refine lucas_of_list 294564827 2 [2, 147282413] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr147282413
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `299016581` is prime. -/
private theorem pr299016581 : (299016581).Prime := by
  refine lucas_of_list 299016581 2 [2, 2, 5, 79, 189251] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `300345371` is prime. -/
private theorem pr300345371 : (300345371).Prime := by
  refine lucas_of_list 300345371 2 [2, 5, 13, 2310349] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `336271517` is prime. -/
private theorem pr336271517 : (336271517).Prime := by
  refine lucas_of_list 336271517 2 [2, 2, 7, 7, 103, 16657] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `338452553` is prime. -/
private theorem pr338452553 : (338452553).Prime := by
  refine lucas_of_list 338452553 3 [2, 2, 2, 257, 164617] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `345267379` is prime. -/
private theorem pr345267379 : (345267379).Prime := by
  refine lucas_of_list 345267379 2 [2, 3, 3, 2203, 8707] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `347593817` is prime. -/
private theorem pr347593817 : (347593817).Prime := by
  refine lucas_of_list 347593817 3 [2, 2, 2, 43449227] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr43449227
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `348513479` is prime. -/
private theorem pr348513479 : (348513479).Prime := by
  refine lucas_of_list 348513479 13 [2, 53, 103, 137, 233] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `368248043` is prime. -/
private theorem pr368248043 : (368248043).Prime := by
  refine lucas_of_list 368248043 2 [2, 184124021] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr184124021
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `372626521` is prime. -/
private theorem pr372626521 : (372626521).Prime := by
  refine lucas_of_list 372626521 13 [2, 2, 2, 3, 5, 7, 443603] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `374713697` is prime. -/
private theorem pr374713697 : (374713697).Prime := by
  refine lucas_of_list 374713697 5 [2, 2, 2, 2, 2, 7, 43, 38903] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `385726793` is prime. -/
private theorem pr385726793 : (385726793).Prime := by
  refine lucas_of_list 385726793 3 [2, 2, 2, 11, 53, 191, 433] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `402585761` is prime. -/
private theorem pr402585761 : (402585761).Prime := by
  refine lucas_of_list 402585761 3 [2, 2, 2, 2, 2, 5, 839, 2999] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `402763523` is prime. -/
private theorem pr402763523 : (402763523).Prime := by
  refine lucas_of_list 402763523 2 [2, 7, 28768823] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr28768823
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `408734203` is prime. -/
private theorem pr408734203 : (408734203).Prime := by
  refine lucas_of_list 408734203 3 [2, 3, 269, 253243] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `414587743` is prime. -/
private theorem pr414587743 : (414587743).Prime := by
  refine lucas_of_list 414587743 3 [2, 3, 23, 449, 6691] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `416115499` is prime. -/
private theorem pr416115499 : (416115499).Prime := by
  refine lucas_of_list 416115499 3 [2, 3, 719, 96457] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `449651011` is prime. -/
private theorem pr449651011 : (449651011).Prime := by
  refine lucas_of_list 449651011 3 [2, 3, 5, 37, 405091] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `458861069` is prime. -/
private theorem pr458861069 : (458861069).Prime := by
  refine lucas_of_list 458861069 2 [2, 2, 53, 197, 10987] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `460826033` is prime. -/
private theorem pr460826033 : (460826033).Prime := by
  refine lucas_of_list 460826033 3 [2, 2, 2, 2, 28801627] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr28801627
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `482874187` is prime. -/
private theorem pr482874187 : (482874187).Prime := by
  refine lucas_of_list 482874187 3 [2, 3, 29, 197, 14087] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `487191779` is prime. -/
private theorem pr487191779 : (487191779).Prime := by
  refine lucas_of_list 487191779 2 [2, 243595889] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr243595889
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `491198077` is prime. -/
private theorem pr491198077 : (491198077).Prime := by
  refine lucas_of_list 491198077 2 [2, 2, 3, 3, 13644391] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr13644391
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `496762583` is prime. -/
private theorem pr496762583 : (496762583).Prime := by
  refine lucas_of_list 496762583 5 [2, 248381291] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr248381291
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `499843579` is prime. -/
private theorem pr499843579 : (499843579).Prime := by
  refine lucas_of_list 499843579 2 [2, 3, 13, 2243, 2857] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `502389653` is prime. -/
private theorem pr502389653 : (502389653).Prime := by
  refine lucas_of_list 502389653 2 [2, 2, 10847, 11579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `532542343` is prime. -/
private theorem pr532542343 : (532542343).Prime := by
  refine lucas_of_list 532542343 5 [2, 3, 103, 861719] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `598596343` is prime. -/
private theorem pr598596343 : (598596343).Prime := by
  refine lucas_of_list 598596343 5 [2, 3, 99766057] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr99766057
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `689490569` is prime. -/
private theorem pr689490569 : (689490569).Prime := by
  refine lucas_of_list 689490569 3 [2, 2, 2, 13, 53, 67, 1867] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `697026959` is prime. -/
private theorem pr697026959 : (697026959).Prime := by
  refine lucas_of_list 697026959 13 [2, 348513479] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr348513479
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `697205147` is prime. -/
private theorem pr697205147 : (697205147).Prime := by
  refine lucas_of_list 697205147 5 [2, 11, 11, 83, 103, 337] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `698084633` is prime. -/
private theorem pr698084633 : (698084633).Prime := by
  refine lucas_of_list 698084633 3 [2, 2, 2, 7, 12465797] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12465797
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `744728227` is prime. -/
private theorem pr744728227 : (744728227).Prime := by
  refine lucas_of_list 744728227 2 [2, 3, 11, 11283761] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr11283761
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `792009763` is prime. -/
private theorem pr792009763 : (792009763).Prime := by
  refine lucas_of_list 792009763 5 [2, 3, 31, 4258117] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `861591053` is prime. -/
private theorem pr861591053 : (861591053).Prime := by
  refine lucas_of_list 861591053 2 [2, 2, 7, 619, 49711] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `861650429` is prime. -/
private theorem pr861650429 : (861650429).Prime := by
  refine lucas_of_list 861650429 2 [2, 2, 2267, 95021] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `890015519` is prime. -/
private theorem pr890015519 : (890015519).Prime := by
  refine lucas_of_list 890015519 7 [2, 7, 7, 17, 19, 31, 907] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `890952973` is prime. -/
private theorem pr890952973 : (890952973).Prime := by
  refine lucas_of_list 890952973 2 [2, 2, 3, 7, 13, 815891] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `902160289` is prime. -/
private theorem pr902160289 : (902160289).Prime := by
  refine lucas_of_list 902160289 11 [2, 2, 2, 2, 2, 3, 3, 3, 1044167] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `910234681` is prime. -/
private theorem pr910234681 : (910234681).Prime := by
  refine lucas_of_list 910234681 7 [2, 2, 2, 3, 5, 61, 124349] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `997295941` is prime. -/
private theorem pr997295941 : (997295941).Prime := by
  refine lucas_of_list 997295941 2 [2, 2, 3, 3, 5, 19, 163, 1789] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1007204273` is prime. -/
private theorem pr1007204273 : (1007204273).Prime := by
  refine lucas_of_list 1007204273 3 [2, 2, 2, 2, 137, 199, 2309] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1027602571` is prime. -/
private theorem pr1027602571 : (1027602571).Prime := by
  refine lucas_of_list 1027602571 3 [2, 3, 5, 17, 31, 64997] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1052173501` is prime. -/
private theorem pr1052173501 : (1052173501).Prime := by
  refine lucas_of_list 1052173501 2 [2, 2, 3, 5, 5, 5, 7, 100207] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1057990333` is prime. -/
private theorem pr1057990333 : (1057990333).Prime := by
  refine lucas_of_list 1057990333 5 [2, 2, 3, 7, 12595123] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12595123
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1077166219` is prime. -/
private theorem pr1077166219 : (1077166219).Prime := by
  refine lucas_of_list 1077166219 2 [2, 3, 107, 631, 2659] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1084120267` is prime. -/
private theorem pr1084120267 : (1084120267).Prime := by
  refine lucas_of_list 1084120267 2 [2, 3, 180686711] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr180686711
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1245634339` is prime. -/
private theorem pr1245634339 : (1245634339).Prime := by
  refine lucas_of_list 1245634339 2 [2, 3, 13, 19, 149, 5641] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1279808347` is prime. -/
private theorem pr1279808347 : (1279808347).Prime := by
  refine lucas_of_list 1279808347 3 [2, 3, 19, 1811, 6199] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1288202143` is prime. -/
private theorem pr1288202143 : (1288202143).Prime := by
  refine lucas_of_list 1288202143 3 [2, 3, 214700357] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr214700357
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1325436053` is prime. -/
private theorem pr1325436053 : (1325436053).Prime := by
  refine lucas_of_list 1325436053 2 [2, 2, 37, 599, 14951] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1378981139` is prime. -/
private theorem pr1378981139 : (1378981139).Prime := by
  refine lucas_of_list 1378981139 2 [2, 689490569] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr689490569
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `1379826499` is prime. -/
private theorem pr1379826499 : (1379826499).Prime := by
  refine lucas_of_list 1379826499 3 [2, 3, 419, 457, 1201] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1495933181` is prime. -/
private theorem pr1495933181 : (1495933181).Prime := by
  refine lucas_of_list 1495933181 3 [2, 2, 5, 7, 149, 71713] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1518054623` is prime. -/
private theorem pr1518054623 : (1518054623).Prime := by
  refine lucas_of_list 1518054623 5 [2, 7, 127, 853799] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `1527136987` is prime. -/
private theorem pr1527136987 : (1527136987).Prime := by
  refine lucas_of_list 1527136987 2 [2, 3, 254522831] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr254522831
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1596505387` is prime. -/
private theorem pr1596505387 : (1596505387).Prime := by
  refine lucas_of_list 1596505387 3 [2, 3, 7, 349, 108917] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1657267373` is prime. -/
private theorem pr1657267373 : (1657267373).Prime := by
  refine lucas_of_list 1657267373 2 [2, 2, 17, 79, 308501] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1716771031` is prime. -/
private theorem pr1716771031 : (1716771031).Prime := by
  refine lucas_of_list 1716771031 15 [2, 3, 5, 13, 19, 191, 1213] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1722927221` is prime. -/
private theorem pr1722927221 : (1722927221).Prime := by
  refine lucas_of_list 1722927221 12 [2, 2, 5, 7, 7, 17, 19, 5443] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1742133817` is prime. -/
private theorem pr1742133817 : (1742133817).Prime := by
  refine lucas_of_list 1742133817 5 [2, 2, 2, 3, 3, 71, 340793] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2086523903` is prime. -/
private theorem pr2086523903 : (2086523903).Prime := by
  refine lucas_of_list 2086523903 5 [2, 13789, 75659] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `2092467329` is prime. -/
private theorem pr2092467329 : (2092467329).Prime := by
  refine lucas_of_list 2092467329 3 [2, 2, 2, 2, 2, 2, 2, 7, 73, 31991] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2322190373` is prime. -/
private theorem pr2322190373 : (2322190373).Prime := by
  refine lucas_of_list 2322190373 2 [2, 2, 593, 979001] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2402762969` is prime. -/
private theorem pr2402762969 : (2402762969).Prime := by
  refine lucas_of_list 2402762969 3 [2, 2, 2, 300345371] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr300345371
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2451732109` is prime. -/
private theorem pr2451732109 : (2451732109).Prime := by
  refine lucas_of_list 2451732109 10 [2, 2, 3, 7, 19, 1536173] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2623759031` is prime. -/
private theorem pr2623759031 : (2623759031).Prime := by
  refine lucas_of_list 2623759031 11 [2, 5, 262375903] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr262375903
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `2722122253` is prime. -/
private theorem pr2722122253 : (2722122253).Prime := by
  refine lucas_of_list 2722122253 5 [2, 2, 3, 3, 97, 779531] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2790406819` is prime. -/
private theorem pr2790406819 : (2790406819).Prime := by
  refine lucas_of_list 2790406819 2 [2, 3, 3, 2089, 74209] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2871144517` is prime. -/
private theorem pr2871144517 : (2871144517).Prime := by
  refine lucas_of_list 2871144517 2 [2, 2, 3, 97, 2466619] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2917682857` is prime. -/
private theorem pr2917682857 : (2917682857).Prime := by
  refine lucas_of_list 2917682857 7 [2, 2, 2, 3, 3, 3, 3, 11, 409327] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2956634677` is prime. -/
private theorem pr2956634677 : (2956634677).Prime := by
  refine lucas_of_list 2956634677 2 [2, 2, 3, 3, 3, 127, 157, 1373] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2993641507` is prime. -/
private theorem pr2993641507 : (2993641507).Prime := by
  refine lucas_of_list 2993641507 2 [2, 3, 3, 53, 107, 29327] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3280193627` is prime. -/
private theorem pr3280193627 : (3280193627).Prime := by
  refine lucas_of_list 3280193627 2 [2, 61, 131, 167, 1229] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3552152101` is prime. -/
private theorem pr3552152101 : (3552152101).Prime := by
  refine lucas_of_list 3552152101 2 [2, 2, 3, 5, 5, 7, 7, 241643] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3581599039` is prime. -/
private theorem pr3581599039 : (3581599039).Prime := by
  refine lucas_of_list 3581599039 3 [2, 3, 37, 641, 25169] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3663362741` is prime. -/
private theorem pr3663362741 : (3663362741).Prime := by
  refine lucas_of_list 3663362741 2 [2, 2, 5, 1621, 112997] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3769344263` is prime. -/
private theorem pr3769344263 : (3769344263).Prime := by
  refine lucas_of_list 3769344263 5 [2, 2719, 693149] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `4147260437` is prime. -/
private theorem pr4147260437 : (4147260437).Prime := by
  refine lucas_of_list 4147260437 2 [2, 2, 11, 61, 1545179] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4233477553` is prime. -/
private theorem pr4233477553 : (4233477553).Prime := by
  refine lucas_of_list 4233477553 5 [2, 2, 2, 2, 3, 19, 31, 137, 1093] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4664162059` is prime. -/
private theorem pr4664162059 : (4664162059).Prime := by
  refine lucas_of_list 4664162059 2 [2, 3, 17, 37, 1235867] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4731360071` is prime. -/
private theorem pr4731360071 : (4731360071).Prime := by
  refine lucas_of_list 4731360071 7 [2, 5, 19919, 23753] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `4764733763` is prime. -/
private theorem pr4764733763 : (4764733763).Prime := by
  refine lucas_of_list 4764733763 2 [2, 641, 3716641] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `4826688001` is prime. -/
private theorem pr4826688001 : (4826688001).Prime := by
  refine lucas_of_list 4826688001 17 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 23, 1093] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `5001364957` is prime. -/
private theorem pr5001364957 : (5001364957).Prime := by
  refine lucas_of_list 5001364957 2 [2, 2, 3, 7, 59540059] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr59540059
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `5119233389` is prime. -/
private theorem pr5119233389 : (5119233389).Prime := by
  refine lucas_of_list 5119233389 2 [2, 2, 1279808347] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr1279808347
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `5247518063` is prime. -/
private theorem pr5247518063 : (5247518063).Prime := by
  refine lucas_of_list 5247518063 5 [2, 2623759031] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr2623759031
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `5320918487` is prime. -/
private theorem pr5320918487 : (5320918487).Prime := by
  refine lucas_of_list 5320918487 10 [2, 13, 23, 8897857] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `5577641177` is prime. -/
private theorem pr5577641177 : (5577641177).Prime := by
  refine lucas_of_list 5577641177 3 [2, 2, 2, 697205147] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr697205147
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `5638689323` is prime. -/
private theorem pr5638689323 : (5638689323).Prime := by
  refine lucas_of_list 5638689323 2 [2, 7, 402763523] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr402763523
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `5717755033` is prime. -/
private theorem pr5717755033 : (5717755033).Prime := by
  refine lucas_of_list 5717755033 5 [2, 2, 2, 3, 11, 21658163] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr21658163
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6197759341` is prime. -/
private theorem pr6197759341 : (6197759341).Prime := by
  refine lucas_of_list 6197759341 2 [2, 2, 3, 5, 19, 47, 131, 883] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6213907913` is prime. -/
private theorem pr6213907913 : (6213907913).Prime := by
  refine lucas_of_list 6213907913 3 [2, 2, 2, 14411, 53899] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6329005313` is prime. -/
private theorem pr6329005313 : (6329005313).Prime := by
  refine lucas_of_list 6329005313 3 [2, 2, 2, 2, 2, 2, 2, 2, 7, 23, 153557] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6434988877` is prime. -/
private theorem pr6434988877 : (6434988877).Prime := by
  refine lucas_of_list 6434988877 5 [2, 2, 3, 3, 139, 1285969] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6456531973` is prime. -/
private theorem pr6456531973 : (6456531973).Prime := by
  refine lucas_of_list 6456531973 2 [2, 2, 3, 11, 773, 63277] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6594009211` is prime. -/
private theorem pr6594009211 : (6594009211).Prime := by
  refine lucas_of_list 6594009211 10 [2, 3, 3, 5, 73266769] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr73266769
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6935507071` is prime. -/
private theorem pr6935507071 : (6935507071).Prime := by
  refine lucas_of_list 6935507071 3 [2, 3, 5, 409, 565241] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6968535269` is prime. -/
private theorem pr6968535269 : (6968535269).Prime := by
  refine lucas_of_list 6968535269 2 [2, 2, 1742133817] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr1742133817
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `7027267483` is prime. -/
private theorem pr7027267483 : (7027267483).Prime := by
  refine lucas_of_list 7027267483 2 [2, 3, 3, 3, 167, 779249] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7080939533` is prime. -/
private theorem pr7080939533 : (7080939533).Prime := by
  refine lucas_of_list 7080939533 2 [2, 2, 19, 109, 599, 1427] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7110835499` is prime. -/
private theorem pr7110835499 : (7110835499).Prime := by
  refine lucas_of_list 7110835499 2 [2, 13, 273493673] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr273493673
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `7732828661` is prime. -/
private theorem pr7732828661 : (7732828661).Prime := by
  refine lucas_of_list 7732828661 2 [2, 2, 5, 101, 3828133] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `8333956667` is prime. -/
private theorem pr8333956667 : (8333956667).Prime := by
  refine lucas_of_list 8333956667 2 [2, 7, 23, 151, 171403] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `8619557693` is prime. -/
private theorem pr8619557693 : (8619557693).Prime := by
  refine lucas_of_list 8619557693 2 [2, 2, 53, 1171, 34721] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `8835549007` is prime. -/
private theorem pr8835549007 : (8835549007).Prime := by
  refine lucas_of_list 8835549007 6 [2, 3, 25229, 58369] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `9102346811` is prime. -/
private theorem pr9102346811 : (9102346811).Prime := by
  refine lucas_of_list 9102346811 2 [2, 5, 910234681] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr910234681
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `9339993463` is prime. -/
private theorem pr9339993463 : (9339993463).Prime := by
  refine lucas_of_list 9339993463 6 [2, 3, 467, 3333331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `9345527687` is prime. -/
private theorem pr9345527687 : (9345527687).Prime := by
  refine lucas_of_list 9345527687 5 [2, 11, 11, 131, 294793] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9529467527` is prime. -/
private theorem pr9529467527 : (9529467527).Prime := by
  refine lucas_of_list 9529467527 5 [2, 4764733763] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr4764733763
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `9766125793` is prime. -/
private theorem pr9766125793 : (9766125793).Prime := by
  refine lucas_of_list 9766125793 5 [2, 2, 2, 2, 2, 3, 3, 2357, 14387] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10365220559` is prime. -/
private theorem pr10365220559 : (10365220559).Prime := by
  refine lucas_of_list 10365220559 7 [2, 7, 11, 193, 348739] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10389832997` is prime. -/
private theorem pr10389832997 : (10389832997).Prime := by
  refine lucas_of_list 10389832997 2 [2, 2, 71, 491, 74509] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11316666059` is prime. -/
private theorem pr11316666059 : (11316666059).Prime := by
  refine lucas_of_list 11316666059 2 [2, 12653, 447193] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `11499543953` is prime. -/
private theorem pr11499543953 : (11499543953).Prime := by
  refine lucas_of_list 11499543953 3 [2, 2, 2, 2, 13, 181, 305449] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11775978961` is prime. -/
private theorem pr11775978961 : (11775978961).Prime := by
  refine lucas_of_list 11775978961 7 [2, 2, 2, 2, 3, 5, 29, 67, 25253] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12034594001` is prime. -/
private theorem pr12034594001 : (12034594001).Prime := by
  refine lucas_of_list 12034594001 7 [2, 2, 2, 2, 5, 5, 5, 11, 13, 29, 1451] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12291831439` is prime. -/
private theorem pr12291831439 : (12291831439).Prime := by
  refine lucas_of_list 12291831439 6 [2, 3, 139, 14738407] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr14738407
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `13301377811` is prime. -/
private theorem pr13301377811 : (13301377811).Prime := by
  refine lucas_of_list 13301377811 2 [2, 5, 7, 7, 101, 397, 677] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13762226441` is prime. -/
private theorem pr13762226441 : (13762226441).Prime := by
  refine lucas_of_list 13762226441 3 [2, 2, 2, 5, 4481, 76781] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `14326396157` is prime. -/
private theorem pr14326396157 : (14326396157).Prime := by
  refine lucas_of_list 14326396157 2 [2, 2, 3581599039] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr3581599039
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `15748433761` is prime. -/
private theorem pr15748433761 : (15748433761).Prime := by
  refine lucas_of_list 15748433761 19 [2, 2, 2, 2, 2, 3, 5, 29, 1131353] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `15956735057` is prime. -/
private theorem pr15956735057 : (15956735057).Prime := by
  refine lucas_of_list 15956735057 3 [2, 2, 2, 2, 997295941] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr997295941
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `17818878313` is prime. -/
private theorem pr17818878313 : (17818878313).Prime := by
  refine lucas_of_list 17818878313 5 [2, 2, 2, 3, 3, 3, 3, 4561, 6029] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `18204693623` is prime. -/
private theorem pr18204693623 : (18204693623).Prime := by
  refine lucas_of_list 18204693623 5 [2, 9102346811] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr9102346811
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `20191382989` is prime. -/
private theorem pr20191382989 : (20191382989).Prime := by
  refine lucas_of_list 20191382989 6 [2, 2, 3, 7, 240373607] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr240373607
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `21585785531` is prime. -/
private theorem pr21585785531 : (21585785531).Prime := by
  refine lucas_of_list 21585785531 2 [2, 5, 17, 5347, 23747] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `21647877547` is prime. -/
private theorem pr21647877547 : (21647877547).Prime := by
  refine lucas_of_list 21647877547 3 [2, 3, 727, 4962833] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `22580452819` is prime. -/
private theorem pr22580452819 : (22580452819).Prime := by
  refine lucas_of_list 22580452819 3 [2, 3, 3, 7, 11, 16291813] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr16291813
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `22999087907` is prime. -/
private theorem pr22999087907 : (22999087907).Prime := by
  refine lucas_of_list 22999087907 2 [2, 11499543953] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr11499543953
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `23831345513` is prime. -/
private theorem pr23831345513 : (23831345513).Prime := by
  refine lucas_of_list 23831345513 3 [2, 2, 2, 13, 229147553] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr229147553
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `24429863873` is prime. -/
private theorem pr24429863873 : (24429863873).Prime := by
  refine lucas_of_list 24429863873 3 [2, 2, 2, 2, 2, 2, 17, 22453919] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr22453919
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `24517321091` is prime. -/
private theorem pr24517321091 : (24517321091).Prime := by
  refine lucas_of_list 24517321091 2 [2, 5, 2451732109] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr2451732109
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `24884605783` is prime. -/
private theorem pr24884605783 : (24884605783).Prime := by
  refine lucas_of_list 24884605783 3 [2, 3, 3, 3, 460826033] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr460826033
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `30372020233` is prime. -/
private theorem pr30372020233 : (30372020233).Prime := by
  refine lucas_of_list 30372020233 5 [2, 2, 2, 3, 13103, 96581] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `31229592833` is prime. -/
private theorem pr31229592833 : (31229592833).Prime := by
  refine lucas_of_list 31229592833 3 [2, 2, 2, 2, 2, 2, 2, 2, 23, 1061, 4999] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `31230853553` is prime. -/
private theorem pr31230853553 : (31230853553).Prime := by
  refine lucas_of_list 31230853553 3 [2, 2, 2, 2, 83, 107, 219787] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `31479206387` is prime. -/
private theorem pr31479206387 : (31479206387).Prime := by
  refine lucas_of_list 31479206387 2 [2, 227, 1531, 45289] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `31485108379` is prime. -/
private theorem pr31485108379 : (31485108379).Prime := by
  refine lucas_of_list 31485108379 2 [2, 3, 5247518063] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr5247518063
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `33238997579` is prime. -/
private theorem pr33238997579 : (33238997579).Prime := by
  refine lucas_of_list 33238997579 2 [2, 41, 941, 430769] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `33324234421` is prime. -/
private theorem pr33324234421 : (33324234421).Prime := by
  refine lucas_of_list 33324234421 2 [2, 2, 3, 5, 53, 53, 149, 1327] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `35420031197` is prime. -/
private theorem pr35420031197 : (35420031197).Prime := by
  refine lucas_of_list 35420031197 2 [2, 2, 11, 1129, 713021] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `36432751309` is prime. -/
private theorem pr36432751309 : (36432751309).Prime := by
  refine lucas_of_list 36432751309 2 [2, 2, 3, 5519, 550111] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `37283447479` is prime. -/
private theorem pr37283447479 : (37283447479).Prime := by
  refine lucas_of_list 37283447479 3 [2, 3, 6213907913] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr6213907913
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `37780381753` is prime. -/
private theorem pr37780381753 : (37780381753).Prime := by
  refine lucas_of_list 37780381753 5 [2, 2, 2, 3, 31, 50780083] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr50780083
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `37895703403` is prime. -/
private theorem pr37895703403 : (37895703403).Prime := by
  refine lucas_of_list 37895703403 2 [2, 3, 16831, 375257] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `39064503173` is prime. -/
private theorem pr39064503173 : (39064503173).Prime := by
  refine lucas_of_list 39064503173 2 [2, 2, 9766125793] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr9766125793
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `39589590367` is prime. -/
private theorem pr39589590367 : (39589590367).Prime := by
  refine lucas_of_list 39589590367 5 [2, 3, 3, 127, 17318281] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr17318281
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `40666679681` is prime. -/
private theorem pr40666679681 : (40666679681).Prime := by
  refine lucas_of_list 40666679681 7 [2, 2, 2, 2, 2, 2, 2, 5, 11, 61, 281, 337] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `42584560313` is prime. -/
private theorem pr42584560313 : (42584560313).Prime := by
  refine lucas_of_list 42584560313 3 [2, 2, 2, 7, 17, 19, 2354299] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `43171571063` is prime. -/
private theorem pr43171571063 : (43171571063).Prime := by
  refine lucas_of_list 43171571063 5 [2, 21585785531] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr21585785531
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `43877959031` is prime. -/
private theorem pr43877959031 : (43877959031).Prime := by
  refine lucas_of_list 43877959031 7 [2, 5, 29, 139, 463, 2351] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `45534680017` is prime. -/
private theorem pr45534680017 : (45534680017).Prime := by
  refine lucas_of_list 45534680017 5 [2, 2, 2, 2, 3, 7, 7, 101, 103, 1861] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `46387923041` is prime. -/
private theorem pr46387923041 : (46387923041).Prime := by
  refine lucas_of_list 46387923041 3 [2, 2, 2, 2, 2, 5, 953, 304223] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `51086952937` is prime. -/
private theorem pr51086952937 : (51086952937).Prime := by
  refine lucas_of_list 51086952937 5 [2, 2, 2, 3, 3, 3, 4723, 50077] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `51904488469` is prime. -/
private theorem pr51904488469 : (51904488469).Prime := by
  refine lucas_of_list 51904488469 10 [2, 2, 3, 7, 17, 36347681] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr36347681
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `53302431541` is prime. -/
private theorem pr53302431541 : (53302431541).Prime := by
  refine lucas_of_list 53302431541 2 [2, 2, 3, 5, 997, 891047] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `53318180099` is prime. -/
private theorem pr53318180099 : (53318180099).Prime := by
  refine lucas_of_list 53318180099 2 [2, 16189, 1646741] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `53834370553` is prime. -/
private theorem pr53834370553 : (53834370553).Prime := by
  refine lucas_of_list 53834370553 5 [2, 2, 2, 3, 3, 3, 89, 2800373] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `54254393867` is prime. -/
private theorem pr54254393867 : (54254393867).Prime := by
  refine lucas_of_list 54254393867 2 [2, 19, 7151, 199657] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `57669660497` is prime. -/
private theorem pr57669660497 : (57669660497).Prime := by
  refine lucas_of_list 57669660497 3 [2, 2, 2, 2, 7, 131, 3930593] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `60178698037` is prime. -/
private theorem pr60178698037 : (60178698037).Prime := by
  refine lucas_of_list 60178698037 2 [2, 2, 3, 3, 3, 23, 24226529] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr24226529
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `60259961959` is prime. -/
private theorem pr60259961959 : (60259961959).Prime := by
  refine lucas_of_list 60259961959 15 [2, 3, 7, 7, 23, 2347, 3797] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `60463226503` is prime. -/
private theorem pr60463226503 : (60463226503).Prime := by
  refine lucas_of_list 60463226503 3 [2, 3, 3, 7, 7, 227, 301993] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `64531875143` is prime. -/
private theorem pr64531875143 : (64531875143).Prime := by
  refine lucas_of_list 64531875143 5 [2, 7, 659, 6994567] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `65309679899` is prime. -/
private theorem pr65309679899 : (65309679899).Prime := by
  refine lucas_of_list 65309679899 2 [2, 347, 94106167] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr94106167
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `66477995159` is prime. -/
private theorem pr66477995159 : (66477995159).Prime := by
  refine lucas_of_list 66477995159 7 [2, 33238997579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr33238997579
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `74825443409` is prime. -/
private theorem pr74825443409 : (74825443409).Prime := by
  refine lucas_of_list 74825443409 3 [2, 2, 2, 2, 19, 227, 1084301] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `76465413523` is prime. -/
private theorem pr76465413523 : (76465413523).Prime := by
  refine lucas_of_list 76465413523 2 [2, 3, 3, 59, 3109, 23159] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `85958376943` is prime. -/
private theorem pr85958376943 : (85958376943).Prime := by
  refine lucas_of_list 85958376943 3 [2, 3, 14326396157] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr14326396157
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `87887482153` is prime. -/
private theorem pr87887482153 : (87887482153).Prime := by
  refine lucas_of_list 87887482153 10 [2, 2, 2, 3, 359, 10200497] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr10200497
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `92635891519` is prime. -/
private theorem pr92635891519 : (92635891519).Prime := by
  refine lucas_of_list 92635891519 6 [2, 3, 271, 56971643] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr56971643
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `92874198779` is prime. -/
private theorem pr92874198779 : (92874198779).Prime := by
  refine lucas_of_list 92874198779 2 [2, 521, 89130709] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr89130709
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `106636360199` is prime. -/
private theorem pr106636360199 : (106636360199).Prime := by
  refine lucas_of_list 106636360199 13 [2, 53318180099] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr53318180099
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `108708092417` is prime. -/
private theorem pr108708092417 : (108708092417).Prime := by
  refine lucas_of_list 108708092417 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 11, 197, 13997] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `108822127027` is prime. -/
private theorem pr108822127027 : (108822127027).Prime := by
  refine lucas_of_list 108822127027 3 [2, 3, 57667, 314513] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `111931372219` is prime. -/
private theorem pr111931372219 : (111931372219).Prime := by
  refine lucas_of_list 111931372219 2 [2, 3, 59, 1109, 285113] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `113635369417` is prime. -/
private theorem pr113635369417 : (113635369417).Prime := by
  refine lucas_of_list 113635369417 5 [2, 2, 2, 3, 41, 115483099] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr115483099
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `124597685867` is prime. -/
private theorem pr124597685867 : (124597685867).Prime := by
  refine lucas_of_list 124597685867 2 [2, 22871, 2723923] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `130619359799` is prime. -/
private theorem pr130619359799 : (130619359799).Prime := by
  refine lucas_of_list 130619359799 11 [2, 65309679899] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr65309679899
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `188916436547` is prime. -/
private theorem pr188916436547 : (188916436547).Prime := by
  refine lucas_of_list 188916436547 2 [2, 227, 416115499] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr416115499
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `192221037521` is prime. -/
private theorem pr192221037521 : (192221037521).Prime := by
  refine lucas_of_list 192221037521 3 [2, 2, 2, 2, 5, 2402762969] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2402762969
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `199105289309` is prime. -/
private theorem pr199105289309 : (199105289309).Prime := by
  refine lucas_of_list 199105289309 2 [2, 2, 31, 179, 199, 45077] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `242025323723` is prime. -/
private theorem pr242025323723 : (242025323723).Prime := by
  refine lucas_of_list 242025323723 2 [2, 7, 13, 29, 857, 53507] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `265826870599` is prime. -/
private theorem pr265826870599 : (265826870599).Prime := by
  refine lucas_of_list 265826870599 6 [2, 3, 23, 23, 2243, 37339] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `290243930833` is prime. -/
private theorem pr290243930833 : (290243930833).Prime := by
  refine lucas_of_list 290243930833 5 [2, 2, 2, 2, 3, 3, 3, 29, 79, 293261] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `294842999443` is prime. -/
private theorem pr294842999443 : (294842999443).Prime := by
  refine lucas_of_list 294842999443 2 [2, 3, 71, 463, 1494859] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `301491416153` is prime. -/
private theorem pr301491416153 : (301491416153).Prime := by
  refine lucas_of_list 301491416153 3 [2, 2, 2, 61, 131, 4716109] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `302314004851` is prime. -/
private theorem pr302314004851 : (302314004851).Prime := by
  refine lucas_of_list 302314004851 10 [2, 3, 5, 5, 11, 11, 13, 1281263] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `305861654093` is prime. -/
private theorem pr305861654093 : (305861654093).Prime := by
  refine lucas_of_list 305861654093 2 [2, 2, 76465413523] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr76465413523
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `311133343753` is prime. -/
private theorem pr311133343753 : (311133343753).Prime := by
  refine lucas_of_list 311133343753 5 [2, 2, 2, 3, 3, 3, 3, 7, 11, 193, 32309] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `312899444027` is prime. -/
private theorem pr312899444027 : (312899444027).Prime := by
  refine lucas_of_list 312899444027 2 [2, 13, 12034594001] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr12034594001
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `315397352443` is prime. -/
private theorem pr315397352443 : (315397352443).Prime := by
  refine lucas_of_list 315397352443 2 [2, 3, 59, 890952973] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr890952973
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `319814589247` is prime. -/
private theorem pr319814589247 : (319814589247).Prime := by
  refine lucas_of_list 319814589247 3 [2, 3, 53302431541] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr53302431541
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `330022844089` is prime. -/
private theorem pr330022844089 : (330022844089).Prime := by
  refine lucas_of_list 330022844089 19 [2, 2, 2, 3, 7, 29, 67738679] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr67738679
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `335578005941` is prime. -/
private theorem pr335578005941 : (335578005941).Prime := by
  refine lucas_of_list 335578005941 2 [2, 2, 5, 79, 212391143] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr212391143
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `365105423671` is prime. -/
private theorem pr365105423671 : (365105423671).Prime := by
  refine lucas_of_list 365105423671 3 [2, 3, 5, 13, 19, 1117, 44111] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `365291935901` is prime. -/
private theorem pr365291935901 : (365291935901).Prime := by
  refine lucas_of_list 365291935901 2 [2, 2, 5, 5, 43, 84951613] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr84951613
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `425051407483` is prime. -/
private theorem pr425051407483 : (425051407483).Prime := by
  refine lucas_of_list 425051407483 3 [2, 3, 13, 71, 103, 701, 1063] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `451762270279` is prime. -/
private theorem pr451762270279 : (451762270279).Prime := by
  refine lucas_of_list 451762270279 6 [2, 3, 11, 41, 379, 440497] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `453364581037` is prime. -/
private theorem pr453364581037 : (453364581037).Prime := by
  refine lucas_of_list 453364581037 2 [2, 2, 3, 37780381753] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr37780381753
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `519044884691` is prime. -/
private theorem pr519044884691 : (519044884691).Prime := by
  refine lucas_of_list 519044884691 2 [2, 5, 51904488469] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr51904488469
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `566279021177` is prime. -/
private theorem pr566279021177 : (566279021177).Prime := by
  refine lucas_of_list 566279021177 3 [2, 2, 2, 11, 6434988877] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr6434988877
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `572940327977` is prime. -/
private theorem pr572940327977 : (572940327977).Prime := by
  refine lucas_of_list 572940327977 3 [2, 2, 2, 19, 3769344263] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3769344263
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `610048503733` is prime. -/
private theorem pr610048503733 : (610048503733).Prime := by
  refine lucas_of_list 610048503733 6 [2, 2, 3, 59, 861650429] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr861650429
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `670429151471` is prime. -/
private theorem pr670429151471 : (670429151471).Prime := by
  refine lucas_of_list 670429151471 14 [2, 5, 13, 17, 2293, 132299] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `748392889147` is prime. -/
private theorem pr748392889147 : (748392889147).Prime := by
  refine lucas_of_list 748392889147 3 [2, 3, 7, 17818878313] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr17818878313
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `779323591693` is prime. -/
private theorem pr779323591693 : (779323591693).Prime := by
  refine lucas_of_list 779323591693 2 [2, 2, 3, 3, 21647877547] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr21647877547
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `818100119659` is prime. -/
private theorem pr818100119659 : (818100119659).Prime := by
  refine lucas_of_list 818100119659 2 [2, 3, 4733, 28808371] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr28808371
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `828206926003` is prime. -/
private theorem pr828206926003 : (828206926003).Prime := by
  refine lucas_of_list 828206926003 2 [2, 3, 3, 4451, 10337339] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr10337339
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `945070436021` is prime. -/
private theorem pr945070436021 : (945070436021).Prime := by
  refine lucas_of_list 945070436021 2 [2, 2, 5, 79103, 597367] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `950150168809` is prime. -/
private theorem pr950150168809 : (950150168809).Prime := by
  refine lucas_of_list 950150168809 11 [2, 2, 2, 3, 39589590367] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr39589590367
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `974925143341` is prime. -/
private theorem pr974925143341 : (974925143341).Prime := by
  refine lucas_of_list 974925143341 2 [2, 2, 3, 5, 227, 71580407] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr71580407
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1063307482397` is prime. -/
private theorem pr1063307482397 : (1063307482397).Prime := by
  refine lucas_of_list 1063307482397 2 [2, 2, 265826870599] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr265826870599
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1088174629013` is prime. -/
private theorem pr1088174629013 : (1088174629013).Prime := by
  refine lucas_of_list 1088174629013 2 [2, 2, 809, 336271517] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr336271517
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `1158991654867` is prime. -/
private theorem pr1158991654867 : (1158991654867).Prime := by
  refine lucas_of_list 1158991654867 2 [2, 3, 17, 82241, 138163] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1452875247809` is prime. -/
private theorem pr1452875247809 : (1452875247809).Prime := by
  refine lucas_of_list 1452875247809 3 [2, 2, 2, 2, 2, 2, 107, 212160521] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr212160521
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1567432317589` is prime. -/
private theorem pr1567432317589 : (1567432317589).Prime := by
  refine lucas_of_list 1567432317589 2 [2, 2, 3, 130619359799] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr130619359799
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `1862295922811` is prime. -/
private theorem pr1862295922811 : (1862295922811).Prime := by
  refine lucas_of_list 1862295922811 2 [2, 5, 89, 2092467329] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr2092467329
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `1938780795079` is prime. -/
private theorem pr1938780795079 : (1938780795079).Prime := by
  refine lucas_of_list 1938780795079 3 [2, 3, 3, 3, 59, 163, 3733321] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1964573055559` is prime. -/
private theorem pr1964573055559 : (1964573055559).Prime := by
  refine lucas_of_list 1964573055559 3 [2, 3, 3, 47, 2322190373] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2322190373
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2095965547883` is prime. -/
private theorem pr2095965547883 : (2095965547883).Prime := by
  refine lucas_of_list 2095965547883 2 [2, 727, 3461, 416503] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2125520100343` is prime. -/
private theorem pr2125520100343 : (2125520100343).Prime := by
  refine lucas_of_list 2125520100343 3 [2, 3, 3, 34123, 3460553] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2387351023727` is prime. -/
private theorem pr2387351023727 : (2387351023727).Prime := by
  refine lucas_of_list 2387351023727 5 [2, 29, 31, 71, 577, 32411] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2420281450523` is prime. -/
private theorem pr2420281450523 : (2420281450523).Prime := by
  refine lucas_of_list 2420281450523 2 [2, 13, 19, 3121, 1569803] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2472615770087` is prime. -/
private theorem pr2472615770087 : (2472615770087).Prime := by
  refine lucas_of_list 2472615770087 7 [2, 7, 11, 23, 698084633] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr698084633
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2523831981577` is prime. -/
private theorem pr2523831981577 : (2523831981577).Prime := by
  refine lucas_of_list 2523831981577 5 [2, 2, 2, 3, 97, 1084120267] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1084120267
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2634324435601` is prime. -/
private theorem pr2634324435601 : (2634324435601).Prime := by
  refine lucas_of_list 2634324435601 14 [2, 2, 2, 2, 3, 5, 5, 11, 13, 31, 495211] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3177474093709` is prime. -/
private theorem pr3177474093709 : (3177474093709).Prime := by
  refine lucas_of_list 3177474093709 7 [2, 2, 3, 1223, 216508183] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr216508183
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3507526212259` is prime. -/
private theorem pr3507526212259 : (3507526212259).Prime := by
  refine lucas_of_list 3507526212259 3 [2, 3, 109, 991, 5411897] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3748127235119` is prime. -/
private theorem pr3748127235119 : (3748127235119).Prime := by
  refine lucas_of_list 3748127235119 13 [2, 7, 17, 15748433761] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr15748433761
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `4088792340533` is prime. -/
private theorem pr4088792340533 : (4088792340533).Prime := by
  refine lucas_of_list 4088792340533 2 [2, 2, 41, 97, 257027429] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr257027429
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4407712336771` is prime. -/
private theorem pr4407712336771 : (4407712336771).Prime := by
  refine lucas_of_list 4407712336771 3 [2, 3, 5, 19, 7732828661] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr7732828661
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4643709938951` is prime. -/
private theorem pr4643709938951 : (4643709938951).Prime := by
  refine lucas_of_list 4643709938951 13 [2, 5, 5, 92874198779] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr92874198779
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `4765869387107` is prime. -/
private theorem pr4765869387107 : (4765869387107).Prime := by
  refine lucas_of_list 4765869387107 2 [2, 61, 39064503173] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr39064503173
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `5117033427953` is prime. -/
private theorem pr5117033427953 : (5117033427953).Prime := by
  refine lucas_of_list 5117033427953 3 [2, 2, 2, 2, 319814589247] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr319814589247
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `5383023947713` is prime. -/
private theorem pr5383023947713 : (5383023947713).Prime := by
  refine lucas_of_list 5383023947713 5 [2, 2, 2, 2, 2, 2, 3, 3, 9345527687] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9345527687
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6440317084823` is prime. -/
private theorem pr6440317084823 : (6440317084823).Prime := by
  refine lucas_of_list 6440317084823 5 [2, 151, 1123, 18989807] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr18989807
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `7042035418679` is prime. -/
private theorem pr7042035418679 : (7042035418679).Prime := by
  refine lucas_of_list 7042035418679 7 [2, 13, 23, 11775978961] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr11775978961
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `9440126545153` is prime. -/
private theorem pr9440126545153 : (9440126545153).Prime := by
  refine lucas_of_list 9440126545153 7 [2, 2, 2, 2, 2, 2, 2, 2, 3, 12291831439] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12291831439
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11546768420377` is prime. -/
private theorem pr11546768420377 : (11546768420377).Prime := by
  refine lucas_of_list 11546768420377 13 [2, 2, 2, 3, 7, 19, 4493, 805121] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11899086257609` is prime. -/
private theorem pr11899086257609 : (11899086257609).Prime := by
  refine lucas_of_list 11899086257609 3 [2, 2, 2, 11, 11, 1229, 1361, 7349] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `14931700285219` is prime. -/
private theorem pr14931700285219 : (14931700285219).Prime := by
  refine lucas_of_list 14931700285219 2 [2, 3, 77681, 32036363] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr32036363
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `15554278306283` is prime. -/
private theorem pr15554278306283 : (15554278306283).Prime := by
  refine lucas_of_list 15554278306283 2 [2, 71, 223, 491198077] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr491198077
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `15805946613607` is prime. -/
private theorem pr15805946613607 : (15805946613607).Prime := by
  refine lucas_of_list 15805946613607 3 [2, 3, 2634324435601] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr2634324435601
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `16212765124043` is prime. -/
private theorem pr16212765124043 : (16212765124043).Prime := by
  refine lucas_of_list 16212765124043 2 [2, 359, 22580452819] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr22580452819
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `16771119123133` is prime. -/
private theorem pr16771119123133 : (16771119123133).Prime := by
  refine lucas_of_list 16771119123133 2 [2, 2, 3, 3, 3, 3, 3, 11, 2713, 578167] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `19347157352023` is prime. -/
private theorem pr19347157352023 : (19347157352023).Prime := by
  refine lucas_of_list 19347157352023 3 [2, 3, 3623, 890015519] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr890015519
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `20246808290977` is prime. -/
private theorem pr20246808290977 : (20246808290977).Prime := by
  refine lucas_of_list 20246808290977 10 [2, 2, 2, 2, 2, 3, 3, 31, 61, 79, 470593] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `20949707179589` is prime. -/
private theorem pr20949707179589 : (20949707179589).Prime := by
  refine lucas_of_list 20949707179589 2 [2, 2, 11, 107, 49433, 90017] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `21771732463127` is prime. -/
private theorem pr21771732463127 : (21771732463127).Prime := by
  refine lucas_of_list 21771732463127 5 [2, 19, 572940327977] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr572940327977
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `22451786674411` is prime. -/
private theorem pr22451786674411 : (22451786674411).Prime := by
  refine lucas_of_list 22451786674411 2 [2, 3, 5, 748392889147] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr748392889147
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `22474902077743` is prime. -/
private theorem pr22474902077743 : (22474902077743).Prime := by
  refine lucas_of_list 22474902077743 3 [2, 3, 23, 23, 7080939533] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr7080939533
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `22630926334829` is prime. -/
private theorem pr22630926334829 : (22630926334829).Prime := by
  refine lucas_of_list 22630926334829 3 [2, 2, 7, 43271, 18678731] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr18678731
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `24477388722767` is prime. -/
private theorem pr24477388722767 : (24477388722767).Prime := by
  refine lucas_of_list 24477388722767 7 [2, 7, 135433, 12909593] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr12909593
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `27675032667859` is prime. -/
private theorem pr27675032667859 : (27675032667859).Prime := by
  refine lucas_of_list 27675032667859 10 [2, 3, 3, 73, 127, 6211, 26701] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `31738775298547` is prime. -/
private theorem pr31738775298547 : (31738775298547).Prime := by
  refine lucas_of_list 31738775298547 2 [2, 3, 8837, 598596343] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr598596343
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `35243004164791` is prime. -/
private theorem pr35243004164791 : (35243004164791).Prime := by
  refine lucas_of_list 35243004164791 21 [2, 3, 5, 31, 37895703403] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr37895703403
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `38865359569567` is prime. -/
private theorem pr38865359569567 : (38865359569567).Prime := by
  refine lucas_of_list 38865359569567 3 [2, 3, 710791, 9113171] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `42541206222269` is prime. -/
private theorem pr42541206222269 : (42541206222269).Prime := by
  refine lucas_of_list 42541206222269 2 [2, 2, 13, 818100119659] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr818100119659
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `43934838800387` is prime. -/
private theorem pr43934838800387 : (43934838800387).Prime := by
  refine lucas_of_list 43934838800387 2 [2, 84503, 259960231] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr259960231
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `44085822541603` is prime. -/
private theorem pr44085822541603 : (44085822541603).Prime := by
  refine lucas_of_list 44085822541603 13 [2, 3, 19, 19, 43, 3989, 118661] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `44575573061713` is prime. -/
private theorem pr44575573061713 : (44575573061713).Prime := by
  refine lucas_of_list 44575573061713 5 [2, 2, 2, 2, 3, 7, 7, 11, 1722927221] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1722927221
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `45538419582079` is prime. -/
private theorem pr45538419582079 : (45538419582079).Prime := by
  refine lucas_of_list 45538419582079 3 [2, 3, 859, 8835549007] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr8835549007
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `47595099254663` is prime. -/
private theorem pr47595099254663 : (47595099254663).Prime := by
  refine lucas_of_list 47595099254663 5 [2, 41, 53, 4889, 2240023] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `48266393033149` is prime. -/
private theorem pr48266393033149 : (48266393033149).Prime := by
  refine lucas_of_list 48266393033149 2 [2, 2, 3, 37, 108708092417] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr108708092417
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `51962785915753` is prime. -/
private theorem pr51962785915753 : (51962785915753).Prime := by
  refine lucas_of_list 51962785915753 10 [2, 2, 2, 3, 3, 467, 13931, 110933] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `53325101004937` is prime. -/
private theorem pr53325101004937 : (53325101004937).Prime := by
  refine lucas_of_list 53325101004937 5 [2, 2, 2, 3, 31481, 70578419] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr70578419
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `56609284696067` is prime. -/
private theorem pr56609284696067 : (56609284696067).Prime := by
  refine lucas_of_list 56609284696067 2 [2, 17, 3331, 499843579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr499843579
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `58344908285777` is prime. -/
private theorem pr58344908285777 : (58344908285777).Prime := by
  refine lucas_of_list 58344908285777 3 [2, 2, 2, 2, 7, 8599, 60581077] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr60581077
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `59412081922873` is prime. -/
private theorem pr59412081922873 : (59412081922873).Prime := by
  refine lucas_of_list 59412081922873 5 [2, 2, 2, 3, 7, 853, 414587743] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr414587743
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `62697292703561` is prime. -/
private theorem pr62697292703561 : (62697292703561).Prime := by
  refine lucas_of_list 62697292703561 3 [2, 2, 2, 5, 1567432317589] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1567432317589
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `71800474063579` is prime. -/
private theorem pr71800474063579 : (71800474063579).Prime := by
  refine lucas_of_list 71800474063579 7 [2, 3, 13, 173, 5320918487] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5320918487
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `72614582527967` is prime. -/
private theorem pr72614582527967 : (72614582527967).Prime := by
  refine lucas_of_list 72614582527967 5 [2, 29, 29, 43171571063] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr43171571063
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `72734635214027` is prime. -/
private theorem pr72734635214027 : (72734635214027).Prime := by
  refine lucas_of_list 72734635214027 2 [2, 16747, 45259, 47981] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `77388629408093` is prime. -/
private theorem pr77388629408093 : (77388629408093).Prime := by
  refine lucas_of_list 77388629408093 2 [2, 2, 19347157352023] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr19347157352023
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `79181590014127` is prime. -/
private theorem pr79181590014127 : (79181590014127).Prime := by
  refine lucas_of_list 79181590014127 3 [2, 3, 3, 73, 60259961959] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr60259961959
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `91401329827331` is prime. -/
private theorem pr91401329827331 : (91401329827331).Prime := by
  refine lucas_of_list 91401329827331 2 [2, 5, 31, 294842999443] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr294842999443
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `104277872792237` is prime. -/
private theorem pr104277872792237 : (104277872792237).Prime := by
  refine lucas_of_list 104277872792237 2 [2, 2, 11, 13, 181, 1007204273] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1007204273
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `112733560547189` is prime. -/
private theorem pr112733560547189 : (112733560547189).Prime := by
  refine lucas_of_list 112733560547189 2 [2, 2, 7, 137, 139, 211426697] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr211426697
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `113248351080743` is prime. -/
private theorem pr113248351080743 : (113248351080743).Prime := by
  refine lucas_of_list 113248351080743 5 [2, 359, 373, 6871, 61543] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `115839677230721` is prime. -/
private theorem pr115839677230721 : (115839677230721).Prime := by
  refine lucas_of_list 115839677230721 3 [2, 2, 2, 2, 2, 2, 2, 5, 67709, 2673197] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `120959307407017` is prime. -/
private theorem pr120959307407017 : (120959307407017).Prime := by
  refine lucas_of_list 120959307407017 10 [2, 2, 2, 3, 3, 3, 13, 107, 402585761] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr402585761
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `134248599246871` is prime. -/
private theorem pr134248599246871 : (134248599246871).Prime := by
  refine lucas_of_list 134248599246871 6 [2, 3, 3, 5, 2801, 532542343] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr532542343
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `142282195240429` is prime. -/
private theorem pr142282195240429 : (142282195240429).Prime := by
  refine lucas_of_list 142282195240429 6 [2, 2, 3, 3, 7573, 15031, 34721] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `157632868713841` is prime. -/
private theorem pr157632868713841 : (157632868713841).Prime := by
  refine lucas_of_list 157632868713841 21 [2, 2, 2, 2, 3, 5, 13, 577, 87562141] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr87562141
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `186419181996451` is prime. -/
private theorem pr186419181996451 : (186419181996451).Prime := by
  refine lucas_of_list 186419181996451 3 [2, 3, 3, 5, 5, 13, 19, 29, 57833987] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr57833987
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `189168169397789` is prime. -/
private theorem pr189168169397789 : (189168169397789).Prime := by
  refine lucas_of_list 189168169397789 2 [2, 2, 7, 6421, 1052173501] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1052173501
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `191285033313581` is prime. -/
private theorem pr191285033313581 : (191285033313581).Prime := by
  refine lucas_of_list 191285033313581 2 [2, 2, 5, 27701, 345267379] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr345267379
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `220251018746027` is prime. -/
private theorem pr220251018746027 : (220251018746027).Prime := by
  refine lucas_of_list 220251018746027 2 [2, 17, 911, 7110835499] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr7110835499
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `230096119521941` is prime. -/
private theorem pr230096119521941 : (230096119521941).Prime := by
  refine lucas_of_list 230096119521941 2 [2, 2, 5, 7, 103, 15956735057] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr15956735057
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `245129705159611` is prime. -/
private theorem pr245129705159611 : (245129705159611).Prime := by
  refine lucas_of_list 245129705159611 10 [2, 3, 5, 73, 111931372219] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr111931372219
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `346124421605093` is prime. -/
private theorem pr346124421605093 : (346124421605093).Prime := by
  refine lucas_of_list 346124421605093 2 [2, 2, 13, 569, 13883, 842623] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `419871237221651` is prime. -/
private theorem pr419871237221651 : (419871237221651).Prime := by
  refine lucas_of_list 419871237221651 2 [2, 5, 5, 23, 365105423671] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr365105423671
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `421359165309683` is prime. -/
private theorem pr421359165309683 : (421359165309683).Prime := by
  refine lucas_of_list 421359165309683 2 [2, 31, 5227, 32381, 40153] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `451388964702847` is prime. -/
private theorem pr451388964702847 : (451388964702847).Prime := by
  refine lucas_of_list 451388964702847 3 [2, 3, 2477, 30372020233] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr30372020233
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `477660828715223` is prime. -/
private theorem pr477660828715223 : (477660828715223).Prime := by
  refine lucas_of_list 477660828715223 5 [2, 193, 431, 2871144517] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr2871144517
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `525372998720231` is prime. -/
private theorem pr525372998720231 : (525372998720231).Prime := by
  refine lucas_of_list 525372998720231 7 [2, 5, 107837, 487191779] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr487191779
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `548634678168341` is prime. -/
private theorem pr548634678168341 : (548634678168341).Prime := by
  refine lucas_of_list 548634678168341 2 [2, 2, 5, 31, 37, 223, 4721, 22717] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `622334808294481` is prime. -/
private theorem pr622334808294481 : (622334808294481).Prime := by
  refine lucas_of_list 622334808294481 22 [2, 2, 2, 2, 3, 3, 3, 5, 41, 7027267483] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr7027267483
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `692248843210187` is prime. -/
private theorem pr692248843210187 : (692248843210187).Prime := by
  refine lucas_of_list 692248843210187 2 [2, 346124421605093] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr346124421605093
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `760880252327401` is prime. -/
private theorem pr760880252327401 : (760880252327401).Prime := by
  refine lucas_of_list 760880252327401 7 [2, 2, 2, 3, 3, 3, 5, 5, 103, 467, 2929331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `769570458831689` is prime. -/
private theorem pr769570458831689 : (769570458831689).Prime := by
  refine lucas_of_list 769570458831689 3 [2, 2, 2, 83, 1158991654867] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1158991654867
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `912271806042529` is prime. -/
private theorem pr912271806042529 : (912271806042529).Prime := by
  refine lucas_of_list 912271806042529 17 [2, 2, 2, 2, 2, 3, 127, 74825443409] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr74825443409
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `916054440512669` is prime. -/
private theorem pr916054440512669 : (916054440512669).Prime := by
  refine lucas_of_list 916054440512669 2 [2, 2, 37, 4969, 1245634339] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1245634339
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `951529557611071` is prime. -/
private theorem pr951529557611071 : (951529557611071).Prime := by
  refine lucas_of_list 951529557611071 3 [2, 3, 3, 5, 239, 257, 6661, 25841] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1155716269053257` is prime. -/
private theorem pr1155716269053257 : (1155716269053257).Prime := by
  refine lucas_of_list 1155716269053257 3 [2, 2, 2, 83, 395671, 4398949] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1267234094133083` is prime. -/
private theorem pr1267234094133083 : (1267234094133083).Prime := by
  refine lucas_of_list 1267234094133083 2 [2, 53, 89, 439, 809, 378223] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1405019647086019` is prime. -/
private theorem pr1405019647086019 : (1405019647086019).Prime := by
  refine lucas_of_list 1405019647086019 2 [2, 3, 37783, 6197759341] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr6197759341
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `1669983630876157` is prime. -/
private theorem pr1669983630876157 : (1669983630876157).Prime := by
  refine lucas_of_list 1669983630876157 2 [2, 2, 3, 3929, 35420031197] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr35420031197
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1860868258313677` is prime. -/
private theorem pr1860868258313677 : (1860868258313677).Prime := by
  refine lucas_of_list 1860868258313677 2 [2, 2, 3, 89, 389, 7057, 634709] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2078511436630121` is prime. -/
private theorem pr2078511436630121 : (2078511436630121).Prime := by
  refine lucas_of_list 2078511436630121 3 [2, 2, 2, 5, 51962785915753] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr51962785915753
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2239816076104753` is prime. -/
private theorem pr2239816076104753 : (2239816076104753).Prime := by
  refine lucas_of_list 2239816076104753 5 [2, 2, 2, 2, 3, 3, 15554278306283] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr15554278306283
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2509852437723749` is prime. -/
private theorem pr2509852437723749 : (2509852437723749).Prime := by
  refine lucas_of_list 2509852437723749 2 [2, 2, 13, 48266393033149] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr48266393033149
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2717960425937833` is prime. -/
private theorem pr2717960425937833 : (2717960425937833).Prime := by
  refine lucas_of_list 2717960425937833 5 [2, 2, 2, 3, 113248351080743] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr113248351080743
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3175247426634629` is prime. -/
private theorem pr3175247426634629 : (3175247426634629).Prime := by
  refine lucas_of_list 3175247426634629 2 [2, 2, 23, 277, 124597685867] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr124597685867
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4126526573127359` is prime. -/
private theorem pr4126526573127359 : (4126526573127359).Prime := by
  refine lucas_of_list 4126526573127359 7 [2, 47, 251, 307, 1429, 398669] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4923460001199119` is prime. -/
private theorem pr4923460001199119 : (4923460001199119).Prime := by
  refine lucas_of_list 4923460001199119 7 [2, 19, 2153, 60178698037] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr60178698037
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `5019704875447499` is prime. -/
private theorem pr5019704875447499 : (5019704875447499).Prime := by
  refine lucas_of_list 5019704875447499 2 [2, 2509852437723749] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr2509852437723749
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `5118474470330537` is prime. -/
private theorem pr5118474470330537 : (5118474470330537).Prime := by
  refine lucas_of_list 5118474470330537 3 [2, 2, 2, 7, 91401329827331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr91401329827331
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `5220125027436647` is prime. -/
private theorem pr5220125027436647 : (5220125027436647).Prime := by
  refine lucas_of_list 5220125027436647 5 [2, 41, 67, 950150168809] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr950150168809
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `6524021120954317` is prime. -/
private theorem pr6524021120954317 : (6524021120954317).Prime := by
  refine lucas_of_list 6524021120954317 2 [2, 2, 3, 7, 569, 292549, 466579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6704479765807211` is prime. -/
private theorem pr6704479765807211 : (6704479765807211).Prime := by
  refine lucas_of_list 6704479765807211 2 [2, 5, 134053, 5001364957] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr5001364957
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `8326536867006979` is prime. -/
private theorem pr8326536867006979 : (8326536867006979).Prime := by
  refine lucas_of_list 8326536867006979 2 [2, 3, 31, 6487049, 6900877] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9784477431121871` is prime. -/
private theorem pr9784477431121871 : (9784477431121871).Prime := by
  refine lucas_of_list 9784477431121871 11 [2, 5, 23, 42541206222269] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr42541206222269
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `9895156140145319` is prime. -/
private theorem pr9895156140145319 : (9895156140145319).Prime := by
  refine lucas_of_list 9895156140145319 7 [2, 7, 7, 31, 8741, 372626521] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr372626521
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9978856522517893` is prime. -/
private theorem pr9978856522517893 : (9978856522517893).Prime := by
  refine lucas_of_list 9978856522517893 6 [2, 2, 3, 37, 22474902077743] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr22474902077743
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10384319362547701` is prime. -/
private theorem pr10384319362547701 : (10384319362547701).Prime := by
  refine lucas_of_list 10384319362547701 10 [2, 2, 3, 3, 3, 3, 5, 5, 857, 1495933181] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1495933181
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10871841703751333` is prime. -/
private theorem pr10871841703751333 : (10871841703751333).Prime := by
  refine lucas_of_list 10871841703751333 2 [2, 2, 2717960425937833] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr2717960425937833
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `11467184916715951` is prime. -/
private theorem pr11467184916715951 : (11467184916715951).Prime := by
  refine lucas_of_list 11467184916715951 3 [2, 3, 5, 5, 61, 3257, 11813, 32573] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11689936606210663` is prime. -/
private theorem pr11689936606210663 : (11689936606210663).Prime := by
  refine lucas_of_list 11689936606210663 6 [2, 3, 3, 31, 20949707179589] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr20949707179589
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11724703249818631` is prime. -/
private theorem pr11724703249818631 : (11724703249818631).Prime := by
  refine lucas_of_list 11724703249818631 13 [2, 3, 5, 269, 1452875247809] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1452875247809
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `14217522899257439` is prime. -/
private theorem pr14217522899257439 : (14217522899257439).Prime := by
  refine lucas_of_list 14217522899257439 11 [2, 29, 245129705159611] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr245129705159611
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `17291715770034751` is prime. -/
private theorem pr17291715770034751 : (17291715770034751).Prime := by
  refine lucas_of_list 17291715770034751 15 [2, 3, 5, 5, 5, 11, 2095965547883] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2095965547883
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `26721148560770567` is prime. -/
private theorem pr26721148560770567 : (26721148560770567).Prime := by
  refine lucas_of_list 26721148560770567 5 [2, 7, 373, 5117033427953] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr5117033427953
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `28873065043059313` is prime. -/
private theorem pr28873065043059313 : (28873065043059313).Prime := by
  refine lucas_of_list 28873065043059313 5 [2, 2, 2, 2, 3, 283, 2125520100343] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2125520100343
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `38102969119615549` is prime. -/
private theorem pr38102969119615549 : (38102969119615549).Prime := by
  refine lucas_of_list 38102969119615549 6 [2, 2, 3, 3175247426634629] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr3175247426634629
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `53864553850831211` is prime. -/
private theorem pr53864553850831211 : (53864553850831211).Prime := by
  refine lucas_of_list 53864553850831211 2 [2, 5, 234203, 22999087907] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr22999087907
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `58385395586721857` is prime. -/
private theorem pr58385395586721857 : (58385395586721857).Prime := by
  refine lucas_of_list 58385395586721857 3 [2, 2, 2, 2, 2, 2, 912271806042529] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr912271806042529
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `64288855770297817` is prime. -/
private theorem pr64288855770297817 : (64288855770297817).Prime := by
  refine lucas_of_list 64288855770297817 5 [2, 2, 2, 3, 7, 6329, 60463226503] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr60463226503
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `65722234366057721` is prime. -/
private theorem pr65722234366057721 : (65722234366057721).Prime := by
  refine lucas_of_list 65722234366057721 3 [2, 2, 2, 5, 11, 3673, 40666679681] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr40666679681
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `69901770934033393` is prime. -/
private theorem pr69901770934033393 : (69901770934033393).Prime := by
  refine lucas_of_list 69901770934033393 5 [2, 2, 2, 2, 3, 9052751, 160866779] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr160866779
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `78211655574940513` is prime. -/
private theorem pr78211655574940513 : (78211655574940513).Prime := by
  refine lucas_of_list 78211655574940513 5 [2, 2, 2, 2, 2, 3, 3, 3, 3, 137, 571, 385726793] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr385726793
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `79440516821738663` is prime. -/
private theorem pr79440516821738663 : (79440516821738663).Prime := by
  refine lucas_of_list 79440516821738663 5 [2, 37, 14291269, 75117227] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr14291269
    · exact pr75117227
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `86603861654270201` is prime. -/
private theorem pr86603861654270201 : (86603861654270201).Prime := by
  refine lucas_of_list 86603861654270201 3 [2, 2, 2, 5, 5, 29, 14931700285219] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr14931700285219
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `94430879944479007` is prime. -/
private theorem pr94430879944479007 : (94430879944479007).Prime := by
  refine lucas_of_list 94430879944479007 3 [2, 3, 2083, 446087, 16937681] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr16937681
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `99684099323208679` is prime. -/
private theorem pr99684099323208679 : (99684099323208679).Prime := by
  refine lucas_of_list 99684099323208679 3 [2, 3, 1279, 1225283, 10601509] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr10601509
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `110643065903853667` is prime. -/
private theorem pr110643065903853667 : (110643065903853667).Prime := by
  refine lucas_of_list 110643065903853667 2 [2, 3, 3, 3, 3, 41, 384889, 43280257] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr43280257
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `145147724148466807` is prime. -/
private theorem pr145147724148466807 : (145147724148466807).Prime := by
  refine lucas_of_list 145147724148466807 5 [2, 3, 13, 1860868258313677] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr1860868258313677
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `167563482700358321` is prime. -/
private theorem pr167563482700358321 : (167563482700358321).Prime := by
  refine lucas_of_list 167563482700358321 3 [2, 2, 2, 2, 5, 37, 56609284696067] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr56609284696067
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `176695608476229709` is prime. -/
private theorem pr176695608476229709 : (176695608476229709).Prime := by
  refine lucas_of_list 176695608476229709 6 [2, 2, 3, 59, 4782719, 52181629] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr52181629
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `191509382975357539` is prime. -/
private theorem pr191509382975357539 : (191509382975357539).Prime := by
  refine lucas_of_list 191509382975357539 12 [2, 3, 3, 7, 13, 13, 467, 19259, 999959] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `222944156490058331` is prime. -/
private theorem pr222944156490058331 : (222944156490058331).Prime := by
  refine lucas_of_list 222944156490058331 2 [2, 5, 97, 151, 257, 4231, 1399817] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `280558478549055913` is prime. -/
private theorem pr280558478549055913 : (280558478549055913).Prime := by
  refine lucas_of_list 280558478549055913 7 [2, 2, 2, 3, 11689936606210663] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11689936606210663
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `293824958127172973` is prime. -/
private theorem pr293824958127172973 : (293824958127172973).Prime := by
  refine lucas_of_list 293824958127172973 2 [2, 2, 1259, 58344908285777] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr58344908285777
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `482438575255746299` is prime. -/
private theorem pr482438575255746299 : (482438575255746299).Prime := by
  refine lucas_of_list 482438575255746299 2 [2, 7, 61, 59281, 9529467527] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9529467527
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `569406979818597733` is prime. -/
private theorem pr569406979818597733 : (569406979818597733).Prime := by
  refine lucas_of_list 569406979818597733 6 [2, 2, 3, 7, 17, 409, 974925143341] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr974925143341
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `633184884311351663` is prime. -/
private theorem pr633184884311351663 : (633184884311351663).Prime := by
  refine lucas_of_list 633184884311351663 5 [2, 269, 4457, 9199, 28705493] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr28705493
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `673215965532847003` is prime. -/
private theorem pr673215965532847003 : (673215965532847003).Prime := by
  refine lucas_of_list 673215965532847003 2 [2, 3, 7, 41, 199, 1964573055559] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1964573055559
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `828618497366655791` is prime. -/
private theorem pr828618497366655791 : (828618497366655791).Prime := by
  refine lucas_of_list 828618497366655791 11 [2, 5, 51902017, 1596505387] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr51902017
    · exact pr1596505387
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `902701302361863029` is prime. -/
private theorem pr902701302361863029 : (902701302361863029).Prime := by
  refine lucas_of_list 902701302361863029 2 [2, 2, 5119, 44085822541603] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr44085822541603
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `925106424198984623` is prime. -/
private theorem pr925106424198984623 : (925106424198984623).Prime := by
  refine lucas_of_list 925106424198984623 5 [2, 7, 23, 29, 313, 50593, 6256091] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `946812652780551077` is prime. -/
private theorem pr946812652780551077 : (946812652780551077).Prime := by
  refine lucas_of_list 946812652780551077 2 [2, 2, 13, 11681, 31321, 49767413] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr49767413
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1215521601171890807` is prime. -/
private theorem pr1215521601171890807 : (1215521601171890807).Prime := by
  refine lucas_of_list 1215521601171890807 5 [2, 53, 11467184916715951] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr11467184916715951
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1226271900451500011` is prime. -/
private theorem pr1226271900451500011 : (1226271900451500011).Prime := by
  refine lucas_of_list 1226271900451500011 2 [2, 5, 409, 1033, 290243930833] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr290243930833
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1259307407003899763` is prime. -/
private theorem pr1259307407003899763 : (1259307407003899763).Prime := by
  refine lucas_of_list 1259307407003899763 2 [2, 23, 617, 12491, 3552152101] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3552152101
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1336633773450893867` is prime. -/
private theorem pr1336633773450893867 : (1336633773450893867).Prime := by
  refine lucas_of_list 1336633773450893867 2 [2, 13, 17, 29, 104277872792237] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr104277872792237
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1805402604723726059` is prime. -/
private theorem pr1805402604723726059 : (1805402604723726059).Prime := by
  refine lucas_of_list 1805402604723726059 2 [2, 902701302361863029] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr902701302361863029
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `1951794736996274813` is prime. -/
private theorem pr1951794736996274813 : (1951794736996274813).Prime := by
  refine lucas_of_list 1951794736996274813 2 [2, 2, 162995029, 2993641507] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr162995029
    · exact pr2993641507
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2120347301714756509` is prime. -/
private theorem pr2120347301714756509 : (2120347301714756509).Prime := by
  refine lucas_of_list 2120347301714756509 2 [2, 2, 3, 176695608476229709] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr176695608476229709
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2692863862131388013` is prime. -/
private theorem pr2692863862131388013 : (2692863862131388013).Prime := by
  refine lucas_of_list 2692863862131388013 2 [2, 2, 673215965532847003] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr673215965532847003
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `3702146813488080077` is prime. -/
private theorem pr3702146813488080077 : (3702146813488080077).Prime := by
  refine lucas_of_list 3702146813488080077 2 [2, 2, 7, 191, 692248843210187] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr692248843210187
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4033171858149485323` is prime. -/
private theorem pr4033171858149485323 : (4033171858149485323).Prime := by
  refine lucas_of_list 4033171858149485323 2 [2, 3, 487, 244787, 5638689323] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5638689323
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4462783807057408057` is prime. -/
private theorem pr4462783807057408057 : (4462783807057408057).Prime := by
  refine lucas_of_list 4462783807057408057 19 [2, 2, 2, 3, 7, 103, 311, 601, 1379826499] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1379826499
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4974868610361993331` is prime. -/
private theorem pr4974868610361993331 : (4974868610361993331).Prime := by
  refine lucas_of_list 4974868610361993331 2 [2, 3, 3, 5, 13, 14220029, 299016581] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr14220029
    · exact pr299016581
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6298302738844988441` is prime. -/
private theorem pr6298302738844988441 : (6298302738844988441).Prime := by
  refine lucas_of_list 6298302738844988441 3 [2, 2, 2, 5, 19, 509, 1607, 3517, 2880739] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9510443673519113051` is prime. -/
private theorem pr9510443673519113051 : (9510443673519113051).Prime := by
  refine lucas_of_list 9510443673519113051 6 [2, 5, 5, 11, 17291715770034751] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr17291715770034751
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11509108433238662069` is prime. -/
private theorem pr11509108433238662069 : (11509108433238662069).Prime := by
  refine lucas_of_list 11509108433238662069 2 [2, 2, 1378981139, 2086523903] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr1378981139
    · exact pr2086523903
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `12162998469897001351` is prime. -/
private theorem pr12162998469897001351 : (12162998469897001351).Prime := by
  refine lucas_of_list 12162998469897001351 3 [2, 3, 3, 3, 5, 5, 13, 53, 34897, 374713697] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr374713697
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12578714787664099229` is prime. -/
private theorem pr12578714787664099229 : (12578714787664099229).Prime := by
  refine lucas_of_list 12578714787664099229 2 [2, 2, 7, 7, 11, 881, 13331, 496762583] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr496762583
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13439412999494045647` is prime. -/
private theorem pr13439412999494045647 : (13439412999494045647).Prime := by
  refine lucas_of_list 13439412999494045647 3 [2, 3, 41, 42409307, 1288202143] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr42409307
    · exact pr1288202143
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `17630303698054596683` is prime. -/
private theorem pr17630303698054596683 : (17630303698054596683).Prime := by
  refine lucas_of_list 17630303698054596683 2 [2, 7, 1259307407003899763] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr1259307407003899763
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `18358313616119304019` is prime. -/
private theorem pr18358313616119304019 : (18358313616119304019).Prime := by
  refine lucas_of_list 18358313616119304019 2 [2, 3, 3, 17, 601, 15461, 6456531973] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr6456531973
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `19020887347038226103` is prime. -/
private theorem pr19020887347038226103 : (19020887347038226103).Prime := by
  refine lucas_of_list 19020887347038226103 5 [2, 9510443673519113051] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr9510443673519113051
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `22438080793250320531` is prime. -/
private theorem pr22438080793250320531 : (22438080793250320531).Prime := by
  refine lucas_of_list 22438080793250320531 10 [2, 3, 5, 149, 5019704875447499] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5019704875447499
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `23430874743757638907` is prime. -/
private theorem pr23430874743757638907 : (23430874743757638907).Prime := by
  refine lucas_of_list 23430874743757638907 3 [2, 3, 7, 67, 8326536867006979] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr8326536867006979
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `25417220552692245857` is prime. -/
private theorem pr25417220552692245857 : (25417220552692245857).Prime := by
  refine lucas_of_list 25417220552692245857 3 [2, 2, 2, 2, 2, 3989287, 199105289309] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr199105289309
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `37776756054769556533` is prime. -/
private theorem pr37776756054769556533 : (37776756054769556533).Prime := by
  refine lucas_of_list 37776756054769556533 6 [2, 2, 3, 79, 907, 43934838800387] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr43934838800387
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `40194649904100499421` is prime. -/
private theorem pr40194649904100499421 : (40194649904100499421).Prime := by
  refine lucas_of_list 40194649904100499421 2 [2, 2, 5, 33827, 59412081922873] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr59412081922873
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `40400420911064051473` is prime. -/
private theorem pr40400420911064051473 : (40400420911064051473).Prime := by
  refine lucas_of_list 40400420911064051473 5 [2, 2, 2, 2, 3, 3, 280558478549055913] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr280558478549055913
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `45142465272184430383` is prime. -/
private theorem pr45142465272184430383 : (45142465272184430383).Prime := by
  refine lucas_of_list 45142465272184430383 3 [2, 3, 7907, 951529557611071] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr951529557611071
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `51062736476452083197` is prime. -/
private theorem pr51062736476452083197 : (51062736476452083197).Prime := by
  refine lucas_of_list 51062736476452083197 2 [2, 2, 11, 47, 81899, 301491416153] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr301491416153
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `58722424903363122961` is prime. -/
private theorem pr58722424903363122961 : (58722424903363122961).Prime := by
  refine lucas_of_list 58722424903363122961 7 [2, 2, 2, 2, 3, 5, 17, 37, 523, 29567, 25155511] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr25155511
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `60004887147455085487` is prime. -/
private theorem pr60004887147455085487 : (60004887147455085487).Prime := by
  refine lucas_of_list 60004887147455085487 3 [2, 3, 3, 7, 23, 45833, 451762270279] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr451762270279
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `75641996375808912001` is prime. -/
private theorem pr75641996375808912001 : (75641996375808912001).Prime := by
  refine lucas_of_list 75641996375808912001 17 [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5, 5, 7, 97, 85958376943] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr85958376943
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `118486009933781072573` is prime. -/
private theorem pr118486009933781072573 : (118486009933781072573).Prime := by
  refine lucas_of_list 118486009933781072573 2 [2, 2, 11, 2692863862131388013] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr2692863862131388013
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `127383622947208730741` is prime. -/
private theorem pr127383622947208730741 : (127383622947208730741).Prime := by
  refine lucas_of_list 127383622947208730741 12 [2, 2, 5, 11, 151, 397, 132421, 72940141] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr72940141
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `136207621785848300351` is prime. -/
private theorem pr136207621785848300351 : (136207621785848300351).Prime := by
  refine lucas_of_list 136207621785848300351 11 [2, 5, 5, 13, 193, 1279, 6857, 123801541] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr123801541
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `136224176548004202491` is prime. -/
private theorem pr136224176548004202491 : (136224176548004202491).Prime := by
  refine lucas_of_list 136224176548004202491 2 [2, 5, 7, 179, 10871841703751333] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr10871841703751333
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `164945316820677181643` is prime. -/
private theorem pr164945316820677181643 : (164945316820677181643).Prime := by
  refine lucas_of_list 164945316820677181643 2 [2, 7, 83, 34227293, 4147260437] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr34227293
    · exact pr4147260437
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `165561626209896455053` is prime. -/
private theorem pr165561626209896455053 : (165561626209896455053).Prime := by
  refine lucas_of_list 165561626209896455053 2 [2, 2, 3, 43, 1237, 1373, 188916436547] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr188916436547
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `206638672199221437191` is prime. -/
private theorem pr206638672199221437191 : (206638672199221437191).Prime := by
  refine lucas_of_list 206638672199221437191 7 [2, 5, 17, 1215521601171890807] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr1215521601171890807
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `212196228946492474003` is prime. -/
private theorem pr212196228946492474003 : (212196228946492474003).Prime := by
  refine lucas_of_list 212196228946492474003 2 [2, 3, 11, 1019, 15511, 16139, 12603847] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12603847
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `257556785377223992213` is prime. -/
private theorem pr257556785377223992213 : (257556785377223992213).Prime := by
  refine lucas_of_list 257556785377223992213 2 [2, 2, 3, 3, 3, 7, 727, 12569, 37283447479] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr37283447479
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `281846721989254322167` is prime. -/
private theorem pr281846721989254322167 : (281846721989254322167).Prime := by
  refine lucas_of_list 281846721989254322167 3 [2, 3, 7, 41, 263, 622334808294481] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr622334808294481
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `299305777708221457297` is prime. -/
private theorem pr299305777708221457297 : (299305777708221457297).Prime := by
  refine lucas_of_list 299305777708221457297 10 [2, 2, 2, 2, 3, 146427179, 42584560313] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr146427179
    · exact pr42584560313
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `329890633641354363287` is prime. -/
private theorem pr329890633641354363287 : (329890633641354363287).Prime := by
  refine lucas_of_list 329890633641354363287 5 [2, 164945316820677181643] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr164945316820677181643
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `359033310256530805319` is prime. -/
private theorem pr359033310256530805319 : (359033310256530805319).Prime := by
  refine lucas_of_list 359033310256530805319 7 [2, 97, 577, 673, 4765869387107] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr4765869387107
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `412818817755914888561` is prime. -/
private theorem pr412818817755914888561 : (412818817755914888561).Prime := by
  refine lucas_of_list 412818817755914888561 12 [2, 2, 2, 2, 5, 11, 31, 47, 1683503, 191250847] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr191250847
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `445947651491381543767` is prime. -/
private theorem pr445947651491381543767 : (445947651491381543767).Prime := by
  refine lucas_of_list 445947651491381543767 3 [2, 3, 19, 67, 58385395586721857] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr58385395586721857
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `503935824962734626127` is prime. -/
private theorem pr503935824962734626127 : (503935824962734626127).Prime := by
  refine lucas_of_list 503935824962734626127 3 [2, 3, 7, 2437, 4923460001199119] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr4923460001199119
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `656843935516215991673` is prime. -/
private theorem pr656843935516215991673 : (656843935516215991673).Prime := by
  refine lucas_of_list 656843935516215991673 3 [2, 2, 2, 6900151, 11899086257609] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11899086257609
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `718066620513061610639` is prime. -/
private theorem pr718066620513061610639 : (718066620513061610639).Prime := by
  refine lucas_of_list 718066620513061610639 7 [2, 359033310256530805319] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr359033310256530805319
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `748317318635326820621` is prime. -/
private theorem pr748317318635326820621 : (748317318635326820621).Prime := by
  refine lucas_of_list 748317318635326820621 2 [2, 2, 5, 10667309, 3507526212259] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr10667309
    · exact pr3507526212259
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `844714314516799947193` is prime. -/
private theorem pr844714314516799947193 : (844714314516799947193).Prime := by
  refine lucas_of_list 844714314516799947193 15 [2, 2, 2, 3, 7, 4409, 408689, 2790406819] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2790406819
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `883518765367127393929` is prime. -/
private theorem pr883518765367127393929 : (883518765367127393929).Prime := by
  refine lucas_of_list 883518765367127393929 11 [2, 2, 2, 3, 71, 127, 311, 130699, 100440719] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr100440719
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `885598448701788237149` is prime. -/
private theorem pr885598448701788237149 : (885598448701788237149).Prime := by
  refine lucas_of_list 885598448701788237149 2 [2, 2, 107, 563, 12157, 302314004851] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr302314004851
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1203758338357956872531` is prime. -/
private theorem pr1203758338357956872531 : (1203758338357956872531).Prime := by
  refine lucas_of_list 1203758338357956872531 6 [2, 5, 13, 7307, 1267234094133083] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1267234094133083
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1362255828628464151313` is prime. -/
private theorem pr1362255828628464151313 : (1362255828628464151313).Prime := by
  refine lucas_of_list 1362255828628464151313 3 [2, 2, 2, 2, 7, 12162998469897001351] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12162998469897001351
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1513992919016165401019` is prime. -/
private theorem pr1513992919016165401019 : (1513992919016165401019).Prime := by
  refine lucas_of_list 1513992919016165401019 2 [2, 31, 203773, 238531, 502389653] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr502389653
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1986415282087976566499` is prime. -/
private theorem pr1986415282087976566499 : (1986415282087976566499).Prime := by
  refine lucas_of_list 1986415282087976566499 2 [2, 7, 37, 3524047, 1088174629013] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1088174629013
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2013180202438700904799` is prime. -/
private theorem pr2013180202438700904799 : (2013180202438700904799).Prime := by
  refine lucas_of_list 2013180202438700904799 6 [2, 3, 7, 883, 224291, 242025323723] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr242025323723
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2366710855645183442959` is prime. -/
private theorem pr2366710855645183442959 : (2366710855645183442959).Prime := by
  refine lucas_of_list 2366710855645183442959 3 [2, 3, 3261029, 120959307407017] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr120959307407017
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `3040619457363130437577` is prime. -/
private theorem pr3040619457363130437577 : (3040619457363130437577).Prime := by
  refine lucas_of_list 3040619457363130437577 10 [2, 2, 2, 3, 173, 5147, 142282195240429] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr142282195240429
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4549543085530438019729` is prime. -/
private theorem pr4549543085530438019729 : (4549543085530438019729).Prime := by
  refine lucas_of_list 4549543085530438019729 3 [2, 2, 2, 2, 11, 23, 673, 1669983630876157] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1669983630876157
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4938663849193098822719` is prime. -/
private theorem pr4938663849193098822719 : (4938663849193098822719).Prime := by
  refine lucas_of_list 4938663849193098822719 22 [2, 23, 29, 3702146813488080077] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr3702146813488080077
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `5376337334771671650313` is prime. -/
private theorem pr5376337334771671650313 : (5376337334771671650313).Prime := by
  refine lucas_of_list 5376337334771671650313 11 [2, 2, 2, 3, 3, 3, 7, 7, 4763557, 106636360199] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr106636360199
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7832642975302929485459` is prime. -/
private theorem pr7832642975302929485459 : (7832642975302929485459).Prime := by
  refine lucas_of_list 7832642975302929485459 2 [2, 317, 547, 593, 7933, 11239, 427181] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9436173198685322265767` is prime. -/
private theorem pr9436173198685322265767 : (9436173198685322265767).Prime := by
  refine lucas_of_list 9436173198685322265767 5 [2, 257, 18358313616119304019] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr18358313616119304019
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `10245363712690297402829` is prime. -/
private theorem pr10245363712690297402829 : (10245363712690297402829).Prime := by
  refine lucas_of_list 10245363712690297402829 2 [2, 2, 23, 21757, 5118474470330537] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5118474470330537
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13052601752489221206953` is prime. -/
private theorem pr13052601752489221206953 : (13052601752489221206953).Prime := by
  refine lucas_of_list 13052601752489221206953 3 [2, 2, 2, 43, 229, 743, 6121, 36432751309] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr36432751309
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `13236432347084098236031` is prime. -/
private theorem pr13236432347084098236031 : (13236432347084098236031).Prime := by
  refine lucas_of_list 13236432347084098236031 6 [2, 3, 3, 5, 31, 571, 263941, 31479206387] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr31479206387
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `14735696059755052093559` is prime. -/
private theorem pr14735696059755052093559 : (14735696059755052093559).Prime := by
  refine lucas_of_list 14735696059755052093559 7 [2, 7, 11, 53, 1805402604723726059] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1805402604723726059
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `17261227208636271758719` is prime. -/
private theorem pr17261227208636271758719 : (17261227208636271758719).Prime := by
  refine lucas_of_list 17261227208636271758719 3 [2, 3, 3, 857, 1447, 15137, 51086952937] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr51086952937
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `18372083701294024233029` is prime. -/
private theorem pr18372083701294024233029 : (18372083701294024233029).Prime := by
  refine lucas_of_list 18372083701294024233029 2 [2, 2, 7, 7, 7, 17599, 760880252327401] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr760880252327401
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `23807031864678216915161` is prime. -/
private theorem pr23807031864678216915161 : (23807031864678216915161).Prime := by
  refine lucas_of_list 23807031864678216915161 3 [2, 2, 2, 5, 3001, 1822477, 108822127027] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr108822127027
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `27551705196575769604487` is prime. -/
private theorem pr27551705196575769604487 : (27551705196575769604487).Prime := by
  refine lucas_of_list 27551705196575769604487 5 [2, 7, 13, 229, 7136123, 92635891519] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr92635891519
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `28329326463708373030007` is prime. -/
private theorem pr28329326463708373030007 : (28329326463708373030007).Prime := by
  refine lucas_of_list 28329326463708373030007 5 [2, 277, 2081, 114079279, 215400961] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr114079279
    · exact pr215400961
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `29060653450353795925049` is prime. -/
private theorem pr29060653450353795925049 : (29060653450353795925049).Prime := by
  refine lucas_of_list 29060653450353795925049 3 [2, 2, 2, 5737, 633184884311351663] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr633184884311351663
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `30010776026931432629789` is prime. -/
private theorem pr30010776026931432629789 : (30010776026931432629789).Prime := by
  refine lucas_of_list 30010776026931432629789 2 [2, 2, 283, 10253, 47659, 54254393867] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr54254393867
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `32482216254667088931641` is prime. -/
private theorem pr32482216254667088931641 : (32482216254667088931641).Prime := by
  refine lucas_of_list 32482216254667088931641 6 [2, 2, 2, 5, 41, 131, 139, 1783, 610048503733] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr610048503733
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `41192624063165237064659` is prime. -/
private theorem pr41192624063165237064659 : (41192624063165237064659).Prime := by
  refine lucas_of_list 41192624063165237064659 2 [2, 47, 89, 151, 839, 38865359569567] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr38865359569567
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `43945623026920103814553` is prime. -/
private theorem pr43945623026920103814553 : (43945623026920103814553).Prime := by
  refine lucas_of_list 43945623026920103814553 5 [2, 2, 2, 3, 29, 8963, 20813983, 338452553] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr20813983
    · exact pr338452553
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `45614572983907197148423` is prime. -/
private theorem pr45614572983907197148423 : (45614572983907197148423).Prime := by
  refine lucas_of_list 45614572983907197148423 3 [2, 3, 3, 3, 844714314516799947193] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr844714314516799947193
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `51900396212045590265813` is prime. -/
private theorem pr51900396212045590265813 : (51900396212045590265813).Prime := by
  refine lucas_of_list 51900396212045590265813 2 [2, 2, 7, 23333, 79440516821738663] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr79440516821738663
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `72730695219214984781741` is prime. -/
private theorem pr72730695219214984781741 : (72730695219214984781741).Prime := by
  refine lucas_of_list 72730695219214984781741 2 [2, 2, 5, 751, 10301, 34157, 13762226441] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr13762226441
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `74219785556488562618461` is prime. -/
private theorem pr74219785556488562618461 : (74219785556488562618461).Prime := by
  refine lucas_of_list 74219785556488562618461 2 [2, 2, 3, 3, 5, 7, 7, 72643, 115839677230721] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr115839677230721
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `80363534630770482953137` is prime. -/
private theorem pr80363534630770482953137 : (80363534630770482953137).Prime := by
  refine lucas_of_list 80363534630770482953137 7 [2, 2, 2, 2, 3, 11, 47, 227, 456791, 31230853553] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr31230853553
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `92681997034922305623089` is prime. -/
private theorem pr92681997034922305623089 : (92681997034922305623089).Prime := by
  refine lucas_of_list 92681997034922305623089 3 [2, 2, 2, 2, 7, 163, 433, 11724703249818631] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11724703249818631
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `95781885718202172715249` is prime. -/
private theorem pr95781885718202172715249 : (95781885718202172715249).Prime := by
  refine lucas_of_list 95781885718202172715249 37 [2, 2, 2, 2, 3, 3, 11, 23, 173, 173, 4903, 32257, 555421] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `105156099570479055542803` is prime. -/
private theorem pr105156099570479055542803 : (105156099570479055542803).Prime := by
  refine lucas_of_list 105156099570479055542803 2 [2, 3, 3, 3, 3, 1527136987, 425051407483] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1527136987
    · exact pr425051407483
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `107558835773597899975051` is prime. -/
private theorem pr107558835773597899975051 : (107558835773597899975051).Prime := by
  refine lucas_of_list 107558835773597899975051 3 [2, 3, 5, 5, 13, 89, 1373, 451388964702847] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr451388964702847
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `115434748546891905857633` is prime. -/
private theorem pr115434748546891905857633 : (115434748546891905857633).Prime := by
  refine lucas_of_list 115434748546891905857633 3 [2, 2, 2, 2, 2, 17, 212196228946492474003] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr212196228946492474003
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `146245767985201734471473` is prime. -/
private theorem pr146245767985201734471473 : (146245767985201734471473).Prime := by
  refine lucas_of_list 146245767985201734471473 3 [2, 2, 2, 2, 523, 9384539, 1862295922811] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1862295922811
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `147344524868721931584433` is prime. -/
private theorem pr147344524868721931584433 : (147344524868721931584433).Prime := by
  refine lucas_of_list 147344524868721931584433 7 [2, 2, 2, 2, 3, 19, 31, 37, 43, 347, 9440126545153] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9440126545153
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `166965747451764499398851` is prime. -/
private theorem pr166965747451764499398851 : (166965747451764499398851).Prime := by
  refine lucas_of_list 166965747451764499398851 2 [2, 5, 5, 341287, 9784477431121871] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9784477431121871
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `200969125281548089384741` is prime. -/
private theorem pr200969125281548089384741 : (200969125281548089384741).Prime := by
  refine lucas_of_list 200969125281548089384741 6 [2, 2, 3, 5, 33601, 99684099323208679] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr99684099323208679
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `292615042094260586161777` is prime. -/
private theorem pr292615042094260586161777 : (292615042094260586161777).Prime := by
  refine lucas_of_list 292615042094260586161777 10 [2, 2, 2, 2, 3, 3, 7, 113, 75659, 251033, 135259027] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr135259027
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `416539151747554478703059` is prime. -/
private theorem pr416539151747554478703059 : (416539151747554478703059).Prime := by
  refine lucas_of_list 416539151747554478703059 2 [2, 841207, 4598999, 53834370553] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr53834370553
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `483162279352983405762947` is prime. -/
private theorem pr483162279352983405762947 : (483162279352983405762947).Prime := by
  refine lucas_of_list 483162279352983405762947 2 [2, 23, 13648559, 769570458831689] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr13648559
    · exact pr769570458831689
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `745207098227029371724807` is prime. -/
private theorem pr745207098227029371724807 : (745207098227029371724807).Prime := by
  refine lucas_of_list 745207098227029371724807 3 [2, 3, 30098239, 4126526573127359] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr30098239
    · exact pr4126526573127359
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `1287753136009443753814303` is prime. -/
private theorem pr1287753136009443753814303 : (1287753136009443753814303).Prime := by
  refine lucas_of_list 1287753136009443753814303 3 [2, 3, 10837, 315881, 62697292703561] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr62697292703561
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1610668957438324017996239` is prime. -/
private theorem pr1610668957438324017996239 : (1610668957438324017996239).Prime := by
  refine lucas_of_list 1610668957438324017996239 7 [2, 757, 48863821, 21771732463127] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr48863821
    · exact pr21771732463127
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2026106462258046807233143` is prime. -/
private theorem pr2026106462258046807233143 : (2026106462258046807233143).Prime := by
  refine lucas_of_list 2026106462258046807233143 3 [2, 3, 407527, 828618497366655791] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr828618497366655791
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2141710841057818288204801` is prime. -/
private theorem pr2141710841057818288204801 : (2141710841057818288204801).Prime := by
  refine lucas_of_list 2141710841057818288204801 22 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 7, 73, 1483, 4088792340533] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr4088792340533
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6681461160575807765631713` is prime. -/
private theorem pr6681461160575807765631713 : (6681461160575807765631713).Prime := by
  refine lucas_of_list 6681461160575807765631713 3 [2, 2, 2, 2, 2, 7813873, 26721148560770567] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr26721148560770567
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6871766633593002730621793` is prime. -/
private theorem pr6871766633593002730621793 : (6871766633593002730621793).Prime := by
  refine lucas_of_list 6871766633593002730621793 3 [2, 2, 2, 2, 2, 67, 71, 45142465272184430383] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr45142465272184430383
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7908849942063650934920749` is prime. -/
private theorem pr7908849942063650934920749 : (7908849942063650934920749).Prime := by
  refine lucas_of_list 7908849942063650934920749 6 [2, 2, 3, 3, 3, 3, 3, 7, 13, 19, 251, 251, 8963, 8333956667] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr8333956667
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10447259502000162783907811` is prime. -/
private theorem pr10447259502000162783907811 : (10447259502000162783907811).Prime := by
  refine lucas_of_list 10447259502000162783907811 2 [2, 5, 13, 80363534630770482953137] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr80363534630770482953137
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `14957884372838020959843697` is prime. -/
private theorem pr14957884372838020959843697 : (14957884372838020959843697).Prime := by
  refine lucas_of_list 14957884372838020959843697 5 [2, 2, 2, 2, 3, 11, 28329326463708373030007] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr28329326463708373030007
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `24590825361407890472118479` is prime. -/
private theorem pr24590825361407890472118479 : (24590825361407890472118479).Prime := by
  refine lucas_of_list 24590825361407890472118479 19 [2, 13, 19, 41, 109, 34757, 57457, 5577641177] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5577641177
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `30203332225010996743539893` is prime. -/
private theorem pr30203332225010996743539893 : (30203332225010996743539893).Prime := by
  refine lucas_of_list 30203332225010996743539893 2 [2, 2, 11, 67, 10245363712690297402829] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr10245363712690297402829
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `34124345809441049514408541` is prime. -/
private theorem pr34124345809441049514408541 : (34124345809441049514408541).Prime := by
  refine lucas_of_list 34124345809441049514408541 2 [2, 2, 3, 5, 11, 23, 61, 61, 293, 1914179, 1077166219] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1077166219
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `39095441725331704246601051` is prime. -/
private theorem pr39095441725331704246601051 : (39095441725331704246601051).Prime := by
  refine lucas_of_list 39095441725331704246601051 6 [2, 5, 5, 29, 227, 16866853, 7042035418679] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr16866853
    · exact pr7042035418679
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `62416232677071478843766407` is prime. -/
private theorem pr62416232677071478843766407 : (62416232677071478843766407).Prime := by
  refine lucas_of_list 62416232677071478843766407 5 [2, 3, 3, 47, 61, 55061, 91250311, 240723731] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr91250311
    · exact pr240723731
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `65351641560433344086222377` is prime. -/
private theorem pr65351641560433344086222377 : (65351641560433344086222377).Prime := by
  refine lucas_of_list 65351641560433344086222377 7 [2, 2, 2, 3, 3, 3, 2221, 136224176548004202491] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr136224176548004202491
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `78666368577342976408244729` is prime. -/
private theorem pr78666368577342976408244729 : (78666368577342976408244729).Prime := by
  refine lucas_of_list 78666368577342976408244729 6 [2, 2, 2, 7, 11, 29, 4651, 946812652780551077] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr946812652780551077
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `96254533221595962582020453` is prime. -/
private theorem pr96254533221595962582020453 : (96254533221595962582020453).Prime := by
  refine lucas_of_list 96254533221595962582020453 2 [2, 2, 1063307482397, 22630926334829] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr1063307482397
    · exact pr22630926334829
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `153633538234781791068580163` is prime. -/
private theorem pr153633538234781791068580163 : (153633538234781791068580163).Prime := by
  refine lucas_of_list 153633538234781791068580163 2 [2, 2420281450523, 31738775298547] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · exact pr2420281450523
    · exact pr31738775298547
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `153832774372503129547869733` is prime. -/
private theorem pr153832774372503129547869733 : (153832774372503129547869733).Prime := by
  refine lucas_of_list 153832774372503129547869733 5 [2, 2, 3, 13, 19, 51900396212045590265813] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr51900396212045590265813
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `234572650351990225479606307` is prime. -/
private theorem pr234572650351990225479606307 : (234572650351990225479606307).Prime := by
  refine lucas_of_list 234572650351990225479606307 2 [2, 3, 39095441725331704246601051] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr39095441725331704246601051
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `451925716330607804743726123` is prime. -/
private theorem pr451925716330607804743726123 : (451925716330607804743726123).Prime := by
  refine lucas_of_list 451925716330607804743726123 2 [2, 3, 71, 337, 113746859, 27675032667859] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr113746859
    · exact pr27675032667859
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `789812704340304383349069829` is prime. -/
private theorem pr789812704340304383349069829 : (789812704340304383349069829).Prime := by
  refine lucas_of_list 789812704340304383349069829 10 [2, 2, 3, 1823, 3137, 11509108433238662069] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11509108433238662069
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1571782070172867986209191007` is prime. -/
private theorem pr1571782070172867986209191007 : (1571782070172867986209191007).Prime := by
  refine lucas_of_list 1571782070172867986209191007 3 [2, 3, 19, 71, 1787, 963943, 112733560547189] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr112733560547189
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1818320332620503848001878811` is prime. -/
private theorem pr1818320332620503848001878811 : (1818320332620503848001878811).Prime := by
  refine lucas_of_list 1818320332620503848001878811 2 [2, 5, 7, 31, 1879, 445947651491381543767] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr445947651491381543767
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1981508142283827480998194771` is prime. -/
private theorem pr1981508142283827480998194771 : (1981508142283827480998194771).Prime := by
  refine lucas_of_list 1981508142283827480998194771 2 [2, 3, 3, 3, 5, 167, 43945623026920103814553] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr43945623026920103814553
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3923732503437934896722585503` is prime. -/
private theorem pr3923732503437934896722585503 : (3923732503437934896722585503).Prime := by
  refine lucas_of_list 3923732503437934896722585503 6 [2, 3, 3, 3, 7, 29, 107, 3067, 432167, 2523831981577] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2523831981577
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `5440143870742166955326084591` is prime. -/
private theorem pr5440143870742166955326084591 : (5440143870742166955326084591).Prime := by
  refine lucas_of_list 5440143870742166955326084591 7 [2, 5, 73709, 6386143, 1155716269053257] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1155716269053257
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7366400106656330968152704173` is prime. -/
private theorem pr7366400106656330968152704173 : (7366400106656330968152704173).Prime := by
  refine lucas_of_list 7366400106656330968152704173 5 [2, 2, 3, 3, 3, 23, 1041169, 408734203, 6968535269] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr408734203
    · exact pr6968535269
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9514210957160511212466547249` is prime. -/
private theorem pr9514210957160511212466547249 : (9514210957160511212466547249).Prime := by
  refine lucas_of_list 9514210957160511212466547249 7 [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 33324234421, 24477388722767] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr33324234421
    · exact pr24477388722767
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9619000479999082942481892337` is prime. -/
private theorem pr9619000479999082942481892337 : (9619000479999082942481892337).Prime := by
  refine lucas_of_list 9619000479999082942481892337 5 [2, 2, 2, 2, 3, 13, 97, 13033, 3253231, 3748127235119] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3748127235119
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `52751610625449532220312726917` is prime. -/
private theorem pr52751610625449532220312726917 : (52751610625449532220312726917).Prime := by
  refine lucas_of_list 52751610625449532220312726917 5 [2, 2, 3, 3, 13, 345637, 13301377811, 24517321091] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr13301377811
    · exact pr24517321091
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `66283874023533288977181798301` is prime. -/
private theorem pr66283874023533288977181798301 : (66283874023533288977181798301).Prime := by
  refine lucas_of_list 66283874023533288977181798301 6 [2, 2, 3, 5, 5, 10009, 2212153, 9978856522517893] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9978856522517893
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `69135092205651805980861073351` is prime. -/
private theorem pr69135092205651805980861073351 : (69135092205651805980861073351).Prime := by
  refine lucas_of_list 69135092205651805980861073351 3 [2, 3, 3, 5, 5, 153633538234781791068580163] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr153633538234781791068580163
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `73377284623470428818606905343` is prime. -/
private theorem pr73377284623470428818606905343 : (73377284623470428818606905343).Prime := by
  refine lucas_of_list 73377284623470428818606905343 3 [2, 3, 43, 113, 8627, 1850789, 157632868713841] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr157632868713841
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `102414823347778104187269761993` is prime. -/
private theorem pr102414823347778104187269761993 : (102414823347778104187269761993).Prime := by
  refine lucas_of_list 102414823347778104187269761993 3 [2, 2, 2, 7, 19, 96254533221595962582020453] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr96254533221595962582020453
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `110795687999866444754173880579` is prime. -/
private theorem pr110795687999866444754173880579 : (110795687999866444754173880579).Prime := by
  refine lucas_of_list 110795687999866444754173880579 2 [2, 7, 11, 29, 47, 83, 3280193627, 1938780795079] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3280193627
    · exact pr1938780795079
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `144661193821913382604745497139` is prime. -/
private theorem pr144661193821913382604745497139 : (144661193821913382604745497139).Prime := by
  refine lucas_of_list 144661193821913382604745497139 2 [2, 11, 32719, 200969125281548089384741] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr200969125281548089384741
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `153910062411705601645112038051` is prime. -/
private theorem pr153910062411705601645112038051 : (153910062411705601645112038051).Prime := by
  refine lucas_of_list 153910062411705601645112038051 2 [2, 3, 5, 5, 13, 23, 167, 877, 23430874743757638907] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr23430874743757638907
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `282401156303852819552097999551` is prime. -/
private theorem pr282401156303852819552097999551 : (282401156303852819552097999551).Prime := by
  refine lucas_of_list 282401156303852819552097999551 7 [2, 5, 5, 11, 17, 30203332225010996743539893] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr30203332225010996743539893
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `334260459649000270477156654889` is prime. -/
private theorem pr334260459649000270477156654889 : (334260459649000270477156654889).Prime := by
  refine lucas_of_list 334260459649000270477156654889 3 [2, 2, 2, 13, 92357, 16994801, 34863181, 58735241] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr16994801
    · exact pr34863181
    · exact pr58735241
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `436993708880564593139454644323` is prime. -/
private theorem pr436993708880564593139454644323 : (436993708880564593139454644323).Prime := by
  refine lucas_of_list 436993708880564593139454644323 2 [2, 3, 3, 43, 67, 73, 115434748546891905857633] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr115434748546891905857633
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `946874521071922737507641579447` is prime. -/
private theorem pr946874521071922737507641579447 : (946874521071922737507641579447).Prime := by
  refine lucas_of_list 946874521071922737507641579447 5 [2, 3213131, 147344524868721931584433] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr147344524868721931584433
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1004233205235910075995966480773` is prime. -/
private theorem pr1004233205235910075995966480773 : (1004233205235910075995966480773).Prime := by
  refine lucas_of_list 1004233205235910075995966480773 3 [2, 2, 13, 89, 109, 63697, 1716771031, 18204693623] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1716771031
    · exact pr18204693623
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1895821019395970170536007797191` is prime. -/
private theorem pr1895821019395970170536007797191 : (1895821019395970170536007797191).Prime := by
  refine lucas_of_list 1895821019395970170536007797191 13 [2, 5, 17, 41, 127, 2141710841057818288204801] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2141710841057818288204801
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2185252366777507749568966192253` is prime. -/
private theorem pr2185252366777507749568966192253 : (2185252366777507749568966192253).Prime := by
  refine lucas_of_list 2185252366777507749568966192253 2 [2, 2, 19828649, 27551705196575769604487] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr19828649
    · exact pr27551705196575769604487
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `2396728248024813875839125734059` is prime. -/
private theorem pr2396728248024813875839125734059 : (2396728248024813875839125734059).Prime := by
  refine lucas_of_list 2396728248024813875839125734059 2 [2, 3, 3, 7, 21529427, 883518765367127393929] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr21529427
    · exact pr883518765367127393929
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2831405074683436646283538151531` is prime. -/
private theorem pr2831405074683436646283538151531 : (2831405074683436646283538151531).Prime := by
  refine lucas_of_list 2831405074683436646283538151531 6 [2, 5, 7, 6359, 69427, 484327, 189168169397789] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr189168169397789
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2914039367799838633448001262213` is prime. -/
private theorem pr2914039367799838633448001262213 : (2914039367799838633448001262213).Prime := by
  refine lucas_of_list 2914039367799838633448001262213 2 [2, 2, 3, 861591053, 281846721989254322167] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr861591053
    · exact pr281846721989254322167
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3669106119155315242775835456613` is prime. -/
private theorem pr3669106119155315242775835456613 : (3669106119155315242775835456613).Prime := by
  refine lucas_of_list 3669106119155315242775835456613 5 [2, 2, 3, 4583, 3784159, 17630303698054596683] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr17630303698054596683
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6460576870103706818150842258699` is prime. -/
private theorem pr6460576870103706818150842258699 : (6460576870103706818150842258699).Prime := by
  refine lucas_of_list 6460576870103706818150842258699 3 [2, 3, 17, 602333, 105156099570479055542803] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr105156099570479055542803
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7262704077927329713075679326819` is prime. -/
private theorem pr7262704077927329713075679326819 : (7262704077927329713075679326819).Prime := by
  refine lucas_of_list 7262704077927329713075679326819 3 [2, 3, 7, 18325387, 9436173198685322265767] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr18325387
    · exact pr9436173198685322265767
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10697380813384255535697285808421` is prime. -/
private theorem pr10697380813384255535697285808421 : (10697380813384255535697285808421).Prime := by
  refine lucas_of_list 10697380813384255535697285808421 2 [2, 2, 5, 29, 458861069, 40194649904100499421] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr458861069
    · exact pr40194649904100499421
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `11027369909708954800354643881351` is prime. -/
private theorem pr11027369909708954800354643881351 : (11027369909708954800354643881351).Prime := by
  refine lucas_of_list 11027369909708954800354643881351 3 [2, 3, 5, 5, 23, 991, 9743, 1057990333, 312899444027] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1057990333
    · exact pr312899444027
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `20080234442654907302619100313719` is prime. -/
private theorem pr20080234442654907302619100313719 : (20080234442654907302619100313719).Prime := by
  refine lucas_of_list 20080234442654907302619100313719 6 [2, 3, 103, 788789, 41192624063165237064659] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr41192624063165237064659
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `23310564992523328982518387439893` is prime. -/
private theorem pr23310564992523328982518387439893 : (23310564992523328982518387439893).Prime := by
  refine lucas_of_list 23310564992523328982518387439893 2 [2, 2, 3, 3, 7, 97, 1321, 10984123, 65722234366057721] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr10984123
    · exact pr65722234366057721
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `28489727874464217203701549572943` is prime. -/
private theorem pr28489727874464217203701549572943 : (28489727874464217203701549572943).Prime := by
  refine lucas_of_list 28489727874464217203701549572943 3 [2, 3, 2939, 113635369417, 14217522899257439] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr113635369417
    · exact pr14217522899257439
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `39872850421944789941639158909903` is prime. -/
private theorem pr39872850421944789941639158909903 : (39872850421944789941639158909903).Prime := by
  refine lucas_of_list 39872850421944789941639158909903 5 [2, 3, 283, 3583, 9127, 718066620513061610639] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr718066620513061610639
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `52350417608590745085532820483581` is prime. -/
private theorem pr52350417608590745085532820483581 : (52350417608590745085532820483581).Prime := by
  refine lucas_of_list 52350417608590745085532820483581 2 [2, 2, 3, 5, 41, 3847, 439771, 12578714787664099229] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12578714787664099229
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `78338063445872011517474274387791` is prime. -/
private theorem pr78338063445872011517474274387791 : (78338063445872011517474274387791).Prime := by
  refine lucas_of_list 78338063445872011517474274387791 17 [2, 5, 43, 3361, 6491, 24884605783, 335578005941] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr24884605783
    · exact pr335578005941
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `80320937770619629210476401254877` is prime. -/
private theorem pr80320937770619629210476401254877 : (80320937770619629210476401254877).Prime := by
  refine lucas_of_list 80320937770619629210476401254877 2 [2, 2, 20080234442654907302619100313719] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr20080234442654907302619100313719
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `85692346627744529504286372538769` is prime. -/
private theorem pr85692346627744529504286372538769 : (85692346627744529504286372538769).Prime := by
  refine lucas_of_list 85692346627744529504286372538769 3 [2, 2, 2, 2, 7, 1693, 451925716330607804743726123] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr451925716330607804743726123
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `97453457741583820275695295256043` is prime. -/
private theorem pr97453457741583820275695295256043 : (97453457741583820275695295256043).Prime := by
  refine lucas_of_list 97453457741583820275695295256043 2 [2, 113, 163, 7901837, 21181301, 15805946613607] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr21181301
    · exact pr15805946613607
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `161500955938333400145779886288853` is prime. -/
private theorem pr161500955938333400145779886288853 : (161500955938333400145779886288853).Prime := by
  refine lucas_of_list 161500955938333400145779886288853 5 [2, 2, 3, 3, 3, 7, 29, 7366400106656330968152704173] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr7366400106656330968152704173
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `193817306103111204544525267760971` is prime. -/
private theorem pr193817306103111204544525267760971 : (193817306103111204544525267760971).Prime := by
  refine lucas_of_list 193817306103111204544525267760971 7 [2, 3, 5, 6460576870103706818150842258699] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr6460576870103706818150842258699
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `230651967228289828054211208494561` is prime. -/
private theorem pr230651967228289828054211208494561 : (230651967228289828054211208494561).Prime := by
  refine lucas_of_list 230651967228289828054211208494561 3 [2, 2, 2, 2, 2, 5, 13, 131, 134399917, 6298302738844988441] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr134399917
    · exact pr6298302738844988441
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `267566513611201937534627046321373` is prime. -/
private theorem pr267566513611201937534627046321373 : (267566513611201937534627046321373).Prime := by
  refine lucas_of_list 267566513611201937534627046321373 2 [2, 2, 3, 3, 3, 37, 79, 863, 1109, 885598448701788237149] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr885598448701788237149
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `734411090819951174645617944217607` is prime. -/
private theorem pr734411090819951174645617944217607 : (734411090819951174645617944217607).Prime := by
  refine lucas_of_list 734411090819951174645617944217607 5 [2, 71, 79, 2917682857, 22438080793250320531] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr2917682857
    · exact pr22438080793250320531
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `924405967195141162109401193137291` is prime. -/
private theorem pr924405967195141162109401193137291 : (924405967195141162109401193137291).Prime := by
  refine lucas_of_list 924405967195141162109401193137291 2 [2, 3, 3, 5, 697026959, 14735696059755052093559] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr697026959
    · exact pr14735696059755052093559
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1824753539972745296906105548490393` is prime. -/
private theorem pr1824753539972745296906105548490393 : (1824753539972745296906105548490393).Prime := by
  refine lucas_of_list 1824753539972745296906105548490393 3 [2, 2, 2, 7, 1325083, 24590825361407890472118479] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr24590825361407890472118479
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3002906296784399476897803346063763` is prime. -/
private theorem pr3002906296784399476897803346063763 : (3002906296784399476897803346063763).Prime := by
  refine lucas_of_list 3002906296784399476897803346063763 2 [2, 330022844089, 4549543085530438019729] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · exact pr330022844089
    · exact pr4549543085530438019729
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `6477226743683174716571913068507497` is prime. -/
private theorem pr6477226743683174716571913068507497 : (6477226743683174716571913068507497).Prime := by
  refine lucas_of_list 6477226743683174716571913068507497 5 [2, 2, 2, 3, 3, 293, 720763, 204948187, 2078511436630121] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr204948187
    · exact pr2078511436630121
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `15499430385677316689550892501957469` is prime. -/
private theorem pr15499430385677316689550892501957469 : (15499430385677316689550892501957469).Prime := by
  refine lucas_of_list 15499430385677316689550892501957469 2 [2, 2, 41, 853, 110795687999866444754173880579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr110795687999866444754173880579
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `16113353454645652897012612804330619` is prime. -/
private theorem pr16113353454645652897012612804330619 : (16113353454645652897012612804330619).Prime := by
  refine lucas_of_list 16113353454645652897012612804330619 2 [2, 43063, 46387923041, 4033171858149485323] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr46387923041
    · exact pr4033171858149485323
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `37721461748156171027981431724172919` is prime. -/
private theorem pr37721461748156171027981431724172919 : (37721461748156171027981431724172919).Prime := by
  refine lucas_of_list 37721461748156171027981431724172919 15 [2, 3, 17, 103421, 4229971, 52141693, 16212765124043] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr52141693
    · exact pr16212765124043
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `108933064718755665533009062543512967` is prime. -/
private theorem pr108933064718755665533009062543512967 : (108933064718755665533009062543512967).Prime := by
  refine lucas_of_list 108933064718755665533009062543512967 7 [2, 3, 3, 53, 7633807, 14957884372838020959843697] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr14957884372838020959843697
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `412114970424412329181892219789694751` is prime. -/
private theorem pr412114970424412329181892219789694751 : (412114970424412329181892219789694751).Prime := by
  refine lucas_of_list 412114970424412329181892219789694751 6 [2, 3, 5, 5, 5, 61, 2147527, 57669660497, 72734635214027] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr57669660497
    · exact pr72734635214027
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1655061418833311493209534308533518401` is prime. -/
private theorem pr1655061418833311493209534308533518401 : (1655061418833311493209534308533518401).Prime := by
  refine lucas_of_list 1655061418833311493209534308533518401 11 [2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 233, 25183, 59377, 329890633641354363287] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr329890633641354363287
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2685385120412324672982362877986595521` is prime. -/
private theorem pr2685385120412324672982362877986595521 : (2685385120412324672982362877986595521).Prime := by
  refine lucas_of_list 2685385120412324672982362877986595521 3 [2, 2, 2, 2, 2, 2, 5, 761, 11027369909708954800354643881351] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11027369909708954800354643881351
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3915570154829806825801666726738001449` is prime. -/
private theorem pr3915570154829806825801666726738001449 : (3915570154829806825801666726738001449).Prime := by
  refine lucas_of_list 3915570154829806825801666726738001449 11 [2, 2, 2, 3, 13, 5743, 2185252366777507749568966192253] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2185252366777507749568966192253
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3959357435784181637973939692257520149` is prime. -/
private theorem pr3959357435784181637973939692257520149 : (3959357435784181637973939692257520149).Prime := by
  refine lucas_of_list 3959357435784181637973939692257520149 6 [2, 2, 3, 3, 3, 227, 161500955938333400145779886288853] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr161500955938333400145779886288853
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4576192381119365422751582036429895797` is prime. -/
private theorem pr4576192381119365422751582036429895797 : (4576192381119365422751582036429895797).Prime := by
  refine lucas_of_list 4576192381119365422751582036429895797 2 [2, 2, 71, 16113353454645652897012612804330619] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr16113353454645652897012612804330619
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `5370770240824649345964725755973191043` is prime. -/
private theorem pr5370770240824649345964725755973191043 : (5370770240824649345964725755973191043).Prime := by
  refine lucas_of_list 5370770240824649345964725755973191043 2 [2, 2685385120412324672982362877986595521] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr2685385120412324672982362877986595521
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `6738816244215335354992736689219393763` is prime. -/
private theorem pr6738816244215335354992736689219393763 : (6738816244215335354992736689219393763).Prime := by
  refine lucas_of_list 6738816244215335354992736689219393763 2 [2, 1259, 3388471, 789812704340304383349069829] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr789812704340304383349069829
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `50238507445403230551505030439079778673` is prime. -/
private theorem pr50238507445403230551505030439079778673 : (50238507445403230551505030439079778673).Prime := by
  refine lucas_of_list 50238507445403230551505030439079778673 3 [2, 2, 2, 2, 7, 53, 26777, 156999499, 2013180202438700904799] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr156999499
    · exact pr2013180202438700904799
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `100477014890806461103010060878159557347` is prime. -/
private theorem pr100477014890806461103010060878159557347 : (100477014890806461103010060878159557347).Prime := by
  refine lucas_of_list 100477014890806461103010060878159557347 2 [2, 50238507445403230551505030439079778673] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr50238507445403230551505030439079778673
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `312778505182968250795137010689501724421` is prime. -/
private theorem pr312778505182968250795137010689501724421 : (312778505182968250795137010689501724421).Prime := by
  refine lucas_of_list 312778505182968250795137010689501724421 3 [2, 2, 5, 1009, 15499430385677316689550892501957469] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr15499430385677316689550892501957469
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `425939975991248449282289579123620083989` is prime. -/
private theorem pr425939975991248449282289579123620083989 : (425939975991248449282289579123620083989).Prime := by
  refine lucas_of_list 425939975991248449282289579123620083989 3 [2, 2, 11, 3469, 519044884691, 5376337334771671650313] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr519044884691
    · exact pr5376337334771671650313
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1564149922740866819182700967858124796579` is prime. -/
private theorem pr1564149922740866819182700967858124796579 : (1564149922740866819182700967858124796579).Prime := by
  refine lucas_of_list 1564149922740866819182700967858124796579 2 [2, 7, 1801, 45538419582079, 1362255828628464151313] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr45538419582079
    · exact pr1362255828628464151313
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3533698000678703430294737811785691398399` is prime. -/
private theorem pr3533698000678703430294737811785691398399 : (3533698000678703430294737811785691398399).Prime := by
  refine lucas_of_list 3533698000678703430294737811785691398399 29 [2, 13, 17, 51944569, 153910062411705601645112038051] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr51944569
    · exact pr153910062411705601645112038051
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `52977049230617030708200696995923311616681` is prime. -/
private theorem pr52977049230617030708200696995923311616681 : (52977049230617030708200696995923311616681).Prime := by
  refine lucas_of_list 52977049230617030708200696995923311616681 15 [2, 2, 2, 5, 7, 368248043, 4643709938951, 110643065903853667] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr368248043
    · exact pr4643709938951
    · exact pr110643065903853667
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `65730830630574893677578879383078345920777` is prime. -/
private theorem pr65730830630574893677578879383078345920777 : (65730830630574893677578879383078345920777).Prime := by
  refine lucas_of_list 65730830630574893677578879383078345920777 10 [2, 2, 2, 3, 13, 47, 83, 883, 8447, 811627, 1657267373, 5383023947713] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1657267373
    · exact pr5383023947713
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `116203633402513533635693201606757936604699` is prime. -/
private theorem pr116203633402513533635693201606757936604699 : (116203633402513533635693201606757936604699).Prime := by
  refine lucas_of_list 116203633402513533635693201606757936604699 2 [2, 3, 991, 242491, 2245057, 453364581037, 79181590014127] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr453364581037
    · exact pr79181590014127
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `678195340223078331832355971258444747462523` is prime. -/
private theorem pr678195340223078331832355971258444747462523 : (678195340223078331832355971258444747462523).Prime := by
  refine lucas_of_list 678195340223078331832355971258444747462523 2 [2, 87433, 53325101004937, 72730695219214984781741] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr53325101004937
    · exact pr72730695219214984781741
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `744747847369451172337412667222529677118783` is prime. -/
private theorem pr744747847369451172337412667222529677118783 : (744747847369451172337412667222529677118783).Prime := by
  refine lucas_of_list 744747847369451172337412667222529677118783 3 [2, 3, 3, 3, 13, 641, 1655061418833311493209534308533518401] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1655061418833311493209534308533518401
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1099864590658222331156146009438844141746579` is prime. -/
private theorem pr1099864590658222331156146009438844141746579 : (1099864590658222331156146009438844141746579).Prime := by
  refine lucas_of_list 1099864590658222331156146009438844141746579 2 [2, 3, 3, 64531875143, 946874521071922737507641579447] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr64531875143
    · exact pr946874521071922737507641579447
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1377403279996042798413218121894006102033707` is prime. -/
private theorem pr1377403279996042798413218121894006102033707 : (1377403279996042798413218121894006102033707).Prime := by
  refine lucas_of_list 1377403279996042798413218121894006102033707 2 [2, 13, 52977049230617030708200696995923311616681] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr52977049230617030708200696995923311616681
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `2346340945937504799853769135456785605975491` is prime. -/
private theorem pr2346340945937504799853769135456785605975491 : (2346340945937504799853769135456785605975491).Prime := by
  refine lucas_of_list 2346340945937504799853769135456785605975491 2 [2, 5, 83, 6701, 176017, 2396728248024813875839125734059] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2396728248024813875839125734059
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3024542461993703675369260051802205186284713` is prime. -/
private theorem pr3024542461993703675369260051802205186284713 : (3024542461993703675369260051802205186284713).Prime := by
  refine lucas_of_list 3024542461993703675369260051802205186284713 5 [2, 2, 2, 3, 18701, 6738816244215335354992736689219393763] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr6738816244215335354992736689219393763
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4418904424034158555949547628088872244242033` is prime. -/
private theorem pr4418904424034158555949547628088872244242033 : (4418904424034158555949547628088872244242033).Prime := by
  refine lucas_of_list 4418904424034158555949547628088872244242033 7 [2, 2, 2, 2, 3, 503, 683, 53864553850831211, 4974868610361993331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr53864553850831211
    · exact pr4974868610361993331
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `5880919681558902168359178863198678891519911` is prime. -/
private theorem pr5880919681558902168359178863198678891519911 : (5880919681558902168359178863198678891519911).Prime := by
  refine lucas_of_list 5880919681558902168359178863198678891519911 6 [2, 3, 5, 1951, 100477014890806461103010060878159557347] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr100477014890806461103010060878159557347
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `38726888063211460961545458695571543210176717` is prime. -/
private theorem pr38726888063211460961545458695571543210176717 : (38726888063211460961545458695571543210176717).Prime := by
  refine lucas_of_list 38726888063211460961545458695571543210176717 2 [2, 2, 13, 744747847369451172337412667222529677118783] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr744747847369451172337412667222529677118783
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `47760295972115698520359286260186358504259559` is prime. -/
private theorem pr47760295972115698520359286260186358504259559 : (47760295972115698520359286260186358504259559).Prime := by
  refine lucas_of_list 47760295972115698520359286260186358504259559 3 [2, 3, 7, 11, 9895156140145319, 10447259502000162783907811] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9895156140145319
    · exact pr10447259502000162783907811
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `105013669757419869852725226123205617502082861` is prime. -/
private theorem pr105013669757419869852725226123205617502082861 : (105013669757419869852725226123205617502082861).Prime := by
  refine lucas_of_list 105013669757419869852725226123205617502082861 2 [2, 2, 5, 79, 34267, 83207, 23310564992523328982518387439893] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr23310564992523328982518387439893
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `940863774473943228707351737234941338605941911` is prime. -/
private theorem pr940863774473943228707351737234941338605941911 : (940863774473943228707351737234941338605941911).Prime := by
  refine lucas_of_list 940863774473943228707351737234941338605941911 7 [2, 5, 7, 47595099254663, 282401156303852819552097999551] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr47595099254663
    · exact pr282401156303852819552097999551
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `953683760031953443637022062659241798656170347` is prime. -/
private theorem pr953683760031953443637022062659241798656170347 : (953683760031953443637022062659241798656170347).Prime := by
  refine lucas_of_list 953683760031953443637022062659241798656170347 2 [2, 44575573061713, 10697380813384255535697285808421] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · exact pr44575573061713
    · exact pr10697380813384255535697285808421
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `1154982302343889994965525813119887125281908153` is prime. -/
private theorem pr1154982302343889994965525813119887125281908153 : (1154982302343889994965525813119887125281908153).Prime := by
  refine lucas_of_list 1154982302343889994965525813119887125281908153 3 [2, 2, 2, 383, 587, 6704479765807211, 95781885718202172715249] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr6704479765807211
    · exact pr95781885718202172715249
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10729638155956753593075113484607173326729375941` is prime. -/
private theorem pr10729638155956753593075113484607173326729375941 : (10729638155956753593075113484607173326729375941).Prime := by
  refine lucas_of_list 10729638155956753593075113484607173326729375941 6 [2, 2, 3, 5, 7, 160441153, 23831345513, 6681461160575807765631713] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr160441153
    · exact pr23831345513
    · exact pr6681461160575807765631713
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `52544935615250625703566376027972985388841637197` is prime. -/
private theorem pr52544935615250625703566376027972985388841637197 : (52544935615250625703566376027972985388841637197).Prime := by
  refine lucas_of_list 52544935615250625703566376027972985388841637197 2 [2, 2, 3, 3, 59, 26959, 1226271900451500011, 748317318635326820621] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1226271900451500011
    · exact pr748317318635326820621
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `69970292000742953289148342118051975969909802271` is prime. -/
private theorem pr69970292000742953289148342118051975969909802271 : (69970292000742953289148342118051975969909802271).Prime := by
  refine lucas_of_list 69970292000742953289148342118051975969909802271 3 [2, 3, 5, 6594009211, 10365220559, 34124345809441049514408541] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr6594009211
    · exact pr10365220559
    · exact pr34124345809441049514408541
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `242581577139639899359795272344604976429811408911` is prime. -/
private theorem pr242581577139639899359795272344604976429811408911 : (242581577139639899359795272344604976429811408911).Prime := by
  refine lucas_of_list 242581577139639899359795272344604976429811408911 11 [2, 3, 5, 7, 11, 105013669757419869852725226123205617502082861] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr105013669757419869852725226123205617502082861
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3449187430720993974895674156987305660643816469163` is prime. -/
private theorem pr3449187430720993974895674156987305660643816469163 : (3449187430720993974895674156987305660643816469163).Prime := by
  refine lucas_of_list 3449187430720993974895674156987305660643816469163 2 [2, 41, 2348491, 4784467, 2472615770087, 1513992919016165401019] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2472615770087
    · exact pr1513992919016165401019
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6902650306217171084728193212909805761734079621529` is prime. -/
private theorem pr6902650306217171084728193212909805761734079621529 : (6902650306217171084728193212909805761734079621529).Prime := by
  refine lucas_of_list 6902650306217171084728193212909805761734079621529 3 [2, 2, 2, 6221, 3040619457363130437577, 45614572983907197148423] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3040619457363130437577
    · exact pr45614572983907197148423
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `299557821746197994748460882884788253840787746091079` is prime. -/
private theorem pr299557821746197994748460882884788253840787746091079 : (299557821746197994748460882884788253840787746091079).Prime := by
  refine lucas_of_list 299557821746197994748460882884788253840787746091079 11 [2, 11, 100411, 5178919, 2722122253, 9619000479999082942481892337] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2722122253
    · exact pr9619000479999082942481892337
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2466389430424272624575924487811306129214143786281097` is prime. -/
private theorem pr2466389430424272624575924487811306129214143786281097 : (2466389430424272624575924487811306129214143786281097).Prime := by
  refine lucas_of_list 2466389430424272624575924487811306129214143786281097 15 [2, 2, 2, 3, 2683, 457153, 2221159, 37721461748156171027981431724172919] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr37721461748156171027981431724172919
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `14469354272753159238990461610612005872345071289912781` is prime. -/
private theorem pr14469354272753159238990461610612005872345071289912781 : (14469354272753159238990461610612005872345071289912781).Prime := by
  refine lucas_of_list 14469354272753159238990461610612005872345071289912781 2 [2, 2, 5, 19, 29, 113, 8761, 107123, 234702103, 52751610625449532220312726917] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr234702103
    · exact pr52751610625449532220312726917
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `28938708545506318477980923221224011744690142579825563` is prime. -/
private theorem pr28938708545506318477980923221224011744690142579825563 : (28938708545506318477980923221224011744690142579825563).Prime := by
  refine lucas_of_list 28938708545506318477980923221224011744690142579825563 2 [2, 14469354272753159238990461610612005872345071289912781] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr14469354272753159238990461610612005872345071289912781
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `35372683796165971757494457776827620672400578749031261` is prime. -/
private theorem pr35372683796165971757494457776827620672400578749031261 : (35372683796165971757494457776827620672400578749031261).Prime := by
  refine lucas_of_list 35372683796165971757494457776827620672400578749031261 2 [2, 2, 5, 1854529, 953683760031953443637022062659241798656170347] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr953683760031953443637022062659241798656170347
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `502611116708176508031701956834201288749493791116306597` is prime. -/
private theorem pr502611116708176508031701956834201288749493791116306597 : (502611116708176508031701956834201288749493791116306597).Prime := by
  refine lucas_of_list 502611116708176508031701956834201288749493791116306597 2 [2, 2, 13, 41, 365699, 4664162059, 945070436021, 146245767985201734471473] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr4664162059
    · exact pr945070436021
    · exact pr146245767985201734471473
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4862667166503269178627968161051346822600953985461563503` is prime. -/
private theorem pr4862667166503269178627968161051346822600953985461563503 : (4862667166503269178627968161051346822600953985461563503).Prime := by
  refine lucas_of_list 4862667166503269178627968161051346822600953985461563503 5 [2, 126257, 9339993463, 86603861654270201, 23807031864678216915161] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr9339993463
    · exact pr86603861654270201
    · exact pr23807031864678216915161
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7794040558759131236694046107932833803593974496156372173` is prime. -/
private theorem pr7794040558759131236694046107932833803593974496156372173 : (7794040558759131236694046107932833803593974496156372173).Prime := by
  refine lucas_of_list 7794040558759131236694046107932833803593974496156372173 2 [2, 2, 3, 3, 23, 289297, 2956634677, 1405019647086019, 7832642975302929485459] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2956634677
    · exact pr1405019647086019
    · exact pr7832642975302929485459
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `12278220695869799283902702923485903093158153845103172551` is prime. -/
private theorem pr12278220695869799283902702923485903093158153845103172551 : (12278220695869799283902702923485903093158153845103172551).Prime := by
  refine lucas_of_list 12278220695869799283902702923485903093158153845103172551 14 [2, 5, 5, 7, 33331, 123449, 51062736476452083197, 166965747451764499398851] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr51062736476452083197
    · exact pr166965747451764499398851
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `47076173808161801279262577811156570674228344243298411301` is prime. -/
private theorem pr47076173808161801279262577811156570674228344243298411301 : (47076173808161801279262577811156570674228344243298411301).Prime := by
  refine lucas_of_list 47076173808161801279262577811156570674228344243298411301 3 [2, 2, 5, 5, 1493, 335131, 940863774473943228707351737234941338605941911] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr940863774473943228707351737234941338605941911
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `72956515876193792964056335658305728277140981281451136601` is prime. -/
private theorem pr72956515876193792964056335658305728277140981281451136601 : (72956515876193792964056335658305728277140981281451136601).Prime := by
  refine lucas_of_list 72956515876193792964056335658305728277140981281451136601 13 [2, 2, 2, 5, 5, 7, 571, 2909, 51270409, 31229592833, 87887482153, 222944156490058331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr51270409
    · exact pr31229592833
    · exact pr87887482153
    · exact pr222944156490058331
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `98888323088149046221501139805879066026526921639110942203` is prime. -/
private theorem pr98888323088149046221501139805879066026526921639110942203 : (98888323088149046221501139805879066026526921639110942203).Prime := by
  refine lucas_of_list 98888323088149046221501139805879066026526921639110942203 2 [2, 3, 3, 2153, 1287753136009443753814303, 1981508142283827480998194771] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1287753136009443753814303
    · exact pr1981508142283827480998194771
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `116537466984665627953034708176397463390432869374874257549` is prime. -/
private theorem pr116537466984665627953034708176397463390432869374874257549 : (116537466984665627953034708176397463390432869374874257549).Prime := by
  refine lucas_of_list 116537466984665627953034708176397463390432869374874257549 2 [2, 2, 3, 89, 241, 69901770934033393, 6477226743683174716571913068507497] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr69901770934033393
    · exact pr6477226743683174716571913068507497
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `402359867514801972109108239729572783015996038808088447169` is prime. -/
private theorem pr402359867514801972109108239729572783015996038808088447169 : (402359867514801972109108239729572783015996038808088447169).Prime := by
  refine lucas_of_list 402359867514801972109108239729572783015996038808088447169 7 [2, 2, 2, 2, 2, 2, 3, 43877959031, 47760295972115698520359286260186358504259559] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr43877959031
    · exact pr47760295972115698520359286260186358504259559
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1062885674841072459489414818970827139736118824610593743247` is prime. -/
private theorem pr1062885674841072459489414818970827139736118824610593743247 : (1062885674841072459489414818970827139736118824610593743247).Prime := by
  refine lucas_of_list 1062885674841072459489414818970827139736118824610593743247 3 [2, 3, 3, 7, 317257, 6440317084823, 925106424198984623, 4462783807057408057] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr6440317084823
    · exact pr925106424198984623
    · exact pr4462783807057408057
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1873565324598816063866500205904094545270190991085389153969` is prime. -/
private theorem pr1873565324598816063866500205904094545270190991085389153969 : (1873565324598816063866500205904094545270190991085389153969).Prime := by
  refine lucas_of_list 1873565324598816063866500205904094545270190991085389153969 3 [2, 2, 2, 2, 3257, 107558835773597899975051, 334260459649000270477156654889] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr107558835773597899975051
    · exact pr334260459649000270477156654889
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2877385295354769565837788842129924060314261381224638749213` is prime. -/
private theorem pr2877385295354769565837788842129924060314261381224638749213 : (2877385295354769565837788842129924060314261381224638749213).Prime := by
  refine lucas_of_list 2877385295354769565837788842129924060314261381224638749213 2 [2, 2, 3, 65351641560433344086222377, 3669106119155315242775835456613] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr65351641560433344086222377
    · exact pr3669106119155315242775835456613
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9339595112696398295496174845486309314598256949990725815653` is prime. -/
private theorem pr9339595112696398295496174845486309314598256949990725815653 : (9339595112696398295496174845486309314598256949990725815653).Prime := by
  refine lucas_of_list 9339595112696398295496174845486309314598256949990725815653 2 [2, 2, 3, 3, 13, 107, 4349, 2387351023727, 1336633773450893867, 13439412999494045647] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr2387351023727
    · exact pr1336633773450893867
    · exact pr13439412999494045647
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `15201432905196083562906601602721786837858186072775135552603` is prime. -/
private theorem pr15201432905196083562906601602721786837858186072775135552603 : (15201432905196083562906601602721786837858186072775135552603).Prime := by
  refine lucas_of_list 15201432905196083562906601602721786837858186072775135552603 2 [2, 7, 13, 19, 37, 67, 229, 7207, 304063, 3533698000678703430294737811785691398399] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3533698000678703430294737811785691398399
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `240446151237719198652011322429727922840874113206424081537051` is prime. -/
private theorem pr240446151237719198652011322429727922840874113206424081537051 : (240446151237719198652011322429727922840874113206424081537051).Prime := by
  refine lucas_of_list 240446151237719198652011322429727922840874113206424081537051 6 [2, 5, 5, 617, 7794040558759131236694046107932833803593974496156372173] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr7794040558759131236694046107932833803593974496156372173
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `362706832208205438254228368220240087421270981908773674097679` is prime. -/
private theorem pr362706832208205438254228368220240087421270981908773674097679 : (362706832208205438254228368220240087421270981908773674097679).Prime := by
  refine lucas_of_list 362706832208205438254228368220240087421270981908773674097679 7 [2, 61, 229, 365291935901, 569406979818597733, 62416232677071478843766407] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr365291935901
    · exact pr569406979818597733
    · exact pr62416232677071478843766407
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `733608319101651903111917349364209992100685813385229227247389` is prime. -/
private theorem pr733608319101651903111917349364209992100685813385229227247389 : (733608319101651903111917349364209992100685813385229227247389).Prime := by
  refine lucas_of_list 733608319101651903111917349364209992100685813385229227247389 2 [2, 2, 31, 131, 28873065043059313, 1564149922740866819182700967858124796579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr28873065043059313
    · exact pr1564149922740866819182700967858124796579
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2700367107603035640685154938861980817357334646492113611234921` is prime. -/
private theorem pr2700367107603035640685154938861980817357334646492113611234921 : (2700367107603035640685154938861980817357334646492113611234921).Prime := by
  refine lucas_of_list 2700367107603035640685154938861980817357334646492113611234921 7 [2, 2, 2, 3, 5, 1534921, 75641996375808912001, 193817306103111204544525267760971] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr75641996375808912001
    · exact pr193817306103111204544525267760971
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `4759585072922070618447077672994894518946958652763505407657947` is prime. -/
private theorem pr4759585072922070618447077672994894518946958652763505407657947 : (4759585072922070618447077672994894518946958652763505407657947).Prime := by
  refine lucas_of_list 4759585072922070618447077672994894518946958652763505407657947 2 [2, 13, 23, 47, 67, 2879, 12547, 69970292000742953289148342118051975969909802271] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr69970292000742953289148342118051975969909802271
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `22894742585238618558768944086717129905554145608409226289231791` is prime. -/
private theorem pr22894742585238618558768944086717129905554145608409226289231791 : (22894742585238618558768944086717129905554145608409226289231791).Prime := by
  refine lucas_of_list 22894742585238618558768944086717129905554145608409226289231791 7 [2, 3, 3, 5, 220251018746027, 1154982302343889994965525813119887125281908153] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr220251018746027
    · exact pr1154982302343889994965525813119887125281908153
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `23745962129962148394257714789277705957807205236868975737393319` is prime. -/
private theorem pr23745962129962148394257714789277705957807205236868975737393319 : (23745962129962148394257714789277705957807205236868975737393319).Prime := by
  refine lucas_of_list 23745962129962148394257714789277705957807205236868975737393319 3 [2, 3, 3, 1229, 16963, 231559, 5220125027436647, 52350417608590745085532820483581] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5220125027436647
    · exact pr52350417608590745085532820483581
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `488584990641815147167821406930488475169798294444325086198732677` is prime. -/
private theorem pr488584990641815147167821406930488475169798294444325086198732677 : (488584990641815147167821406930488475169798294444325086198732677).Prime := by
  refine lucas_of_list 488584990641815147167821406930488475169798294444325086198732677 2 [2, 2, 3, 3, 23, 23, 43, 439, 347593817, 25417220552692245857, 153832774372503129547869733] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr347593817
    · exact pr25417220552692245857
    · exact pr153832774372503129547869733
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7038294985091189274108843635204547554077540708191839200002594979` is prime. -/
private theorem pr7038294985091189274108843635204547554077540708191839200002594979 : (7038294985091189274108843635204547554077540708191839200002594979).Prime := by
  refine lucas_of_list 7038294985091189274108843635204547554077540708191839200002594979 3 [2, 3, 19, 71, 4751, 28961, 1610668957438324017996239, 3923732503437934896722585503] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1610668957438324017996239
    · exact pr3923732503437934896722585503
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `16128507032749352725307363163755968196418058977345819608639920939` is prime. -/
private theorem pr16128507032749352725307363163755968196418058977345819608639920939 : (16128507032749352725307363163755968196418058977345819608639920939).Prime := by
  refine lucas_of_list 16128507032749352725307363163755968196418058977345819608639920939 3 [2, 3, 43, 43, 19927, 72956515876193792964056335658305728277140981281451136601] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr72956515876193792964056335658305728277140981281451136601
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `31373845400456053491709001473732135590986614506854673896933034931` is prime. -/
private theorem pr31373845400456053491709001473732135590986614506854673896933034931 : (31373845400456053491709001473732135590986614506854673896933034931).Prime := by
  refine lucas_of_list 31373845400456053491709001473732135590986614506854673896933034931 10 [2, 3, 5, 11, 230096119521941, 421359165309683, 10384319362547701, 94430879944479007] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr230096119521941
    · exact pr421359165309683
    · exact pr10384319362547701
    · exact pr94430879944479007
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `537603718971126540592567204047301612088726211624567805565089155487` is prime. -/
private theorem pr537603718971126540592567204047301612088726211624567805565089155487 : (537603718971126540592567204047301612088726211624567805565089155487).Prime := by
  refine lucas_of_list 537603718971126540592567204047301612088726211624567805565089155487 3 [2, 3, 3, 17, 3499, 69135092205651805980861073351, 7262704077927329713075679326819] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr69135092205651805980861073351
    · exact pr7262704077927329713075679326819
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7201436315176075089609839897367476691048104462476615413533065021739` is prime. -/
private theorem pr7201436315176075089609839897367476691048104462476615413533065021739 : (7201436315176075089609839897367476691048104462476615413533065021739).Prime := by
  refine lucas_of_list 7201436315176075089609839897367476691048104462476615413533065021739 2 [2, 1051, 225373, 15201432905196083562906601602721786837858186072775135552603] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr15201432905196083562906601602721786837858186072775135552603
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `21611626709292047953692709004258975803177567316341638237479157522509` is prime. -/
private theorem pr21611626709292047953692709004258975803177567316341638237479157522509 : (21611626709292047953692709004258975803177567316341638237479157522509).Prime := by
  refine lucas_of_list 21611626709292047953692709004258975803177567316341638237479157522509 2 [2, 2, 673429, 102414823347778104187269761993, 78338063445872011517474274387791] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr102414823347778104187269761993
    · exact pr78338063445872011517474274387791
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1679046988346873026146887221139362418417358968325633914812660916662337` is prime. -/
private theorem pr1679046988346873026146887221139362418417358968325633914812660916662337 : (1679046988346873026146887221139362418417358968325633914812660916662337).Prime := by
  refine lucas_of_list 1679046988346873026146887221139362418417358968325633914812660916662337 3 [2, 2, 2, 2, 2, 2, 7, 31, 4826688001, 10389832997, 32482216254667088931641, 74219785556488562618461] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr4826688001
    · exact pr10389832997
    · exact pr32482216254667088931641
    · exact pr74219785556488562618461
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3728235385612593906219464253122105959350970167631344433874698554925829` is prime. -/
private theorem pr3728235385612593906219464253122105959350970167631344433874698554925829 : (3728235385612593906219464253122105959350970167631344433874698554925829).Prime := by
  refine lucas_of_list 3728235385612593906219464253122105959350970167631344433874698554925829 3 [2, 2, 37, 113, 479, 49831, 9339595112696398295496174845486309314598256949990725815653] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9339595112696398295496174845486309314598256949990725815653
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9312212619263090917897138723002602408981303378170047237550347786432331` is prime. -/
private theorem pr9312212619263090917897138723002602408981303378170047237550347786432331 : (9312212619263090917897138723002602408981303378170047237550347786432331).Prime := by
  refine lucas_of_list 9312212619263090917897138723002602408981303378170047237550347786432331 2 [2, 3, 5, 7, 19, 3697, 3177474093709, 525372998720231, 916054440512669, 412818817755914888561] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3177474093709
    · exact pr525372998720231
    · exact pr916054440512669
    · exact pr412818817755914888561
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `10621128142373409499195583622724658327733520284359846116039668724274497` is prime. -/
private theorem pr10621128142373409499195583622724658327733520284359846116039668724274497 : (10621128142373409499195583622724658327733520284359846116039668724274497).Prime := by
  refine lucas_of_list 10621128142373409499195583622724658327733520284359846116039668724274497 5 [2, 2, 2, 2, 2, 2, 3, 3, 11, 5557, 507301, 11316666059, 52544935615250625703566376027972985388841637197] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11316666059
    · exact pr52544935615250625703566376027972985388841637197
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `84473155511516801699753296603537882978672072906944063728424320294815297` is prime. -/
private theorem pr84473155511516801699753296603537882978672072906944063728424320294815297 : (84473155511516801699753296603537882978672072906944063728424320294815297).Prime := by
  refine lucas_of_list 84473155511516801699753296603537882978672072906944063728424320294815297 7 [2, 2, 2, 2, 2, 2, 3, 38699, 71693, 154459, 45534680017, 22451786674411, 1004233205235910075995966480773] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr45534680017
    · exact pr22451786674411
    · exact pr1004233205235910075995966480773
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `3240649991503555639428204275604905638325493575603176438667521029678451189` is prime. -/
private theorem pr3240649991503555639428204275604905638325493575603176438667521029678451189 : (3240649991503555639428204275604905638325493575603176438667521029678451189).Prime := by
  refine lucas_of_list 3240649991503555639428204275604905638325493575603176438667521029678451189 2 [2, 2, 3, 29, 9312212619263090917897138723002602408981303378170047237550347786432331] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9312212619263090917897138723002602408981303378170047237550347786432331
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `7938941841766738918493466332180163194506386206940387117250400242128671627` is prime. -/
private theorem pr7938941841766738918493466332180163194506386206940387117250400242128671627 : (7938941841766738918493466332180163194506386206940387117250400242128671627).Prime := by
  refine lucas_of_list 7938941841766738918493466332180163194506386206940387117250400242128671627 2 [2, 1027602571, 656843935516215991673, 5880919681558902168359178863198678891519911] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · exact pr1027602571
    · exact pr656843935516215991673
    · exact pr5880919681558902168359178863198678891519911
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `47633651050600433510960797993080979167038317241642322703502401452772029763` is prime. -/
private theorem pr47633651050600433510960797993080979167038317241642322703502401452772029763 : (47633651050600433510960797993080979167038317241642322703502401452772029763).Prime := by
  refine lucas_of_list 47633651050600433510960797993080979167038317241642322703502401452772029763 5 [2, 3, 7938941841766738918493466332180163194506386206940387117250400242128671627] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr7938941841766738918493466332180163194506386206940387117250400242128671627
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `287133344003252864260928865034032319529444417564748776037457268398692795961` is prime. -/
private theorem pr287133344003252864260928865034032319529444417564748776037457268398692795961 : (287133344003252864260928865034032319529444417564748776037457268398692795961).Prime := by
  refine lucas_of_list 287133344003252864260928865034032319529444417564748776037457268398692795961 7 [2, 2, 2, 3, 5, 23, 1811, 1831, 31373845400456053491709001473732135590986614506854673896933034931] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr31373845400456053491709001473732135590986614506854673896933034931
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `632990951087576550218441577609987341766987146003149705045875451683776895053` is prime. -/
private theorem pr632990951087576550218441577609987341766987146003149705045875451683776895053 : (632990951087576550218441577609987341766987146003149705045875451683776895053).Prime := by
  refine lucas_of_list 632990951087576550218441577609987341766987146003149705045875451683776895053 2 [2, 2, 7, 479, 11719, 828206926003, 4862667166503269178627968161051346822600953985461563503] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr828206926003
    · exact pr4862667166503269178627968161051346822600953985461563503
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1076816245108724712233609143583394882224298942700903835752063578872374793467` is prime. -/
private theorem pr1076816245108724712233609143583394882224298942700903835752063578872374793467 : (1076816245108724712233609143583394882224298942700903835752063578872374793467).Prime := by
  refine lucas_of_list 1076816245108724712233609143583394882224298942700903835752063578872374793467 3 [2, 3, 7, 7, 599, 7331, 1996343, 305861654093, 482438575255746299, 2831405074683436646283538151531] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr305861654093
    · exact pr482438575255746299
    · exact pr2831405074683436646283538151531
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `6804993587313637538011336005449854012446026441548504005500400464791812204863` is prime. -/
private theorem pr6804993587313637538011336005449854012446026441548504005500400464791812204863 : (6804993587313637538011336005449854012446026441548504005500400464791812204863).Prime := by
  refine lucas_of_list 6804993587313637538011336005449854012446026441548504005500400464791812204863 5 [2, 6329005313, 537603718971126540592567204047301612088726211624567805565089155487] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · norm_num
    · exact pr6329005313
    · exact pr537603718971126540592567204047301612088726211624567805565089155487
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · decide
    · decide

/-- `17952410985912354799368682030333023617030357390433258217612699495181423124703` is prime. -/
private theorem pr17952410985912354799368682030333023617030357390433258217612699495181423124703 : (17952410985912354799368682030333023617030357390433258217612699495181423124703).Prime := by
  refine lucas_of_list 17952410985912354799368682030333023617030357390433258217612699495181423124703 5 [2, 3, 3, 127, 293, 85692346627744529504286372538769, 312778505182968250795137010689501724421] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr85692346627744529504286372538769
    · exact pr312778505182968250795137010689501724421
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `21651079410133137758242128758752980815211510601393464207301965097681170881071` is prime. -/
private theorem pr21651079410133137758242128758752980815211510601393464207301965097681170881071 : (21651079410133137758242128758752980815211510601393464207301965097681170881071).Prime := by
  refine lucas_of_list 21651079410133137758242128758752980815211510601393464207301965097681170881071 3 [2, 3, 5, 292615042094260586161777, 2466389430424272624575924487811306129214143786281097] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr292615042094260586161777
    · exact pr2466389430424272624575924487811306129214143786281097
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `155309047950935806763197823001019084235723449740190964048085928878151671716881523` is prime. -/
private theorem pr155309047950935806763197823001019084235723449740190964048085928878151671716881523 : (155309047950935806763197823001019084235723449740190964048085928878151671716881523).Prime := by
  refine lucas_of_list 155309047950935806763197823001019084235723449740190964048085928878151671716881523 2 [2, 42571, 6935507071, 38102969119615549, 6902650306217171084728193212909805761734079621529] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr6935507071
    · exact pr38102969119615549
    · exact pr6902650306217171084728193212909805761734079621529
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `1413702781295101713257352953733477645621197570697664471397360264047107833843960893` is prime. -/
private theorem pr1413702781295101713257352953733477645621197570697664471397360264047107833843960893 : (1413702781295101713257352953733477645621197570697664471397360264047107833843960893).Prime := by
  refine lucas_of_list 1413702781295101713257352953733477645621197570697664471397360264047107833843960893 5 [2, 2, 3, 3, 29, 43, 281, 307, 8539, 12503, 8619557693, 4938663849193098822719, 80320937770619629210476401254877] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr8619557693
    · exact pr4938663849193098822719
    · exact pr80320937770619629210476401254877
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `9419375561335912358362027106137052856354993658405403330597004732765250793229164459` is prime. -/
private theorem pr9419375561335912358362027106137052856354993658405403330597004732765250793229164459 : (9419375561335912358362027106137052856354993658405403330597004732765250793229164459).Prime := by
  refine lucas_of_list 9419375561335912358362027106137052856354993658405403330597004732765250793229164459 2 [2, 211, 186419181996451, 39872850421944789941639158909903, 3002906296784399476897803346063763] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr186419181996451
    · exact pr39872850421944789941639158909903
    · exact pr3002906296784399476897803346063763
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `93004568384399041680927367152274519724408862963348759691076025654380143152631657267` is prime. -/
private theorem pr93004568384399041680927367152274519724408862963348759691076025654380143152631657267 : (93004568384399041680927367152274519724408862963348759691076025654380143152631657267).Prime := by
  refine lucas_of_list 93004568384399041680927367152274519724408862963348759691076025654380143152631657267 3 [2, 3, 49374739, 167563482700358321, 1873565324598816063866500205904094545270190991085389153969] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr49374739
    · exact pr167563482700358321
    · exact pr1873565324598816063866500205904094545270190991085389153969
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `706331413524551373602699881195056245170458960025879982991539562328802923646986860823` is prime. -/
private theorem pr706331413524551373602699881195056245170458960025879982991539562328802923646986860823 : (706331413524551373602699881195056245170458960025879982991539562328802923646986860823).Prime := by
  refine lucas_of_list 706331413524551373602699881195056245170458960025879982991539562328802923646986860823 3 [2, 3, 89, 349, 4233477553, 311133343753, 2877385295354769565837788842129924060314261381224638749213] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr4233477553
    · exact pr311133343753
    · exact pr2877385295354769565837788842129924060314261381224638749213
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091` is prime. -/
private theorem pr2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091 : (2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091).Prime := by
  refine lucas_of_list 2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091 2 [2, 5, 193, 18863753, 37482791, 20246808290977, 98888323088149046221501139805879066026526921639110942203] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr18863753
    · exact pr37482791
    · exact pr20246808290977
    · exact pr98888323088149046221501139805879066026526921639110942203
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769` is prime. -/
private theorem pr499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769 : (499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769).Prime := by
  refine lucas_of_list 499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769 3 [2, 2, 2, 13, 2809019, 71800474063579, 145147724148466807, 17261227208636271758719, 9514210957160511212466547249] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr71800474063579
    · exact pr145147724148466807
    · exact pr17261227208636271758719
    · exact pr9514210957160511212466547249
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019 2 [2, 2239816076104753, 745207098227029371724807, 299557821746197994748460882884788253840787746091079] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · exact pr2239816076104753
    · exact pr745207098227029371724807
    · exact pr299557821746197994748460882884788253840787746091079
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133 2 [2, 2, 43, 11148619, 20191382989, 548634678168341, 47076173808161801279262577811156570674228344243298411301] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr11148619
    · exact pr20191382989
    · exact pr548634678168341
    · exact pr47076173808161801279262577811156570674228344243298411301
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201 26 [2, 2, 2, 3, 3, 3, 5, 5, 73, 21611, 31485108379, 3728235385612593906219464253122105959350970167631344433874698554925829] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr31485108379
    · exact pr3728235385612593906219464253122105959350970167631344433874698554925829
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369 11 [2, 2, 2, 2, 2, 3, 20129, 939317, 6521923, 84473155511516801699753296603537882978672072906944063728424320294815297] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr84473155511516801699753296603537882978672072906944063728424320294815297
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763 2 [2, 4100939, 72614582527967, 1679046988346873026146887221139362418417358968325633914812660916662337] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr72614582527967
    · exact pr1679046988346873026146887221139362418417358968325633914812660916662337
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069 2 [2, 2, 11546768420377, 21651079410133137758242128758752980815211510601393464207301965097681170881071] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr11546768420377
    · exact pr21651079410133137758242128758752980815211510601393464207301965097681170881071
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093 2 [2, 2, 17, 10704557, 60004887147455085487, 22894742585238618558768944086717129905554145608409226289231791] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr10704557
    · exact pr60004887147455085487
    · exact pr22894742585238618558768944086717129905554145608409226289231791
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419 2 [2, 3, 11, 19, 1129, 706331413524551373602699881195056245170458960025879982991539562328802923646986860823] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr706331413524551373602699881195056245170458960025879982991539562328802923646986860823
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591 17 [2, 5, 15907, 2625449, 22083617, 16771119123133, 1203758338357956872531, 5370770240824649345964725755973191043] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr22083617
    · exact pr16771119123133
    · exact pr1203758338357956872531
    · exact pr5370770240824649345964725755973191043
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651 2 [2, 5, 5, 419871237221651, 47633651050600433510960797993080979167038317241642322703502401452772029763] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr419871237221651
    · exact pr47633651050600433510960797993080979167038317241642322703502401452772029763
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747 2 [2, 7, 59, 181, 43067, 155309047950935806763197823001019084235723449740190964048085928878151671716881523] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr155309047950935806763197823001019084235723449740190964048085928878151671716881523
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161 3 [2, 2, 2, 2, 2, 5, 79, 149, 103529, 482874187, 10621128142373409499195583622724658327733520284359846116039668724274497] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr482874187
    · exact pr10621128142373409499195583622724658327733520284359846116039668724274497
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541 2 [2, 2, 3, 3, 5, 11, 43, 163, 250954577, 287133344003252864260928865034032319529444417564748776037457268398692795961] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr250954577
    · exact pr287133344003252864260928865034032319529444417564748776037457268398692795961
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739 3 [2, 3, 3, 3, 3, 3, 11, 11, 97, 5231, 1228547, 7908849942063650934920749, 3449187430720993974895674156987305660643816469163] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr7908849942063650934920749
    · exact pr3449187430720993974895674156987305660643816469163
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839 7 [2, 7, 229, 317, 54809323, 17952410985912354799368682030333023617030357390433258217612699495181423124703] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr54809323
    · exact pr17952410985912354799368682030333023617030357390433258217612699495181423124703
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953 3 [2, 2, 2, 109, 909113, 78211655574940513, 16128507032749352725307363163755968196418058977345819608639920939] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr78211655574940513
    · exact pr16128507032749352725307363163755968196418058977345819608639920939
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039 3 [2, 3, 31, 792009763, 234572650351990225479606307, 28938708545506318477980923221224011744690142579825563] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr792009763
    · exact pr234572650351990225479606307
    · exact pr28938708545506318477980923221224011744690142579825563
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241 3 [2, 2, 2, 5, 26029, 3959357435784181637973939692257520149, 242581577139639899359795272344604976429811408911] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr3959357435784181637973939692257520149
    · exact pr242581577139639899359795272344604976429811408911
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571 2 [2, 5, 23, 29, 27481, 8618747, 632990951087576550218441577609987341766987146003149705045875451683776895053] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr632990951087576550218441577609987341766987146003149705045875451683776895053
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721 6 [2, 2, 2, 5, 7, 31, 41, 61, 461, 136207621785848300351, 733608319101651903111917349364209992100685813385229227247389] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr136207621785848300351
    · exact pr733608319101651903111917349364209992100685813385229227247389
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167 5 [2, 3, 1789, 13236432347084098236031, 7038294985091189274108843635204547554077540708191839200002594979] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr13236432347084098236031
    · exact pr7038294985091189274108843635204547554077540708191839200002594979
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219 2 [2, 557573, 1909241, 30956819, 3663362741, 4731360071, 191285033313581, 4576192381119365422751582036429895797] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr30956819
    · exact pr3663362741
    · exact pr4731360071
    · exact pr191285033313581
    · exact pr4576192381119365422751582036429895797
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521 7 [2, 2, 2, 3, 3, 3, 3, 5, 11, 157, 6949, 36629, 1325436053, 257556785377223992213, 299305777708221457297, 6871766633593002730621793] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1325436053
    · exact pr257556785377223992213
    · exact pr299305777708221457297
    · exact pr6871766633593002730621793
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137 3 [2, 2, 2, 2, 2, 2, 11, 29, 97453457741583820275695295256043, 502611116708176508031701956834201288749493791116306597] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr97453457741583820275695295256043
    · exact pr502611116708176508031701956834201288749493791116306597
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151 12 [2, 3, 3, 5, 5, 179, 84509, 218339699, 19020887347038226103, 35372683796165971757494457776827620672400578749031261] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr218339699
    · exact pr19020887347038226103
    · exact pr35372683796165971757494457776827620672400578749031261
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187 3 [2, 3, 3, 7549, 30097, 75454081, 3240649991503555639428204275604905638325493575603176438667521029678451189] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr75454081
    · exact pr3240649991503555639428204275604905638325493575603176438667521029678451189
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251 10 [2, 5, 5, 5, 13, 5407, 1478251, 193663667, 1824753539972745296906105548490393, 108933064718755665533009062543512967] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr193663667
    · exact pr1824753539972745296906105548490393
    · exact pr108933064718755665533009062543512967
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307 2 [2, 3, 61, 2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr2732240437158469945355191256830601092896174863387978142076502732240437158469945355191091
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331 10 [2, 3, 3, 3, 3, 5, 7, 7, 18493, 111053, 902160289, 191509382975357539, 13052601752489221206953, 5440143870742166955326084591] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr902160289
    · exact pr191509382975357539
    · exact pr13052601752489221206953
    · exact pr5440143870742166955326084591
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539 2 [2, 499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · norm_num
    · exact pr499999999999999999999999999999999999999999999999999999999999999999999999999999999999969769
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907 2 [2, 3, 3, 11, 101, 374347, 949153, 12334241, 2914039367799838633448001262213, 3915570154829806825801666726738001449] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr12334241
    · exact pr2914039367799838633448001262213
    · exact pr3915570154829806825801666726738001449
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923 2 [2, 6263, 80320879, 192221037521, 78666368577342976408244729, 65730830630574893677578879383078345920777] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact pr80320879
    · exact pr192221037521
    · exact pr78666368577342976408244729
    · exact pr65730830630574893677578879383078345920777
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129 13 [2, 2, 2, 2, 2, 3, 7, 206638672199221437191, 7201436315176075089609839897367476691048104462476615413533065021739] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr206638672199221437191
    · exact pr7201436315176075089609839897367476691048104462476615413533065021739
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229 2 [2, 2, 32069, 169114769, 4407712336771, 2366710855645183442959, 4418904424034158555949547628088872244242033] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr169114769
    · exact pr4407712336771
    · exact pr2366710855645183442959
    · exact pr4418904424034158555949547628088872244242033
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487 5 [2, 461, 217829, 20150267, 2120347301714756509, 116537466984665627953034708176397463390432869374874257549] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr20150267
    · exact pr2120347301714756509
    · exact pr116537466984665627953034708176397463390432869374874257549
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111 26 [2, 5, 17, 7159, 744728227, 28489727874464217203701549572943, 38726888063211460961545458695571543210176717] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr744728227
    · exact pr28489727874464217203701549572943
    · exact pr38726888063211460961545458695571543210176717
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173 2 [2, 2, 3, 77388629408093, 1076816245108724712233609143583394882224298942700903835752063578872374793467] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr77388629408093
    · exact pr1076816245108724712233609143583394882224298942700903835752063578872374793467
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191 11 [2, 3, 5, 33503, 1444501, 3583793, 477660828715223, 402359867514801972109108239729572783015996038808088447169] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr477660828715223
    · exact pr402359867514801972109108239729572783015996038808088447169
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201 6 [2, 2, 2, 2, 5, 5, 13, 97, 416539151747554478703059, 4759585072922070618447077672994894518946958652763505407657947] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr416539151747554478703059
    · exact pr4759585072922070618447077672994894518946958652763505407657947
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299 7 [2, 3, 179, 10597, 66477995159, 436993708880564593139454644323, 3024542461993703675369260051802205186284713] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr66477995159
    · exact pr436993708880564593139454644323
    · exact pr3024542461993703675369260051802205186284713
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363 2 [2, 937, 8819893, 294564827, 566279021177, 362706832208205438254228368220240087421270981908773674097679] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr294564827
    · exact pr566279021177
    · exact pr362706832208205438254228368220240087421270981908773674097679
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753 3 [2, 2, 2, 7, 1949, 6481, 1413702781295101713257352953733477645621197570697664471397360264047107833843960893] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1413702781295101713257352953733477645621197570697664471397360264047107833843960893
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301 6 [2, 2, 3, 3, 3, 5, 5, 17, 71, 779323591693, 924405967195141162109401193137291, 425939975991248449282289579123620083989] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr779323591693
    · exact pr924405967195141162109401193137291
    · exact pr425939975991248449282289579123620083989
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421 6 [2, 2, 3, 5, 1813223, 5921891, 144661193821913382604745497139, 10729638155956753593075113484607173326729375941] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr144661193821913382604745497139
    · exact pr10729638155956753593075113484607173326729375941
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437 2 [2, 2, 11, 17, 249233, 1986415282087976566499, 2700367107603035640685154938861980817357334646492113611234921] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1986415282087976566499
    · exact pr2700367107603035640685154938861980817357334646492113611234921
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701 2 [2, 2, 5, 5, 11, 67, 134248599246871, 73377284623470428818606905343, 1377403279996042798413218121894006102033707] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr134248599246871
    · exact pr73377284623470428818606905343
    · exact pr1377403279996042798413218121894006102033707
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731 2 [2, 5, 179, 3637, 6599, 15731, 6524021120954317, 1951794736996274813, 116203633402513533635693201606757936604699] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr6524021120954317
    · exact pr1951794736996274813
    · exact pr116203633402513533635693201606757936604699
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769 17 [2, 2, 2, 2, 3, 3, 23, 283, 373, 670429151471, 1818320332620503848001878811, 2346340945937504799853769135456785605975491] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr670429151471
    · exact pr1818320332620503848001878811
    · exact pr2346340945937504799853769135456785605975491
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183 3 [2, 3, 3, 23, 137, 47848291, 30010776026931432629789, 12278220695869799283902702923485903093158153845103172551] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr47848291
    · exact pr30010776026931432629789
    · exact pr12278220695869799283902702923485903093158153845103172551
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301 2 [2, 2, 5, 5, 31, 24429863873, 118486009933781072573, 483162279352983405762947, 230651967228289828054211208494561] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr24429863873
    · exact pr118486009933781072573
    · exact pr483162279352983405762947
    · exact pr230651967228289828054211208494561
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403 2 [2, 6469, 80567, 40400420911064051473, 23745962129962148394257714789277705957807205236868975737393319] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr40400420911064051473
    · exact pr23745962129962148394257714789277705957807205236868975737393319
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927 3 [2, 3, 139, 863, 64288855770297817, 21611626709292047953692709004258975803177567316341638237479157522509] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr64288855770297817
    · exact pr21611626709292047953692709004258975803177567316341638237479157522509
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967 5 [2, 17, 652261, 5717755033, 58722424903363122961, 2026106462258046807233143, 66283874023533288977181798301] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr5717755033
    · exact pr58722424903363122961
    · exact pr2026106462258046807233143
    · exact pr66283874023533288977181798301
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089 14 [2, 2, 2, 3, 1442377, 5119233389, 127383622947208730741, 165561626209896455053, 267566513611201937534627046321373] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr5119233389
    · exact pr127383622947208730741
    · exact pr165561626209896455053
    · exact pr267566513611201937534627046321373
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513 3 [2, 2, 2, 2, 2, 2, 207743, 11052637, 6804993587313637538011336005449854012446026441548504005500400464791812204863] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr11052637
    · exact pr6804993587313637538011336005449854012446026441548504005500400464791812204863
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611 3 [2, 3, 5, 37, 1009, 391691, 15138241, 108150937, 1895821019395970170536007797191, 734411090819951174645617944217607] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr15138241
    · exact pr108150937
    · exact pr1895821019395970170536007797191
    · exact pr734411090819951174645617944217607
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623 3 [2, 3, 3, 3, 7, 7, 1571782070172867986209191007, 240446151237719198652011322429727922840874113206424081537051] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1571782070172867986209191007
    · exact pr240446151237719198652011322429727922840874113206424081537051
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687 5 [2, 1213, 17351, 2532637, 3928049, 315397352443, 18372083701294024233029, 412114970424412329181892219789694751] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr315397352443
    · exact pr18372083701294024233029
    · exact pr412114970424412329181892219789694751
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851 2 [2, 3, 5, 5, 17, 17, 31, 79, 9419375561335912358362027106137052856354993658405403330597004732765250793229164459] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr9419375561335912358362027106137052856354993658405403330597004732765250793229164459
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577 5 [2, 2, 2, 3, 3, 449651011, 29060653450353795925049, 1062885674841072459489414818970827139736118824610593743247] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr449651011
    · exact pr29060653450353795925049
    · exact pr1062885674841072459489414818970827139736118824610593743247
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327 5 [2, 3, 109, 125247679, 293824958127172973, 37776756054769556533, 1099864590658222331156146009438844141746579] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact pr125247679
    · exact pr293824958127172973
    · exact pr37776756054769556533
    · exact pr1099864590658222331156146009438844141746579
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331 2 [2, 5, 7, 11, 41, 503935824962734626127, 92681997034922305623089, 678195340223078331832355971258444747462523] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr503935824962734626127
    · exact pr92681997034922305623089
    · exact pr678195340223078331832355971258444747462523
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417 7 [2, 2, 2, 2, 3, 797, 1518054623, 35243004164791, 488584990641815147167821406930488475169798294444325086198732677] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr1518054623
    · exact pr35243004164791
    · exact pr488584990641815147167821406930488475169798294444325086198732677
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- `999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721` is prime. -/
private theorem pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721 : (999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721).Prime := by
  refine lucas_of_list 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721 3 [2, 2, 2, 2, 2, 5, 17, 59, 67, 93004568384399041680927367152274519724408862963348759691076025654380143152631657267] ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact pr93004568384399041680927367152274519724408862963348759691076025654380143152631657267
  · decide
  · decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide

/-- A block of length `a + b` is its first `a` entries followed by the next `b`
entries. This is the only list bookkeeping the assembly needs; it is proved here
so that no existing file is touched. -/
private theorem take_add_split (l : List ℕ) (a b : ℕ) :
    l.take (a + b) = l.take a ++ (l.drop a).take b := by
  conv_lhs => rw [← List.take_append_drop a (l.take (a + b))]
  rw [List.take_take, List.take_drop]
  simp

/-- LEAF. First step of the proof of the exponent-720 component: the
congruence obligation on the first window of eight candidates of `qs.take 64`,
namely positions 1 through 8 of the fixed row 10^90 candidate list, cut by
`qs.take 8`. The finite certification for these eight candidates stays OPEN. -/
theorem component7_window0 :
    ∀ q ∈ qs.take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : qs.take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934019 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934133 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934201 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934369 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999934763 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935069 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935093 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935419 p hp hd


/-- LEAF. Second step of the proof of the exponent-720 component: the
congruence obligation on positions 9 through 16 of the candidate list, cut by
`(qs.drop 8).take 8`, the second window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window1 :
    ∀ q ∈ (qs.drop 8).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 8).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935591 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935651 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999935747 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936161 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936541 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936739 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936839 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999936953 p hp hd


/-- LEAF. Third step of the proof of the exponent-720 component: the
congruence obligation on positions 17 through 24 of the candidate list, cut by
`(qs.drop 16).take 8`, the third window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window2 :
    ∀ q ∈ (qs.drop 16).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 16).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937039 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937241 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937571 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999937721 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999938167 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999938219 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999938521 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939137 p hp hd


/-- LEAF. Fourth step of the proof of the exponent-720 component: the
congruence obligation on positions 25 through 32 of the candidate list, cut by
`(qs.drop 24).take 8`, the fourth window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window3 :
    ∀ q ∈ (qs.drop 24).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 24).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939151 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939187 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939251 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939307 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939331 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939539 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939907 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999939923 p hp hd


/-- LEAF. Fifth step of the proof of the exponent-720 component: the
congruence obligation on positions 33 through 40 of the candidate list, cut by
`(qs.drop 32).take 8`, the fifth window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window4 :
    ∀ q ∈ (qs.drop 32).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 32).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999940129 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999940229 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999940487 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941111 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941173 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941191 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941201 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941299 p hp hd


/-- LEAF. Sixth step of the proof of the exponent-720 component: the
congruence obligation on positions 41 through 48 of the candidate list, cut by
`(qs.drop 40).take 8`, the sixth window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window5 :
    ∀ q ∈ (qs.drop 40).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 40).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941363 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999941753 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942301 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942421 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942437 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942701 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942731 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999942769 p hp hd


/-- LEAF. Seventh step of the proof of the exponent-720 component: the
congruence obligation on positions 49 through 56 of the candidate list, cut by
`(qs.drop 48).take 8`, the seventh window of the block. The finite
certification for these eight candidates stays OPEN. -/
theorem component7_window6 :
    ∀ q ∈ (qs.drop 48).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 48).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943183 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943301 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943403 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943927 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999943967 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944089 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944513 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944611 p hp hd


/-- LEAF. Eighth and last step of the proof of the exponent-720 component: the
congruence obligation on the final window of eight candidates, positions 57
through 64 of the fixed row 10^90 candidate list, cut by `(qs.drop 56).take 8`,
which is what remains of the block after the seven earlier windows. The finite
certification for these eight candidates stays OPEN. -/
theorem component7_window7 :
    ∀ q ∈ (qs.drop 56).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  have hw : (qs.drop 56).take 8 = [999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417, 999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721] := by decide
  intro q hq p hp hd
  rw [hw] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944623 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944687 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999944851 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999945577 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946327 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946331 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946417 p hp hd
  · exact closes_of_prime _ pr999999999999999999999999999999999999999999999999999999999999999999999999999999999999946721 p hp hd


/-- The exact statement of `component7`, proved from the eight windows above and
not from `component7` itself. Each step rewrites the remaining block
`(qs.drop (8 * k)).take (64 - 8 * k)` into its next window of eight followed by
a shorter remainder, using `take_add_split` and `List.drop_drop`. -/
theorem component7_split : ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q → ∃ i : ℕ, i < 7 ∧ p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  rw [show (64 : ℕ) = 8 + 56 from rfl, take_add_split] at hq
  rcases List.mem_append.mp hq with h | h
  · exact component7_window0 q h p hp hd
  rw [show (56 : ℕ) = 8 + 48 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window1 q h p hp hd
  rw [List.drop_drop, show (8 : ℕ) + 8 = 16 from rfl,
    show (48 : ℕ) = 8 + 40 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window2 q h p hp hd
  rw [List.drop_drop, show (16 : ℕ) + 8 = 24 from rfl,
    show (40 : ℕ) = 8 + 32 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window3 q h p hp hd
  rw [List.drop_drop, show (24 : ℕ) + 8 = 32 from rfl,
    show (32 : ℕ) = 8 + 24 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window4 q h p hp hd
  rw [List.drop_drop, show (32 : ℕ) + 8 = 40 from rfl,
    show (24 : ℕ) = 8 + 16 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window5 q h p hp hd
  rw [List.drop_drop, show (40 : ℕ) + 8 = 48 from rfl,
    show (16 : ℕ) = 8 + 8 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window6 q h p hp hd
  rw [List.drop_drop, show (48 : ℕ) + 8 = 56 from rfl] at h
  exact component7_window7 q h p hp hd

#print axioms component7_split

#print axioms LeanLab.DtRS1998.Decomp445a.component7_window0
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window1
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window2
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window3
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window4
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window5
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window6
#print axioms LeanLab.DtRS1998.Decomp445a.component7_window7

end LeanLab.DtRS1998.Decomp445a
