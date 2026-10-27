/-
Unit U-1537, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0035, J. Pintz and I. Z. Ruzsa 2020, On Linnik's approximation to Goldbach's problem II,
Acta Math. Hungar. Read from the PC copy copies/P0035.pdf, 14 pages, page numbers as printed;
page images of pp. 6, 7, 9, 11 checked for every display used here.

File a: Lemma 1 of p. 6, display (2.34), with its proof on p. 7, displays (2.35) to (2.40),
and the transfer from one class `H_i = {h : r_i | C(ε) h}` of (4.3), p. 9, to Lemma 1.

Lemma 1 is stated here in the general form needed by BOTH of its applications: the sum runs over
all `ν ∈ [1, L]` with `m - 2^ν ≠ 0`, and `m` is any integer with `|m| ≤ 2^{2L}`. The paper states
it for `0 < m ≤ N` and `2^ν < m`; that covers (4.5) on p. 9, where `m = 2^{ν₂}`, but the
application in (6.3) on p. 11 takes `m = 2^{ν₁} + ... + 2^{ν_k} - 2^{μ₁} - ... - 2^{μ_{k-1}}`,
which can be negative or exceed `N`. The proof of p. 7 works verbatim with `|m - 2^ν|`.

Notation. `kf d = k(d) = ∏_{p | d} 1/(p - 2)` on odd squarefree `d`, 0 otherwise, so the primed
sums of the paper are sums of `kf`; `xi d = ξ(d)`, the order of 2 mod `d`; `sfac h` is
`∏_{p | h, p > 2} (1 + 1/(p - 2))`, so that `𝔖(h) = 2 C₀ sfac h` for `h ≠ 0`, (2.13) p. 4.
`Aq m q L` is `A(m, q)/(2 C₀)` of (2.34) in the general form; `Pm m L = ∏ |m - 2^ν|`, (2.39).

Assemblies, CONDITIONAL ON the leaves of this file, no sorry of their own:
* `lemma1_general`: Lemma 1, (2.34), in the general form above.
* `lemma1_class`: the per class bound used in (4.5) and (6.3): for one modulus `r` whose odd
  squarefree part is large, `∑_{ν : r | C (m - 2^ν)} sfac (m - 2^ν) ≤ η L`.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Linnik.Decomp1537a

open Finset Real

/-! ### Definitions, p. 4 and p. 7 -/

/-- `k(d) = ∏_{p | d, p > 2} 1/(p - 2)` for odd squarefree `d`, (2.35) p. 7, and `0` for other
`d`, so that `∑'` of the paper is a plain sum of `kf`. -/
noncomputable def kf (d : ℕ) : ℝ :=
  if Odd d ∧ Squarefree d then ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) else 0

/-- `ξ(d) = min {ν ≥ 1 : 2^ν ≡ 1 mod d}`, (2.35) p. 7, as the order of 2 in `ZMod d`. -/
noncomputable def xi (d : ℕ) : ℕ := orderOf (2 : ZMod d)

/-- `∏_{p | h, p > 2} (1 + 1/(p - 2))`, the product in `𝔖(h)` of (2.13) p. 4. -/
noncomputable def sfac (h : ℤ) : ℝ :=
  ∏ p ∈ h.natAbs.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

/-- The exponents of (2.34): `ν ∈ [1, L]` with `m - 2^ν ≠ 0` and `q | m - 2^ν`. -/
def nus (m : ℤ) (q L : ℕ) : Finset ℕ :=
  (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (q : ℤ) ∣ m - 2 ^ ν)

/-- `A(m, q)/(2 C₀)` of (2.34) p. 6, general form: `∑_{ν ∈ nus} sfac (m - 2^ν)`. -/
noncomputable def Aq (m : ℤ) (q L : ℕ) : ℝ := ∑ ν ∈ nus m q L, sfac (m - 2 ^ ν)

/-- `P(m) = ∏_{ν ≤ L, m ≠ 2^ν} |m - 2^ν|`, (2.39) p. 7. -/
def Pm (m : ℤ) (L : ℕ) : ℕ :=
  ∏ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0), (m - 2 ^ ν).natAbs

/-- The odd squarefree part `r' = ∏_{p | r, p > 2} p`, (2.27) p. 5. -/
def oddSqf (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p

/-- `q = r'/(r', C)`: the odd squarefree modulus that `r | C h` forces to divide `h`. -/
def qOf (r C : ℕ) : ℕ := oddSqf r / Nat.gcd (oddSqf r) C

/-! ### Small proved facts -/

lemma kf_nonneg (d : ℕ) : 0 ≤ kf d := by
  unfold kf
  split_ifs with h
  · refine prod_nonneg fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr h.1) (even_iff_two_dvd.mpr hpd)
    have h3 : (3 : ℝ) ≤ p := by
      have := hpp.two_le
      exact_mod_cast (by omega : 3 ≤ p)
    exact div_nonneg zero_le_one (by linarith)
  · exact le_refl 0

lemma odd_of_kf_ne {d : ℕ} (h : kf d ≠ 0) : Odd d := by
  unfold kf at h
  split_ifs at h with h1
  · exact h1.1
  · exact absurd rfl h

lemma sfac_nonneg (h : ℤ) : 0 ≤ sfac h := by
  unfold sfac
  refine prod_nonneg fun p hp => ?_
  have h2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  have : 0 < 1 / ((p : ℝ) - 2) := one_div_pos.mpr (by linarith)
  linarith

lemma Pm_pos (m : ℤ) (L : ℕ) : 0 < Pm m L := by
  unfold Pm
  apply Finset.prod_pos
  intro ν hν
  exact Int.natAbs_pos.mpr (mem_filter.mp hν).2

/-! ### Leaves for Lemma 1, p. 7 -/

/-- LEAF. Unit U-1537. For `h ≠ 0`, `∏_{p | h, p > 2} (1 + 1/(p - 2)) = ∑'_{d | h} k(d)`, the sum
over odd squarefree divisors; this is how `𝔖(m - 2^ν)/(2C₀)` becomes the divisor sum in the first
inequality of (2.36) p. 7, and how `∑'_{d | P(m)} k(d)` becomes the product in (2.40) p. 7. -/
theorem sfac_eq_sum_kf (h : ℤ) (hh : h ≠ 0) :
    sfac h = ∑ d ∈ h.natAbs.divisors, kf d := by
  sorry

/-- LEAF. Unit U-1537. The interchange in (2.36) p. 7: expanding each `sfac (m - 2^ν)` as a
divisor sum and swapping, `A(m, q)/(2C₀) = ∑_{d | P(m)} k(d) · #{ν ≤ L : m ≠ 2^ν, [d, q] | m - 2^ν}`;
every divisor of some `m - 2^ν ≠ 0` divides `P(m)`. -/
theorem Aq_eq_sum (m : ℤ) (q L : ℕ) :
    Aq m q L = ∑ d ∈ (Pm m L).divisors, kf d * ((nus m (Nat.lcm d q) L).card : ℝ) := by
  sorry

/-- LEAF. Unit U-1537. For odd `n`, the `ν ∈ [1, L]` with `2^ν ≡ m mod n` lie in one class mod
`ξ(n)`, so there are at most `L/ξ(n) + 1` of them; second inequality of (2.36) p. 7. -/
theorem card_nus_le (m : ℤ) {n : ℕ} (L : ℕ) (hn : Odd n) :
    ((nus m n L).card : ℝ) ≤ L / xi n + 1 := by
  sorry

/-- LEAF. Unit U-1537. For odd `n` and `d | n`, `ξ(d) ≤ ξ(n)`, since `ξ(d) | ξ(n)`; used with
`n = [d, q]` for both `ξ([d, q]) ≥ ξ(q)` and `ξ([d, q]) ≥ ξ(d)` in (2.38) p. 7. -/
theorem xi_le_of_dvd {d n : ℕ} (hn : Odd n) (hd : d ∣ n) : xi d ≤ xi n := by
  sorry

/-- LEAF. Unit U-1537. `ξ(q) ≥ log₂ q` for odd `q`, since `q | 2^{ξ(q)} - 1`; the trivial bound
"ξ(m) ≥ log₂ m" stated before (2.38) p. 7. -/
theorem log_le_xi_mul {q : ℕ} (hq : Odd q) : Real.log q ≤ xi q * Real.log 2 := by
  sorry

/-- LEAF. Unit U-1537. Romanov's series `∑' k(d)/ξ(d)` converges, the sentence after (2.37)
p. 7; its value is below 1.94 by (8.14) of part I. The lab's `U1474R0.r0Summable` proves the same
series summable with `wt = kf` and `eps = xi` by definition, so a prover can bridge to it. -/
theorem summable_kf_div_xi : Summable (fun d : ℕ => kf d / (xi d : ℝ)) := by
  sorry

/-- LEAF. Unit U-1537. Choice of `D(η)` in (2.37) p. 7: the tail of a summable nonnegative series
is eventually below any `η > 0`, uniformly over finite sets beyond `D`. -/
theorem tail_small {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ d, 0 ≤ f d) {η : ℝ} (hη : 0 < η) :
    ∃ D : ℕ, ∀ s : Finset ℕ, (∀ d ∈ s, D < d) → ∑ d ∈ s, f d < η := by
  sorry

/-- LEAF. Unit U-1537. The split at `D` in (2.38) p. 7: for odd `q`,
`∑_{d ∈ s} k(d)/ξ([d, q]) ≤ (∑_{d ≤ D} k(d))/ξ(q) + ∑_{d ∈ s, d > D} k(d)/ξ(d)`. -/
theorem sum_div_xi_lcm_le {q : ℕ} (hq : Odd q) (D : ℕ) (s : Finset ℕ) :
    ∑ d ∈ s, kf d / (xi (Nat.lcm d q) : ℝ) ≤
      (∑ d ∈ range (D + 1), kf d) / xi q + ∑ d ∈ s.filter (fun d => D < d), kf d / xi d := by
  sorry

/-- LEAF. Unit U-1537. (2.39) p. 7 in the general form: if `|m| ≤ 2^{2L}` then
`P(m) = ∏ |m - 2^ν| ≤ (2^{2L+1})^L`, so `log P(m) ≪ L²`. -/
theorem Pm_le {m : ℤ} {L : ℕ} (hm : |m| ≤ 2 ^ (2 * L)) : Pm m L ≤ 2 ^ ((2 * L + 1) * L) := by
  sorry

/-- LEAF. Unit U-1537. The primes `p > L³` in (2.40) p. 7: if `0 < P ≤ 2^{(2L+1)L}` and `L ≥ 2`,
then `P` has at most `3L²` prime factors, each above `L³`, so
`∏_{p | P, p > 2, p > L³} (1 + 1/(p - 2)) ≤ exp(6/L) ≤ e³`. -/
theorem large_prime_prod_le {L P : ℕ} (hL : 2 ≤ L) (hP : 0 < P)
    (hPle : P ≤ 2 ^ ((2 * L + 1) * L)) :
    ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2)) ≤ Real.exp 3 := by
  sorry

/-- LEAF. Unit U-1537. The primes `p ≤ L³` in (2.40) p. 7: the product over odd prime factors
`p ≤ x` of `P` is at most the product over all odd primes `p ≤ x`, all factors being `≥ 1`. -/
theorem small_prime_prod_le (P x : ℕ) :
    ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ x),
      (1 + 1 / ((p : ℝ) - 2)) ≤
    ∏ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ 2 < p), (1 + 1 / ((p : ℝ) - 2)) := by
  sorry

/-- LEAF. Unit U-1537. Mertens: `∏_{2 < p ≤ x} (1 + 1/(p - 2)) ≤ C log x` for `x ≥ 2`, the step
`∑_{p ≤ L³} 1/p ≤ log log L + O(1)` of (2.40) p. 7, and also the bound `∑_{d ≤ x} k(d) ≤ C log x`
before (2.38). Since `1 + 1/(p - 2) = (p - 1)/(p - 2)` this is the lab's `MertensProd`, proved in
`U1469Mertens.mertensProd` with `C = e^24`. -/
theorem mertens_prod : ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∏ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ 2 < p), (1 + 1 / ((p : ℝ) - 2)) ≤
      C * Real.log x := by
  sorry

/-- LEAF. Unit U-1537. `log L = o(L)`, the last line of (2.40) p. 7: for every `c > 0`,
`log L ≤ c L` for all large natural `L`. -/
theorem log_le_mul_eventually {c : ℝ} (hc : 0 < c) :
    ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → Real.log L ≤ c * L := by
  sorry

/-! ### Leaves for the classes `H_i` of (4.3), p. 9 -/

/-- LEAF. Unit U-1537. If `r | C h` then `q = r'/(r', C)` divides `h`, where `r'` is the odd
squarefree part of `r`; this is how `h ∈ H_i`, (4.3) p. 9, i.e. `r_i | C(ε) h`, puts `h` into
the range of Lemma 1, whose modulus must be odd squarefree, p. 6. -/

lemma oddSqf_dvd_r (r : ℕ) : oddSqf r ∣ r := by
  unfold oddSqf
  have hdvd : ∏ p ∈ r.primeFactors, p ∣ r := Nat.prod_primeFactors_dvd r
  apply dvd_trans _ hdvd
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  exact hp.1

lemma oddSqf_pos (r : ℕ) : 0 < oddSqf r := by
  unfold oddSqf
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact Nat.pos_of_ne_zero (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp.1))

theorem qOf_dvd {r C : ℕ} {h : ℤ} (hr : 0 < r) (hdvd : (r : ℤ) ∣ C * h) :
    (qOf r C : ℤ) ∣ h := by
  sorry

/-- LEAF. Unit U-1537. `q = r'/(r', C)` is odd, as a divisor of the odd number `r'`; Lemma 1
p. 6 needs an odd modulus. -/
theorem qOf_odd (r C : ℕ) : Odd (qOf r C) := by
  sorry

/-- LEAF. Unit U-1537. `r' ≤ q · C` for `C ≥ 1`, so `q ≥ r'/C` is large when `r'` is, by (2.27)
p. 5; this is the "min(q, N) > C₀(η)" of Lemma 1 p. 6 for `q = r'/(r', C(ε))`. -/
theorem le_qOf_mul (r C : ℕ) (hC : 0 < C) : oddSqf r ≤ qOf r C * C := by
  sorry

/-! ### Assemblies -/

/-- **Lemma 1, (2.34) p. 6, general form. CONDITIONAL ON the leaves above.** For every `η > 0`
there are `Q₀, L₀` with `A(m, q)/(2C₀) ≤ η L` whenever `L ≥ L₀`, `q ≥ Q₀` is odd and
`|m| ≤ 2^{2L}`. The proof is the paper's: (2.36), (2.37), (2.38), then (2.39), (2.40). -/
theorem lemma1_general {η : ℝ} (hη : 0 < η) :
    ∃ Q0 L0 : ℕ, ∀ L q : ℕ, L0 ≤ L → Q0 ≤ q → Odd q → ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
      Aq m q L ≤ η * L := by
  obtain ⟨D, hD⟩ := tail_small summable_kf_div_xi
    (fun d => div_nonneg (kf_nonneg d) (Nat.cast_nonneg _)) (by positivity : 0 < η / 8)
  set K := ∑ d ∈ range (D + 1), kf d with hK
  have hK0 : 0 ≤ K := sum_nonneg fun d _ => kf_nonneg d
  obtain ⟨C, hC⟩ := mertens_prod
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have he3 : 0 < Real.exp 3 := Real.exp_pos 3
  obtain ⟨L1, hL1⟩ := log_le_mul_eventually (c := η / (6 * C' * Real.exp 3)) (by positivity)
  obtain ⟨Q0, hQ0⟩ := exists_nat_gt (Real.exp (8 * K * Real.log 2 / η))
  refine ⟨Q0, max L1 2, ?_⟩
  intro L q hL hq hqodd m hm
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLL1 : L1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set P := Pm m L with hPdef
  have hP0 : 0 < P := Pm_pos m L
  -- (2.36): divisor expansion, interchange, and the count of `ν`
  have step1 : Aq m q L ≤
      ∑ d ∈ P.divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d q)) + kf d) := by
    rw [Aq_eq_sum]
    apply sum_le_sum
    intro d _
    by_cases hk : kf d = 0
    · simp [hk]
    · have hdodd := odd_of_kf_ne hk
      have hlo : Odd (Nat.lcm d q) :=
        (hdodd.mul hqodd).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right d q) (dvd_mul_left q d))
      have hc := card_nus_le m L hlo
      have hk0 := kf_nonneg d
      calc kf d * ((nus m (Nat.lcm d q) L).card : ℝ)
          ≤ kf d * ((L : ℝ) / xi (Nat.lcm d q) + 1) := mul_le_mul_of_nonneg_left hc hk0
        _ = kf d * ((L : ℝ) / xi (Nat.lcm d q)) + kf d := by ring
  have step2 : ∑ d ∈ P.divisors, (kf d * ((L : ℝ) / xi (Nat.lcm d q)) + kf d) =
      (L : ℝ) * ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) + ∑ d ∈ P.divisors, kf d := by
    rw [sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro d _
    ring
  -- Σ₂ is the product of (2.40)
  have hS2 : ∑ d ∈ P.divisors, kf d = sfac (P : ℤ) := by
    rw [sfac_eq_sum_kf (P : ℤ) (by exact_mod_cast hP0.ne')]
    simp
  -- (2.37), (2.38)
  have hS1 : ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) ≤ K / xi q + η / 8 := by
    have h8 := sum_div_xi_lcm_le hqodd D P.divisors
    have h9 := hD (P.divisors.filter (fun d => D < d)) (fun d hd => (mem_filter.mp hd).2)
    linarith
  have hxi : K / xi q ≤ η / 8 := by
    have hq1 : (Q0 : ℝ) ≤ q := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (lt_trans (Real.exp_pos _) hQ0) hq1
    have hlogq : 8 * K * Real.log 2 / η < Real.log q := by
      rw [Real.lt_log_iff_exp_lt hqpos]
      linarith
    have hl5 := log_le_xi_mul hqodd
    have hlog2 := Real.log_pos one_lt_two
    have h0 : 0 ≤ 8 * K * Real.log 2 / η := by positivity
    have hlq_pos : 0 < Real.log q := lt_of_le_of_lt h0 hlogq
    have hxi_pos : (0 : ℝ) < xi q := by
      rcases le_or_gt (xi q : ℝ) 0 with hcon | hcon
      · have : (xi q : ℝ) * Real.log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hlog2.le
        linarith
      · exact hcon
    rw [div_le_iff₀ hxi_pos]
    have h1 : 8 * K * Real.log 2 < Real.log q * η := (div_lt_iff₀ hη).mp hlogq
    have h2 : 8 * K * Real.log 2 < η * (xi q * Real.log 2) := by
      calc 8 * K * Real.log 2 < Real.log q * η := h1
        _ ≤ (xi q * Real.log 2) * η := mul_le_mul_of_nonneg_right hl5 hη.le
        _ = η * (xi q * Real.log 2) := by ring
    have h3 : K * Real.log 2 < (η / 8 * xi q) * Real.log 2 := by linarith
    exact (lt_of_mul_lt_mul_right h3 hlog2.le).le
  -- (2.39), (2.40)
  have hsfac : sfac (P : ℤ) ≤ η / 2 * L := by
    have hPle : P ≤ 2 ^ ((2 * L + 1) * L) := Pm_le hm
    have hnat : (P : ℤ).natAbs = P := Int.natAbs_natCast P
    unfold sfac
    rw [hnat, ← prod_filter_mul_prod_filter_not (P.primeFactors.filter (fun p => 2 < p))
      (fun p => p ≤ L ^ 3)]
    have hsmall := small_prime_prod_le P (L ^ 3)
    have hL3 : 2 ≤ L ^ 3 := le_trans hL2 (Nat.le_self_pow (by norm_num) L)
    have hmert := hC (L ^ 3) hL3
    have hlogL3 : Real.log ((L ^ 3 : ℕ) : ℝ) = 3 * Real.log L := by
      push_cast
      rw [Real.log_pow]
      norm_num
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
    have hlarge := large_prime_prod_le hL2 hP0 hPle
    have hfac_nonneg : ∀ s : Finset ℕ, (∀ p ∈ s, 2 < p) →
        0 ≤ ∏ p ∈ s, (1 + 1 / ((p : ℝ) - 2)) := by
      intro s hs
      refine prod_nonneg fun p hp => ?_
      have h2 : (2 : ℝ) < p := by exact_mod_cast hs p hp
      have : 0 < 1 / ((p : ℝ) - 2) := one_div_pos.mpr (by linarith)
      linarith
    have hA0 := hfac_nonneg ((P.primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ L ^ 3))
      (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    have hB0 := hfac_nonneg
      ((P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3))
      (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    set Asm := ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2))
    set Blg := ∏ p ∈ (P.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ≤ L ^ 3),
      (1 + 1 / ((p : ℝ) - 2))
    have hAsm : Asm ≤ C' * (3 * Real.log L) := by
      calc Asm ≤ _ := hsmall
        _ ≤ C * Real.log ((L ^ 3 : ℕ) : ℝ) := hmert
        _ = C * (3 * Real.log L) := by rw [hlogL3]
        _ ≤ C' * (3 * Real.log L) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hlogc := hL1 L hLL1
    calc Asm * Blg ≤ (C' * (3 * Real.log L)) * Real.exp 3 :=
          mul_le_mul hAsm hlarge hB0 (by positivity)
      _ = 3 * C' * Real.exp 3 * Real.log L := by ring
      _ ≤ 3 * C' * Real.exp 3 * (η / (6 * C' * Real.exp 3) * L) :=
          mul_le_mul_of_nonneg_left hlogc (by positivity)
      _ = η / 2 * L := by field_simp; ring
  calc Aq m q L ≤ (L : ℝ) * ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) +
        ∑ d ∈ P.divisors, kf d := by rw [← step2]; exact step1
    _ ≤ (L : ℝ) * (η / 8 + η / 8) + η / 2 * L := by
        rw [hS2]
        have : ∑ d ∈ P.divisors, kf d / xi (Nat.lcm d q) ≤ η / 8 + η / 8 := by linarith
        have := mul_le_mul_of_nonneg_left this hLpos
        linarith
    _ ≤ η * L := by nlinarith

/-- **The per class bound of (4.5) p. 9 and (6.3) p. 11. CONDITIONAL ON the leaves above.**
For every `η > 0` there are `T, L₀` such that, for `L ≥ L₀`, any modulus `r` and constant
`C ≥ 1` with `T C ≤ r'`, the odd squarefree part, and any `|m| ≤ 2^{2L}`,
`∑_{ν ≤ L, m ≠ 2^ν, r | C (m - 2^ν)} sfac(m - 2^ν) ≤ η L`. In the paper `r = r_i`,
`C = C(ε)`, and `r_i' ≫ L²` by (2.27) p. 5 makes `T C ≤ r_i'` hold for large `N`. -/
theorem lemma1_class {η : ℝ} (hη : 0 < η) :
    ∃ T L0 : ℕ, ∀ L : ℕ, L0 ≤ L → ∀ r C : ℕ, 0 < r → 0 < C → T * C ≤ oddSqf r →
      ∀ m : ℤ, |m| ≤ 2 ^ (2 * L) →
        ∑ ν ∈ (Icc 1 L).filter (fun ν => m - 2 ^ ν ≠ 0 ∧ (r : ℤ) ∣ C * (m - 2 ^ ν)),
          sfac (m - 2 ^ ν) ≤ η * L := by
  obtain ⟨Q0, L0, h⟩ := lemma1_general hη
  refine ⟨Q0, L0, fun L hL r C hr hC hT m hm => ?_⟩
  have hq : Q0 ≤ qOf r C :=
    Nat.le_of_mul_le_mul_right (hT.trans (le_qOf_mul r C hC)) hC
  calc _ ≤ Aq m (qOf r C) L := by
        unfold Aq nus
        apply sum_le_sum_of_subset_of_nonneg
        · intro ν hν
          simp only [mem_filter] at hν ⊢
          exact ⟨hν.1, hν.2.1, qOf_dvd hr hν.2.2⟩
        · intro ν _ _
          exact sfac_nonneg _
    _ ≤ η * L := h L _ hL hq (qOf_odd r C) m hm

end LeanLab.Linnik.Decomp1537a
