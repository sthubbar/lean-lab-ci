import LeanLab.PNTPort.Vinogradov.SingPos

/-!
# R-5060, the Ramanujan-Fourier expansion of the binary Goldbach count

Lab proof, unit U-5550, CLOUD 20261019T1321Z-cloud25. AI wrote the Lean code. Known mathematics,
Ramanujan 1918, Hardy 1921, Gadiyar-Padma 1999 for the heuristic. Binary Goldbach is OPEN; this is
a T3 route, never progress on Goldbach.

Hardy's expansion `φ(n)/n · Λ(n) = ∑_q μ(q) c_q(n)/φ(q)`, put into `∑_{a+b=N}` and summed term
by term with the orthogonality of Ramanujan sums, gives the Hardy-Littlewood main term
`𝔖(N) N` with `𝔖(N) = ∑_q μ(q)² c_q(N)/φ(q)²`. The interchange is the whole problem. These are
the two smallest lemmas of the route:

* `bS_euler`, `one_add_bS_prime`: the binary singular series truncated to the divisors of the
  primorial is the Euler product `∏_{p ≤ P} (1 + c_p(N)/(p-1)²)`, with local factor `p/(p-1)` for
  `p ∣ N` and `1 - 1/(p-1)²` for `p ∤ N`; `one_add_bS_two` is the factor `2` at `p = 2`, `N` even.
* `wQ_eq_divisorSum`, `wQ_congr`: the truncated expansion `w_Q(n) = ∑_{q ≤ Q} μ(q) c_q(n)/φ(q)` is
  a divisor sum of level `Q`, so it sees only `{d ≤ Q : d ∣ n}`; `wQ_prime_semiprime` is the
  vacuity test and the parity statement: `w_10(11) = w_10(143)`, a prime and a product of two
  primes get the same weight.
-/

namespace LeanLab.Routes.R5060

open Finset ArithmeticFunction LeanLab.PNTPort.Vinogradov
open scoped ArithmeticFunction.Moebius

/-- `q ↦ 1/φ(q)²`. -/
noncomputable def invPhi2 : ArithmeticFunction ℝ := ⟨fun q => 1 / (q.totient : ℝ) ^ 2, by simp⟩

lemma invPhi2_mult : invPhi2.IsMultiplicative := by
  refine ⟨by simp [invPhi2], fun {a b} hab => ?_⟩
  show 1 / ((a * b).totient : ℝ) ^ 2 = 1 / (a.totient : ℝ) ^ 2 * (1 / (b.totient : ℝ) ^ 2)
  rw [Nat.totient_mul hab]; push_cast; rw [mul_pow, one_div_mul_one_div]

/-- The binary singular series term `μ(q)² c_q(N)/φ(q)²`. -/
noncomputable def bS (N : ℕ) : ArithmeticFunction ℝ :=
  (((μ : ArithmeticFunction ℝ).pmul (μ : ArithmeticFunction ℝ)).pmul (cR N)).pmul invPhi2

lemma bS_mult (N : ℕ) : (bS N).IsMultiplicative :=
  ((isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul
    (cR_mult N)).pmul invPhi2_mult

lemma bS_apply {q : ℕ} (hq : 1 ≤ q) (N : ℕ) :
    bS N q = (μ q : ℝ) ^ 2 * HeathBrown1985.ramanujan q N / (q.totient : ℝ) ^ 2 := by
  unfold bS
  rw [pmul_apply, pmul_apply, pmul_apply, intCoe_apply, cR_apply hq]
  show _ * (1 / (q.totient : ℝ) ^ 2) = _
  ring

/-- The local factor at a prime. -/
lemma one_add_bS_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    1 + bS N p = if p ∣ N then (p : ℝ) / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  rw [bS_apply hp.one_lt.le, ramanujan_prime hp, moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq : (p : ℝ) - 1 ≠ 0 := by linarith
  push_cast
  split_ifs
  · field_simp; ring
  · field_simp; ring

lemma one_add_bS_two {N : ℕ} (hN : Even N) : 1 + bS N 2 = 2 := by
  rw [one_add_bS_prime Nat.prime_two, if_pos (even_iff_two_dvd.1 hN)]; norm_num

/-- The binary singular series over the divisors of the primorial is the Euler product. -/
theorem bS_euler (N P : ℕ) :
    ∑ d ∈ (primorial P).divisors, bS N d = ∏ p ∈ Nat.primesLE P, (1 + bS N p) := by
  rw [← (bS_mult N).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial P),
    primeFactors_primorial]

/-- The truncated Hardy expansion `w_Q(n) = ∑_{q ≤ Q} μ(q) c_q(n)/φ(q)`. -/
noncomputable def wQ (Q n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (μ q : ℝ) * HeathBrown1985.ramanujan q n / (q.totient : ℝ)

/-- The divisor coefficient `κ_Q(d) = ∑_{q ≤ Q, d ∣ q} μ(q) μ(q/d)/φ(q)`. -/
noncomputable def kappa (Q d : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 Q).filter (d ∣ ·), (μ q : ℝ) * (μ (q / d) : ℝ) / (q.totient : ℝ)

/-- `w_Q` is a divisor sum of level `Q`. -/
theorem wQ_eq_divisorSum (Q : ℕ) {n : ℕ} (hn : n ≠ 0) :
    wQ Q n = ∑ d ∈ n.divisors.filter (· ≤ Q), (d : ℝ) * kappa Q d := by
  unfold wQ kappa HeathBrown1985.ramanujan
  simp_rw [mul_sum, sum_div]
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, d⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff, mem_filter] at h ⊢
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := h
    exact ⟨⟨⟨h3, hn⟩, (Nat.le_of_dvd (by omega) h4).trans h2⟩, ⟨h1, h2⟩, h4⟩
  · rintro ⟨d, q⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff, mem_filter] at h ⊢
    obtain ⟨⟨⟨h1, -⟩, -⟩, ⟨h3, h4⟩, h5⟩ := h
    exact ⟨⟨h3, h4⟩, ⟨h1, h5⟩, Nat.gcd_ne_zero_right (by omega)⟩
  · intro x _; rfl
  · intro x _; rfl
  · rintro ⟨q, d⟩ _
    ring

/-- `w_Q(n)` depends only on which `d ≤ Q` divide `n`: the truncated expansion is sieve data. -/
theorem wQ_congr (Q : ℕ) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (h : ∀ d ≤ Q, d ∣ n ↔ d ∣ m) :
    wQ Q n = wQ Q m := by
  rw [wQ_eq_divisorSum Q hn, wQ_eq_divisorSum Q hm]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨(h d h2).1 h1, hm⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨(h d h2).2 h1, hn⟩, h2⟩

/-- Vacuity test and the parity statement: the prime `11` and `143 = 11 · 13` get the same
truncated weight at level `10`. -/
theorem wQ_prime_semiprime : wQ 10 11 = wQ 10 143 := by
  apply wQ_congr 10 (by norm_num) (by norm_num)
  intro d hd
  interval_cases d <;> decide

end LeanLab.Routes.R5060
