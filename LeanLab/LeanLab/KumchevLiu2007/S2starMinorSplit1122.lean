/-
ROUTE BURST S34, burst-20261122, unit P1122-0136. Splits the open leaf
Prep1121DKLMajorCut.S2star_minor_mean_square, P0088 page 6 display 24, the mean
square of S2* over m0 = M minus M0, into the steps of the printed proof.
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 6 displays 14, 17, 22, 23, 24.

The printed chain is
  int over m0 of |S2*|^2 <= sum over q <= P, a of |S(q, a)|^2 / phi(q)^2
      int over |beta| > 1/(q Q0) of |T2(beta)|^2 d beta
    << sum over q <= P of q^eta int over |beta| > 1/(q Q0) of Y / (1 + Y |beta|)^2
    << P^(-1 + eta),   Q0 = Y P^(-3) of display 14.
The pieces below follow it line by line, with eta = 1/2 in the Gauss sum mean.

* gauss_mean_square, PROVED, split class HARD: the sum over a of |S(q, a)|^2 / phi(q)^2 is
  << q^eta, display 24 second line, here with eta = 1/2.
* arcs_disjoint, PROVED, split class EASY: the arcs M(q, a) of display 15 are disjoint once
  H/P exceeds 2P, which the first sum of display 24 uses.
* off_M0, PROVED, split class EASY: on M(q, a) outside M0 of display 23, |q alpha - a| > P^3/Y.
* eventually_large, PROVED, split class MEDIUM: for large X the block range gives H/P > 2P and
  P/H <= Y^(-1/2)/4, so display 22 for T2 applies on every arc.
* pointwise_bound, PROVED, split class MEDIUM: on the complement of M0, |S2*|^2 is at most the
  sum over arcs of |S(q,a)|^2/phi(q)^2 C^2/(Y beta^2) on |beta| > P^3/(q Y),
  from arcs_disjoint, off_M0 and display 22.
* tail_integral, PROVED, split class MEDIUM: the integral of K/beta^2 over |beta| > r is 2K/r,
  the last integral of display 24.
* arc_sum_bound, PROVED, split class EASY: the sum over q <= P of q times the Gauss mean is
  at most (Cg + 1) P^(5/2), display 24 last step.

The final theorem S2star_minor_mean_square_of_pieces proves the exact statement
of the parent leaf from these pieces and T2BoundProp, with no step of its own.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLMajorCut

namespace LeanLab.KumchevLiu2007.S2starMinorSplit1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

private lemma gauss_mean_square_sq_le (j : ℕ) : (j + 2) ^ 2 ≤ 5 * 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; norm_num
    · have : (j + 3) ^ 2 ≤ 2 * (j + 2) ^ 2 := by nlinarith
      calc (j + 1 + 2) ^ 2 = (j + 3) ^ 2 := by ring
        _ ≤ 2 * (j + 2) ^ 2 := this
        _ ≤ 2 * (5 * 2 ^ j) := by omega
        _ = 5 * 2 ^ (j + 1) := by ring

private def gauss_mean_square_c (p : ℕ) : ℕ :=
  if p = 2 then 10 else if p = 3 then 4 else if p = 5 then 2 else 1

private lemma gauss_mean_square_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    (k + 1) ^ 2 * p ^ k ≤ gauss_mean_square_c p * (p ^ (k - 1) * (p - 1)) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 := hp.two_le
  have hpj : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left h2 j
  have hA : (j + 1 + 1) ^ 2 * p ^ (j + 1) ≤ 5 * p * (p ^ j) ^ 2 := by
    have := gauss_mean_square_sq_le j
    have h3 : (j + 2) ^ 2 ≤ 5 * p ^ j := le_trans this (by omega)
    calc (j + 1 + 1) ^ 2 * p ^ (j + 1) = (j + 2) ^ 2 * (p ^ j * p) := by ring
      _ ≤ (5 * p ^ j) * (p ^ j * p) := Nat.mul_le_mul_right _ h3
      _ = 5 * p * (p ^ j) ^ 2 := by ring
  have hB : 5 * p ≤ gauss_mean_square_c p * (p - 1) ^ 2 := by
    unfold gauss_mean_square_c
    by_cases e2 : p = 2
    · subst e2; norm_num
    by_cases e3 : p = 3
    · subst e3; norm_num
    by_cases e5 : p = 5
    · subst e5; norm_num
    simp only [e2, e3, e5, ite_false, one_mul]
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    have h6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
    have h7 : 7 ≤ p := by omega
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  calc (j + 1 + 1) ^ 2 * p ^ (j + 1) ≤ 5 * p * (p ^ j) ^ 2 := hA
    _ ≤ gauss_mean_square_c p * (p - 1) ^ 2 * (p ^ j) ^ 2 := Nat.mul_le_mul_right _ hB
    _ = gauss_mean_square_c p * (p ^ j * (p - 1)) ^ 2 := by ring

private lemma gauss_mean_square_c_prod (s : Finset ℕ) : ∏ p ∈ s, gauss_mean_square_c p ≤ 80 := by
  have h1 : ∏ p ∈ s, gauss_mean_square_c p = ∏ p ∈ s ∩ {2, 3, 5}, gauss_mean_square_c p := by
    symm
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hn
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, not_and] at hn
    have := hn hp
    unfold gauss_mean_square_c
    simp only [not_or] at this
    simp [this.1, this.2.1, this.2.2]
  have h2 : ∏ p ∈ s ∩ {2, 3, 5}, gauss_mean_square_c p ∣ ∏ p ∈ ({2, 3, 5} : Finset ℕ), gauss_mean_square_c p :=
    Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
  have h3 : ∏ p ∈ ({2, 3, 5} : Finset ℕ), gauss_mean_square_c p = 80 := by
    simp [gauss_mean_square_c]
  rw [h1]; rw [h3] at h2; exact Nat.le_of_dvd (by norm_num) h2

private lemma gauss_mean_square_tau_phi (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ 2 * n ≤ 80 * (Nat.totient n) ^ 2 := by
  rw [Nat.card_divisors hn, Nat.totient_eq_prod_factorization hn, Finsupp.prod,
    Nat.support_factorization]
  have e : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    have := Nat.prod_factorization_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at this
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  calc (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2) * n
      = ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2 * p ^ n.factorization p := by
        rw [Finset.prod_mul_distrib, e]
    _ ≤ _ := ?_
  clear e
  calc ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 2 * p ^ n.factorization p
      ≤ ∏ p ∈ n.primeFactors, gauss_mean_square_c p * (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 := by
        apply Finset.prod_le_prod' 
        intro p hp
        exact gauss_mean_square_prime_pow p _ (Nat.prime_of_mem_primeFactors hp)
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])))
    _ = (∏ p ∈ n.primeFactors, gauss_mean_square_c p) * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 := Finset.prod_mul_distrib
    _ ≤ 80 * ∏ p ∈ n.primeFactors, (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 :=
        Nat.mul_le_mul_right _ (gauss_mean_square_c_prod _)

private lemma gauss_mean_square_key (q x y : ℤ) (hq : 0 < q) (h : q ∣ x ^ 2 - y ^ 2) :
    q / (Int.gcd (y - x) q : ℤ) ∣ y + x := by
  have hd : 0 < Int.gcd (y - x) q := Int.gcd_pos_of_ne_zero_right _ hq.ne'
  have hcop := Int.gcd_div_gcd_div_gcd hd
  set d : ℤ := (Int.gcd (y - x) q : ℤ) with hd_def
  have hdpos : 0 < d := by rw [hd_def]; exact_mod_cast hd
  have h1 : (y - x) / d * d = y - x := Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
  have h2 : q / d * d = q := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have h3 : q / d * d ∣ (y - x) / d * (y + x) * d := by
    rw [h2, mul_right_comm, h1]
    have : x ^ 2 - y ^ 2 = -((y - x) * (y + x)) := by ring
    rw [this] at h; exact (dvd_neg).mp h
  have h4 : q / d ∣ (y - x) / d * (y + x) := (mul_dvd_mul_iff_right hdpos.ne').mp h3
  have hc : IsCoprime (q / d) ((y - x) / d) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcop
  exact hc.dvd_of_dvd_mul_left h4

private lemma gauss_mean_square_inj (q x y y' : ℤ) (hq : 0 < q) (hx : IsCoprime q x)
    (hy : 0 ≤ y ∧ y < q) (hy' : 0 ≤ y' ∧ y' < q)
    (h : q ∣ x ^ 2 - y ^ 2) (h' : q ∣ x ^ 2 - y' ^ 2)
    (hg : Int.gcd (y - x) q = Int.gcd (y' - x) q) (hb : 2 * y < q ↔ 2 * y' < q) : y = y' := by
  have e1 := gauss_mean_square_key q x y hq h
  have e2 := gauss_mean_square_key q x y' hq h'
  rw [← hg] at e2
  set d : ℤ := (Int.gcd (y - x) q : ℤ) with hd_def
  have d1 : d ∣ y - x := Int.gcd_dvd_left _ _
  have d2 : d ∣ y' - x := by rw [hd_def, hg]; exact Int.gcd_dvd_left _ _
  have h2 : q / d * d = q := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have dz : d ∣ y - y' := by have := dvd_sub d1 d2; rwa [sub_sub_sub_cancel_right] at this
  have ez : q / d ∣ y - y' := by have := dvd_sub e1 e2; rwa [add_sub_add_right_eq_sub] at this
  have k1 : q / d * d ∣ (y + x) * (y - y') := mul_dvd_mul e1 dz
  have k2 : q / d * d ∣ (y - y') * (y - x) := mul_dvd_mul ez d1
  rw [h2] at k1 k2
  have k3 : q ∣ (2 * (y - y')) * x := by
    have := dvd_sub k1 k2
    have e : (y + x) * (y - y') - (y - y') * (y - x) = (2 * (y - y')) * x := by ring
    rwa [e] at this
  have k4 : q ∣ 2 * (y - y') := hx.dvd_of_dvd_mul_right k3
  obtain ⟨k, hk⟩ := k4
  have kl : -2 < k := by
    by_contra hc; have hc := not_lt.mp hc; nlinarith
  have ku : k < 2 := by
    by_contra hc; have hc := not_lt.mp hc; nlinarith
  interval_cases k <;> omega

private lemma gauss_mean_square_fiber (q x : ℕ) (hq : 1 ≤ q) (hx : Nat.Coprime x q) :
    (((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
      (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card ≤ 2 * q.divisors.card := by
  have hc : (((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
      (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card ≤
      (q.divisors ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun y : ℕ => (Int.gcd ((y : ℤ) - x) q, decide (2 * y < q)))
    · intro y _
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true,
        Nat.mem_divisors]
      refine ⟨?_, by omega⟩
      exact Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right _ _)
    · intro y hy y' hy' he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hy hy'
      simp only [Prod.mk.injEq, decide_eq_decide] at he
      have hqz : (0 : ℤ) < q := by exact_mod_cast hq
      have hxc : IsCoprime (q : ℤ) (x : ℤ) := Nat.isCoprime_iff_coprime.mpr hx.symm
      have := gauss_mean_square_inj q x y y' hqz hxc ⟨by positivity, by exact_mod_cast hy.1.1⟩
        ⟨by positivity, by exact_mod_cast hy'.1.1⟩ hy.2 hy'.2 he.1
        (by constructor <;> intro h <;> [exact_mod_cast he.2.mp (by exact_mod_cast h);
          exact_mod_cast he.2.mpr (by exact_mod_cast h)])
      exact_mod_cast this
  simpa [Finset.card_product, mul_comm] using hc

private lemma gauss_mean_square_ee_add (s t : ℝ) : U1534.ee (s + t) = U1534.ee s * U1534.ee t := by
  unfold U1534.ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma gauss_mean_square_conj (t : ℝ) : (starRingEnd ℂ) (U1534.ee t) = U1534.ee (-t) := by
  unfold U1534.ee; rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]

private lemma gauss_mean_square_ee_nat_mul (n : ℕ) (t : ℝ) : U1534.ee (n * t) = U1534.ee t ^ n := by
  unfold U1534.ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private lemma gauss_mean_square_ee_int (m : ℤ) : U1534.ee m = 1 := by
  unfold U1534.ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

private lemma gauss_mean_square_geom (q : ℕ) (hq : 1 ≤ q) (m : ℤ) :
    ∑ a ∈ Finset.Icc 1 q, U1534.ee ((m : ℝ) / q) ^ a = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  set ζ := U1534.ee ((m : ℝ) / q) with hζ
  have hq0 : (q : ℝ) ≠ 0 := by have : (0:ℝ) < q := by exact_mod_cast hq
                               exact this.ne'
  have hζq : ζ ^ q = 1 := by
    rw [hζ, ← gauss_mean_square_ee_nat_mul, mul_div_cancel₀ _ hq0, gauss_mean_square_ee_int]
  have hI : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp_rw [pow_add, pow_one, ← Finset.mul_sum]
  split_ifs with hd
  · obtain ⟨n, hn⟩ := hd
    have : ζ = 1 := by
      rw [hζ, hn]; push_cast; rw [mul_div_cancel_left₀ _ hq0]; exact gauss_mean_square_ee_int n
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ] at h1; unfold U1534.ee at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      apply hd
      refine ⟨n, ?_⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : (((m : ℝ) / q : ℝ) : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ hpi; rw [hn]; ring
      have h3 : ((m : ℝ) / q) = (n : ℝ) := by exact_mod_cast h2
      have h4 : (m : ℝ) = (q : ℝ) * n := by field_simp at h3; linarith
      exact_mod_cast h4
    rw [geom_sum_eq hne, hζq]; simp

private lemma gauss_mean_square_term (q a x y : ℕ) :
    U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / q) * (starRingEnd ℂ) (U1534.ee (((a * y ^ 2 : ℕ) : ℝ) / q)) =
      U1534.ee ((((x : ℤ) ^ 2 - (y : ℤ) ^ 2 : ℤ) : ℝ) / q) ^ a := by
  rw [gauss_mean_square_conj, ← gauss_mean_square_ee_add, ← gauss_mean_square_ee_nat_mul]
  congr 1; push_cast; ring

private lemma gauss_mean_square_parseval (q : ℕ) (hq : 1 ≤ q) :
    ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 =
      ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        (q : ℝ) * ((((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
          (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have hS : ∀ a, ((‖U1534.gaussS q a‖ : ℂ)) ^ 2 = U1534.gaussS q a * (starRingEnd ℂ) (U1534.gaussS q a) := by
    intro a
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [hS]
  unfold U1534.gaussS
  simp_rw [map_sum, Finset.sum_mul_sum, gauss_mean_square_term]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp_rw [gauss_mean_square_geom q hq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- PROVED. P0088 page 6 display 24 second line, the mean of the reduced quadratic
Gauss sums S(q, a) of page 3 display 8: the sum over 1 <= a <= q, (a, q) = 1, of
|S(q, a)|^2 / phi(q)^2 is << q^eta; here eta = 1/2. Split class HARD: needs
multiplicativity of S(q, a) in q and the prime power evaluation, or the
Parseval identity over a mod q with a count of square roots of unity. -/
theorem gauss_mean_square : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
    ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) := by
  refine ⟨18, by norm_num, ?_⟩
  intro q hq
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set τ : ℝ := (q.divisors.card : ℝ) with hτ
  have h1 : ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have hU : ((Finset.range q).filter (fun x => Nat.Coprime x q)).card = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    apply Finset.filter_congr
    intro x _
    exact Nat.coprime_comm
  have h2 : ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 ≤
      (Nat.totient q : ℝ) * ((q : ℝ) * (2 * τ)) := by
    rw [gauss_mean_square_parseval q hq]
    calc _ ≤ ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), (q : ℝ) * (2 * τ) := by
          apply Finset.sum_le_sum
          intro x hx
          have hx' : Nat.Coprime x q := (Finset.mem_filter.mp hx).2
          have := gauss_mean_square_fiber q x hq hx'
          have : ((((Finset.range q).filter (fun y => Nat.Coprime y q)).filter
              (fun y : ℕ => (q : ℤ) ∣ (x : ℤ) ^ 2 - (y : ℤ) ^ 2)).card : ℝ) ≤ 2 * τ := by
            rw [hτ]; exact_mod_cast this
          exact mul_le_mul_of_nonneg_left this hqpos.le
      _ = _ := by rw [Finset.sum_const, hU, nsmul_eq_mul]
  have h3 : ∑ a ∈ Finset.Icc 1 q, ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
      2 * q * τ / (Nat.totient q : ℝ) := by
    rw [← Finset.sum_div, div_le_div_iff₀ (by positivity) hφpos]
    calc _ ≤ (Nat.totient q : ℝ) * ((q : ℝ) * (2 * τ)) * (Nat.totient q : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hφpos.le
      _ = _ := by ring
  have hτφ : τ ^ 2 * q ≤ 80 * (Nat.totient q : ℝ) ^ 2 := by
    rw [hτ]; exact_mod_cast gauss_mean_square_tau_phi q (by omega)
  have hτ0 : 0 ≤ τ := by positivity
  have h4 : 2 * q * τ / (Nat.totient q : ℝ) ≤ 18 * (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hφpos, ← Real.sqrt_eq_rpow]
    have hs := Real.sq_sqrt hqpos.le
    have hs0 := Real.sqrt_nonneg (q : ℝ)
    have hlhs : 0 ≤ 2 * q * τ := by positivity
    have hrhs : 0 ≤ 18 * Real.sqrt q * (Nat.totient q : ℝ) := by positivity
    have hk := mul_le_mul_of_nonneg_left hτφ (by positivity : (0:ℝ) ≤ 4 * q)
    have hφ2 : 0 ≤ (q : ℝ) * (Nat.totient q : ℝ) ^ 2 := by positivity
    refine (pow_le_pow_iff_left₀ hlhs hrhs two_ne_zero).mp ?_
    have e1 : (2 * q * τ) ^ 2 = 4 * q * (τ ^ 2 * q) := by ring
    have e2 : (18 * Real.sqrt q * (Nat.totient q : ℝ)) ^ 2 =
        324 * (Real.sqrt q) ^ 2 * (Nat.totient q : ℝ) ^ 2 := by ring
    rw [e1, e2, hs]
    nlinarith [hk, hφ2]
  linarith [h1, h3, h4]

/-- PROVED. P0088 page 4 display 15, the arcs M(q, a) with q <= P are pairwise
disjoint when the width parameter R = Q = H/P exceeds 2P, used in the first sum
of page 6 display 24. Split class EASY: |a q' - a' q| <= (q + q')/R < 1 and coprimality. -/
theorem arcs_disjoint {P R : ℝ} (hR : 2 * P < R) {v w : ℕ × ℕ}
    (hv : v ∈ arcPairs P) (hw : w ∈ arcPairs P) {α : ℝ}
    (h1 : α ∈ arc R v) (h2 : α ∈ arc R w) : v = w := by
  obtain ⟨q, a⟩ := v
  obtain ⟨q2, a2⟩ := w
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hv hw
  simp only [arc, Set.mem_ofPred_eq] at h1 h2
  obtain ⟨⟨⟨hq1, hqP⟩, _⟩, _, hcop⟩ := hv
  obtain ⟨⟨⟨hq21, hq2P⟩, _⟩, _, hcop2⟩ := hw
  have hP0 : (0 : ℝ) ≤ P := by
    by_contra h
    push Not at h
    have : ⌊P⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  have hqle : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hqP) (Nat.floor_le hP0)
  have hq2le : (q2 : ℝ) ≤ P := le_trans (by exact_mod_cast hq2P) (Nat.floor_le hP0)
  have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hRpos : 0 < R := by linarith
  have hkey : |((a2 : ℝ) * q - a * q2)| < 1 := by
    have e : ((a2 : ℝ) * q - a * q2) = q2 * (q * α - a) - q * (q2 * α - a2) := by ring
    rw [e]
    have hq0 : (0:ℝ) ≤ q := by positivity
    have hq20 : (0:ℝ) ≤ q2 := by positivity
    calc |(q2:ℝ) * (q * α - a) - q * (q2 * α - a2)|
        ≤ |(q2:ℝ) * (q * α - a)| + |(q:ℝ) * (q2 * α - a2)| := abs_sub _ _
      _ = q2 * |(q:ℝ) * α - a| + q * |(q2:ℝ) * α - a2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hq20]
      _ ≤ q2 * R⁻¹ + q * R⁻¹ := by gcongr
      _ = (q2 + q) / R := by ring
      _ < 1 := by rw [div_lt_one hRpos]; linarith
  have hint : ((a2 * q : ℕ) : ℤ) - ((a * q2 : ℕ) : ℤ) = 0 := by
    have : |(((a2 * q : ℕ) : ℤ) - ((a * q2 : ℕ) : ℤ) : ℝ)| < 1 := by
      push_cast; exact hkey
    have h' : |((a2 * q : ℕ) : ℤ) - ((a * q2 : ℕ) : ℤ)| < 1 := by exact_mod_cast this
    rw [abs_lt] at h'
    omega
  have heq : a2 * q = a * q2 := by omega
  have hd1 : q ∣ q2 := by
    have : q ∣ a * q2 := ⟨a2, by rw [← heq]; ring⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hd2 : q2 ∣ q := by
    have : q2 ∣ a2 * q := ⟨a, by rw [heq]; ring⟩
    exact (Nat.Coprime.symm hcop2).dvd_of_dvd_mul_left this
  have hqq : q = q2 := Nat.dvd_antisymm hd1 hd2
  subst hqq
  have : a = a2 := by
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) heq
    omega
  subst this
  rfl

/-- PROVED. P0088 page 6 display 23: a point of M(q, a) with q <= P outside M0 has
|q alpha - a| > 1/Q0 = P^3/Y, Q0 = Y P^(-3) of display 14. M0 is written as
majorArcs (Y P^(-2)) P. Split class EASY. -/
theorem off_M0 {Y P : ℝ} (hY : 0 < Y) (hP : 0 < P) {v : ℕ × ℕ} (hv : v ∈ arcPairs P)
    {α : ℝ} (hα : α ∉ majorArcs (Y * P ^ (-2 : ℤ)) P) :
    P ^ 3 / Y < |(v.1 : ℝ) * α - v.2| := by
  by_contra h
  push Not at h
  apply hα
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hv
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _, hcop⟩ := hv
  have hinv : ((Y * P ^ (-2 : ℤ)) / P)⁻¹ = P ^ 3 / Y := by
    rw [zpow_neg, zpow_two]
    field_simp
  refine ⟨v.1, h1, ?_, (v.2 : ℤ), ?_, ?_⟩
  · exact le_trans (by exact_mod_cast h2) (Nat.floor_le hP.le)
  · exact Nat.isCoprime_iff_coprime.mpr hcop
  · rw [hinv]; push_cast; exact h

/-- PROVED. P0088 page 6 display 23 and the block range of display 24: for large X,
P = (log X)^B and Y = X^(7/12 + eps/2), one has 8 P^6 Y^(1/2) <= X^(7/18 + eps),
so H/P > 2P and P/H <= Y^(-1/2)/4 for H >= X^(7/18 + eps) P^(-4). Split class MEDIUM:
a power of log X against a power of X. -/
theorem eventually_large {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 3 ≤ X ∧
      8 * (Real.log X ^ B) ^ 6 * Real.sqrt (windowY X ε) ≤ X ^ (7 / 18 + ε) := by
  have hlo := isLittleO_log_rpow_rpow_atTop (6 * B) (show (0:ℝ) < 7 / 72 by norm_num)
  have hb := hlo.bound (show (0:ℝ) < 1 / 8 by norm_num)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 hb
  refine ⟨max X1 3, fun X hX => ?_⟩
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hX1' : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1'
  refine ⟨hX3, ?_⟩
  have h := hX1 X ((le_max_left _ _).trans hX)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _)] at h
  have hpow : (Real.log X ^ B) ^ 6 = Real.log X ^ (6 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]; norm_num [mul_comm]
  have hsq : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4) := by
    unfold windowY
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]; congr 1; ring
  have hmono : X ^ ((7:ℝ) / 72) ≤ X ^ (7 / 72 + 3 * ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
  have hsplit : X ^ (7 / 18 + ε) = X ^ (7 / 72 + 3 * ε / 4) * X ^ (7 / 24 + ε / 4) := by
    rw [← Real.rpow_add hXpos]; congr 1; ring
  rw [hpow, hsq, hsplit]
  have hpos : 0 ≤ X ^ (7 / 24 + ε / 4) := Real.rpow_nonneg hXpos.le _
  have : 8 * Real.log X ^ (6 * B) ≤ X ^ (7 / 72 + 3 * ε / 4) := by linarith
  exact mul_le_mul_of_nonneg_right this hpos

private theorem pointwise_bound_T2sq {Y C β : ℝ} {T : ℂ} (hY : 0 < Y) (hC : 0 < C)
    (hβ : 0 < |β|) (h : ‖T‖ ≤ C * Real.sqrt Y / (1 + Y * |β|)) :
    ‖T‖ ^ 2 ≤ C ^ 2 / Y / β ^ 2 := by
  have h1 : ‖T‖ ≤ C * Real.sqrt Y / (Y * |β|) :=
    h.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hY.le, sq_abs]
  field_simp

/-- PROVED. P0088 page 6 display 24 first line, pointwise form. Off M0, with the arcs
disjoint and display 22 for T2 on every arc, |S2*(alpha)|^2 is at most the sum over
q, a of |S(q, a)|^2/phi(q)^2 C^2/(Y beta^2) on |beta| > P^3/(q Y), beta = alpha - a/q.
Class MEDIUM. -/
theorem pointwise_bound {Y H P C : ℝ} (hY : 0 < Y) (hP : 0 < P) (hC : 0 < C)
    (hRP : 2 * P < H / P)
    (hT2 : ∀ β : ℝ, |β| ≤ P / H → ‖T2 Y P β‖ ≤ C * Real.sqrt Y / (1 + Y * |β|))
    (α : ℝ) (hα : α ∉ majorArcs (Y * P ^ (-2 : ℤ)) P) :
    ‖S2star Y H P α‖ ^ 2 ≤
      ∑ v ∈ arcPairs P, Set.indicator
        {x : ℝ | P ^ 3 / ((v.1 : ℝ) * Y) < |x - (v.2 : ℝ) / v.1|}
        (fun x => ‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2 * (C ^ 2 / Y) /
          (x - (v.2 : ℝ) / v.1) ^ 2) α := by
  have hnn : ∀ v ∈ arcPairs P, 0 ≤ Set.indicator
        {x : ℝ | P ^ 3 / ((v.1 : ℝ) * Y) < |x - (v.2 : ℝ) / v.1|}
        (fun x => ‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2 * (C ^ 2 / Y) /
          (x - (v.2 : ℝ) / v.1) ^ 2) α := fun v _ =>
    Set.indicator_nonneg (fun x _ => by positivity) α
  by_cases hex : ∃ v0 ∈ arcPairs P, α ∈ arc (H / P) v0
  · obtain ⟨v0, hv0, hαv0⟩ := hex
    have hS : S2star Y H P α = U1534.gaussS v0.1 v0.2 / (Nat.totient v0.1 : ℂ) *
        T2 Y P (α - v0.2 / v0.1) := by
      unfold S2star
      rw [Finset.sum_eq_single v0]
      · exact Set.indicator_of_mem hαv0 _
      · intro v hv hne
        apply Set.indicator_of_notMem
        intro hαv
        exact hne (arcs_disjoint hRP hv hv0 hαv hαv0)
      · intro h; exact absurd hv0 h
    refine le_trans ?_ (Finset.single_le_sum hnn hv0)
    have hq1 : (1 : ℝ) ≤ v0.1 := by
      have h := hv0
      simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
      exact_mod_cast h.1.1.1
    have hq0 : (0 : ℝ) < v0.1 := by linarith
    set q : ℝ := (v0.1 : ℝ) with hqdef
    set a : ℝ := (v0.2 : ℝ) with hadef
    set β : ℝ := α - a / q with hβdef
    have hqβ : q * α - a = q * β := by rw [hβdef]; field_simp
    have habsβ : |q * α - a| = q * |β| := by rw [hqβ, abs_mul, abs_of_pos hq0]
    have hHpos : 0 < H / P := by linarith
    have hβle : |β| ≤ P / H := by
      have h := hαv0
      simp only [arc, Set.mem_ofPred_eq] at h
      rw [← hqdef, ← hadef, habsβ, inv_div] at h
      have hPH : 0 ≤ P / H := by
        rw [← inv_div]; exact inv_nonneg.mpr hHpos.le
      nlinarith [abs_nonneg β]
    have hoff := off_M0 hY hP hv0 hα
    rw [← hqdef, ← hadef, habsβ] at hoff
    have hmem : P ^ 3 / (q * Y) < |β| := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hY] at hoff
      nlinarith
    have hβpos : 0 < |β| := lt_trans (by positivity) hmem
    rw [Set.indicator_of_mem (show α ∈ {x : ℝ | P ^ 3 / ((v0.1 : ℝ) * Y) <
        |x - (v0.2 : ℝ) / v0.1|} from hmem)]
    rw [hS]
    have hT := pointwise_bound_T2sq hY hC hβpos (hT2 β hβle)
    have hφ : (0 : ℝ) < Nat.totient v0.1 := by
      exact_mod_cast Nat.totient_pos.mpr (by rw [hqdef] at hq0; exact_mod_cast hq0)
    rw [norm_mul, norm_div, Complex.norm_natCast, mul_pow, div_pow]
    calc ‖U1534.gaussS v0.1 v0.2‖ ^ 2 / (Nat.totient v0.1 : ℝ) ^ 2 * ‖T2 Y P β‖ ^ 2
        ≤ ‖U1534.gaussS v0.1 v0.2‖ ^ 2 / (Nat.totient v0.1 : ℝ) ^ 2 * (C ^ 2 / Y / β ^ 2) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = _ := by ring
  · push Not at hex
    have hS : S2star Y H P α = 0 := by
      unfold S2star
      exact Finset.sum_eq_zero fun v hv => Set.indicator_of_notMem (hex v hv) _
    rw [hS, norm_zero, sq, mul_zero]
    exact Finset.sum_nonneg hnn

private lemma tail_integral_G {r K : ℝ} (hr : 0 < r) :
    Integrable (Set.indicator (Set.Ioi r) fun y : ℝ => K / y ^ 2) ∧
      ∫ y, Set.indicator (Set.Ioi r) (fun y : ℝ => K / y ^ 2) y = K / r := by
  have hI : IntegrableOn (fun y : ℝ => K * y ^ (-2 : ℝ)) (Set.Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hr).const_mul K
  have heq : Set.EqOn (fun y : ℝ => K * y ^ (-2 : ℝ)) (fun y : ℝ => K / y ^ 2) (Set.Ioi r) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hr hy
    simp only
    rw [Real.rpow_neg hy0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).2 (hI.congr_fun heq measurableSet_Ioi), ?_⟩
  rw [integral_indicator measurableSet_Ioi, ← setIntegral_congr_fun measurableSet_Ioi heq,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hr]
  have : (-2:ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

/-- PROVED. P0088 page 6 display 24, the last integral: for r > 0 the function
K/(x - c)^2 on |x - c| > r is integrable with integral 2K/r. Split class MEDIUM. -/
theorem tail_integral {r K : ℝ} (hr : 0 < r) (c : ℝ) :
    Integrable (Set.indicator {x : ℝ | r < |x - c|} fun x => K / (x - c) ^ 2) ∧
      ∫ x, Set.indicator {x : ℝ | r < |x - c|} (fun x => K / (x - c) ^ 2) x = 2 * K / r := by
  obtain ⟨hGi, hGv⟩ := tail_integral_G (K := K) hr
  set G := Set.indicator (Set.Ioi r) fun y : ℝ => K / y ^ 2 with hG
  have hF : ∀ y : ℝ, Set.indicator {y : ℝ | r < |y|} (fun y => K / y ^ 2) y = G y + G (-y) := by
    intro y
    simp only [hG, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi, neg_sq]
    rcases lt_or_ge r y with h | h
    · have : ¬ r < -y := by linarith
      rw [if_pos (lt_abs.2 (Or.inl h)), if_pos h, if_neg this]; ring
    · rcases lt_or_ge r (-y) with h' | h'
      · rw [if_pos (lt_abs.2 (Or.inr h')), if_neg (not_lt.2 h), if_pos h']; ring
      · have : ¬ r < |y| := not_lt.2 (abs_le.2 ⟨by linarith, h⟩)
        rw [if_neg this, if_neg (not_lt.2 h), if_neg (not_lt.2 h')]; ring
  have hfun : (Set.indicator {x : ℝ | r < |x - c|} fun x => K / (x - c) ^ 2) =
      fun x => (fun y => G y + G (-y)) (x - c) := by
    funext x
    show _ = G (x - c) + G (-(x - c))
    rw [← hF (x - c)]
    simp only [Set.indicator, Set.mem_ofPred_eq]
  have hHi : Integrable (fun y => G y + G (-y)) := hGi.add hGi.comp_neg
  rw [hfun]
  refine ⟨hHi.comp_sub_right c, ?_⟩
  rw [integral_sub_right_eq_self (fun y => G y + G (-y)) c, integral_add hGi hGi.comp_neg,
    integral_neg_eq_self, hGv]
  ring

private lemma arc_sum_bound_g10 :
    ‖U1534.gaussS 1 0‖ ^ 2 / (Nat.totient 1 : ℝ) ^ 2 = 1 := by
  simp [U1534.gaussS, U1534.ee]

private lemma arc_sum_bound_inner {P Cg : ℝ} (q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ ⌊P⌋₊)
    (hG : ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Cg * (q : ℝ) ^ (1 / 2 : ℝ)) :
    ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
      ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤
      Cg * (q : ℝ) ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0) := by
  set g : ℕ → ℝ := fun a => ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 with hg
  set X := (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)
  have h1 : ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q), g a
      = ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          (if Nat.Coprime a q then g a else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter] at ha
    simp [ha.2.2]
  have h2 : ∑ a ∈ (Finset.range (⌊P⌋₊ + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          (if Nat.Coprime a q then g a else 0) ≤
        ∑ a ∈ insert 0 X, (if Nat.Coprime a q then g a else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      rcases Nat.eq_zero_or_pos a with h | h
      · simp [h]
      · apply Finset.mem_insert_of_mem
        simp only [X, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h, ha.2.1⟩, ha.2.2⟩
    · intro a _ _
      split_ifs <;> positivity
  have h0X : (0 : ℕ) ∉ X := by simp [X]
  rw [Finset.sum_insert h0X] at h2
  have h3 : ∑ a ∈ X, (if Nat.Coprime a q then g a else 0) = ∑ a ∈ X, g a := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [X, Finset.mem_filter] at ha
    simp [ha.2]
  have h4 : (if Nat.Coprime 0 q then g 0 else 0) = (if q = 1 then 1 else 0) := by
    simp only [Nat.coprime_zero_left]
    split_ifs with h
    · subst h; exact arc_sum_bound_g10
    · rfl
  rw [h3, h4] at h2
  rw [h1]
  linarith

/-- PROVED. P0088 page 6 display 24 last step: with the Gauss mean bound Cg q^(1/2)
over 1 <= a <= q, the sum over the arc pairs q <= P, 0 <= a <= q, of
q |S(q, a)|^2/phi(q)^2 is at most (Cg + 1) P^(5/2); the pair q = 1, a = 0 adds
at most 1. Split class EASY. -/
theorem arc_sum_bound {P Cg : ℝ} (hP : 1 ≤ P) (hCg : 0 ≤ Cg)
    (hG : ∀ q : ℕ, 1 ≤ q →
      ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Cg * (q : ℝ) ^ (1 / 2 : ℝ)) :
    ∑ v ∈ arcPairs P, (v.1 : ℝ) * (‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2) ≤
      (Cg + 1) * P ^ (5 / 2 : ℝ) := by
  set N := ⌊P⌋₊ with hN
  have hNP : (N : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hP0 : 0 ≤ P := by linarith
  rw [arcPairs, Finset.sum_filter, Finset.sum_product]
  have step : ∀ q ∈ Finset.Icc 1 N,
      (∑ a ∈ Finset.range (N + 1), if a ≤ q ∧ Nat.Coprime a q then
        (q : ℝ) * (‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2) else 0) ≤
      Cg * P * P ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have hi := arc_sum_bound_inner (P := P) q hq.1 hq.2 (hG q hq.1)
    have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hq.2) hNP
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hqs : (q : ℝ) ^ (1 / 2 : ℝ) ≤ P ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hq0 hqP (by norm_num)
    have hs0 : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
    calc (q : ℝ) * ∑ a ∈ (Finset.range (N + 1)).filter (fun a => a ≤ q ∧ Nat.Coprime a q),
          ‖U1534.gaussS q a‖ ^ 2 / (Nat.totient q : ℝ) ^ 2
        ≤ (q : ℝ) * (Cg * (q : ℝ) ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0)) :=
          mul_le_mul_of_nonneg_left hi hq0
      _ ≤ Cg * P * P ^ (1 / 2 : ℝ) + (if q = 1 then 1 else 0) := by
          split_ifs with h
          · subst h
            simp only [Nat.cast_one, one_mul]
            have : Cg * (1 : ℝ) ^ (1 / 2 : ℝ) ≤ Cg * P * P ^ (1 / 2 : ℝ) := by
              rw [Real.one_rpow, mul_one]
              have h1 : (1 : ℝ) ≤ P ^ (1 / 2 : ℝ) := Real.one_le_rpow hP (by norm_num)
              have hCP : Cg ≤ Cg * P := by nlinarith
              nlinarith [mul_le_mul hCP h1 zero_le_one (by positivity)]
            linarith
          · simp only [add_zero]
            have := mul_le_mul hqs (le_refl Cg) hCg (by positivity)
            nlinarith [mul_le_mul hqP this (by positivity) hP0]
  refine (Finset.sum_le_sum step).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Finset.sum_ite_eq']
  have hP52 : P ^ (5 / 2 : ℝ) = P * P * P ^ (1 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by linarith),
      Real.rpow_two, sq]
  have h1 : (1 : ℝ) ≤ P ^ (5 / 2 : ℝ) := Real.one_le_rpow hP (by norm_num)
  have hs : 0 ≤ P ^ (1 / 2 : ℝ) := by positivity
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  have hA : (N : ℝ) * (Cg * P * P ^ (1 / 2 : ℝ)) ≤ P * (Cg * P * P ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hNP (by positivity)
  have hB : (if (1 : ℕ) ∈ Finset.Icc 1 N then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [hP52] at h1 ⊢
  nlinarith

/-- The first coordinate of an arc pair is at least one. -/
theorem one_le_of_mem_arcPairs {P : ℝ} {v : ℕ × ℕ} (hv : v ∈ arcPairs P) : 1 ≤ v.1 := by
  simp only [arcPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hv
  exact hv.1.1.1

/-- The exact statement of Prep1121DKLMajorCut.S2star_minor_mean_square, P0088 page 6
display 24, from gauss_mean_square, eventually_large, pointwise_bound, tail_integral
and arc_sum_bound, with display 22 for T2 as the hypothesis T2BoundProp, as in the
parent. No sorry of its own. -/
theorem S2star_minor_mean_square_of_pieces (h2 : T2BoundProp) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H (Real.log X ^ B) \
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B)),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) := by
  intro B hB ε hε hε'
  obtain ⟨C, X1, hC, hT⟩ := h2 B hB ε hε hε'
  obtain ⟨Cg, hCg, hG⟩ := gauss_mean_square
  obtain ⟨X2, hL⟩ := eventually_large hB hε
  refine ⟨2 * C ^ 2 * (Cg + 1), max X1 X2, by positivity, ?_⟩
  intro X H hX hlo _hhi
  have hX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hX2 : X2 ≤ X := (le_max_right _ _).trans hX
  obtain ⟨hX3, hbig⟩ := hL X hX2
  have hXpos : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact Real.exp_one_lt_three.le.trans hX3
  set P := Real.log X ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hlog1 hB.le
  have hP : 0 < P := by linarith
  have hY1 : 1 ≤ Y := Prep1121DKLMajorCut.windowY_ge_one (by linarith) hε
  have hY : 0 < Y := by linarith
  have hsY1 : 1 ≤ Real.sqrt Y := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hY1
  have hsY : 0 < Real.sqrt Y := by linarith
  -- H is at least 8 P^2 Y^(1/2)
  have hz : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hH8 : 8 * P ^ 2 * Real.sqrt Y ≤ H := by
    refine le_trans ?_ hlo
    rw [hz]
    have h4 : 0 < P ^ 4 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h4]
    calc 8 * P ^ 2 * Real.sqrt Y * P ^ 4 = 8 * P ^ 6 * Real.sqrt Y := by ring
      _ ≤ _ := hbig
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hH8
  have hRP : 2 * P < H / P := by
    rw [lt_div_iff₀ hP]
    nlinarith [mul_le_mul_of_nonneg_left hsY1 (by positivity : (0 : ℝ) ≤ 8 * P ^ 2)]
  have hPH : P / H ≤ 1 / (4 * Real.sqrt Y) := by
    rw [div_le_div_iff₀ hHpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hP1 (by positivity : (0 : ℝ) ≤ 4 * P * Real.sqrt Y)]
  have hT2 : ∀ β : ℝ, |β| ≤ P / H → ‖T2 Y P β‖ ≤ C * Real.sqrt Y / (1 + Y * |β|) :=
    fun β hβ => hT X hX1 β (hβ.trans hPH)
  -- the majorant
  set g : ℕ × ℕ → ℝ → ℝ := fun v => Set.indicator
    {x : ℝ | P ^ 3 / ((v.1 : ℝ) * Y) < |x - (v.2 : ℝ) / v.1|}
    (fun x => ‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2 * (C ^ 2 / Y) /
      (x - (v.2 : ℝ) / v.1) ^ 2) with hgdef
  have hr : ∀ v ∈ arcPairs P, 0 < P ^ 3 / ((v.1 : ℝ) * Y) := fun v hv => by
    have : (1 : ℝ) ≤ v.1 := by exact_mod_cast one_le_of_mem_arcPairs hv
    positivity
  have hgi : ∀ v ∈ arcPairs P, Integrable (g v) := fun v hv =>
    (tail_integral (hr v hv) _).1
  have hGi : Integrable (fun x => ∑ v ∈ arcPairs P, g v x) := integrable_finsetSum _ hgi
  have hg0 : ∀ v x, 0 ≤ g v x := fun v x =>
    Set.indicator_nonneg (fun x _ => by positivity) x
  set S : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P)
  have hSm : MeasurableSet S := measurableSet_Ioc.inter
    ((measurableSet_majorArcs H P).diff (measurableSet_majorArcs _ P))
  have hSI : S ⊆ Set.Ioc (0 : ℝ) 1 := Set.inter_subset_left
  have : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSI).trans_lt measure_Ioc_lt_top).ne
  obtain ⟨m2, c2, b2⟩ := Prep1121DKLMajorCut.S2star_props Y H P
  have hfi : IntegrableOn (fun α => ‖S2star Y H P α‖ ^ 2) S := by
    refine (MemLp.of_bound (m2.norm.pow_const 2).aestronglyMeasurable (c2 ^ 2)
      (Filter.Eventually.of_forall fun α => ?_)).integrable le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (b2 α) 2
  -- step 1: pointwise majorant on S
  have step1 : (∫ α in S, ‖S2star Y H P α‖ ^ 2) ≤ ∫ α in S, ∑ v ∈ arcPairs P, g v α :=
    setIntegral_mono_on hfi hGi.integrableOn hSm fun α hα =>
      pointwise_bound hY hP hC hRP hT2 α hα.2.2
  -- step 2: enlarge to the whole line
  have step2 : (∫ α in S, ∑ v ∈ arcPairs P, g v α) ≤ ∫ α, ∑ v ∈ arcPairs P, g v α :=
    setIntegral_le_integral hGi
      (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun v _ => hg0 v x)
  -- step 3: the tail integrals
  have step3 : (∫ α, ∑ v ∈ arcPairs P, g v α) =
      2 * C ^ 2 / P ^ 3 * ∑ v ∈ arcPairs P,
        (v.1 : ℝ) * (‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2) := by
    rw [integral_finsetSum _ hgi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [(tail_integral (hr v hv) _).2]
    have hq : (0 : ℝ) < v.1 := by
      have : (1 : ℝ) ≤ v.1 := by exact_mod_cast one_le_of_mem_arcPairs hv
      linarith
    field_simp
  -- step 4: the arithmetic of display 24
  have step4 := arc_sum_bound hP1 hCg.le hG
  have hP3 : P ^ (5 / 2 : ℝ) / P ^ 3 = P ^ (-(1 / 2 : ℝ)) := by
    rw [show (P ^ 3 : ℝ) = P ^ (3 : ℝ) by norm_cast, ← Real.rpow_sub hP]
    norm_num
  calc (∫ α in S, ‖S2star Y H P α‖ ^ 2)
      ≤ 2 * C ^ 2 / P ^ 3 * ∑ v ∈ arcPairs P,
        (v.1 : ℝ) * (‖U1534.gaussS v.1 v.2‖ ^ 2 / (Nat.totient v.1 : ℝ) ^ 2) :=
        step1.trans (step2.trans step3.le)
    _ ≤ 2 * C ^ 2 / P ^ 3 * ((Cg + 1) * P ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left step4 (by positivity)
    _ = 2 * C ^ 2 * (Cg + 1) * (P ^ (5 / 2 : ℝ) / P ^ 3) := by ring
    _ = 2 * C ^ 2 * (Cg + 1) * P ^ (-(1 / 2 : ℝ)) := by rw [hP3]

example : type_of% @Prep1121DKLMajorCut.S2star_minor_mean_square :=
  S2star_minor_mean_square_of_pieces

/-- PROVED. P0088 page 6 display 24 with no hypothesis: display 22 for T2,
T2BoundProp, is already PROVED on main as Prep1121DKLMajorCut.T2_bound_of_pieces. -/
theorem S2star_minor_mean_square_unconditional :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H (Real.log X ^ B) \
            majorArcs (windowY X ε * (Real.log X ^ B) ^ (-2 : ℤ)) (Real.log X ^ B)),
          ‖S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) :=
  S2star_minor_mean_square_of_pieces Prep1121DKLMajorCut.T2_bound_of_pieces

open Prep1121DKLMajorCut in
/-- PROVED. P0088 page 6 display 24, the bound of Prep1121KLMajor.bound24 with no
hypothesis: the proof of Prep1121DKLMajorCut.bound24_of_pieces, with its open leaf
replaced by S2star_minor_mean_square_unconditional. -/
theorem bound24_unconditional : BlockErrorBound termC := by
  intro B hB ε hε hε'
  obtain ⟨C, X0, hC, k⟩ := S2star_minor_mean_square_unconditional B hB ε hε hε'
  refine ⟨Real.sqrt 2 * Real.sqrt C, max X0 3, by positivity, ?_⟩
  intro X H hX hlo hhi n
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY1 := Prep1121DKLMajorCut.windowY_ge_one (by linarith : (1 : ℝ) ≤ X) hε
  set Y := windowY X ε
  set P := Real.log X ^ B
  have hc := termC_cauchy X Y H P n
  have h1 := S1_mean_square (sub_nonneg.mpr (windowY_le (by linarith) hε')) hY1
  have h3 := k X H hXa hlo hhi
  have hs1 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1, ‖primeSum X Y α‖ ^ 2) ≤
      Real.sqrt 2 * Real.sqrt Y := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs3 : Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        (majorArcs H P \ majorArcs (Y * P ^ (-2 : ℤ)) P), ‖S2star Y H P α‖ ^ 2) ≤
      Real.sqrt C * P ^ (-(1 / 4 : ℝ)) := by
    have hq : Real.sqrt (P ^ (-(1 / 2 : ℝ))) = P ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le]
      norm_num
    rw [← hq, ← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt h3
  have hnn1 : 0 ≤ Real.sqrt 2 * Real.sqrt Y := by positivity
  calc ‖termC X Y H P n‖ ≤ _ := hc
    _ ≤ (Real.sqrt 2 * Real.sqrt Y) * (Real.sqrt C * P ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul hs1 hs3 (Real.sqrt_nonneg _) hnn1
    _ = Real.sqrt 2 * Real.sqrt C * Real.sqrt Y * P ^ (-(1 / 4 : ℝ)) := by ring

example : type_of% @Prep1121KLMajor.bound24 := fun _ => bound24_unconditional

end LeanLab.KumchevLiu2007.S2starMinorSplit1122

#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.one_le_of_mem_arcPairs
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.S2star_minor_mean_square_of_pieces
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.gauss_mean_square
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.arcs_disjoint
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.off_M0
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.eventually_large
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.pointwise_bound
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.tail_integral
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.arc_sum_bound
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.S2star_minor_mean_square_unconditional
#print axioms LeanLab.KumchevLiu2007.S2starMinorSplit1122.bound24_unconditional
