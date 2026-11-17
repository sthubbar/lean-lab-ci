/-
Kumchev and Liu 2007, P0088, page 11, the first display of the proof of
Lemma 3.4: the rough indicator Phi(k, z) of page 4 display 10 is opened by the
Moebius function over the divisors d of k that divide Pi(z), the product of
the primes below z. Here "d divides Pi(z)" is written as: every prime factor
of d is below z. Divisors that are not squarefree carry Moebius value zero, so
this is the same sum as over the squarefree d dividing Pi(z).

This is a proved helper for the open leaves under `lemma34_second_sum_dyadic`
and `lemma34_first_sum`. It does not prove any of them: the three cases that
follow on page 11 use Lemmas 3.1 and 3.2, which P0088 cites to Liu and Zhan
1997.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace LeanLab.KumchevLiu2007.Eq33RouteD
open Real Complex LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- P0088 page 11, first display of the proof of Lemma 3.4, for one k: for a
positive integer k, Phi(k, z) is the sum of the Moebius function over the
divisors d of k all of whose prime factors are below z. -/
theorem roughWeight_eq_moebius_sum (z : ℝ) (k : ℕ) (hk : 0 < k) :
    roughWeight z k =
      ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  set P : Finset ℕ := k.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hP
  set r : ℕ := ∏ p ∈ P, p with hr
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hrk : r ∣ k :=
    Finset.prod_primes_dvd k (fun p hp => (hPprime p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  have hr0 : r ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hPprime p hp).ne_zero)
  have hmemP : ∀ p : ℕ, p.Prime → p ∣ r → p ∈ P := by
    intro p hp hpr
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpr
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp (hPprime q hq)).mp hpq
    rw [this]; exact hq
  have hsub : r.divisors ⊆
      k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) := by
    intro d hd
    have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdr.trans hrk, hk.ne'⟩, ?_⟩
    intro p hp hpd
    exact (Finset.mem_filter.mp (hmemP p hp (hpd.trans hdr))).2
  have hstep1 : ∑ d ∈ r.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    apply Finset.sum_subset hsub
    intro d hd hnd
    obtain ⟨hdk, hsm⟩ := Finset.mem_filter.mp hd
    by_contra hne
    have hmu : ArithmeticFunction.moebius d ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    have hdr : d ∣ r := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      refine Finset.mem_filter.mpr ⟨?_, hsm p hpp hpd⟩
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Nat.dvd_of_mem_divisors hdk), hk.ne'⟩
    exact hnd (Nat.mem_divisors.mpr ⟨hdr, hr0⟩)
  have hstep2 : ∑ d ∈ r.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      if r = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℂ => f r)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
      ArithmeticFunction.intCoe_apply] at h
    exact h
  rw [← hstep1, hstep2]
  unfold roughWeight
  have hiff : (∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)) ↔ r = 1 := by
    constructor
    · intro h
      have hPe : P = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        have := h p (Nat.prime_of_mem_primeFactors hp1) (Nat.dvd_of_mem_primeFactors hp1)
        linarith
      rw [hr, hPe, Finset.prod_empty]
    · intro h p hp hpk
      by_contra hlt
      push Not at hlt
      have hpP : p ∈ P :=
        Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpk, hk.ne'⟩, hlt⟩
      have hpr : p ∣ r := Finset.dvd_prod_of_mem _ hpP
      rw [h] at hpr
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpr)
  by_cases hc : ∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)
  · have h1 : r = 1 := hiff.mp hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true h1)]
  · have h1 : ¬ r = 1 := fun h => hc (hiff.mpr h)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false h1)]

/-- P0088 page 11, first display of the proof of Lemma 3.4, for a sum over k:
for any complex F and any N, the sum over k from 1 to N of Phi(k, z) F(k) is
the sum over the d from 1 to N with all prime factors below z of the Moebius
function of d times the sum of F over the multiples k of d from 1 to N. In the
paper F(k) is the sum over m of a_m g_t(m k) e(alpha m^2 k^2), and the
multiples of d are written k d. -/
theorem sum_roughWeight_eq_moebius_sum (z : ℝ) (N : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 N, roughWeight z k * F k =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => d ∣ k), F k := by
  have h1 : ∑ k ∈ Finset.Icc 1 N, roughWeight z k * F k =
      ∑ k ∈ Finset.Icc 1 N,
        ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * F k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [roughWeight_eq_moebius_sum z k (Finset.mem_Icc.mp hk).1, Finset.sum_mul]
  rw [h1]
  simp only [Finset.mul_sum]
  apply Finset.sum_comm'
  intro k d
  simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, ⟨hdk, hk0⟩, hsm⟩
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdk hk1
    have hdN : d ≤ N := (Nat.le_of_dvd hk1 hdk).trans hkN
    exact ⟨⟨⟨hk1, hkN⟩, hdk⟩, ⟨hd1, hdN⟩, hsm⟩
  · rintro ⟨⟨⟨hk1, hkN⟩, hdk⟩, ⟨hd1, hdN⟩, hsm⟩
    exact ⟨⟨hk1, hkN⟩, ⟨hdk, by omega⟩, hsm⟩

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, the choice of s. Let
p_1, ..., p_r be nonnegative reals, each at most z, with product at least V,
where V exceeds one. Then there is an index n below r with
p_1 ... p_n < V ≤ p_1 ... p_(n+1) and V / z ≤ p_1 ... p_n. In the paper the
p_i are the prime factors of d in decreasing order, V = y x^(-1/2) L^(-B), and
the index is called s. This is existence only; uniqueness holds when every
entry is at least one, as for primes, and is not proved here. -/
theorem prefix_product_crossing (l : List ℝ) (z V : ℝ) (hz : 0 < z)
    (hl0 : ∀ x ∈ l, 0 ≤ x) (hlz : ∀ x ∈ l, x ≤ z) (hV1 : 1 < V) (hV : V ≤ l.prod) :
    ∃ n : ℕ, n < l.length ∧ (l.take n).prod < V ∧ V ≤ (l.take (n + 1)).prod ∧
      V / z ≤ (l.take n).prod := by
  have hex : ∃ m : ℕ, V ≤ (l.take m).prod := ⟨l.length, by simpa using hV⟩
  have hm := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hm
    simp at hm
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : ¬ V ≤ (l.take n).prod := Nat.find_min hex (by omega)
  have hlen : n < l.length := by
    by_contra hge
    apply hmin
    have : l.take n = l := List.take_of_length_le (by omega)
    rw [this]
    exact hV
  rw [hn] at hm
  refine ⟨n, hlen, lt_of_not_ge hmin, hm, ?_⟩
  have hsucc : (l.take (n + 1)).prod = (l.take n).prod * l[n] := List.prod_take_succ l n hlen
  have hpre : 0 ≤ (l.take n).prod :=
    List.prod_nonneg (fun x hx => hl0 x (List.mem_of_mem_take hx))
  have hx : l[n] ≤ z := hlz _ (List.getElem_mem hlen)
  rw [div_le_iff₀ hz]
  calc V ≤ (l.take n).prod * l[n] := by rw [← hsucc]; exact hm
    _ ≤ (l.take n).prod * z := mul_le_mul_of_nonneg_left hx hpre

/-- P0088 page 11, Case 1 of the proof of Lemma 3.4, the bound on the
convolution b_r, the sum over d m = r of a_m mu(d) with side conditions on d.
If every a_m has norm at most K then b_r has norm at most K times the number
of divisors of r. Here the pair (d, m) is written (d, r / d) and Q is any side
condition on d, such as d in a dyadic range and d dividing Pi(z). -/
theorem moebius_convolution_norm_le (a : ℕ → ℂ) (K : ℝ) (hK : ∀ m : ℕ, ‖a m‖ ≤ K)
    (r : ℕ) (Q : ℕ → Prop) :
    ‖∑ d ∈ r.divisors.filter Q, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * a (r / d)‖ ≤
      K * (r.divisors.card : ℝ) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hterm : ∀ d ∈ r.divisors.filter Q,
      ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * a (r / d)‖ ≤ K := by
    intro d _
    rw [norm_mul, Complex.norm_intCast]
    have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * ‖a (r / d)‖
        ≤ 1 * K := mul_le_mul h1 (hK _) (norm_nonneg _) zero_le_one
      _ = K := one_mul K
  calc ‖∑ d ∈ r.divisors.filter Q, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * a (r / d)‖
      ≤ ∑ d ∈ r.divisors.filter Q,
          ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * a (r / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ r.divisors.filter Q, K := Finset.sum_le_sum hterm
    _ = ((r.divisors.filter Q).card : ℝ) * K := by simp
    _ ≤ (r.divisors.card : ℝ) * K :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hK0
    _ = K * (r.divisors.card : ℝ) := mul_comm _ _

/-- The multiples of a positive d from 1 to N are the d j with j from 1 to
N / d. This is the change of variable k to k d in the first display of the
proof of P0088 page 11 Lemma 3.4. -/
theorem sum_multiples_eq (d N : ℕ) (hd : 0 < d) (F : ℕ → ℂ) :
    ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => d ∣ k), F k =
      ∑ j ∈ Finset.Icc 1 (N / d), F (d * j) := by
  symm
  refine Finset.sum_bij (fun j _ => d * j) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right d j⟩
    · exact Nat.mul_pos hd hj1
    · have := (Nat.le_div_iff_mul_le hd).mp hj2
      rw [mul_comm]; exact this
  · intro j1 _ j2 _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro k hk
    obtain ⟨hk1, c, rfl⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1', hkN⟩ := Finset.mem_Icc.mp hk1
    refine ⟨c, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra h0
      have : c = 0 := by omega
      rw [this] at hk1'
      simp at hk1'
    · rw [Nat.le_div_iff_mul_le hd, mul_comm]; exact hkN
  · intro j _
    rfl

/-- P0088 page 11, the first display of the proof of Lemma 3.4, in the form
of the paper: the sum over k from 1 to N of Phi(k, z) F(k) is the sum over the
d from 1 to N with all prime factors below z of mu(d) times the sum over j
from 1 to N / d of F(d j). -/
theorem sum_roughWeight_eq_moebius_double_sum (z : ℝ) (N : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 N, roughWeight z k * F k =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ j ∈ Finset.Icc 1 (N / d), F (d * j) := by
  rw [sum_roughWeight_eq_moebius_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_multiples_eq d N (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1 F]

end LeanLab.KumchevLiu2007.Eq33RouteD
