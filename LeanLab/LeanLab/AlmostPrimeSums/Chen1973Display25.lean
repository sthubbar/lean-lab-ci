/-
AI-written Lean code, Claude, 2026-10-21, session 20261021T0217Z-cloud56, unit U-6814, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, p. 171, display (25), read from the lab copy
papers/P0002.pdf, page image rendered with pdftoppm.

Chen's display (25) ends with
`∑_{q ≤ z, (q,x)=1} μ²(q)/(ψ(q)φ(q)) · φ(qx)/(qx) · log(z/q)
   = (φ(x)/x) (log x^{1/4-ε/2}) ∏_{p∤x} (1 + 1/(p(p-2))) + O(1) = (1/8 - ε/4)(log x)/C_x + O(1)`,
`z = (x^{1/2-ε})^{1/2}`, `x` even. The first inequality of (25) is `Chen1973V.chen25_lower`.
This file proves the two equalities, with an O(1) that is uniform in `x` and `ε`:

* `summable_of_primes`: a nonnegative multiplicative `f` vanishing on prime powers `p^e`, `e ≥ 2`,
  with bounded prime sums is summable, by the smooth-number Euler product.
* `w`, `a`: Chen's weight `μ²(q)/(qψ(q)) = ∏_{p∣q} 1/(p(p-2))` on `q` prime to `x`.
* `tsum_a_mul_tsum_hq`: `∑ a_x · ∑ h_x = 1` by the Euler products, where `h_x` is the lab's
  `Euler23.hq` of P0032, local factor `1 - 1/(p-1)²`; so `∑ a_x = ∏_{p∤x, p>2} (1 + 1/(p(p-2)))`.
* `totient_div_mul_tsum_a`: `φ(x)/x · ∑ a_x = 1/(2 C_x)` for even `x`, `C_x` the lab's `CN x`.
* `chen25_main`: `|T(x,z) - log z/(2C_x)| ≤ B` for even `x`, `z ≥ 1`, one absolute `B`; the
  error is `∑_q a(q) log q`, by Rankin's weight `√q`.
* `chen_display25`: the paper's form, `|T - (1/8 - ε/4) log x / C_x| ≤ B` for `ε ≤ 1/2`.
* `chen_display25_S`: `S ≥ (1/8 - ε/4) log x / C_x - B` for every real `ε`.

All unconditional. Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.Chen1973V
import LeanLab.RieselVaughan1983.Euler23
import LeanLab.ChenDoubleSieve.Statements

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Display25

open LeanLab.AlmostPrimeSums.Chen1973V
open LeanLab.RieselVaughan1983.Euler23 (hq hq_one hq_zero hq_mul summable_hq hasProd_hq K
  tsum_hq_mul tsum_h1_eq_twinC hq_one_prime)

/-! ### A summability criterion -/

/-- A nonnegative multiplicative `f` with `f(p^e) = 0` for `e ≥ 2` and bounded sums over
primes is summable. -/
lemma summable_of_primes {f : ℕ → ℝ} (h0 : f 0 = 0) (hnn : ∀ n, 0 ≤ f n) (h1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hpow : ∀ {p e : ℕ}, p.Prime → 2 ≤ e → f (p ^ e) = 0) (C : ℝ)
    (hC : ∀ N : ℕ, ∑ p ∈ N.primesBelow, f p ≤ C) : Summable f := by
  have hloc : ∀ {p : ℕ}, p.Prime → HasSum (fun e : ℕ => f (p ^ e)) (1 + f p) := by
    intro p hp
    have : ∀ e ∉ ({0, 1} : Finset ℕ), f (p ^ e) = 0 := by
      intro e he
      simp only [mem_insert, mem_singleton, not_or] at he
      exact hpow hp (by omega)
    convert hasSum_sum_of_ne_finset_zero this using 1
    · simp [h1]
    · infer_instance
  have hnorm : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖f (p ^ e)‖) := by
    intro p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnn _)] using (hloc hp).summable
  refine summable_of_sum_range_le (c := Real.exp C) hnn fun N => ?_
  have H := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := f) h1 (fun h => hmul h) (fun hp => hnorm hp) N).2
  have H' := (hasSum_subtype_iff_indicator (f := f) (s := (N.smoothNumbers : Set ℕ))).mp
    (by exact H)
  have e1 : ∑ n ∈ range N, f n = ∑ n ∈ range N, (N.smoothNumbers : Set ℕ).indicator f n := by
    refine sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with h | hpos
    · subst h; rw [Set.indicator_apply]; split_ifs <;> simp [h0]
    · rw [Set.indicator_of_mem]
      exact Nat.mem_smoothNumbers_of_lt hpos (mem_range.mp hn)
  rw [e1]
  calc _ ≤ ∏ p ∈ N.primesBelow, ∑' e : ℕ, f (p ^ e) := by
        apply sum_le_hasSum _ _ H'
        intro i _
        by_cases hi : i ∈ (N.smoothNumbers : Set ℕ)
        · rw [Set.indicator_of_mem hi]; exact hnn i
        · rw [Set.indicator_of_notMem hi]
    _ = ∏ p ∈ N.primesBelow, (1 + f p) :=
        prod_congr rfl fun p hp => (hloc (Nat.prime_of_mem_primesBelow hp)).tsum_eq
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (f p) :=
        prod_le_prod₀ (fun p _ => by linarith [hnn p])
          (fun p _ => by linarith [Real.add_one_le_exp (f p)])
    _ = Real.exp (∑ p ∈ N.primesBelow, f p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp C := Real.exp_le_exp.mpr (hC N)

/-! ### Chen's weight -/

/-- `w(q) = ∏_{p∣q} 1/(p(p-2))`, Chen's `μ²(q)/(qψ(q))` on squarefree `q`; `w(q) = 0` for even
`q` since the factor at `2` is `1/0 = 0`. -/
def w (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, 1 / ((p : ℝ) * ((p : ℝ) - 2))

/-- `a_x(q) = μ²(q) [(q,x)=1] / (qψ(q))`. -/
def a (x q : ℕ) : ℝ := if Squarefree q ∧ q.Coprime x then w q else 0

lemma w_nonneg (q : ℕ) : 0 ≤ w q := by
  unfold w
  refine prod_nonneg fun p hp => ?_
  have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  apply one_div_nonneg.mpr
  apply mul_nonneg <;> linarith

lemma w_mul {m n : ℕ} (h : m.Coprime n) : w (m * n) = w m * w n := by
  unfold w
  rw [h.primeFactors_mul, prod_union h.disjoint_primeFactors]

lemma a_nonneg (x q : ℕ) : 0 ≤ a x q := by
  unfold a; split_ifs
  · exact w_nonneg q
  · exact le_rfl

lemma a_zero (x : ℕ) : a x 0 = 0 := by simp [a]

lemma a_one (x : ℕ) : a x 1 = 1 := by simp [a, w]

lemma a_mul (x : ℕ) {m n : ℕ} (h : m.Coprime n) : a x (m * n) = a x m * a x n := by
  unfold a
  have hsq : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
    rw [Nat.squarefree_mul_iff]; exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  have hcop : (m * n).Coprime x ↔ m.Coprime x ∧ n.Coprime x := Nat.coprime_mul_iff_left
  by_cases hm : Squarefree m ∧ m.Coprime x <;> by_cases hn : Squarefree n ∧ n.Coprime x
  · rw [if_pos ⟨hsq.2 ⟨hm.1, hn.1⟩, hcop.2 ⟨hm.2, hn.2⟩⟩, if_pos hm, if_pos hn, w_mul h]
  · rw [if_neg, if_neg hn, mul_zero]
    rintro ⟨h1, h2⟩; exact hn ⟨(hsq.1 h1).2, (hcop.1 h2).2⟩
  · rw [if_neg, if_neg hm, zero_mul]
    rintro ⟨h1, h2⟩; exact hm ⟨(hsq.1 h1).1, (hcop.1 h2).1⟩
  · rw [if_neg, if_neg hm, zero_mul]
    rintro ⟨h1, h2⟩; exact hm ⟨(hsq.1 h1).1, (hcop.1 h2).1⟩

lemma not_squarefree_prime_pow {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) : ¬ Squarefree (p ^ e) := by
  intro h
  have hd : p * p ∣ p ^ e := by
    rw [← pow_two]; exact pow_dvd_pow p he
  have := h p hd
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

lemma a_pow (x : ℕ) {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) : a x (p ^ e) = 0 := by
  unfold a; rw [if_neg]; rintro ⟨h, -⟩; exact not_squarefree_prime_pow hp he h

lemma a_prime (x : ℕ) {p : ℕ} (hp : p.Prime) :
    a x p = if p ∣ x then 0 else 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  unfold a w
  rw [hp.primeFactors, prod_singleton]
  by_cases hd : p ∣ x
  · rw [if_pos hd, if_neg]; rintro ⟨-, hc⟩; exact (hp.coprime_iff_not_dvd.mp hc) hd
  · rw [if_neg hd, if_pos ⟨hp.prime.squarefree, hp.coprime_iff_not_dvd.mpr hd⟩]

lemma a_le_a_one (x n : ℕ) : a x n ≤ a 1 n := by
  unfold a
  by_cases h : Squarefree n ∧ n.Coprime x
  · rw [if_pos h, if_pos ⟨h.1, Nat.coprime_one_right n⟩]
  · rw [if_neg h]; split_ifs
    · exact w_nonneg n
    · exact le_rfl

/-- Rankin's majorant `b(n) = a_1(n) √n`. -/
def b (n : ℕ) : ℝ := a 1 n * √(n : ℝ)

lemma b_nonneg (n : ℕ) : 0 ≤ b n := mul_nonneg (a_nonneg 1 n) (Real.sqrt_nonneg _)

lemma b_prime_le {p : ℕ} (hp : p.Prime) : b p ≤ 3 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  unfold b
  rw [a_prime 1 hp, if_neg (fun h => hp.one_lt.ne' (Nat.dvd_one.mp h))]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr : (p : ℝ) ^ (3 / 2 : ℝ) = p * √(p : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hr]
  have hs : 0 < √(p : ℝ) := Real.sqrt_pos.mpr hp0
  have hss : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt hp0.le
  rcases hp.two_le.lt_or_eq with h3 | h2
  · have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
    have hd : 0 < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
    have e : √(p : ℝ) * ((p : ℝ) * √(p : ℝ)) = (p : ℝ) * p := by linear_combination (p : ℝ) * hss
    rw [div_mul_eq_mul_div, one_mul, ← div_eq_mul_inv, div_le_div_iff₀ hd (by positivity), e]
    nlinarith
  · subst h2; norm_num

lemma summable_b : Summable b := by
  have hS : Summable (fun n : ℕ => 3 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 3
  refine summable_of_primes (f := b) (by simp [b, a_zero]) b_nonneg (by simp [b, a_one])
    (fun {m n} h => ?_) (fun {p e} hp he => by simp [b, a_pow 1 hp he])
    (∑' n : ℕ, 3 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) (fun N => ?_)
  · unfold b
    rw [a_mul 1 h, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]; ring
  · calc ∑ p ∈ N.primesBelow, b p ≤ ∑ p ∈ N.primesBelow, 3 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
          sum_le_sum fun p hp => b_prime_le (Nat.prime_of_mem_primesBelow hp)
      _ ≤ _ := hS.sum_le_tsum _ (fun n _ => by positivity)

lemma a_le_b (x n : ℕ) : a x n ≤ b n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [a_zero, b]
  · have h1 : (1 : ℝ) ≤ √(n : ℝ) := by
      rw [Real.one_le_sqrt]; exact_mod_cast h
    calc a x n ≤ a 1 n := a_le_a_one x n
      _ ≤ a 1 n * √(n : ℝ) := le_mul_of_one_le_right (a_nonneg 1 n) h1

lemma log_le_two_sqrt (n : ℕ) : Real.log n ≤ 2 * √(n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hn.le] at this
    linarith

lemma alog_le_b (x n : ℕ) : a x n * Real.log n ≤ 2 * b n := by
  calc a x n * Real.log n ≤ a 1 n * Real.log n :=
        mul_le_mul_of_nonneg_right (a_le_a_one x n) (Real.log_natCast_nonneg n)
    _ ≤ a 1 n * (2 * √(n : ℝ)) := mul_le_mul_of_nonneg_left (log_le_two_sqrt n) (a_nonneg 1 n)
    _ = 2 * b n := by unfold b; ring

lemma summable_a (x : ℕ) : Summable (a x) :=
  Summable.of_nonneg_of_le (a_nonneg x) (a_le_b x) summable_b

lemma summable_alog (x : ℕ) : Summable (fun n => a x n * Real.log n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (a_nonneg x n) (Real.log_natCast_nonneg n))
    (alog_le_b x) (summable_b.mul_left 2)

/-! ### The Euler product -/

lemma hasProd_a (x : ℕ) :
    HasProd (Set.mulIndicator {p | p.Prime} fun p => 1 + a x p) (∑' n, a x n) := by
  have hloc : ∀ {p : ℕ}, p.Prime → HasSum (fun e : ℕ => a x (p ^ e)) (1 + a x p) := by
    intro p hp
    have : ∀ e ∉ ({0, 1} : Finset ℕ), a x (p ^ e) = 0 := by
      intro e he
      simp only [mem_insert, mem_singleton, not_or] at he
      exact a_pow x hp (by omega)
    convert hasSum_sum_of_ne_finset_zero this using 1
    · simp [a_one]
    · infer_instance
  have hs : Summable (fun n => ‖a x n‖) :=
    (summable_a x).congr fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (a_nonneg x n)]
  have H := EulerProduct.eulerProduct_hasProd_mulIndicator (f := a x) (a_one x)
    (fun h => a_mul x h) hs (a_zero x)
  convert H using 1
  funext p
  by_cases hp : p.Prime
  · have hp' : p ∈ {p : ℕ | p.Prime} := hp
    rw [Set.mulIndicator_of_mem hp', Set.mulIndicator_of_mem hp', (hloc hp).tsum_eq]
  · have hp' : p ∉ {p : ℕ | p.Prime} := hp
    rw [Set.mulIndicator_of_notMem hp', Set.mulIndicator_of_notMem hp']

lemma local_one (x : ℕ) {p : ℕ} (hp : p.Prime) : (1 + a x p) * (1 + hq x p) = 1 := by
  rw [a_prime x hp]
  by_cases hd : p ∣ x
  · have : hq x p = 0 := by
      unfold hq; rw [if_neg]; rintro ⟨-, hc⟩; exact (hp.coprime_iff_not_dvd.mp hc) hd
    rw [if_pos hd, this]; norm_num
  · rw [if_neg hd]
    rcases hp.two_le.lt_or_eq with h3 | h2
    · have hodd : Odd p := hp.odd_of_ne_two (by omega)
      have hq' : hq x p = -(1 / ((p : ℝ) - 1) ^ 2) := by
        simp [hq, hodd, hp.coprime_iff_not_dvd.mpr hd, moebius_apply_prime hp,
          Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, neg_div]
      rw [hq']
      have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
      have e1 : (p : ℝ) - 2 ≠ 0 := by linarith
      have e2 : (p : ℝ) - 1 ≠ 0 := by linarith
      have e3 : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    · subst h2
      have : hq x 2 = 0 := by unfold hq; rw [if_neg]; rintro ⟨h, -⟩; exact (Nat.not_odd_iff_even.mpr even_two) h
      rw [this]; norm_num

/-- **`∑ a_x · ∑ h_x = 1`**, the two Euler products have reciprocal local factors. -/
theorem tsum_a_mul_tsum_hq (x : ℕ) : (∑' n, a x n) * (∑' n, hq x n) = 1 := by
  have H := (hasProd_a x).mul (hasProd_hq x)
  have e : (fun p => (Set.mulIndicator {p | p.Prime} (fun p => 1 + a x p)) p *
      (Set.mulIndicator {p | p.Prime} (fun p => 1 + hq x p)) p) = fun _ => (1 : ℝ) := by
    funext p
    by_cases hp : p.Prime
    · have hp' : p ∈ {p : ℕ | p.Prime} := hp
      rw [Set.mulIndicator_of_mem hp', Set.mulIndicator_of_mem hp', local_one x hp]
    · have hp' : p ∉ {p : ℕ | p.Prime} := hp
      rw [Set.mulIndicator_of_notMem hp', Set.mulIndicator_of_notMem hp', mul_one]
  rw [e] at H
  exact H.unique hasProd_one

/-- `∑ a_x · twinC = K(x) = ∏_{p∣x}(1 + h_1(p))`, for `x ≠ 0`. -/
theorem tsum_a_mul_twinC {x : ℕ} (hx : x ≠ 0) :
    (∑' n, a x n) * LeanLab.ChenExplicit.twinC = K x := by
  rw [← tsum_h1_eq_twinC, tsum_hq_mul hx, ← mul_assoc, tsum_a_mul_tsum_hq, one_mul]

lemma totient_div_eq {x : ℕ} (h : 0 < x) :
    (x.totient : ℝ) / x = ∏ p ∈ x.primeFactors, (1 - 1 / (p : ℝ)) := by
  have := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors x)
  push_cast at this
  rw [this, mul_div_cancel_left₀ _ (by exact_mod_cast h.ne')]
  simp [one_div]

/-- For even `x`: `φ(x)/x · K(x) · ∏_{p∣x, p>2} (p-1)/(p-2) = 1/2`. -/
lemma totient_K_oddFactor {x : ℕ} (he : Even x) (hx : x ≠ 0) :
    (x.totient : ℝ) / x * K x * LeanLab.ChenDoubleSieve.oddFactor x = 1 / 2 := by
  rw [totient_div_eq (Nat.pos_of_ne_zero hx), K, ← prod_mul_distrib, LeanLab.ChenDoubleSieve.oddFactor]
  have h2 : 2 ∈ x.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp he, hx⟩
  have hf : x.primeFactors.filter (fun p => ¬ 2 < p) = {2} := by
    ext p
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hp, hlt⟩
      have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
    · rintro rfl; exact ⟨h2, by omega⟩
  rw [← prod_filter_mul_prod_filter_not x.primeFactors (fun p => 2 < p), hf, prod_singleton,
    mul_comm, ← mul_assoc, ← prod_mul_distrib]
  have h1 : ∀ p ∈ x.primeFactors.filter (fun p => 2 < p),
      ((p : ℝ) - 1) / ((p : ℝ) - 2) * ((1 - 1 / (p : ℝ)) * (1 + hq 1 p)) = 1 := by
    intro p hp
    simp only [mem_filter] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp.1
    rw [hq_one_prime hpp hp.2]
    have h3' : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have e1 : (p : ℝ) - 2 ≠ 0 := by linarith
    have e2 : (p : ℝ) - 1 ≠ 0 := by linarith
    have e3 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [prod_congr rfl h1, prod_const_one, one_mul]
  have : hq 1 2 = 0 := by
    unfold hq; rw [if_neg]; rintro ⟨h, -⟩; exact (Nat.not_odd_iff_even.mpr even_two) h
  rw [this]; norm_num

/-- **Chen (25), the Euler product step**: for even `x ≥ 2`,
`φ(x)/x · ∏_{p∤x} (1 + 1/(p(p-2))) = φ(x)/x · ∑_{(q,x)=1} μ²(q)/(qψ(q)) = 1/(2 C_x)`. -/
theorem totient_div_mul_tsum_a {x : ℕ} (he : Even x) (hx : x ≠ 0) :
    (x.totient : ℝ) / x * (∑' n, a x n) = 1 / (2 * LeanLab.ChenDoubleSieve.CN x) := by
  have hT := LeanLab.ChenExplicit.twinC_pos
  have hO : 0 < LeanLab.ChenDoubleSieve.oddFactor x :=
    lt_of_lt_of_le one_pos (LeanLab.ChenExplicit.one_le_oddFactor x)
  have hA : (∑' n, a x n) = K x / LeanLab.ChenExplicit.twinC := by
    rw [← tsum_a_mul_twinC hx, mul_div_assoc, div_self hT.ne', mul_one]
  have hK := totient_K_oddFactor he hx
  rw [hA, LeanLab.ChenDoubleSieve.CN, eq_div_iff (by positivity)]
  have e : (x.totient : ℝ) / x * (K x / LeanLab.ChenExplicit.twinC) *
      (2 * (LeanLab.ChenDoubleSieve.oddFactor x * LeanLab.ChenExplicit.twinC)) =
      2 * ((x.totient : ℝ) / x * K x * LeanLab.ChenDoubleSieve.oddFactor x) *
        (LeanLab.ChenExplicit.twinC / LeanLab.ChenExplicit.twinC) := by ring
  rw [e, hK, div_self hT.ne']; norm_num

/-! ### The asymptotic -/

/-- Chen's sum on the right of the inequality in (25), as in `chen25_lower`. -/
def T (x : ℕ) (z : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊z⌋₊, (if Squarefree q ∧ q.Coprime x then F q else 0) *
    (((q * x).totient : ℝ) * Real.log (z / q) / (q * x : ℕ))

lemma F_mul_totient (q : ℕ) (hq : 1 ≤ q) : F q * ((q.totient : ℝ) / q) = w q := by
  rw [totient_div_eq hq, F, w, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have e2 : (p : ℝ) - 1 ≠ 0 := by linarith
  have e3 : (p : ℝ) ≠ 0 := by linarith
  by_cases h : (p : ℝ) - 2 = 0
  · rw [h]; simp
  · field_simp

lemma T_eq {x : ℕ} (hx : 1 ≤ x) (z : ℝ) :
    T x z = (x.totient : ℝ) / x * ∑ q ∈ Icc 1 ⌊z⌋₊, a x q * Real.log (z / q) := by
  unfold T
  rw [mul_sum]
  refine sum_congr rfl fun q hq => ?_
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  unfold a
  split_ifs with hc
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    rw [Nat.totient_mul hc.2, ← F_mul_totient q hq1]
    push_cast
    field_simp
  · simp

/-- `B_x = ∑ a_x(q) log q ≤ B_1`, the uniform constant. -/
def Bc : ℝ := ∑' n, a 1 n * Real.log n

lemma Bc_nonneg : 0 ≤ Bc :=
  tsum_nonneg fun n => mul_nonneg (a_nonneg 1 n) (Real.log_natCast_nonneg n)

lemma tsum_alog_le (x : ℕ) : ∑' n, a x n * Real.log n ≤ Bc :=
  (summable_alog x).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (a_le_a_one x n) (Real.log_natCast_nonneg n))
    (summable_alog 1)

/-- The lower half: `∑_{q ≤ z} a_x(q) log(z/q) ≥ log z · ∑ a_x - ∑ a_x(q) log q`, any `z > 0`. -/
lemma sum_lower (x : ℕ) {z : ℝ} (hz : 0 < z) :
    (∑' n, a x n) * Real.log z - ∑' n, a x n * Real.log n ≤
      ∑ q ∈ Icc 1 ⌊z⌋₊, a x q * Real.log (z / q) := by
  set u : ℕ → ℝ := fun n => a x n * (Real.log n - Real.log z)
  have hu : Summable u := by
    have := (summable_alog x).sub ((summable_a x).mul_right (Real.log z))
    refine this.congr fun n => ?_
    simp only [u]; ring
  have htu : ∑' n, u n = ∑' n, a x n * Real.log n - (∑' n, a x n) * Real.log z := by
    rw [← tsum_mul_right, ← (summable_alog x).tsum_sub ((summable_a x).mul_right _)]
    congr 1; funext n; simp only [u]; ring
  have hle := hu.sum_le_tsum (Icc 1 ⌊z⌋₊) (fun n hn => by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [u, a_zero]
    · have hlt : ⌊z⌋₊ < n := by
        by_contra hc; exact hn (mem_Icc.mpr ⟨h, by omega⟩)
      have hzn : z < n := Nat.lt_of_floor_lt hlt
      have := Real.log_lt_log hz hzn
      exact mul_nonneg (a_nonneg x n) (by linarith))
  have hs : ∑ q ∈ Icc 1 ⌊z⌋₊, a x q * Real.log (z / q) = -∑ q ∈ Icc 1 ⌊z⌋₊, u q := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun q hq => ?_
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hq).1)
    rw [Real.log_div hz.ne' hq0]; simp only [u]; ring
  rw [hs]; linarith

/-- The upper half: `∑_{q ≤ z} a_x(q) log(z/q) ≤ log z · ∑ a_x`, for `z ≥ 1`. -/
lemma sum_upper (x : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    ∑ q ∈ Icc 1 ⌊z⌋₊, a x q * Real.log (z / q) ≤ (∑' n, a x n) * Real.log z := by
  have hlz : 0 ≤ Real.log z := Real.log_nonneg hz
  calc ∑ q ∈ Icc 1 ⌊z⌋₊, a x q * Real.log (z / q)
      ≤ ∑ q ∈ Icc 1 ⌊z⌋₊, a x q * Real.log z := by
        refine sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (a_nonneg x q)
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
        rw [Real.log_div (by linarith) hq0.ne']
        linarith [Real.log_natCast_nonneg q]
    _ = (∑ q ∈ Icc 1 ⌊z⌋₊, a x q) * Real.log z := by rw [sum_mul]
    _ ≤ (∑' n, a x n) * Real.log z :=
        mul_le_mul_of_nonneg_right ((summable_a x).sum_le_tsum _ (fun n _ => a_nonneg x n)) hlz

lemma totient_div_nonneg_le (x : ℕ) : 0 ≤ (x.totient : ℝ) / x ∧ (x.totient : ℝ) / x ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast Nat.totient_le x

/-- **Chen (25), the asymptotic, PROVED**: one absolute constant `B` with, for every even `x ≥ 2`
and real `z`: `T(x,z) ≥ log z/(2 C_x) - B` when `z > 0`, and `T(x,z) ≤ log z/(2 C_x)` when
`z ≥ 1`. -/
theorem chen25_main : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℕ, Even x → 0 < x →
    (∀ z : ℝ, 0 < z → Real.log z / (2 * LeanLab.ChenDoubleSieve.CN x) - B ≤ T x z) ∧
    (∀ z : ℝ, 1 ≤ z → T x z ≤ Real.log z / (2 * LeanLab.ChenDoubleSieve.CN x)) := by
  refine ⟨Bc, Bc_nonneg, fun x he hx => ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
  · have hm := totient_div_mul_tsum_a he hx.ne'
    obtain ⟨h0, h1⟩ := totient_div_nonneg_le x
    have hl := mul_le_mul_of_nonneg_left (sum_lower x hz) h0
    have hB := tsum_alog_le x
    have hBn : 0 ≤ ∑' n, a x n * Real.log n :=
      tsum_nonneg fun n => mul_nonneg (a_nonneg x n) (Real.log_natCast_nonneg n)
    rw [T_eq hx]
    have e : Real.log z / (2 * LeanLab.ChenDoubleSieve.CN x) =
        (x.totient : ℝ) / x * (∑' n, a x n) * Real.log z := by rw [hm]; ring
    rw [e]
    have : (x.totient : ℝ) / x * (∑' n, a x n * Real.log n) ≤ Bc :=
      (mul_le_of_le_one_left hBn h1).trans hB
    nlinarith
  · have hm := totient_div_mul_tsum_a he hx.ne'
    obtain ⟨h0, -⟩ := totient_div_nonneg_le x
    rw [T_eq hx]
    have e : Real.log z / (2 * LeanLab.ChenDoubleSieve.CN x) =
        (x.totient : ℝ) / x * ((∑' n, a x n) * Real.log z) := by rw [← mul_assoc, hm]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_upper x hz) h0

/-- Chen's `z = (x^{1/2-ε})^{1/2}`. -/
def zC (x : ℕ) (ε : ℝ) : ℝ := ((x : ℝ) ^ (1 / 2 - ε)) ^ (1 / 2 : ℝ)

lemma zC_pos {x : ℕ} (hx : 0 < x) (ε : ℝ) : 0 < zC x ε := by
  unfold zC; have : (0 : ℝ) < x := by exact_mod_cast hx
  positivity

lemma log_zC {x : ℕ} (hx : 0 < x) (ε : ℝ) :
    Real.log (zC x ε) = (1 / 4 - ε / 2) * Real.log x := by
  have h : (0 : ℝ) < x := by exact_mod_cast hx
  unfold zC
  rw [Real.log_rpow (Real.rpow_pos_of_pos h _), Real.log_rpow h]; ring

lemma one_le_zC {x : ℕ} (hx : 0 < x) {ε : ℝ} (hε : ε ≤ 1 / 2) : 1 ≤ zC x ε := by
  have h : (1 : ℝ) ≤ x := by exact_mod_cast hx
  unfold zC
  exact Real.one_le_rpow (Real.one_le_rpow h (by linarith)) (by norm_num)

lemma main_term {x : ℕ} (hx : 0 < x) (ε : ℝ) :
    Real.log (zC x ε) / (2 * LeanLab.ChenDoubleSieve.CN x) =
      (1 / 8 - ε / 4) * Real.log x / LeanLab.ChenDoubleSieve.CN x := by
  rw [log_zC hx]
  have hC : 0 < LeanLab.ChenDoubleSieve.CN x := by
    unfold LeanLab.ChenDoubleSieve.CN
    exact mul_pos (lt_of_lt_of_le one_pos (LeanLab.ChenExplicit.one_le_oddFactor x))
      LeanLab.ChenExplicit.twinC_pos
  field_simp
  ring

/-- **Chen 1973, display (25), the equality `... = (1/8 - ε/4)(log x)/C_x + O(1)`, PROVED**:
there is an absolute `B` with, for every even `x ≥ 2` and every `ε ≤ 1/2`,
`|∑_{q ≤ z, (q,x)=1} μ²(q)/(ψ(q)φ(q)) · φ(qx)/(qx) · log(z/q) - (1/8 - ε/4) log x / C_x| ≤ B`,
`z = (x^{1/2-ε})^{1/2}`. -/
theorem chen_display25 : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℕ, Even x → 0 < x → ∀ ε : ℝ, ε ≤ 1 / 2 →
    |T x (zC x ε) - (1 / 8 - ε / 4) * Real.log x / LeanLab.ChenDoubleSieve.CN x| ≤ B := by
  obtain ⟨B, hB, h⟩ := chen25_main
  refine ⟨B, hB, fun x he hx ε hε => ?_⟩
  have h1 := (h x he hx).1 (zC x ε) (zC_pos hx ε)
  have h2 := (h x he hx).2 (zC x ε) (one_le_zC hx hε)
  rw [main_term hx] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- **Chen 1973, display (25), whole, PROVED**: there is an absolute `B` with
`S ≥ (1/8 - ε/4) log x / C_x - B` for every even `x ≥ 2` and every real `ε`,
`S = ∑_{k ≤ z, (k,x)=1} μ²(k)/φ(k) ∏_{p∣k}(1 + 1/(p-2))`, `z = (x^{1/2-ε})^{1/2}`. -/
theorem chen_display25_S : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℕ, Even x → 0 < x → ∀ ε : ℝ,
    (1 / 8 - ε / 4) * Real.log x / LeanLab.ChenDoubleSieve.CN x - B ≤ S x (zC x ε) := by
  obtain ⟨B, hB, h⟩ := chen25_main
  refine ⟨B, hB, fun x he hx ε => ?_⟩
  have h1 := (h x he hx).1 (zC x ε) (zC_pos hx ε)
  rw [main_term hx] at h1
  exact h1.trans (chen25_lower x hx (zC x ε) (zC_pos hx ε).le)

/-- Vacuity check: the hypotheses hold at `x = 2`, `ε = 1/4`, and the main term
`(1/8 - ε/4)/C_x` is then positive, so the bound grows like `log x`. -/
theorem display25_instance :
    Even 2 ∧ 0 < 2 ∧ (1 / 4 : ℝ) ≤ 1 / 2 ∧
      0 < (1 / 8 - (1 / 4 : ℝ) / 4) / LeanLab.ChenDoubleSieve.CN 2 := by
  refine ⟨even_two, two_pos, by norm_num, div_pos (by norm_num) ?_⟩
  unfold LeanLab.ChenDoubleSieve.CN
  exact mul_pos (lt_of_lt_of_le one_pos (LeanLab.ChenExplicit.one_le_oddFactor 2))
    LeanLab.ChenExplicit.twinC_pos

end LeanLab.AlmostPrimeSums.Chen1973Display25
