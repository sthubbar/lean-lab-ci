/-
P0095 is done; this is P0066 Vaughan 1977, Lemma 10, p. 102, read on the page image.
Unit U-6849, CLOUD MANUAL-M1, 2026-10-21, track T1.

Lemma 10: A(x) > x/26 for 3.6·10^9 ≤ x ≤ 2.6·10^53. The proof: with p₁, ..., p₈ = 3, ..., 23,
A(x) ≥ Σ_{n≤x} (1 - Π(1 - a_i(n))) ≥ Σ_i Σ_n a_i(n) - Σ_{i<j} Σ_n a_i(n)a_j(n)
     ≥ s(π(x) - 13) - Σ_{i<j≤s} R(h(i,j), x),
then Lemma 8 for R and (2.14) for π give X₄, X₅, X₈ with the constants 73.95, 130.28,
409.15, and F(u; α, β) > 0 on 22 ≤ u ≤ 81, 34 ≤ u ≤ 95, 84 ≤ u ≤ 123 finishes.

This file PROVES Lemma 10 CONDITIONAL ON Lemma 8, stated as printed with the constant C of
(2.5) as a parameter, C ≤ 0.6602 by (2.10), and on (2.14), the lab's `RS33`. The count uses
π(⌊x⌋ - 23) - 1 in place of the paper's π(x) - 13; the loss is far inside the margin
(β - 16·0.6602·Σ) x / ((1 + log x) log x). The pair sums Σ_{i<j≤s} Π_{p | p_j - p_i, p > 2}
(p - 1)/(p - 2) are 7, 37/3, 581/15 exactly, kernel evaluated, and 16·0.6602 times them is
73.9424, 130.2795, 409.1479, below the printed 73.95, 130.28, 409.15: MATCH.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Sec6

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma10
open LeanLab.SchnirelmannConstant LeanLab.RieselVaughan1983 LeanLab.SchnirelmannBounds.Vaughan1977
  LeanLab.SchnirelmannBounds.Vaughan1977Sec6

/-- `p₁, ..., p₈ = 3, 5, 7, 11, 13, 17, 19, 23`, p. 102, indexed from 0. -/
def pr (i : ℕ) : ℕ := [3, 5, 7, 11, 13, 17, 19, 23].getD i 0

/-- The odd prime divisors of `h`. -/
def oddPF (h : ℕ) : Finset ℕ := (range (h + 1)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ h)

/-- `Π_{p | h, p > 2} (p - 1)/(p - 2)`. -/
def prodQ (h : ℕ) : ℚ := ∏ p ∈ oddPF h, ((p : ℚ) - 1) / ((p : ℚ) - 2)

/-- `Σ_{i<j≤s} Π_{p | h(i,j), p > 2} (p - 1)/(p - 2)`. -/
def pairSum (s : ℕ) : ℚ := ∑ j ∈ range s, ∑ i ∈ range j, prodQ (pr j - pr i)

theorem pairSum4 : pairSum 4 = 7 := by decide +kernel
theorem pairSum5 : pairSum 5 = 37 / 3 := by decide +kernel
theorem pairSum8 : pairSum 8 = 581 / 15 := by decide +kernel

theorem pr_facts : ∀ i < 8, (pr i).Prime ∧ 3 ≤ pr i ∧ pr i ≤ 23 := by decide +kernel

theorem pr_lt : ∀ j < 8, ∀ i < j, pr i < pr j := by decide +kernel

/-- `R(h, x)`, Lemma 8: the primes `p ≤ x` with `|h - p|` prime. -/
noncomputable def Rc (h : ℤ) (x : ℝ) : ℕ :=
  ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ Nat.Prime (h - (p : ℤ)).natAbs)).card

/-- `α(x)`, (3.8): 1 for `10^9 ≤ x < 10^44`, 1.6 for `x ≥ 10^44`. -/
noncomputable def alpha (x : ℝ) : ℝ := if x < 10 ^ 44 then 1 else 1.6

/-- Lemma 8, p. 101, as printed, with the constant `C` of (2.5) a parameter. -/
def Lemma8 (C : ℝ) : Prop :=
  ∀ x : ℝ, 10 ^ 9 ≤ x → ∀ h : ℤ, Even h → (h < 0 ∨ x < h) →
    (Rc h x : ℝ) < 16 * C * x / ((alpha x + Real.log x) * Real.log x) * (prodQ h.natAbs : ℝ)

/-- The even numbers `p + p_i`, `p` an odd prime, up to `n`. -/
def S (n i : ℕ) : Finset ℕ := (oddPrimes (n - pr i)).image (· + pr i)

/-- Bonferroni: `|⋃ S_i| ≥ Σ |S_i| - Σ_{i<j} |S_i ∩ S_j|`. -/
theorem bonferroni (T : ℕ → Finset ℕ) (s : ℕ) :
    (∑ i ∈ range s, (#(T i) : ℝ)) - ∑ j ∈ range s, ∑ i ∈ range j, (#(T i ∩ T j) : ℝ) ≤
      #((range s).biUnion T) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_add_one, Finset.biUnion_insert]
    have hu := Finset.card_union_add_card_inter (T s) ((range s).biUnion T)
    have hi : #(T s ∩ (range s).biUnion T) ≤ ∑ i ∈ range s, #(T i ∩ T s) := by
      rw [Finset.inter_biUnion]
      refine Finset.card_biUnion_le.trans (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro i _; rw [Finset.inter_comm]
    have hu' : (#(T s ∪ (range s).biUnion T) : ℝ) + #(T s ∩ (range s).biUnion T) =
        #(T s) + #((range s).biUnion T) := by exact_mod_cast hu
    have hi' : (#(T s ∩ (range s).biUnion T) : ℝ) ≤ ∑ i ∈ range s, (#(T i ∩ T s) : ℝ) := by
      exact_mod_cast hi
    linarith

/-- Each `S_i` lies in 𝒜 up to `n`. -/
theorem union_le (x : ℝ) (n : ℕ) (hn : ⌊x⌋₊ = n) (s : ℕ) (hs : s ≤ 8) :
    #((range s).biUnion (S n)) ≤ NCount x := by
  unfold NCount; rw [hn]
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_biUnion, Finset.mem_range, S, Finset.mem_image, oddPrimes,
    Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨i, hi, p, ⟨⟨hp3, hpn⟩, hpp⟩, rfl⟩ := hm
  obtain ⟨hpr, hpr3, _⟩ := pr_facts i (by omega)
  simp only [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by omega, by omega⟩, ?_, (AtMostPrimes.prime hpp).add (AtMostPrimes.prime hpr)⟩
  have ho1 : Odd p := hpp.odd_of_ne_two (by omega)
  have ho2 : Odd (pr i) := hpr.odd_of_ne_two (by omega)
  exact ho1.add_odd ho2

/-- `|S_i| ≥ #oddPrimes(n - 23)`. -/
theorem card_S (n i : ℕ) (hi : i < 8) : #(oddPrimes (n - 23)) ≤ #(S n i) := by
  unfold S
  rw [Finset.card_image_of_injective _ (add_left_injective _)]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨_, _, h23⟩ := pr_facts i hi
  simp only [oddPrimes, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩

/-- `|S_i ∩ S_j| ≤ R(p_i - p_j, x)` for `i < j`. -/
theorem inter_le (x : ℝ) (n : ℕ) (hn : ⌊x⌋₊ = n) (i j : ℕ) (hij : i < j) (hj : j < 8) :
    #(S n i ∩ S n j) ≤ Rc ((pr i : ℤ) - pr j) x := by
  unfold Rc; rw [hn]
  have hlt := pr_lt j hj i hij
  obtain ⟨_, _, _⟩ := pr_facts j hj
  refine Finset.card_le_card_of_injOn (fun m => m - pr j) ?_ ?_
  · intro m hm
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hm
    obtain ⟨h1, h2⟩ := hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp h2
    simp only [oddPrimes, Finset.mem_filter, Finset.mem_Icc] at hp hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    have hq' : p + pr i - pr j = q := by omega
    simp only
    rw [hq']
    refine ⟨⟨by omega, by omega⟩, hq.2, ?_⟩
    have : ((pr i : ℤ) - pr j - (q : ℤ)).natAbs = p := by omega
    rw [this]; exact hp.2
  · intro a ha b hb hab
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at ha hb
    obtain ⟨qa, _, rfl⟩ := Finset.mem_image.mp ha.2
    obtain ⟨qb, _, rfl⟩ := Finset.mem_image.mp hb.2
    simp only at hab
    omega

/-- The count of p. 102: `A(x) ≥ s(#oddPrimes(n - 23)) - Σ_{i<j<s} R(p_i - p_j, x)`. -/
theorem count (x : ℝ) (n : ℕ) (hn : ⌊x⌋₊ = n) (s : ℕ) (hs : s ≤ 8) :
    (s : ℝ) * #(oddPrimes (n - 23)) - ∑ j ∈ range s, ∑ i ∈ range j, (Rc ((pr i : ℤ) - pr j) x : ℝ) ≤
      NCount x := by
  have hb := bonferroni (S n) s
  have hu : (#((range s).biUnion (S n)) : ℝ) ≤ NCount x := by exact_mod_cast union_le x n hn s hs
  have h1 : (s : ℝ) * #(oddPrimes (n - 23)) ≤ ∑ i ∈ range s, (#(S n i) : ℝ) := by
    have := Finset.sum_le_sum (fun i (hi : i ∈ range s) =>
      (show (#(oddPrimes (n - 23)) : ℝ) ≤ #(S n i) by
        exact_mod_cast card_S n i (by simp at hi; omega)))
    simpa using this
  have h2 : ∑ j ∈ range s, ∑ i ∈ range j, (#(S n i ∩ S n j) : ℝ) ≤
      ∑ j ∈ range s, ∑ i ∈ range j, (Rc ((pr i : ℤ) - pr j) x : ℝ) := by
    apply Finset.sum_le_sum; intro j hj; apply Finset.sum_le_sum; intro i hi
    simp only [Finset.mem_range] at hi hj
    exact_mod_cast inter_le x n hn i j hi (by omega)
  linarith

/-- Lemma 8 on the pairs: `R(p_i - p_j, x) < 16·0.6602·x/((1 + log x) log x) Π`. -/
theorem R_le {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 0.6602) (h8 : Lemma8 C) (x : ℝ) (hx : 10 ^ 9 ≤ x)
    (i j : ℕ) (hij : i < j) (hj : j < 8) :
    (Rc ((pr i : ℤ) - pr j) x : ℝ) ≤
      16 * 0.6602 * x / ((1 + Real.log x) * Real.log x) * (prodQ (pr j - pr i) : ℝ) := by
  have hlt := pr_lt j hj i hij
  obtain ⟨hpi, hpi3, _⟩ := pr_facts i (by omega)
  obtain ⟨hpj, hpj3, _⟩ := pr_facts j hj
  have hev : Even ((pr i : ℤ) - pr j) := by
    have h1 : Odd (pr i : ℤ) := by exact_mod_cast hpi.odd_of_ne_two (by omega)
    have h2 : Odd (pr j : ℤ) := by exact_mod_cast hpj.odd_of_ne_two (by omega)
    exact h1.sub_odd h2
  have hneg : ((pr i : ℤ) - pr j) < 0 := by omega
  have h := h8 x hx _ hev (Or.inl hneg)
  have hna : ((pr i : ℤ) - pr j).natAbs = pr j - pr i := by omega
  rw [hna] at h
  have hL : 20 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have : Real.exp 20 < 10 ^ 9 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 20 < 2.7182818286 ^ 20 := by gcongr
        _ < 10 ^ 9 := by norm_num
    linarith
  have hal : 1 ≤ alpha x := by unfold alpha; split_ifs <;> norm_num
  have hP : (0 : ℝ) ≤ prodQ (pr j - pr i) := by
    unfold prodQ; push_cast
    apply Finset.prod_nonneg; intro p hp
    simp only [oddPF, Finset.mem_filter] at hp
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp.2.2.1
    apply div_nonneg <;> linarith
  have hx0 : 0 < x := by linarith
  have hden : (1 + Real.log x) * Real.log x ≤ (alpha x + Real.log x) * Real.log x := by
    apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hd1 : 0 < (1 + Real.log x) * Real.log x := by positivity
  have e1 : 16 * C * x / ((alpha x + Real.log x) * Real.log x) ≤
      16 * 0.6602 * x / ((1 + Real.log x) * Real.log x) := by
    apply div_le_div₀ (by positivity) (by nlinarith) hd1 hden
  have := mul_le_mul_of_nonneg_right e1 hP
  linarith

/-- The algebraic identity behind `F(u; s, β)`: with `a = 1/(L - 1/2)` and `b = 1/((1+L)L)`,
`s a - β b - 1/26 = F(L) a b`. -/
theorem key_id (s β L a b : ℝ) (ha1 : a * (L - 1 / 2) = 1) (hb1 : b * ((1 + L) * L) = 1) :
    s * a - β * b - 1 / 26 =
      (s * (L + L ^ 2) - β * (L - 1 / 2) - (L ^ 3 + L ^ 2 / 2 - L / 2) / 26) * a * b := by
  linear_combination (-(s * a) + 1 / 26) * hb1 + (β * b + (1 / 26) * b * ((1 + L) * L)) * ha1

/-- The final inequality, from the cubic `F(u; s, β) > 0` and the slack in the constants. -/
theorem final_ineq {s β β0 x L : ℝ} (hs : 0 ≤ s) (hs8 : s ≤ 8) (hx : 3.6 * 10 ^ 9 ≤ x)
    (hL1 : 22 ≤ L) (hL2 : L ≤ 123)
    (hF : 0 < s * (L + L ^ 2) - β * (L - 1 / 2) - (L ^ 3 + L ^ 2 / 2 - L / 2) / 26)
    (hgap : 300000 ≤ (β - β0) * (3.6 * 10 ^ 9)) (hβ0 : β0 ≤ β) :
    x / 26 < s * ((x - 24) / (L - 1 / 2) - 1) - β0 * x / ((1 + L) * L) := by
  have hL0 : 0 < L - 1 / 2 := by linarith
  have hD0 : 0 < (1 + L) * L := by positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (L - 1 / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 / ((1 + L) * L) := ⟨_, rfl⟩
  have ha1 : a * (L - 1 / 2) = 1 := by rw [ha]; exact one_div_mul_cancel hL0.ne'
  have hb1 : b * ((1 + L) * L) = 1 := by rw [hb]; exact one_div_mul_cancel hD0.ne'
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have e1 : (x - 24) / (L - 1 / 2) = (x - 24) * a := by rw [ha]; ring
  have e2 : β0 * x / ((1 + L) * L) = β0 * x * b := by rw [hb]; ring
  rw [e1, e2]
  set Fv := s * (L + L ^ 2) - β * (L - 1 / 2) - (L ^ 3 + L ^ 2 / 2 - L / 2) / 26 with hFv
  have key : s * a - β * b - 1 / 26 = Fv * a * b := key_id s β L a b ha1 hb1
  have hab : a ≤ 1 / 21.5 := by
    rw [ha]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hDle : (1 + L) * L ≤ 15252 := by nlinarith
  have hslack : 24 * s * a + s ≤ (β - β0) * x * b := by
    have h1 : (24 * s * a + s) * ((1 + L) * L) ≤ 268435 := by
      have : 24 * s * a + s ≤ 17.6 := by nlinarith
      have h0 : 0 ≤ 24 * s * a + s := by positivity
      nlinarith
    have h2 : 300000 ≤ (β - β0) * x := by nlinarith
    have h3 : (24 * s * a + s) * ((1 + L) * L) ≤ (β - β0) * x := by linarith
    have e3 : (24 * s * a + s) = ((24 * s * a + s) * ((1 + L) * L)) * b := by
      rw [mul_assoc (24 * s * a + s), mul_comm ((1 + L) * L) b, hb1, mul_one]
    rw [e3]
    exact mul_le_mul_of_nonneg_right h3 hb0.le
  have hxpos : 0 < x := by linarith
  have hFab : 0 < Fv * a * b := by positivity
  have hmain : 0 < x * (s * a - β * b - 1 / 26) := by rw [key]; positivity
  nlinarith

/-- `e^22 < 3.6·10^9` and `2.6·10^53 < e^123`. -/
theorem exp_range : Real.exp 22 < 3.6 * 10 ^ 9 ∧ 2.6 * 10 ^ 53 < Real.exp 123 := by
  have hl := Real.exp_one_gt_d9
  have hu := Real.exp_one_lt_d9
  have e22 : Real.exp 22 = Real.exp 1 ^ 22 := by rw [← Real.exp_nat_mul]; norm_num
  have e123 : Real.exp 123 = Real.exp 1 ^ 123 := by rw [← Real.exp_nat_mul]; norm_num
  constructor
  · rw [e22]
    calc Real.exp 1 ^ 22 < 2.7182818286 ^ 22 := by gcongr
      _ < 3.6 * 10 ^ 9 := by norm_num
  · rw [e123]
    calc (2.6 : ℝ) * 10 ^ 53 < 2.7182818283 ^ 123 := by norm_num
      _ < Real.exp 1 ^ 123 := by gcongr

/-- **Lemma 10, CONDITIONAL ON Lemma 8 with C ≤ 0.6602 and on (2.14)**. Generic in `C`: `Lemma8 C`
is false for small `C`, so cite the paper's Lemma 8 only through `Vaughan1977Twin.lemma10_of_twin`,
where `C` is the paper's own constant. -/
theorem lemma10_of {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 0.6602) (h8 : Lemma8 C) (hRS : RS33) :
    Lemma10 := by
  intro x hx1 hx2
  unfold A
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  set L := Real.log x with hLdef
  obtain ⟨e22, e123⟩ := exp_range
  have hL1 : 22 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]; linarith
  have hL2 : L ≤ 123 := by
    rw [hLdef, Real.log_le_iff_le_exp (by linarith)]; linarith
  have hn90 : (90 : ℝ) ≤ n := by linarith
  have hn90' : 90 ≤ n := by exact_mod_cast hn90
  -- π(n - 23) > (x - 24)/(L - 1/2)
  have hrs := hRS (n - 23) (by omega)
  have hm : ((n - 23 : ℕ) : ℝ) = (n : ℝ) - 23 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hm] at hrs
  have hpi := primeCounting_eq_oddPrimes (n - 23) (by omega)
  have hlog : Real.log ((n : ℝ) - 23) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hlog1 : 1 < Real.log ((n : ℝ) - 23) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hodd : (x - 24) / (L - 1 / 2) - 1 ≤ (#(oddPrimes (n - 23)) : ℝ) := by
    have h1 : (x - 24) / (L - 1 / 2) ≤ ((n : ℝ) - 23) / (Real.log ((n : ℝ) - 23) - 1 / 2) := by
      apply div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : (Nat.primeCounting (n - 23) : ℝ) = #(oddPrimes (n - 23)) + 1 := by
      exact_mod_cast hpi
    linarith
  -- the three ranges
  have hx9 : (10 : ℝ) ^ 9 ≤ x := by linarith
  have hcnt : ∀ s : ℕ, s ≤ 8 → ∀ β0 : ℝ, (16 * 0.6602 * (pairSum s : ℝ)) ≤ β0 →
      (s : ℝ) * ((x - 24) / (L - 1 / 2) - 1) - β0 * x / ((1 + L) * L) ≤ NCount x := by
    intro s hs β0 hβ0
    have hc := count x n hn.symm s hs
    have hR : ∑ j ∈ range s, ∑ i ∈ range j, (Rc ((pr i : ℤ) - pr j) x : ℝ) ≤
        16 * 0.6602 * x / ((1 + L) * L) * (pairSum s : ℝ) := by
      unfold pairSum; push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i hi
      simp only [Finset.mem_range] at hi hj
      exact R_le hC0 hC h8 x hx9 i j hi (by omega)
    have hD : 0 < (1 + L) * L := by positivity
    have hP : 16 * 0.6602 * x / ((1 + L) * L) * (pairSum s : ℝ) ≤ β0 * x / ((1 + L) * L) := by
      rw [div_mul_eq_mul_div, mul_comm (16 * 0.6602 * x), mul_assoc, ← mul_assoc (pairSum s : ℝ)]
      apply div_le_div_of_nonneg_right _ hD.le
      nlinarith
    have hsx : (s : ℝ) * ((x - 24) / (L - 1 / 2) - 1) ≤ (s : ℝ) * #(oddPrimes (n - 23)) :=
      mul_le_mul_of_nonneg_left hodd (Nat.cast_nonneg _)
    linarith
  rcases le_or_gt L 81 with h81 | h81
  · have := hcnt 4 (by norm_num) 73.9424 (by rw [pairSum4]; norm_num)
    have hF : 0 < (4 : ℝ) * (L + L ^ 2) - 73.95 * (L - 1 / 2) - (L ^ 3 + L ^ 2 / 2 - L / 2) / 26 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (sub_nonneg.mpr h81),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hL1) (sub_nonneg.mpr h81)) (sub_nonneg.mpr hL1),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hL1) (sub_nonneg.mpr h81)) (sub_nonneg.mpr h81)]
    have := final_ineq (s := 4) (β := 73.95) (β0 := 73.9424) (by norm_num) (by norm_num) hx1
      hL1 hL2 hF (by norm_num) (by norm_num)
    push_cast at *
    linarith
  rcases le_or_gt L 95 with h95 | h95
  · have := hcnt 5 (by norm_num) 130.27947 (by rw [pairSum5]; norm_num)
    have h34 : 34 ≤ L := by linarith
    have hF : 0 < (5 : ℝ) * (L + L ^ 2) - 130.28 * (L - 1 / 2) - (L ^ 3 + L ^ 2 / 2 - L / 2) / 26 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h34) (sub_nonneg.mpr h95),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h34) (sub_nonneg.mpr h95)) (sub_nonneg.mpr h34),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h34) (sub_nonneg.mpr h95)) (sub_nonneg.mpr h95)]
    have := final_ineq (s := 5) (β := 130.28) (β0 := 130.27947) (by norm_num) (by norm_num) hx1
      hL1 hL2 hF (by norm_num) (by norm_num)
    push_cast at *
    linarith
  · have := hcnt 8 (by norm_num) 409.14795 (by rw [pairSum8]; norm_num)
    have h84 : 84 ≤ L := by linarith
    have hF : 0 < (8 : ℝ) * (L + L ^ 2) - 409.15 * (L - 1 / 2) - (L ^ 3 + L ^ 2 / 2 - L / 2) / 26 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h84) (sub_nonneg.mpr hL2),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h84) (sub_nonneg.mpr hL2)) (sub_nonneg.mpr h84),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr h84) (sub_nonneg.mpr hL2)) (sub_nonneg.mpr hL2)]
    have := final_ineq (s := 8) (β := 409.15) (β0 := 409.14795) (by norm_num) (by norm_num) hx1
      hL1 hL2 hF (by norm_num) (by norm_num)
    push_cast at *
    linarith

/-- The Theorem, CONDITIONAL ON (2.14), Lemma 8 with C ≤ 0.6602, and Lemma 12. -/
theorem statement27_of_RS_L8 {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ 0.6602) (hRS : RS33)
    (h8 : Lemma8 C) (h12 : Lemma12) : Statement27 :=
  statement27_of_RS hRS (lemma10_of hC0 hC h8 hRS) h12

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma10

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.pairSum4
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.pairSum5
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.pairSum8
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.pr_facts
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.pr_lt
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.bonferroni
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.union_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.card_S
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.inter_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.count
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.R_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.key_id
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.final_ineq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.exp_range
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.lemma10_of
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma10.statement27_of_RS_L8
