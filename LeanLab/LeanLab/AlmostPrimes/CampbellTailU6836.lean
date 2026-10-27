/-
AI-written Lean code, Claude, 2026-10-21, session 20261021T0316Z-cloud57, unit U-6836.
P0020 P. J. Campbell 2026, arXiv 2608.09488 v1, Case 2 of Theorem 1.2, rows 209 to 227 of the
Case 2 table, `z` from 1013527 to `10^8`. Infrastructure for the prime count route.

Above about `10^6` the kernel coverage walk `cov` of CampbellCase2TableU6820 is too slow, so the
products over the primes of a tail `[Y, V)` are bounded through an upper bound on the prime
counts at the points of a grid `Y = x 0 ≤ x 1 ≤ ... ≤ x n = V`, by summation by parts:
if `φ p ≤ Φ i` on the primes of `[x i, x (i+1))` and `Φ` decreases, then
`Σ_{Y ≤ p < V} φ p ≤ Φ n · U n + Σ_{i<n} U (i+1) · (Φ i - Φ (i+1))`
for any `U i ≥ #{Y ≤ p < x i}`. Only upper bounds on the counts are needed, so the cited
input can be an upper bound on `π`, the lab's `DusartPi11`, and a lower bound on `π (Y - 1)`.

PROVED, no cited input: `abel_eq`, `abel_le`, `card_primes_Ico`, `sum_blocks`, `tail_sum_le`;
`prime_of_isP`, the converse of `isP_of_prime`; `length_le_primeCounting'`, a lower bound for
`π' Y` from a kernel checked list, `length_le_card_primesIco` and `addK` for checked blocks;
`log_ratio_ge`; `exp_neg_ge_pow`, `exp_le_inv_pow`;
`pi'_le_of_dusart` CONDITIONAL ON `DusartPi11Body`, the body of the lab's cited `Thm5.DusartPi11`;
`PE_tail`, `P5_tail` and `good_of_tail`: from `Good a b Y m e` and upper bounds `Qm`, `Qe` on
`Σ_{Y ≤ p < V} 2/(p-2)` and `Σ_{Y ≤ p < V} 8/p^{a/b}`, any `m' ≤ m e^{-Qm}` and `e' ≥ e e^{Qe}`
give `Good a b V m' e'`.
KNOWN mathematics, Abel summation. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.CampbellCase2TableU6820

open Finset

namespace LeanLab.AlmostPrimes.CampbellTailU6836
open LeanLab.AlmostPrimes CampbellCase2 CampbellCase2TableU6820

/-- **Summation by parts, exact form, PROVED.** -/
theorem abel_eq (Φ c : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i ∈ range n, Φ i * c i =
      Φ n * ∑ j ∈ range n, c j + ∑ i ∈ range n, (∑ j ∈ range (i + 1), c j) * (Φ i - Φ (i + 1))
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, abel_eq Φ c n,
      sum_range_succ (fun i => (∑ j ∈ range (i + 1), c j) * (Φ i - Φ (i + 1))) n,
      sum_range_succ c n]
    ring

/-- **Summation by parts with upper bounds on the partial sums, PROVED.** -/
theorem abel_le (Φ c U : ℕ → ℝ) (n : ℕ) (hΦ : ∀ i < n, Φ (i + 1) ≤ Φ i) (hΦn : 0 ≤ Φ n)
    (hU : ∀ i ≤ n, ∑ j ∈ range i, c j ≤ U i) :
    ∑ i ∈ range n, Φ i * c i ≤ Φ n * U n + ∑ i ∈ range n, U (i + 1) * (Φ i - Φ (i + 1)) := by
  rw [abel_eq]
  refine add_le_add (mul_le_mul_of_nonneg_left (hU n le_rfl) hΦn) (sum_le_sum fun i hi => ?_)
  have hi' := mem_range.mp hi
  exact mul_le_mul_of_nonneg_right (hU (i + 1) (by omega)) (sub_nonneg.mpr (hΦ i hi'))

/-- The primes of `[a, b)`. -/
def primesIco (a b : ℕ) : Finset ℕ := (Ico a b).filter Nat.Prime

/-- **`#primes in [a, b) = π' b - π' a`, PROVED.** -/
theorem card_primes_Ico {a b : ℕ} (h : a ≤ b) :
    (primesIco a b).card + Nat.primeCounting' a = Nat.primeCounting' b := by
  simp only [Nat.primeCounting', Nat.count_eq_card_filter_range, primesIco]
  rw [← card_union_of_disjoint]
  · congr 1
    rw [← filter_union, range_eq_Ico, range_eq_Ico, union_comm,
      Ico_union_Ico_eq_Ico (Nat.zero_le a) h]
  · refine disjoint_filter_filter ?_
    rw [range_eq_Ico]
    exact (Ico_disjoint_Ico_consecutive 0 a b).symm

lemma chain_le (x : ℕ → ℕ) (n : ℕ) (hx : ∀ i < n, x i ≤ x (i + 1)) : ∀ i ≤ n, x 0 ≤ x i
  | 0, _ => le_rfl
  | i + 1, h => (chain_le x n hx i (by omega)).trans (hx i (by omega))

/-- **The primes of `[x 0, x n)` split along a nondecreasing grid, PROVED.** -/
theorem sum_blocks (x : ℕ → ℕ) (φ : ℕ → ℝ) : ∀ n : ℕ, (∀ i < n, x i ≤ x (i + 1)) →
    ∑ p ∈ primesIco (x 0) (x n), φ p = ∑ i ∈ range n, ∑ p ∈ primesIco (x i) (x (i + 1)), φ p
  | 0, _ => by simp [primesIco]
  | n + 1, hx => by
    rw [sum_range_succ, ← sum_blocks x φ n (fun i hi => hx i (by omega)), ← sum_union]
    · congr 1
      simp only [primesIco]
      rw [← filter_union, Ico_union_Ico_eq_Ico (chain_le x (n + 1) hx n (by omega))
        (hx n (by omega))]
    · simp only [primesIco]
      exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)

/-- **Tail bound by a grid and upper bounds on prime counts, PROVED.**
If `φ p ≤ Φ i` for the primes of `[x i, x (i+1))`, `Φ` decreases on `0..n`, `Φ n ≥ 0` and
`π' (x i) - π' (x 0) ≤ U i`, then the sum of `φ` over the primes of `[x 0, x n)` is at most
`Φ n · U n + Σ_{i<n} U (i+1) · (Φ i - Φ (i+1))`. -/
theorem tail_sum_le (x : ℕ → ℕ) (φ Φ U : ℕ → ℝ) (n : ℕ) (hx : ∀ i < n, x i ≤ x (i + 1))
    (hφ : ∀ i < n, ∀ p, x i ≤ p → p < x (i + 1) → p.Prime → φ p ≤ Φ i)
    (hΦ : ∀ i < n, Φ (i + 1) ≤ Φ i) (hΦn : 0 ≤ Φ n)
    (hU : ∀ i ≤ n, (Nat.primeCounting' (x i) : ℝ) - Nat.primeCounting' (x 0) ≤ U i) :
    ∑ p ∈ primesIco (x 0) (x n), φ p ≤
      Φ n * U n + ∑ i ∈ range n, U (i + 1) * (Φ i - Φ (i + 1)) := by
  set c : ℕ → ℝ := fun i => ((primesIco (x i) (x (i + 1))).card : ℝ)
  have h1 : ∑ p ∈ primesIco (x 0) (x n), φ p ≤ ∑ i ∈ range n, Φ i * c i := by
    rw [sum_blocks x φ n hx]
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.mp hi
    have := sum_le_card_nsmul (primesIco (x i) (x (i + 1))) φ (Φ i) (fun p hp => by
      simp only [primesIco, mem_filter, mem_Ico] at hp
      exact hφ i hi' p hp.1.1 hp.1.2 hp.2)
    simpa [c, nsmul_eq_mul, mul_comm] using this
  refine h1.trans (abel_le Φ c U n hΦ hΦn fun i hi => ?_)
  have hsum : ∑ j ∈ range i, c j = ((primesIco (x 0) (x i)).card : ℝ) := by
    have e := sum_blocks x (fun _ => (1 : ℝ)) i (fun j hj => hx j (by omega))
    simp only [sum_const, nsmul_eq_mul, mul_one] at e
    rw [e]
  rw [hsum]
  have := card_primes_Ico (chain_le x n hx i hi)
  have h' : ((primesIco (x 0) (x i)).card : ℝ) =
      (Nat.primeCounting' (x i) : ℝ) - Nat.primeCounting' (x 0) := by
    rw [← this]; push_cast; ring
  rw [h']
  exact hU i hi

/-! ### Primality from trial division, and a lower bound for `π'` from a list -/

lemma tdiv_false_no_div (n : ℕ) : ∀ f d, CampbellCase2Table.tdiv n f d = false →
    ∀ k, d ≤ k → k * k ≤ n → k < d + f → ¬ k ∣ n := by
  intro f
  induction f with
  | zero => intro d _ k h1 _ h3; omega
  | succ f ih =>
    intro d h k hk hkk hkf
    simp only [CampbellCase2Table.tdiv] at h
    split_ifs at h with h1 h2
    · exact absurd (lt_of_lt_of_le h1 (le_trans (Nat.mul_le_mul hk hk) hkk)) (lt_irrefl _)
    · rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
      · exact ih (d + 1) h k hlt hkk (by omega)

/-- **Trial division certifies primality, PROVED**: the converse of `isP_of_prime`. -/
theorem prime_of_isP {n : ℕ} (h : CampbellCase2Table.isP n = true) : n.Prime := by
  simp only [CampbellCase2Table.isP, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  by_contra hp
  have h0 : 0 < n := by omega
  have hsq := Nat.minFac_sq_le_self h0 hp
  have hm2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hle := Nat.minFac_le h0
  exact tdiv_false_no_div n n 2 h.2 n.minFac hm2 (by rw [← pow_two]; exact hsq) (by omega)
    (Nat.minFac_dvd n)

/-- Kernel check: a strictly increasing list of trial division primes below `Y`. -/
def incrBelow (Y : ℕ) : List ℕ → Bool
  | [] => true
  | [a] => CampbellCase2Table.isP a && decide (a < Y)
  | a :: b :: t => CampbellCase2Table.isP a && decide (a < b) && incrBelow Y (b :: t)

lemma incrBelow_spec (Y : ℕ) : ∀ l : List ℕ, incrBelow Y l = true →
    (∀ x ∈ l, x.Prime ∧ x < Y) ∧ l.Pairwise (· < ·)
  | [] => fun _ => by simp
  | [a] => fun h => by
    simp only [incrBelow, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [prime_of_isP h.1, h.2]
  | a :: b :: t => fun h => by
    simp only [incrBelow, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hab⟩, hr⟩ := h
    obtain ⟨h1, h2⟩ := incrBelow_spec Y (b :: t) hr
    have hbY := (h1 b (by simp)).2
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨prime_of_isP ha, by omega⟩
      · exact h1 x hx
    · refine List.pairwise_cons.mpr ⟨fun x hx => ?_, h2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact lt_trans hab ((List.pairwise_cons.mp h2).1 x hx)

/-- **A lower bound for `π' Y` from a kernel checked list, PROVED.** -/
theorem length_le_primeCounting' {Y : ℕ} {l : List ℕ} (h : incrBelow Y l = true) :
    l.length ≤ Nat.primeCounting' Y := by
  obtain ⟨h1, h2⟩ := incrBelow_spec Y l h
  have hnd : l.Nodup := h2.imp (fun hab => ne_of_lt hab)
  rw [← List.toFinset_card_of_nodup hnd, Nat.primeCounting', Nat.count_eq_card_filter_range]
  refine card_le_card fun x hx => ?_
  rw [List.mem_toFinset] at hx
  simp only [mem_filter, mem_range]
  exact ⟨(h1 x hx).2, (h1 x hx).1⟩

/-- Kernel check: a strictly increasing list of trial division primes in `[A, B)`. -/
def incrIn (A B : ℕ) (l : List ℕ) : Bool := incrBelow B l && l.all (fun p => decide (A ≤ p))

/-- **A lower bound for the primes of `[A, B)` from a kernel checked list, PROVED.** -/
theorem length_le_card_primesIco {A B : ℕ} {l : List ℕ} (h : incrIn A B l = true) :
    l.length ≤ (primesIco A B).card := by
  simp only [incrIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := incrBelow_spec B l h.1
  have hnd : l.Nodup := h2.imp (fun hab => ne_of_lt hab)
  rw [← List.toFinset_card_of_nodup hnd]
  refine card_le_card fun x hx => ?_
  rw [List.mem_toFinset] at hx
  simp only [primesIco, mem_filter, mem_Ico]
  exact ⟨⟨h.2 x hx, (h1 x hx).2⟩, (h1 x hx).1⟩

/-- **Adding one checked block to a lower bound for `π'`, PROVED.** -/
theorem addK {K1 K2 a b : ℕ} {l : List ℕ} (hab : a ≤ b) (h1 : K1 ≤ Nat.primeCounting' a)
    (h2 : incrIn a b l = true) (hl : l.length = K2) : K1 + K2 ≤ Nat.primeCounting' b := by
  have := card_primes_Ico hab
  have := length_le_card_primesIco h2
  omega

/-! ### Logarithm steps -/

/-- **`log B - log A ≥ 2 (B - A)/(B + A)` for `0 < A < B`, PROVED**, the first term of the
series `log(1 + 1/a) = Σ 2/(2k+1) (2a+1)^{-(2k+1)}`. -/
theorem log_ratio_ge {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    2 * (B - A) / (B + A) ≤ Real.log B - Real.log A := by
  have hBA : 0 < B - A := by linarith
  set a := A / (B - A) with ha
  have ha0 : 0 < a := div_pos hA hBA
  have hs := Real.hasSum_log_one_add_inv ha0
  have h0 := le_hasSum hs 0 (fun j _ => by positivity)
  have e1 : 1 + a⁻¹ = B / A := by
    rw [ha, inv_div]; field_simp; ring
  have e2 : 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * 0 + 1) =
      2 * (B - A) / (B + A) := by
    rw [ha]; field_simp; ring
  rw [e1, Real.log_div (by linarith) hA.ne', e2] at h0
  exact h0

/-! ### Count bound from Dusart, and exponential bounds by powers -/

/-- The body of the lab's cited `Thm5.DusartPi11`, BJSThm5At3273.lean: Dusart 2010,
`π(x) ≤ x/(ln x - 1.1)` for `x ≥ 60184`. Stated here as a hypothesis shape only, so this file
does not import the BJS chain; `Thm5.DusartPi11` unfolds to it. -/
def DusartPi11Body : Prop :=
  ∀ x : ℝ, 60184 ≤ x → ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤ x / (Real.log x - 1.1)

/-- **`π' x ≤ x/(λ - 1.1)` for `λ ≤ log x`, CONDITIONAL ON `DusartPi11Body`.** -/
theorem pi'_le_of_dusart (hP : DusartPi11Body) {x : ℕ} (hx : 60184 ≤ x) {lam : ℝ}
    (hl : lam ≤ Real.log x) (h11 : 1.1 < lam) :
    (Nat.primeCounting' x : ℝ) ≤ x / (lam - 1.1) := by
  have h1 : Nat.primeCounting' x ≤ Nat.primeCounting x := by
    rw [Nat.primeCounting]; exact Nat.monotone_primeCounting' (Nat.le_succ x)
  have h2 := hP (x : ℝ) (by exact_mod_cast hx)
  rw [Nat.floor_natCast] at h2
  calc (Nat.primeCounting' x : ℝ) ≤ Nat.primeCounting x := by exact_mod_cast h1
    _ ≤ x / (Real.log x - 1.1) := h2
    _ ≤ x / (lam - 1.1) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg x) (by linarith) (by linarith)

/-- **`e^{-q} ≥ (1 - q/N)^N` for `0 ≤ q ≤ N`, PROVED.** -/
theorem exp_neg_ge_pow {q : ℝ} {N : ℕ} (hN : 0 < N) (_hq : 0 ≤ q) (hqN : q ≤ N) :
    (1 - q / N) ^ N ≤ Real.exp (-q) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 ≤ 1 - q / N := by rw [sub_nonneg, div_le_one hN']; exact hqN
  have h1 : 1 - q / N ≤ Real.exp (-(q / N)) := by linarith [Real.add_one_le_exp (-(q / N))]
  calc (1 - q / N) ^ N ≤ Real.exp (-(q / N)) ^ N := pow_le_pow_left₀ h0 h1 N
    _ = Real.exp (-q) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

/-- **`e^q ≤ (1 - q/N)^{-N}` for `0 ≤ q < N`, PROVED.** -/
theorem exp_le_inv_pow {q : ℝ} {N : ℕ} (hN : 0 < N) (hq : 0 ≤ q) (hqN : q < N) :
    Real.exp q ≤ ((1 - q / N) ^ N)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 < 1 - q / N := by rw [sub_pos, div_lt_one hN']; exact hqN
  have h1 := exp_neg_ge_pow hN hq hqN.le
  rw [Real.exp_neg] at h1
  have hp : 0 < (1 - q / N) ^ N := pow_pos h0 N
  rw [le_inv_comm₀ (Real.exp_pos q) hp]
  exact h1

/-! ### The tail certificate -/

/-- **Lower bounds for `log` along a grid, PROVED**: `λ 0/S ≤ log (x 0)` and
`λ (i+1) (x (i+1) + x i) ≤ λ i (x (i+1) + x i) + 2 S (x (i+1) - x i)` give `λ i/S ≤ log (x i)`. -/
theorem lam_le_log (x lam : ℕ → ℕ) (n S : ℕ) (hS : 0 < S) (hx0 : 0 < x 0)
    (hx : ∀ i < n, x i < x (i + 1))
    (hl : ∀ i < n, lam (i + 1) * (x (i + 1) + x i) ≤ lam i * (x (i + 1) + x i) + 2 * S * (x (i + 1) - x i))
    (h0 : (lam 0 : ℝ) / S ≤ Real.log (x 0)) : ∀ i ≤ n, (lam i : ℝ) / S ≤ Real.log (x i)
  | 0, _ => h0
  | i + 1, hi => by
    have ih := lam_le_log x lam n S hS hx0 hx hl h0 i (by omega)
    have hxi := hx i (by omega)
    have hpos : 0 < x i := lt_of_lt_of_le hx0
      (chain_le x n (fun j hj => (hx j hj).le) i (by omega))
    have hA : (0 : ℝ) < x i := by exact_mod_cast hpos
    have hAB : (x i : ℝ) < x (i + 1) := by exact_mod_cast hxi
    have hlog := log_ratio_ge hA hAB
    have hint := hl i (by omega)
    have hreal : ((lam (i + 1) : ℝ)) * ((x (i + 1) : ℝ) + x i) ≤
        (lam i : ℝ) * ((x (i + 1) : ℝ) + x i) + 2 * S * ((x (i + 1) : ℝ) - x i) := by
      have : ((lam (i + 1) * (x (i + 1) + x i) : ℕ) : ℝ) ≤
          ((lam i * (x (i + 1) + x i) + 2 * S * (x (i + 1) - x i) : ℕ) : ℝ) := by
        exact_mod_cast hint
      push_cast [Nat.cast_sub hxi.le] at this
      exact this
    have hS' : (0 : ℝ) < S := by exact_mod_cast hS
    have hsum : (0 : ℝ) < (x (i + 1) : ℝ) + x i := by linarith
    have step : (lam (i + 1) : ℝ) / S ≤ (lam i : ℝ) / S +
        2 * ((x (i + 1) : ℝ) - x i) / ((x (i + 1) : ℝ) + x i) := by
      have key : (lam (i + 1) : ℝ) / S - (lam i : ℝ) / S -
          2 * ((x (i + 1) : ℝ) - x i) / ((x (i + 1) : ℝ) + x i) =
          ((lam (i + 1) : ℝ) * ((x (i + 1) : ℝ) + x i) - ((lam i : ℝ) * ((x (i + 1) : ℝ) + x i) +
            2 * S * ((x (i + 1) : ℝ) - x i))) / (S * ((x (i + 1) : ℝ) + x i)) := by
        field_simp
        ring
      have hneg : ((lam (i + 1) : ℝ) * ((x (i + 1) : ℝ) + x i) - ((lam i : ℝ) * ((x (i + 1) : ℝ) + x i) +
            2 * S * ((x (i + 1) : ℝ) - x i))) / (S * ((x (i + 1) : ℝ) + x i)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    linarith

/-- **Count bounds along a grid, CONDITIONAL ON `DusartPi11Body`.** -/
theorem count_le (hP : DusartPi11Body) (x lam U : ℕ → ℕ) (n S K : ℕ) (hS : 0 < S)
    (hK : K ≤ Nat.primeCounting' (x 0)) (hx60 : ∀ i ≤ n, 60184 ≤ x i)
    (hlam : ∀ i ≤ n, (lam i : ℝ) / S ≤ Real.log (x i))
    (hc : ∀ i ≤ n, 0 < i → 11 * S < 10 * lam i ∧ 10 * S * x i ≤ (U i + K) * (10 * lam i - 11 * S)) :
    ∀ i ≤ n, (Nat.primeCounting' (x i) : ℝ) - Nat.primeCounting' (x 0) ≤ U i := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  obtain ⟨h1, h2⟩ := hc i hi hpos
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hl11 : (1.1 : ℝ) < (lam i : ℝ) / S := by
    rw [lt_div_iff₀ hS']
    have : ((11 * S : ℕ) : ℝ) < ((10 * lam i : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hpi := pi'_le_of_dusart hP (hx60 i hi) (hlam i hi) hl11
  have hK' : (K : ℝ) ≤ Nat.primeCounting' (x 0) := by exact_mod_cast hK
  have hden : (0 : ℝ) < 10 * (lam i : ℝ) - 11 * S := by
    have : ((11 * S : ℕ) : ℝ) < ((10 * lam i : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have h2r : 10 * (S : ℝ) * x i ≤ ((U i : ℝ) + K) * (10 * (lam i : ℝ) - 11 * S) := by
    have : ((10 * S * x i : ℕ) : ℝ) ≤ (((U i + K) * (10 * lam i - 11 * S) : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast [Nat.cast_sub h1.le] at this
    exact this
  have e : (x i : ℝ) / ((lam i : ℝ) / S - 1.1) = 10 * (S : ℝ) * x i / (10 * (lam i : ℝ) - 11 * S) := by
    have hne : (lam i : ℝ) / S - 1.1 ≠ 0 := by linarith
    rw [div_eq_div_iff hne hden.ne']
    field_simp
    ring
  have h3 : (x i : ℝ) / ((lam i : ℝ) / S - 1.1) ≤ (U i : ℝ) + K := by
    rw [e, div_le_iff₀ hden]; exact h2r
  linarith

/-! ### The products over a tail of primes -/

lemma primesBelow_split {Y V : ℕ} (h3 : 3 < Y) (hYV : Y ≤ V) :
    primesBelow (V : ℝ) = primesBelow (Y : ℝ) ∪ primesIco Y V ∧
      Disjoint (primesBelow (Y : ℝ)) (primesIco Y V) := by
  refine ⟨?_, ?_⟩
  · ext p
    simp only [mem_union, mem_primesBelow, primesIco, mem_filter, mem_Ico, Nat.cast_lt]
    constructor
    · rintro ⟨hp, h3', hpV⟩
      rcases Nat.lt_or_ge p Y with h | h
      · exact Or.inl ⟨hp, h3', h⟩
      · exact Or.inr ⟨⟨h, hpV⟩, hp⟩
    · rintro (⟨hp, h3', h⟩ | ⟨⟨h1, h2⟩, hp⟩)
      · exact ⟨hp, h3', by omega⟩
      · exact ⟨hp, by omega, h2⟩
  · rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [mem_primesBelow, primesIco, mem_filter, mem_Ico, Nat.cast_lt] at h1 h2
    omega

lemma primes5Below_split {Y V : ℕ} (h5 : 5 ≤ Y) (hYV : Y ≤ V) :
    primes5Below (V : ℝ) = primes5Below (Y : ℝ) ∪ primesIco Y V ∧
      Disjoint (primes5Below (Y : ℝ)) (primesIco Y V) := by
  obtain ⟨hs, hd⟩ := primesBelow_split (by omega : 3 < Y) hYV
  refine ⟨?_, ?_⟩
  · unfold primes5Below
    rw [hs, filter_union]
    congr 1
    refine (filter_true_of_mem fun p hp => ?_)
    simp only [primesIco, mem_filter, mem_Ico] at hp
    omega
  · exact Finset.disjoint_of_subset_left (filter_subset _ _) hd

lemma PE_nonneg (a b Y : ℕ) : 0 ≤ PE a b Y :=
  prod_nonneg fun x _ => by linarith [f_ge ((a : ℝ) / b) x]

/-- **Error product over a tail, PROVED**: `1 + t ≤ e^t`. -/
theorem PE_tail (a b : ℕ) {Y V : ℕ} (h3 : 3 < Y) (hYV : Y ≤ V) :
    PE a b V ≤ PE a b Y * Real.exp (∑ p ∈ primesIco Y V, 8 / (p : ℝ) ^ ((a : ℝ) / b)) := by
  obtain ⟨hs, hd⟩ := primesBelow_split h3 hYV
  have e1 : PE a b V = PE a b Y * ∏ p ∈ primesIco Y V, (1 + 8 / (p : ℝ) ^ ((a : ℝ) / b)) := by
    unfold PE; rw [hs, prod_union hd]
  rw [e1, Real.exp_sum]
  refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun p _ => ?_) (fun p _ => ?_)) (PE_nonneg a b Y)
  · linarith [f_ge ((a : ℝ) / b) p]
  · linarith [Real.add_one_le_exp (8 / (p : ℝ) ^ ((a : ℝ) / b))]

/-- **Main product over a tail, PROVED**: `e^{-2/(p-2)} ≤ 1 - 2/p` for `p ≥ 5`. -/
theorem P5_tail {Y V : ℕ} (h5 : 5 ≤ Y) (hYV : Y ≤ V) :
    P5 Y * Real.exp (-∑ p ∈ primesIco Y V, 2 / ((p : ℝ) - 2)) ≤ P5 V := by
  obtain ⟨hs, hd⟩ := primes5Below_split h5 hYV
  have e1 : P5 V = P5 Y * ∏ p ∈ primesIco Y V, (1 - 2 / (p : ℝ)) := by
    unfold P5; rw [hs, prod_union hd]
  rw [e1, ← sum_neg_distrib, Real.exp_sum]
  refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => ?_))
    (P5_nonneg Y)
  simp only [primesIco, mem_filter, mem_Ico] at hp
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast (le_trans h5 hp.1.1)
  have hs0 : 0 < 2 / ((p : ℝ) - 2) := div_pos (by norm_num) (by linarith)
  have h1 := Real.add_one_le_exp (2 / ((p : ℝ) - 2))
  rw [Real.exp_neg]
  have h2 : (Real.exp (2 / ((p : ℝ) - 2)))⁻¹ ≤ (2 / ((p : ℝ) - 2) + 1)⁻¹ :=
    inv_anti₀ (by positivity) h1
  have h3 : (2 / ((p : ℝ) - 2) + 1)⁻¹ = 1 - 2 / (p : ℝ) := by
    have hq : (p : ℝ) - 2 ≠ 0 := by linarith
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    rw [show 2 / ((p : ℝ) - 2) + 1 = (p : ℝ) / ((p : ℝ) - 2) by field_simp; ring, inv_div]
    rw [eq_sub_iff_add_eq, ← add_div]
    rw [show (p : ℝ) - 2 + 2 = p by ring, div_self hp0]
  linarith

/-- **Chain step over a tail, PROVED**: `Good` at `Y`, bounds `Qm`, `Qe` on the tail sums and
`m' ≤ m e^{-Qm}`, `e e^{Qe} ≤ e'` give `Good` at `V`. -/
theorem good_of_tail {a b Y V m e m' e' : ℕ} (h : Good a b Y m e) (h5 : 5 ≤ Y) (hYV : Y ≤ V)
    {Qm Qe : ℝ} (hQm : ∑ p ∈ primesIco Y V, 2 / ((p : ℝ) - 2) ≤ Qm)
    (hQe : ∑ p ∈ primesIco Y V, 8 / (p : ℝ) ^ ((a : ℝ) / b) ≤ Qe)
    (hm : (m' : ℝ) ≤ m * Real.exp (-Qm)) (he : (e : ℝ) * Real.exp Qe ≤ e') : Good a b V m' e' := by
  have hR : (0 : ℝ) < R := by unfold R; positivity
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · calc (m' : ℝ) / R ≤ (m * Real.exp (-Qm)) / R := div_le_div_of_nonneg_right hm hR.le
      _ = (m : ℝ) / R * Real.exp (-Qm) := by ring
      _ ≤ P5 Y * Real.exp (-∑ p ∈ primesIco Y V, 2 / ((p : ℝ) - 2)) :=
          mul_le_mul h1 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (P5_nonneg Y)
      _ ≤ P5 V := P5_tail h5 hYV
  · calc PE a b V ≤ PE a b Y * Real.exp (∑ p ∈ primesIco Y V, 8 / (p : ℝ) ^ ((a : ℝ) / b)) :=
          PE_tail a b (by omega) hYV
      _ ≤ (e : ℝ) / R * Real.exp Qe :=
          mul_le_mul h2 (Real.exp_le_exp.mpr hQe) (Real.exp_pos _).le (by positivity)
      _ = ((e : ℝ) * Real.exp Qe) / R := by ring
      _ ≤ (e' : ℝ) / R := div_le_div_of_nonneg_right he hR.le

/-- The scaled sum `Φ n U n + Σ_{i<n} U (i+1) (Φ i - Φ (i+1))` over the naturals. -/
def abelN (F U : ℕ → ℕ) (n : ℕ) : ℕ := F n * U n + ∑ i ∈ range n, U (i + 1) * (F i - F (i + 1))

lemma abelN_cast (F U : ℕ → ℕ) (n S : ℕ) (hF : ∀ i < n, F (i + 1) ≤ F i) :
    ((abelN F U n : ℕ) : ℝ) / S = (F n : ℝ) / S * U n +
      ∑ i ∈ range n, (U (i + 1) : ℝ) * ((F i : ℝ) / S - (F (i + 1) : ℝ) / S) := by
  unfold abelN
  push_cast
  rw [add_div, sum_div]
  congr 1
  · ring
  · refine sum_congr rfl fun i hi => ?_
    rw [Nat.cast_sub (hF i (mem_range.mp hi))]
    ring

lemma scaled_pow_le {m m' A B N : ℕ} (hA : 0 < A) (hBA : B ≤ A)
    (h : m' * A ^ N ≤ m * (A - B) ^ N) :
    (m' : ℝ) ≤ m * (1 - ((B : ℝ) / A)) ^ N := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hr : (m' : ℝ) * (A : ℝ) ^ N ≤ m * ((A : ℝ) - B) ^ N := by
    have : ((m' * A ^ N : ℕ) : ℝ) ≤ ((m * (A - B) ^ N : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hBA] at this
    exact this
  have e : (1 - (B : ℝ) / A) = ((A : ℝ) - B) / A := by field_simp
  rw [e, div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hA' N)]
  exact hr

/-- **The tail certificate, CONDITIONAL ON `DusartPi11Body`.** From `Good` at `Y = x 0 ≥ 60184`,
a kernel checkable grid certificate up to `V = x n` and the scaled exponential checks with
`N`-th powers, `Good` at `V`. -/
theorem good_tail_cert (hP : DusartPi11Body) {a b Y V m e m' e' : ℕ} (hb : 0 < b)
    (h : Good a b Y m e) (x lam ell U Fm Fe : ℕ → ℕ) (n S K N : ℕ)
    (hx0 : x 0 = Y) (hxn : x n = V) (hY : 60184 ≤ Y) (hS : 0 < S) (hN : 0 < N)
    (hK : K ≤ Nat.primeCounting' Y) (hlam0 : (lam 0 : ℝ) / S ≤ Real.log Y)
    (hstep : ∀ i < n, x i < x (i + 1) ∧
      lam (i + 1) * (x (i + 1) + x i) ≤ lam i * (x (i + 1) + x i) + 2 * S * (x (i + 1) - x i) ∧
      ell i ^ b ≤ x i ^ a * 1000 ^ b ∧ 8000 * S ≤ Fe i * ell i ∧ 2 * S ≤ Fm i * (x i - 2) ∧
      Fe (i + 1) ≤ Fe i ∧ Fm (i + 1) ≤ Fm i)
    (hc : ∀ i ≤ n, 0 < i → 11 * S < 10 * lam i ∧ 10 * S * x i ≤ (U i + K) * (10 * lam i - 11 * S))
    (hmN : abelN Fm U n ≤ N * S) (heN : abelN Fe U n < N * S)
    (hm : m' * (N * S) ^ N ≤ m * (N * S - abelN Fm U n) ^ N)
    (he : e * (N * S) ^ N ≤ e' * (N * S - abelN Fe U n) ^ N) : Good a b V m' e' := by
  have hle : ∀ i < n, x i ≤ x (i + 1) := fun i hi => (hstep i hi).1.le
  have hx60 : ∀ i ≤ n, 60184 ≤ x i := fun i hi => by
    have := chain_le x n hle i hi; omega
  have hlam := lam_le_log x lam n S hS (by omega) (fun i hi => (hstep i hi).1)
    (fun i hi => (hstep i hi).2.1) (by rw [hx0]; exact hlam0)
  have hU := count_le hP x lam U n S K hS (by rw [hx0]; exact hK) hx60 hlam hc
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hYV : Y ≤ V := by rw [← hx0, ← hxn]; exact chain_le x n hle n le_rfl
  -- the main sum
  have hsm : ∑ p ∈ primesIco Y V, 2 / ((p : ℝ) - 2) ≤ ((abelN Fm U n : ℕ) : ℝ) / S := by
    rw [abelN_cast Fm U n S (fun i hi => (hstep i hi).2.2.2.2.2.2), ← hx0, ← hxn]
    refine tail_sum_le x (fun p => 2 / ((p : ℝ) - 2)) (fun i => (Fm i : ℝ) / S) (fun i => (U i : ℝ))
      n hle ?_ ?_ (by positivity) hU
    · intro i hi p h1 _ _
      have h60 := hx60 i hi.le
      have hxi : (60184 : ℝ) ≤ x i := by exact_mod_cast h60
      have hpx : (x i : ℝ) ≤ p := by exact_mod_cast h1
      have hF : ((2 * S : ℕ) : ℝ) ≤ ((Fm i * (x i - 2) : ℕ) : ℝ) := by
        exact_mod_cast (hstep i hi).2.2.2.2.1
      push_cast [Nat.cast_sub (by omega : 2 ≤ x i)] at hF
      calc 2 / ((p : ℝ) - 2) ≤ 2 / ((x i : ℝ) - 2) :=
            div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
        _ ≤ (Fm i : ℝ) / S := by
            rw [div_le_div_iff₀ (by linarith) hS']; linarith
    · intro i hi
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hstep i hi).2.2.2.2.2.2) hS'.le
  -- the error sum
  have hse : ∑ p ∈ primesIco Y V, 8 / (p : ℝ) ^ ((a : ℝ) / b) ≤ ((abelN Fe U n : ℕ) : ℝ) / S := by
    rw [abelN_cast Fe U n S (fun i hi => (hstep i hi).2.2.2.2.2.1), ← hx0, ← hxn]
    refine tail_sum_le x (fun p => 8 / (p : ℝ) ^ ((a : ℝ) / b)) (fun i => (Fe i : ℝ) / S)
      (fun i => (U i : ℝ)) n hle ?_ ?_ (by positivity) hU
    · intro i hi p h1 _ _
      obtain ⟨_, _, hell, hFe, _, _, _⟩ := hstep i hi
      have hell0 : 0 < ell i := by
        rcases Nat.eq_zero_or_pos (ell i) with h0 | h0
        · rw [h0] at hFe; omega
        · exact h0
      have hl := CampbellCase2Table.le_rpow_of_pow hb (by norm_num : 0 < 1000) hell
      have hpx : (x i : ℝ) ≤ p := by exact_mod_cast h1
      have hmono : (x i : ℝ) ^ ((a : ℝ) / b) ≤ (p : ℝ) ^ ((a : ℝ) / b) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hpx (by positivity)
      have hellpos : (0 : ℝ) < (ell i : ℝ) / (1000 : ℕ) := by
        have : (0 : ℝ) < ell i := by exact_mod_cast hell0
        positivity
      have hF : ((8000 * S : ℕ) : ℝ) ≤ ((Fe i * ell i : ℕ) : ℝ) := by exact_mod_cast hFe
      push_cast at hF hellpos
      have hell' : (0 : ℝ) < ell i := by exact_mod_cast hell0
      calc 8 / (p : ℝ) ^ ((a : ℝ) / b) ≤ 8 / ((ell i : ℝ) / (1000 : ℕ)) :=
            div_le_div_of_nonneg_left (by norm_num) (by push_cast; exact hellpos)
              (le_trans hl hmono)
        _ ≤ (Fe i : ℝ) / S := by
            push_cast
            rw [div_div_eq_mul_div, div_le_div_iff₀ hell' hS']
            linarith
    · intro i hi
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hstep i hi).2.2.2.2.2.1) hS'.le
  -- the exponentials
  have hNS : 0 < N * S := Nat.mul_pos hN hS
  have hNS' : ((N * S : ℕ) : ℝ) = (N : ℝ) * S := by push_cast; ring
  refine good_of_tail h (by omega) hYV hsm hse ?_ ?_
  · have h1 := scaled_pow_le hNS hmN hm
    have h2 := exp_neg_ge_pow hN (q := ((abelN Fm U n : ℕ) : ℝ) / S) (by positivity) (by
      rw [div_le_iff₀ hS']
      have : ((abelN Fm U n : ℕ) : ℝ) ≤ ((N * S : ℕ) : ℝ) := by exact_mod_cast hmN
      rw [hNS'] at this; exact this)
    have e : ((abelN Fm U n : ℕ) : ℝ) / ((N * S : ℕ) : ℝ) = ((abelN Fm U n : ℕ) : ℝ) / S / N := by
      rw [hNS', div_div, mul_comm]
    rw [e] at h1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hm0)
  · have hq : ((abelN Fe U n : ℕ) : ℝ) / S < N := by
      rw [div_lt_iff₀ hS']
      have : ((abelN Fe U n : ℕ) : ℝ) < ((N * S : ℕ) : ℝ) := by exact_mod_cast heN
      rw [hNS'] at this; exact this
    have h2 := exp_le_inv_pow hN (q := ((abelN Fe U n : ℕ) : ℝ) / S) (by positivity) hq
    have h1 := scaled_pow_le (m := e') (m' := e) hNS heN.le he
    have e1 : ((abelN Fe U n : ℕ) : ℝ) / ((N * S : ℕ) : ℝ) = ((abelN Fe U n : ℕ) : ℝ) / S / N := by
      rw [hNS', div_div, mul_comm]
    rw [e1] at h1
    have hpos : 0 < (1 - ((abelN Fe U n : ℕ) : ℝ) / S / N) ^ N := by
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      apply pow_pos
      rw [sub_pos, div_lt_one hN']; exact hq
    calc (e : ℝ) * Real.exp (((abelN Fe U n : ℕ) : ℝ) / S)
        ≤ e * ((1 - ((abelN Fe U n : ℕ) : ℝ) / S / N) ^ N)⁻¹ :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg e)
      _ ≤ e' := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact h1

end LeanLab.AlmostPrimes.CampbellTailU6836

#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.tail_sum_le
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.abel_le
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.good_of_tail
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.length_le_primeCounting'
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.log_ratio_ge
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.exp_le_inv_pow
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.pi'_le_of_dusart
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.lam_le_log
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.count_le
#print axioms LeanLab.AlmostPrimes.CampbellTailU6836.good_tail_cert
