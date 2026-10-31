/-
Unit U-1543, run 20261026T0808Z-17522, track T1. Decomposition of Lemma 6.7 of Liu-Wang 2002,
Acta Arith. 105, pp. 170-174, the bound for the bilinear sum `S4(α)`, the deepest step of
Proposition 6.1. This file: the sum `W` of (6.12)-(6.17) pp. 171-172, the coefficient step of
p. 173, (6.18)-(6.19), the four terms of (6.22) p. 174, and the assemblies `W_bound`,
`block_bound` and `lemma67`, proved CONDITIONAL ON the leaves of this file and of
Decomp1543a. Every numerical leaf is stated for `log N ≥ 3100`, the range of Theorem 1.
QUESTION, p. 173: the paper asserts `log U / log(N/V) ≥ 2/3`; this is false for every
`N > e`, see `ratio_claim_false`, PROVED. The true value of `1 - (log U/log(N/V))^2` exceeds
`5/9`; for `log N ≥ 3100` it is below `0.56`, `ratio_true`, and the leaves below use `0.56`.
With it the printed `1.926` and `0.861` of p. 174 become `1.94` and `0.87`; Proposition 6.1
still holds with its printed constants for `log N ≥ 3100`, see Decomp1543c.
Source: papers/P0023.pdf, pages 171-174 rendered with pdftoppm.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
CODEX task141, 2026-10-27: all 17 elementary leaves are now closed.
The cited rs2_mertens input remains open. Its source is named below.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LiuWang2002.Decomp1543a

namespace LeanLab.LiuWang2002.U1543

open Real Finset ArithmeticFunction MeasureTheory

/-! ### Objects -/

/-- The primes `p ≤ X`. -/
noncomputable def primesTo (X : ℝ) : Finset ℕ := (range (⌊X⌋₊ + 1)).filter Nat.Prime

/-- The sum of (6.13) p. 171: `∑_{U < p^i, p^k ≤ X} p^(-max(i,k)) log^2 p`. -/
noncomputable def ppSum (U X : ℝ) : ℝ :=
  ∑ p ∈ primesTo X, ∑ i ∈ Icc 1 ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
    if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ X then
      Real.log p ^ 2 / (p : ℝ) ^ (max i k) else 0

/-- `W1 = ∑_{U<p≤X} p^(-1) log^2 p`, (6.13). -/
noncomputable def W1 (U X : ℝ) : ℝ :=
  ∑ p ∈ primesTo X, if U < (p : ℝ) ∧ (p : ℝ) ≤ X then Real.log p ^ 2 / p else 0

/-- `W2 = ∑_{U<p^i≤X, i≥2} p^(-i) log^2 p`, (6.13). -/
noncomputable def W2 (U X : ℝ) : ℝ :=
  ∑ p ∈ primesTo X, ∑ i ∈ Icc 2 ⌊X⌋₊,
    if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X then Real.log p ^ 2 / (p : ℝ) ^ i else 0

/-- `W3 = ∑_{U<p^i<p^k≤X} p^(-k) log^2 p`, (6.13). -/
noncomputable def W3 (U X : ℝ) : ℝ :=
  ∑ p ∈ primesTo X, ∑ i ∈ Icc 1 ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
    if i < k ∧ U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X then Real.log p ^ 2 / (p : ℝ) ^ k else 0

/-- `∑_{p≤x} p^(-1) log p`, p. 172. -/
noncomputable def primeLogSum (x : ℝ) : ℝ := ∑ p ∈ primesTo x, Real.log p / p

/-- `W = ∑_{U<m≤X} a_m^2`, the sum over `m` in (6.12) p. 171, with `X = N/M_j`. -/
noncomputable def Wsum (N : ℕ) (U X : ℝ) : ℝ := ∑ m ∈ lRange N U X, am U m ^ 2

/-- The step of p. 171: two prime powers above `U` dividing `m ≤ U^2` share their prime. -/
def SamePrimeAt (U : ℝ) : Prop :=
  ∀ m p p' i k : ℕ, p.Prime → p'.Prime → 1 ≤ i → 1 ≤ k → U < (p : ℝ) ^ i → U < (p' : ℝ) ^ k →
    p ^ i ∣ m → p' ^ k ∣ m → 0 < m → (m : ℝ) ≤ U ^ 2 → p = p'

/-- The tail bound of pp. 171-172: `∑_{n>y} n^(-i) ≤ i/(i-1) · y^(1-i)` for `y ≥ 1`, `i ≥ 2`. -/
def TailPow : Prop :=
  ∀ y : ℝ, 1 ≤ y → ∀ i : ℕ, 2 ≤ i → ∀ K : ℕ,
    ∑ n ∈ (Icc 1 K).filter (fun n : ℕ => y < n), 1 / (n : ℝ) ^ i ≤
      (i : ℝ) / (i - 1) / y ^ (i - 1)

/-- The constant `0.6111 · 0.5203 · 0.56` of (6.21) p. 173, with `0.56` for the paper's `5/9`. -/
noncomputable def K67 : ℝ := 0.6111 * (0.5203 * 0.56)

/-! ### Input from another paper -/

/-- CITED, not proved in the lab: Rosser-Schoenfeld 1962, Illinois J. Math. 6, Theorem 6 and
(2.11), as used on p. 172: for `x ≥ 15000`, `log x - 1.385 ≤ ∑_{p≤x} p^(-1) log p ≤ log x - 1.28`. -/
theorem rs2_mertens (x : ℝ) (hx : 15000 ≤ x) :
    Real.log x - 1.385 ≤ primeLogSum x ∧ primeLogSum x ≤ Real.log x - 1.28 := by sorry

/-- Elementary logarithm bound for the range used on pages 171 to 174. -/
theorem task141_log_log (L : ℝ) (hL : 3100 ≤ L) : Real.log L ≤ 0.0027 * L := by
  have hL0 : 0 < L := by linarith
  have h8 : Real.log (3100 : ℝ) ≤ 8.3 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have he : (2.7 : ℝ) ≤ exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he 8
    have ee : exp (8 : ℝ) = exp 1 ^ 8 := by simpa using Real.exp_nat_mul (1 : ℝ) 8
    rw [show (8.3 : ℝ) = 8 + 0.3 by norm_num, Real.exp_add, ee]
    have ht := Real.add_one_le_exp (0.3 : ℝ)
    nlinarith
  have ht := Real.log_le_sub_one_of_pos (show 0 < L / 3100 by positivity)
  rw [Real.log_div hL0.ne' (by norm_num)] at ht
  linarith

/-- Logarithms of the parameters from display 6.6 on page 168. -/
theorem task141_logs (N : ℕ) (hL : 3100 ≤ Real.log N) :
    0 < (N : ℝ) ∧ 0 < Uf N ∧ 0 < Vf N ∧
    Real.log (Uf N) = 2 / 5 * Real.log N - 4 / 5 * Real.log (Real.log N) ∧
    Real.log (Vf N) = 2 / 5 * Real.log N + 1 / 5 * Real.log (Real.log N) := by
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hL; linarith
    · exact_mod_cast h
  have hL0 : 0 < Real.log N := by linarith
  have hp := Real.rpow_pos_of_pos hN ((2 : ℝ) / 5)
  have hU : 0 < Uf N := mul_pos hp (Real.rpow_pos_of_pos hL0 _)
  have hV : 0 < Vf N := mul_pos hp (Real.rpow_pos_of_pos hL0 _)
  refine ⟨hN, hU, hV, ?_, ?_⟩
  · unfold Uf
    rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]
    ring
  · unfold Vf
    rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]

/-! ### Leaves on `W`, pp. 171-173 -/

/-- LEAF. Unit U-1543. P. 171: if `r = p^i > U` and `s = p'^k > U` both divide `0 < m ≤ U^2`
then `p = p'`, since otherwise `rs | m` and `U^2 < rs ≤ m`. -/
theorem same_prime (U : ℝ) (hU : 0 ≤ U) : SamePrimeAt U := by
  intro m p p' i k hp hp' hi hk hUp hUp' hdvd hdvd' hm hmU2
  by_contra hneq
  have h1 : p ^ i * p' ^ k ∣ m := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ hdvd hdvd'
    apply Nat.Coprime.pow
    exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr (fun h => hneq (hp'.eq_one_or_self_of_dvd p h |>.resolve_left hp.ne_one))
  have h2 : p ^ i * p' ^ k ≤ m := Nat.le_of_dvd hm h1
  have h3 : (p ^ i * p' ^ k : ℝ) ≤ m := by exact_mod_cast h2
  have h4 : U * U < (p : ℝ) ^ i * (p' : ℝ) ^ k := by
    have p1 : 0 ≤ (p : ℝ) ^ i := by positivity
    have p2 : 0 < (p : ℝ) ^ i := lt_of_le_of_lt hU hUp
    have p3 : 0 ≤ U := hU
    nlinarith
  have h5 : (p : ℝ) ^ i * (p' : ℝ) ^ k = (p ^ i * p' ^ k : ℕ) := by push_cast; rfl
  rw [h5, ← sq] at h4
  linarith

/-- Reindex the coefficient from page 170 by its prime powers, as used on page 171. -/
theorem task141_am_expansion (U X : ℝ) (m : ℕ) (hm0 : 0 < m) (hmX : (m : ℝ) ≤ X) :
    am U m = ∑ p ∈ primesTo X, ∑ i ∈ Icc 1 ⌊X⌋₊,
      if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ p ^ i ∣ m then Real.log p else 0 := by
  classical
  let R := (m.divisors.filter (fun r : ℕ => U < r)).filter IsPrimePow
  let T := ((primesTo X) ×ˢ Icc 1 ⌊X⌋₊).filter (fun t : ℕ × ℕ =>
    U < (t.1 : ℝ) ^ t.2 ∧ (t.1 : ℝ) ^ t.2 ≤ X ∧ t.1 ^ t.2 ∣ m)
  have hr : ∑ r ∈ R, (vonMangoldt r : ℝ) = am U m := by
    unfold R am
    apply sum_subset (filter_subset _ _)
    intro r hr hnot
    apply vonMangoldt_eq_zero_iff.mpr
    simpa [hr] using hnot
  have he : (∑ t ∈ T, (vonMangoldt (t.1 ^ t.2) : ℝ)) = ∑ r ∈ R, (vonMangoldt r : ℝ) := by
    apply sum_bij (fun t ht => t.1 ^ t.2)
    · intro t ht
      obtain ⟨ht, hcond⟩ := mem_filter.mp ht
      obtain ⟨hp, hi⟩ := mem_product.mp ht
      have hprime := (mem_filter.mp hp).2
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hcond.2.2, hm0.ne'⟩, ?_⟩, ?_⟩
      · exact_mod_cast hcond.1
      · exact (isPrimePow_nat_iff _).mpr ⟨t.1, t.2, hprime, by have := (mem_Icc.mp hi).1; omega, rfl⟩
    · intro t ht s hs hEq
      have ht' := (mem_product.mp (mem_filter.mp ht).1)
      have hs' := (mem_product.mp (mem_filter.mp hs).1)
      have hp := (mem_filter.mp ht'.1).2
      have hp' := (mem_filter.mp hs'.1).2
      have hti : t.2 ≠ 0 := by have := (mem_Icc.mp ht'.2).1; omega
      have hsi : s.2 ≠ 0 := by have := (mem_Icc.mp hs'.2).1; omega
      exact Prod.ext ((hp.pow_inj' hp' hti hsi hEq).1) ((hp.pow_inj' hp' hti hsi hEq).2)
    · intro r hr
      obtain ⟨hr, hpp⟩ := mem_filter.mp hr
      obtain ⟨hdr, hUr⟩ := mem_filter.mp hr
      obtain ⟨p, i, hp, hi, hpi⟩ := (isPrimePow_nat_iff _).mp hpp
      have hrm : r ≤ m := Nat.le_of_dvd hm0 (Nat.mem_divisors.mp hdr).1
      have hrX : r ≤ ⌊X⌋₊ := Nat.le_floor ((by exact_mod_cast hrm : (r : ℝ) ≤ m).trans hmX)
      have hpr : p ≤ r := by
        rw [← hpi]
        exact Nat.le_self_pow (by omega : i ≠ 0) p
      have hir : i ≤ r := by
        rw [← hpi]
        exact (Nat.lt_pow_self hp.one_lt).le
      refine ⟨(p, i), ?_, hpi⟩
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩,
        mem_Icc.mpr ⟨hi, hir.trans hrX⟩⟩, ?_⟩
      have hpir : (p : ℝ) ^ i = r := by exact_mod_cast hpi
      exact ⟨hpir ▸ hUr, hpir ▸ ((by exact_mod_cast hrm : (r : ℝ) ≤ m).trans hmX), hpi ▸ (Nat.mem_divisors.mp hdr).1⟩
    · intro t ht
      rfl
  rw [← hr, ← he]
  unfold T
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro i hi
  have hprime := (mem_filter.mp hp).2
  rw [vonMangoldt_apply_pow (by have := (mem_Icc.mp hi).1; omega), vonMangoldt_apply_prime hprime]

/-- The square expansion in the proof of display 6.13 on page 171. -/
theorem task141_am_square (U X : ℝ) (m : ℕ) (hm0 : 0 < m) (hmX : (m : ℝ) ≤ X)
    (hmU : (m : ℝ) ≤ U ^ 2) (hsp : SamePrimeAt U) :
    am U m ^ 2 = ∑ p ∈ primesTo X, ∑ i ∈ Icc 1 ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
      if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ X ∧
        p ^ max i k ∣ m then Real.log p ^ 2 else 0 := by
  classical
  let B := Icc 1 ⌊X⌋₊
  let f := fun p i : ℕ => if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ p ^ i ∣ m then Real.log p else 0
  have he : am U m = ∑ p ∈ primesTo X, ∑ i ∈ B, f p i := task141_am_expansion U X m hm0 hmX
  have hcross (p q : ℕ) (hp : p ∈ primesTo X) (hq : q ∈ primesTo X) (hne : p ≠ q) :
      (∑ i ∈ B, f p i) * (∑ k ∈ B, f q k) = 0 := by
    rw [sum_mul_sum]
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro k hk
    dsimp [f]
    split_ifs with hpi hqk <;> try simp
    have hpq := hsp m p q i k (mem_filter.mp hp).2 (mem_filter.mp hq).2
      (mem_Icc.mp hi).1 (mem_Icc.mp hk).1 hpi.1 hqk.1 hpi.2.2 hqk.2.2 hm0 hmU
    exact (hne hpq).elim
  have hdiag : (∑ p ∈ primesTo X, ∑ i ∈ B, f p i) ^ 2 =
      ∑ p ∈ primesTo X, (∑ i ∈ B, f p i) ^ 2 := by
    rw [pow_two, sum_mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [sum_eq_single p]
    · exact (pow_two _).symm
    · intro q hq hqp
      exact hcross p q hp hq (Ne.symm hqp)
    · simp [hp]
  rw [he, hdiag]
  apply sum_congr rfl
  intro p hp
  rw [pow_two, sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro k hk
  have hdiv : p ^ max i k ∣ m ↔ p ^ i ∣ m ∧ p ^ k ∣ m := by
    rcases le_total i k with hik | hki
    · rw [max_eq_right hik]
      exact ⟨fun h => ⟨(pow_dvd_pow p hik).trans h, h⟩, And.right⟩
    · rw [max_eq_left hki]
      exact ⟨fun h => ⟨h, (pow_dvd_pow p hki).trans h⟩, And.left⟩
  dsimp [f]
  split_ifs with hi' hk' hc <;> simp_all [pow_two, hdiv] <;> tauto

/-- Count positive multiples in the range of display 6.12 on page 171. -/
theorem task141_count (N : ℕ) (U X : ℝ) (hX : 0 ≤ X) (d : ℕ) :
    (((lRange N U X).filter (fun m => d ∣ m)).card : ℝ) ≤ X / d := by
  have hsub : (lRange N U X).filter (fun m => d ∣ m) ⊆
      (range (⌊X⌋₊ + 1)).filter (fun m => m ≠ 0 ∧ d ∣ m) := by
    intro m hm
    obtain ⟨hm, hd⟩ := mem_filter.mp hm
    obtain ⟨hmN, hmU, hmX⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hmX)),
      ⟨by have := (mem_Icc.mp hmN).1; omega, hd⟩⟩
  calc
    _ ≤ (((range (⌊X⌋₊ + 1)).filter (fun m => m ≠ 0 ∧ d ∣ m)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ = ((⌊X⌋₊ / d : ℕ) : ℝ) := by rw [Nat.card_multiples']
    _ ≤ (⌊X⌋₊ : ℝ) / d := Nat.cast_div_le
    _ ≤ X / d := div_le_div_of_nonneg_right (Nat.floor_le hX) (Nat.cast_nonneg d)

/-- LEAF. Unit U-1543. (6.13) p. 171, first line: for `0 ≤ U` and `X ≤ U^2`,
`∑_{U<m≤X} a_m^2 ≤ X ∑_{U<p^i,p^k≤X} p^(-max(i,k)) log^2 p`, by `SamePrimeAt` and the count
of multiples of `p^max(i,k)` up to `X`. -/
theorem W_le (N : ℕ) (U X : ℝ) (hU : 0 ≤ U) (hX : X ≤ U ^ 2) (hsp : SamePrimeAt U) :
    Wsum N U X ≤ X * ppSum U X := by
  classical
  by_cases hX0 : 0 ≤ X
  · let P := primesTo X
    let B := Icc 1 ⌊X⌋₊
    let T := lRange N U X
    let F := fun (m p i k : ℕ) =>
      if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ X ∧
        p ^ max i k ∣ m then Real.log p ^ 2 else 0
    have he : Wsum N U X = ∑ p ∈ P, ∑ i ∈ B, ∑ k ∈ B, ∑ m ∈ T, F m p i k := by
      unfold Wsum
      calc
        _ = ∑ m ∈ T, ∑ p ∈ P, ∑ i ∈ B, ∑ k ∈ B, F m p i k := by
          apply sum_congr rfl
          intro m hm
          obtain ⟨hmN, hmU, hmX⟩ := mem_filter.mp hm
          have hm0 : 0 < m := (mem_Icc.mp hmN).1
          exact task141_am_square U X m hm0 hmX (hmX.trans hX) hsp
        _ = ∑ p ∈ P, ∑ m ∈ T, ∑ i ∈ B, ∑ k ∈ B, F m p i k := sum_comm
        _ = ∑ p ∈ P, ∑ i ∈ B, ∑ m ∈ T, ∑ k ∈ B, F m p i k := by
          apply sum_congr rfl
          intro p hp
          exact sum_comm
        _ = _ := by
          apply sum_congr rfl
          intro p hp
          apply sum_congr rfl
          intro i hi
          exact sum_comm
    rw [he]
    unfold ppSum
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    have hcount := task141_count N U X hX0 (p ^ max i k)
    push_cast at hcount
    by_cases hc : U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ X
    · rw [if_pos hc]
      have hsum : (∑ m ∈ T, F m p i k) =
          (((T.filter (fun m => p ^ max i k ∣ m)).card : ℕ) : ℝ) * Real.log p ^ 2 := by
        dsimp [F]
        simp only [show ∀ m, (U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧
            (p : ℝ) ^ k ≤ X ∧ p ^ max i k ∣ m) ↔ p ^ max i k ∣ m by intro m; tauto]
        rw [← sum_filter]
        simp
      rw [hsum]
      calc
        _ ≤ (X / (p : ℝ) ^ max i k) * Real.log p ^ 2 :=
          mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
        _ = _ := by ring
    · have hzero : ∑ m ∈ T, F m p i k = 0 := by
        apply sum_eq_zero
        intro m hm
        simp [F, show ¬ (U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧
          (p : ℝ) ^ k ≤ X ∧ p ^ max i k ∣ m) by tauto]
      rw [hzero, if_neg hc, mul_zero]
  · have hXneg : X < 0 := lt_of_not_ge hX0
    have hP : primesTo X = ∅ := by
      unfold primesTo
      rw [Nat.floor_of_nonpos hXneg.le]
      norm_num
    have hT : lRange N U X = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro m hm
      have hmX := (mem_filter.mp hm).2.2
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    simp [Wsum, ppSum, hP, hT]


/-- Finite symmetric sum bookkeeping for display 6.13 on page 171. -/
theorem task141_symmetric_sum (s : Finset ℕ) (F : ℕ → ℕ → ℝ) (hsym : ∀ i k, F i k = F k i) :
    ∑ i ∈ s, ∑ k ∈ s, F i k = (∑ i ∈ s, F i i) +
      2 * ∑ i ∈ s, ∑ k ∈ s, if i < k then F i k else 0 := by
  have hparts (i k : ℕ) : F i k = (if k = i then F i i else 0) +
      (if i < k then F i k else 0) + (if k < i then F i k else 0) := by
    rcases lt_trichotomy i k with h | h | h
    · simp [h, ne_of_gt h, not_lt.mpr h.le]
    · subst k; simp
    · simp [h, ne_of_lt h, not_lt.mpr h.le]
  have he : (∑ i ∈ s, ∑ k ∈ s, F i k) = (∑ i ∈ s, F i i) +
      (∑ i ∈ s, ∑ k ∈ s, if i < k then F i k else 0) +
      (∑ i ∈ s, ∑ k ∈ s, if k < i then F i k else 0) := by
    calc
      _ = ∑ i ∈ s, ∑ k ∈ s, ((if k = i then F i i else 0) +
          (if i < k then F i k else 0) + (if k < i then F i k else 0)) := by
        exact sum_congr rfl fun i hi => sum_congr rfl fun k hk => hparts i k
      _ = _ := by
        simp only [sum_add_distrib]
        congr 2
        apply sum_congr rfl
        intro i hi
        simp [hi]
  have hswap : (∑ i ∈ s, ∑ k ∈ s, if k < i then F i k else 0) =
      ∑ i ∈ s, ∑ k ∈ s, if i < k then F i k else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro k hk
    rw [hsym k i]
  rw [hswap] at he
  linarith

/-- LEAF. Unit U-1543. (6.13) p. 171, the split of the double sum into the diagonal
`i = k = 1`, the diagonal `i = k ≥ 2`, and twice the part `i < k`. -/
theorem W_split (U X : ℝ) : ppSum U X = W1 U X + W2 U X + 2 * W3 U X := by
  classical
  unfold ppSum W1 W2 W3
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hp' : Nat.Prime p := (mem_filter.mp hp).2
  have hpF : p ≤ ⌊X⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
  have hF1 : 1 ≤ ⌊X⌋₊ := le_trans hp'.one_lt.le hpF
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
  let F : ℕ → ℕ → ℝ := fun i k =>
    if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ X then
      Real.log p ^ 2 / (p : ℝ) ^ (max i k) else 0
  have hs : ∀ i k, F i k = F k i := by
    intro i k
    dsimp [F]
    rw [max_comm]
    congr 1
    apply propext
    tauto
  have hd : (∑ i ∈ Icc 1 ⌊X⌋₊, F i i) =
      (if U < (p : ℝ) ∧ (p : ℝ) ≤ X then Real.log p ^ 2 / p else 0) +
      ∑ i ∈ Icc 2 ⌊X⌋₊, if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X then
        Real.log p ^ 2 / (p : ℝ) ^ i else 0 := by
    have hI : Icc 1 ⌊X⌋₊ = insert 1 (Icc 2 ⌊X⌋₊) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]
    simp [F, and_assoc, and_left_comm, and_comm]
  have hu : (∑ i ∈ Icc 1 ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊, if i < k then F i k else 0) =
      ∑ i ∈ Icc 1 ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
        if i < k ∧ U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X then
          Real.log p ^ 2 / (p : ℝ) ^ k else 0 := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro k hk
    by_cases hik : i < k
    · have hpow := pow_le_pow_right₀ hp1 hik.le
      have hc : (U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X ∧ U < (p : ℝ) ^ k ∧ (p : ℝ) ^ k ≤ X) ↔
          (U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X) := by
        constructor
        · tauto
        · rintro ⟨ha, hb⟩
          exact ⟨ha, hpow.trans hb, ha.trans_le hpow, hb⟩
      simp [F, hik, max_eq_right hik.le, hc]
    · simp [hik]
  simpa only [hd, hu] using task141_symmetric_sum (Icc 1 ⌊X⌋₊) F hs


/-- The integral comparison for the tail in displays 6.14 and 6.15 on pages 171 to 172. -/
theorem task141_integer_tail (a K i : ℕ) (ha : 1 ≤ a) (hi : 2 ≤ i) :
    ∑ n ∈ Ico a K, 1 / ((n + 1 : ℕ) : ℝ) ^ i ≤
      (1 / ((i : ℝ) - 1)) / (a : ℝ) ^ (i - 1) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hi0 : (i : ℝ) > 1 := by exact_mod_cast (show 1 < i by omega)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(i : ℝ))) (Set.Icc (a : ℝ) K) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (ha0.trans_le hx.1) hxy (by linarith)
  have ht := hanti.sum_Ico_le_integral
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(i : ℝ) < -1) ha0)
    (fun x hx => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx]) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -(i : ℝ) < -1) ha0] at ht
  have he (n j : ℕ) : (n : ℝ) ^ (-(j : ℝ)) = 1 / (n : ℝ) ^ j := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
  simp_rw [he] at ht
  have hexp : -(i : ℝ) + 1 = -((i - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num
    ring
  rw [hexp, he a (i - 1), Nat.cast_sub (by omega : 1 ≤ i)] at ht
  norm_num only [Nat.cast_one] at ht
  convert ht using 1 <;> field_simp <;> ring


/-- LEAF. Unit U-1543. The tail bound used in (6.14) and (6.15), pp. 171-172. -/
theorem tail_pow : TailPow := by
  intro y hy i hi K
  have hy0 : 0 < y := by linarith
  have hi0 : 0 < (i : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < (i : ℤ) - 1 by omega)
  let a := ⌊y⌋₊ + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hya : y < (a : ℝ) := by simpa [a] using Nat.lt_floor_add_one y
  have ha0 : (0 : ℝ) < a := hy0.trans hya
  have hset : (Icc 1 K).filter (fun n : ℕ => y < n) = Icc a K := by
    ext n
    simp only [mem_filter, mem_Icc]
    rw [← Nat.floor_lt hy0.le]
    dsimp [a]
    omega
  rw [hset]
  by_cases hKa : K < a
  · rw [Icc_eq_empty_of_lt hKa, sum_empty]
    positivity
  have haK : a ≤ K := by omega
  have hI : Icc a K = insert a (Icc (a + 1) K) := by ext n; simp only [mem_Icc, mem_insert]; omega
  rw [hI, sum_insert (by simp)]
  have hshift : (∑ n ∈ Icc (a + 1) K, 1 / (n : ℝ) ^ i) =
      ∑ n ∈ Ico a K, 1 / ((n + 1 : ℕ) : ℝ) ^ i := by
    apply sum_bij (fun n hn => n - 1)
    · intro n hn
      simp only [mem_Icc, mem_Ico] at hn ⊢
      omega
    · intro n hn m hm hnm
      simp only [mem_Icc] at hn hm
      omega
    · intro n hn
      refine ⟨n + 1, ?_, by omega⟩
      simp only [mem_Icc, mem_Ico] at hn ⊢
      omega
    · intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Icc.mp hn).1; omega
      rw [Nat.sub_add_cancel hn1]
  rw [hshift]
  have ht := task141_integer_tail a K i ha hi
  have hp1 : 1 / (a : ℝ) ^ i ≤ 1 / y ^ (i - 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have hyi : y ^ (i - 1) ≤ y ^ i := pow_le_pow_right₀ hy (by omega)
    exact hyi.trans (pow_le_pow_left₀ hy0.le hya.le _)
  have hp2 : (1 / ((i : ℝ) - 1)) / (a : ℝ) ^ (i - 1) ≤
      (1 / ((i : ℝ) - 1)) / y ^ (i - 1) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hy0.le hya.le _)
  have he : 1 / y ^ (i - 1) + (1 / ((i : ℝ) - 1)) / y ^ (i - 1) =
      (i : ℝ) / (i - 1) / y ^ (i - 1) := by field_simp; ring
  linarith


/-- The reciprocal coefficient sum in display 6.14 on page 172. -/
theorem task141_telescope (K : ℕ) : ∑ i ∈ Icc 2 K, 1 / ((i : ℝ) * (i - 1)) ≤ 1 := by
  suffices hh : ∀ K : ℕ, 1 ≤ K → (∑ i ∈ Icc 2 K, 1 / ((i : ℝ) * (i - 1))) = 1 - 1 / K by
    by_cases hk : 1 ≤ K
    · rw [hh K hk]
      have ht : (0 : ℝ) ≤ 1 / K := by positivity
      linarith
    · have : K = 0 := by omega
      subst K; simp
  intro K
  induction K with
  | zero => omega
  | succ K ih =>
    intro hk
    by_cases hK : K = 0
    · subst K; simp
    have hK1 : 1 ≤ K := by omega
    rw [sum_Icc_succ_top (by omega : 2 ≤ K + 1), ih hK1]
    have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    push_cast
    field_simp [hKr.ne']
    ring

/-- One exponent of the prime power estimate in display 6.14 on page 172. -/
theorem task141_perpower (hT : TailPow) (U X : ℝ) (hU : 1 ≤ U) (hX : 1 ≤ X) (i : ℕ) (hi : 2 ≤ i) :
    (∑ p ∈ primesTo X, if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X then
      Real.log p ^ 2 / (p : ℝ) ^ i else 0) ≤
      Real.log X ^ 2 / ((i : ℝ) * (i - 1)) / √U := by
  have hU0 : 0 < U := by linarith
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hi2 : (2 : ℝ) ≤ i := by exact_mod_cast hi
  have hi1 : 0 < (i : ℝ) - 1 := by linarith
  let t := U ^ (1 / (i : ℝ))
  have ht0 : 0 < t := Real.rpow_pos_of_pos hU0 _
  have ht1 : 1 ≤ t := Real.one_le_rpow hU (by positivity)
  have htlog : Real.log t = Real.log U / i := by dsimp [t]; rw [Real.log_rpow hU0]; ring
  have hpoint (p : ℕ) (hp : p ∈ primesTo X) :
      (if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X then Real.log p ^ 2 / (p : ℝ) ^ i else 0) ≤
      (Real.log X / i) ^ 2 * (if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0) := by
    have hpr := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    split_ifs with hc ht
    · have hlp0 := (Real.log_pos hp1).le
      have hl := Real.log_le_log (pow_pos hp0 i) hc.2
      rw [Real.log_pow] at hl
      have hlp : Real.log p ≤ Real.log X / i := (le_div_iff₀ hi0).mpr (by nlinarith)
      have hsq : Real.log p ^ 2 ≤ (Real.log X / i) ^ 2 := by nlinarith
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ ((p : ℝ) ^ i)⁻¹)
    · have hl := Real.log_lt_log hU0 hc.1
      rw [Real.log_pow] at hl
      have ht' : t < (p : ℝ) := by
        apply (Real.log_lt_log_iff ht0 hp0).mp
        rw [htlog]
        apply (div_lt_iff₀ hi0).mpr
        nlinarith
      exact (ht ht').elim
    · positivity
    · simp
  have hsum : (∑ p ∈ primesTo X, if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0) ≤
      ∑ n ∈ (Icc 1 ⌊X⌋₊).filter (fun n : ℕ => t < n), 1 / (n : ℝ) ^ i := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, htp⟩ := mem_filter.mp hp
      obtain ⟨hprange, hprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.one_lt.le,
        Nat.lt_succ_iff.mp (mem_range.mp hprange)⟩, htp⟩
    · intro n hn hnot
      positivity
  have htail := hT t ht1 i hi ⌊X⌋₊
  have hroot : √U ≤ t ^ (i - 1) := by
    apply (Real.log_le_log_iff (Real.sqrt_pos.mpr hU0) (pow_pos ht0 _)).mp
    rw [Real.log_sqrt hU0.le, Real.log_pow, htlog]
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num only [Nat.cast_one]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hi0).mpr
    have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
    nlinarith
  calc
    _ ≤ ∑ p ∈ primesTo X, (Real.log X / i) ^ 2 * (if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0) :=
      sum_le_sum hpoint
    _ = (Real.log X / i) ^ 2 * ∑ p ∈ primesTo X, if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0 := by rw [mul_sum]
    _ ≤ (Real.log X / i) ^ 2 * ((i : ℝ) / (i - 1) / t ^ (i - 1)) :=
      mul_le_mul_of_nonneg_left (hsum.trans htail) (sq_nonneg _)
    _ ≤ (Real.log X / i) ^ 2 * ((i : ℝ) / (i - 1) / √U) := by gcongr
    _ = _ := by field_simp [hi0.ne', hi1.ne']

/-- LEAF. Unit U-1543. (6.14) p. 172: `W2 ≤ U^(-1/2) log^2 X` for `U, X ≥ 1`. -/
theorem W2_le (hT : TailPow) (U X : ℝ) (hU : 1 ≤ U) (hX : 1 ≤ X) :
    W2 U X ≤ Real.log X ^ 2 / √U := by
  unfold W2
  rw [sum_comm]
  calc
    _ ≤ ∑ i ∈ Icc 2 ⌊X⌋₊, Real.log X ^ 2 / ((i : ℝ) * (i - 1)) / √U := by
      apply sum_le_sum
      intro i hi
      exact task141_perpower hT U X hU hX i (mem_Icc.mp hi).1
    _ = (Real.log X ^ 2 / √U) * ∑ i ∈ Icc 2 ⌊X⌋₊, 1 / ((i : ℝ) * (i - 1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ ≤ (Real.log X ^ 2 / √U) * 1 :=
      mul_le_mul_of_nonneg_left (task141_telescope _) (by positivity)
    _ = _ := mul_one _

/-- One ordered exponent pair in display 6.15 on page 172. -/
theorem task141_offpower (hT : TailPow) (U X : ℝ) (hU : 1 ≤ U) (hX : 1 ≤ X) (i j : ℕ) (hj : 1 ≤ j) (hji : j < i) :
    (∑ p ∈ primesTo X, if U < (p : ℝ) ^ j ∧ (p : ℝ) ^ i ≤ X then
      Real.log p ^ 2 / (p : ℝ) ^ i else 0) ≤
      Real.log X ^ 2 / ((i : ℝ) * (i - 1)) / U := by
  have hi : 2 ≤ i := by omega
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hU0 : 0 < U := by linarith
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hi2 : (2 : ℝ) ≤ i := by exact_mod_cast hi
  have hi1 : 0 < (i : ℝ) - 1 := by linarith
  let t := U ^ (1 / (j : ℝ))
  have ht0 : 0 < t := Real.rpow_pos_of_pos hU0 _
  have ht1 : 1 ≤ t := Real.one_le_rpow hU (by positivity)
  have htlog : Real.log t = Real.log U / j := by dsimp [t]; rw [Real.log_rpow hU0]; ring
  have hpoint (p : ℕ) (hp : p ∈ primesTo X) :
      (if U < (p : ℝ) ^ j ∧ (p : ℝ) ^ i ≤ X then Real.log p ^ 2 / (p : ℝ) ^ i else 0) ≤
      (Real.log X / i) ^ 2 * (if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0) := by
    have hpr := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    split_ifs with hc ht
    · have hlp0 := (Real.log_pos hp1).le
      have hl := Real.log_le_log (pow_pos hp0 i) hc.2
      rw [Real.log_pow] at hl
      have hlp : Real.log p ≤ Real.log X / i := (le_div_iff₀ hi0).mpr (by nlinarith)
      have hsq : Real.log p ^ 2 ≤ (Real.log X / i) ^ 2 := by nlinarith
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ ((p : ℝ) ^ i)⁻¹)
    · have hl := Real.log_lt_log hU0 hc.1
      rw [Real.log_pow] at hl
      have ht' : t < (p : ℝ) := by
        apply (Real.log_lt_log_iff ht0 hp0).mp
        rw [htlog]
        apply (div_lt_iff₀ hj0).mpr
        nlinarith
      exact (ht ht').elim
    · positivity
    · simp
  have hsum : (∑ p ∈ primesTo X, if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0) ≤
      ∑ n ∈ (Icc 1 ⌊X⌋₊).filter (fun n : ℕ => t < n), 1 / (n : ℝ) ^ i := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, htp⟩ := mem_filter.mp hp
      obtain ⟨hprange, hprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.one_lt.le,
        Nat.lt_succ_iff.mp (mem_range.mp hprange)⟩, htp⟩
    · intro n hn hnot
      positivity
  have htail := hT t ht1 i hi ⌊X⌋₊
  have hroot : U ≤ t ^ (i - 1) := by
    apply (Real.log_le_log_iff hU0 (pow_pos ht0 _)).mp
    rw [Real.log_pow, htlog, ← mul_div_assoc]
    apply (le_div_iff₀ hj0).mpr
    have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
    have hij : (j : ℝ) ≤ (i - 1 : ℕ) := by exact_mod_cast (show j ≤ i - 1 by omega)
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hij hlogU
  calc
    _ ≤ ∑ p ∈ primesTo X, (Real.log X / i) ^ 2 * (if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0) :=
      sum_le_sum hpoint
    _ = (Real.log X / i) ^ 2 * ∑ p ∈ primesTo X, if t < (p : ℝ) then 1 / (p : ℝ) ^ i else 0 := by rw [mul_sum]
    _ ≤ (Real.log X / i) ^ 2 * ((i : ℝ) / (i - 1) / t ^ (i - 1)) :=
      mul_le_mul_of_nonneg_left (hsum.trans htail) (sq_nonneg _)
    _ ≤ (Real.log X / i) ^ 2 * ((i : ℝ) / (i - 1) / U) := by gcongr
    _ = _ := by field_simp [hi0.ne', hi1.ne']

/-- LEAF. Unit U-1543. (6.15) p. 172: `W3 ≤ U^(-1) log^2 X ∑_{2≤k≤log X/log 2} 1/k`. -/
theorem W3_le (hT : TailPow) (U X : ℝ) (hU : 1 ≤ U) (hX : 1 ≤ X) :
    W3 U X ≤ Real.log X ^ 2 / U *
      ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) / k := by
  classical
  let B := Icc 1 ⌊X⌋₊
  let C := ⌊Real.log X / Real.log 2⌋₊
  let S := fun k : ℕ => ∑ i ∈ B, ∑ p ∈ primesTo X,
    if i < k ∧ U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X then Real.log p ^ 2 / (p : ℝ) ^ k else 0
  have hre : W3 U X = ∑ k ∈ B, S k := by
    unfold W3
    calc
      _ = ∑ p ∈ primesTo X, ∑ k ∈ B, ∑ i ∈ B,
          if i < k ∧ U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X then Real.log p ^ 2 / (p : ℝ) ^ k else 0 := by
        apply sum_congr rfl
        intro p hp
        exact sum_comm
      _ = ∑ k ∈ B, ∑ p ∈ primesTo X, ∑ i ∈ B,
          if i < k ∧ U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X then Real.log p ^ 2 / (p : ℝ) ^ k else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro k hk
        exact sum_comm
  have hzero (k : ℕ) (hk : ¬ (2 ≤ k ∧ k ≤ C)) : S k = 0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro p hp
    split_ifs with hc
    · have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
      have hk2 : 2 ≤ k := by omega
      have hpr := (mem_filter.mp hp).2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hlp := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp2
      have hl := Real.log_le_log (pow_pos hp0 k) hc.2.2
      rw [Real.log_pow] at hl
      have hkC : k ≤ C := by
        apply Nat.le_floor
        apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
        nlinarith [mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hlp)]
      exact (hk ⟨hk2, hkC⟩).elim
    · rfl
  have hbound (k : ℕ) (hk : k ∈ B) (hk2 : 2 ≤ k) : S k ≤ Real.log X ^ 2 / U * (1 / k) := by
    have hkF : k ≤ ⌊X⌋₊ := (mem_Icc.mp hk).2
    have hI : B.filter (fun i => i < k) = Icc 1 (k - 1) := by
      ext i
      simp only [B, mem_filter, mem_Icc]
      omega
    have he : S k = ∑ i ∈ B.filter (fun i => i < k), ∑ p ∈ primesTo X,
        if U < (p : ℝ) ^ i ∧ (p : ℝ) ^ k ≤ X then Real.log p ^ 2 / (p : ℝ) ^ k else 0 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      by_cases hik : i < k <;> simp [hik]
    rw [he, hI]
    calc
      _ ≤ ∑ i ∈ Icc 1 (k - 1), Real.log X ^ 2 / ((k : ℝ) * (k - 1)) / U := by
        apply sum_le_sum
        intro i hi
        exact task141_offpower hT U X hU hX k i (mem_Icc.mp hi).1 (by have := (mem_Icc.mp hi).2; omega)
      _ = _ := by
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
          have ht : (2 : ℝ) ≤ k := by exact_mod_cast hk2
          linarith
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num only [Nat.cast_one]
        field_simp [hk0.ne', hk1.ne']
  rw [hre]
  calc
    _ = ∑ k ∈ B.filter (fun k => 2 ≤ k ∧ k ≤ C), S k := by
      symm
      apply sum_subset (filter_subset _ _)
      intro k hk hnot
      apply hzero
      simpa [hk] using hnot
    _ ≤ ∑ k ∈ B.filter (fun k => 2 ≤ k ∧ k ≤ C), Real.log X ^ 2 / U * (1 / k) := by
      apply sum_le_sum
      intro k hk
      exact hbound k (mem_filter.mp hk).1 (mem_filter.mp hk).2.1
    _ ≤ ∑ k ∈ Icc 2 C, Real.log X ^ 2 / U * (1 / k) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact mem_Icc.mpr (mem_filter.mp hk).2
      · intro k hk hnot
        positivity
    _ = _ := by rw [mul_sum]


/-- Abel summation in display 6.16 on page 172. -/
theorem task141_abel (U X : ℝ) (hU : 1 ≤ U) (hUX : U ≤ X) :
    W1 U X = Real.log X * primeLogSum X - Real.log U * primeLogSum U -
      ∫ t in Set.Ioc U X, t⁻¹ * primeLogSum t := by
  classical
  let c := fun n : ℕ => if n.Prime then Real.log n / n else 0
  have hsum (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, c k) = primeLogSum t := by
    unfold primeLogSum primesTo
    rw [sum_filter]
    have he : Icc 0 ⌊t⌋₊ = range (⌊t⌋₊ + 1) := by ext k; simp
    rw [he]
  have hU0 : 0 < U := by linarith
  have hX0 : 0 < X := hU0.trans_le hUX
  have hdiff : ∀ t ∈ Set.Icc U X, DifferentiableAt ℝ Real.log t := by
    intro t ht
    exact Real.differentiableAt_log (ne_of_gt (hU0.trans_le ht.1))
  have hder : Set.EqOn (deriv Real.log) (fun t : ℝ => t⁻¹) (Set.Icc U X) := by
    intro t ht
    exact Real.deriv_log t
  have hint : IntegrableOn (deriv Real.log) (Set.Icc U X) := by
    apply IntegrableOn.congr_fun _ hder.symm measurableSet_Icc
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_inv₀.mono
    intro t ht
    exact ne_of_gt (hU0.trans_le ht.1)
  have hab := sum_mul_eq_sub_sub_integral_mul c hU0.le hUX hdiff hint
  simp_rw [hsum] at hab
  have he : (∑ k ∈ Ioc ⌊U⌋₊ ⌊X⌋₊, Real.log k * c k) = W1 U X := by
    unfold W1 primesTo
    rw [sum_filter]
    have hsub : Ioc ⌊U⌋₊ ⌊X⌋₊ ⊆ range (⌊X⌋₊ + 1) := by
      intro k hk
      exact mem_range.mpr (by have := (mem_Ioc.mp hk).2; omega)
    calc
      _ = ∑ k ∈ Ioc ⌊U⌋₊ ⌊X⌋₊,
          if k.Prime then (if U < (k : ℝ) ∧ (k : ℝ) ≤ X then Real.log k ^ 2 / k else 0) else 0 := by
        apply sum_congr rfl
        intro k hk
        have hkU : U < (k : ℝ) := (Nat.floor_lt hU0.le).mp (mem_Ioc.mp hk).1
        have hkX : (k : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (mem_Ioc.mp hk).2
        simp [c, hkU, hkX, pow_two, mul_div_assoc]
      _ = _ := by
        apply sum_subset hsub
        intro k hk hnot
        by_cases hpk : k.Prime
        · simp only [if_pos hpk]
          have hnotU : ¬ U < (k : ℝ) := by
            intro hu
            apply hnot
            exact mem_Ioc.mpr ⟨(Nat.floor_lt hU0.le).mpr hu, by have := mem_range.mp hk; omega⟩
          simp [hnotU]
        · simp [hpk]
  rw [he] at hab
  rw [hab]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only [Real.deriv_log]

/-- LEAF. Unit U-1543. (6.16)-(6.17) p. 172, partial summation: if
`log x - a ≤ ∑_{p≤x} p^(-1) log p ≤ log x - b` on `[U, X]`, `1 ≤ U ≤ X`, then
`W1 ≤ (log^2 X - log^2 U)/2 + (a - b) log X`. The paper has `a = 1.385`, `b = 1.28`. -/
theorem W1_le (U X a b : ℝ) (hU : 1 ≤ U) (hUX : U ≤ X)
    (hM : ∀ x, U ≤ x → x ≤ X →
      Real.log x - a ≤ primeLogSum x ∧ primeLogSum x ≤ Real.log x - b) :
    W1 U X ≤ (Real.log X ^ 2 - Real.log U ^ 2) / 2 + (a - b) * Real.log X := by
  classical
  have hU0 : 0 < U := by linarith
  have hX0 : 0 < X := hU0.trans_le hUX
  have hlog : ContinuousOn Real.log (Set.Icc U X) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (hU0.trans_le ht.1)
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc U X) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_inv₀.mono
    intro t ht
    exact ne_of_gt (hU0.trans_le ht.1)
  have hilow : IntegrableOn (fun t : ℝ => (Real.log t - a) / t) (Set.Icc U X) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (hlog.sub continuousOn_const).div continuousOn_id (fun t ht => ne_of_gt (hU0.trans_le ht.1))
  let c := fun n : ℕ => if n.Prime then Real.log n / n else 0
  have hsum (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, c k) = primeLogSum t := by
    unfold primeLogSum primesTo
    rw [sum_filter]
    have he : Icc 0 ⌊t⌋₊ = range (⌊t⌋₊ + 1) := by ext k; simp
    rw [he]
  have hiPS : IntegrableOn (fun t : ℝ => t⁻¹ * primeLogSum t) (Set.Icc U X) := by
    simpa only [hsum] using integrableOn_mul_sum_Icc c (m := 0) hU0.le hinv
  have hd : ∀ t ∈ Set.uIcc U X, HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2 - a * Real.log t)
      ((Real.log t - a) / t) t := by
    intro t ht
    have ht0 : 0 < t := hU0.trans_le ((Set.uIcc_of_le hUX) ▸ ht).1
    convert (((Real.hasDerivAt_log ht0.ne').pow 2).div_const 2).sub
      ((Real.hasDerivAt_log ht0.ne').const_mul a) using 1 <;> field_simp <;> ring
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hUX).mpr hilow)
  rw [intervalIntegral.integral_of_le hUX] at heval
  have hmi := setIntegral_mono_on (hilow.mono_set Set.Ioc_subset_Icc_self)
    (hiPS.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc (fun t ht => show
      (Real.log t - a) / t ≤ t⁻¹ * primeLogSum t from by
        have ht0 : 0 ≤ t := hU0.le.trans ht.1.le
        simpa only [div_eq_inv_mul] using
          div_le_div_of_nonneg_right (hM t ht.1.le ht.2).1 ht0)
  rw [heval] at hmi
  rw [task141_abel U X hU hUX]
  have htop := mul_le_mul_of_nonneg_left (hM X hUX le_rfl).2 (Real.log_nonneg (hU.trans hUX))
  have hbot := mul_le_mul_of_nonneg_left (hM U le_rfl hUX).1 (Real.log_nonneg hU)
  nlinarith


/-- LEAF. Unit U-1543. (6.14) p. 172, the number: `U^(-1/2) log^2 X ≤ 2.5876` for
`1 ≤ X ≤ N/V` and `log N ≥ 3100`. -/
theorem W2_num (N : ℕ) (hL : 3100 ≤ Real.log N) (X : ℝ) (hX1 : 1 ≤ X) (hX : X ≤ N / Vf N) :
    Real.log X ^ 2 / √(Uf N) ≤ 2.5876 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hl := task141_log_log (Real.log N) hL
  have hL0 : 0 < Real.log N := by linarith
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hV1 : 1 ≤ Vf N := (Real.log_nonneg_iff hV).mp (by rw [hlv]; positivity)
  have hXN : X ≤ N := hX.trans (div_le_self hN.le hV1)
  have hx0 : 0 < X := by linarith
  have hlX0 := Real.log_nonneg hX1
  have hlX := Real.log_le_log hx0 hXN
  have hpow : Real.log N ^ 4 ≤ Uf N := by
    apply (Real.log_le_log_iff (by positivity) hU).mp
    rw [Real.log_pow, hlu]
    norm_num
    linarith
  have hs : Real.log N ^ 2 ≤ √(Uf N) := by
    rw [Real.le_sqrt (sq_nonneg _) hU.le]
    nlinarith [hpow]
  have hs0 : 0 < √(Uf N) := Real.sqrt_pos.mpr hU
  have hsq : Real.log X ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hd : Real.log X ^ 2 / √(Uf N) ≤ 1 := (div_le_one hs0).mpr (hsq.trans hs)
  linarith

/-- LEAF. Unit U-1543. (6.15) p. 172, the number: `U^(-1) log^2 X ∑ 1/k ≤ 0.0681`. -/
theorem W3_num (N : ℕ) (hL : 3100 ≤ Real.log N) (X : ℝ) (hX1 : 1 ≤ X) (hX : X ≤ N / Vf N) :
    Real.log X ^ 2 / Uf N * ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) / k ≤ 0.0681 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hl := task141_log_log (Real.log N) hL
  have hL0 : 0 < Real.log N := by linarith
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hV1 : 1 ≤ Vf N := (Real.log_nonneg_iff hV).mp (by rw [hlv]; positivity)
  have hXN : X ≤ N := hX.trans (div_le_self hN.le hV1)
  have hx0 : 0 < X := by linarith
  have hlX0 := Real.log_nonneg hX1
  have hlX := Real.log_le_log hx0 hXN
  have hpow : Real.log N ^ 4 ≤ Uf N := by
    apply (Real.log_le_log_iff (by positivity) hU).mp
    rw [Real.log_pow, hlu]
    norm_num
    linarith
  have h2 : (0.5 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have hs : ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) / k ≤ 2 * Real.log N := by
    calc
      _ ≤ ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) := by
        apply sum_le_sum
        intro k hk
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        exact (div_le_one (by linarith)).mpr (by linarith)
      _ = ((Icc 2 ⌊Real.log X / Real.log 2⌋₊).card : ℝ) := by simp
      _ ≤ (⌊Real.log X / Real.log 2⌋₊ : ℝ) := by
        exact_mod_cast (show (Icc 2 ⌊Real.log X / Real.log 2⌋₊).card ≤
          ⌊Real.log X / Real.log 2⌋₊ by rw [Nat.card_Icc]; omega)
      _ ≤ Real.log X / Real.log 2 := Nat.floor_le (by positivity)
      _ ≤ 2 * Real.log N := by
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith
  have hsq : Real.log X ^ 2 ≤ Real.log N ^ 2 := by nlinarith
  have hs0 : 0 ≤ ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) / k :=
    sum_nonneg fun _ _ => by positivity
  have hm := mul_le_mul hsq hs hs0 (sq_nonneg (Real.log N))
  rw [div_mul_eq_mul_div, div_le_iff₀ hU]
  have hh := mul_nonneg (show 0 ≤ 0.0681 * Real.log N - 2 by linarith)
    (show 0 ≤ Real.log N ^ 3 by positivity)
  nlinarith

/-- LEAF. Unit U-1543. P. 173, first display: for `U ≤ X ≤ N/V` and `log N ≥ 3100`,
`(log^2 X - log^2 U)/2 + 0.105 log X + 2.5876 + 2 · 0.0681 ≤ 0.5203 (log^2(N/V) - log^2 U)`. -/
theorem W_coeff (N : ℕ) (hL : 3100 ≤ Real.log N) (X : ℝ) (hUX : Uf N ≤ X) (hX : X ≤ N / Vf N) :
    (Real.log X ^ 2 - Real.log (Uf N) ^ 2) / 2 + 0.105 * Real.log X + 2.5876 + 2 * 0.0681 ≤
      0.5203 * (Real.log (N / Vf N) ^ 2 - Real.log (Uf N) ^ 2) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hl := task141_log_log (Real.log N) hL
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hnv : Real.log (N / Vf N) = 3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N) := by
    rw [Real.log_div hN.ne' hV.ne', hlv]
    ring
  have ha0 : 0 ≤ Real.log (Uf N) := by rw [hlu]; linarith
  have hx0 : 0 ≤ Real.log X := ha0.trans (Real.log_le_log hU hUX)
  have hxb := Real.log_le_log (hU.trans_le hUX) hX
  have hb0 : 0 ≤ Real.log (N / Vf N) := hx0.trans hxb
  have hsq : Real.log X ^ 2 ≤ Real.log (N / Vf N) ^ 2 := by nlinarith
  have hdiff : 0.19 * Real.log N ^ 2 ≤ Real.log (N / Vf N) ^ 2 - Real.log (Uf N) ^ 2 := by
    have h1 : 0.2 * Real.log N ≤ Real.log (N / Vf N) - Real.log (Uf N) := by
      rw [hnv, hlu]; linarith
    have h2 : 0.997 * Real.log N ≤ Real.log (N / Vf N) + Real.log (Uf N) := by
      rw [hnv, hlu]; linarith
    have hh := mul_le_mul h1 h2 (by positivity : 0 ≤ 0.997 * Real.log N)
      (by linarith : 0 ≤ Real.log (N / Vf N) - Real.log (Uf N))
    nlinarith
  have hbL : Real.log (N / Vf N) ≤ Real.log N := by rw [hnv]; linarith
  nlinarith [sq_nonneg (Real.log N - 3100)]

/-- LEAF. Unit U-1543. Replacement for the step `log U / log(N/V) ≥ 2/3` of p. 173, which is
false: for `log N ≥ 3100`, `log^2(N/V) - log^2 U ≤ 0.56 log^2(N/V)`. The true ratio is
`1 - (log U / log(N/V))^2 = 0.55939...` at `log N = 3100` and decreases to `5/9`. -/
theorem ratio_true (N : ℕ) (hL : 3100 ≤ Real.log N) :
    Real.log (N / Vf N) ^ 2 - Real.log (Uf N) ^ 2 ≤ 0.56 * Real.log (N / Vf N) ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hl := task141_log_log (Real.log N) hL
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hnv : Real.log (N / Vf N) = 3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N) := by
    rw [Real.log_div hN.ne' hV.ne', hlv]
    ring
  rw [hnv, hlu]
  have ha : 0 ≤ 2 / 5 * Real.log N - 4 / 5 * Real.log (Real.log N) := by linarith
  have hb : 0 ≤ 3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N) := by linarith
  have hab : 0.6635 * (3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N)) ≤
      2 / 5 * Real.log N - 4 / 5 * Real.log (Real.log N) := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (show 0 ≤ (2 / 5 * Real.log N - 4 / 5 * Real.log (Real.log N)) +
      0.6635 * (3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N)) by positivity)]

/-- LEAF. Unit U-1543. The size facts behind pp. 168-174 for `log N ≥ 3100`: `U ≥ 15000`,
`V ≥ exp(13.066)`, `UV ≤ N`, `N/V ≤ U^2`, `U ≤ N/V`, `N > 0`. From (6.5), (6.6) and p. 173. -/
theorem params_facts (N : ℕ) (hL : 3100 ≤ Real.log N) :
    15000 ≤ Uf N ∧ exp 13.066 ≤ Vf N ∧ Uf N * Vf N ≤ N ∧ (N : ℝ) / Vf N ≤ Uf N ^ 2 ∧
      Uf N ≤ N / Vf N ∧ (0 : ℝ) < N := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hl := task141_log_log (Real.log N) hL
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hnv : Real.log (N / Vf N) = 3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N) := by
    rw [Real.log_div hN.ne' hV.ne', hlv]
    ring
  have he20 : (15000 : ℝ) ≤ exp 20 := by
    have he : (2 : ℝ) ≤ exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 20
    have ee : exp (20 : ℝ) = exp 1 ^ 20 := by simpa using Real.exp_nat_mul (1 : ℝ) 20
    rw [ee]
    norm_num at hp ⊢
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, hN⟩
  · apply he20.trans
    apply (Real.le_log_iff_exp_le hU).mp
    rw [hlu]
    linarith
  · apply (Real.le_log_iff_exp_le hV).mp
    rw [hlv]
    linarith
  · apply (Real.log_le_log_iff (mul_pos hU hV) hN).mp
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  · apply (Real.log_le_log_iff (div_pos hN hV) (pow_pos hU 2)).mp
    rw [hnv, Real.log_pow, hlu]
    norm_num
    linarith
  · apply (Real.log_le_log_iff hU (div_pos hN hV)).mp
    rw [hlu, hnv]
    linarith

/-- LEAF. Unit U-1543. (6.18)-(6.19) p. 173: for `V ≤ M ≤ N/U`, `2 ≤ q ≤ N`, `log N ≥ 3100`,
`([([N/M] - [U])/q] + 1)(5(M + 0.5) + q log q) ≤ 5N/q + 5M + (N/M) log q + q log q`;
the curly bracket of (6.18) is negative. -/
theorem bracket_6_19 (N : ℕ) (hL : 3100 ≤ Real.log N) (M : ℝ) (hVM : Vf N ≤ M)
    (hMU : M ≤ N / Uf N) (q : ℕ) (hq : 2 ≤ q) (hqN : q ≤ N) :
    ((((⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊) / q : ℕ) : ℝ) + 1) * (5 * (M + 1 / 2) + q * Real.log q) ≤
      5 * N / q + 5 * M + N / M * Real.log q + q * Real.log q := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  obtain ⟨hU15, hV13, hUV, hNVU, hUNV, _⟩ := params_facts N hL
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hUV' : Uf N ≤ Vf N := by
    apply (Real.log_le_log_iff hU hV).mp
    rw [hlu, hlv]
    linarith
  have hM0 : 0 < M := hV.trans_le hVM
  have hUM : Uf N ≤ M := hUV'.trans hVM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0.5 ≤ Real.log q := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq2
    linarith [Real.log_two_gt_d9]
  have hUA : Uf N ≤ N / M := by
    rw [le_div_iff₀ hM0]
    rw [le_div_iff₀ hU] at hMU
    nlinarith
  have hA : (N : ℝ) / M ≤ M * Uf N := by
    have hh : (N : ℝ) / M ≤ N / Vf N := div_le_div_of_nonneg_left hN.le hV hVM
    nlinarith [mul_le_mul_of_nonneg_right hUM hU.le]
  have hfloor : (⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊ : ℕ) ≤ ⌊(N : ℝ) / M⌋₊ := Nat.sub_le _ _
  have hsub : ((⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊ : ℕ) : ℝ) ≤ N / M - Uf N + 1 := by
    rw [Nat.cast_sub (Nat.floor_mono hUA)]
    have ht := Nat.lt_floor_add_one (Uf N)
    have ha := Nat.floor_le (div_nonneg hN.le hM0.le)
    linarith
  have hdiv : (((⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊) / q : ℕ) : ℝ) ≤
      (N / M - Uf N + 1) / q := by
    have ht : (((⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊) / q : ℕ) : ℝ) ≤
        ((⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊ : ℕ) : ℝ) / q := by
      exact Nat.cast_div_le
    exact ht.trans (div_le_div_of_nonneg_right hsub hq0.le)
  calc
    _ ≤ ((N / M - Uf N + 1) / q + 1) * (5 * (M + 1 / 2) + q * Real.log q) := by
      gcongr
    _ ≤ _ := by
      have hneg : 0 ≤ (Uf N - 1) * Real.log q - 2.5 := by
        nlinarith [mul_nonneg (show 0 ≤ Uf N - 6 by linarith) (show 0 ≤ Real.log q - 0.5 by linarith)]
      have hm := mul_nonneg hM0.le (show 0 ≤ 2.5 * Uf N - 5 by linarith)
      have hn : 0 ≤ 5 * M * (Uf N - 1) - 2.5 * (N / M) + 2.5 * (Uf N - 1) := by
        nlinarith
      have hid : (5 * N / q + 5 * M + N / M * Real.log q + q * Real.log q) -
          (((N / M - Uf N + 1) / q + 1) * (5 * (M + 1 / 2) + q * Real.log q)) =
          (5 * M * (Uf N - 1) - 2.5 * (N / M) + 2.5 * (Uf N - 1)) / q +
            ((Uf N - 1) * Real.log q - 2.5) := by
        field_simp
        ring
      apply sub_nonneg.mp
      rw [hid]
      exact add_nonneg (div_nonneg hn hq0.le) hneg


/-- The logarithmic factors in display 6.22 on page 174. -/
theorem task141_factors (N : ℕ) (hL : 3100 ≤ Real.log N) :
    0 ≤ Real.log (N / Vf N) ∧ Real.log (N / Vf N) ≤ 0.6 * Real.log N ∧
    0 ≤ 1 + Real.log (N / (Uf N * Vf N)) / Real.log 2 ∧
    1 + Real.log (N / (Uf N * Vf N)) / Real.log 2 ≤ 0.292 * Real.log N := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hl := task141_log_log (Real.log N) hL
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have hnv : Real.log (N / Vf N) = 3 / 5 * Real.log N - 1 / 5 * Real.log (Real.log N) := by
    rw [Real.log_div hN.ne' hV.ne', hlv]
    ring
  have hnuv : Real.log (N / (Uf N * Vf N)) = 1 / 5 * Real.log N +
      3 / 5 * Real.log (Real.log N) := by
    rw [Real.log_div hN.ne' (mul_pos hU hV).ne', Real.log_mul hU.ne' hV.ne', hlu, hlv]
    ring
  have h2 : (0.693 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  refine ⟨by rw [hnv]; linarith, by rw [hnv]; linarith, ?_, ?_⟩
  · rw [hnuv]
    positivity
  · have hh : Real.log (N / (Uf N * Vf N)) / Real.log 2 ≤ 0.2915 * Real.log N := by
      apply (div_le_iff₀ (by linarith)).mpr
      rw [hnuv]
      nlinarith
    linarith

/-! ### Leaves, the four terms of (6.22) p. 174 -/

/-- LEAF. Unit U-1543. (6.22) p. 174, first term, `≤ 0.2264 N q^(-1/2) log^2 N`. -/
theorem term1_num (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ) (hq : 1 ≤ q) :
    √(K67 * N) * Real.log (N / Vf N) *
        ((1 + Real.log (N / (Uf N * Vf N)) / Real.log 2) * √(5 * N / q)) ≤
      0.2264 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  obtain ⟨hl0, hl, hc0, hc⟩ := task141_factors N hL
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hK : 0 ≤ K67 := by norm_num [K67]
  have hk : √K67 ≤ 0.423 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num [K67]
  have h5 : √(5 : ℝ) ≤ 2.237 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [Real.sqrt_mul hK, Real.sqrt_div' _ hq0.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
  calc
    _ ≤ 0.423 * √N * (0.6 * Real.log N) *
        ((0.292 * Real.log N) * (2.237 * √N / √q)) := by gcongr
    _ = (0.423 * 0.6 * 0.292 * 2.237) * N / √q * Real.log N ^ 2 := by
      ring_nf
      rw [Real.sq_sqrt hN.le]
      ring
    _ ≤ _ := by gcongr <;> norm_num

/-- LEAF. Unit U-1543. (6.22) p. 174, second term, `≤ 1.94 N^(4/5) log^1.4 N`; the paper
prints `1.926`, which rests on the false `5/9`. -/
theorem term2_num (N : ℕ) (hL : 3100 ≤ Real.log N) :
    √(K67 * N) * Real.log (N / Vf N) * (√5 * ((2 + √2) * √(N / Uf N))) ≤
      1.94 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  obtain ⟨hl0, hl, hc0, hc⟩ := task141_factors N hL
  have hL0 : 0 < Real.log N := by linarith
  have hK : 0 ≤ K67 := by norm_num [K67]
  have hk : √K67 ≤ 0.423 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num [K67]
  have h5 : √(5 : ℝ) ≤ 2.237 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(2 : ℝ) ≤ 1.415 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs : √(N : ℝ) * √(N / Uf N) = (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (0.4 : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt hN.le,
      Real.log_sqrt (by positivity), Real.log_div hN.ne' hU.ne', hlu,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
    ring
  calc
    _ = √K67 * √5 * (2 + √2) * (√N * √(N / Uf N)) * Real.log (N / Vf N) := by
      rw [Real.sqrt_mul hK]; ring
    _ ≤ 0.423 * 2.237 * 3.415 *
        ((N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (0.4 : ℝ)) * (0.6 * Real.log N) := by
      rw [hs]
      gcongr
      linarith
    _ = (0.423 * 2.237 * 3.415 * 0.6) * (N : ℝ) ^ ((4 : ℝ) / 5) *
        Real.log N ^ (1.4 : ℝ) := by
      rw [show (1.4 : ℝ) = 0.4 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := by gcongr <;> norm_num

/-- LEAF. Unit U-1543. (6.22) p. 174, third term, `≤ 0.87 N^(4/5) log^1.4 N` for `q ≤ N`;
the paper prints `0.861`, which rests on the false `5/9`. -/
theorem term3_num (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) :
    √(K67 * N) * Real.log (N / Vf N) * (√(N * Real.log q) * ((2 + √2) / √(Vf N))) ≤
      0.87 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  obtain ⟨hl0, hl, hc0, hc⟩ := task141_factors N hL
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqN' : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 hqN'
  have hK : 0 ≤ K67 := by norm_num [K67]
  have hk : √K67 ≤ 0.423 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num [K67]
  have h2 : √(2 : ℝ) ≤ 1.415 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs : √(N : ℝ) * √(N * Real.log N) / √(Vf N) =
      (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (0.4 : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_sqrt hN.le,
      Real.log_sqrt (by positivity), Real.log_mul hN.ne' hL0.ne', Real.log_sqrt hV.le,
      hlv, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
    ring
  calc
    _ = √K67 * (2 + √2) * (√N * √(N * Real.log q) / √(Vf N)) * Real.log (N / Vf N) := by
      rw [Real.sqrt_mul hK]; ring
    _ ≤ √K67 * (2 + √2) * (√N * √(N * Real.log N) / √(Vf N)) * Real.log (N / Vf N) := by
      gcongr
    _ ≤ 0.423 * 3.415 * ((N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (0.4 : ℝ)) *
        (0.6 * Real.log N) := by
      rw [hs]
      gcongr
      linarith
    _ = (0.423 * 3.415 * 0.6) * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
      rw [show (1.4 : ℝ) = 0.4 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := by gcongr <;> norm_num

/-- LEAF. Unit U-1543. (6.22) p. 174, fourth term, `≤ 0.0785 N^(1/2) q^(1/2) log^2.5 N`
for `q ≤ N`. -/
theorem term4_num (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) :
    √(K67 * N) * Real.log (N / Vf N) *
        ((1 + Real.log (N / (Uf N * Vf N)) / Real.log 2) * √(q * Real.log q)) ≤
      0.0785 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  obtain ⟨hl0, hl, hc0, hc⟩ := task141_factors N hL
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqN' : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 hqN'
  have hK : 0 ≤ K67 := by norm_num [K67]
  have hk : √K67 ≤ 0.423 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num [K67]
  rw [Real.sqrt_mul hK, Real.sqrt_mul hq0.le]
  calc
    _ ≤ 0.423 * √N * (0.6 * Real.log N) *
        ((0.292 * Real.log N) * (√q * √(Real.log N))) := by gcongr
    _ = (0.423 * 0.6 * 0.292) * √N * √q * Real.log N ^ (2.5 : ℝ) := by
      rw [show (2.5 : ℝ) = (2 : ℕ) + (1 / 2 : ℝ) by norm_num,
        Real.rpow_add hL0, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := by gcongr <;> norm_num


/-- Displays 6.13 to 6.15 on pages 171 to 172, with only W1 left to estimate. -/
theorem task141_W_reduction (N : ℕ) (U X : ℝ) (hU : 1 ≤ U) (hX : 1 ≤ X)
    (hXU : X ≤ U ^ 2) :
    Wsum N U X ≤ X * (W1 U X + Real.log X ^ 2 / √U +
      2 * (Real.log X ^ 2 / U * ∑ k ∈ Icc 2 ⌊Real.log X / Real.log 2⌋₊, (1 : ℝ) / k)) := by
  have hU0 : 0 ≤ U := by linarith
  have hw := W_le N U X hU0 hXU (same_prime U hU0)
  rw [W_split] at hw
  have h2 := W2_le tail_pow U X hU hX
  have h3 := W3_le tail_pow U X hU hX
  apply hw.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  linarith

/-! ### The false step of p. 173 -/

/-- QUESTION evidence, PROVED: for `log N > 1`, `log U / log(N/V) < 2/3`, so the claim
`≥ 2/3` on p. 173 fails. Indeed `(2 - 4x)/(3 - x) < 2/3` for `x = log log N / log N > 0`. -/
theorem ratio_claim_false (N : ℕ) (hL : 1 < Real.log N) :
    Real.log (Uf N) / Real.log (N / Vf N) < 2 / 3 := by
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hL; linarith
    · exact_mod_cast h
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hlL : 0 < Real.log L := Real.log_pos hL
  have hlL' : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hL0
  have hNp : (0 : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos hN _
  have hU : Real.log (Uf N) = 2 / 5 * L - 4 / 5 * Real.log L := by
    unfold Uf
    rw [Real.log_mul hNp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]
    ring
  have hV : Real.log (N / Vf N) = 3 / 5 * L - 1 / 5 * Real.log L := by
    unfold Vf
    rw [Real.log_div hN.ne' (mul_pos hNp (Real.rpow_pos_of_pos hL0 _)).ne',
      Real.log_mul hNp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]
    ring
  rw [hU, hV, div_lt_iff₀ (by linarith)]
  linarith

/-! ### Assemblies -/

/-- Helper: `√(a+b+c+d) ≤ √a + √b + √c + √d` for nonnegative reals. PROVED. -/
theorem sqrt_add4_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    √(a + b + c + d) ≤ √a + √b + √c + √d := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc, Real.sq_sqrt hd,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sqrt_nonneg d,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg d),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg d),
    mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg d)]

/-- P. 173 first display with `0.56` in place of `5/9`: for `U ≤ X ≤ N/V`, `log N ≥ 3100`,
`W ≤ 0.5203 · 0.56 · X log^2(N/V)`. PROVED, CONDITIONAL ON `same_prime`, `W_le`, `W_split`,
`tail_pow`, `W1_le`, `rs2_mertens`, `W2_le`, `W3_le`, `W2_num`, `W3_num`, `W_coeff`,
`ratio_true`, `params_facts`. -/
theorem W_bound (N : ℕ) (hL : 3100 ≤ Real.log N) (X : ℝ) (hUX : Uf N ≤ X) (hXV : X ≤ N / Vf N) :
    Wsum N (Uf N) X ≤ X * (0.5203 * 0.56) * Real.log (N / Vf N) ^ 2 := by
  obtain ⟨hU15, -, -, hNVU, -, -⟩ := params_facts N hL
  have hU1 : (1 : ℝ) ≤ Uf N := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXU2 : X ≤ Uf N ^ 2 := hXV.trans hNVU
  have h1 := W_le N (Uf N) X (by linarith) hXU2 (same_prime _ (by linarith))
  rw [W_split] at h1
  have hw1 := W1_le (Uf N) X 1.385 1.28 hU1 hUX
    (fun x hx _ => rs2_mertens x (by linarith))
  have hw2 := (W2_le tail_pow (Uf N) X hU1 hX1).trans (W2_num N hL X hX1 hXV)
  have hw3 := (W3_le tail_pow (Uf N) X hU1 hX1).trans (W3_num N hL X hX1 hXV)
  have hc := W_coeff N hL X hUX hXV
  have hr := ratio_true N hL
  have hsum : W1 (Uf N) X + W2 (Uf N) X + 2 * W3 (Uf N) X ≤
      0.5203 * 0.56 * Real.log (N / Vf N) ^ 2 := by
    nlinarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  calc Wsum N (Uf N) X ≤ X * (W1 (Uf N) X + W2 (Uf N) X + 2 * W3 (Uf N) X) := h1
    _ ≤ X * (0.5203 * 0.56 * Real.log (N / Vf N) ^ 2) := mul_le_mul_of_nonneg_left hsum hX0
    _ = X * (0.5203 * 0.56) * Real.log (N / Vf N) ^ 2 := by ring

/-- (6.11), (6.12), (6.19), (6.20), (6.21) p. 170-173, one block: for `V ≤ M ≤ N/U`,
`|block_M| ≤ (K N)^(1/2) log(N/V) ((5N/q)^(1/2) + 5^(1/2) M^(1/2) + (N log q)^(1/2) M^(-1/2)
+ (q log q)^(1/2))` with `K = 0.6111 · 0.5203 · 0.56`. PROVED, CONDITIONAL ON
`block_cauchy`, `squarefree_dyadic`, `square_expand`, `geom_dyadic`, `inner_l_sum`,
`wc_lemma2`, `W_bound` and its leaves, `bracket_6_19`, `params_facts`. -/
theorem block_bound (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq : 2 ≤ q) (hqN : q ≤ N) (M : ℝ) (hVM : Vf N ≤ M)
    (hMU : M ≤ N / Uf N) :
    ‖block c N (Uf N) M α‖ ≤ √(K67 * N) * Real.log (N / Vf N) *
      (√(5 * N / q) + √5 * √M + √(N * Real.log q) * (1 / √M) + √(q * Real.log q)) := by
  obtain ⟨hU15, hV13, -, -, -, hN0⟩ := params_facts N hL
  have hU0 : 0 < Uf N := by linarith
  have hM13 : exp 13.066 ≤ M := hV13.trans hVM
  have hM1 : (1 : ℝ) ≤ M := le_trans (Real.one_le_exp (by norm_num)) hM13
  have hM0 : 0 < M := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hUX : Uf N ≤ N / M := by
    rw [le_div_iff₀ hM0]; rw [le_div_iff₀ hU0] at hMU; linarith
  have hXV : (N : ℝ) / M ≤ N / Vf N :=
    div_le_div_of_nonneg_left hN0.le (by linarith [Real.exp_pos 13.066]) hVM
  -- the bound on `∑ |μ|`
  have hA := squarefree_dyadic N M hM13
  -- the bound on `∑ |inner|^2`
  set G : ℝ := ((((⌊(N : ℝ) / M⌋₊ - ⌊Uf N⌋₊) / q : ℕ) : ℝ) + 1) *
    (5 * (M + 1 / 2) + q * Real.log q) with hG
  have hG0 : 0 ≤ G := by positivity
  have hB1 := square_expand c N (Uf N) M α hU0.le hM1 (fun θ A B hA hB =>
    geom_dyadic θ M hM0.le A B hA hB)
  have hB2 : ∑ m ∈ lRange N (Uf N) (N / M), am (Uf N) m ^ 2 *
      ∑ l ∈ lRange N (Uf N) (N / M), minK (M + 1 / 2) (α * ((m : ℝ) - l)) ≤
      Wsum N (Uf N) (N / M) * G := by
    unfold Wsum
    rw [sum_mul]
    refine sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact inner_l_sum wc_lemma2 α a q hD N (Uf N) (N / M) (M + 1 / 2) hU0.le (by linarith) m
  have hW := W_bound N hL (N / M) hUX hXV
  have hW0 : 0 ≤ Wsum N (Uf N) (N / M) := sum_nonneg fun _ _ => sq_nonneg _
  have hBr := bracket_6_19 N hL M hVM hMU q hq hqN
  set ℓ := Real.log (N / Vf N) with hℓ
  set Br : ℝ := 5 * N / q + 5 * M + N / M * Real.log q + q * Real.log q with hBrdef
  have hBr0 : 0 ≤ Br := by positivity
  have hB : ∑ t ∈ tBlock N M, ‖inner c N (Uf N) α t‖ ^ 2 ≤ N / M * (0.5203 * 0.56) * ℓ ^ 2 * Br :=
    hB1.trans (hB2.trans (mul_le_mul hW hBr hG0 (by positivity)))
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓ]
    apply Real.log_nonneg
    obtain ⟨-, -, -, -, h, -⟩ := params_facts N hL
    linarith
  have hK : 0.6111 * M * (N / M * (0.5203 * 0.56) * ℓ ^ 2 * Br) = K67 * N * ℓ ^ 2 * Br := by
    unfold K67; field_simp
  have hsplit : √Br ≤ √(5 * N / q) + √5 * √M + √(N * Real.log q) * (1 / √M) +
      √(q * Real.log q) := by
    have h4 := sqrt_add4_le (5 * N / q) (5 * M) (N / M * Real.log q) (q * Real.log q)
      (by positivity) (by positivity) (by positivity) (by positivity)
    have e1 : √(5 * M) = √5 * √M := Real.sqrt_mul (by norm_num) M
    have e2 : √(N / M * Real.log q) = √(N * Real.log q) * (1 / √M) := by
      rw [show (N : ℝ) / M * Real.log q = N * Real.log q / M by ring,
        Real.sqrt_div' _ hM0.le]
      ring
    rw [e1, e2] at h4
    exact h4
  calc ‖block c N (Uf N) M α‖
      ≤ √(∑ t ∈ tBlock N M, |(moebius t : ℝ)|) *
          √(∑ t ∈ tBlock N M, ‖inner c N (Uf N) α t‖ ^ 2) := block_cauchy _ _
    _ ≤ √(0.6111 * M) * √(N / M * (0.5203 * 0.56) * ℓ ^ 2 * Br) :=
        mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √(K67 * N) * ℓ * √Br := by
        rw [← Real.sqrt_mul (by positivity), hK,
          Real.sqrt_mul (by unfold K67; positivity), Real.sqrt_mul (by unfold K67; positivity),
          Real.sqrt_sq hℓ0]
    _ ≤ √(K67 * N) * ℓ * (√(5 * N / q) + √5 * √M + √(N * Real.log q) * (1 / √M) +
          √(q * Real.log q)) := mul_le_mul_of_nonneg_left hsplit (by positivity)

/-- Lemma 6.7 p. 170, for `log N ≥ 3100`, with the corrected constant:
`|S4(α)| ≤ 0.2264 N q^(-1/2) log^2 N + 2.81 N^(4/5) log^1.4 N + 0.0785 N^(1/2) q^(1/2) log^2.5 N`;
the paper prints `2.787` in the middle. PROVED, CONDITIONAL ON `S4_dyadic`, `J_props`,
`dyadic_sqrt_sum`, `dyadic_invsqrt_sum`, `block_bound` and its leaves, `term1_num` to
`term4_num`. -/
theorem lemma67 (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq : 2 ≤ q) (hqN : q ≤ N) :
    ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤
      0.2264 * N / √q * Real.log N ^ 2 + 2.81 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0785 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hU15, hV13, hUV, -, -, hN0⟩ := params_facts N hL
  have hU0 : 0 < Uf N := by linarith
  have hV0 : 0 < Vf N := lt_of_lt_of_le (Real.exp_pos _) hV13
  obtain ⟨hJV, hJ⟩ := J_props N (Uf N) (Vf N) hU0 hV0 hUV
  set J := Jn N (Uf N) (Vf N) with hJdef
  have hJ1 : 1 ≤ J := by rw [hJdef]; unfold Jn; omega
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set C := √(K67 * N) * Real.log (N / Vf N) with hC
  have hC0 : 0 ≤ C := by
    obtain ⟨-, -, -, -, h, -⟩ := params_facts N hL
    have : 1 ≤ (N : ℝ) / Vf N := by linarith
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg this)
  set a1 := √(5 * N / q)
  set b1 := √(N * Real.log q)
  set d1 := √(q * Real.log q)
  set lam := Real.log (N / (Uf N * Vf N)) / Real.log 2
  have hblk : ∀ j ∈ range J, ‖block c N (Uf N) (2 ^ j * Vf N) α‖ ≤
      C * (a1 + √5 * √(2 ^ j * Vf N) + b1 * (1 / √(2 ^ j * Vf N)) + d1) := by
    intro j hj
    have hjJ : j ≤ J - 1 := by rw [mem_range] at hj; omega
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ (J - 1) := pow_le_pow_right₀ (by norm_num) hjJ
    exact block_bound c N hL α a q hD hq hqN _ (by nlinarith)
      (le_trans (by nlinarith) hJV)
  have hS := S4_dyadic c N (Uf N) (Vf N) α hU0 hV0
  have hsum : ∑ j ∈ range J, C * (a1 + √5 * √(2 ^ j * Vf N) + b1 * (1 / √(2 ^ j * Vf N)) + d1) =
      C * (J * a1 + √5 * ∑ j ∈ range J, √(2 ^ j * Vf N) +
        b1 * ∑ j ∈ range J, 1 / √(2 ^ j * Vf N) + J * d1) := by
    rw [← mul_sum]
    congr 1
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hs1 := dyadic_sqrt_sum N (Uf N) (Vf N) hU0 hV0 J hJ1 hJV
  have hs2 := dyadic_invsqrt_sum (Vf N) hV0 J
  have ha1 : 0 ≤ a1 := Real.sqrt_nonneg _
  have hb1 : 0 ≤ b1 := Real.sqrt_nonneg _
  have hd1 : 0 ≤ d1 := Real.sqrt_nonneg _
  have hinner : J * a1 + √5 * ∑ j ∈ range J, √(2 ^ j * Vf N) +
      b1 * ∑ j ∈ range J, 1 / √(2 ^ j * Vf N) + J * d1 ≤
      (1 + lam) * a1 + √5 * ((2 + √2) * √(N / Uf N)) + b1 * ((2 + √2) / √(Vf N)) +
        (1 + lam) * d1 := by
    have := Real.sqrt_nonneg 5
    gcongr
  have t1 := term1_num N hL q (by omega)
  have t2 := term2_num N hL
  have t3 := term3_num N hL q (by omega) hqN
  have t4 := term4_num N hL q (by omega) hqN
  have hN45 : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by positivity
  calc ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖
      = ‖∑ j ∈ range J, block c N (Uf N) (2 ^ j * Vf N) α‖ := by rw [hS]
    _ ≤ ∑ j ∈ range J, ‖block c N (Uf N) (2 ^ j * Vf N) α‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J, C * (a1 + √5 * √(2 ^ j * Vf N) + b1 * (1 / √(2 ^ j * Vf N)) + d1) :=
        sum_le_sum hblk
    _ = _ := hsum
    _ ≤ C * ((1 + lam) * a1 + √5 * ((2 + √2) * √(N / Uf N)) + b1 * ((2 + √2) / √(Vf N)) +
        (1 + lam) * d1) := mul_le_mul_of_nonneg_left hinner hC0
    _ ≤ _ := by
        have e : C * ((1 + lam) * a1 + √5 * ((2 + √2) * √(N / Uf N)) +
            b1 * ((2 + √2) / √(Vf N)) + (1 + lam) * d1) =
            C * ((1 + lam) * a1) + C * (√5 * ((2 + √2) * √(N / Uf N))) +
            C * (b1 * ((2 + √2) / √(Vf N))) + C * ((1 + lam) * d1) := by ring
        rw [e]
        linarith

/-! ### Vacuity instances -/

/-- Vacuity: the hypotheses inside `SamePrimeAt 3` can all hold, with `m = 4`, `p = p' = 2`,
`i = k = 2`. PROVED. -/
theorem samePrime_hyps_hold :
    Nat.Prime 2 ∧ (3 : ℝ) < (2 : ℕ) ^ 2 ∧ 2 ^ 2 ∣ 4 ∧ 0 < 4 ∧ ((4 : ℕ) : ℝ) ≤ 3 ^ 2 := by
  refine ⟨Nat.prime_two, by norm_num, dvd_refl _, by norm_num, by norm_num⟩

/-- Vacuity: the hypotheses of `TailPow` can hold, `y = 1`, `i = 2`. PROVED. -/
theorem tailPow_hyps_hold : (1 : ℝ) ≤ 1 ∧ 2 ≤ 2 := ⟨le_rfl, le_rfl⟩

/-- Vacuity: the hypothesis `hM` of `W1_le` holds with `U = X = 1`, `a = 1`, `b = 0`. PROVED. -/
theorem W1_hyps_hold : ∀ x : ℝ, 1 ≤ x → x ≤ 1 →
    Real.log x - 1 ≤ primeLogSum x ∧ primeLogSum x ≤ Real.log x - 0 := by
  intro x h1 h2
  have hx : x = 1 := le_antisymm h2 h1
  subst hx
  have : primeLogSum 1 = 0 := by
    unfold primeLogSum primesTo
    rw [Nat.floor_one, show (range (1 + 1)).filter Nat.Prime = ∅ by decide, sum_empty]
  rw [this]
  norm_num

/-- Vacuity: `log N ≥ 3100`, the hypothesis of every numerical leaf, holds for
`N = ⌈e^3100⌉`. PROVED. -/
theorem logN_hyp_holds : (3100 : ℝ) ≤ Real.log (⌈exp 3100⌉₊ : ℕ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact Nat.le_ceil _

/-- A positive instance of the W identity on page 171. -/
theorem task141_nonzero_instance : Wsum 4 3 4 = Real.log 2 ^ 2 ∧ 4 * ppSum 3 4 = Real.log 2 ^ 2 ∧ 0 < Real.log 2 ^ 2 := by
  have ha : am 3 4 = Real.log 2 := by
    unfold am
    rw [show (4 : ℕ).divisors = {1, 2, 4} by decide]
    simp only [filter_insert, filter_singleton, Finset.mem_singleton]
    norm_num
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by decide), vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hr : lRange 4 3 4 = {4} := by
    norm_num [lRange, Finset.filter_insert, Finset.filter_singleton, show Icc 1 (4 : ℕ) = {1, 2, 3, 4} by decide]
  refine ⟨?_, ?_, ?_⟩
  · simp [Wsum, hr, ha]
  · norm_num [ppSum, primesTo, Finset.filter_insert, Finset.filter_singleton,
      show range 5 = {0, 1, 2, 3, 4} by decide, show Icc 1 (4 : ℕ) = {1, 2, 3, 4} by decide,
      Finset.sum_range_succ]
    ring
  · positivity

/-- A concrete simultaneous instance of the numerical hypotheses on pages 172 to 174. -/
theorem task141_numeric_hyps_hold : ∃ N : ℕ, 3100 ≤ Real.log N ∧ 2 ≤ N ∧
    1 ≤ (N : ℝ) / Vf N ∧ Uf N ≤ N / Vf N ∧ Vf N ≤ N / Uf N := by
  let N := ⌈exp 3100⌉₊
  have hL : 3100 ≤ Real.log N := logN_hyp_holds
  obtain ⟨hU15, hV13, hUV, hNVU, hUNV, hN⟩ := params_facts N hL
  have hU0 : 0 < Uf N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hN
  have hN2 : 2 ≤ N := by
    by_contra hn
    have he : N = 1 := by omega
    rw [he, Nat.cast_one, Real.log_one] at hL
    linarith
  refine ⟨N, hL, hN2, ?_, hUNV, ?_⟩
  · linarith
  · apply (le_div_iff₀ hU0).mpr
    nlinarith

end LeanLab.LiuWang2002.U1543
