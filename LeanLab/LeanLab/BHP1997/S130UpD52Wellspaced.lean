/-
P0069 Baker, Harman, Pintz 1997, pages 47 to 50, burst-20261122 session S130, tag
upD_lemma34_52-p3. Split of the two Lemma 33 case 5.13 LEAFs of the upD52 wave,
`upD52_leaf_lemma33_block` and `upD52_leaf_gs_pair_big`, one step further.

Page 47, the remarks before Lemma 33: for G = N M with Y^eps < N < Y^c1 and M satisfying 3.2,
Lemma 32 with j = 8 gives, through 5.10 to 5.12, the bound for one interval of length T2, and
"the contribution to M_j(G) from any interval [k T2, (k + 1) T2] is << Y T2^(-2) (k^2 + 1)^(-1)
L^(-A). Accordingly, (5.1) and (5.2) hold." Case 5.13 of Lemma 33 is exactly these remarks.

Here the step "accordingly 5.2 holds" is PROVED, uniformly in an index, as
`s130w_of_wellspaced_indexed`, by the same unit block and consecutive block summation as
`upD52_gbig_of_wellspaced` on main. What remains in each LEAF is the one interval bound, in the
well spaced form the lab already uses in `kept52_wellspaced` and `upD52_gbig_of_wellspaced`.

No new definition, no existing statement changed. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52BigBlocks
import LeanLab.BHP1997.Prep1122UpD52SmallStep

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- Helper lemma: the coefficient c x P m satisfies a divisor bound with exponent B + 2. -/
theorem s130w_c_divisor_bound {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x P k, c x P k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p) (p : ℝ)) :
    ∃ C' : ℝ, ∀ x P m, |(c x P m : ℝ)| ≤ C' * ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) := by
  obtain ⟨C, hC⟩ := ha
  have hC0 : 0 ≤ C := by
    have h := hC 0 1
    simp at h
    exact le_trans (abs_nonneg _) h
  use max 1 (C * 1)
  intro x P m
  have h₁ : c x P m = ∑ n ∈ m.divisors.filter (fun n : ℕ =>
      (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
    a x n * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
        ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
          (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
        (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
      upperRough (m / n / p) (p : ℝ) := by rw [hc x P m]
  rw [h₁]
  have h₂ : ∀ n ∈ m.divisors.filter (fun n : ℕ => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      |(a x n : ℝ)| ≤ C * ((m.divisors.card : ℕ) : ℝ) ^ B := by
    intro n hn
    have h₃ : n ∈ m.divisors := (Finset.mem_filter.mp hn).1
    have h₄ : |(a x n : ℝ)| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B := by exact_mod_cast hC x n
    have h₅ : (n.divisors.card : ℕ) ≤ m.divisors.card := by
      apply Finset.card_le_of_subset
      intro d hd
      have h₆ : d ∣ n := Nat.mem_divisors.mp hd
      have h₇ : n ∣ m := Nat.mem_divisors.mp h₃
      exact Nat.mem_divisors.mpr (dvd_trans h₆ h₇)
    have h₆ : ((n.divisors.card : ℕ) : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by exact_mod_cast h₅
    have h₇ : ((n.divisors.card : ℕ) : ℝ) ^ B ≤ ((m.divisors.card : ℕ) : ℝ) ^ B := by
      exact Real.rpow_le_rpow (by
        have : 1 ≤ (n.divisors.card : ℕ) := by
          apply Finset.card_pos.mpr
          exact ⟨1, by simp [Nat.mem_divisors, Nat.dvd_one]⟩
        exact_mod_cast this) h₆ B
    calc |(a x n : ℝ)| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B := h₄
      _ ≤ C * ((m.divisors.card : ℕ) : ℝ) ^ B := by gcongr
  have h₃ : ∀ n ∈ m.divisors.filter (fun n : ℕ => (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
      |(∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
            (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
        upperRough (m / n / p) (p : ℝ) : ℝ)| ≤ ((m.divisors.card : ℕ) : ℝ) := by
    intro n hn
    have h₄ : |(∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
        ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
          (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
      upperRough (m / n / p) (p : ℝ) : ℝ)| ≤
      ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
        ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
          (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
      |(upperRough (m / n / p) (p : ℝ) : ℝ)| := by
      calc
        _ ≤ ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          |(upperRough (m / n / p) (p : ℝ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by rfl
    have h₅ : ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
        ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
          (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
          (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
      |(upperRough (m / n / p) (p : ℝ) : ℝ)| ≤ ((m.divisors.card : ℕ) : ℝ) := by
      have h₆ : ∀ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
            (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
        |(upperRough (m / n / p) (p : ℝ) : ℝ)| ≤ 1 := by
        intro p hp
        have h₇ : 0 ≤ upperRough (m / n / p) (p : ℝ) := upperRough_nonneg _ _
        have h₈ : upperRough (m / n / p) (p : ℝ) ≤ 1 := by
          unfold upperRough
          split_ifs <;> norm_num
        rw [abs_of_nonneg h₇]
        exact by linarith
      calc
        _ ≤ ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)), (1 : ℝ) := Finset.sum_le_sum h₆
        _ = (((m / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P))).card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((m / n).primeFactors.card : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
        _ ≤ ((m.divisors.card : ℕ) : ℝ) := by
          have h₇ : (m / n).primeFactors.card ≤ m.divisors.card := by
            have h₈ : (m / n).primeFactors ⊆ m.divisors := by
              intro p hp
              simp only [Nat.mem_primeFactors, Nat.mem_divisors] at hp ⊢
              exact ⟨p.1, by
                have h₉ := hp.2.1
                have h₁₀ : p.1 ∣ m / n := h₉
                have h₁₁ : m / n ∣ m := Nat.div_dvd_of_dvd (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1)
                exact dvd_trans h₁₀ h₁₁⟩
            exact Finset.card_le_card h₈
          exact_mod_cast h₇
    calc
      _ ≤ ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
          ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
            (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
        |(upperRough (m / n / p) (p : ℝ) : ℝ)| := h₄
      _ ≤ ((m.divisors.card : ℕ) : ℝ) := h₅
  have h₄ : |(∑ n ∈ m.divisors.filter (fun n : ℕ =>
      (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
    (a x n : ℝ) * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
        ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
          (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
        (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
      upperRough (m / n / p) (p : ℝ))| ≤
    (max 1 (C * 1) : ℝ) * ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) := by
    calc
      _ ≤ ∑ n ∈ m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        |(a x n : ℝ) * ∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (m / n / p) (p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        (|(a x n : ℝ)| * |∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (m / n / p) (p : ℝ)|) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [abs_mul]
      _ ≤ ∑ n ∈ m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        (C * ((m.divisors.card : ℕ) : ℝ) ^ B * ((m.divisors.card : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        have h₅ := h₂ n hn
        have h₆ := h₃ n hn
        calc
          (|(a x n : ℝ)| * |∑ p ∈ (m / n).primeFactors.filter (fun p : ℕ =>
              ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
                (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
                (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
            upperRough (m / n / p) (p : ℝ)|) ≤ (C * ((m.divisors.card : ℕ) : ℝ) ^ B) * ((m.divisors.card : ℕ) : ℝ) := by
            gcongr <;> simp_all [abs_mul, abs_of_nonneg]
            <;> nlinarith
          _ = C * ((m.divisors.card : ℕ) : ℝ) ^ B * ((m.divisors.card : ℕ) : ℝ) := by rfl
      _ = ∑ n ∈ m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        (C * ((m.divisors.card : ℕ) : ℝ) ^ (B + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring_nf
        <;> field_simp [Real.rpow_add, Real.rpow_one] <;> ring_nf
        <;> simp_all [pow_succ]
        <;> field_simp [Real.rpow_add, Real.rpow_one] <;> ring_nf
      _ ≤ (m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).card • (C * ((m.divisors.card : ℕ) : ℝ) ^ (B + 1)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((m.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).card : ℝ) * (C * ((m.divisors.card : ℕ) : ℝ) ^ (B + 1)) := by
        simp [nsmul_eq_mul]
      _ ≤ ((m.divisors.card : ℕ) : ℝ) * (C * ((m.divisors.card : ℕ) : ℝ) ^ (B + 1)) := by
        have h₅ : (m.divisors.filter (fun n : ℕ =>
            (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).card ≤ m.divisors.card := by
          apply Finset.card_le_of_subset
          intro n hn
          exact Finset.mem_filter.mp hn |>.1
        have h₆ : 0 ≤ (C * ((m.divisors.card : ℕ) : ℝ) ^ (B + 1) : ℝ) := by positivity
        have h₇ : ((m.divisors.filter (fun n : ℕ =>
            (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε))).card : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by exact_mod_cast h₅
        nlinarith
      _ = C * ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) := by
        ring_nf
        <;> field_simp [Real.rpow_add, Real.rpow_one] <;> ring_nf
        <;> simp_all [pow_succ]
        <;> field_simp [Real.rpow_add, Real.rpow_one] <;> ring_nf
      _ ≤ (max 1 (C * 1) : ℝ) * ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) := by
        have h₅ : (C : ℝ) ≤ max 1 (C * 1) := by
          apply le_max_right
        have h₆ : 0 ≤ ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) := by positivity
        have h₇ : (C : ℝ) * ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) ≤ (max 1 (C * 1) : ℝ) * ((m.divisors.card : ℕ) : ℝ) ^ (B + 2) := by
          gcongr
        linarith
  simpa [abs_mul, abs_of_nonneg] using h₄

/-- P0069 page 47, the sentence "Accordingly, (5.1) and (5.2) hold" before Lemma 33, for 5.2 of
page 43 and the principal character, uniform in an index i ranging over the pairs with R x i:
a well spaced bound on every interval of length T2 in the range T0 <= |t| <= Y, with one
constant for all admissible i, gives 5.2 with one constant for all admissible i. PROVED, the
proof of `upD52_gbig_of_wellspaced` with the index carried along. -/
theorem s130w_of_wellspaced_indexed {ε : ℝ} {ι : Type*} (R : ℝ → ι → Prop)
    (c : ℝ → ι → ℕ → ℝ)
    (hws : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ i : ι, R x i →
      ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ i : ι, R x i →
      ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := hws A hA
  refine ⟨max (12 * max C 0) (max C 1), fun x hx i hi q hq1 hqQ => ?_⟩
  have hxC : C ≤ x := (le_max_left C 1).trans (hx.trans' (le_max_right _ _))
  have hx1 : 1 ≤ x := (le_max_right C 1).trans (hx.trans' (le_max_right _ _))
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  set Y := x ^ (11 / 20 + ε) with hYdef
  set T0 := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hT0def
  set T2 := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT2def
  set Lg := Real.log x ^ (-A) with hLg
  set F : ℝ → ℝ := fun t => ‖∑ m ∈ rightInterval ε x, (c x i m : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
    with hFdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 ≤ Lg := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hQ1 : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hqQ
  have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT2 : 0 < T2 := by rw [hT2def]; positivity
  have hT0 : 0 ≤ T0 := (Real.exp_pos _).le
  have hFc : Continuous F := kept52_continuous ε x q (c x i)
  have hF0 : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  set M := max C 0 with hM
  have hV : 0 ≤ 2 * (M * Y * Lg) := by positivity
  have hblock : ∀ a b : ℝ, a ≤ b → b - a ≤ T2 →
      ((T0 ≤ a ∧ b ≤ Y) ∨ (-Y ≤ a ∧ b ≤ -T0)) → ∫ t in a..b, F t ≤ 2 * (M * Y * Lg) := by
    intro a b hab hba hrange
    have h1 := kept52_block_le_two_wellspaced F hFc hF0 hab
      (hC x hxC i hi q hq1 hqQ a b hab hba hrange)
    have h2 : C * Y * Lg ≤ M * Y * Lg :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) hL0
    linarith
  have hpos : ∫ t in T0..Y, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
    kept52_block_sum F hFc hF0 hT0 hT2 hV fun a b ha hab hb hba =>
      hblock a b hab hba (Or.inl ⟨ha, hb⟩)
  have hneg : ∫ t in -Y..-T0, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 := by
    have hc := intervalIntegral.integral_comp_neg (a := T0) (b := Y)
      (fun t => F t / (T2 ^ 2 + t ^ 2))
    simp only [neg_sq] at hc
    rw [← hc]
    refine kept52_block_sum (fun t => F (-t)) (hFc.comp continuous_neg) (fun t => hF0 _)
      hT0 hT2 hV fun a b ha hab hb hba => ?_
    have hc2 := intervalIntegral.integral_comp_neg (a := a) (b := b) F
    rw [hc2]
    exact hblock (-b) (-a) (by linarith) (by linarith) (Or.inr ⟨by linarith, by linarith⟩)
  have hmain : 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 =
      12 * M * (Y / T2 ^ 2) * Lg := by ring
  have hfin : 12 * M * (Y / T2 ^ 2) * Lg ≤ max (12 * M) (max C 1) * (Y / T2 ^ 2) * Lg :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hL0
  calc _ ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
        add_le_add hneg hpos
    _ = 12 * M * (Y / T2 ^ 2) * Lg := hmain
    _ ≤ _ := hfin

/-- LEAF: P0069 pages 47 and 49 to 50, Lemma 33 case 5.13 for the block h_m of page 49, the one
interval bound of the remarks before Lemma 33: N(s, chi) the sum over P <= p1 < 2P,
Y^eps <= p1, of chi(p1) p1^(-s), satisfying 3.2 by Lemma 5, times the n and psi factor
satisfying 3.1; Lemma 32 with j = 8 and 5.10 to 5.12 bound the mean square over any well
spaced set S in one interval of length T2 = Y/(q Q) inside T0 <= |t| <= Y by Y L^(-A), with one
constant for all P with 1 <= P <= Y^c1. Principal character. CONDITIONAL on the cited Theorem 4
and Lemma 9. Class HARD. Same coefficient as `upD52_leaf_lemma33_block`, with its notes on the
boundary Y^eps of case 5.13 and on the coupling of n1 and p1 through psi(n1, p1). -/
theorem s130w_leaf_lemma33_block_wellspaced (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℕ → ℝ)
    (hc : ∀ x P k, c x P k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            ((Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)) ∧ (P ≤ p ∧ p < 2 * P)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ P : ℕ, 1 ≤ P →
      (P : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ u v : ℝ, u ≤ v → v - u ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ u ∧ v ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ u ∧ v ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, u ≤ t ∧ t ≤ v) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x P m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 pages 47 to 50, Lemma 33 case 5.13 for the block h_m, with the exact statement of
`upD52_leaf_lemma33_block`. PROVED from the LEAF `s130w_leaf_lemma33_block_wellspaced` by
`s130w_of_wellspaced_indexed`, indexed by P. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem s130w_lemma33_block : type_of% @upD52_leaf_lemma33_block := by
  intro h4 h9 ε hε hε8 a B ha c hc
  have key := s130w_of_wellspaced_indexed (ε := ε)
    (fun x (P : ℕ) => 1 ≤ P ∧ (P : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ upperC1 ε) c
    (fun A hA => by
      obtain ⟨C, hC⟩ := s130w_leaf_lemma33_block_wellspaced h4 h9 hε hε8 a ha c hc A hA
      exact ⟨C, fun x hx P hP => hC x hx P hP.1 hP.2⟩)
  intro A hA
  obtain ⟨C, hC⟩ := key A hA
  exact ⟨C, fun x hx P hP1 hP2 => hC x hx P ⟨hP1, hP2⟩⟩

/-- LEAF: P0069 pages 47 and 50, Lemma 33 case 5.13 for the pair part of the second Buchstab
step, the one interval bound of the remarks before Lemma 33: p1 p2 is the variable, of size
between Y^eps and Y^(2 eps) < Y^c1, its Dirichlet polynomial satisfying 3.2 by Lemma 5, the n
and psi factor satisfying 3.1; Lemma 32 with j = 8 and 5.10 to 5.12 bound the mean square over
any well spaced set S in one interval of length T2 = Y/(q Q) inside T0 <= |t| <= Y by Y L^(-A).
Principal character. Same coefficient as `upD52_leaf_gs_pair_big`. CONDITIONAL on the cited
Theorem 4 and Lemma 9. Class HARD. -/
theorem s130w_leaf_gs_pair_big_wellspaced (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            ¬ (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          ∑ p2 ∈ (k / n / p).primeFactors.filter (fun p2 : ℕ =>
              (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p2 : ℝ) ∧ (p2 : ℝ) < (p : ℝ)) ∧
              (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ) * (p2 : ℝ)),
            upperRough (k / n / p / p2) (p2 : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ u v : ℝ, u ≤ v → v - u ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ u ∧ v ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ u ∧ v ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, u ≤ t ∧ t ≤ v) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 50, the pair part with Y^eps <= p1 p2, with the exact statement of
`upD52_leaf_gs_pair_big`. PROVED from the LEAF `s130w_leaf_gs_pair_big_wellspaced` by
`upD52_gbig_of_wellspaced` of main. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem s130w_gs_pair_big : type_of% @upD52_leaf_gs_pair_big := by
  intro h4 h9 ε hε hε8 a B ha c hc
  exact upD52_gbig_of_wellspaced c
    (s130w_leaf_gs_pair_big_wellspaced h4 h9 hε hε8 a ha c hc)

end LeanLab.BHP1997.DecompC165d
