import Mathlib
import LeanLab.Routes.R0018DiscreteCircle

/-!
# R-5220, T3 MOONSHOT: the absolute-value circle method at denominator `N` is pigeonhole

Unit U-6600, CLOUD 20261020T1618Z-cloud46. AI wrote this file.

Route: in the exact discrete circle method of R-0018, for `A, B ⊆ (0, N)`,
`N · #{(x, y) ∈ A × B : x + y = N} = |A||B| + Σ_{0 < a < N} S_A(a) S_B(a)`.
Any proof of `r(N) > 0` that bounds the nonzero frequencies by absolute values needs
`Σ_{a ≠ 0} |S_A(a)| |S_B(a)| < |A||B|`. This file shows what such certificates can reach:
* `error_le_abs`: the error term is at most `Σ_{a ≠ 0} |S_A(a)| |S_B(a)|`;
* `abs_le_cs`: by Cauchy-Schwarz and Parseval that sum is at most
  `√((N|A| - |A|²)(N|B| - |B|²))`;
* `cs_cert_iff`: this Cauchy-Schwarz certificate holds EXACTLY when `N < |A| + |B|`;
* `pigeonhole`: but `N ≤ |A| + |B|` already gives a pair with `x + y = N`, with no Fourier
  analysis at all, so `cs_cert_implies_pigeonhole`: the certificate never reaches beyond
  pigeonhole;
* `holder_self_ge`: for `A = B`, the Hölder form `max_{a ≠ 0} |S_A(a)| · Σ_{a ≠ 0} |S_A(a)|`
  is at least the Parseval mass `N|A| - |A|²`, so `holder_self_needs_half`: a sup times L¹
  certificate for `A + A` forces `N < 2|A|`, the pigeonhole range again;
* `abs_self_cert_iff`: for `A + A` the absolute-value sum IS the Parseval mass, so the
  certificate holds iff `N < 2|A|`. For `A ≠ B` the absolute sum can be far below the
  Cauchy-Schwarz bound, and numerically it is for the primes against the integers with no
  digit 7, Routes/numerics/r5220_U6600.out: there the certificate holds at `N = 10^6` with
  `|A| + |B| ≈ 0.61 N`, beyond pigeonhole.
For the primes below `N`, `|A| ≈ N / log N`, far below `N / 2`. So for the SYMMETRIC binary
problem `P + P`, every absolute-value method at denominator `N` stops at density `1/2`: a proof
must use the signs, the phases of `S(a/N)²`. Only an ASYMMETRIC pair, one set with tiny L¹ norm,
as Maynard's missing-digit sets, and the other with small sup on its support, can beat the
pigeonhole range; `P + P` has no such asymmetry.

KNOWN mathematics in substance: the L² barrier of the circle method, R-0001 and R-0018
`l2_barrier`, and the folklore that Fourier positivity by absolute values is no better than
counting. Nothing claimed new. A map entry, not progress on Goldbach, which is OPEN.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

open Finset Complex

namespace LeanLab.Routes.R5220

open LeanLab.Routes.R0018

/-- Exact identity for two sets: `Σ_{a < N} S_A(a) S_B(a) = N · #{x + y = N}`. -/
theorem pair_identity {N : ℕ} (hN : N ≠ 0) (A B : Finset ℕ)
    (hA : ∀ x ∈ A, 0 < x ∧ x < N) (hB : ∀ y ∈ B, 0 < y ∧ y < N) :
    ∑ a ∈ range N, S N A a * S N B a = (N : ℂ) * (pairCount N A B : ℂ) := by
  classical
  rw [pair_count_identity hN A B]
  congr 3
  refine Finset.filter_congr fun p hp => ?_
  rw [Finset.mem_product] at hp
  exact dvd_iff_eq (hA _ hp.1).1 (hA _ hp.1).2 (hB _ hp.2).1 (hB _ hp.2).2

/-- The error term against `|A||B|` is bounded by the nonzero frequencies in absolute value. -/
theorem error_le_abs {N : ℕ} (hN : N ≠ 0) (A B : Finset ℕ)
    (hA : ∀ x ∈ A, 0 < x ∧ x < N) (hB : ∀ y ∈ B, 0 < y ∧ y < N) :
    |(N : ℝ) * pairCount N A B - (A.card : ℝ) * B.card| ≤
      ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ * ‖S N B (a + 1)‖ := by
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hid := pair_identity hN A B hA hB
  have hsplit := Finset.sum_range_succ' (fun a => S N A a * S N B a) (N - 1)
  rw [Nat.sub_add_cancel hNpos] at hsplit
  rw [hsplit, S_zero, S_zero] at hid
  have hrest : (N : ℂ) * (pairCount N A B : ℂ) - (A.card : ℂ) * B.card =
      ∑ a ∈ range (N - 1), S N A (a + 1) * S N B (a + 1) := by
    rw [← hid]; ring
  have hnorm : ‖(N : ℂ) * (pairCount N A B : ℂ) - (A.card : ℂ) * B.card‖ ≤
      ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ * ‖S N B (a + 1)‖ := by
    rw [hrest]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_mul]
  have e : ((N : ℂ) * (pairCount N A B : ℂ) - (A.card : ℂ) * B.card) =
      (((N : ℝ) * pairCount N A B - (A.card : ℝ) * B.card : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm

/-- Parseval on the nonzero frequencies: `Σ_{0 < a < N} |S_A(a)|² = N|A| - |A|²`. -/
theorem parseval_nonzero {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ) (hA : ∀ x ∈ A, x < N) :
    ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ ^ 2 = (N : ℝ) * A.card - (A.card : ℝ) ^ 2 := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hpar := parseval_count hN A hA
  have hsplit := Finset.sum_range_succ' (fun a => ‖S N A a‖ ^ 2) (N - 1)
  rw [Nat.sub_add_cancel hNpos] at hsplit
  rw [hsplit, S_zero] at hpar
  simp only [Complex.norm_natCast] at hpar
  linarith

/-- **Cauchy-Schwarz plus Parseval.** -/
theorem abs_le_cs {N : ℕ} (hN : N ≠ 0) (A B : Finset ℕ)
    (hA : ∀ x ∈ A, x < N) (hB : ∀ y ∈ B, y < N) :
    ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ * ‖S N B (a + 1)‖ ≤
      √(((N : ℝ) * A.card - (A.card : ℝ) ^ 2) * ((N : ℝ) * B.card - (B.card : ℝ) ^ 2)) := by
  rw [← parseval_nonzero hN A hA, ← parseval_nonzero hN B hB]
  apply Real.le_sqrt_of_sq_le
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The Cauchy-Schwarz certificate holds exactly in the pigeonhole range.** For
`0 < a, b` and `0 < N`, `√((N a - a²)(N b - b²)) < a b ↔ N < a + b`. -/
theorem cs_cert_iff {N a b : ℝ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) (haN : a ≤ N)
    (hbN : b ≤ N) :
    √((N * a - a ^ 2) * (N * b - b ^ 2)) < a * b ↔ N < a + b := by
  have hfac : (N * a - a ^ 2) * (N * b - b ^ 2) = a * b * ((N - a) * (N - b)) := by ring
  have hnn : 0 ≤ (N * a - a ^ 2) * (N * b - b ^ 2) := by
    rw [hfac]; have := mul_nonneg (sub_nonneg.2 haN) (sub_nonneg.2 hbN); positivity
  have hab : 0 < a * b := mul_pos ha hb
  rw [Real.sqrt_lt' hab, hfac]
  constructor
  · intro h
    have h2 : (N - a) * (N - b) < a * b := by
      have : a * b * ((N - a) * (N - b)) < a * b * (a * b) := by nlinarith
      exact lt_of_mul_lt_mul_left this hab.le
    nlinarith
  · intro h
    have h2 : (N - a) * (N - b) < a * b := by nlinarith
    nlinarith

/-- **Pigeonhole.** For `A, B ⊆ (0, N)` with `N ≤ |A| + |B|`, some `x ∈ A`, `y ∈ B` have
`x + y = N`. -/
theorem pigeonhole {N : ℕ} (hN : 0 < N) (A B : Finset ℕ)
    (hA : ∀ x ∈ A, 0 < x ∧ x < N) (hB : ∀ y ∈ B, 0 < y ∧ y < N)
    (hcard : N ≤ A.card + B.card) : 0 < pairCount N A B := by
  classical
  set B' := B.image (fun y => N - y) with hB'
  have hinj : Set.InjOn (fun y => N - y) (B : Set ℕ) := by
    intro x hx y hy hxy
    have := hB x hx; have := hB y hy
    simp only at hxy; omega
  have hcB' : B'.card = B.card := Finset.card_image_of_injOn hinj
  have hsubA : A ⊆ Finset.Ioo 0 N := fun x hx => by
    rw [Finset.mem_Ioo]; exact hA x hx
  have hsubB : B' ⊆ Finset.Ioo 0 N := fun x hx => by
    rw [hB', Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hB y hy
    rw [Finset.mem_Ioo]; omega
  have hne : (A ∩ B').Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdisj : Disjoint A B' := Finset.disjoint_iff_inter_eq_empty.2 hemp
    have hu : (A ∪ B').card ≤ (Finset.Ioo 0 N).card :=
      Finset.card_le_card (Finset.union_subset hsubA hsubB)
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ioo, hcB'] at hu
    omega
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter, hB', Finset.mem_image] at hx
  obtain ⟨hxA, y, hyB, hyx⟩ := hx
  apply Finset.card_pos.2
  refine ⟨(x, y), ?_⟩
  rw [Finset.mem_filter, Finset.mem_product]
  have := hB y hyB
  exact ⟨⟨hxA, hyB⟩, by omega⟩

/-- **The certificate never beats pigeonhole.** If the Cauchy-Schwarz bound on the nonzero
frequencies is below the main term `|A||B|`, then already `N < |A| + |B|`, where pigeonhole
gives a pair without any Fourier analysis. -/
theorem cs_cert_implies_pigeonhole {N : ℕ} (hN : N ≠ 0) (A B : Finset ℕ)
    (hA : ∀ x ∈ A, 0 < x ∧ x < N) (hB : ∀ y ∈ B, 0 < y ∧ y < N)
    (hA0 : A.Nonempty) (hB0 : B.Nonempty)
    (hcert : √(((N : ℝ) * A.card - (A.card : ℝ) ^ 2) * ((N : ℝ) * B.card - (B.card : ℝ) ^ 2)) <
      (A.card : ℝ) * B.card) :
    N < A.card + B.card ∧ 0 < pairCount N A B := by
  have hAN : A.card ≤ N := by
    have : A ⊆ Finset.range N := fun x hx => Finset.mem_range.2 (hA x hx).2
    simpa using Finset.card_le_card this
  have hBN : B.card ≤ N := by
    have : B ⊆ Finset.range N := fun x hx => Finset.mem_range.2 (hB x hx).2
    simpa using Finset.card_le_card this
  have hlt : (N : ℝ) < A.card + B.card :=
    (cs_cert_iff (by exact_mod_cast Nat.pos_of_ne_zero hN)
      (by exact_mod_cast hA0.card_pos) (by exact_mod_cast hB0.card_pos)
      (by exact_mod_cast hAN) (by exact_mod_cast hBN)).1 hcert
  have hlt' : N < A.card + B.card := by exact_mod_cast hlt
  exact ⟨hlt', pigeonhole (Nat.pos_of_ne_zero hN) A B hA hB hlt'.le⟩

/-- **Hölder for `A + A`.** If `M` bounds every nonzero frequency, then
`M · Σ_{a ≠ 0} |S_A(a)| ≥ N|A| - |A|²`, the Parseval mass. -/
theorem holder_self_ge {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ) (hA : ∀ x ∈ A, x < N) {M : ℝ}
    (hM : ∀ a ∈ range (N - 1), ‖S N A (a + 1)‖ ≤ M) :
    (N : ℝ) * A.card - (A.card : ℝ) ^ 2 ≤ M * ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ := by
  rw [← parseval_nonzero hN A hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hM a ha) (norm_nonneg _)

/-- **A sup times L¹ certificate for `A + A` forces `N < 2|A|`.** -/
theorem holder_self_needs_half {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ)
    (hA : ∀ x ∈ A, 0 < x ∧ x < N) {M : ℝ}
    (hM : ∀ a ∈ range (N - 1), ‖S N A (a + 1)‖ ≤ M)
    (hcert : M * ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ < (A.card : ℝ) ^ 2) :
    N < 2 * A.card ∧ 0 < pairCount N A A := by
  have h := holder_self_ge hN A (fun x hx => (hA x hx).2) hM
  have hA0 : 0 < A.card := by
    rcases Nat.eq_zero_or_pos A.card with h0 | h0
    · rw [h0] at hcert
      have : 0 ≤ M * ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ := by
        have := holder_self_ge hN A (fun x hx => (hA x hx).2) hM
        rw [h0] at this; simpa using this
      push_cast at hcert; linarith
    · exact h0
  have hlt : (N : ℝ) * A.card < 2 * A.card * A.card := by nlinarith
  have hlt2 : (N : ℝ) < 2 * A.card :=
    lt_of_mul_lt_mul_right (by linarith) (by positivity : (0 : ℝ) ≤ A.card)
  have hlt' : N < 2 * A.card := by exact_mod_cast hlt2
  exact ⟨hlt', pigeonhole (Nat.pos_of_ne_zero hN) A A hA hA (by omega)⟩

/-- **For `A + A` the absolute-value certificate is exactly Parseval.** Since
`|S_A(a)| |S_A(a)| = |S_A(a)|²`, the triangle-inequality certificate for `A + A` holds iff
`N < 2|A|`, with no loss from Cauchy-Schwarz: the symmetric problem has no room at all. -/
theorem abs_self_cert_iff {N : ℕ} (hN : N ≠ 0) (A : Finset ℕ) (hA : ∀ x ∈ A, x < N)
    (hA0 : A.Nonempty) :
    ∑ a ∈ range (N - 1), ‖S N A (a + 1)‖ * ‖S N A (a + 1)‖ < (A.card : ℝ) * A.card ↔
      N < 2 * A.card := by
  have h := parseval_nonzero hN A hA
  simp_rw [← sq]
  rw [h]
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA0.card_pos
  constructor
  · intro hlt
    have : (N : ℝ) * A.card < 2 * A.card * A.card := by nlinarith
    have : (N : ℝ) < 2 * A.card := lt_of_mul_lt_mul_right (by linarith) hpos.le
    exact_mod_cast this
  · intro hlt
    have : (N : ℝ) < 2 * A.card := by exact_mod_cast hlt
    nlinarith

/-- Vacuity: the pigeonhole range is reached, `N = 10`, `A = B = {1, ..., 5}`. -/
example : 0 < pairCount 10 (Finset.Icc 1 5) (Finset.Icc 1 5) :=
  pigeonhole (by norm_num) _ _ (fun x hx => by simp at hx; omega) (fun x hx => by simp at hx; omega)
    (by decide)

/-- Vacuity of `cs_cert_iff` on both sides: `N = 10`, `a = b = 6` holds, `a = b = 5` fails. -/
example : √((10 * 6 - (6 : ℝ) ^ 2) * (10 * 6 - (6 : ℝ) ^ 2)) < 6 * 6 :=
  (cs_cert_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)

example : ¬ √((10 * 5 - (5 : ℝ) ^ 2) * (10 * 5 - (5 : ℝ) ^ 2)) < 5 * 5 := by
  rw [cs_cert_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The primes below 10 are far below half: `|A| = 4 < 5`, so no absolute-value certificate
exists at `N = 10`, though `r(10) = 3`. -/
example : 2 * ({2, 3, 5, 7} : Finset ℕ).card < 10 := by decide

end LeanLab.Routes.R5220
