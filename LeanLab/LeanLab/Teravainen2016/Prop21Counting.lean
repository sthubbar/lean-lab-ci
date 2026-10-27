/-
P0076, Proposition 2.1, page 7, displays 2.3 and 2.4.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.NaturalConvolution

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The middle half interval is usable for every target in the final tenth. -/
theorem middle_difference {N n k : ℕ} (hN : 0 < N) (hn : n ≤ N) (h9 : 9 * N ≤ 10 * n)
    (hk1 : (N : ℝ) / 3 < k) (hk2 : (k : ℝ) < N / 2) :
    k ≤ n ∧ n - k < N ∧ (N : ℝ) / 3 < (n - k : ℕ) ∧
      ((n - k : ℕ) : ℝ) < 2 * N / 3 ∧ (n + N - k) % N = n - k := by
  have h9r : (9 : ℝ) * N ≤ 10 * n := by exact_mod_cast h9
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkn : k ≤ n := by
    have : (k : ℝ) < n := by linarith
    exact_mod_cast this.le
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hdiff : n - k < N := by omega
  refine ⟨hkn, hdiff, ?_, ?_, ?_⟩
  · rw [Nat.cast_sub hkn]
    linarith
  · rw [Nat.cast_sub hkn]
    linarith
  · have he : n + N - k = n - k + N := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hdiff]

/-- Display 2.3: a nonnegative smooth factor bounded below by delta in the middle
produces convolution at least delta squared on the final tenth. -/
theorem conv_smooth_lower {N : ℕ} (hN : 0 < N) (f g : ℕ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hgl : ∀ k : ℕ, (N : ℝ) / 3 < k → (k : ℝ) < 2 * N / 3 → δ ≤ g k)
    (hmass : δ * N ≤ ∑ k ∈ (range N).filter
      (fun k : ℕ => (N : ℝ) / 3 < k ∧ (k : ℝ) < N / 2), f k)
    {n : ℕ} (hn : n ≤ N) (h9 : 9 * N ≤ 10 * n) : δ ^ 2 ≤ conv N f g n := by
  let S := (range N).filter (fun k : ℕ => (N : ℝ) / 3 < k ∧ (k : ℝ) < N / 2)
  have hsum : δ * ∑ k ∈ S, f k ≤ ∑ k ∈ range N, f k * g ((n + N - k) % N) := by
    calc
      _ = ∑ k ∈ S, δ * f k := mul_sum _ _ _
      _ ≤ ∑ k ∈ S, f k * g ((n + N - k) % N) := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hkN, hk1, hk2⟩ := mem_filter.mp hk
        obtain ⟨_, _, hd1, hd2, he⟩ := middle_difference hN hn h9 hk1 hk2
        rw [he]
        nlinarith [hgl (n - k) hd1 hd2, hf k]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by
        intro k _ _
        exact mul_nonneg (hf k) (hg _))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold conv
  rw [inv_mul_eq_div, le_div_iff₀ hNr]
  have hh := mul_le_mul_of_nonneg_left hmass hδ.le
  nlinarith

/-- The natural convolution is periodic in its output variable. -/
theorem conv_mod (N : ℕ) [NeZero N] (f g : ℕ → ℝ) (n : ℕ) :
    conv N f g (n % N) = conv N f g n := by
  apply Complex.ofReal_injective
  rw [conv_eq_cyclicConv, conv_eq_cyclicConv]
  simp

/-- The mean square error controls the exceptional count, including the endpoint N. -/
theorem prop21_bad_count {N : ℕ} (hN : 0 < N) (f₁ f₂ g₂ : ℕ → ℝ) {δ ε : ℝ}
    (hδ : 0 < δ)
    (hmain : ∀ n ≤ N, 9 * N ≤ 10 * n → δ ^ 2 ≤ conv N f₁ g₂ n)
    (henergy : (N : ℝ)⁻¹ * ∑ n ∈ range N, (conv N f₁ (fun k => f₂ k - g₂ k) n) ^ 2 ≤
      δ ^ 4 * ε / 10) :
    (#{n ∈ Icc 0 N | 9 * N ≤ 10 * n ∧ conv N f₁ f₂ n < δ ^ 2 / 3} : ℝ) ≤ ε * N := by
  letI : NeZero N := ⟨hN.ne'⟩
  let T := {n ∈ Icc 0 N | 9 * N ≤ 10 * n ∧ conv N f₁ f₂ n < δ ^ 2 / 3}
  let E := fun n => conv N f₁ (fun k => f₂ k - g₂ k) n
  have hinj : Set.InjOn (fun n => n % N) (T : Set ℕ) := by
    intro n hn m hm he
    change n % N = m % N at he
    have hn' := mem_filter.mp hn
    have hm' := mem_filter.mp hm
    have hnN := (mem_Icc.mp hn'.1).2
    have hmN := (mem_Icc.mp hm'.1).2
    have hn0 : 0 < n := by omega
    have hm0 : 0 < m := by omega
    by_cases hnEq : n = N
    · subst n
      simp only [Nat.mod_self] at he
      by_cases hmEq : m = N
      · exact hmEq.symm
      · rw [Nat.mod_eq_of_lt (by omega)] at he
        omega
    · rw [Nat.mod_eq_of_lt (by omega)] at he
      by_cases hmEq : m = N
      · subst m
        simp only [Nat.mod_self] at he
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at he
        exact he
  have hp : ∀ n ∈ T, δ ^ 4 / 10 ≤ E (n % N) ^ 2 := by
    intro n hn
    obtain ⟨hnI, hn9, hbad⟩ := mem_filter.mp hn
    have hl := hmain n (mem_Icc.mp hnI).2 hn9
    have he : E (n % N) = conv N f₁ f₂ n - conv N f₁ g₂ n := by
      dsimp [E]
      rw [conv_mod, conv_sub_right]
    rw [he]
    have hd : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hh : 2 * δ ^ 2 / 3 ≤ -(conv N f₁ f₂ n - conv N f₁ g₂ n) := by linarith
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ 2 * δ ^ 2 / 3) hh
    nlinarith [sq_nonneg (conv N f₁ f₂ n - conv N f₁ g₂ n)]
  have htotal : (#T : ℝ) * (δ ^ 4 / 10) ≤ ∑ n ∈ range N, E n ^ 2 := by
    calc
      _ = ∑ n ∈ T, δ ^ 4 / 10 := by simp
      _ ≤ ∑ n ∈ T, E (n % N) ^ 2 := sum_le_sum hp
      _ = ∑ m ∈ T.image (fun n => n % N), E m ^ 2 := (sum_image (f := fun m => E m ^ 2) hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
        intro m hm
        obtain ⟨n, _, rfl⟩ := mem_image.mp hm
        exact mem_range.mpr (Nat.mod_lt _ hN)) (by intro _ _ _; positivity)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [inv_mul_eq_div, div_le_iff₀ hNr] at henergy
  have hd : 0 < δ ^ 4 / 10 := by positivity
  change (#T : ℝ) ≤ ε * N
  apply (mul_le_mul_iff_of_pos_right hd).mp
  nlinarith

#print axioms middle_difference
#print axioms conv_smooth_lower
#print axioms conv_mod
#print axioms prop21_bad_count

end LeanLab.Teravainen2016
