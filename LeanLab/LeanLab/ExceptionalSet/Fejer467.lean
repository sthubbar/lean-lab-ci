import LeanLab.ExceptionalSet.Decomp1539a
/-!
A finite Fejer argument for the auxiliary discrepancy split.
Source: P0082 page359, Lemma4. The paper omits the discrepancy proof.
These derived finite identities repair the power sum step of the formal split.
They do not supply the omitted discrepancy theorem.
AI wrote the Lean code. Goldbach is open.
-/
open Finset
open LeanLab.ExceptionalSet.U1539
namespace LeanLab.ExceptionalSet.Fejer467
set_option maxHeartbeats 400000

/-- P0082 page359 discrepancy auxiliary. Multiplication of exponential phases. -/
theorem phase_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- P0082 page359 discrepancy auxiliary. Subtraction of phases is conjugate multiplication. -/
theorem phase_sub (a b : ℝ) : eC (a - b) = eC a * (starRingEnd ℂ) (eC b) := by
  rw [sub_eq_add_neg, phase_add, eC_neg]

/-- P0082 page359 discrepancy auxiliary. Expanding a squared phase sum gives its pair correlations. -/
theorem norm_phase_sum_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ‖∑ i ∈ s, eC (x i)‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (eC (x i - x j)).re := by
  have hh : ((∑ i ∈ s, eC (x i)) * (starRingEnd ℂ) (∑ i ∈ s, eC (x i))).re =
      ‖∑ i ∈ s, eC (x i)‖ ^ 2 := by
    rw [Complex.mul_conj']
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← hh, map_sum, Finset.sum_mul_sum]
  change Complex.reCLM _ = _
  simp only [map_sum, Complex.reCLM_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [phase_sub]

/-- P0082 page359 discrepancy auxiliary. Interchanging the four finite sums gives the Gram duality identity. -/
theorem gram_duality {ι : Type*} (s : Finset ι) (x : ι → ℝ) (M : ℕ) :
    (∑ i ∈ s, ∑ j ∈ s,
      ‖∑ h ∈ range (M + 1), eC ((h : ℝ) * (x i - x j))‖ ^ 2) =
    ∑ h ∈ range (M + 1), ∑ k ∈ range (M + 1),
      ‖∑ i ∈ s, eC (((h : ℝ) - k) * x i)‖ ^ 2 := by
  simp_rw [norm_phase_sum_sq]
  conv_lhs =>
    arg 2; ext i
    rw [sum_comm]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_lhs =>
    arg 2; ext i
    rw [sum_comm]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  ring

/-- P0082 page359 discrepancy auxiliary. Every positive distance occurs at most twice in a finite row. -/
theorem difference_row_le (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d)
    (M h : ℕ) (hh : h ≤ M) :
    (∑ k ∈ range (M + 1), g (Nat.dist h k)) ≤
      g 0 + 2 * ∑ d ∈ Icc 1 M, g d := by
  let L := (range (M + 1)).filter (fun k => k < h)
  let R := (range (M + 1)).filter (fun k => h < k)
  have hl : (∑ k ∈ L, g (Nat.dist h k)) ≤ ∑ d ∈ Icc 1 M, g d := by
    apply sum_le_sum_of_injOn (fun k => h - k)
    · intro a ha b hb he
      change a ∈ L at ha
      change b ∈ L at hb
      dsimp at he
      simp only [L, mem_filter, mem_range] at ha hb
      omega
    · intro d hd
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hd
      simp only [L, mem_filter, mem_range] at hk
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k hk
      simp only [L, mem_filter, mem_range] at hk
      rw [Nat.dist_eq_sub_of_le_right (by omega : k ≤ h)]
    · intro d hd hnot
      exact hg d
  have hr : (∑ k ∈ R, g (Nat.dist h k)) ≤ ∑ d ∈ Icc 1 M, g d := by
    apply sum_le_sum_of_injOn (fun k => k - h)
    · intro a ha b hb he
      change a ∈ R at ha
      change b ∈ R at hb
      dsimp at he
      simp only [R, mem_filter, mem_range] at ha hb
      omega
    · intro d hd
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hd
      simp only [R, mem_filter, mem_range] at hk
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k hk
      simp only [R, mem_filter, mem_range] at hk
      rw [Nat.dist_eq_sub_of_le (by omega : h ≤ k)]
    · intro d hd hnot
      exact hg d
  have heach (k : ℕ) : g (Nat.dist h k) =
      (if k = h then g 0 else 0) +
      (if k < h then g (Nat.dist h k) else 0) +
      (if h < k then g (Nat.dist h k) else 0) := by
    rcases lt_trichotomy k h with hk | hk | hk
    · simp [hk, hk.ne, not_lt.mpr hk.le]
    · subst k
      simp [Nat.dist_self]
    · simp [hk, hk.ne', not_lt.mpr hk.le]
  have heq : (∑ k ∈ range (M + 1), g (Nat.dist h k)) =
      g 0 + (∑ k ∈ L, g (Nat.dist h k)) + ∑ k ∈ R, g (Nat.dist h k) := by
    conv_lhs => arg 2; ext k; rw [heach k]
    rw [sum_add_distrib, sum_add_distrib]
    simp only [sum_ite_eq', mem_range, show h < M + 1 by omega, ite_true]
    simp only [L, R, sum_filter]
  rw [heq]
  linarith

/-- P0082 page359 discrepancy auxiliary. Reversing the frequency conjugates the phase sum. -/
theorem phase_norm_neg {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ℝ) :
    ‖∑ i ∈ s, eC (-t * x i)‖ = ‖∑ i ∈ s, eC (t * x i)‖ := by
  have he : (∑ i ∈ s, eC (-t * x i)) =
      (starRingEnd ℂ) (∑ i ∈ s, eC (t * x i)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro i hi
    rw [← eC_neg]
    congr 1
    ring
  rw [he, Complex.norm_conj]

/-- P0082 page359 discrepancy auxiliary. The norm depends only on the absolute frequency difference. -/
theorem phase_norm_nat_diff {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h k : ℕ) :
    ‖∑ i ∈ s, eC (((h : ℝ) - k) * x i)‖ =
      ‖∑ i ∈ s, eC ((Nat.dist h k : ℕ) * x i)‖ := by
  rcases le_total h k with hh | hk
  · rw [Nat.dist_eq_sub_of_le hh, Nat.cast_sub hh]
    have he : (h : ℝ) - k = -((k : ℝ) - h) := by ring
    rw [he, phase_norm_neg]
  · rw [Nat.dist_eq_sub_of_le_right hk, Nat.cast_sub hk]

/-- P0082 page359 discrepancy auxiliary. Keeping the diagonal terms gives a lower bound for the nonnegative Gram energy. -/
theorem gram_diagonal_lower {ι : Type*} (s : Finset ι) (x : ι → ℝ) (M : ℕ) :
    (s.card : ℝ) * (M + 1) ^ 2 ≤
      ∑ i ∈ s, ∑ j ∈ s,
        ‖∑ h ∈ range (M + 1), eC ((h : ℝ) * (x i - x j))‖ ^ 2 := by
  classical
  calc
    _ = ∑ i ∈ s, (M + 1 : ℝ) ^ 2 := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      have hdiag : ‖∑ h ∈ range (M + 1), eC ((h : ℝ) * (x i - x i))‖ ^ 2 =
          (M + 1 : ℝ) ^ 2 := by
        have he : (∑ h ∈ range (M + 1), eC ((h : ℝ) * (x i - x i))) =
            ((M + 1 : ℕ) : ℂ) := by simp [eC]
        rw [he]
        norm_cast
      rw [← hdiag]
      exact single_le_sum (f := fun j => ‖∑ h ∈ range (M + 1), eC ((h : ℝ) * (x i - x j))‖ ^ 2)
        (fun j hj => sq_nonneg _) hi

/-- P0082 page359 discrepancy auxiliary. Nonnegative squared geometric sums give at least half the number of points in the first power sum second moment. This is a derived Fejer argument, not a statement printed in the paper. -/
theorem second_moment_lower {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (s.card : ℝ) / 2 ≤
      ∑ d ∈ Icc 1 s.card, ‖∑ i ∈ s, eC ((d : ℝ) * x i)‖ ^ 2 := by
  let M := s.card
  let g : ℕ → ℝ := fun d => ‖∑ i ∈ s, eC ((d : ℝ) * x i)‖ ^ 2
  have hg : ∀ d, 0 ≤ g d := fun d => sq_nonneg _
  have hz : g 0 = (M : ℝ) ^ 2 := by simp [g, eC, M]
  have hl := gram_diagonal_lower s x M
  rw [gram_duality] at hl
  have hu : (∑ h ∈ range (M + 1), ∑ k ∈ range (M + 1),
      ‖∑ i ∈ s, eC (((h : ℝ) - k) * x i)‖ ^ 2) ≤
        (M + 1 : ℝ) * ((M : ℝ) ^ 2 + 2 * ∑ d ∈ Icc 1 M, g d) := by
    calc
      _ = ∑ h ∈ range (M + 1), ∑ k ∈ range (M + 1), g (Nat.dist h k) := by
        simp_rw [phase_norm_nat_diff]
        rfl
      _ ≤ ∑ h ∈ range (M + 1), (g 0 + 2 * ∑ d ∈ Icc 1 M, g d) := by
        apply sum_le_sum
        intro h hh
        apply difference_row_le g hg M h
        have := mem_range.mp hh
        omega
      _ = _ := by simp [hz]; ring
  have hbound := hl.trans hu
  have hM : (s.card : ℝ) = M := rfl
  rw [hM] at hbound
  have hp : (0 : ℝ) < M + 1 := by positivity
  have hc : (M : ℝ) * (M + 1) ≤ (M : ℝ) ^ 2 + 2 * ∑ d ∈ Icc 1 M, g d := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hbound]
  change (M : ℝ) / 2 ≤ ∑ d ∈ Icc 1 M, g d
  nlinarith only [hc]

/-- P0082 page359 discrepancy auxiliary. Every exponential phase has norm one. -/
theorem phase_sum_norm_le_card {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ℝ) :
    ‖∑ i ∈ s, eC (t * x i)‖ ≤ s.card := by
  calc
    _ ≤ ∑ i ∈ s, ‖eC (t * x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_eC, sum_const, nsmul_eq_mul, mul_one]

/-- P0082 page359 discrepancy auxiliary. A finite second moment and the cardinality bound give a positive weighted power sum. -/
theorem weighted_phase_sum_lower {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ) (H : ℕ) (hH : s.card ≤ H) :
    1 ≤ 2 * ((s.card : ℝ) + 1) *
      ∑ d ∈ Icc 1 H, ‖∑ i ∈ s, eC ((d : ℝ) * x i)‖ / ((d : ℝ) + 1) := by
  let M := s.card
  let a : ℕ → ℝ := fun d => ‖∑ i ∈ s, eC ((d : ℝ) * x i)‖
  have hM : (0 : ℝ) < M := by exact_mod_cast hs.card_pos
  have ha (d : ℕ) : 0 ≤ a d := norm_nonneg _
  have hb (d : ℕ) : a d ≤ M := phase_sum_norm_le_card s x d
  have hl := second_moment_lower s x
  change (M : ℝ) / 2 ≤ ∑ d ∈ Icc 1 M, (a d) ^ 2 at hl
  have hsquare : (∑ d ∈ Icc 1 M, (a d) ^ 2) ≤ (M : ℝ) * ∑ d ∈ Icc 1 M, a d := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    nlinarith only [ha d, hb d]
  have hsum : (1 / 2 : ℝ) ≤ ∑ d ∈ Icc 1 M, a d := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [hl.trans hsquare]
  have hweight : (∑ d ∈ Icc 1 M, a d) ≤
      ((M : ℝ) + 1) * ∑ d ∈ Icc 1 M, a d / ((d : ℝ) + 1) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hdM : (d : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hd).2
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
    nlinarith only [ha d, hdM]
  have hmono : (∑ d ∈ Icc 1 M, a d / ((d : ℝ) + 1)) ≤
      ∑ d ∈ Icc 1 H, a d / ((d : ℝ) + 1) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rcases mem_Icc.mp hd with ⟨hd1, hdM⟩
      exact mem_Icc.mpr ⟨hd1, hdM.trans hH⟩
    · intro d hd hnot
      exact div_nonneg (ha d) (by positivity)
  have hweighted := hsum.trans (hweight.trans
    (mul_le_mul_of_nonneg_left hmono (by positivity)))
  change 1 ≤ 2 * ((M : ℝ) + 1) * ∑ d ∈ Icc 1 H, a d / ((d : ℝ) + 1)
  nlinarith only [hweighted]

/-- P0082 page359 discrepancy auxiliary. Exact supply for the open leaf_dirichlet_lower in SPLIT_leaf_fejer_majorant. The proof uses nonnegative Gram energy and does not use the false Dirichlet kernel lower bound in the old comment. -/
theorem dirichlet_lower_supplied (α γ : ℝ) (N H : ℕ) (hN : 1 ≤ N) (hH : N - N / 2 ≤ H) :
    1 ≤ (4 * (N : ℝ) - 2) * ∑ h ∈ Icc 1 H,
      ‖∑ n ∈ Ioc (N / 2) N, eC (h * α * LeanLab.ExceptionalSet.BrudernPerelli1998.F γ n)‖ /
        ((h : ℝ) + 1) := by
  let s := Ioc (N / 2) N
  let x := fun n : ℕ => α * LeanLab.ExceptionalSet.BrudernPerelli1998.F γ n
  have hcard : s.card = N - N / 2 := Nat.card_Ioc _ _
  have hs : s.Nonempty := by
    apply card_pos.mp
    rw [hcard]
    omega
  have he (h : ℕ) : (∑ n ∈ s, eC ((h : ℝ) * x n)) =
      ∑ n ∈ Ioc (N / 2) N, eC (h * α * LeanLab.ExceptionalSet.BrudernPerelli1998.F γ n) := by
    apply sum_congr rfl
    intro n hn
    dsimp [x]
    congr 1
    ring
  by_cases hN1 : N = 1
  · subst N
    have hH1 : 1 ≤ H := by simpa using hH
    have hsingle : (1 / 2 : ℝ) ≤ ∑ h ∈ Icc 1 H,
        ‖∑ n ∈ Ioc (1 / 2 : ℕ) 1,
          eC (h * α * LeanLab.ExceptionalSet.BrudernPerelli1998.F γ n)‖ / ((h : ℝ) + 1) := by
      have hh := single_le_sum (s := Icc 1 H)
        (f := fun h : ℕ => ‖∑ n ∈ Ioc (1 / 2 : ℕ) 1,
          eC (h * α * LeanLab.ExceptionalSet.BrudernPerelli1998.F γ n)‖ / ((h : ℝ) + 1))
        (fun h hh => by positivity) (mem_Icc.mpr ⟨le_refl 1, hH1⟩)
      norm_num [norm_eC] at hh ⊢
      exact hh
    norm_num [norm_eC] at hsingle ⊢
    linarith
  · have hl := weighted_phase_sum_lower s hs x H (by omega)
    simp_rw [he] at hl
    have hc : 2 * ((s.card : ℝ) + 1) ≤ 4 * (N : ℝ) - 2 := by
      rw [hcard]
      have hn2 : 2 ≤ N := by omega
      have hM : (N - N / 2 : ℕ) ≤ N := Nat.sub_le _ _
      have hr : (N - N / 2 : ℕ) + 2 ≤ 2 * N := by omega
      have hrreal : ((N - N / 2 : ℕ) : ℝ) + 2 ≤ 2 * (N : ℝ) := by exact_mod_cast hr
      linarith only [hrreal]
    have hw : 0 ≤ ∑ h ∈ Icc 1 H,
        ‖∑ n ∈ Ioc (N / 2) N,
          eC (h * α * LeanLab.ExceptionalSet.BrudernPerelli1998.F γ n)‖ / ((h : ℝ) + 1) :=
      sum_nonneg (fun h hh => by positivity)
    exact hl.trans (mul_le_mul_of_nonneg_right hc hw)
/-- P0082 page359 discrepancy auxiliary audit. The unweighted two term
cosine kernel in the old formal hint takes the value minus nine eighths.
This is a counterexample to that hint, not to the paper or to the proved leaf. -/
theorem cosine_kernel_counterexample :
    Real.cos (Real.arccos (-(1 / 4 : ℝ))) +
      Real.cos (2 * Real.arccos (-(1 / 4 : ℝ))) = -(9 / 8 : ℝ) := by
  rw [Real.cos_two_mul, Real.cos_arccos (by norm_num) (by norm_num)]
  norm_num

/-- P0082 page359 discrepancy auxiliary audit. The kernel lower bound
proposed in the original leaf comment is false. The supplied leaf proof is independent. -/
theorem not_cosine_kernel_lower :
    ¬ (∀ x : ℝ, -1 ≤ Real.cos x + Real.cos (2 * x)) := by
  intro h
  have hc := h (Real.arccos (-(1 / 4 : ℝ)))
  rw [cosine_kernel_counterexample] at hc
  norm_num at hc

end LeanLab.ExceptionalSet.Fejer467
