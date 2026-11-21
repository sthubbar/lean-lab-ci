/-
Prove2Me port, mission 504a8119.
Theorem LL_Decomp1543c.wc_lemma3.
Author kmehltretter82. License Apache 2.0.
Accepted submission bb7e71c5-a5ed-48f3-b6c5-568b523c390c, 2026-11-19.
Theorem id 4d14178b-f61f-44c7-984d-efc77d7e0c38.
Source https://beta.prove2.me . Raw closure pulled 2026-11-20.
Port from Lean 4.33.1 to Lean 4.35 by CODEX task667.
Uses the sealed lab definitions without replacement definitions.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ported.Prove2Me.LL_Decomp1543c_Core
import LeanLab.LiuWang2002.WC3Definition667

namespace LeanLab.Ported.Prove2Me.Task667
open Real Finset ArithmeticFunction LeanLab.LiuWang2002.U1543

theorem wc_lemma3 : WCLemma3 := by
  intro α a q hD hq15 X Y hX hY
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
  have hlogX_nn : 0 ≤ Real.log X := Real.log_nonneg hX
  set M := ⌊X⌋₊
  set m₀ := q / 2
  by_cases hM : M ≤ m₀
  · have h1 := first_half_bound α a q hD hq15 Y hY M hM
    have hX_term : 0 ≤ X * Real.log (q : ℝ) := by positivity
    have hY_term : 0 ≤ 5 * Y / (q : ℝ) * Real.log X := by positivity
    nlinarith
  · push Not at hM
    have hsplit : ∑ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ)) =
        ∑ n ∈ Icc 1 m₀, minK (Y / (n : ℝ)) (α * (n : ℝ)) +
          ∑ n ∈ Icc (m₀ + 1) M, minK (Y / (n : ℝ)) (α * (n : ℝ)) := by
      have hdisj : Disjoint (Icc 1 m₀) (Icc (m₀ + 1) M) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [mem_Icc] at hx1 hx2; omega
      have hunion : Icc 1 m₀ ∪ Icc (m₀ + 1) M = Icc 1 M := by
        ext x; simp only [mem_union, mem_Icc]; omega
      rw [← Finset.sum_union hdisj, hunion]
    have hfirst := first_half_bound α a q hD hq15 Y hY m₀ le_rfl
    set K : ℕ := (M - m₀ - 1) / q
    let B : ℕ → Finset ℕ := fun k => Icc (m₀ + 1 + k * q) (min M (m₀ + (k + 1) * q))
    have htail_eq : ∑ n ∈ Icc (m₀ + 1) M, minK (Y / (n : ℝ)) (α * (n : ℝ)) =
        ∑ k ∈ range (K + 1), ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) := by
      have hdisj : Set.PairwiseDisjoint (↑(range (K + 1)) : Set ℕ) B := by
        intro k₁ _ k₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro n hn₁ hn₂
        simp only [B, mem_Icc] at hn₁ hn₂
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : (k₁ + 1) * q ≤ k₂ * q := Nat.mul_le_mul_right q (by omega)
          omega
        · have : (k₂ + 1) * q ≤ k₁ * q := Nat.mul_le_mul_right q (by omega)
          omega
      have hbi : (range (K + 1)).biUnion B = Icc (m₀ + 1) M := by
        ext n
        simp only [mem_biUnion, mem_range, B, mem_Icc]
        constructor
        · rintro ⟨k, _, h1, h2⟩; omega
        · intro ⟨h1, h2⟩
          refine ⟨(n - m₀ - 1) / q, ?_, ?_, ?_⟩
          · have : (n - m₀ - 1) / q ≤ (M - m₀ - 1) / q := Nat.div_le_div_right (by omega)
            omega
          · have : (n - m₀ - 1) / q * q ≤ n - m₀ - 1 := Nat.div_mul_le_self _ _
            omega
          · have : n - m₀ - 1 < ((n - m₀ - 1) / q + 1) * q := by
              have := Nat.lt_div_mul_add (a := n - m₀ - 1) (b := q) (by omega)
              linarith
            omega
      rw [← hbi, Finset.sum_biUnion hdisj]
    have hblock : ∀ k ∈ range (K + 1),
        ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
          3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) + (q : ℝ) * Real.log (q : ℝ) := by
      intro k _
      set Xk : ℝ := Y / (((k : ℝ) + 1 / 2) * (q : ℝ))
      have hXk_pos : 0 < Xk := by dsimp [Xk]; positivity
      have hmono : ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
          ∑ n ∈ B k, minK Xk (α * (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [B, mem_Icc] at hn
        apply minK_mono_left
        apply div_le_div_of_nonneg_left (le_of_lt hY) (by positivity)
        have hm0_ge : (q : ℝ) / 2 < (m₀ : ℝ) + 1 := by
          have : q < 2 * (m₀ + 1) := by omega
          have : (q : ℝ) < 2 * ((m₀ : ℝ) + 1) := by exact_mod_cast this
          linarith
        have hn_ge : ((m₀ + 1 + k * q : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
        push_cast at hn_ge
        linarith
      set S : Finset ℤ := (B k).image (fun n : ℕ => (n : ℤ))
      have hsum_Z : ∑ n ∈ B k, minK Xk (α * (n : ℝ)) =
          ∑ z ∈ S, minK Xk (α * (z : ℝ)) := by
        symm
        dsimp [S]
        rw [Finset.sum_image (f := fun z : ℤ => minK Xk (α * (z : ℝ)))
          (g := fun n : ℕ => (n : ℤ)) (fun x _ y _ h => Int.ofNat.inj h)]
        refine Finset.sum_congr rfl fun n _ => by push_cast; rfl
      have hS_range : ∀ z ∈ S,
          ((m₀ + 1 + k * q : ℕ) : ℤ) ≤ z ∧ z < ((m₀ + 1 + k * q : ℕ) : ℤ) + (q : ℤ) := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
        simp only [B, mem_Icc] at hn
        have hmul : (k + 1) * q = k * q + q := by ring
        have hle2 : n ≤ m₀ + k * q + q := by
          have := le_trans hn.2 (Nat.min_le_right _ _)
          omega
        constructor <;> omega
      have hblk := block_minK_bound α a q hD Xk hXk_pos ((m₀ + 1 + k * q : ℕ) : ℤ) S hS_range
      linarith
    have htail_le : ∑ k ∈ range (K + 1), ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
        ∑ k ∈ range (K + 1), (3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) + (q : ℝ) * Real.log (q : ℝ)) :=
      Finset.sum_le_sum hblock
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htail_le
    have hKnat : K * q + m₀ + 1 ≤ M := by
      have hKmul : K * q ≤ M - m₀ - 1 := Nat.div_mul_le_self _ _
      omega
    have hKreal : (K : ℝ) * (q : ℝ) + (m₀ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hKnat
    have hMX : (M : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hKq : ((K + 1 : ℕ) : ℝ) * (q : ℝ) ≤ X + 0.5 * (q : ℝ) := by
      have hm0_ge : (q : ℝ) - 1 ≤ 2 * (m₀ : ℝ) := by
        have : q - 1 ≤ 2 * m₀ := by omega
        have hq1' : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1]; simp
        rw [← hq1']; exact_mod_cast this
      push_cast; linarith
    have hlogq_sum : ((K + 1 : ℕ) : ℝ) * ((q : ℝ) * Real.log (q : ℝ)) ≤
        X * Real.log (q : ℝ) + 0.5 * (q : ℝ) * Real.log (q : ℝ) := by
      calc ((K + 1 : ℕ) : ℝ) * ((q : ℝ) * Real.log (q : ℝ))
          = (((K + 1 : ℕ) : ℝ) * (q : ℝ)) * Real.log (q : ℝ) := by ring
        _ ≤ (X + 0.5 * (q : ℝ)) * Real.log (q : ℝ) :=
            mul_le_mul_of_nonneg_right hKq hlogq_nn
        _ = X * Real.log (q : ℝ) + 0.5 * (q : ℝ) * Real.log (q : ℝ) := by ring
    have hY_eq : ∑ k ∈ range (K + 1), 3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) =
        (Y / (q : ℝ)) * (3 * (2 * ∑ r ∈ Icc 1 (K + 1), (1 : ℝ) / (2 * (r : ℝ) - 1))) := by
      have hshift : ∑ k ∈ range (K + 1), 3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) =
          ∑ r ∈ Icc 1 (K + 1), (Y / (q : ℝ)) * (6 / (2 * (r : ℝ) - 1)) := by
        refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [mem_range, mem_Icc] at hk ⊢; omega
        · intro k₁ _ k₂ _ h; omega
        · intro r hr
          simp only [mem_Icc] at hr
          refine ⟨r - 1, ?_, by omega⟩
          simp only [mem_range]; omega
        · intro k _
          push_cast
          have hne : (2 * ((k : ℝ) + 1) - 1) ≠ 0 := by linarith
          have hne' : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
          field_simp; ring
      rw [hshift, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hoddK := odd_harmonic_bound (K + 1) (Nat.succ_pos K)
    have hX_lb : (2 * ((K + 1 : ℕ) : ℝ) - 1) * 7.5 ≤ X := by
      have hm0_ge : (q : ℝ) / 2 < (m₀ : ℝ) + 1 := by
        have : q < 2 * (m₀ + 1) := by omega
        have : (q : ℝ) < 2 * ((m₀ : ℝ) + 1) := by exact_mod_cast this
        linarith
      have hq15r : (15 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq15
      push_cast
      nlinarith
    have hlog75 : (2 : ℝ) ≤ Real.log 7.5 := by
      have hexp2 : Real.exp 2 ≤ (7.5 : ℝ) := by
        have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [h2]
        calc (Real.exp 1) ^ 2 ≤ (2.72 : ℝ) ^ 2 := by gcongr; exact le_of_lt exp_one_lt_272
          _ ≤ (7.5 : ℝ) := by norm_num
      have := Real.log_le_log (Real.exp_pos _) hexp2
      rwa [Real.log_exp] at this
    have h2K_pos : (0 : ℝ) < 2 * ((K + 1 : ℕ) : ℝ) - 1 := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
    have hlogX_lb : Real.log (2 * ((K + 1 : ℕ) : ℝ) - 1) + 2 ≤ Real.log X := by
      have h1 := Real.log_le_log (by positivity) hX_lb
      rw [Real.log_mul (ne_of_gt h2K_pos) (by norm_num)] at h1
      linarith
    have hlog2K_nn : 0 ≤ Real.log (2 * ((K + 1 : ℕ) : ℝ) - 1) := by
      apply Real.log_nonneg; push_cast; linarith
    have hY_bound : ∑ k ∈ range (K + 1), 3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) ≤
        5 * Y / (q : ℝ) * Real.log X := by
      rw [hY_eq]
      have hcoef : 3 * (2 * ∑ r ∈ Icc 1 (K + 1), (1 : ℝ) / (2 * (r : ℝ) - 1)) ≤ 5 * Real.log X := by
        linarith
      calc (Y / (q : ℝ)) * (3 * (2 * ∑ r ∈ Icc 1 (K + 1), (1 : ℝ) / (2 * (r : ℝ) - 1)))
          ≤ (Y / (q : ℝ)) * (5 * Real.log X) :=
            mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = 5 * Y / (q : ℝ) * Real.log X := by ring
    linarith

#print axioms wc_lemma3

end LeanLab.Ported.Prove2Me.Task667
