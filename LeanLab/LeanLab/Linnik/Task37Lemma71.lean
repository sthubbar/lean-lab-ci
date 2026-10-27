/-
Li and Liu, https://arxiv.org/pdf/2610.15784, page 21, proof of Lemma 7.1.
The two function reflection and Cauchy step before the asymptotic first moments.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Task37Fourier

namespace LeanLab.Linnik.Task37Lemma71
open Finset Real
open LeanLab.Linnik.U1434Lemma21
open LeanLab.Linnik.LiLiuDisplay37 (primesIn)

noncomputable def r5pp (N1 N L : ℕ) : ℝ :=
  ∑ p1 ∈ primesIn N1 N, ∑ p2 ∈ primesIn N1 N, ∑ ν : Fin 5 → Fin L,
    if p1 + p2 + ∑ i, 2 ^ ((ν i : ℕ) + 1) = N then Real.log p1 * Real.log p2 else 0

noncomputable def f2 (c : ℝ) (N1 N L n : ℕ) : ℝ :=
  rj 2 N1 N L n - c * L * rj 1 N1 N L n

lemma split5 (N L p1 p2 : ℕ) (x : ℝ) :
    (∑ ν : Fin 5 → Fin L, if p1 + p2 + ∑ i, 2 ^ ((ν i : ℕ) + 1) = N then x else 0) =
      ∑ ν1 : Fin 2 → Fin L, ∑ ν2 : Fin 3 → Fin L,
        if p1 + sv ν1 + (p2 + sv ν2) = N then x else 0 := by
  rw [← Fintype.sum_prod_type', ← (Fin.appendEquiv 2 3).sum_comp]
  refine Fintype.sum_congr _ _ fun ν => ?_
  have he : p1 + p2 + ∑ i, 2 ^ (((Fin.appendEquiv 2 3 ν) i : ℕ) + 1) =
      p1 + sv ν.1 + (p2 + sv ν.2) := by
    simp only [Fin.appendEquiv_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right, sv]
    ring
  rw [he]

/-- The ordered five power count is the convolution of the two and three power counts. -/
theorem r5pp_eq (N1 N L : ℕ) :
    r5pp N1 N L = ∑ n ∈ range (N + 1), rj 2 N1 N L n * rj 3 N1 N L (N - n) := by
  unfold r5pp
  simp_rw [split5]
  unfold rj
  simp_rw [sum_mul_sum]
  symm
  rw [sum_comm]
  refine sum_congr rfl fun p1 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun p2 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun ν1 _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun ν2 _ => ?_
  exact inner_sum _ _ _ _ _

/-- The reflection step for two different real functions, with arbitrary real weights. -/
theorem reflection {N : ℕ} (hN : Even N) (hN0 : 0 < N) (g h : ℕ → ℝ) (u v : ℝ) :
    (2 / N) * (u * ∑ n ∈ UN N, g n + v * ∑ n ∈ UN N, h n) ^ 2 -
      u ^ 2 * ∑ n ∈ UN N, g n ^ 2 - v ^ 2 * ∑ n ∈ UN N, h n ^ 2 ≤
        2 * u * v * ∑ n ∈ UN N, g n * h (N - n) := by
  have hn := Nat.even_iff.mp hN
  have hS : ∑ n ∈ UN N, (u * g n + v * h (N - n)) =
      u * ∑ n ∈ UN N, g n + v * ∑ n ∈ UN N, h n := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_UN_refl hn h]
  have hQ : ∑ n ∈ UN N, (u * g n + v * h (N - n)) ^ 2 =
      u ^ 2 * ∑ n ∈ UN N, g n ^ 2 + v ^ 2 * ∑ n ∈ UN N, h n ^ 2 +
        2 * u * v * ∑ n ∈ UN N, g n * h (N - n) := by
    have he (n : ℕ) : (u * g n + v * h (N - n)) ^ 2 =
        u ^ 2 * g n ^ 2 + v ^ 2 * h (N - n) ^ 2 + 2 * u * v * (g n * h (N - n)) := by ring
    simp_rw [he, sum_add_distrib, ← mul_sum, sum_UN_refl hn (fun n => h n ^ 2)]
  have hC := sq_sum_le_card_mul_sum_sq (s := UN N) (f := fun n => u * g n + v * h (N - n))
  have hnn : 0 ≤ ∑ n ∈ UN N, (u * g n + v * h (N - n)) ^ 2 :=
    sum_nonneg fun n _ => sq_nonneg _
  have hb := mul_le_mul_of_nonneg_right (card_UN N) hnn
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hd : (u * ∑ n ∈ UN N, g n + v * ∑ n ∈ UN N, h n) ^ 2 / N ≤
      (∑ n ∈ UN N, (u * g n + v * h (N - n)) ^ 2) / 2 := by
    rw [div_le_iff₀ hNr]
    rw [hS] at hC
    nlinarith
  rw [hQ] at hd
  have hd0 := (div_le_iff₀ hNr).mp hd
  have hd1 : (2 / N) * (u * ∑ n ∈ UN N, g n + v * ∑ n ∈ UN N, h n) ^ 2 ≤
      u ^ 2 * ∑ n ∈ UN N, g n ^ 2 + v ^ 2 * ∑ n ∈ UN N, h n ^ 2 +
        2 * u * v * ∑ n ∈ UN N, g n * h (N - n) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hNr]
    nlinarith
  linarith

lemma f2_positive_part_le {c : ℝ} (hc : 0 ≤ c) (N1 N L n : ℕ) :
    max (f2 c N1 N L n) 0 ≤ rj 2 N1 N L n := by
  have h1 := rj_nonneg 1 N1 N L n
  have h2 := rj_nonneg 2 N1 N L n
  have hp : 0 ≤ c * (L : ℝ) * rj 1 N1 N L n := by positivity
  unfold f2
  exact max_le (by linarith) h2

/-- The finite two function lower bound in the proof of Lemma 7.1. -/
theorem lemma71_finite {a b c τ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hτ : 0 < τ) (N1 N L : ℕ) (hN : Even N) (hN0 : 0 < N) (hL : 0 < L) :
    let g := fun n => max (f2 c N1 N L n) 0
    let h := fun n => max (ff a b N1 N L n) 0
    ((2 / N) * ((L : ℝ) * ∑ n ∈ UN N, g n + τ * ∑ n ∈ UN N, h n) ^ 2 -
      (L : ℝ) ^ 2 * ∑ n ∈ UN N, f2 c N1 N L n ^ 2 -
      τ ^ 2 * ∑ n ∈ UN N, ff a b N1 N L n ^ 2) / (2 * τ * L) ≤ r5pp N1 N L := by
  intro g h
  have hg : ∀ n, g n ≤ rj 2 N1 N L n := fun n => f2_positive_part_le hc N1 N L n
  have hh : ∀ n, h n ≤ rj 3 N1 N L n := fun n => g_le ha hb N1 N L n
  have hU : UN N ⊆ range (N + 1) := by
    intro n hn
    simp only [UN, mem_filter, mem_range] at hn ⊢
    omega
  have hconv : ∑ n ∈ UN N, g n * h (N - n) ≤ r5pp N1 N L := by
    rw [r5pp_eq]
    apply le_trans (sum_le_sum fun n _ =>
      mul_le_mul (hg n) (hh (N - n)) (le_max_right _ _) (rj_nonneg 2 N1 N L n))
    exact sum_le_sum_of_subset_of_nonneg hU fun n _ _ =>
      mul_nonneg (rj_nonneg 2 N1 N L n) (rj_nonneg 3 N1 N L (N - n))
  have hgsq : ∑ n ∈ UN N, g n ^ 2 ≤ ∑ n ∈ UN N, f2 c N1 N L n ^ 2 :=
    sum_le_sum fun n _ => g_sq_le _
  have hhsq : ∑ n ∈ UN N, h n ^ 2 ≤ ∑ n ∈ UN N, ff a b N1 N L n ^ 2 :=
    sum_le_sum fun n _ => g_sq_le _
  have hR := reflection hN hN0 g h (L : ℝ) τ
  have h1 := mul_le_mul_of_nonneg_left hgsq (sq_nonneg (L : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hhsq (sq_nonneg τ)
  have h3 := mul_le_mul_of_nonneg_left hconv (by positivity : 0 ≤ 2 * (L : ℝ) * τ)
  have hden : 0 < 2 * τ * (L : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- A concrete instance with positive weights and nonempty odd index set. -/
theorem reflection_instance :
    (2 / (8 : ℝ)) * (1 * ∑ _n ∈ UN 8, (1 : ℝ) + 1 * ∑ _n ∈ UN 8, (1 : ℝ)) ^ 2 -
      1 ^ 2 * ∑ _n ∈ UN 8, (1 : ℝ) ^ 2 - 1 ^ 2 * ∑ _n ∈ UN 8, (1 : ℝ) ^ 2 ≤
      2 * 1 * 1 * ∑ _n ∈ UN 8, (1 : ℝ) * 1 :=
  reflection (by decide) (by norm_num) (fun _ => 1) (fun _ => 1) 1 1

end LeanLab.Linnik.Task37Lemma71

#print axioms LeanLab.Linnik.Task37Lemma71.split5
#print axioms LeanLab.Linnik.Task37Lemma71.r5pp_eq
#print axioms LeanLab.Linnik.Task37Lemma71.reflection
#print axioms LeanLab.Linnik.Task37Lemma71.f2_positive_part_le
#print axioms LeanLab.Linnik.Task37Lemma71.lemma71_finite
#print axioms LeanLab.Linnik.Task37Lemma71.reflection_instance
