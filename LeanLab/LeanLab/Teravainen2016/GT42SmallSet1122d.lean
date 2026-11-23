/-
P0076, Proposition 4.2, pages 13 to 14, via Green and Tao, Restriction theory of the Selberg
sieve, arXiv math/0405581, proof of Proposition 4.1, display 4.2 for a small set B, pages 10
to 12. Split of the LEAF LevelSet1122b.gt42_small_set: the passage from the capped weight to the
uncapped sieve, the expansion of the square into a double sum over pairs x, y in B with the
triangle inequality, and the insertion of the Fourier expansion of EnvelopingFourierBounds
with the coefficient bound are proved here. The pointwise bound of one exponential kernel is
proved, as is the error of the transported value at n equal to 0; the remaining LEAF is the
main part of the pair count over B against the weights q^(eps/2 - 1), HARD. burst-20261122 step gt42_small_set1122d.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.LevelSetLarge1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.GT42SmallSet1122d

open LeanLab.Teravainen2016

/-- Green and Tao page 10, the additive character as a unit exponential. -/
theorem gt42d_eC_eq_exp (t : ℝ) : eC t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
  unfold eC; congr 1; push_cast; ring

/-- Green and Tao page 10, the additive character has norm one. -/
theorem gt42d_norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  rw [gt42d_eC_eq_exp, mul_comm, Complex.norm_exp_ofReal_mul_I]

theorem gt42d_four_le_norm_eC_sub_one {t : ℝ} (ht : |t| ≤ 1 / 2) : 4 * |t| ≤ ‖eC t - 1‖ := by
  rw [gt42d_eC_eq_exp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hπ := Real.pi_pos
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢
    have hs := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith)
    have he : 2 * Real.pi * t / 2 = Real.pi * t := by ring
    rw [he]
    have : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rw [this] at hs
    have := le_abs_self (Real.sin (Real.pi * t))
    linarith
  · rw [abs_of_nonpos h0] at ht ⊢
    have hs := Real.mul_le_sin (x := Real.pi * (-t)) (by nlinarith) (by nlinarith)
    have he : 2 * Real.pi * t / 2 = -(Real.pi * (-t)) := by ring
    rw [he, Real.sin_neg, abs_neg]
    have : 2 / Real.pi * (Real.pi * (-t)) = 2 * (-t) := by field_simp
    rw [this] at hs
    have := le_abs_self (Real.sin (Real.pi * (-t)))
    linarith

/-- Green and Tao page 10, the geometric sum bound min of M and 1 over 2d for a unit z at
distance at least 4d from 1. -/
theorem gt42d_geom_norm_le (M : ℕ) (hM : 1 ≤ M) (z : ℂ) (hz : ‖z‖ = 1) (d : ℝ) (hd : 0 ≤ d)
    (hzd : 4 * d ≤ ‖z - 1‖) :
    ‖∑ n ∈ range M, z ^ n‖ ≤ M / max 1 (2 * M * d) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rcases le_total (2 * M * d) 1 with h1 | h1
  · rw [max_eq_left h1, div_one]
    refine (norm_sum_le _ _).trans ?_
    simp [norm_pow, hz]
  · rw [max_eq_right h1]
    have hd0 : 0 < d := by
      by_contra hcon
      have : d = 0 := le_antisymm (not_lt.mp hcon) hd
      rw [this] at h1; linarith
    have hz1 : z ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hzd; linarith
    have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    rw [geom_sum_eq hz1, norm_div]
    have hnum : ‖z ^ M - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, hz]; norm_num
    have hMp : (0 : ℝ) < M := by linarith
    calc ‖z ^ M - 1‖ / ‖z - 1‖ ≤ 2 / (4 * d) :=
          div_le_div₀ (by norm_num) hnum (by positivity) hzd
      _ = M / (2 * M * d) := by field_simp; norm_num

/-- Green and Tao, Restriction theory of the Selberg sieve, arXiv math/0405581, proof of
Proposition 4.1, page 10, the kernel of one fraction a/q: the mean over n below M of
e of n times theta, with theta equal to h/M minus a/q, is a geometric sum bounded by
1 over 2 M times the distance of theta to the nearest integer, and the transported value at n
equal to 0 changes the mean by at most 2/M. The bound uses max with 1 so that it also covers
theta an integer. This replaces the smooth cutoff and Poisson summation of the printed proof,
following the QUESTION in the notes of level_set_large_delta. Proved. -/
theorem kernel_pointwise (M q a : ℕ) (hM : 1 ≤ M) (_hq : 1 ≤ q) (h : ℝ) :
    ‖(M : ℂ)⁻¹ * ∑ n ∈ range M,
        eC (-((a : ℝ) * (if n = 0 then M else n) / q)) * eC (h * n / M)‖ ≤
      1 / max 1 (2 * M * |(h / M - a / q) - round (h / M - a / q)|) + 2 / M := by
  set θ : ℝ := h / M - a / q with hθ
  set d : ℝ := |θ - round θ| with hd
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set z : ℂ := eC θ with hz
  have hzn : ‖z‖ = 1 := gt42d_norm_eC θ
  have hzd : 4 * d ≤ ‖z - 1‖ := by
    have h1 := gt42d_four_le_norm_eC_sub_one (abs_sub_round θ)
    have h2 : eC θ = eC (θ - round θ) := by
      conv_lhs => rw [show θ = (θ - round θ) + ((round θ : ℤ) : ℝ) by ring]
      rw [lss_eC_add, lss_eC_int, mul_one]
    rw [hz, h2]; exact h1
  have hterm : ∀ n ∈ range M, n ≠ 0 →
      eC (-((a : ℝ) * (if n = 0 then M else n) / q)) * eC (h * n / M) = z ^ n := by
    intro n _ hn
    simp only [hn, ↓reduceIte]
    rw [hz, ← lss_eC_nat_mul, ← lss_eC_add]
    congr 1; rw [hθ]; ring
  have hsplit : ∑ n ∈ range M,
      eC (-((a : ℝ) * (if n = 0 then M else n) / q)) * eC (h * n / M) =
      ∑ n ∈ range M, z ^ n +
        (eC (-((a : ℝ) * (if (0:ℕ) = 0 then M else (0:ℕ)) / q)) * eC (h * (0:ℕ) / M) - 1) := by
    rw [← sub_eq_iff_eq_add', ← sum_sub_distrib]
    rw [sum_eq_single 0]
    · simp
    · intro n hn hn0; rw [hterm n hn hn0, sub_self]
    · intro h0; exact absurd (mem_range.mpr (by omega)) h0
  rw [hsplit, mul_add]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  have hg := gt42d_geom_norm_le M hM z hzn d (abs_nonneg _) hzd
  have h0 : ‖eC (-((a : ℝ) * (if (0:ℕ) = 0 then M else (0:ℕ)) / q)) * eC (h * (0:ℕ) / M) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, gt42d_norm_eC, gt42d_norm_eC]; norm_num
  have hmax : 0 < max 1 (2 * M * d) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have e1 : (M : ℝ)⁻¹ * (M / max 1 (2 * M * d)) = 1 / max 1 (2 * M * d) := by
    field_simp
  calc (M : ℝ)⁻¹ * ‖∑ n ∈ range M, z ^ n‖ + (M : ℝ)⁻¹ * ‖eC (-((a : ℝ) * (if (0:ℕ) = 0 then M else (0:ℕ)) / q)) * eC (h * (0:ℕ) / M) - 1‖
      ≤ (M : ℝ)⁻¹ * (M / max 1 (2 * M * d)) + (M : ℝ)⁻¹ * 2 := by
        gcongr
    _ = 1 / max 1 (2 * M * d) + 2 / M := by rw [e1]; ring

/-- LEAF: Green and Tao, Restriction theory of the Selberg sieve, arXiv math/0405581, proof of
Proposition 4.1, display 4.2 for a small set B, pages 10 to 12, the counting step: the fractions
a/q with q at most M^(1/5) are separated by M^(-2/5), so for each pair x, y in B only the
nearest fraction to y minus x over M contributes beyond a negligible error, and the moment bound
for the restricted divisor function bounds the sum over pairs of the weights q^(eps/2 - 1)
times the main part 1 over max of 1 and 2 M times the distance of y minus x over M minus a/q
to the nearest integer, of the kernel bound of kernel_pointwise, by K |B|^(1+eps) once |B| is
below M^c. The bound eps at most 1 is needed, see the notes. Class HARD. -/
theorem leaf_pair_main :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ M : ℕ, 1 ≤ M → ∀ B : Finset ℕ, B ⊆ range M → (B.card : ℝ) < (M : ℝ) ^ c →
        ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            (q : ℝ) ^ (ε / 2 - 1) *
              (1 / max 1 (2 * M * |((((y : ℝ) - x)) / M - a / q) -
                round ((((y : ℝ) - x)) / M - a / q)|))
          ≤ K * (B.card : ℝ) ^ (1 + ε) := by
  sorry

/-- Green and Tao, proof of Proposition 4.1, page 10, the error term of the transported value at
n equal to 0: there are at most |B|^2 pairs and at most M^(2/5) fractions, each costing 2/M, so
the total is at most 2 |B|^(1+eps) when |B| is below M^(1/10). Proved. -/
theorem pair_error (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (M : ℕ) (hM : 1 ≤ M) (B : Finset ℕ)
    (hcard : (B.card : ℝ) < (M : ℝ) ^ ((1 : ℝ) / 10)) :
    ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (q : ℝ) ^ (ε / 2 - 1) * (2 / M) ≤ 2 * (B.card : ℝ) ^ (1 + ε) := by
  set Q := ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊ with hQ
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  set t : ℝ := (M : ℝ) ^ ((1 : ℝ) / 10) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hM1 (by norm_num)
  have hpow : ∀ k : ℕ, t ^ k = (M : ℝ) ^ ((k : ℝ) / 10) := by
    intro k
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
    congr 1; ring
  have hMt : (M : ℝ) = t ^ 10 := by
    rw [hpow]; norm_num
  have hQt : (Q : ℝ) ≤ t ^ 2 := by
    rw [hpow]
    have := Nat.floor_le (Real.rpow_nonneg hMp.le ((1 : ℝ) / 5))
    rw [← hQ] at this
    convert this using 2; norm_num
  have hinner : ∀ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (q : ℝ) ^ (ε / 2 - 1) * (2 / M) ≤ (Q : ℝ) * (2 / M) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hq
    have hw : (q : ℝ) ^ (ε / 2 - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq1) (by linarith)
    calc _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), (2 / M : ℝ) := by
          apply sum_le_sum; intro a _
          have : (0 : ℝ) ≤ 2 / M := by positivity
          nlinarith
      _ = (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * (2 / M) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * (2 / M) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h1 := card_filter_le (range q) (fun a => Nat.Coprime a q)
          rw [card_range] at h1
          exact_mod_cast h1.trans hqQ
  have hq : ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (q : ℝ) ^ (ε / 2 - 1) * (2 / M) ≤ (Q : ℝ) * ((Q : ℝ) * (2 / M)) := by
    refine (sum_le_sum hinner).trans ?_
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
    simp
  have hxy : ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 Q,
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), (q : ℝ) ^ (ε / 2 - 1) * (2 / M) ≤
      (B.card : ℝ) * ((B.card : ℝ) * ((Q : ℝ) * ((Q : ℝ) * (2 / M)))) := by
    calc _ ≤ ∑ x ∈ B, ∑ y ∈ B, (Q : ℝ) * ((Q : ℝ) * (2 / M)) := by
          apply sum_le_sum; intro x _; apply sum_le_sum; intro y _; exact hq
      _ = _ := by simp [sum_const, nsmul_eq_mul]
  refine hxy.trans ?_
  rcases Nat.eq_zero_or_pos B.card with h0 | h0
  · rw [h0]; simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg le_rfl _)
  have hc1 : (1 : ℝ) ≤ B.card := by exact_mod_cast h0
  have hcp : (1 : ℝ) ≤ (B.card : ℝ) ^ (1 + ε) := Real.one_le_rpow hc1 (by linarith)
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hprod : (B.card : ℝ) * ((B.card : ℝ) * ((Q : ℝ) * (Q : ℝ))) ≤ t ^ 10 := by
    have h1 : (B.card : ℝ) * (B.card : ℝ) ≤ t * t := mul_le_mul hcard.le hcard.le hc0 (by linarith)
    have h2 : (Q : ℝ) * Q ≤ t ^ 2 * t ^ 2 := mul_le_mul hQt hQt hQ0 (by positivity)
    have h3 : t * t * (t ^ 2 * t ^ 2) ≤ t ^ 10 := by
      have : t ^ 6 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num)
      nlinarith
    calc (B.card : ℝ) * ((B.card : ℝ) * ((Q : ℝ) * (Q : ℝ)))
        = ((B.card : ℝ) * B.card) * ((Q : ℝ) * Q) := by ring
      _ ≤ t * t * (t ^ 2 * t ^ 2) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ ≤ t ^ 10 := h3
  calc (B.card : ℝ) * ((B.card : ℝ) * ((Q : ℝ) * ((Q : ℝ) * (2 / M))))
      = (B.card : ℝ) * ((B.card : ℝ) * ((Q : ℝ) * (Q : ℝ))) * (2 / M) := by ring
    _ ≤ (M : ℝ) * (2 / M) := by
        rw [hMt]; exact mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = 2 := by field_simp
    _ ≤ 2 * (B.card : ℝ) ^ (1 + ε) := by linarith
/-- Green and Tao, proof of Proposition 4.1, display 4.2 for a small set B, pages 10 to 12, the
counting step for the full kernel bound of kernel_pointwise, from the main part leaf_pair_main and
the proved error part pair_error. CONDITIONAL ON leaf_pair_main. -/
theorem pair_count :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ M : ℕ, 1 ≤ M → ∀ B : Finset ℕ, B ⊆ range M → (B.card : ℝ) < (M : ℝ) ^ c →
        ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            (q : ℝ) ^ (ε / 2 - 1) *
              (1 / max 1 (2 * M * |((((y : ℝ) - x)) / M - a / q) -
                round ((((y : ℝ) - x)) / M - a / q)|) + 2 / M)
          ≤ K * (B.card : ℝ) ^ (1 + ε) := by
  intro ε hε hε1
  obtain ⟨c, hc, K, hK, H⟩ := leaf_pair_main ε hε hε1
  refine ⟨min c (1 / 10), lt_min hc (by norm_num), K + 2, by linarith, ?_⟩
  intro M hM B hB hcard
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc1 : (B.card : ℝ) < (M : ℝ) ^ c :=
    lt_of_lt_of_le hcard (Real.rpow_le_rpow_of_exponent_le hM1 (min_le_left _ _))
  have hc2 : (B.card : ℝ) < (M : ℝ) ^ ((1 : ℝ) / 10) :=
    lt_of_lt_of_le hcard (Real.rpow_le_rpow_of_exponent_le hM1 (min_le_right _ _))
  have h1 := H M hM B hB hc1
  have h2 := pair_error ε hε hε1 M hM B hc2
  simp only [mul_add, sum_add_distrib]
  linarith

/-- Green and Tao, Restriction theory of the Selberg sieve, arXiv math/0405581, proof of
Proposition 4.1, display 4.2 for a small set B, pages 10 to 12, after the expansion 3.3 has been
inserted: the sum over pairs in B of the kernels of the fractions a/q with q at most M^(1/5),
weighted by q^(eps/2 - 1), the coefficient bound of Proposition 4.1 v at eps/2, is at most
K |B|^(1+eps) once |B| is below M^c, for eps at most 1. Here n equal to 0 is transported from n equal to M as in
envelopingBeta. CONDITIONAL ON leaf_pair_main. -/
theorem kernel_pair_sum :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ M : ℕ, 1 ≤ M → ∀ B : Finset ℕ, B ⊆ range M → (B.card : ℝ) < (M : ℝ) ^ c →
        ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            (q : ℝ) ^ (ε / 2 - 1) *
              ‖(M : ℂ)⁻¹ * ∑ n ∈ range M,
                eC (-((a : ℝ) * (if n = 0 then M else n) / q)) * eC (((y : ℝ) - x) * n / M)‖
          ≤ K * (B.card : ℝ) ^ (1 + ε) := by
  intro ε hε hε1
  obtain ⟨c, hc, K, hK, H⟩ := pair_count ε hε hε1
  refine ⟨c, hc, K, hK, ?_⟩
  intro M hM B hB hcard
  refine le_trans ?_ (H M hM B hB hcard)
  apply sum_le_sum; intro x _
  apply sum_le_sum; intro y _
  apply sum_le_sum; intro q hq
  apply sum_le_sum; intro a _
  apply mul_le_mul_of_nonneg_left
    (kernel_pointwise M q a hM (mem_Icc.mp hq).1 _)
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Green and Tao, proof of Proposition 4.1, page 10: expanding the square of the exponential sum
into a double sum over pairs in B and applying the triangle inequality, for a real weight and
coefficients of size at most one. Proved. -/
theorem expand_square (β : ℕ → ℝ) (M : ℕ) (B : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    (M : ℝ)⁻¹ * ∑ n ∈ range M, β n * ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 ≤
      ∑ x ∈ B, ∑ y ∈ B,
        ‖(M : ℂ)⁻¹ * ∑ n ∈ range M, (β n : ℂ) * eC (((y : ℝ) - x) * n / M)‖ := by
  set T : ℕ → ℕ → ℂ := fun x y =>
    (M : ℂ)⁻¹ * ∑ n ∈ range M, (β n : ℂ) * eC (((y : ℝ) - x) * n / M) with hT
  have hsq : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hprod : ∀ x y n : ℕ, eC (-((x : ℝ) * n / M)) * eC ((y : ℝ) * n / M) =
      eC (((y : ℝ) - x) * n / M) := by
    intro x y n
    rw [← lss_eC_add]
    congr 1
    ring
  have key : (((M : ℝ)⁻¹ * ∑ n ∈ range M,
      β n * ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ B, ∑ y ∈ B, f x * (starRingEnd ℂ) (f y) * T x y := by
    push_cast [Complex.ofReal_sum, Complex.ofReal_mul]
    simp only [← Complex.ofReal_pow, hsq]
    have hn : ∀ n : ℕ, (β n : ℂ) * ((∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))) *
        (starRingEnd ℂ) (∑ x ∈ B, f x * eC (-((x : ℝ) * n / M)))) =
        ∑ x ∈ B, ∑ y ∈ B, f x * (starRingEnd ℂ) (f y) *
          ((β n : ℂ) * eC (((y : ℝ) - x) * n / M)) := by
      intro n
      rw [map_sum, sum_mul_sum, mul_sum]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      rw [map_mul, lss_eC_conj, neg_neg, ← hprod x y n]
      ring
    rw [sum_congr rfl (fun n _ => hn n), mul_sum]
    simp only [mul_sum]
    conv_lhs => rw [sum_comm]
    apply sum_congr rfl
    intro x _
    conv_lhs => rw [sum_comm]
    apply sum_congr rfl
    intro y _
    simp only [hT, mul_sum]
    apply sum_congr rfl
    intro n _
    ring
  have hre : (M : ℝ)⁻¹ * ∑ n ∈ range M,
      β n * ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 =
      (∑ x ∈ B, ∑ y ∈ B, f x * (starRingEnd ℂ) (f y) * T x y).re := by
    rw [← key, Complex.ofReal_re]
  rw [hre]
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro x _
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro y _
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h1 := hf x
  have h2 := hf y
  have h3 := norm_nonneg (T x y)
  have h4 := norm_nonneg (f x)
  have h5 := norm_nonneg (f y)
  calc ‖f x‖ * ‖f y‖ * ‖T x y‖ ≤ 1 * 1 * ‖T x y‖ := by gcongr
    _ = ‖T x y‖ := by ring

/-- Green and Tao, proof of Proposition 4.1, page 10: inserting the expansion 3.3 of the uncapped
sieve, as given by EnvelopingFourierExpansion, into the mean of the sieve against a linear phase,
and bounding the coefficients by Proposition 4.1 v. Proved. -/
theorem insert_expansion (w : ℕ) (W b : ℤ) (M : ℕ) (D : ℝ → ℝ) (v : ℕ → ℕ → ℂ)
    (ε : ℝ) (hε : 0 < ε)
    (hvb : ∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
      ‖v q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1))
    (hexp : ∀ n < M, (envelopingBeta w W b M n : ℂ) =
      ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          v q a * eC (-((a : ℝ) * (if n = 0 then M else n) / q))) (h : ℝ) :
    ‖(M : ℂ)⁻¹ * ∑ n ∈ range M, (envelopingBeta w W b M n : ℂ) * eC (h * n / M)‖ ≤
      ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          D ε * ((q : ℝ) ^ (ε - 1) *
            ‖(M : ℂ)⁻¹ * ∑ n ∈ range M,
              eC (-((a : ℝ) * (if n = 0 then M else n) / q)) * eC (h * n / M)‖) := by
  have hid : (M : ℂ)⁻¹ * ∑ n ∈ range M, (envelopingBeta w W b M n : ℂ) * eC (h * n / M) =
      ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          v q a * ((M : ℂ)⁻¹ * ∑ n ∈ range M,
            eC (-((a : ℝ) * (if n = 0 then M else n) / q)) * eC (h * n / M)) := by
    rw [sum_congr rfl (fun n hn => by rw [hexp n (mem_range.mp hn)])]
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro n _
    ring
  rw [hid]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro q hq
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro a ha
  have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
  obtain ⟨har, hcop⟩ := mem_filter.mp ha
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hvb ε hε q hq1 a (mem_range.mp har) hcop) (norm_nonneg _)

/-- Green and Tao, Restriction theory of the Selberg sieve, proof of Proposition 4.1, display
4.2 for a small set B, pages 10 to 12, assembled from the proved reductions and
kernel_pair_sum at min of eps and 1. The statement is literally LevelSet1122b.gt42_small_set.
CONDITIONAL ON leaf_pair_main. -/
theorem gt42_small_set_of_leaves : type_of% @LevelSet1122b.gt42_small_set := by
  intro A D hAD ε hε
  have he : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨c, hc, K, hK, HL⟩ := kernel_pair_sum (min ε 1) he (min_le_right _ _)
  have hε2 : 0 < min ε 1 / 2 := by positivity
  have hpow : ∀ B : Finset ℕ, (B.card : ℝ) ^ (1 + min ε 1) ≤ (B.card : ℝ) ^ (1 + ε) := by
    intro B
    rcases Nat.eq_zero_or_pos B.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by linarith [min_le_left ε 1])
  have hD := (hAD (min ε 1 / 2) hε2).2
  refine ⟨c, hc, D (min ε 1 / 2) * K, mul_pos hD hK, ?_⟩
  intro J w hJ hw b hb hbW ham M hM hEB B hB hcard f hf
  obtain ⟨v, -, -, hvb, hexp⟩ := hEB.2
  have hstep1 : (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n *
      ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 ≤
      (M : ℝ)⁻¹ * ∑ n ∈ range M, envelopingBeta w (WW J w) b M n *
      ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro n _
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
  refine hstep1.trans ((expand_square _ M B f hf).trans ?_)
  calc ∑ x ∈ B, ∑ y ∈ B, ‖(M : ℂ)⁻¹ * ∑ n ∈ range M,
        (envelopingBeta w (WW J w) b M n : ℂ) * eC (((y : ℝ) - x) * n / M)‖
      ≤ ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            D (min ε 1 / 2) * ((q : ℝ) ^ (min ε 1 / 2 - 1) *
              ‖(M : ℂ)⁻¹ * ∑ n ∈ range M,
                eC (-((a : ℝ) * (if n = 0 then M else n) / q)) *
                  eC (((y : ℝ) - x) * n / M)‖) := by
        apply sum_le_sum
        intro x _
        apply sum_le_sum
        intro y _
        exact insert_expansion w (WW J w) b M D v (min ε 1 / 2) hε2 hvb hexp _
    _ = D (min ε 1 / 2) * ∑ x ∈ B, ∑ y ∈ B, ∑ q ∈ Icc 1 ⌊(M : ℝ) ^ ((1 : ℝ) / 5)⌋₊,
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            (q : ℝ) ^ (min ε 1 / 2 - 1) *
              ‖(M : ℂ)⁻¹ * ∑ n ∈ range M,
                eC (-((a : ℝ) * (if n = 0 then M else n) / q)) *
                  eC (((y : ℝ) - x) * n / M)‖ := by
        simp only [mul_sum]
    _ ≤ D (min ε 1 / 2) * (K * (B.card : ℝ) ^ (1 + min ε 1)) :=
        mul_le_mul_of_nonneg_left (HL M hM B hB hcard) hD.le
    _ ≤ D (min ε 1 / 2) * (K * (B.card : ℝ) ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpow B) hK.le) hD.le
    _ = D (min ε 1 / 2) * K * (B.card : ℝ) ^ (1 + ε) := by ring

end LeanLab.Teravainen2016.GT42SmallSet1122d

#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.gt42_small_set_of_leaves
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.expand_square
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.insert_expansion
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.kernel_pair_sum
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.kernel_pointwise
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.pair_count
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.pair_error
#print axioms LeanLab.Teravainen2016.GT42SmallSet1122d.leaf_pair_main
