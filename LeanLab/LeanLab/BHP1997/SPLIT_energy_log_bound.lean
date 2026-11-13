/-
Split of `energy_log_bound` in LeanLab.BHP1997.DecompC165c into leaves.
The sealed statement is unchanged; the target theorem is neither imported nor used.

The statement asks, for every real exponent `B`, for one exponent `K` and one positive
constant `C`, such that the coefficient energy of every Dirichlet polynomial whose
coefficients obey `‖a n‖ ≤ τ(n)^B` is at most `C * (log F)^K`, uniformly in the
coefficients and in the window `c1 F < n < c2 F`.

The split follows the shape of the estimate.

Leaf 1 replaces each `‖a n‖ ^ 2` by its divisor bound, turning the energy into the
divisor moment `Σ τ(n)^(2B) / n` over the same window.

Leaf 2 is the divisor moment in the range `B ≤ 1/2`. There the exponent `2B` is at most
one, so the divisor factor is at most `τ(n)`, and the moment is at most the harmonic
divisor moment, which is a square of a logarithm.

Leaf 3 is the divisor moment in the complementary range `1/2 ≤ B`. There the divisor
factor is a positive power of `τ(n)`, at most `τ(n)^m` with `m = ⌈2B⌉`, and the integer
moment is bounded by the iteration `H_{k+1} ≤ H_k^2` of `EnergyLogC165`.

Leaf 4 exchanges the two logarithms: `log (⌊c2 F⌋₊ + 2)` is comparable with `log F`
on the range `F ≥ 2`, and the comparison survives raising to the power `K`.

Nothing else is needed, so the assembly below closes every goal it states. All four leaves
are proved here from `LeanLab.BHP1997.DecompC165c` and its imports. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- LEAF: the coefficient step of page 12, display 3.1 applied term by term. Every `‖a n‖` is at
most `τ(n)^B`, and the squares and the division by `n` are carried through, so the energy of `a` on
the window is at most the divisor moment on the same window. -/
theorem leaf_energy_le_divisor_moment (a : ℕ → ℂ) (B c1 c2 F : ℝ)
    (ha : Thm4.CoeffBound a B) :
    energy a c1 c2 F ≤
      ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
          (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
        ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
  unfold energy
  apply Finset.sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha n) 2)
    (Nat.cast_nonneg n)

/-- LEAF: the divisor moment for `B ≤ 1/2`. With `2B ≤ 1` and `τ(n) ≥ 1` each divisor factor is at
most `τ(n)`, so the moment is at most the harmonic divisor moment `H_1`, bounded by a square of a
logarithm, and `1 + log N` is at most a constant times `log (N + 2)`. -/
theorem leaf_divisor_moment_half (B : ℝ) (hB : B ≤ 1 / 2) (c2 : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
      ∀ F : ℝ, 2 ≤ F →
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  set R : ℝ := 1 / Real.log 2 + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  refine ⟨2, R ^ 2, by norm_num, by positivity, ?_⟩
  intro F hF
  set N : ℕ := ⌊c2 * F⌋₊ with hN
  have hsplit :
      (∑ n ∈ Finset.range (N + 1), ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ))
        = ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
    rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) from ?_]
    · rw [Finset.sum_insert (by simp)]
      simp
    · ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
  rw [hsplit]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) / (n : ℝ) := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hn
    have hτ1 : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    have hpow : ((n.divisors.card : ℝ) ^ B) ^ 2 = ((n.divisors.card : ℕ) : ℝ) ^ (B * 2) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n.divisors.card) B 2]
      norm_num
    rw [hpow]
    calc ((n.divisors.card : ℕ) : ℝ) ^ (B * 2) / (n : ℝ)
        ≤ ((n.divisors.card : ℕ) : ℝ) ^ (1 : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
            (Nat.cast_nonneg n)
      _ = ((n.divisors.card : ℕ) : ℝ) / (n : ℝ) := by rw [Real.rpow_one]
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h]; simp; exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  have hone : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log ((N : ℝ) + 2) := by
    have h2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) hN2
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / Real.log 2)
    rwa [one_div_mul_cancel (ne_of_gt hl2)] at this
  have hlog : 1 + Real.log (N : ℝ) ≤ R * Real.log ((N : ℝ) + 2) := by
    have hexp : (1 / Real.log 2 + 1) * Real.log ((N : ℝ) + 2)
        = (1 / Real.log 2) * Real.log ((N : ℝ) + 2) + Real.log ((N : ℝ) + 2) := by ring
    rw [hRdef, hexp]
    linarith
  have hlog2 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  calc (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / (n : ℝ) :=
        Finset.sum_le_sum hterm
    _ = EnergyLogC165.harmonicDivisorMoment 1 N := by
        simp [EnergyLogC165.harmonicDivisorMoment]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
        simpa using EnergyLogC165.harmonicDivisorMoment_le 1 N
    _ ≤ (R * Real.log ((N : ℝ) + 2)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hlog 2
    _ = R ^ 2 * Real.log ((N : ℝ) + 2) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        ring

/-- LEAF: the divisor moment for `1/2 ≤ B`. With `m = ⌈2B⌉` the divisor factor `τ(n)^(2B)` is at
most `τ(n)^m`, the integer moment is bounded by the iteration of `EnergyLogC165`, and the logarithm
is rescaled as in the previous leaf. -/
theorem leaf_divisor_moment_large (B : ℝ) (hB : 1 / 2 ≤ B) (c2 : ℝ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
      ∀ F : ℝ, 2 ≤ F →
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  set m : ℕ := ⌈2 * B⌉₊ with hm
  set R : ℝ := 1 / Real.log 2 + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  refine ⟨((2 ^ m : ℕ) : ℝ), R ^ ((2 ^ m : ℕ) : ℝ), by positivity, by positivity, ?_⟩
  intro F hF
  set N : ℕ := ⌊c2 * F⌋₊ with hN
  have hsplit :
      (∑ n ∈ Finset.range (N + 1), ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ))
        = ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
    rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) from ?_]
    · rw [Finset.sum_insert (by simp)]
      simp
    · ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
  rw [hsplit]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ) := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hn
    have hτ1 : (1 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    have hpow : ((n.divisors.card : ℝ) ^ B) ^ 2 = ((n.divisors.card : ℕ) : ℝ) ^ (B * 2) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n.divisors.card) B 2]
      norm_num
    have hexp : B * 2 ≤ ((m : ℕ) : ℝ) := by
      have := Nat.le_ceil (2 * B)
      rw [hm]
      push_cast
      linarith
    rw [hpow]
    calc ((n.divisors.card : ℕ) : ℝ) ^ (B * 2) / (n : ℝ)
        ≤ ((n.divisors.card : ℕ) : ℝ) ^ ((m : ℕ) : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hτ1 hexp)
            (Nat.cast_nonneg n)
      _ = ((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ) := by rw [Real.rpow_natCast]
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h]; simp; exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (by exact_mod_cast h) (by linarith)
  have hone : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log ((N : ℝ) + 2) := by
    have h2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) hN2
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / Real.log 2)
    rwa [one_div_mul_cancel (ne_of_gt hl2)] at this
  have hlog : 1 + Real.log (N : ℝ) ≤ R * Real.log ((N : ℝ) + 2) := by
    have hexp : (1 / Real.log 2 + 1) * Real.log ((N : ℝ) + 2)
        = (1 / Real.log 2) * Real.log ((N : ℝ) + 2) + Real.log ((N : ℝ) + 2) := by ring
    rw [hRdef, hexp]
    linarith
  have hlog2 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  calc (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ))
      ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) ^ m / (n : ℝ) :=
        Finset.sum_le_sum hterm
    _ = EnergyLogC165.harmonicDivisorMoment m N := by
        simp [EnergyLogC165.harmonicDivisorMoment]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 ^ m := EnergyLogC165.harmonicDivisorMoment_le m N
    _ ≤ (R * Real.log ((N : ℝ) + 2)) ^ 2 ^ m :=
        pow_le_pow_left₀ (by linarith) hlog (2 ^ m)
    _ = R ^ ((2 ^ m : ℕ) : ℝ) * Real.log ((N : ℝ) + 2) ^ ((2 ^ m : ℕ) : ℝ) := by
        rw [← Real.rpow_natCast, Real.mul_rpow hR.le hlog2]

/-- LEAF: the logarithmic comparison. On `F ≥ 2` the integer part `⌊c2 F⌋₊` is at most
`(max c2 0) * F`, so `log (⌊c2 F⌋₊ + 2) ≤ R * log F`, and raising to the power `K ≥ 0` keeps the
comparison with `R^K` as the constant. -/
theorem leaf_log_floor_rpow_le (c2 K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 < D ∧ ∀ F : ℝ, 2 ≤ F →
      Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K ≤ D * Real.log F ^ K := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  set A : ℝ := max c2 0 + 1 with hA
  have hA1 : 0 < A := by rw [hA]; have := le_max_right c2 0; linarith
  have hAge1 : 1 ≤ A := by rw [hA]; have := le_max_right c2 0; linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hAge1
  set R : ℝ := 1 + Real.log A / Real.log 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  refine ⟨R ^ K, Real.rpow_pos_of_pos hR K, ?_⟩
  intro F hF
  set N : ℕ := ⌊c2 * F⌋₊ with hN
  have hF0 : (0 : ℝ) < F := by linarith
  have ht0 : (0 : ℝ) < (N : ℝ) + 2 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hNle : (N : ℝ) ≤ max c2 0 * F := by
    by_cases h : c2 ≤ 0
    · have hz : N = 0 := by
        rw [hN]
        exact Nat.floor_eq_zero.mpr (by nlinarith)
      have hmax : max c2 0 = 0 := max_eq_right h
      rw [hz, hmax]
      simp
    · have hpos : 0 < c2 := lt_of_not_ge h
      rw [hN]
      calc ((⌊c2 * F⌋₊ : ℕ) : ℝ) ≤ c2 * F := Nat.floor_le (mul_pos hpos hF0).le
        _ = max c2 0 * F := by rw [max_eq_left hpos.le]
  have hAle : (N : ℝ) + 2 ≤ A * F := by
    have hAF : A * F = max c2 0 * F + F := by
      rw [hA]
      ring
    rw [hAF]
    nlinarith [hNle, hF]
  have hlogle : Real.log ((N : ℝ) + 2) ≤ R * Real.log F := by
    have h1 : Real.log ((N : ℝ) + 2) ≤ Real.log (A * F) := Real.log_le_log ht0 hAle
    rw [Real.log_mul (ne_of_gt hA1) (ne_of_gt hF0)] at h1
    have h2 : Real.log A ≤ (Real.log A / Real.log 2) * Real.log F := by
      have h3 : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
      have := mul_le_mul_of_nonneg_left h3 (div_nonneg hlogA hl2.le)
      rwa [div_mul_cancel₀ _ (ne_of_gt hl2)] at this
    rw [hRdef]
    linarith
  have hlogpos : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlogF : (0 : ℝ) ≤ Real.log F := Real.log_nonneg (by linarith)
  calc Real.log ((N : ℝ) + 2) ^ K ≤ (R * Real.log F) ^ K :=
        Real.rpow_le_rpow hlogpos hlogle hK
    _ = R ^ K * Real.log F ^ K := Real.mul_rpow hR.le hlogF

/-- The assembly of `energy_log_bound` from the four leaves, with the sealed statement unchanged.
The two cases `B ≤ 1/2` and `1/2 ≤ B` select the second or the third leaf; the first leaf changes
the energy into the divisor moment, the fourth leaf replaces the logarithm of the range by the
logarithm of `F`, and the sum over the window filter is bounded by the sum over the whole range
because every summand is nonnegative. -/
theorem energy_log_bound_split : EnergyLogBound := by
  intro B c1 c2 hc1 hc2
  rcases le_total B (1 / 2) with hB | hB
  · obtain ⟨K, C, hK, hC, hbound⟩ := leaf_divisor_moment_half B hB c2
    obtain ⟨D, hD, hlog⟩ := leaf_log_floor_rpow_le c2 K hK
    refine ⟨K, C * D, mul_pos hC hD, ?_⟩
    intro a ha F hF
    have h1 :
        energy a c1 c2 F ≤
          ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) :=
      leaf_energy_le_divisor_moment a B c1 c2 F ha
    have h2 :
        (∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          ∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro x _ _
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg x)
    have h3 :
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K :=
      hbound F hF
    have h4 : Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K ≤ D * Real.log F ^ K := hlog F hF
    calc energy a c1 c2 F
        ≤ C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := le_trans (le_trans h1 h2) h3
      _ ≤ C * (D * Real.log F ^ K) := mul_le_mul_of_nonneg_left h4 hC.le
      _ = C * D * Real.log F ^ K := by ring
  · obtain ⟨K, C, hK, hC, hbound⟩ := leaf_divisor_moment_large B hB c2
    obtain ⟨D, hD, hlog⟩ := leaf_log_floor_rpow_le c2 K hK
    refine ⟨K, C * D, mul_pos hC hD, ?_⟩
    intro a ha F hF
    have h1 :
        energy a c1 c2 F ≤
          ∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) :=
      leaf_energy_le_divisor_moment a B c1 c2 F ha
    have h2 :
        (∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
              (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          ∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro x _ _
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg x)
    have h3 :
        (∑ n ∈ Finset.range (⌊c2 * F⌋₊ + 1),
            ((n.divisors.card : ℝ) ^ B) ^ 2 / (n : ℝ)) ≤
          C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K :=
      hbound F hF
    have h4 : Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K ≤ D * Real.log F ^ K := hlog F hF
    calc energy a c1 c2 F
        ≤ C * Real.log ((⌊c2 * F⌋₊ : ℝ) + 2) ^ K := le_trans (le_trans h1 h2) h3
      _ ≤ C * (D * Real.log F ^ K) := mul_le_mul_of_nonneg_left h4 hC.le
      _ = C * D * Real.log F ^ K := by ring

end LeanLab.BHP1997.DecompC165c
