/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E4 sum reached from display 5.15, page 50: partial summation in one outer prime.

The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the outer primes the consequence is partial summation against the weight
`1 / p` times a function of bounded variation. This file proves that tool:

* `four_abel_reciprocal`: partial summation with the weight `f n / n`, when the unweighted
  prefix sums up to `i` are at most `ρ i`;
* `four_pnt_reciprocal`: the prime number theorem in the form
  `∑ (ρ(n) - 1 / log n) f(n) / n = O((M log U + V) / log^A L)` over `(L, U]`, for `f` bounded
  by `M` with total variation `V`.

* `four_fibre_fixed_level`, `four_transfer_iterated`: the same for the fibre of the E4 sum
  along one outer prime which is not the level, and summed over the other three variables;
* `four_fibre_level`, `four_transfer_iterated_level`: the same along the level `p4`;
* `four_transfer_p1`, `four_transfer_p2`, `four_transfer_p3`, `four_transfer_p4`: partial
  summation in each outer prime of the E4 sum at one point of J, with every log power saved.

The geometric input, that the indicator of E4 has boundedly many jumps along a line, is
`four_region_jumps` of `FourDensityMain517b.lean`. No new definition, nothing left open in this
file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.PrimeWeighted517
import LeanLab.BHP1997.FourDensityMain517b

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51, display 5.17, partial summation in one outer prime with the weight `1 / p`.
If the unweighted sums of `a` over `(L, i]` are at most `ρ i` for every `i` up to `U`, then for
`f` bounded by `M` with total variation at most `V` the sum of `a n f(n) / n` over `(L, U]` is
at most `ρ (M (2 + log U) + V)`. -/
theorem four_abel_reciprocal (a f : ℕ → ℝ) {L U : ℕ} (hL : 1 ≤ L) (hLU : L ≤ U) {M V ρ : ℝ}
    (hM0 : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hf : ∀ n ∈ Finset.Icc (L + 1) U, |f n| ≤ M)
    (hV : ∑ i ∈ Finset.Ico (L + 1) U, |f (i + 1) - f i| ≤ V)
    (hR : ∀ i : ℕ, L ≤ i → i ≤ U → |∑ m ∈ Finset.Ioc L i, a m| ≤ ρ * i) :
    |∑ n ∈ Finset.Ioc L U, a n * (f n / n)| ≤ ρ * (M * (2 + Real.log U) + V) := by
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hV
  have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hL.trans hLU
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU1
  rcases hLU.eq_or_lt with rfl | hlt
  · rw [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    positivity
  have hs : ∀ m ∈ Finset.Ioc L U, L + 1 ≤ m ∧ m ≤ U := fun m hm => by
    have := Finset.mem_Ioc.mp hm
    omega
  have key := Decomp514Abel.finite_abel (Finset.Ioc L U) hs
    (fun m => (((f m / (m : ℝ) : ℝ)) : ℂ)) (fun m => ((a m : ℝ) : ℂ))
  have keyR : ∑ m ∈ Finset.Ioc L U, f m / (m : ℝ) * a m =
      f U / (U : ℝ) * ∑ m ∈ Finset.Ioc L U, a m -
        ∑ i ∈ Finset.Ico (L + 1) U, (f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ)) *
          ∑ m ∈ (Finset.Ioc L U).filter (fun m => m ≤ i), a m := by
    exact_mod_cast key
  have he : ∑ n ∈ Finset.Ioc L U, a n * (f n / n) =
      ∑ m ∈ Finset.Ioc L U, f m / (m : ℝ) * a m :=
    Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [he, keyR]
  have hU0 : (0 : ℝ) < (U : ℝ) := by linarith
  -- the endpoint term
  have t1 : |f U / (U : ℝ) * ∑ m ∈ Finset.Ioc L U, a m| ≤ ρ * M := by
    have h1 := hf U (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    have h2 := hR U hlt.le le_rfl
    rw [abs_mul, abs_div, abs_of_pos hU0]
    calc |f U| / (U : ℝ) * |∑ m ∈ Finset.Ioc L U, a m|
        ≤ M / (U : ℝ) * (ρ * U) :=
          mul_le_mul (div_le_div_of_nonneg_right h1 hU0.le) h2 (abs_nonneg _)
            (div_nonneg hM0 hU0.le)
      _ = ρ * M := by field_simp
  -- the variation terms
  have t2 : ∀ i ∈ Finset.Ico (L + 1) U,
      |(f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ)) *
          ∑ m ∈ (Finset.Ioc L U).filter (fun m => m ≤ i), a m| ≤
        ρ * |f (i + 1) - f i| + ρ * M * (((i : ℝ) + 1)⁻¹) := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hfil : (Finset.Ioc L U).filter (fun m => m ≤ i) = Finset.Ioc L i := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    rw [hfil]
    have hS := hR i (by omega) (by omega)
    have hfi := hf i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
    have hi0 : (0 : ℝ) < (i : ℝ) := by
      have : 0 < i := by omega
      exact_mod_cast this
    have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
    have hd : f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ) =
        (f (i + 1) - f i) / ((i : ℝ) + 1) - f i / ((i : ℝ) * ((i : ℝ) + 1)) := by
      field_simp
      ring
    have hb : |f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ)| ≤
        |f (i + 1) - f i| / ((i : ℝ) + 1) + M / ((i : ℝ) * ((i : ℝ) + 1)) := by
      rw [hd]
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_div, abs_of_pos hi1, abs_of_pos (mul_pos hi0 hi1)]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right hfi (mul_pos hi0 hi1).le)
    rw [abs_mul]
    have hD0 := abs_nonneg (f (i + 1) - f i)
    calc |f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ)| * |∑ m ∈ Finset.Ioc L i, a m|
        ≤ (|f (i + 1) - f i| / ((i : ℝ) + 1) + M / ((i : ℝ) * ((i : ℝ) + 1))) * (ρ * i) :=
          mul_le_mul hb hS (abs_nonneg _) (by positivity)
      _ = ρ * (|f (i + 1) - f i| * ((i : ℝ) / ((i : ℝ) + 1))) + ρ * M * (((i : ℝ) + 1)⁻¹) := by
          field_simp
      _ ≤ ρ * |f (i + 1) - f i| + ρ * M * (((i : ℝ) + 1)⁻¹) := by
          have h1 : (i : ℝ) / ((i : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hi1]
            linarith
          have h2 := mul_le_mul_of_nonneg_left h1 hD0
          have h3 := mul_le_mul_of_nonneg_left h2 hρ
          linarith
  have hharm : ∑ i ∈ Finset.Ico (L + 1) U, (((i : ℝ) + 1)⁻¹) ≤ 1 + Real.log U := by
    have h1 := harmonic_le_one_add_log U
    have h2 : ((harmonic U : ℚ) : ℝ) = ∑ i ∈ Finset.range U, (((i : ℝ) + 1)⁻¹) := by
      unfold harmonic
      push_cast
      rfl
    rw [h2] at h1
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity) h1
    intro i hi
    have := Finset.mem_Ico.mp hi
    exact Finset.mem_range.mpr this.2
  have t3 : |∑ i ∈ Finset.Ico (L + 1) U, (f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ)) *
        ∑ m ∈ (Finset.Ioc L U).filter (fun m => m ≤ i), a m| ≤
      ρ * V + ρ * M * (1 + Real.log U) := by
    calc _ ≤ ∑ i ∈ Finset.Ico (L + 1) U,
          |(f (i + 1) / ((i : ℝ) + 1) - f i / (i : ℝ)) *
            ∑ m ∈ (Finset.Ioc L U).filter (fun m => m ≤ i), a m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico (L + 1) U,
          (ρ * |f (i + 1) - f i| + ρ * M * (((i : ℝ) + 1)⁻¹)) := Finset.sum_le_sum t2
      _ = ρ * ∑ i ∈ Finset.Ico (L + 1) U, |f (i + 1) - f i| +
          ρ * M * ∑ i ∈ Finset.Ico (L + 1) U, (((i : ℝ) + 1)⁻¹) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ρ * V + ρ * M * (1 + Real.log U) :=
          add_le_add (mul_le_mul_of_nonneg_left hV hρ)
            (mul_le_mul_of_nonneg_left hharm (mul_nonneg hρ hM0))
  refine (abs_sub _ _).trans ?_
  have e : ρ * (M * (2 + Real.log U) + V) = ρ * M + (ρ * V + ρ * M * (1 + Real.log U)) := by
    ring
  rw [e]
  exact add_le_add t1 t3

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem":
the prime number theorem with partial summation against `f(n) / n`. For every positive `A`
there is `C` such that for integers `C ≤ L ≤ U` and `f` bounded by `M` on `(L, U]` with total
variation at most `V`, the sum of `f(p) / p` over the primes of `(L, U]` differs from the sum
of `f(n) / (n log n)` over the integers by at most `C (M (2 + log U) + V) / log^A L`. -/
theorem four_pnt_reciprocal (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ L U : ℕ, C ≤ (L : ℝ) → L ≤ U → ∀ (f : ℕ → ℝ) (M V : ℝ), 0 ≤ M →
      (∀ n ∈ Finset.Icc (L + 1) U, |f n| ≤ M) →
      ∑ i ∈ Finset.Ico (L + 1) U, |f (i + 1) - f i| ≤ V →
      |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ)) * (f n / n)| ≤
        C * (M * (2 + Real.log U) + V) * Real.log (L : ℝ) ^ (-A) := by
  obtain ⟨C1, hC1, h⟩ := pnt_interval_nat A hA
  refine ⟨max C1 3, fun L U hCL hLU f M V hM0 hf hV => ?_⟩
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := (le_max_right _ _).trans hCL
  have hLC : C1 ≤ (L : ℝ) := (le_max_left _ _).trans hCL
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  have hlL : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hV
  have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hL1.trans hLU
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hpowL : 0 ≤ Real.log (L : ℝ) ^ (-A) := Real.rpow_nonneg hlL.le _
  have hR : ∀ i : ℕ, L ≤ i → i ≤ U →
      |∑ m ∈ Finset.Ioc L i, (primeWeight m - 1 / Real.log (m : ℝ))| ≤
        C1 * Real.log (L : ℝ) ^ (-A) * i := by
    intro i hLi _
    have hLi' : (L : ℝ) ≤ (i : ℝ) := by exact_mod_cast hLi
    have h1 := h (i : ℝ) (hLC.trans hLi') L i hLi le_rfl
    have hlog : Real.log (L : ℝ) ≤ Real.log (i : ℝ) := Real.log_le_log (by linarith) hLi'
    have hpow : Real.log (i : ℝ) ^ (-A) ≤ Real.log (L : ℝ) ^ (-A) := by
      rw [Real.rpow_neg (hlL.le.trans hlog), Real.rpow_neg hlL.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hlL _) (Real.rpow_le_rpow hlL.le hlog hA.le)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    calc _ ≤ C1 * (i : ℝ) * Real.log (i : ℝ) ^ (-A) := h1
      _ ≤ C1 * (i : ℝ) * Real.log (L : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (by linarith) hi0)
      _ = C1 * Real.log (L : ℝ) ^ (-A) * i := by ring
  have key := four_abel_reciprocal (fun m => primeWeight m - 1 / Real.log (m : ℝ)) f hL1 hLU
    hM0 (mul_nonneg (by linarith) hpowL) hf hV hR
  refine key.trans ?_
  have hK : 0 ≤ M * (2 + Real.log U) + V := by positivity
  calc C1 * Real.log (L : ℝ) ^ (-A) * (M * (2 + Real.log U) + V)
      = C1 * ((M * (2 + Real.log U) + V) * Real.log (L : ℝ) ^ (-A)) := by ring
    _ ≤ max C1 3 * ((M * (2 + Real.log U) + V) * Real.log (L : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hK hpowL)
    _ = _ := by ring

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in one outer prime `n` of the E4 sum which is not the level, the other
outer variables held fixed. Here `t = log (m / D)` for the product `D` of the other three
variables, `lq` is the logarithm of the level, and `P` collects the order conditions and the
E4 indicator along the variable. If `P` fails up to `L0` and its indicator has variation at
most `J`, then replacing the prime indicator by the density `1 / log n` costs at most
`C (2 + J + log N / lq) / (lq D) (2 + log N) / log^A L0`: the weight is `1 / n` times
`ω((t - log n) / lq)`, which is Lipschitz in `log n` above the jump of `ω` at 1. -/
theorem four_fibre_fixed_level (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L0 N : ℕ, C ≤ (L0 : ℝ) → L0 ≤ N → ∀ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω →
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω →
      ∀ (P : ℕ → Prop) [DecidablePred P] (J t lq Dr : ℝ), 0 < lq → 0 < Dr →
      (∀ n : ℕ, n ≤ L0 → ¬ P n) →
      ∑ i ∈ Finset.Ico (L0 + 1) N,
        |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| ≤ J →
      |∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
          (if P n then ω ((t - Real.log (n : ℝ)) / lq) / lq / (Dr * (n : ℝ)) else 0)| ≤
        C * ((2 + J + Real.log (N : ℝ) / lq) / (lq * Dr)) * (2 + Real.log (N : ℝ)) *
          Real.log (L0 : ℝ) ^ (-A) := by
  obtain ⟨C0, hC0⟩ := four_pnt_reciprocal A hA
  refine ⟨max C0 3, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro L0 N hCL hLN ω hω hz P _ J t lq Dr hlq hDr hlow hJ
  have hL3 : (3 : ℝ) ≤ (L0 : ℝ) := (le_max_right _ _).trans hCL
  have hL1 : 1 ≤ L0 := by
    have : (1 : ℝ) ≤ (L0 : ℝ) := by linarith
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hL1.trans hLN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hJ0 : 0 ≤ J := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hJ
  have hκ : 0 < lq * Dr := mul_pos hlq hDr
  have hlogL : 0 ≤ Real.log (L0 : ℝ) ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = (t - Real.log (n : ℝ)) / lq := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, ∀ n, G n = ω (max (u n) 1) / (lq * Dr) := ⟨_, fun _ => rfl⟩
  have hω0 : ∀ v : ℝ, 0 ≤ ω v := Decomp514a.four_density_buchstab_nonneg hω hz
  have hω1 : ∀ v : ℝ, ω v ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
  have hGM : ∀ n : ℕ, |G n| ≤ 1 / (lq * Dr) := fun n => by
    rw [hG, abs_div, abs_of_pos hκ, abs_of_nonneg (hω0 _)]
    exact div_le_div_of_nonneg_right (hω1 _) hκ.le
  have hlogmono : ∀ i : ℕ, Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exact Real.log_le_log (by exact_mod_cast hi) (by push_cast; linarith)
  have hustep : ∀ i : ℕ, u (i + 1) ≤ u i := fun i => by
    rw [hu, hu]
    exact div_le_div_of_nonneg_right (by linarith [hlogmono i]) hlq.le
  -- restrict to (L0, N]
  have hsub : Finset.Ioc L0 N ⊆ Finset.Icc 1 N := fun n hn => by
    have := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
        (if P n then ω ((t - Real.log (n : ℝ)) / lq) / lq / (Dr * (n : ℝ)) else 0) =
      ∑ n ∈ Finset.Ioc L0 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
        ((G n * (if (P n ∧ 1 ≤ u n) then (1 : ℝ) else 0)) / (n : ℝ)) := by
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      congr 1
      by_cases hP : P n
      · by_cases hQ : 1 ≤ u n
        · rw [if_pos hP, if_pos ⟨hP, hQ⟩, hG, max_eq_left hQ, hu]
          field_simp
        · rw [if_pos hP, if_neg (fun h => hQ h.2), ← hu, hz _ (not_le.mp hQ)]
          simp
      · rw [if_neg hP, if_neg (fun h => hP h.1)]
        simp
    · intro n hn hn'
      have hn1 := Finset.mem_Icc.mp hn
      have hnL : n ≤ L0 := by
        by_contra h
        exact hn' (Finset.mem_Ioc.mpr ⟨by omega, hn1.2⟩)
      rw [if_neg (hlow n hnL)]
      simp
  rw [hsplit]
  -- variation of the smooth part
  have hVG : ∑ i ∈ Finset.Ico (L0 + 1) N, |G (i + 1) - G i| ≤
      Real.log (N : ℝ) / lq / (lq * Dr) := by
    have hpt : ∀ i ∈ Finset.Ico (L0 + 1) N, |G (i + 1) - G i| ≤
        (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) / lq / (lq * Dr) := by
      intro i _
      rw [hG, hG, ← sub_div, abs_div, abs_of_pos hκ]
      refine div_le_div_of_nonneg_right ?_ hκ.le
      refine (Decomp514a.four_density_buchstab_lipschitz hω hz (le_max_right _ _)
        (le_max_right _ _)).trans ?_
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hustep i]), hu, hu, ← sub_div]
      exact le_of_eq (by ring)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_div, ← Finset.sum_div]
    refine div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ?_ hlq.le) hκ.le
    rcases Nat.lt_or_ge N (L0 + 1) with h | h
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      exact hlogN
    · rw [Finset.sum_Ico_sub (f := fun n : ℕ => Real.log (n : ℝ)) h]
      have : 0 ≤ Real.log ((L0 + 1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
      linarith
  -- variation of the indicator
  have hQ := indicator_variation_anti_le_one (fun n : ℕ => 1 ≤ u n)
    (fun i h => h.trans (hustep i)) (L0 + 1) N
  have hS := (indicator_variation_and_le P (fun n : ℕ => 1 ≤ u n)
    (Finset.Ico (L0 + 1) N)).trans (add_le_add hJ hQ)
  have hM0 : (0 : ℝ) ≤ 1 / (lq * Dr) := by positivity
  have hV := variation_mul_le G (fun n : ℕ => if (P n ∧ 1 ≤ u n) then (1 : ℝ) else 0)
    (a := L0 + 1) (b := N) hM0 (fun n _ => hGM n)
    (fun n _ => by
      by_cases h : (P n ∧ 1 ≤ u n) <;> simp [h]) hVG hS
  have hfM : ∀ n ∈ Finset.Icc (L0 + 1) N,
      |G n * (if (P n ∧ 1 ≤ u n) then (1 : ℝ) else 0)| ≤ 1 / (lq * Dr) := by
    intro n _
    by_cases h : (P n ∧ 1 ≤ u n)
    · rw [if_pos h, mul_one]
      exact hGM n
    · rw [if_neg h, mul_zero, abs_zero]
      exact hM0
  have key := hC0 L0 N ((le_max_left _ _).trans hCL) hLN
    (fun n : ℕ => G n * (if (P n ∧ 1 ≤ u n) then (1 : ℝ) else 0)) (1 / (lq * Dr))
    (Real.log (N : ℝ) / lq / (lq * Dr) + 1 / (lq * Dr) * (J + 1)) hM0 hfM hV
  refine key.trans ?_
  have hr : 0 ≤ Real.log (N : ℝ) / lq := div_nonneg hlogN hlq.le
  have hbound : 1 / (lq * Dr) * (2 + Real.log (N : ℝ)) +
      (Real.log (N : ℝ) / lq / (lq * Dr) + 1 / (lq * Dr) * (J + 1)) ≤
      (2 + J + Real.log (N : ℝ) / lq) / (lq * Dr) * (2 + Real.log (N : ℝ)) := by
    have e1 : 1 / (lq * Dr) * (2 + Real.log (N : ℝ)) +
        (Real.log (N : ℝ) / lq / (lq * Dr) + 1 / (lq * Dr) * (J + 1)) =
        1 / (lq * Dr) * (2 + Real.log (N : ℝ) + Real.log (N : ℝ) / lq + J + 1) := by ring
    have e2 : (2 + J + Real.log (N : ℝ) / lq) / (lq * Dr) * (2 + Real.log (N : ℝ)) =
        1 / (lq * Dr) * ((2 + J + Real.log (N : ℝ) / lq) * (2 + Real.log (N : ℝ))) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    nlinarith [mul_nonneg hJ0 hlogN, mul_nonneg hr hlogN]
  have hK0 : 0 ≤ max C0 3 := le_trans (by norm_num) (le_max_right _ _)
  have hC0nn : 0 ≤ 1 / (lq * Dr) * (2 + Real.log (N : ℝ)) +
      (Real.log (N : ℝ) / lq / (lq * Dr) + 1 / (lq * Dr) * (J + 1)) := by positivity
  calc C0 * (1 / (lq * Dr) * (2 + Real.log (N : ℝ)) +
        (Real.log (N : ℝ) / lq / (lq * Dr) + 1 / (lq * Dr) * (J + 1))) *
        Real.log (L0 : ℝ) ^ (-A)
      ≤ max C0 3 * (1 / (lq * Dr) * (2 + Real.log (N : ℝ)) +
        (Real.log (N : ℝ) / lq / (lq * Dr) + 1 / (lq * Dr) * (J + 1))) *
        Real.log (L0 : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hC0nn) hlogL
    _ ≤ max C0 3 * ((2 + J + Real.log (N : ℝ) / lq) / (lq * Dr) * (2 + Real.log (N : ℝ))) *
        Real.log (L0 : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hK0) hlogL
    _ = _ := by ring

/-- P0069 page 51, display 5.17, the outer variables of the E4 sum. The reciprocal sum over
three outer variables up to `N` is at most the cube of the harmonic sum. -/
theorem four_triple_reciprocal (N : ℕ) :
    ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 N,
        1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)) ≤ (1 + Real.log (N : ℝ)) ^ 3 := by
  have hh : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log N := by
    have h1 := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    simpa [one_div] using h1
  have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have e3 : ∀ o1 o2 : ℕ, ∑ q ∈ Finset.Icc 1 N, 1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)) =
      1 / (o1 : ℝ) * (1 / (o2 : ℝ)) * ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) := fun o1 o2 => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [one_div_mul_one_div, one_div_mul_one_div]
  have e2 : ∀ o1 : ℕ, ∑ o2 ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 N,
      1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)) =
      1 / (o1 : ℝ) * (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ^ 2 := fun o1 => by
    simp only [e3]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  calc _ = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ)) ^ 3 := by
        simp only [e2]
        rw [← Finset.sum_mul]
        ring
    _ ≤ _ := pow_le_pow_left₀ h0 hh 3

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in one outer prime of the E4 sum which is not the level, summed over the
other three outer variables `o1`, `o2` and the level `q`. If the condition `cond` forces the
variable above `L0` and the level above `exp lam`, and along the variable its indicator has
variation at most `J`, then the fibre sums of `four_fibre_fixed_level` add up to at most a fixed
log power times `1 / log^A L0`. -/
theorem four_transfer_iterated (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L0 N : ℕ, C ≤ (L0 : ℝ) → L0 ≤ N → ∀ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω →
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω →
      ∀ (cond : ℕ → ℕ → ℕ → ℕ → Prop) [∀ o1 o2 q n, Decidable (cond o1 o2 q n)]
        (J lam μ : ℝ), 0 < lam →
      (∀ o1 o2 q n, cond o1 o2 q n → L0 < n ∧ lam ≤ Real.log (q : ℝ)) →
      (∀ o1 o2 q, ∑ i ∈ Finset.Ico (L0 + 1) N,
        |(if cond o1 o2 q (i + 1) then (1 : ℝ) else 0) -
          (if cond o1 o2 q i then (1 : ℝ) else 0)| ≤ J) →
      ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 N,
        |∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
          (if cond o1 o2 q n then
            ω ((Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
                Real.log (q : ℝ)) / Real.log (q : ℝ) /
              ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) else 0)| ≤
        C * ((2 + J + Real.log (N : ℝ) / lam) / lam) * (2 + Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 3 * Real.log (L0 : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := four_fibre_fixed_level A hA
  refine ⟨max C 1, le_trans hC0 (le_max_left _ _), ?_⟩
  intro L0 N hCL hLN ω hω hz cond _ J lam μ hlam h1 hJ
  have hL1 : (1 : ℝ) ≤ (L0 : ℝ) := (le_max_right _ _).trans hCL
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := hL1.trans (by exact_mod_cast hLN)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hJ0 : 0 ≤ J := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hJ 1 1 1)
  have hlogL : 0 ≤ Real.log (L0 : ℝ) ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hL1) _
  have hR0 : 0 ≤ (2 + J + Real.log (N : ℝ) / lam) / lam :=
    div_nonneg (by have := div_nonneg hlogN hlam.le; linarith) hlam.le
  have hW0 : 0 ≤ 2 + Real.log (N : ℝ) := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * ((2 + J + Real.log (N : ℝ) / lam) / lam) *
      (2 + Real.log (N : ℝ)) * Real.log (L0 : ℝ) ^ (-A) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0 hR0) hW0) hlogL
  have hfib : ∀ o1 ∈ Finset.Icc 1 N, ∀ o2 ∈ Finset.Icc 1 N, ∀ q ∈ Finset.Icc 1 N,
      |∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
          (if cond o1 o2 q n then
            ω ((Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
                Real.log (q : ℝ)) / Real.log (q : ℝ) /
              ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) else 0)| ≤
        K * (1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) := by
    intro o1 ho1 o2 ho2 q hq
    have ho1' : (0 : ℝ) < (o1 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho1).1
    have ho2' : (0 : ℝ) < (o2 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho2).1
    have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
    have hDr : 0 < (o1 : ℝ) * (o2 : ℝ) * (q : ℝ) := by positivity
    by_cases hex : ∃ n, cond o1 o2 q n
    · obtain ⟨n0, hn0⟩ := hex
      have hlq := (h1 _ _ _ _ hn0).2
      have hlq0 : 0 < Real.log (q : ℝ) := lt_of_lt_of_le hlam hlq
      have key := hC L0 N ((le_max_left _ _).trans hCL) hLN ω hω hz
        (fun n => cond o1 o2 q n) J (Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))))
        (Real.log (q : ℝ)) ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)) hlq0 hDr
        (fun n hn hc => by
          have := (h1 _ _ _ _ hc).1
          omega) (hJ o1 o2 q)
      refine key.trans ?_
      have h2 : Real.log (N : ℝ) / Real.log (q : ℝ) ≤ Real.log (N : ℝ) / lam :=
        div_le_div_of_nonneg_left hlogN hlam hlq
      have hfrac : (2 + J + Real.log (N : ℝ) / Real.log (q : ℝ)) /
          (Real.log (q : ℝ) * ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) ≤
          (2 + J + Real.log (N : ℝ) / lam) / lam *
            (1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) := by
        rw [div_mul_div_comm, mul_one]
        exact div_le_div₀ (by have := div_nonneg hlogN hlam.le; linarith) (by linarith)
          (mul_pos hlam hDr) (mul_le_mul_of_nonneg_right hlq hDr.le)
      calc C * ((2 + J + Real.log (N : ℝ) / Real.log (q : ℝ)) /
              (Real.log (q : ℝ) * ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)))) *
            (2 + Real.log (N : ℝ)) * Real.log (L0 : ℝ) ^ (-A)
          ≤ C * ((2 + J + Real.log (N : ℝ) / lam) / lam *
              (1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)))) *
            (2 + Real.log (N : ℝ)) * Real.log (L0 : ℝ) ^ (-A) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfrac hC0) hW0) hlogL
        _ = K * (1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) := by
            rw [hK]
            ring
    · have hex' : ∀ n, ¬ cond o1 o2 q n := fun n hn => hex ⟨n, hn⟩
      rw [Finset.sum_eq_zero fun n _ => by rw [if_neg (hex' n), mul_zero], abs_zero]
      exact mul_nonneg hK0 (by positivity)
  have hT0 : 0 ≤ (1 + Real.log (N : ℝ)) ^ 3 := by positivity
  calc _ ≤ ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 N,
          K * (1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) :=
        Finset.sum_le_sum fun o1 ho1 => Finset.sum_le_sum fun o2 ho2 =>
          Finset.sum_le_sum fun q hq => hfib o1 ho1 o2 ho2 q hq
    _ = K * ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ q ∈ Finset.Icc 1 N,
          1 / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ)) := by
        simp only [Finset.mul_sum]
    _ ≤ K * (1 + Real.log (N : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left (four_triple_reciprocal N) hK0
    _ = C * (((2 + J + Real.log (N : ℝ) / lam) / lam) * (2 + Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 3 * Real.log (L0 : ℝ) ^ (-A)) := by
        rw [hK]
        ring
    _ ≤ max C 1 * (((2 + J + Real.log (N : ℝ) / lam) / lam) * (2 + Real.log (N : ℝ)) *
          (1 + Real.log (N : ℝ)) ^ 3 * Real.log (L0 : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (mul_nonneg (mul_nonneg (mul_nonneg hR0 hW0) hT0) hlogL)
    _ = _ := by ring

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in the outer prime `p4` of the E4 sum, which is also the level of the
Buchstab density, the other outer variables held fixed. Here `t = log (m / D)` for the product
`D` of the other three variables, bounded by `τ` in absolute value, and `P` collects the order
conditions and the E4 indicator along the variable. If `P` fails up to `L0` and its indicator
has variation at most `J`, then replacing the prime indicator by the density `1 / log n` costs
at most `C (3 + J + τ / log L0) / (D log L0) (2 + log N) / log^A L0`: the weight is `1 / n`
times `ω(t / log n - 1) / log n`, a product of a function Lipschitz in `1 / log n` above the
jump of `ω` at 1 and the monotone factor `1 / log n`. -/
theorem four_fibre_level (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L0 N : ℕ, C ≤ (L0 : ℝ) → L0 ≤ N → ∀ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω →
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω →
      ∀ (P : ℕ → Prop) [DecidablePred P] (J t τ Dr : ℝ), 0 < Dr → |t| ≤ τ →
      (∀ n : ℕ, n ≤ L0 → ¬ P n) →
      ∑ i ∈ Finset.Ico (L0 + 1) N,
        |(if P (i + 1) then (1 : ℝ) else 0) - (if P i then (1 : ℝ) else 0)| ≤ J →
      |∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
          (if P n then ω ((t - Real.log (n : ℝ)) / Real.log (n : ℝ)) / Real.log (n : ℝ) /
            (Dr * (n : ℝ)) else 0)| ≤
        C * ((3 + J + τ / Real.log (L0 : ℝ)) / (Real.log (L0 : ℝ) * Dr)) *
          (2 + Real.log (N : ℝ)) * Real.log (L0 : ℝ) ^ (-A) := by
  obtain ⟨C0, hC0⟩ := four_pnt_reciprocal A hA
  refine ⟨max C0 3, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro L0 N hCL hLN ω hω hz P _ J t τ Dr hDr hτ hlow hJ
  have hL3 : (3 : ℝ) ≤ (L0 : ℝ) := (le_max_right _ _).trans hCL
  have hL1 : 1 ≤ L0 := by
    have : (1 : ℝ) ≤ (L0 : ℝ) := by linarith
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hL1.trans hLN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hJ0 : 0 ≤ J := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hJ
  have hτ0 : 0 ≤ τ := (abs_nonneg t).trans hτ
  have hlL : 0 < Real.log (L0 : ℝ) := Real.log_pos (by linarith)
  have hκ : 0 < Real.log (L0 : ℝ) * Dr := mul_pos hlL hDr
  have hlogL : 0 ≤ Real.log (L0 : ℝ) ^ (-A) := Real.rpow_nonneg hlL.le _
  -- logarithms above the cut
  have hlogge : ∀ n : ℕ, L0 + 1 ≤ n → Real.log (L0 : ℝ) ≤ Real.log (n : ℝ) := fun n hn =>
    Real.log_le_log (by linarith) (by exact_mod_cast (Nat.le_succ L0).trans hn)
  have hlogmono : ∀ i : ℕ, Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exact Real.log_le_log (by exact_mod_cast hi) (by push_cast; linarith)
  obtain ⟨g2, hg2⟩ : ∃ g2 : ℕ → ℝ, ∀ n, g2 n = 1 / Real.log (n : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = (t - Real.log (n : ℝ)) / Real.log (n : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ g1 : ℕ → ℝ, ∀ n, g1 n = ω (max (u n) 1) := ⟨_, fun _ => rfl⟩
  have hω0 : ∀ v : ℝ, 0 ≤ ω v := Decomp514a.four_density_buchstab_nonneg hω hz
  have hω1 : ∀ v : ℝ, ω v ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz
  have hg2pos : ∀ n : ℕ, L0 + 1 ≤ n → 0 < g2 n := fun n hn => by
    rw [hg2]
    exact one_div_pos.mpr (lt_of_lt_of_le hlL (hlogge n hn))
  have hg2le : ∀ n : ℕ, L0 + 1 ≤ n → g2 n ≤ 1 / Real.log (L0 : ℝ) := fun n hn => by
    rw [hg2]
    exact one_div_le_one_div_of_le hlL (hlogge n hn)
  have hg2step : ∀ i : ℕ, L0 + 1 ≤ i → g2 (i + 1) ≤ g2 i := fun i hi => by
    rw [hg2, hg2]
    exact one_div_le_one_div_of_le (lt_of_lt_of_le hlL (hlogge i hi)) (hlogmono i)
  have hueq : ∀ n : ℕ, L0 + 1 ≤ n → u n = t * g2 n - 1 := fun n hn => by
    have h0 : Real.log (n : ℝ) ≠ 0 := (lt_of_lt_of_le hlL (hlogge n hn)).ne'
    rw [hu, hg2]
    field_simp
  -- the variation of `1 / log n`
  have hVg2 : ∑ i ∈ Finset.Ico (L0 + 1) N, |g2 (i + 1) - g2 i| ≤ 1 / Real.log (L0 : ℝ) := by
    have hpt : ∀ i ∈ Finset.Ico (L0 + 1) N, |g2 (i + 1) - g2 i| =
        (fun n : ℕ => -g2 n) (i + 1) - (fun n : ℕ => -g2 n) i := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      rw [abs_of_nonpos (by linarith [hg2step i hi'.1])]
      ring
    rw [Finset.sum_congr rfl hpt]
    rcases Nat.lt_or_ge N (L0 + 1) with h | h
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [Finset.sum_Ico_sub (f := fun n : ℕ => -g2 n) h]
      have h1 := hg2pos N h
      have h2 := hg2le (L0 + 1) le_rfl
      linarith
  -- the variation of the Buchstab factor
  have hVg1 : ∑ i ∈ Finset.Ico (L0 + 1) N, |g1 (i + 1) - g1 i| ≤
      τ * (1 / Real.log (L0 : ℝ)) := by
    have hpt : ∀ i ∈ Finset.Ico (L0 + 1) N, |g1 (i + 1) - g1 i| ≤
        τ * |g2 (i + 1) - g2 i| := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      rw [hg1, hg1]
      refine (Decomp514a.four_density_buchstab_lipschitz hω hz (le_max_right _ _)
        (le_max_right _ _)).trans ?_
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [hueq i hi'.1, hueq (i + 1) (by omega)]
      have e : t * g2 (i + 1) - 1 - (t * g2 i - 1) = t * (g2 (i + 1) - g2 i) := by ring
      rw [e, abs_mul]
      exact mul_le_mul_of_nonneg_right hτ (abs_nonneg _)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hVg2 hτ0
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, ∀ n, G n = g2 n / Dr := ⟨_, fun _ => rfl⟩
  have hM0 : (0 : ℝ) ≤ 1 / (Real.log (L0 : ℝ) * Dr) := by positivity
  have hGM : ∀ n ∈ Finset.Icc (L0 + 1) N, |G n| ≤ 1 / (Real.log (L0 : ℝ) * Dr) := by
    intro n hn
    have hn' := (Finset.mem_Icc.mp hn).1
    rw [hG, abs_div, abs_of_pos hDr, abs_of_pos (hg2pos n hn'), ← div_div]
    exact div_le_div_of_nonneg_right (hg2le n hn') hDr.le
  have hVG : ∑ i ∈ Finset.Ico (L0 + 1) N, |G (i + 1) - G i| ≤
      1 / Real.log (L0 : ℝ) / Dr := by
    have hpt : ∀ i ∈ Finset.Ico (L0 + 1) N, |G (i + 1) - G i| = |g2 (i + 1) - g2 i| / Dr := by
      intro i _
      rw [hG, hG, ← sub_div, abs_div, abs_of_pos hDr]
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right hVg2 hDr.le
  have hg1le : ∀ n : ℕ, |g1 n| ≤ 1 := fun n => by
    rw [hg1, abs_of_nonneg (hω0 _)]
    exact hω1 _
  -- the smooth part `G g1`
  have hV1 := variation_mul_le G g1 (a := L0 + 1) (b := N) hM0 hGM (fun n _ => hg1le n)
    hVG hVg1
  have hGg1M : ∀ n ∈ Finset.Icc (L0 + 1) N, |G n * g1 n| ≤ 1 / (Real.log (L0 : ℝ) * Dr) := by
    intro n hn
    rw [abs_mul]
    calc |G n| * |g1 n| ≤ 1 / (Real.log (L0 : ℝ) * Dr) * 1 :=
          mul_le_mul (hGM n hn) (hg1le n) (abs_nonneg _) hM0
      _ = _ := mul_one _
  -- the indicator
  have hQ := indicator_variation_anti_le_one (fun n : ℕ => 2 * Real.log (n : ℝ) ≤ t)
    (fun i h => by
      have := hlogmono i
      linarith) (L0 + 1) N
  have hS := (indicator_variation_and_le P (fun n : ℕ => 2 * Real.log (n : ℝ) ≤ t)
    (Finset.Ico (L0 + 1) N)).trans (add_le_add hJ hQ)
  have hV2 := variation_mul_le (fun n : ℕ => G n * g1 n)
    (fun n : ℕ => if (P n ∧ 2 * Real.log (n : ℝ) ≤ t) then (1 : ℝ) else 0)
    (a := L0 + 1) (b := N) hM0 hGg1M
    (fun n _ => by
      by_cases h : (P n ∧ 2 * Real.log (n : ℝ) ≤ t) <;> simp [h]) hV1 hS
  have hfM : ∀ n ∈ Finset.Icc (L0 + 1) N,
      |G n * g1 n * (if (P n ∧ 2 * Real.log (n : ℝ) ≤ t) then (1 : ℝ) else 0)| ≤
        1 / (Real.log (L0 : ℝ) * Dr) := by
    intro n hn
    by_cases h : (P n ∧ 2 * Real.log (n : ℝ) ≤ t)
    · rw [if_pos h, mul_one]
      exact hGg1M n hn
    · rw [if_neg h, mul_zero, abs_zero]
      exact hM0
  -- restrict to (L0, N]
  have hsub : Finset.Ioc L0 N ⊆ Finset.Icc 1 N := fun n hn => by
    have := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hsplit : ∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
        (if P n then ω ((t - Real.log (n : ℝ)) / Real.log (n : ℝ)) / Real.log (n : ℝ) /
          (Dr * (n : ℝ)) else 0) =
      ∑ n ∈ Finset.Ioc L0 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
        ((G n * g1 n * (if (P n ∧ 2 * Real.log (n : ℝ) ≤ t) then (1 : ℝ) else 0)) /
          (n : ℝ)) := by
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn' := Finset.mem_Ioc.mp hn
      have hln : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlL (hlogge n (by omega))
      have hQiff : 2 * Real.log (n : ℝ) ≤ t ↔ 1 ≤ u n := by
        rw [hu, le_div_iff₀ hln]
        constructor <;> intro h <;> linarith
      congr 1
      by_cases hP : P n
      · by_cases hQ : 2 * Real.log (n : ℝ) ≤ t
        · rw [if_pos hP, if_pos ⟨hP, hQ⟩, hG, hg1, hg2, max_eq_left (hQiff.mp hQ), hu]
          field_simp
        · have hu1 : u n < 1 := not_le.mp (fun h => hQ (hQiff.mpr h))
          rw [if_pos hP, if_neg (fun h => hQ h.2), ← hu, hz _ hu1]
          simp
      · rw [if_neg hP, if_neg (fun h => hP h.1)]
        simp
    · intro n hn hn'
      have hn1 := Finset.mem_Icc.mp hn
      have hnL : n ≤ L0 := by
        by_contra h
        exact hn' (Finset.mem_Ioc.mpr ⟨by omega, hn1.2⟩)
      rw [if_neg (hlow n hnL)]
      simp
  rw [hsplit]
  have key := hC0 L0 N ((le_max_left _ _).trans hCL) hLN
    (fun n : ℕ => G n * g1 n * (if (P n ∧ 2 * Real.log (n : ℝ) ≤ t) then (1 : ℝ) else 0))
    (1 / (Real.log (L0 : ℝ) * Dr))
    (1 / Real.log (L0 : ℝ) / Dr + 1 / (Real.log (L0 : ℝ) * Dr) * (τ * (1 / Real.log (L0 : ℝ))) +
      1 / (Real.log (L0 : ℝ) * Dr) * (J + 1)) hM0 hfM hV2
  refine key.trans ?_
  have hr : 0 ≤ τ / Real.log (L0 : ℝ) := div_nonneg hτ0 hlL.le
  have hbound : 1 / (Real.log (L0 : ℝ) * Dr) * (2 + Real.log (N : ℝ)) +
      (1 / Real.log (L0 : ℝ) / Dr +
        1 / (Real.log (L0 : ℝ) * Dr) * (τ * (1 / Real.log (L0 : ℝ))) +
        1 / (Real.log (L0 : ℝ) * Dr) * (J + 1)) ≤
      (3 + J + τ / Real.log (L0 : ℝ)) / (Real.log (L0 : ℝ) * Dr) *
        (2 + Real.log (N : ℝ)) := by
    have e1 : 1 / (Real.log (L0 : ℝ) * Dr) * (2 + Real.log (N : ℝ)) +
        (1 / Real.log (L0 : ℝ) / Dr +
          1 / (Real.log (L0 : ℝ) * Dr) * (τ * (1 / Real.log (L0 : ℝ))) +
          1 / (Real.log (L0 : ℝ) * Dr) * (J + 1)) =
        1 / (Real.log (L0 : ℝ) * Dr) *
          (2 + Real.log (N : ℝ) + 1 + τ / Real.log (L0 : ℝ) + J + 1) := by
      field_simp
      ring
    have e2 : (3 + J + τ / Real.log (L0 : ℝ)) / (Real.log (L0 : ℝ) * Dr) *
        (2 + Real.log (N : ℝ)) =
        1 / (Real.log (L0 : ℝ) * Dr) *
          ((3 + J + τ / Real.log (L0 : ℝ)) * (2 + Real.log (N : ℝ))) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    nlinarith [mul_nonneg hJ0 hlogN, mul_nonneg hr hlogN]
  have hK0 : 0 ≤ max C0 3 := le_trans (by norm_num) (le_max_right _ _)
  have hC0nn : 0 ≤ 1 / (Real.log (L0 : ℝ) * Dr) * (2 + Real.log (N : ℝ)) +
      (1 / Real.log (L0 : ℝ) / Dr +
        1 / (Real.log (L0 : ℝ) * Dr) * (τ * (1 / Real.log (L0 : ℝ))) +
        1 / (Real.log (L0 : ℝ) * Dr) * (J + 1)) := by positivity
  calc C0 * (1 / (Real.log (L0 : ℝ) * Dr) * (2 + Real.log (N : ℝ)) +
        (1 / Real.log (L0 : ℝ) / Dr +
          1 / (Real.log (L0 : ℝ) * Dr) * (τ * (1 / Real.log (L0 : ℝ))) +
          1 / (Real.log (L0 : ℝ) * Dr) * (J + 1))) * Real.log (L0 : ℝ) ^ (-A)
      ≤ max C0 3 * (1 / (Real.log (L0 : ℝ) * Dr) * (2 + Real.log (N : ℝ)) +
        (1 / Real.log (L0 : ℝ) / Dr +
          1 / (Real.log (L0 : ℝ) * Dr) * (τ * (1 / Real.log (L0 : ℝ))) +
          1 / (Real.log (L0 : ℝ) * Dr) * (J + 1))) * Real.log (L0 : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hC0nn) hlogL
    _ ≤ max C0 3 * ((3 + J + τ / Real.log (L0 : ℝ)) / (Real.log (L0 : ℝ) * Dr) *
        (2 + Real.log (N : ℝ))) * Real.log (L0 : ℝ) ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hK0) hlogL
    _ = _ := by ring

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in the outer prime `p4` of the E4 sum, the level, summed over the other
three outer variables. If the condition `cond` forces the variable above `L0` and along the
variable its indicator has variation at most `J`, then the fibre sums of `four_fibre_level` add
up to at most a fixed log power times `1 / log^A L0`. Here `1 ≤ μ ≤ N` is the point `m`. -/
theorem four_transfer_iterated_level (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L0 N : ℕ, C ≤ (L0 : ℝ) → L0 ≤ N → ∀ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω →
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω →
      ∀ (cond : ℕ → ℕ → ℕ → ℕ → Prop) [∀ o1 o2 o3 n, Decidable (cond o1 o2 o3 n)]
        (J μ : ℝ), 1 ≤ μ → μ ≤ (N : ℝ) →
      (∀ o1 o2 o3 n, cond o1 o2 o3 n → L0 < n) →
      (∀ o1 o2 o3, ∑ i ∈ Finset.Ico (L0 + 1) N,
        |(if cond o1 o2 o3 (i + 1) then (1 : ℝ) else 0) -
          (if cond o1 o2 o3 i then (1 : ℝ) else 0)| ≤ J) →
      ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ o3 ∈ Finset.Icc 1 N,
        |∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
          (if cond o1 o2 o3 n then
            ω ((Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))) - Real.log (n : ℝ)) /
                Real.log (n : ℝ)) / Real.log (n : ℝ) /
              ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) * (n : ℝ)) else 0)| ≤
        C * ((3 + J + 4 * Real.log (N : ℝ) / Real.log (L0 : ℝ)) / Real.log (L0 : ℝ)) *
          (2 + Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) ^ 3 *
          Real.log (L0 : ℝ) ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := four_fibre_level A hA
  refine ⟨max C 3, le_trans hC0 (le_max_left _ _), ?_⟩
  intro L0 N hCL hLN ω hω hz cond _ J μ hμ1 hμN h1 hJ
  have hL3 : (3 : ℝ) ≤ (L0 : ℝ) := (le_max_right _ _).trans hCL
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlL : 0 < Real.log (L0 : ℝ) := Real.log_pos (by linarith)
  have hJ0 : 0 ≤ J := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hJ 1 1 1)
  have hlogL : 0 ≤ Real.log (L0 : ℝ) ^ (-A) := Real.rpow_nonneg hlL.le _
  have hR0 : 0 ≤ (3 + J + 4 * Real.log (N : ℝ) / Real.log (L0 : ℝ)) / Real.log (L0 : ℝ) :=
    div_nonneg (by
      have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlogN) hlL.le
      linarith) hlL.le
  have hW0 : 0 ≤ 2 + Real.log (N : ℝ) := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C *
      ((3 + J + 4 * Real.log (N : ℝ) / Real.log (L0 : ℝ)) / Real.log (L0 : ℝ)) *
      (2 + Real.log (N : ℝ)) * Real.log (L0 : ℝ) ^ (-A) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0 hR0) hW0) hlogL
  have hlogμ0 : 0 ≤ Real.log μ := Real.log_nonneg hμ1
  have hlogμN : Real.log μ ≤ Real.log (N : ℝ) := Real.log_le_log (by linarith) hμN
  have hfib : ∀ o1 ∈ Finset.Icc 1 N, ∀ o2 ∈ Finset.Icc 1 N, ∀ o3 ∈ Finset.Icc 1 N,
      |∑ n ∈ Finset.Icc 1 N, (primeWeight n - 1 / Real.log (n : ℝ)) *
          (if cond o1 o2 o3 n then
            ω ((Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))) - Real.log (n : ℝ)) /
                Real.log (n : ℝ)) / Real.log (n : ℝ) /
              ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) * (n : ℝ)) else 0)| ≤
        K * (1 / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))) := by
    intro o1 ho1 o2 ho2 o3 ho3
    have hb : ∀ o ∈ Finset.Icc 1 N, (1 : ℝ) ≤ (o : ℝ) ∧ Real.log (o : ℝ) ≤ Real.log (N : ℝ) ∧
        0 ≤ Real.log (o : ℝ) := fun o ho => by
      have ho' := Finset.mem_Icc.mp ho
      have h1o : (1 : ℝ) ≤ (o : ℝ) := by exact_mod_cast ho'.1
      exact ⟨h1o, Real.log_le_log (by linarith) (by exact_mod_cast ho'.2), Real.log_nonneg h1o⟩
    obtain ⟨p1, q1, r1⟩ := hb o1 ho1
    obtain ⟨p2, q2, r2⟩ := hb o2 ho2
    obtain ⟨p3, q3, r3⟩ := hb o3 ho3
    have hDr : 0 < (o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) := by positivity
    have ht : |Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ)))| ≤ 4 * Real.log (N : ℝ) := by
      rw [Real.log_div (by linarith) hDr.ne', Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), abs_le]
      constructor <;> linarith
    have key := hC L0 N ((le_max_left _ _).trans hCL) hLN ω hω hz
      (fun n => cond o1 o2 o3 n) J (Real.log (μ / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))))
      (4 * Real.log (N : ℝ)) ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ)) hDr ht
      (fun n hn hc => by
        have := h1 _ _ _ _ hc
        omega) (hJ o1 o2 o3)
    refine key.trans (le_of_eq ?_)
    rw [hK]
    field_simp
  have hT0 : 0 ≤ (1 + Real.log (N : ℝ)) ^ 3 := by positivity
  calc _ ≤ ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ o3 ∈ Finset.Icc 1 N,
          K * (1 / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))) :=
        Finset.sum_le_sum fun o1 ho1 => Finset.sum_le_sum fun o2 ho2 =>
          Finset.sum_le_sum fun o3 ho3 => hfib o1 ho1 o2 ho2 o3 ho3
    _ = K * ∑ o1 ∈ Finset.Icc 1 N, ∑ o2 ∈ Finset.Icc 1 N, ∑ o3 ∈ Finset.Icc 1 N,
          1 / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ)) := by
        simp only [Finset.mul_sum]
    _ ≤ K * (1 + Real.log (N : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left (four_triple_reciprocal N) hK0
    _ = C * (((3 + J + 4 * Real.log (N : ℝ) / Real.log (L0 : ℝ)) / Real.log (L0 : ℝ)) *
          (2 + Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) ^ 3 * Real.log (L0 : ℝ) ^ (-A)) := by
        rw [hK]
        ring
    _ ≤ max C 3 * (((3 + J + 4 * Real.log (N : ℝ) / Real.log (L0 : ℝ)) / Real.log (L0 : ℝ)) *
          (2 + Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) ^ 3 * Real.log (L0 : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (mul_nonneg (mul_nonneg (mul_nonneg hR0 hW0) hT0) hlogL)
    _ = _ := by ring

/-- P0069 page 51, display 5.17, the exponent `β = log p / log Z` of pages 50 and 51 is
nondecreasing in `p` once `Z > 1`. -/
theorem four_expo_monotone {ε x : ℝ} (hZ : 1 < scaleZ ε x) : Monotone (expo ε x) := by
  intro a b hab
  unfold expo
  refine div_le_div_of_nonneg_right ?_ (Real.log_nonneg hZ.le)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)

/-- P0069 page 51, display 5.17, the outer variables of the E4 sum: a sum over a filtered
fourfold product is an iterated sum with the condition written out. -/
theorem four_sum_filter_iter (B : Finset ℕ) (p : ℕ × ℕ × ℕ × ℕ → Prop) [DecidablePred p]
    (F : ℕ × ℕ × ℕ × ℕ → ℝ) :
    ∑ i ∈ (B ×ˢ B ×ˢ B ×ˢ B).filter p, F i =
      ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, ∑ d ∈ B, if p (a, b, c, d) then F (a, b, c, d) else 0 := by
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]

/-- P0069 page 51, display 5.17, partial summation in `p1`: the first of four summation
variables is moved to the innermost place. -/
theorem four_rot_first (B : Finset ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, ∑ d ∈ B, G a b c d =
      ∑ b ∈ B, ∑ c ∈ B, ∑ d ∈ B, ∑ a ∈ B, G a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finset.sum_comm

/-- P0069 page 51, display 5.17, partial summation in `p2`: the second of four summation
variables is moved to the innermost place. -/
theorem four_rot_second (B : Finset ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, ∑ d ∈ B, G a b c d =
      ∑ a ∈ B, ∑ c ∈ B, ∑ d ∈ B, ∑ b ∈ B, G a b c d := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finset.sum_comm

/-- P0069 page 51, display 5.17, partial summation in `p3`: the third of four summation
variables is moved to the innermost place. -/
theorem four_rot_third (B : Finset ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B, ∑ d ∈ B, G a b c d =
      ∑ a ∈ B, ∑ b ∈ B, ∑ d ∈ B, ∑ c ∈ B, G a b c d := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact Finset.sum_comm

/-- P0069 page 51, display 5.17, partial summation in one outer prime: weights bounded by 2 on
the other three outer variables are taken out of the fibre sums at the cost of a factor 8. -/
theorem four_iterated_abs_le (B : Finset ℕ) (a1 a2 a3 : ℕ → ℝ) (h1 : ∀ n, |a1 n| ≤ 2)
    (h2 : ∀ n, |a2 n| ≤ 2) (h3 : ∀ n, |a3 n| ≤ 2) (T : ℕ → ℕ → ℕ → ℕ → ℝ) :
    |∑ o1 ∈ B, ∑ o2 ∈ B, ∑ q ∈ B, ∑ n ∈ B, a1 o1 * a2 o2 * a3 q * T o1 o2 q n| ≤
      8 * ∑ o1 ∈ B, ∑ o2 ∈ B, ∑ q ∈ B, |∑ n ∈ B, T o1 o2 q n| := by
  have hpt : ∀ o1 o2 q : ℕ, |∑ n ∈ B, a1 o1 * a2 o2 * a3 q * T o1 o2 q n| ≤
      8 * |∑ n ∈ B, T o1 o2 q n| := by
    intro o1 o2 q
    rw [← Finset.mul_sum, abs_mul, abs_mul, abs_mul]
    have hS := abs_nonneg (∑ n ∈ B, T o1 o2 q n)
    have h12 : |a1 o1| * |a2 o2| ≤ 2 * 2 :=
      mul_le_mul (h1 o1) (h2 o2) (abs_nonneg _) (by norm_num)
    have h123 : |a1 o1| * |a2 o2| * |a3 q| ≤ 2 * 2 * 2 :=
      mul_le_mul h12 (h3 q) (abs_nonneg _) (by norm_num)
    calc |a1 o1| * |a2 o2| * |a3 q| * |∑ n ∈ B, T o1 o2 q n|
        ≤ 2 * 2 * 2 * |∑ n ∈ B, T o1 o2 q n| := mul_le_mul_of_nonneg_right h123 hS
      _ = 8 * |∑ n ∈ B, T o1 o2 q n| := by ring
  calc _ ≤ ∑ o1 ∈ B, |∑ o2 ∈ B, ∑ q ∈ B, ∑ n ∈ B, a1 o1 * a2 o2 * a3 q * T o1 o2 q n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o1 ∈ B, ∑ o2 ∈ B, |∑ q ∈ B, ∑ n ∈ B, a1 o1 * a2 o2 * a3 q * T o1 o2 q n| :=
        Finset.sum_le_sum fun o1 _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o1 ∈ B, ∑ o2 ∈ B, ∑ q ∈ B, |∑ n ∈ B, a1 o1 * a2 o2 * a3 q * T o1 o2 q n| :=
        Finset.sum_le_sum fun o1 _ => Finset.sum_le_sum fun o2 _ =>
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ o1 ∈ B, ∑ o2 ∈ B, ∑ q ∈ B, 8 * |∑ n ∈ B, T o1 o2 q n| :=
        Finset.sum_le_sum fun o1 _ => Finset.sum_le_sum fun o2 _ =>
          Finset.sum_le_sum fun q _ => hpt o1 o2 q
    _ = _ := by simp only [Finset.mul_sum]

/-- P0069 page 51, display 5.17, the argument of `ω` in the E4 sum: with one outer variable `n`
split off the product, `log (m / (D n)) = log (m / D) - log n`. -/
theorem four_phi_split {μ D n : ℝ} (hμ : 0 < μ) (hD : 0 < D) (hn : 0 < n) :
    Real.log (μ / (D * n)) = Real.log (μ / D) - Real.log n := by
  rw [← div_div, Real.log_div (by positivity) hn.ne']

set_option maxHeartbeats 400000 in
/-- P0069 page 51, display 5.17 with page 3: the scales of the partial summation in one outer
prime. For large `x`, with `Y = x ^ (11/20 + ε)`, `Z = 4 Y`, `N = ⌊2 Y⌋` and the cut
`L0 = ⌊x ^ (11/200) / 2⌋`: `L0` exceeds any fixed constant and is at most `N`, `log Z ≥ 10`,
every `n` with exponent at least `1 / 10` exceeds `L0`, `log N ≤ log Z`, and the bound of
`four_transfer_iterated` with saving `log^(A + 4) L0` is `O(log^(-A) x)`. -/
theorem four_transfer_scales {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (A : ℝ) (hA : 0 < A)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      1 ≤ x ∧ K ≤ ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ∧
      ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ ∧
      10 ≤ Real.log (scaleZ ε x) ∧
      (∀ n : ℕ, Real.log (scaleZ ε x) / 10 ≤ Real.log (n : ℝ) → ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ < n) ∧
      8 * (K * ((2 + 603 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / (Real.log (scaleZ ε x) / 10)) /
            (Real.log (scaleZ ε x) / 10)) * (2 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) *
          (1 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) ^ 3 *
          Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (-(A + 4))) ≤ C * Real.log x ^ (-A) ∧
      8 * (K * ((3 + 603 + 4 * Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ)) /
            Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ)) * (2 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) *
          (1 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) ^ 3 *
          Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (-(A + 4))) ≤ C * Real.log x ^ (-A) := by
  refine ⟨max (max ((4 : ℝ) ^ 200) (K ^ 20)) (max (Real.exp 20) (5488 * K * (20 : ℝ) ^ (A + 4))),
    fun x hx => ?_⟩
  have h4 : (4 : ℝ) ^ 200 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hK20 : K ^ 20 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxe : Real.exp 20 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hCf : 5488 * K * (20 : ℝ) ^ (A + 4) ≤
      max (max ((4 : ℝ) ^ 200) (K ^ 20)) (max (Real.exp 20) (5488 * K * (20 : ℝ) ^ (A + 4))) :=
    (le_max_right _ _).trans (le_max_right _ _)
  generalize max (max ((4 : ℝ) ^ 200) (K ^ 20))
    (max (Real.exp 20) (5488 * K * (20 : ℝ) ^ (A + 4))) = C at hx hCf ⊢
  have hx1 : (1 : ℝ) ≤ x := le_trans (one_le_pow₀ (by norm_num)) h4
  have hxpos : 0 < x := by linarith
  have hl20 : 20 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have hlpos : 0 < Real.log x := by linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hxpos _
  have hlY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x := Real.log_rpow hxpos _
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlZ : Real.log (scaleZ ε x) = Real.log 4 + (11 / 20 + ε) * Real.log x := by
    unfold scaleZ shortY
    rw [Real.log_mul (by norm_num) hYpos.ne', hlY]
  have hprod : (11 / 20 + ε) * Real.log x = 11 / 20 * Real.log x + ε * Real.log x := by ring
  have hεl : 0 ≤ ε * Real.log x := mul_nonneg hε.le hlpos.le
  have hεl2 : ε * Real.log x ≤ 1 / 20 * Real.log x :=
    mul_le_mul_of_nonneg_right (by norm_num at hε8 ⊢; linarith) hlpos.le
  have hlZ10 : 10 ≤ Real.log (scaleZ ε x) := by
    rw [hlZ]
    linarith
  have hlZpos : 0 < Real.log (scaleZ ε x) := by linarith
  -- the cut
  have hx200 : (4 : ℝ) ≤ x ^ (1 / 200 : ℝ) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (200 : ℕ)) ^ (1 / 200 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ x ^ (1 / 200 : ℝ) := Real.rpow_le_rpow (by positivity) h4 (by norm_num)
  have hx20 : (1 : ℝ) ≤ x ^ (1 / 20 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hPsplit : x ^ (11 / 200 : ℝ) = x ^ (1 / 20 : ℝ) * x ^ (1 / 200 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hP4 : 4 * x ^ (1 / 20 : ℝ) ≤ x ^ (11 / 200 : ℝ) := by
    rw [hPsplit]
    nlinarith
  have hPpos : 0 < x ^ (11 / 200 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hL0le : ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ x ^ (11 / 200 : ℝ) / 2 := Nat.floor_le (by positivity)
  have hL0gt : x ^ (11 / 200 : ℝ) / 2 < ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hL0big : x ^ (1 / 20 : ℝ) ≤ ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) := by linarith
  have hKx : K ≤ x ^ (1 / 20 : ℝ) := by
    by_contra h
    have h' := not_le.mp h
    have h1 : (x ^ (1 / 20 : ℝ)) ^ (20 : ℕ) < K ^ 20 :=
      pow_lt_pow_left₀ h' (by positivity) (by norm_num)
    have e : (x ^ (1 / 20 : ℝ)) ^ (20 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      norm_num
    linarith
  clear h4 hK20 hx hxe
  have hPY : x ^ (11 / 200 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hL0N : ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.floor_mono (by linarith)
  have hNle : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := Nat.floor_le (by positivity)
  have hN1 : (1 : ℝ) ≤ ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) :=
    (hx20.trans hL0big).trans (by exact_mod_cast hL0N)
  have hlogN0 : 0 ≤ Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := Real.log_nonneg hN1
  have hlogNZ : Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ Real.log (scaleZ ε x) := by
    refine Real.log_le_log (by linarith) ?_
    unfold scaleZ shortY
    linarith
  have hlogNx : Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ Real.log 2 + (11 / 20 + ε) * Real.log x := by
    have h1 := Real.log_le_log (by linarith) hNle
    rwa [Real.log_mul (by norm_num) hYpos.ne', hlY] at h1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hW : 2 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ Real.log x := by linarith
  have hT : 1 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ Real.log x := by linarith
  refine ⟨hx1, hKx.trans hL0big, hL0N, hlZ10, ?_, ?_⟩
  · intro n hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, Real.log_zero] at hn
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hPn : x ^ (11 / 200 : ℝ) ≤ (n : ℝ) := by
      rw [Real.rpow_def_of_pos hxpos, ← Real.exp_log hnpos]
      refine Real.exp_le_exp.mpr ?_
      rw [hlZ] at hn
      linarith
    have : ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  · have hlam : (1 : ℝ) ≤ Real.log (scaleZ ε x) / 10 := by linarith
    have hlam0 : (0 : ℝ) < Real.log (scaleZ ε x) / 10 := by linarith
    have hr : Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / (Real.log (scaleZ ε x) / 10) ≤ 10 := by
      rw [div_le_iff₀ hlam0]
      linarith
    have hr0 : 0 ≤ Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / (Real.log (scaleZ ε x) / 10) := div_nonneg hlogN0 hlam0.le
    have hR : (2 + 603 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / (Real.log (scaleZ ε x) / 10)) / (Real.log (scaleZ ε x) / 10) ≤ 615 := by
      rw [div_le_iff₀ hlam0]
      linarith
    have hR0 : 0 ≤ (2 + 603 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / (Real.log (scaleZ ε x) / 10)) / (Real.log (scaleZ ε x) / 10) :=
      div_nonneg (by linarith) hlam0.le
    have hW0 : 0 ≤ 2 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by linarith
    have hT0 : 0 ≤ 1 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by linarith
    -- the saving
    have hg : Real.log (x ^ (1 / 20 : ℝ)) = 1 / 20 * Real.log x := Real.log_rpow hxpos _
    have hlogL0 : 1 / 20 * Real.log x ≤ Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) := by
      rw [← hg]
      exact Real.log_le_log (by linarith) hL0big
    have hg0 : 0 < 1 / 20 * Real.log x := by linarith
    have hLpos : 0 < Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) := by linarith
    have hA4 : 0 ≤ A + 4 := by linarith
    have hLp0 : 0 ≤ Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (-(A + 4)) := Real.rpow_nonneg hLpos.le _
    have hsave : Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (-(A + 4)) ≤
        (20 : ℝ) ^ (A + 4) * Real.log x ^ (-(A + 4)) := by
      have e1 : Real.log x ^ (A + 4) = (20 : ℝ) ^ (A + 4) * (1 / 20 * Real.log x) ^ (A + 4) := by
        rw [← Real.mul_rpow (by norm_num) hg0.le]
        congr 1
        ring
      have e2 : (1 / 20 * Real.log x) ^ (A + 4) ≤ Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (A + 4) :=
        Real.rpow_le_rpow hg0.le hlogL0 hA4
      have ha : 0 < Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (A + 4) := Real.rpow_pos_of_pos hLpos _
      have hb : 0 < Real.log x ^ (A + 4) := Real.rpow_pos_of_pos hlpos _
      have ht : 0 < (20 : ℝ) ^ (A + 4) := Real.rpow_pos_of_pos (by norm_num) _
      rw [Real.rpow_neg hLpos.le, Real.rpow_neg hlpos.le, ← div_eq_mul_inv,
        le_div_iff₀ hb, inv_mul_le_iff₀ ha]
      rw [e1]
      calc (20 : ℝ) ^ (A + 4) * (1 / 20 * Real.log x) ^ (A + 4)
          ≤ (20 : ℝ) ^ (A + 4) * Real.log (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℝ) ^ (A + 4) :=
            mul_le_mul_of_nonneg_left e2 ht.le
        _ = _ := mul_comm _ _
    have hpow : Real.log x ^ (4 : ℕ) * Real.log x ^ (-(A + 4)) = Real.log x ^ (-A) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hlpos]
      congr 1
      push_cast
      ring
    have hlxp0 : 0 ≤ Real.log x ^ (-(A + 4)) := Real.rpow_nonneg hlpos.le _
    have h20 : 0 ≤ (20 : ℝ) ^ (A + 4) := Real.rpow_nonneg (by norm_num) _
    have hlA0 : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlpos.le _
    have fin : ∀ R : ℝ, 0 ≤ R → R ≤ 686 →
        8 * (K * R * (2 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) *
          (1 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) ^ 3 *
          Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (-(A + 4))) ≤ C * Real.log x ^ (-A) := by
      intro R _ hR686
      have m1 := mul_le_mul_of_nonneg_left hR686 hK
      have m2 := mul_le_mul m1 hW hW0 (mul_nonneg hK (by norm_num))
      have m3 := mul_le_mul m2 (pow_le_pow_left₀ hT0 hT 3) (pow_nonneg hT0 3)
        (mul_nonneg (mul_nonneg hK (by norm_num)) hlpos.le)
      have m4 := mul_le_mul m3 hsave hLp0
        (mul_nonneg (mul_nonneg (mul_nonneg hK (by norm_num)) hlpos.le)
          (pow_nonneg hlpos.le 3))
      calc 8 * (K * R * (2 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) *
            (1 + Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ)) ^ 3 *
            Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ^ (-(A + 4)))
          ≤ 8 * (K * 686 * Real.log x * Real.log x ^ 3 *
              ((20 : ℝ) ^ (A + 4) * Real.log x ^ (-(A + 4)))) :=
            mul_le_mul_of_nonneg_left m4 (by norm_num)
        _ = 5488 * K * (20 : ℝ) ^ (A + 4) *
              (Real.log x ^ (4 : ℕ) * Real.log x ^ (-(A + 4))) := by ring
        _ = 5488 * K * (20 : ℝ) ^ (A + 4) * Real.log x ^ (-A) := by rw [hpow]
        _ ≤ _ := mul_le_mul_of_nonneg_right hCf hlA0
    have hLL1 : (1 : ℝ) ≤ Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) := by linarith
    have hr2 : 4 * Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ 80 := by
      rw [div_le_iff₀ hLpos]
      linarith
    have hr20 : 0 ≤ 4 * Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) :=
      div_nonneg (by linarith) hLpos.le
    have hR2 : (3 + 603 + 4 * Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ)) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ 686 := by
      rw [div_le_iff₀ hLpos]
      linarith
    have hR20 : 0 ≤ (3 + 603 + 4 * Real.log ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ)) / Real.log ((⌊x ^ (11 / 200 : ℝ) / 2⌋₊ : ℕ) : ℝ) :=
      div_nonneg (by linarith) hLpos.le
    exact ⟨fin _ hR0 (hR.trans (by norm_num)), fin _ hR20 hR2⟩


/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in the outer prime `p1` of the E4 sum at one point `m` of J, the other
three outer variables held fixed with arbitrary weights bounded by 2: the statement of
`leaf_four_transfer_p1`. Replacing the prime indicator of `p1` by the density
`1 / log n` changes the sum by every log power. Proved from `four_transfer_iterated`, the prime
number theorem with partial summation, and `four_region_jumps` of `FourDensityMain517b.lean`. -/
theorem four_transfer_p1 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a2 a3 a4 : ℕ → ℝ, (∀ n, |a2 n| ≤ 2) → (∀ n, |a3 n| ≤ 2) → (∀ n, |a4 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          (primeWeight i.1 - 1 / Real.log (i.1 : ℝ)) * a2 i.2.1 * a3 i.2.2.1 * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨K, hK0, happ⟩ := four_transfer_iterated (A + 4) (by linarith)
  obtain ⟨C, hC⟩ := four_transfer_scales hε hε8 A hA K hK0
  refine ⟨C, fun x hx m hm1 hm2 a2 a3 a4 hb1 hb2 hb3 => ?_⟩
  obtain ⟨hx1, s1, s2, s3, s4, sfin, -⟩ := hC x hx
  have hlZ0 : 0 < Real.log (scaleZ ε x) := by linarith
  have hZ1 : 1 < scaleZ ε x := (scaleZ_rpow_ge hε hε8 hx1).2
  have hmono : Monotone (expo ε x) := four_expo_monotone hZ1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hm1
  have key := happ ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ s1 s2 ω hω hz
    (fun o1 o2 q n : ℕ => o1 < n ∧ o2 < o1 ∧ q < o2 ∧
        lowerFourRegion ε (expo ε x n) (expo ε x o1) (expo ε x o2) (expo ε x q))
    603 (Real.log (scaleZ ε x) / 10) (m : ℝ) (by linarith)
    (fun o1 o2 q n hc => by
      obtain ⟨hd, hdc, hcb, hba, -, -⟩ := Decomp514a.four_density_region_box hε hε8 hc.2.2.2
      have hq' : 1 / 10 ≤ Real.log (q : ℝ) / Real.log (scaleZ ε x) := hd
      have hn' : 1 / 10 ≤ Real.log (n : ℝ) / Real.log (scaleZ ε x) := by
        have h1 : expo ε x n = Real.log (n : ℝ) / Real.log (scaleZ ε x) := rfl
        rw [← h1]
        linarith
      have hq2 := (le_div_iff₀ hlZ0).mp hq'
      have hn2 := (le_div_iff₀ hlZ0).mp hn'
      exact ⟨s4 n (by linarith), by linarith⟩)
    (fun o1 o2 q => by
      have r := four_region_jumps ε (expo ε x) hmono 0 1 (expo ε x o1) 0 (expo ε x o2) 0 (expo ε x q) 0
        (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      simp only [zero_add, one_mul, zero_mul, add_zero] at r
      have j1 := indicator_variation_mono_le_one (fun n : ℕ => o1 < n)
        (fun i h => by omega) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j2 := indicator_variation_mono_le_one (fun _ : ℕ => o2 < o1)
        (fun _ h => h) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j3 := indicator_variation_mono_le_one (fun _ : ℕ => q < o2)
        (fun _ h => h) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have k3 := (indicator_variation_and_le (fun n : ℕ => q < o2)
        (fun n : ℕ => lowerFourRegion ε (expo ε x n) (expo ε x o1) (expo ε x o2) (expo ε x q)) _).trans (add_le_add j3 r)
      have k2 := (indicator_variation_and_le (fun n : ℕ => o2 < o1)
        (fun n : ℕ => q < o2 ∧ lowerFourRegion ε (expo ε x n) (expo ε x o1) (expo ε x o2) (expo ε x q)) _).trans (add_le_add j2 k3)
      have k1 := (indicator_variation_and_le (fun n : ℕ => o1 < n)
        (fun n : ℕ => o2 < o1 ∧ q < o2 ∧ lowerFourRegion ε (expo ε x n) (expo ε x o1) (expo ε x o2) (expo ε x q)) _).trans (add_le_add j1 k2)
      exact k1.trans (by norm_num))
  have hre : ∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          (primeWeight i.1 - 1 / Real.log (i.1 : ℝ)) * a2 i.2.1 * a3 i.2.2.1 * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) =
      ∑ o1 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ o2 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ q ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, a2 o1 * a3 o2 * a4 q *
          ((primeWeight n - 1 / Real.log (n : ℝ)) *
            (if o1 < n ∧ o2 < o1 ∧ q < o2 ∧
        lowerFourRegion ε (expo ε x n) (expo ε x o1) (expo ε x o2) (expo ε x q) then
              ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
              Real.log (q : ℝ)) / Real.log (q : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) else 0)) := by
    rw [four_sum_filter_iter, four_rot_first]
    refine Finset.sum_congr rfl fun o1 ho1 => Finset.sum_congr rfl fun o2 ho2 =>
      Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun n hn => ?_
    have ho1' : (0 : ℝ) < (o1 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho1).1
    have ho2' : (0 : ℝ) < (o2 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho2).1
    have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hΦ : ω (Real.log ((m : ℝ) / ((n : ℝ) * (o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) / Real.log (q : ℝ)) /
            Real.log (q : ℝ) / ((n : ℝ) * (o1 : ℝ) * (o2 : ℝ) * (q : ℝ)) =
        ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
              Real.log (q : ℝ)) / Real.log (q : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) := by
      have e : (n : ℝ) * (o1 : ℝ) * (o2 : ℝ) * (q : ℝ) = (o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ) := by ring
      rw [e, four_phi_split hm0 (by positivity) hn']
    dsimp only
    split_ifs with g1
    · rw [hΦ]
      ring
    · ring
  rw [hre]
  refine (four_iterated_abs_le _ a2 a3 a4 hb1 hb2 hb3 _).trans ?_
  exact (mul_le_mul_of_nonneg_left key (by norm_num)).trans sfin


/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in the outer prime `p2` of the E4 sum at one point `m` of J, the other
three outer variables held fixed with arbitrary weights bounded by 2: the statement of
`leaf_four_transfer_p2`. Replacing the prime indicator of `p2` by the density
`1 / log n` changes the sum by every log power. Proved from `four_transfer_iterated`, the prime
number theorem with partial summation, and `four_region_jumps` of `FourDensityMain517b.lean`. -/
theorem four_transfer_p2 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a1 a3 a4 : ℕ → ℝ, (∀ n, |a1 n| ≤ 2) → (∀ n, |a3 n| ≤ 2) → (∀ n, |a4 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * (primeWeight i.2.1 - 1 / Real.log (i.2.1 : ℝ)) * a3 i.2.2.1 * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨K, hK0, happ⟩ := four_transfer_iterated (A + 4) (by linarith)
  obtain ⟨C, hC⟩ := four_transfer_scales hε hε8 A hA K hK0
  refine ⟨C, fun x hx m hm1 hm2 a1 a3 a4 hb1 hb2 hb3 => ?_⟩
  obtain ⟨hx1, s1, s2, s3, s4, sfin, -⟩ := hC x hx
  have hlZ0 : 0 < Real.log (scaleZ ε x) := by linarith
  have hZ1 : 1 < scaleZ ε x := (scaleZ_rpow_ge hε hε8 hx1).2
  have hmono : Monotone (expo ε x) := four_expo_monotone hZ1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hm1
  have key := happ ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ s1 s2 ω hω hz
    (fun o1 o2 q n : ℕ => n < o1 ∧ o2 < n ∧ q < o2 ∧
        lowerFourRegion ε (expo ε x o1) (expo ε x n) (expo ε x o2) (expo ε x q))
    603 (Real.log (scaleZ ε x) / 10) (m : ℝ) (by linarith)
    (fun o1 o2 q n hc => by
      obtain ⟨hd, hdc, hcb, hba, -, -⟩ := Decomp514a.four_density_region_box hε hε8 hc.2.2.2
      have hq' : 1 / 10 ≤ Real.log (q : ℝ) / Real.log (scaleZ ε x) := hd
      have hn' : 1 / 10 ≤ Real.log (n : ℝ) / Real.log (scaleZ ε x) := by
        have h1 : expo ε x n = Real.log (n : ℝ) / Real.log (scaleZ ε x) := rfl
        rw [← h1]
        linarith
      have hq2 := (le_div_iff₀ hlZ0).mp hq'
      have hn2 := (le_div_iff₀ hlZ0).mp hn'
      exact ⟨s4 n (by linarith), by linarith⟩)
    (fun o1 o2 q => by
      have r := four_region_jumps ε (expo ε x) hmono (expo ε x o1) 0 0 1 (expo ε x o2) 0 (expo ε x q) 0
        (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      simp only [zero_add, one_mul, zero_mul, add_zero] at r
      have j1 := indicator_variation_anti_le_one (fun n : ℕ => n < o1)
        (fun i h => by omega) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j2 := indicator_variation_mono_le_one (fun n : ℕ => o2 < n)
        (fun i h => by omega) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j3 := indicator_variation_mono_le_one (fun _ : ℕ => q < o2)
        (fun _ h => h) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have k3 := (indicator_variation_and_le (fun n : ℕ => q < o2)
        (fun n : ℕ => lowerFourRegion ε (expo ε x o1) (expo ε x n) (expo ε x o2) (expo ε x q)) _).trans (add_le_add j3 r)
      have k2 := (indicator_variation_and_le (fun n : ℕ => o2 < n)
        (fun n : ℕ => q < o2 ∧ lowerFourRegion ε (expo ε x o1) (expo ε x n) (expo ε x o2) (expo ε x q)) _).trans (add_le_add j2 k3)
      have k1 := (indicator_variation_and_le (fun n : ℕ => n < o1)
        (fun n : ℕ => o2 < n ∧ q < o2 ∧ lowerFourRegion ε (expo ε x o1) (expo ε x n) (expo ε x o2) (expo ε x q)) _).trans (add_le_add j1 k2)
      exact k1.trans (by norm_num))
  have hre : ∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * (primeWeight i.2.1 - 1 / Real.log (i.2.1 : ℝ)) * a3 i.2.2.1 * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) =
      ∑ o1 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ o2 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ q ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, a1 o1 * a3 o2 * a4 q *
          ((primeWeight n - 1 / Real.log (n : ℝ)) *
            (if n < o1 ∧ o2 < n ∧ q < o2 ∧
        lowerFourRegion ε (expo ε x o1) (expo ε x n) (expo ε x o2) (expo ε x q) then
              ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
              Real.log (q : ℝ)) / Real.log (q : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) else 0)) := by
    rw [four_sum_filter_iter, four_rot_second]
    refine Finset.sum_congr rfl fun o1 ho1 => Finset.sum_congr rfl fun o2 ho2 =>
      Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun n hn => ?_
    have ho1' : (0 : ℝ) < (o1 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho1).1
    have ho2' : (0 : ℝ) < (o2 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho2).1
    have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hΦ : ω (Real.log ((m : ℝ) / ((o1 : ℝ) * (n : ℝ) * (o2 : ℝ) * (q : ℝ))) / Real.log (q : ℝ)) /
            Real.log (q : ℝ) / ((o1 : ℝ) * (n : ℝ) * (o2 : ℝ) * (q : ℝ)) =
        ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
              Real.log (q : ℝ)) / Real.log (q : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) := by
      have e : (o1 : ℝ) * (n : ℝ) * (o2 : ℝ) * (q : ℝ) = (o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ) := by ring
      rw [e, four_phi_split hm0 (by positivity) hn']
    dsimp only
    split_ifs with g1
    · rw [hΦ]
      ring
    · ring
  rw [hre]
  refine (four_iterated_abs_le _ a1 a3 a4 hb1 hb2 hb3 _).trans ?_
  exact (mul_le_mul_of_nonneg_left key (by norm_num)).trans sfin


/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in the outer prime `p3` of the E4 sum at one point `m` of J, the other
three outer variables held fixed with arbitrary weights bounded by 2: the statement of
`leaf_four_transfer_p3`. Replacing the prime indicator of `p3` by the density
`1 / log n` changes the sum by every log power. Proved from `four_transfer_iterated`, the prime
number theorem with partial summation, and `four_region_jumps` of `FourDensityMain517b.lean`. -/
theorem four_transfer_p3 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a1 a2 a4 : ℕ → ℝ, (∀ n, |a1 n| ≤ 2) → (∀ n, |a2 n| ≤ 2) → (∀ n, |a4 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * a2 i.2.1 * (primeWeight i.2.2.1 - 1 / Real.log (i.2.2.1 : ℝ)) * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨K, hK0, happ⟩ := four_transfer_iterated (A + 4) (by linarith)
  obtain ⟨C, hC⟩ := four_transfer_scales hε hε8 A hA K hK0
  refine ⟨C, fun x hx m hm1 hm2 a1 a2 a4 hb1 hb2 hb3 => ?_⟩
  obtain ⟨hx1, s1, s2, s3, s4, sfin, -⟩ := hC x hx
  have hlZ0 : 0 < Real.log (scaleZ ε x) := by linarith
  have hZ1 : 1 < scaleZ ε x := (scaleZ_rpow_ge hε hε8 hx1).2
  have hmono : Monotone (expo ε x) := four_expo_monotone hZ1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hm1
  have key := happ ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ s1 s2 ω hω hz
    (fun o1 o2 q n : ℕ => o2 < o1 ∧ n < o2 ∧ q < n ∧
        lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x n) (expo ε x q))
    603 (Real.log (scaleZ ε x) / 10) (m : ℝ) (by linarith)
    (fun o1 o2 q n hc => by
      obtain ⟨hd, hdc, hcb, hba, -, -⟩ := Decomp514a.four_density_region_box hε hε8 hc.2.2.2
      have hq' : 1 / 10 ≤ Real.log (q : ℝ) / Real.log (scaleZ ε x) := hd
      have hn' : 1 / 10 ≤ Real.log (n : ℝ) / Real.log (scaleZ ε x) := by
        have h1 : expo ε x n = Real.log (n : ℝ) / Real.log (scaleZ ε x) := rfl
        rw [← h1]
        linarith
      have hq2 := (le_div_iff₀ hlZ0).mp hq'
      have hn2 := (le_div_iff₀ hlZ0).mp hn'
      exact ⟨s4 n (by linarith), by linarith⟩)
    (fun o1 o2 q => by
      have r := four_region_jumps ε (expo ε x) hmono (expo ε x o1) 0 (expo ε x o2) 0 0 1 (expo ε x q) 0
        (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      simp only [zero_add, one_mul, zero_mul, add_zero] at r
      have j1 := indicator_variation_mono_le_one (fun _ : ℕ => o2 < o1)
        (fun _ h => h) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j2 := indicator_variation_anti_le_one (fun n : ℕ => n < o2)
        (fun i h => by omega) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j3 := indicator_variation_mono_le_one (fun n : ℕ => q < n)
        (fun i h => by omega) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have k3 := (indicator_variation_and_le (fun n : ℕ => q < n)
        (fun n : ℕ => lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x n) (expo ε x q)) _).trans (add_le_add j3 r)
      have k2 := (indicator_variation_and_le (fun n : ℕ => n < o2)
        (fun n : ℕ => q < n ∧ lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x n) (expo ε x q)) _).trans (add_le_add j2 k3)
      have k1 := (indicator_variation_and_le (fun n : ℕ => o2 < o1)
        (fun n : ℕ => n < o2 ∧ q < n ∧ lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x n) (expo ε x q)) _).trans (add_le_add j1 k2)
      exact k1.trans (by norm_num))
  have hre : ∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * a2 i.2.1 * (primeWeight i.2.2.1 - 1 / Real.log (i.2.2.1 : ℝ)) * a4 i.2.2.2 *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) =
      ∑ o1 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ o2 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ q ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, a1 o1 * a2 o2 * a4 q *
          ((primeWeight n - 1 / Real.log (n : ℝ)) *
            (if o2 < o1 ∧ n < o2 ∧ q < n ∧
        lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x n) (expo ε x q) then
              ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
              Real.log (q : ℝ)) / Real.log (q : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) else 0)) := by
    rw [four_sum_filter_iter, four_rot_third]
    refine Finset.sum_congr rfl fun o1 ho1 => Finset.sum_congr rfl fun o2 ho2 =>
      Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun n hn => ?_
    have ho1' : (0 : ℝ) < (o1 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho1).1
    have ho2' : (0 : ℝ) < (o2 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho2).1
    have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hq).1
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hΦ : ω (Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (n : ℝ) * (q : ℝ))) / Real.log (q : ℝ)) /
            Real.log (q : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (n : ℝ) * (q : ℝ)) =
        ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ))) - Real.log (n : ℝ)) /
              Real.log (q : ℝ)) / Real.log (q : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ)) := by
      have e : (o1 : ℝ) * (o2 : ℝ) * (n : ℝ) * (q : ℝ) = (o1 : ℝ) * (o2 : ℝ) * (q : ℝ) * (n : ℝ) := by ring
      rw [e, four_phi_split hm0 (by positivity) hn']
    dsimp only
    split_ifs with g1
    · rw [hΦ]
      ring
    · ring
  rw [hre]
  refine (four_iterated_abs_le _ a1 a2 a4 hb1 hb2 hb3 _).trans ?_
  exact (mul_le_mul_of_nonneg_left key (by norm_num)).trans sfin

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number theorem",
partial summation in the outer prime `p4` of the E4 sum at one point `m` of J, the other
three outer variables held fixed with arbitrary weights bounded by 2: the statement of
`leaf_four_transfer_p4`. The variable `p4` is also the level of the Buchstab density.
Replacing the prime indicator of `p4` by the density `1 / log n` changes the sum by every log
power. Proved from `four_transfer_iterated_level`, the prime number theorem with partial
summation, and `four_region_jumps` of `FourDensityMain517b.lean`. -/
theorem four_transfer_p4 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      ∀ a1 a2 a3 : ℕ → ℝ, (∀ n, |a1 n| ≤ 2) → (∀ n, |a2 n| ≤ 2) → (∀ n, |a3 n| ≤ 2) →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * a2 i.2.1 * a3 i.2.2.1 * (primeWeight i.2.2.2 - 1 / Real.log (i.2.2.2 : ℝ)) *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ)))| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨K, hK0, happ⟩ := four_transfer_iterated_level (A + 4) (by linarith)
  obtain ⟨C, hC⟩ := four_transfer_scales hε hε8 A hA K hK0
  refine ⟨C, fun x hx m hm1 hm2 a1 a2 a3 hb1 hb2 hb3 => ?_⟩
  obtain ⟨hx1, s1, s2, s3, s4, -, sfin⟩ := hC x hx
  have hlZ0 : 0 < Real.log (scaleZ ε x) := by linarith
  have hZ1 : 1 < scaleZ ε x := (scaleZ_rpow_ge hε hε8 hx1).2
  have hmono : Monotone (expo ε x) := four_expo_monotone hZ1
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hm1
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hm1
  have key := happ ⌊x ^ (11 / 200 : ℝ) / 2⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊ s1 s2 ω hω hz
    (fun o1 o2 o3 n : ℕ => o2 < o1 ∧ o3 < o2 ∧ n < o3 ∧
        lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x o3) (expo ε x n))
    603 (m : ℝ) hm1' (by exact_mod_cast hm2)
    (fun o1 o2 o3 n hc => by
      obtain ⟨hd, -⟩ := Decomp514a.four_density_region_box hε hε8 hc.2.2.2
      have hn' : 1 / 10 ≤ Real.log (n : ℝ) / Real.log (scaleZ ε x) := hd
      have hn2 := (le_div_iff₀ hlZ0).mp hn'
      exact s4 n (by linarith))
    (fun o1 o2 o3 => by
      have r := four_region_jumps ε (expo ε x) hmono (expo ε x o1) 0 (expo ε x o2) 0
        (expo ε x o3) 0 0 1 (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      simp only [zero_add, one_mul, zero_mul, add_zero] at r
      have j1 := indicator_variation_mono_le_one (fun _ : ℕ => o2 < o1)
        (fun _ h => h) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j2 := indicator_variation_mono_le_one (fun _ : ℕ => o3 < o2)
        (fun _ h => h) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have j3 := indicator_variation_anti_le_one (fun n : ℕ => n < o3)
        (fun i h => by omega) (⌊x ^ (11 / 200 : ℝ) / 2⌋₊ + 1) ⌊2 * x ^ (11 / 20 + ε)⌋₊
      have k3 := (indicator_variation_and_le (fun n : ℕ => n < o3)
        (fun n : ℕ => lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x o3) (expo ε x n)) _).trans (add_le_add j3 r)
      have k2 := (indicator_variation_and_le (fun _ : ℕ => o3 < o2)
        (fun n : ℕ => n < o3 ∧ lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x o3) (expo ε x n)) _).trans (add_le_add j2 k3)
      have k1 := (indicator_variation_and_le (fun _ : ℕ => o2 < o1)
        (fun n : ℕ => o3 < o2 ∧ n < o3 ∧ lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x o3) (expo ε x n)) _).trans (add_le_add j1 k2)
      exact k1.trans (by norm_num))
  have hre : ∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
            i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
              lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                (expo ε x i.2.2.2)),
          a1 i.1 * a2 i.2.1 * a3 i.2.2.1 * (primeWeight i.2.2.2 - 1 / Real.log (i.2.2.2 : ℝ)) *
          (ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) *
              (i.2.2.2 : ℝ))) / Real.log (i.2.2.2 : ℝ)) /
            Real.log (i.2.2.2 : ℝ) /
              ((i.1 : ℝ) * (i.2.1 : ℝ) * (i.2.2.1 : ℝ) * (i.2.2.2 : ℝ))) =
      ∑ o1 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ o2 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, ∑ o3 ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, a1 o1 * a2 o2 * a3 o3 *
          ((primeWeight n - 1 / Real.log (n : ℝ)) *
            (if o2 < o1 ∧ o3 < o2 ∧ n < o3 ∧
        lowerFourRegion ε (expo ε x o1) (expo ε x o2) (expo ε x o3) (expo ε x n) then
              ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))) - Real.log (n : ℝ)) /
              Real.log (n : ℝ)) / Real.log (n : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) * (n : ℝ)) else 0)) := by
    rw [four_sum_filter_iter]
    refine Finset.sum_congr rfl fun o1 ho1 => Finset.sum_congr rfl fun o2 ho2 =>
      Finset.sum_congr rfl fun o3 ho3 => Finset.sum_congr rfl fun n hn => ?_
    have ho1' : (0 : ℝ) < (o1 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho1).1
    have ho2' : (0 : ℝ) < (o2 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho2).1
    have ho3' : (0 : ℝ) < (o3 : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp ho3).1
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hΦ : ω (Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) * (n : ℝ))) /
          Real.log (n : ℝ)) / Real.log (n : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) * (n : ℝ)) =
        ω ((Real.log ((m : ℝ) / ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ))) - Real.log (n : ℝ)) /
              Real.log (n : ℝ)) / Real.log (n : ℝ) /
            ((o1 : ℝ) * (o2 : ℝ) * (o3 : ℝ) * (n : ℝ)) := by
      rw [four_phi_split hm0 (by positivity) hn']
    dsimp only
    split_ifs with g1
    · rw [hΦ]
      ring
    · ring
  rw [hre]
  refine (four_iterated_abs_le _ a1 a2 a3 hb1 hb2 hb3 _).trans ?_
  exact (mul_le_mul_of_nonneg_left key (by norm_num)).trans sfin

#print axioms four_pnt_reciprocal
#print axioms four_fibre_fixed_level
#print axioms four_transfer_iterated
#print axioms four_transfer_scales
#print axioms four_transfer_p1
#print axioms four_transfer_p2
#print axioms four_transfer_p3
#print axioms four_transfer_p4

end LeanLab.BHP1997.LowerShortC165
