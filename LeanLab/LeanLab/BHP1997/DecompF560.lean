/-
Independent split of the Vaughan singular series tail reduction in BHP1997.
The pointwise divisor weight is separated from the finite mean square step.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- The minimum divisor weight used in the Vaughan tail estimate. -/
noncomputable def divisorWeight560 (D x : ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ N.divisors, 1 / (Nat.totient d : ℝ) *
    min ((d : ℝ) / Real.log x ^ (2 * D)) 1

/-- LEAF. Pointwise divisor tail estimate for one truncated singular series
value. The squared truncation error is bounded by the logarithmic scale divided
by the frequency interval length and by the squared minimum divisor weight.
The internal arc parameter is taken sufficiently large. -/
theorem leaf_pointwise_divisor_tail560 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ A : ℝ, 0 < A → ∀ u v : ℝ,
        ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
          ∃ K : ℝ, 0 ≤ K ∧
            ∀ x : ℝ, 3 ≤ x →
              ∀ N ∈ frequencies512 ε x,
                ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ^ 2 ≤
                  K * (scale512 ε A x /
                      x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) +
                    length512 ε x ^ 2 * divisorWeight560 D x N ^ 2) := by
  sorry

/-- LEAF. The number of even frequencies in the short interval is at most a
fixed multiple of the interval length. This is the counting input needed when
the pointwise logarithmic error is summed. -/
theorem leaf_frequency_cardinality560 :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ M : ℝ, 1 ≤ M ∧
        ∀ x : ℝ, 3 ≤ x →
          (frequencies512 ε x).card ≤
            M * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  sorry

/-- LEAF. Finite mean square aggregation. If each summand is at most the
logarithmic term divided by the interval length plus the squared divisor
weight, then the sum is at most the logarithmic term multiplied by the
frequency count factor plus the weighted square sum. -/
theorem leaf_finite_square_aggregation560 (S : Finset ℕ)
    {K H M R B : ℝ} {f w : ℕ → ℝ}
    (hK : 0 ≤ K) (hH : 0 < H) (hM : 1 ≤ M)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hf : ∀ N ∈ S, f N ≤ K * (R / H + B * w N ^ 2))
    (hcard : S.card ≤ M * H) :
    (∑ N ∈ S, f N) ≤ K * M * R + K * B * (∑ N ∈ S, w N ^ 2) := by
  sorry

/-- The complete Vaughan singular series tail reduction. The pointwise
estimate is summed over the even frequencies and the finite counting estimate
absorbs the number of frequencies. -/
theorem leaf_vaughan_tail_reduction512_F560 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ, ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → seriesError512 ε D x u v ≤ C * (scale512 ε A x + length512 ε x ^ 2 * divisorTailMoment512 ε D x) := by
  refine ⟨1, one_pos, ?_⟩
  intro ε hε hε1 u v A hA
  obtain ⟨D₀, hD₀⟩ :=
    leaf_pointwise_divisor_tail560 ε hε hε1 A hA u v
  obtain ⟨M, hM, hMbound⟩ := leaf_frequency_cardinality560 ε hε hε1
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨K, hK, hKbound⟩ := hD₀ D hD
  let C : ℝ := max (K * M) 3
  refine ⟨C, fun x hx => ?_⟩
  have hC3 : 3 ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hx3 : 3 ≤ x := hC3.trans hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx3
  have hH : 0 < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hscale : 0 ≤ scale512 ε A x := scale_nonneg512 ε A hx1
  have hmom : 0 ≤ divisorTailMoment512 ε D x :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpoint : ∀ N ∈ frequencies512 ε x,
      ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ^ 2 ≤
        K * (scale512 ε A x /
            x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) +
          length512 ε x ^ 2 * divisorWeight560 D x N ^ 2) := by
    intro N hN
    exact hKbound x hx3 N hN
  have hcard : (frequencies512 ε x).card ≤
      M * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    hMbound x hx3
  have hsum := leaf_finite_square_aggregation560
    (S := frequencies512 ε x) (K := K)
    (H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
    (M := M) (R := scale512 ε A x) (B := length512 ε x ^ 2)
    (f := fun N => ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ^ 2)
    (w := fun N => divisorWeight560 D x N)
    hK hH hM hscale (sq_nonneg _) hpoint hcard
  have hmom_eq : (∑ N ∈ frequencies512 ε x, divisorWeight560 D x N ^ 2) =
      divisorTailMoment512 ε D x := by
    rfl
  have hCKM : K * M ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hKC : K ≤ C := by
    have hKM : K ≤ K * M := by
      simpa using mul_le_mul_of_nonneg_left hM hK
    exact hKM.trans hCKM
  have hscale' : K * M * scale512 ε A x ≤ C * scale512 ε A x :=
    mul_le_mul_of_nonneg_right hCKM hscale
  have htail : K * length512 ε x ^ 2 * divisorTailMoment512 ε D x ≤
      C * length512 ε x ^ 2 * divisorTailMoment512 ε D x := by
    exact mul_le_mul_of_nonneg_right hKC (mul_nonneg (sq_nonneg _) hmom)
  calc
    seriesError512 ε D x u v = ∑ N ∈ frequencies512 ε x,
        ‖truncatedMain512 ε D x u v N - expected512 ε x u v N‖ ^ 2 := rfl
    _ ≤ K * M * scale512 ε A x +
        K * length512 ε x ^ 2 * divisorTailMoment512 ε D x := by
      simpa only [hmom_eq] using hsum
    _ ≤ C * scale512 ε A x +
        C * length512 ε x ^ 2 * divisorTailMoment512 ε D x :=
      add_le_add hscale' htail
    _ = C * (scale512 ε A x + length512 ε x ^ 2 * divisorTailMoment512 ε D x) := by
      ring

end LeanLab.BHP1997.Section2MS
