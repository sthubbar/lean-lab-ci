/-
BURST 2026-11-22, session S81, burst-20261122. SPLIT of the leaves
Split1122SecondDyadicBlock.case1_small_D and case2_middle_D, Cases 1 and 2 of the
proof of Lemma 3.4 of Kumchev and Liu 2007, P0088, arXiv 0801.0130, pages 10 to
12, applied on page 15 to the second sum of display 52 in window form, t in
[Y/4, Y] with the squareWindow Y filter on m.

KNOWN OBSTACLE, confirmed. Lemmas 3.1 and 3.2 bound the integral over [x, 2x] of
the full short sum over t < m^2 <= t + y. The leaves keep the squareWindow Y
filter, so for t in [Y - H, Y] the short sum is cut at m^2 < Y and is no longer
the sum of the lemmas. For the unit coefficient, M = 1, S54 and S39 bounded the
stretch [Y - 2H, Y] trivially, Split1122KLLemma34M1.tail_arith, since each
coefficient has modulus at most 1. Here the coefficient of m is the sum over the
primes p of the block dividing m and over the divisors d of m / p in the block D
of mu of d, bounded only by tau of m squared. The trivial bound on the edge is
2H times the square of H Y^(-1/2) max tau, about H^3 Y^(-1) max tau^4, at most
H^2 (log X)^(-4B) max tau^4 for H up to Y (log X)^(-4B), and the maximum of tau
over m near Y^(1/2) exceeds every power of log X. So the trivial route fails;
the edge needs a mean bound for a divisor type function over the short interval
of m of length about H Y^(-1/2), Shiu type.

This file therefore proves each case statement exactly from two LEAFs:
* case1_interior and case2_interior, the integral over [Y/4, Y - 2H], where the
  window filter is no restriction once the stretch is cut at x = Y/2 as in
  Split1122KLLemma34M1; they rest on Lemmas 3.1 and 3.2, the LEAFs
  Prep1122KLLemma31Cases.lemma31 and lemma32, by the convolution b_r of Case 1
  over r = p d in [MD, 4MD), two dyadic blocks, and by the variable p d of
  Case 2. That reduction is NOT done here for lack of time.
* case1_edge and case2_edge, the integral over [Y - 2H, Y].
* case1_small_D_of_split and case2_middle_D_of_split, PROVED from the two LEAFs
  by additivity of the interval integral; each is checked by type_of% against
  the leaf of Split1122SecondDyadicBlock.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Split1122SecondDyadicBlock
import LeanLab.KumchevLiu2007.BlockEdge687

namespace LeanLab.KumchevLiu2007.SecondDyadicCases1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11, Case 1 of the proof of Lemma 3.4 on the interior stretch
t in [Y/4, Y - 2H]. Class MEDIUM. Follows from Lemma 3.1,
Prep1122KLLemma31Cases.lemma31 with c = 1, applied with x = Y/4 and x = Y/2 to
b_r the sum over p d = r of the prime indicator times mu of d, r in [MD, 4MD),
two dyadic blocks, |b_r| at most tau of r, with a smaller B' than B for the
slack R at most x^(1/4) L^(-B'); on this stretch the window filter is no
restriction, Split1122KLLemma34M1.window_filter_eq. Reduction not yet written. -/
theorem case1_interior (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11, Case 1 of the proof of Lemma 3.4 on the edge stretch
t in [Y - 2H, Y], where the squareWindow Y filter cuts the short sum at m^2 < Y.
Class HARD. Not treated in the paper. The trivial bound fails since the
coefficient is bounded only by a power of tau of m; it needs a Shiu type mean
bound for tau powers over the short interval of m near Y^(1/2) of length about
H Y^(-1/2), or a smoothing of the window. -/
theorem case1_edge (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in windowY X ε - 2 * H..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  refine ⟨A + 2, by linarith, ?_⟩
  intro B hB ε hε hε'
  have hBpos : 0 < B := by linarith
  have hεmax : ε ≤ 7 / 18 := by linarith
  obtain ⟨X1, hX1, hbig⟩ := Split1122KLLemma34M1.block_large_X B ε 0 hBpos hε hεmax
  refine ⟨288, X1, by norm_num, hX1, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM hMz hzM D hD hDP
  obtain ⟨hL1, hP2, hgap, hhalf, -⟩ := hbig X hX
  have hX2 : 2 ≤ X := hX1.trans hX
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos hX0 _
  have hY1 : 1 ≤ windowY X ε := Real.one_le_rpow (by linarith) (by linarith)
  obtain ⟨-, -, -, -, -, -, hsY, hH4, hHP, -, -⟩ :=
    Split1122KLLemma34M1.block_hyps B ε X H (windowY X ε / 2)
      (windowY X ε ^ (1 / 6 + ε / 2)) α q a hBpos hε hεmax hX2 hL1 hP2 hgap hhalf
      hlo hhi hqP hqQ hclose le_rfl (by linarith) (by linarith)
  refine Task687.small_block_edge_integral_le _ _ _ _ _ A B hY0 hsY hH4 hHP hL1
    (by linarith) ?_
  intro m hm
  rw [norm_mul, show ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 from
    Circle.norm_coe _, mul_one]
  have hmwin := (Finset.mem_filter.mp hm).2
  have hmpos : 0 < m := by
    have hs := Real.sqrt_pos.mpr hY0
    have : (0 : ℝ) < m := by linarith [hmwin.1]
    exact_mod_cast this
  have hmz : (m : ℝ) < (windowY X ε ^ (1 / 6 + ε / 2)) ^ 3 := by
    refine hmwin.2.trans_le ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num; linarith)
  refine le_trans (Task687.small_divisor_block_norm_le _ _ _ m
    (windowY X ε ^ (1 / 6 + ε / 2)) D hmpos (by positivity) hmz hD ?_ ?_ ?_) ?_
  · intro p hp
    obtain ⟨hp, -, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpp, hpz, -, hpm⟩ := Finset.mem_filter.mp hp
    exact ⟨hpp, hpm, hpz⟩
  · intro p hp d hd
    exact (Finset.mem_filter.mp hd).2.2
  · intro p hp d hd
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  · linarith

/-- LEAF: P0088 page 11, Case 2 of the proof of Lemma 3.4 on the interior stretch
t in [Y/4, Y - 2H]. Class MEDIUM. Follows from Lemma 3.2,
Prep1122KLLemma31Cases.lemma32 with c = 1, applied with x = Y/4 and x = Y/2,
the variable of Lemma 3.2 being d in the block D with coefficient mu of d on d
dividing Pi of z1, the other variable m / d carrying the sum over the primes p of
the block dividing it, bounded by tau; on this stretch the window filter is no
restriction. Reduction not yet written. -/
theorem case2_interior (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, Real.log X ^ B < D →
        D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε - 2 * H,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11, Case 2 of the proof of Lemma 3.4 on the edge stretch
t in [Y - 2H, Y], where the squareWindow Y filter cuts the short sum at m^2 < Y.
Class HARD. Not treated in the paper. The trivial bound fails since the
coefficient is bounded only by a power of tau of m; it needs a Shiu type mean
bound for tau powers over the short interval of m near Y^(1/2) of length about
H Y^(-1/2), or a smoothing of the window. -/
theorem case2_edge (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, Real.log X ^ B < D →
        D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        (∫ t in windowY X ε - 2 * H..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- PROVED from case1_interior and case1_edge. The exact statement of
Split1122SecondDyadicBlock.case1_small_D: the integral over [Y/4, Y] is the sum
of the integrals over [Y/4, Y - 2H] and [Y - 2H, Y]. -/
theorem case1_small_D_of_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case1_interior A hA
  obtain ⟨B2, hB2, h2⟩ := case1_edge A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, add_pos hC1 hC2, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD1 hD2
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  refine le_of_eq_of_le (intervalIntegral.integral_add_adjacent_intervals
    (b := windowY X ε - 2 * H) ?_ ?_).symm ?_
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · calc _ ≤ C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := add_le_add e1 e2
      _ = (C1 + C2) * H ^ 2 / Real.log X ^ A := by ring

/-- PROVED from case2_interior and case2_edge. The exact statement of
Split1122SecondDyadicBlock.case2_middle_D, by the same split at Y - 2H. -/
theorem case2_middle_D_of_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        ∀ D : ℝ, Real.log X ^ B < D →
        D ≤ H / (Real.sqrt (windowY X ε) * Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
                  (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
                  (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := case2_interior A hA
  obtain ⟨B2, hB2, h2⟩ := case2_edge A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨C1 + C2, max X1 X2, add_pos hC1 hC2, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose M hM htop hlow D hD1 hD2
  have e1 := k1 X H ((le_max_left _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  have e2 := k2 X H ((le_max_right _ _).trans hX) hlo hhi α q a hcop hqP hqQ hclose
    M hM htop hlow D hD1 hD2
  refine le_of_eq_of_le (intervalIntegral.integral_add_adjacent_intervals
    (b := windowY X ε - 2 * H) ?_ ?_).symm ?_
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · exact short_sum_sq_intervalIntegrable _ _ _ _ _
  · calc _ ≤ C1 * H ^ 2 / Real.log X ^ A + C2 * H ^ 2 / Real.log X ^ A := add_le_add e1 e2
      _ = (C1 + C2) * H ^ 2 / Real.log X ^ A := by ring

example : type_of% @Split1122SecondDyadicBlock.case1_small_D := case1_small_D_of_split

example : type_of% @Split1122SecondDyadicBlock.case2_middle_D := case2_middle_D_of_split

end LeanLab.KumchevLiu2007.SecondDyadicCases1122

#print axioms LeanLab.KumchevLiu2007.SecondDyadicCases1122.case1_small_D_of_split
#print axioms LeanLab.KumchevLiu2007.SecondDyadicCases1122.case2_middle_D_of_split
