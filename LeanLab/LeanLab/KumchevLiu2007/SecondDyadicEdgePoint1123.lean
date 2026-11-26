/-
BURST 2026-11-22, session S154, burst-20261122, STEP second-dyadic-edges-p2. SPLIT of the
MEDIUM LEAF SecondDyadicEdges1123.edge_pointwise, P0088 Kumchev and Liu 2007, Lemma 3.4
Cases 1 to 3, pages 11 to 12, the edge stretch t in [Y - 2H, Y] of the second sum of
display 52, page 15, in window form.
One PROVED step and one smaller LEAF:
* coef_norm_le, PROVED, the coefficient of m has modulus at most 2 tau of m: at most two block primes
  p at least Y^(1/6 + eps/2) divide m below Y^(1/2), and the inner Moebius sum over divisors
  of m/p has at most tau of m terms of modulus at most one.
* tau_edge_sum, LEAF MEDIUM, the squared sum of tau of m over the short edge interval is at most
  C H L^(-A), by the hyperbola bound for tau over an interval of length at most 2H Y^(-1/2)
  below Y^(1/2) and the H range of Theorem 1.
SecondDyadicEdges1123.edge_pointwise is PROVED from them, with the triangle inequality and
|e(m^2 alpha)| = 1.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SecondDyadicCases1122
import LeanLab.KumchevLiu2007.SecondDyadicCase3Split1122

namespace LeanLab.KumchevLiu2007.SecondDyadicEdgePoint1123

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED, S154. Three distinct primes at least z dividing m force z^3 at most m, so if
m < Y^(1/2) at most z^3, at most two such primes divide m. -/
theorem three_primes_le (z Y : ℝ) (hz : Y ^ (1 / 2 : ℝ) ≤ z ^ 3) (hz0 : 0 ≤ z)
    (m : ℕ) (hm : (m : ℝ) < Real.sqrt Y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ z ≤ (p : ℝ) ∧ p ∣ m) (hm0 : m ≠ 0) : s.card ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
  obtain ⟨pa, za, da⟩ := hs a ha
  obtain ⟨pb, zb, db⟩ := hs b hb
  obtain ⟨pc, zc, dc⟩ := hs c hc
  have cab : Nat.Coprime a b := (Nat.coprime_primes pa pb).2 hab
  have cac : Nat.Coprime a c := (Nat.coprime_primes pa pc).2 hac
  have cbc : Nat.Coprime b c := (Nat.coprime_primes pb pc).2 hbc
  have hd : a * b * c ∣ m :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_mul_iff_left.2 ⟨cac, cbc⟩)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd cab da db) dc
  have hle : a * b * c ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd
  have hle' : (a : ℝ) * b * c ≤ m := by exact_mod_cast hle
  have h3 : z ^ 3 ≤ (a : ℝ) * b * c := by
    have h1 : z * z ≤ (a : ℝ) * b := mul_le_mul za zb hz0 (by linarith)
    calc z ^ 3 = z * z * z := by ring
      _ ≤ (a : ℝ) * b * c := mul_le_mul h1 zc hz0 (by positivity)
  rw [Real.sqrt_eq_rpow] at hm
  linarith

/-- PROVED, S154. P0088 pages 11 to 12, Lemma 3.4, the size of the coefficient of m in the
short sum. Three primes at least Y^(1/6 + eps/2) multiply to more than Y^(1/2) > m, so at most two
block primes divide m; for each, the Moebius sum over a set of divisors of m/p has modulus
at most the number of divisors of m/p, at most tau of m. -/
theorem coef_norm_le (X ε B M D : ℝ) (hX : 1 ≤ X) (hε : 0 < ε) (m : ℕ)
    (hm : m ∈ squareWindow (windowY X ε)) :
    ‖∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
        (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
        p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      ∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
          (r : ℝ) < windowY X ε ^ (1 / 6 + ε / 2))).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 2 * (m.divisors.card : ℝ) := by
  set Y := windowY X ε with hYdef
  have hY : 1 ≤ Y := Real.one_le_rpow hX (by linarith)
  have hmw := (Finset.mem_filter.1 hm).2
  have hsq : 0 < Real.sqrt Y := Real.sqrt_pos.2 (by linarith)
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hmw; simp at hmw; linarith [hmw.1]
  set z := Y ^ (1 / 6 + ε / 2) with hz
  have hz0 : 0 ≤ z := Real.rpow_nonneg (by linarith) _
  have hz3 : Y ^ (1 / 2 : ℝ) ≤ z ^ 3 := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hY (by push_cast; linarith)
  set P := ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧ z ≤ (p : ℝ) ∧
        (p : ℝ) < Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧ p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M) with hP
  have hcard : P.card ≤ 2 := by
    refine three_primes_le z Y hz3 hz0 m hmw.2 P (fun p hp => ?_) hm0
    have h := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ P, ‖∑ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime →
      r ∣ d → (r : ℝ) < z)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ (m.divisors.card : ℝ) := by
    intro p hp
    have hpm : p ∣ m := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.2.2.2
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ d ∈ ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime →
        r ∣ d → (r : ℝ) < z)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      intro d _
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : ((m / p).divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime →
        r ∣ d → (r : ℝ) < z)).filter (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D) ⊆
        m.divisors :=
      (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans
        (Nat.divisors_subset_of_dvd hm0 (Nat.div_dvd_of_dvd hpm)))
    exact_mod_cast Finset.card_le_card hsub
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (P.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have h0 : (0 : ℝ) ≤ m.divisors.card := Nat.cast_nonneg _
  nlinarith

/-- LEAF: P0088 pages 11 to 12, Lemma 3.4 Cases 1 to 3, the edge stretch. MEDIUM. For t in
[Y - 2H, Y] the m with m^2 in (t, t + H] and m in the window lie in an interval of length at
most 2H Y^(-1/2) below Y^(1/2); the hyperbola bound gives a sum of tau at most
4H Y^(-1/2)(1 + log Y) + 2 Y^(1/4) + 2, whose square is at most C H L^(-A) once
4B at least A + 2, since H at most Y L^(-4B) and Y^(1/2) L^(A + 4B) at most X^(7/18 + eps). -/
theorem tau_edge_sum (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ t : ℝ, windowY X ε - 2 * H ≤ t → t ≤ windowY X ε →
        (∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (m.divisors.card : ℝ)) ^ 2 ≤ C * H / Real.log X ^ A := by
  sorry

end LeanLab.KumchevLiu2007.SecondDyadicEdgePoint1123

#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdgePoint1123.three_primes_le
#print axioms LeanLab.KumchevLiu2007.SecondDyadicEdgePoint1123.coef_norm_le
