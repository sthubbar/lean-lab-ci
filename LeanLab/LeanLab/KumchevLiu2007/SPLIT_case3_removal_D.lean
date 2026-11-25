/-
Split of `leaf_case3_lemma33_removal` of
`LeanLab.KumchevLiu2007.SPLIT_lemma34_case3_core`, the use of Lemma 3.3 in
Case 3 of the proof of Lemma 3.4 of Kumchev and Liu 2007, P0088 page 12.

The block d ∼ D of Case 3 lives on the divisors d = e f of the square roots m
of the window, so d ≤ m < Y^(1/2). For D ≥ Y^(1/2) the left side is 0 and the
bound holds with w = v = 0; that part is PROVED in `case3_removal_large_D`.
The LEAF `leaf_case3_lemma33_removal_core` is the parent statement with the
extra hypothesis D < Y^(1/2), the only range where the block is nonempty, and
it is still the cited use of Lemma 3.3, Kumchev 2006 Lemma 2.7.
`case3_removal_of_core` proves the parent statement with no sorry of its own.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD

namespace LeanLab.KumchevLiu2007.Eq33RouteD.Case3RemovalD1123

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4, the use of Lemma 3.3,
Kumchev Lemma 2.7, to remove the conditions p' < p, pp' d1 d2 ∼ D and
d1 p p' ≥ V, in the range D < Y^(1/2) where the block d ∼ D can meet the
divisors of the square roots m < Y^(1/2). Same left and right sides as
`leaf_case3_lemma33_removal`. Class HARD, cited input. -/
theorem leaf_case3_lemma33_removal_core :
    ∃ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        H < windowY X ε * Real.log X ^ B →
        D < Real.sqrt (windowY X ε) →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
              if (Squarefree e ∧ Squarefree f ∧
                  (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
                  (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
                  D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
                  (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
                  ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                    H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
              then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
                ((ArithmeticFunction.moebius f : ℤ) : ℂ)
              else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  sorry

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, outside the range of the
block: for D ≥ Y^(1/2), the statement of `leaf_case3_lemma33_removal` holds
with w = v = 0, since every pair e, f in the sum has e f dividing m, so
e f ≤ m < Y^(1/2) ≤ D, and the left side is 0. -/
theorem case3_removal_large_D :
    ∀ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∀ X0 : ℝ, 2 ≤ X0 → ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        H < windowY X ε * Real.log X ^ B →
        Real.sqrt (windowY X ε) ≤ D →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
              if (Squarefree e ∧ Squarefree f ∧
                  (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
                  (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
                  D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
                  (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
                  ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                    H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
              then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
                ((ArithmeticFunction.moebius f : ℤ) : ℂ)
              else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  intro c0 B hB ε hε X0 hX0 X H hX hlow hhigh α z hz2 hz D hD1 hD3 hsmall hDbig
  refine ⟨fun _ => 0, fun _ => 0, fun d => by rw [norm_zero]; positivity, fun k => by rw [norm_zero]; positivity, ?_⟩
  have hzero : ∀ t : ℝ, ∀ m ∈ (squareWindow (windowY X ε)).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
      (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
        if (Squarefree e ∧ Squarefree f ∧
            (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
            (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
            D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
            (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
            ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
              H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
        then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          ((ArithmeticFunction.moebius f : ℤ) : ℂ)
        else 0) = 0 := by
    intro t m hm
    obtain ⟨-, -, hmhi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
    refine Finset.sum_eq_zero fun e he => Finset.sum_eq_zero fun f hf => ?_
    rw [if_neg]
    rintro ⟨-, -, -, -, hDe, -⟩
    obtain ⟨hem, hm0⟩ := Nat.mem_divisors.mp he
    have hfm : f ∣ m / e := (Nat.mem_divisors.mp hf).1
    have hef : e * f ∣ m := Nat.mul_dvd_of_dvd_div hem hfm
    have hle : ((e * f : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hef
    linarith
  have hL : ∀ t : ℝ, ‖∑ m ∈ (squareWindow (windowY X ε)).filter
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
      (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
        if (Squarefree e ∧ Squarefree f ∧
            (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
            (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
            D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
            (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
            ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
              H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
        then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          ((ArithmeticFunction.moebius f : ℤ) : ℂ)
        else 0) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 = 0 := by
    intro t
    rw [Finset.sum_congr rfl fun m hm => by rw [hzero t m hm, zero_mul]]
    simp
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t _ => hL t)]
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  simp
  exact pow_nonneg hL0.le _

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4: the statement of
`leaf_case3_lemma33_removal`, from `leaf_case3_lemma33_removal_core` for
D < Y^(1/2) and from `case3_removal_large_D` otherwise.
CONDITIONAL ON leaf_case3_lemma33_removal_core. -/
theorem case3_removal_of_core :
    ∃ c0 : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) → ∀ α : ℝ,
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ D : ℝ, 1 ≤ D → H ≤ D * Real.sqrt (windowY X ε) * Real.log X ^ B →
        H < windowY X ε * Real.log X ^ B →
        ∃ w v : ℕ → ℂ, (∀ d : ℕ, ‖w d‖ ≤ (d.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, ‖v k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ e ∈ m.divisors, ∑ f ∈ (m / e).divisors,
              if (Squarefree e ∧ Squarefree f ∧
                  (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
                  (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
                  D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
                  (e : ℝ) < H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ∧
                  ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                    H / (Real.sqrt (windowY X ε) * Real.log X ^ B) ≤ (e : ℝ) * q)
              then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
                ((ArithmeticFunction.moebius f : ℤ) : ℂ)
              else 0) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            Real.log X ^ (c0 : ℝ) *
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ m.divisors.filter (fun d : ℕ => Real.log X ^ B ≤ (d : ℝ) ∧
                (d : ℝ) * Real.sqrt (windowY X ε) * Real.log X ^ B ≤ H),
              w d * v (m / d)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
            Real.log X ^ (c0 : ℝ) := by
  obtain ⟨c0, hcore⟩ := leaf_case3_lemma33_removal_core
  refine ⟨c0, fun B hB ε hε => ?_⟩
  obtain ⟨X0, hX0, k⟩ := hcore B hB ε hε
  refine ⟨X0, hX0, ?_⟩
  intro X H hX hlow hhigh α z hz2 hz D hD1 hD3 hsmall
  by_cases hD : D < Real.sqrt (windowY X ε)
  · exact k X H hX hlow hhigh α z hz2 hz D hD1 hD3 hsmall hD
  · exact case3_removal_large_D c0 B hB ε hε X0 hX0 X H hX hlow hhigh α z hz2 hz D hD1 hD3 hsmall
      (not_lt.mp hD)

end LeanLab.KumchevLiu2007.Eq33RouteD.Case3RemovalD1123

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.Case3RemovalD1123.leaf_case3_lemma33_removal_core
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.Case3RemovalD1123.case3_removal_large_D
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.Case3RemovalD1123.case3_removal_of_core
