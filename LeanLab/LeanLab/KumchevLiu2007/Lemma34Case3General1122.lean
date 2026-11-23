/-
BURST 2026-11-22, session S81, step case3-general. Case 3 of the proof of
Lemma 3.4 of Kumchev and Liu 2007, P0088 pages 11 and 12, in the general x, y
form of Prep1122KLLemma34Cases.case_three, D at least V = y x^(-1/2) L^(-B),
M = 1 and a_1 = 1.

* block_eq_case3, PROVED: the factorisation display of page 12 for every n,
  from the generic Case3Core1122.moebius_block_case3_factor; for n = 0 both
  sides are empty sums.
* leaf_case3_lemma33_general, LEAF HARD: the use of Lemma 3.3, Kumchev
  reference 12 Lemma 2.7, that removes the conditions p' < p, pp'd1d2 near D
  and d1pp' at least V, ending in the Lemma 3.2 shaped sum in u = kp'd2 and
  v = pd1, times L^c plus L^c. Coefficients are chosen before the integral
  over t, see Q3 of the lemma34_large_right-p2 notes.
* case_three_of_leaves, no sorry of its own: the exact statement of
  Prep1122KLLemma34Cases.case_three from Prep1122KLLemma31Cases.lemma32 with
  A + c and the new LEAF. CONDITIONAL ON both.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases
import LeanLab.KumchevLiu2007.SPLIT_lemma34_case3_core

namespace LeanLab.KumchevLiu2007.Lemma34Case3General1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- PROVED. P0088 page 12, Case 3 of the proof of Lemma 3.4: the Moebius block
of display 42 over d near D, d dividing Pi of z, rewritten over n = e f k with
e = d1 p, f = p' d2, for 1 < V at most D, for every n including n = 0. -/
theorem block_eq_case3 (z V D : ℝ) (hV : 1 < V) (hVD : V ≤ D) (n : ℕ) :
    (∑ d ∈ (n.divisors.filter (fun d : ℕ => Squarefree d ∧
          ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ e ∈ n.divisors, ∑ f ∈ (n / e).divisors,
      if (Squarefree e ∧ Squarefree f ∧ (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
          (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
          D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧ (e : ℝ) < V ∧
          ∃ q : ℕ, q.Prime ∧ q ∣ f ∧ V ≤ (e : ℝ) * q)
      then ((ArithmeticFunction.moebius e : ℤ) : ℂ) * ((ArithmeticFunction.moebius f : ℤ) : ℂ)
      else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Case3Core1122.moebius_block_case3_factor z V D hV hVD n hn.ne'

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4, Lemma 3.3 removing
p' < p, pp'd1d2 near D and d1pp' at least V, V = y x^(-1/2) L^(-B). Left side:
display 42, M = 1, over n = e f k, e = d1 p, f = p' d2, as in block_eq_case3.
Right side: L^c times the Lemma 3.2 shaped integral in v = pd1, u = kp'd2, v in
one dyadic range M inside L^B to V, plus L^c; the dyadic split is paid by L^c,
coefficients bounded by tau^c, chosen before the t integral. Class HARD.
CITED on Lemma 3.3, Kumchev 2006 Lemma 2.7, not in hand. -/
theorem leaf_case3_lemma33_general :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ B : ℝ, 0 < B →
      ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x → ∀ α : ℝ,
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, y / Real.sqrt x / Real.log x ^ B ≤ D →
        ∃ M : ℝ, Real.log x ^ B ≤ M ∧ M ≤ y / Real.sqrt x / Real.log x ^ B ∧
        ∃ am bk : ℕ → ℂ, (∀ m : ℕ, m ≠ 0 → ‖am m‖ ≤ (m.divisors.card : ℝ) ^ c0) ∧
          (∀ k : ℕ, k ≠ 0 → ‖bk k‖ ≤ (k.divisors.card : ℝ) ^ c0) ∧
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ e ∈ n.divisors, ∑ f ∈ (n / e).divisors,
              if (Squarefree e ∧ Squarefree f ∧
                  (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
                  (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
                  D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
                  (e : ℝ) < y / Real.sqrt x / Real.log x ^ B ∧
                  ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                    y / Real.sqrt x / Real.log x ^ B ≤ (e : ℝ) * q)
              then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
                ((ArithmeticFunction.moebius f : ℤ) : ℂ)
              else 0) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          Real.log x ^ c0 *
          (∫ t in x..2 * x,
            ‖∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
                (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
              ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
                (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
              am m * bk k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) +
          Real.log x ^ c0 := by
  sorry

/-- P0088 pages 11 and 12, display 42 in Case 3, the exact statement of
Prep1122KLLemma34Cases.case_three. Lemma 3.2 is applied with A + c and the
coefficient exponent c of the new LEAF; the error L^c is at most y^2 L^(-A)
once L^(A + c) is at most x. CONDITIONAL ON leaf_case3_lemma33_general and
Prep1122KLLemma31Cases.lemma32. -/
theorem case_three_of_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, y / Real.sqrt x / Real.log x ^ B ≤ D →
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  obtain ⟨c0, hc0, hleaf⟩ := leaf_case3_lemma33_general
  obtain ⟨B1, hB1, h32⟩ := Prep1122KLLemma31Cases.lemma32 (A + c0) c0 (by linarith) hc0
  refine ⟨B1, hB1, fun B hB => ?_⟩
  obtain ⟨C, x1, hC, hx1, k32⟩ := h32 B hB
  obtain ⟨x2, hx2, kl⟩ := hleaf B (hB1.trans_le hB)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + c0) (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨C + 1, max x1 (max x2 (max T 3)), by linarith,
    hx1.trans (le_max_left _ _), ?_⟩
  intro x y hx hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz D hVD
  have hx1' : x1 ≤ x := (le_max_left _ _).trans hx
  have hx2' : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxT : T ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hx3 : 3 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log x := by linarith
  have hLB : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hL B
  have hLB1 : 1 ≤ Real.log x ^ B := Real.one_le_rpow hL1 (hB1.le.trans hB)
  have hL2B : Real.log x ^ B ≤ Real.log x ^ (2 * B) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hB1.trans_le hB])
  -- V = y x^(-1/2) L^(-B) is above 1
  have hV1 : 1 < y / Real.sqrt x / Real.log x ^ B := by
    rw [lt_div_iff₀ hLB, one_mul]
    have hL2Bpos : 0 < Real.log x ^ (2 * B) := Real.rpow_pos_of_pos hL _
    have h1 : 2 * Real.log x ^ (2 * B) ≤ y / Real.sqrt x := by
      have := (le_div_iff₀ hL2Bpos).mp (hz2.trans hz)
      linarith
    linarith
  -- rewrite the left side by the factorisation of page 12
  have hrw : ∀ t : ℝ,
      (∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
        (∑ d ∈ (n.divisors.filter
            (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
      ∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
        (∑ e ∈ n.divisors, ∑ f ∈ (n / e).divisors,
          if (Squarefree e ∧ Squarefree f ∧
              (∀ p : ℕ, p.Prime → p ∣ e * f → (p : ℝ) < z) ∧
              (∀ p q : ℕ, p.Prime → q.Prime → p ∣ e → q ∣ f → q < p) ∧
              D ≤ ((e * f : ℕ) : ℝ) ∧ ((e * f : ℕ) : ℝ) < 2 * D ∧
              (e : ℝ) < y / Real.sqrt x / Real.log x ^ B ∧
              ∃ q : ℕ, q.Prime ∧ q ∣ f ∧
                y / Real.sqrt x / Real.log x ^ B ≤ (e : ℝ) * q)
          then ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            ((ArithmeticFunction.moebius f : ℤ) : ℂ)
          else 0) *
        fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro t
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [block_eq_case3 z _ D hV1 hVD n]
  simp only [hrw]
  obtain ⟨M, hM1, hM2, am, bk, ham, hbk, hb⟩ := kl x y hx2' hy1 hy2 α z hz2 hz D hVD
  have h32x := k32 x y hx1' hy1 hy2 α q a hcop hqP hqQ happ am bk ham hbk M hM1 hM2
  -- the error term L^c is at most y^2 L^(-A)
  have hLc0 : 0 ≤ Real.log x ^ c0 := (Real.rpow_pos_of_pos hL c0).le
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL A
  have hsplit : Real.log x ^ (A + c0) = Real.log x ^ A * Real.log x ^ c0 :=
    Real.rpow_add hL A c0
  have hbig : Real.log x ^ (A + c0) ≤ x := by
    have h0 := hT x hxT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL _),
      abs_of_pos (Real.rpow_pos_of_pos hx0 _), Real.rpow_one, one_mul] at h0
    exact h0
  have hy2x : x ≤ y ^ 2 := by
    have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith
  have herr : Real.log x ^ c0 ≤ y ^ 2 / Real.log x ^ A := by
    rw [le_div_iff₀ hLA]
    nlinarith
  have hmain : Real.log x ^ c0 * (C * y ^ 2 / Real.log x ^ (A + c0)) =
      C * y ^ 2 / Real.log x ^ A := by
    rw [hsplit]
    have hc0' : 0 < Real.log x ^ c0 := Real.rpow_pos_of_pos hL c0
    field_simp
  calc _ ≤ _ := hb
    _ ≤ Real.log x ^ c0 * (C * y ^ 2 / Real.log x ^ (A + c0)) + y ^ 2 / Real.log x ^ A :=
        add_le_add (mul_le_mul_of_nonneg_left h32x hLc0) herr
    _ = (C + 1) * y ^ 2 / Real.log x ^ A := by rw [hmain]; ring

example : type_of% @Prep1122KLLemma34Cases.case_three := case_three_of_leaves

end LeanLab.KumchevLiu2007.Lemma34Case3General1122

#print axioms LeanLab.KumchevLiu2007.Lemma34Case3General1122.block_eq_case3
#print axioms LeanLab.KumchevLiu2007.Lemma34Case3General1122.case_three_of_leaves
