/-
BURST 2026-11-22, session S39, unit P1122-0141, third step. Proves the leaves
Prep1122KLLemma34Cases.case_one and case_two from Lemmas 3.1 and 3.2 of P0088
page 10, stated here as printed. Kumchev and Liu 2007, P0088, arXiv 0801.0130.

* lemma31, LEAF HARD: Lemma 3.1 of page 10 as printed, for every A and c.
* lemma32, LEAF HARD: Lemma 3.2 of page 10 as printed, for every A and c.
  Both are CITED-LEFT: the paper calls them restatements of Lemmas 3.1 and 3.2
  of Kumchev reference 14 and omits the proofs.
* reindex_mul, PROVED: the change of variables n = mk of pages 10 and 11, the
  double sum over m and k becomes a sum over n with the coefficient summed over
  the divisors of n.
* case_one_of_lemma31, PROVED from lemma31 with M = D, c = 1 and the
  convolution b_r of Case 1, which for M = 1 is mu of r when r divides Pi of z.
* case_two_of_lemma32, PROVED from lemma32 with M = D, c = 1, a_d = mu of d
  when d divides Pi of z, and b = 1, as in Case 2.

The sequences of Lemmas 3.1 and 3.2 are indexed by the positive integers; the
bound by tau to the power c is asked for m and k at least 1 only, since a zero
index never enters a sum over t below m^2 k^2 with t positive.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1122KLLemma34Cases

namespace LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 10 Lemma 3.1, with display 41 at L = log x, tau of m the
number of divisors of m, m near M meaning M at most m below 2M. Class HARD.
CITED-LEFT: a restatement of Kumchev reference 14 Lemma 3.1, proof omitted. -/
theorem lemma31 (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ am : ℕ → ℂ, (∀ m : ℕ, m ≠ 0 → ‖am m‖ ≤ (m.divisors.card : ℝ) ^ c) →
        ∀ M : ℝ, 1 ≤ M → M ≤ x ^ (1 / 4 : ℝ) / Real.log x ^ B →
        (∫ t in x..2 * x,
          ‖∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
              (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
            ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
            am m * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- LEAF: P0088 page 10 Lemma 3.2, with display 41 at L = log x, tau the
divisor function, m near M meaning M at most m below 2M. Class HARD.
CITED-LEFT: a restatement of Kumchev reference 14 Lemma 3.2, proof omitted. -/
theorem lemma32 (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ am bk : ℕ → ℂ, (∀ m : ℕ, m ≠ 0 → ‖am m‖ ≤ (m.divisors.card : ℝ) ^ c) →
        (∀ k : ℕ, k ≠ 0 → ‖bk k‖ ≤ (k.divisors.card : ℝ) ^ c) →
        ∀ M : ℝ, Real.log x ^ B ≤ M → M ≤ y / Real.sqrt x / Real.log x ^ B →
        (∫ t in x..2 * x,
          ‖∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
              (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
            ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
            am m * bk k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- PROVED. The change of variables n = mk of P0088 pages 10 and 11: a double
sum over m in R and k with a condition on mk is the sum over n of the
coefficient summed over the divisors of n in R. -/
theorem reindex_mul (R : Finset ℕ) (N : ℕ) (b g : ℕ → ℂ) (P : ℕ → Prop)
    (hR : ∀ r ∈ R, r ≠ 0) (hP : ∀ n, P n → n ≠ 0 ∧ n ≤ N) :
    ∑ r ∈ R, ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => P (r * k)), b r * g (r * k) =
      ∑ n ∈ (Finset.range (N + 1)).filter P,
        (∑ d ∈ n.divisors.filter (fun d : ℕ => d ∈ R), b d) * g n := by
  have hin : ∀ r ∈ R, ∑ k ∈ (Finset.range (N + 1)).filter (fun k : ℕ => P (r * k)),
      b r * g (r * k) =
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => P n ∧ r ∣ n), b r * g n := by
    intro r hr
    have hr0 : 0 < r := Nat.pos_of_ne_zero (hR r hr)
    refine Finset.sum_nbij' (fun k => r * k) (fun n => n / r) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨_, hPk⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hP _ hPk).2),
        hPk, dvd_mul_right r k⟩
    · intro n hn
      obtain ⟨hnr, hPn, hdvd⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact lt_of_le_of_lt (Nat.div_le_self n r) (Finset.mem_range.mp hnr)
      · show P (r * (n / r))
        rw [Nat.mul_div_cancel' hdvd]
        exact hPn
    · intro k _
      exact Nat.mul_div_cancel_left k hr0
    · intro n hn
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2.2
    · intro k _
      rfl
  rw [Finset.sum_congr rfl hin]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_comm' fun r n => ?_
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨hr, hn, hPn, hd⟩
    exact ⟨⟨⟨hd, (hP n hPn).1⟩, hr⟩, hn, hPn⟩
  · rintro ⟨⟨⟨hd, _⟩, hr⟩, hn, hPn⟩
    exact ⟨hr, hn, hPn, hd⟩

/-- PROVED. P0088 page 11: for t in x to 2x with x positive and y at most x,
the short sum condition t below n^2 at most t + y forces n positive and at most
the floor of the square root of 3x. -/
theorem window_n_bound {x y t : ℝ} (hx : 0 < x) (hy : y ≤ x) (ht : x ≤ t) (ht2 : t ≤ 2 * x)
    (n : ℕ) (hn : t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y) :
    n ≠ 0 ∧ n ≤ ⌊Real.sqrt (3 * x)⌋₊ := by
  refine ⟨?_, Nat.le_floor ?_⟩
  · rintro rfl
    norm_num at hn
    linarith [hn.1]
  · rw [← Real.sqrt_sq (Nat.cast_nonneg n)]
    exact Real.sqrt_le_sqrt (by linarith [hn.2])

/-- PROVED. P0088 page 11: the coefficient set of Case 1 and Case 2, divisors
d of n dividing Pi of z with D at most d below 2D, is the set of divisors of n
in the dyadic range of m near D cut to d dividing Pi of z. -/
theorem divisor_set_eq (z D : ℝ) (n : ℕ) :
    n.divisors.filter (fun d : ℕ => d ∈ ((Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)).filter
        (fun m : ℕ => Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z)) =
      (n.divisors.filter
        (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hd, ⟨_, h1, h2⟩, h3⟩
    exact ⟨⟨hd, h3⟩, h1, h2⟩
  · rintro ⟨⟨hd, h3⟩, h1, h2⟩
    exact ⟨hd, ⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith)), h1, h2⟩, h3⟩

/-- PROVED. The coefficient of Cases 1 and 2 with M = 1: mu of m when m divides
Pi of z, else zero, bounded by tau of m for m at least 1. -/
theorem mu_weight_bound (z : ℝ) (m : ℕ) (hm : m ≠ 0) :
    ‖(if Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0)‖ ≤
      (m.divisors.card : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have h1 : (1 : ℝ) ≤ m.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  split_ifs
  · refine le_trans ?_ h1
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- PROVED. P0088 page 11: on t in x to 2x the double sum of Lemmas 3.1 and 3.2
with the coefficient mu of m on m dividing Pi of z is the sum of display 42 in
the variable n = mk. -/
theorem integrand_eq {x y z D t α : ℝ} (hx : 0 < x) (hy : y ≤ x) (ht : x ≤ t) (ht2 : t ≤ 2 * x)
    (hD : 0 < D) :
    (∑ m ∈ (Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
      (if Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z then
          ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0) *
        fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
    ∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
      (∑ d ∈ (n.divisors.filter
          (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
          (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
      fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  rw [← Finset.sum_filter_add_sum_filter_not _
    (fun m : ℕ => Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z)]
  have hzero : ∑ m ∈ ((Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)).filter
        (fun m : ℕ => ¬ (Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z)),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
      (if Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z then
          ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0) *
        fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (Finset.mem_filter.mp hm).2, zero_mul]
  rw [hzero, add_zero]
  have hpos : ∀ m ∈ ((Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)).filter
        (fun m : ℕ => Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
      (if Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z then
          ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0) *
        fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) =
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
      ((ArithmeticFunction.moebius m : ℤ) : ℂ) *
        fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    intro m hm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos (Finset.mem_filter.mp hm).2]
  rw [Finset.sum_congr rfl hpos]
  have hR : ∀ r ∈ ((Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)).filter
        (fun m : ℕ => Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z), r ≠ 0 := by
    intro r hr
    obtain ⟨hr1, _⟩ := Finset.mem_filter.mp hr
    obtain ⟨_, hDr, _⟩ := Finset.mem_filter.mp hr1
    rintro rfl
    norm_num at hDr
    linarith
  have e := reindex_mul (((Finset.range (⌊2 * D⌋₊ + 1)).filter
        (fun m : ℕ => D ≤ (m : ℝ) ∧ (m : ℝ) < 2 * D)).filter
        (fun m : ℕ => Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z))
    ⌊Real.sqrt (3 * x)⌋₊ (fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℂ))
    (fun n : ℕ => fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)))
    (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y) hR
    (fun n hn => window_n_bound hx hy ht ht2 n hn)
  refine Eq.trans ?_ (e.trans ?_)
  · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr ?_ fun k _ => rfl
    ext k
    simp only [Finset.mem_filter]
  · refine Finset.sum_congr (by ext n; simp only [Finset.mem_filter]) fun n _ => ?_
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hd, ⟨_, h1, h2⟩, h3⟩
      exact ⟨⟨hd, h3⟩, h1, h2⟩
    · rintro ⟨⟨hd, h3⟩, h1, h2⟩
      exact ⟨hd, ⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith)), h1, h2⟩, h3⟩

/-- The exact statement of Prep1122KLLemma34Cases.case_one, from lemma31 with
M = D and c = 1. No sorry of its own. -/
theorem case_one_of_lemma31 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, 1 ≤ D → D ≤ Real.log x ^ B →
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  obtain ⟨B1, hB1, h⟩ := lemma31 A 1 hA one_pos
  refine ⟨B1, hB1, fun B hB => ?_⟩
  obtain ⟨C, x1, hC, hx1, k⟩ := h B hB
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (2 * B) (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, max x1 (max T 3), hC, hx1.trans (le_max_left _ _), ?_⟩
  intro x y hx hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz D hD1 hDL
  have hxa : x1 ≤ x := (le_max_left _ _).trans hx
  have hxT : T ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : 3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hPB : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hL B
  have h2B : Real.log x ^ (2 * B) ≤ x ^ (1 / 4 : ℝ) := by
    have h := hT x hxT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL (2 * B)),
      abs_of_pos (Real.rpow_pos_of_pos hx0 (1 / 4 : ℝ)), one_mul] at h
    exact h
  have hDM : D ≤ x ^ (1 / 4 : ℝ) / Real.log x ^ B := by
    rw [le_div_iff₀ hPB]
    calc
      D * Real.log x ^ B ≤ Real.log x ^ B * Real.log x ^ B :=
        mul_le_mul_of_nonneg_right hDL hPB.le
      _ = Real.log x ^ (2 * B) := by rw [← Real.rpow_add hL]; ring_nf
      _ ≤ x ^ (1 / 4 : ℝ) := h2B
  have hk := k x y hxa hy1 hy2 α q a hcop hqP hqQ happ
    (fun m => if Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0)
    (fun m hm => mu_weight_bound z m hm) D hD1 hDM
  refine le_of_eq_of_le ?_ hk
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by linarith)] at ht
  rw [integrand_eq hx0 hy2 ht.1 ht.2 (by linarith)]

/-- The exact statement of Prep1122KLLemma34Cases.case_two, from lemma32 with
M = D, c = 1 and b = 1. No sorry of its own. -/
theorem case_two_of_lemma32 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        ∀ D : ℝ, Real.log x ^ B ≤ D → D ≤ y / Real.sqrt x / Real.log x ^ B →
        (∫ t in x..2 * x,
          ‖∑ n ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + y),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => Squarefree d ∧ ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => D ≤ (d : ℝ) ∧ (d : ℝ) < 2 * D),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
            fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  obtain ⟨B1, hB1, h⟩ := lemma32 A 1 hA one_pos
  refine ⟨B1, hB1, fun B hB => ?_⟩
  obtain ⟨C, x1, hC, hx1, k⟩ := h B hB
  refine ⟨C, max x1 3, hC, hx1.trans (le_max_left _ _), ?_⟩
  intro x y hx hy1 hy2 α q a hcop hqP hqQ happ z hz2 hz D hDL hDU
  have hxa : x1 ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hPB : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hL B
  have hk := k x y hxa hy1 hy2 α q a hcop hqP hqQ happ
    (fun m => if Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < z then
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) else 0)
    (fun _ => 1)
    (fun m hm => mu_weight_bound z m hm)
    (fun k hk => by
      rw [norm_one, Real.rpow_one]
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk⟩)
    D hDL hDU
  refine le_of_eq_of_le ?_ hk
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by linarith)] at ht
  simp only [mul_one]
  rw [integrand_eq hx0 hy2 ht.1 ht.2 (hPB.trans_le hDL)]

example : type_of% @Prep1122KLLemma34Cases.case_one := case_one_of_lemma31
example : type_of% @Prep1122KLLemma34Cases.case_two := case_two_of_lemma32

end LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases

#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.reindex_mul
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.window_n_bound
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.divisor_set_eq
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.mu_weight_bound
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.integrand_eq
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.case_one_of_lemma31
#print axioms LeanLab.KumchevLiu2007.Prep1122KLLemma31Cases.case_two_of_lemma32
