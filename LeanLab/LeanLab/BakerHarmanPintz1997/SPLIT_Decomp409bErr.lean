/-
Split of the OPEN leaf `leaf_err_rearrange` of SPLIT_Decomp409b.lean, P0069 page 27,
display (4.13), first inequality. The statement is restated verbatim in
`leaf_err_rearrange_of_leaves`.

The split follows the proof described in the leaf's doc comment.
Leaf 1, the sum swap and interval count: the sum of c double prime over I1 is a sum over m, n
and d of |a_m b_n| times the number of k in I1 divisible by mnd, at most y1/(mnd) + 2.
Leaf 2, the harmonic weight sums: the sums over m ~ M of |a_m|/m and over n ~ N of |b_n|/n
have product at most L^K, from the bound of tau(m)^B/m summed over m up to 2M.
Leaf 3, the remainder size: the plain weight sums times the number of d below gamma w
are O(x^0.96) under (4.8) or (4.9) once epsilon is small.
The assembly is proved. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp409b

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-! ### Proved helpers for the sum swap, S117 -/

/-- Proved helper: the multiples of q in Ioc A B number at most (B - A)/q + 1. -/
theorem s409e_count_mult_le (A B q : ℕ) (hq : 0 < q) (hAB : A ≤ B) :
    (((Ioc A B).filter (fun k => q ∣ k)).card : ℝ) ≤ ((B : ℝ) - A) / q + 1 := by
  have hsub : (Ioc A B).filter (fun k => q ∣ k) ⊆ (Ioc (A / q) (B / q)).image (fun j => q * j) := by
    intro k hk
    rw [mem_filter, mem_Ioc] at hk
    obtain ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩ := hk
    refine mem_image.mpr ⟨j, mem_Ioc.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [Nat.div_lt_iff_lt_mul hq]; linarith [mul_comm q j]
    · rw [Nat.le_div_iff_mul_le hq]; linarith [mul_comm q j]
  have hc := (card_le_card hsub).trans card_image_le
  rw [Nat.card_Ioc] at hc
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e1 : ((B / q : ℕ) : ℝ) ≤ (B : ℝ) / q := Nat.cast_div_le
  have e2 : (A : ℝ) / q - 1 < ((A / q : ℕ) : ℝ) := by
    have hm := Nat.div_add_mod A q
    have hlt := Nat.mod_lt A hq
    have : (A : ℝ) = q * ((A / q : ℕ) : ℝ) + ((A % q : ℕ) : ℝ) := by exact_mod_cast hm.symm
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hq', this]
    have : ((A % q : ℕ) : ℝ) < q := by exact_mod_cast hlt
    nlinarith
  calc (((Ioc A B).filter (fun k => q ∣ k)).card : ℝ) ≤ ((B / q - A / q : ℕ) : ℝ) := by
        exact_mod_cast hc
    _ = ((B / q : ℕ) : ℝ) - ((A / q : ℕ) : ℝ) := by
        rw [Nat.cast_sub (Nat.div_le_div_right hAB)]
    _ ≤ ((B : ℝ) - A) / q + 1 := by rw [sub_div]; linarith

/-- Proved helper: the d sum of the statement, over the cast image, is the sum over naturals. -/
theorem s409e_sumD_cast (w γ : ℝ) : ∑ d ∈ (siftingProduct w).divisors.filter
          (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w), (1 / (d : ℝ)) =
     ∑ d ∈ ((siftingProduct w).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)),
        (1 / ((d : ℕ) : ℝ)) := by
  rw [← Finset.sum_image (f := fun d : ℝ => 1 / d) (s := (siftingProduct w).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)) (g := (Nat.cast : ℕ → ℝ)) (fun a _ b _ h => Nat.cast_injective h)]
  congr 1
  ext y
  simp
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, h⟩; exact ⟨a, ⟨ha, h⟩, rfl⟩
  · rintro ⟨a, ⟨ha, h⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, h⟩

/-- Proved helper: psiErr as a sum of divisibility indicators. -/
theorem s409e_psiErr_eq_sum (l : ℕ) (w γ : ℝ) : psiErr l w γ =
    ∑ d ∈ (siftingProduct w).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w),
      (if d ∣ l then (1 : ℝ) else 0) := by
  rw [psiErr, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_filter]
  congr 2
  ext d; simp only [mem_filter]; tauto

/-- Proved helper: mn | k and d | k/(mn) is mnd | k. -/
theorem s409e_term_eq (a b : ℕ → ℂ) (w γ : ℝ) (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (if m * n ∣ k then ‖a m‖ * ‖b n‖ * psiErr (k / (m * n)) w γ else 0) =
    ∑ d ∈ (siftingProduct w).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w),
      (if m * n * d ∣ k then ‖a m‖ * ‖b n‖ else 0) := by
  by_cases h : m * n ∣ k
  · rw [if_pos h, s409e_psiErr_eq_sum, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    by_cases hd : d ∣ k / (m * n)
    · have := (Nat.dvd_div_iff_mul_dvd h).mp hd
      simp [hd, this]
    · have := mt (Nat.dvd_div_iff_mul_dvd h).mpr hd
      simp [hd, this]
  · rw [if_neg h]
    symm
    refine sum_eq_zero fun d _ => ?_
    rw [if_neg]
    exact fun h' => h ((Dvd.intro d rfl).trans h')


/-- LEAF: display (4.13), first step, the sum swap. MEDIUM.
Summing c double prime over k in I1 and swapping, the pairs m, n with mn | k and the d with
d | k/(mn) give, for each m, n and each d | P(w) with gamma at most d below gamma w, the
number of k in I1 divisible by mnd, at most (y1 + 1)/(mnd) + 1 at most y1/(mnd) + 2. The d
counted number at most gamma w + 1, since they are positive integers below gamma w.
Non-vacuity: every x at least 1 and every a, b, M, N; equality-free for a = b = 0. -/
theorem leaf_err_swap (x M N w γ : ℝ) (a b : ℕ → ℂ) (hx : 1 ≤ x) (hγ : 1 ≤ γ) (hw : 1 ≤ w) :
    ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, conv2E a b M N w γ k ≤
      y1 x * ((∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ‖b n‖ / (n : ℝ))) *
        ∑ d ∈ (siftingProduct w).divisors.filter
          (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w), (1 / (d : ℝ)) +
      2 * ((∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖) * (∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ‖b n‖)) *
        (γ * w + 1) := by
  rw [s409e_sumD_cast]
  set D := (siftingProduct w).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)
    with hD
  set SM := Ioc ⌊M⌋₊ ⌊2 * M⌋₊
  set SN := Ioc ⌊N⌋₊ ⌊2 * N⌋₊
  set A := ⌊x - y1 x⌋₊
  set B := ⌊x⌋₊
  have hx0 : 0 < x := by linarith
  -- y1 facts
  have hy0 : 0 ≤ y1 x := (mul_pos hx0 (Real.exp_pos _)).le
  have hyx : y1 x ≤ x := by
    unfold y1
    have : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.rpow_nonneg (Real.log_nonneg hx) (1 / 3 : ℝ)
      linarith
    nlinarith
  have hAB : A ≤ B := Nat.floor_le_floor (by linarith)
  have hBA : (B : ℝ) - A ≤ y1 x + 1 := by
    have h1 : (B : ℝ) ≤ x := Nat.floor_le hx0.le
    have h2 : x - y1 x < A + 1 := Nat.lt_floor_add_one _
    linarith
  have hDcard : (D.card : ℝ) ≤ γ * w + 1 := by
    have hsub : D ⊆ Finset.range ⌈γ * w⌉₊ := by
      intro d hd
      rw [hD, mem_filter] at hd
      rw [mem_range]
      exact Nat.lt_ceil.mpr hd.2.2
    have := card_le_card hsub
    rw [card_range] at this
    have h2 : (⌈γ * w⌉₊ : ℝ) < γ * w + 1 := Nat.ceil_lt_add_one (by nlinarith)
    have h3 : (D.card : ℝ) ≤ ⌈γ * w⌉₊ := by exact_mod_cast this
    linarith
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rw [hD, mem_filter] at hd
    have : (1 : ℝ) ≤ d := hγ.trans hd.2.1
    exact_mod_cast (show (0 : ℝ) < d by linarith)
  have hMpos : ∀ m ∈ SM, 0 < m := fun m hm => by
    have := (mem_Ioc.mp hm).1; omega
  have hNpos : ∀ n ∈ SN, 0 < n := fun n hn => by
    have := (mem_Ioc.mp hn).1; omega
  -- rewrite and swap
  have hL : ∑ k ∈ Ioc A B, conv2E a b M N w γ k =
      ∑ m ∈ SM, ∑ n ∈ SN, ∑ d ∈ D, ∑ k ∈ Ioc A B,
        (if m * n * d ∣ k then ‖a m‖ * ‖b n‖ else 0) := by
    unfold conv2E
    rw [sum_comm]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_comm]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_congr rfl fun k _ => s409e_term_eq a b w γ k m n (hMpos m hm) (hNpos n hn), sum_comm]
  rw [hL]
  have hterm : ∀ m ∈ SM, ∀ n ∈ SN, ∀ d ∈ D,
      ∑ k ∈ Ioc A B, (if m * n * d ∣ k then ‖a m‖ * ‖b n‖ else 0) ≤
        ‖a m‖ * ‖b n‖ * (y1 x * ((1 / (m : ℝ)) * (1 / (n : ℝ)) * (1 / (d : ℝ))) + 2) := by
    intro m hm n hn d hd
    have hq : 0 < m * n * d := Nat.mul_pos (Nat.mul_pos (hMpos m hm) (hNpos n hn)) (hDpos d hd)
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    have hc := s409e_count_mult_le A B (m * n * d) hq hAB
    have hq' : (1 : ℝ) ≤ ((m * n * d : ℕ) : ℝ) := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < ((m * n * d : ℕ) : ℝ) := by linarith
    have hab : 0 ≤ ‖a m‖ * ‖b n‖ := by positivity
    refine mul_le_mul_of_nonneg_left (hc.trans ?_) hab
    have e : (1 / (m : ℝ)) * (1 / (n : ℝ)) * (1 / (d : ℝ)) = 1 / ((m * n * d : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [e]
    have h1 : ((B : ℝ) - A) / ((m * n * d : ℕ) : ℝ) ≤ (y1 x + 1) / ((m * n * d : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hBA hqpos.le
    have h2 : 1 / ((m * n * d : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact hq'
    have h3 : (y1 x + 1) / ((m * n * d : ℕ) : ℝ) = y1 x * (1 / ((m * n * d : ℕ) : ℝ)) +
        1 / ((m * n * d : ℕ) : ℝ) := by ring
    linarith
  have hsum := sum_le_sum fun m hm => sum_le_sum fun n hn => sum_le_sum fun d hd =>
    hterm m hm n hn d hd
  have S1 : ∑ m ∈ SM, ∑ n ∈ SN, ∑ d ∈ D,
      ‖a m‖ * ‖b n‖ * (y1 x * ((1 / (m : ℝ)) * (1 / (n : ℝ)) * (1 / (d : ℝ))) + 2) =
      ∑ m ∈ SM, ∑ n ∈ SN, ((y1 x * (‖a m‖ / (m : ℝ) * (‖b n‖ / (n : ℝ)))) *
        ∑ d ∈ D, (1 / (d : ℝ)) + (2 * (‖a m‖ * ‖b n‖)) * (D.card : ℝ)) := by
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [show (2 * (‖a m‖ * ‖b n‖)) * (D.card : ℝ) = ∑ d ∈ D, 2 * (‖a m‖ * ‖b n‖) by
      rw [sum_const, nsmul_eq_mul]; ring, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring
  have S2 : ∑ m ∈ SM, ∑ n ∈ SN, ((y1 x * (‖a m‖ / (m : ℝ) * (‖b n‖ / (n : ℝ)))) *
        ∑ d ∈ D, (1 / (d : ℝ)) + (2 * (‖a m‖ * ‖b n‖)) * (D.card : ℝ)) =
      (∑ m ∈ SM, ∑ n ∈ SN, y1 x * (‖a m‖ / (m : ℝ) * (‖b n‖ / (n : ℝ)))) *
        ∑ d ∈ D, (1 / (d : ℝ)) +
      (∑ m ∈ SM, ∑ n ∈ SN, 2 * (‖a m‖ * ‖b n‖)) * (D.card : ℝ) := by
    simp only [sum_add_distrib, sum_mul]
  have S3 : (∑ m ∈ SM, ∑ n ∈ SN, y1 x * (‖a m‖ / (m : ℝ) * (‖b n‖ / (n : ℝ)))) =
      y1 x * ((∑ m ∈ SM, ‖a m‖ / (m : ℝ)) * (∑ n ∈ SN, ‖b n‖ / (n : ℝ))) := by
    rw [sum_mul_sum]; simp only [mul_sum]
  have S4 : (∑ m ∈ SM, ∑ n ∈ SN, 2 * (‖a m‖ * ‖b n‖)) =
      2 * ((∑ m ∈ SM, ‖a m‖) * (∑ n ∈ SN, ‖b n‖)) := by
    rw [sum_mul_sum]; simp only [mul_sum]
  rw [S1, S2, S3, S4] at hsum
  have hP : 0 ≤ 2 * ((∑ m ∈ SM, ‖a m‖) * (∑ n ∈ SN, ‖b n‖)) := by positivity
  have := mul_le_mul_of_nonneg_left hDcard hP
  linarith

/-- LEAF: display (4.13), "using sum over m ~ M of tau(m)^B/m at most L^K". HARD, CITED.
The harmonic sums of tau to the B over m up to 2M with 2M at most x are O(L^K), K depending
on B, the classical mean value of the divisor function; the ranges (4.8) or (4.9) give
M and N at most x. Non-vacuity: a = b = 0 gives the product zero. -/
theorem leaf_err_harmonic (ε : ℝ) (hε : 0 < ε) (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ)
    (ha : ∀ x k, ‖a x k‖ ≤ tau k ^ B) (hb : ∀ x k, ‖b x k‖ ≤ tau k ^ B)
    (hr : ∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) :
    ∃ C K X0 : ℝ, 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
      (∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ)) ≤ C * L x ^ K := by
  sorry

/-- LEAF: display (4.13), the remainder "at most M N gamma w times x^o(1), below x^0.96
under (4.8) or (4.9) once epsilon is small". MEDIUM.
The plain sums are at most (M + 1) and (N + 1) times x^o(1) by the divisor bound, MN is at
most x^0.775 under (4.8) and x^(0.92 + ε/4) under (4.9), and gamma w is x^(ε/12 + o(1)).
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_remainder :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
        2 * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖) * (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖)) *
          (cutoff ε x * wof x + 1) ≤ C * x ^ (0.96 : ℝ) := by
  sorry

/-- `leaf_err_rearrange` of SPLIT_Decomp409b, verbatim. CONDITIONAL ON `leaf_err_swap`,
`leaf_err_harmonic` and `leaf_err_remainder`. -/
theorem leaf_err_rearrange_of_leaves :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C K X0 : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊,
          conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k ≤
            C * (y1 x * L x ^ K *
              ∑ d ∈ (siftingProduct (wof x)).divisors.filter
                (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ))
              + x ^ (0.96 : ℝ)) := by
  obtain ⟨ε0, hε0, hrem⟩ := leaf_err_remainder
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨C1, K, X1, hK, h1⟩ := leaf_err_harmonic ε hε B a b M N ha hb hr
  obtain ⟨C2, X2, h2⟩ := hrem ε hε hεs B a b M N ha hb hr
  refine ⟨max (max C1 C2) 0, K, max (max X1 X2) 1, le_max_right _ _, hK, ?_⟩
  intro x hx
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hγ : (1 : ℝ) ≤ cutoff ε x := le_trans (by norm_num) (le_max_left _ _)
  have hw : (1 : ℝ) ≤ wof x := by
    unfold wof
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx3) _)
  have hy : 0 ≤ y1 x := (y1_pos (by linarith)).le
  have hL : 0 ≤ L x ^ K := Real.rpow_nonneg (Real.log_nonneg hx3) _
  set S := ∑ d ∈ (siftingProduct (wof x)).divisors.filter
    (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg fun d hd => ?_
    have h1 : cutoff ε x ≤ d := (Finset.mem_filter.mp hd).2.1
    exact one_div_nonneg.mpr (by linarith)
  have hsw := leaf_err_swap x (M x) (N x) (wof x) (cutoff ε x) (a x) (b x) hx3 hγ hw
  have hh := h1 x hx1
  have hrr := h2 x hx2
  have hxp : 0 ≤ x ^ (0.96 : ℝ) := Real.rpow_nonneg (by linarith) _
  set C := max (max C1 C2) 0
  have hC1 : C1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmain : y1 x * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ))) * S ≤
        C * (y1 x * L x ^ K * S) := by
    have hyS : 0 ≤ y1 x * S := mul_nonneg hy hS0
    calc _ = (y1 x * S) * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ)) *
          (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ))) := by ring
      _ ≤ (y1 x * S) * (C1 * L x ^ K) := mul_le_mul_of_nonneg_left hh hyS
      _ ≤ (y1 x * S) * (C * L x ^ K) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC1 hL) hyS
      _ = C * (y1 x * L x ^ K * S) := by ring
  have hrem' : 2 * ((∑ m ∈ Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖) *
      (∑ n ∈ Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖)) * (cutoff ε x * wof x + 1) ≤
        C * x ^ (0.96 : ℝ) := hrr.trans (mul_le_mul_of_nonneg_right hC2 hxp)
  calc _ ≤ _ := hsw
    _ ≤ C * (y1 x * L x ^ K * S) + C * x ^ (0.96 : ℝ) := add_le_add hmain hrem'
    _ = _ := by ring

#print axioms leaf_err_swap
#print axioms leaf_err_rearrange_of_leaves

end LeanLab.BakerHarmanPintz1997.Decomp409b
