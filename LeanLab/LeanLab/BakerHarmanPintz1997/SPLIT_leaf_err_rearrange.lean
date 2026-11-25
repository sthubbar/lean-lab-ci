/-
Split of the OPEN leaf `leaf_err_rearrange` of SPLIT_Decomp409b, the first inequality of
display (4.13), P0069 page 27, with remainder x^0.96.

The paper swaps the sums in the sum of c double prime over I1 = (x - y1, x]: for fixed m, n
and d in the dagger range, the k = mnl in I1 with d | l are the multiples of mnd in I1, at
most y1/(mnd) + 2 of them. This gives three pieces:
* `leaf_err_count`, the swap and the interval count, deterministic, MEDIUM;
* `leaf_err_main`, the y1/(mnd) part, bounded by y1 L^K times the reciprocal sum over d
  through the divisor moment sum over m ~ M of tau(m)^B / m, HARD;
* `leaf_err_remainder`, the + 2 part, bounded by x^0.96 under (4.8) or (4.9), HARD.
`leaf_err_rearrange_split` restates `leaf_err_rearrange` verbatim.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_Decomp409b
import LeanLab.Akeno2026.DecompJ267
import LeanLab.BakerHarmanPintz1997.SPLIT_leaf_err_rearrange_p2_rem

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-- Proved glue: the multiples of q in (A, B] number at most (B - A)/q + 1. -/
theorem count_mult_Ioc_le (A B q : ℕ) (hq : 0 < q) (hAB : A ≤ B) :
    ((((Finset.Ioc A B).filter (fun k => q ∣ k)).card : ℕ) : ℝ) ≤ ((B : ℝ) - A) / q + 1 := by
  have hsub : (Finset.Ioc A B).filter (fun k => q ∣ k) ⊆
      (Finset.Ioc (A / q) (B / q)).image (fun j => q * j) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    obtain ⟨⟨h1, h2⟩, ⟨j, rfl⟩⟩ := hk
    rw [Finset.mem_image]
    refine ⟨j, Finset.mem_Ioc.2 ⟨?_, ?_⟩, rfl⟩
    · exact (Nat.div_lt_iff_lt_mul hq).2 (by rw [mul_comm]; exact h1)
    · exact (Nat.le_div_iff_mul_le hq).2 (by rw [mul_comm]; exact h2)
  have hc : ((Finset.Ioc A B).filter (fun k => q ∣ k)).card ≤ B / q - A / q := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (Finset.Ioc (A / q) (B / q)).card := Finset.card_image_le
      _ = _ := Nat.card_Ioc _ _
  have hle : A / q ≤ B / q := Nat.div_le_div_right hAB
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hB : ((B / q : ℕ) : ℝ) ≤ (B : ℝ) / q := Nat.cast_div_le
  have hA0 : A < A / q * q + q := Nat.lt_div_mul_add hq
  have hA : (A : ℝ) / q < ((A / q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hq']
    have : (A : ℝ) < ((A / q : ℕ) : ℝ) * q + q := by exact_mod_cast hA0
    linarith
  calc ((((Finset.Ioc A B).filter (fun k => q ∣ k)).card : ℕ) : ℝ)
      ≤ ((B / q - A / q : ℕ) : ℝ) := by exact_mod_cast hc
    _ = ((B / q : ℕ) : ℝ) - ((A / q : ℕ) : ℝ) := Nat.cast_sub hle
    _ ≤ (B : ℝ) / q - ((A : ℝ) / q - 1) := by linarith
    _ = ((B : ℝ) - A) / q + 1 := by ring

/-- Proved glue: psiErr l is the sum over the dagger range of d of the indicator of d | l. -/
theorem psiErr_eq_sum (l : ℕ) (w γ : ℝ) :
    psiErr l w γ = ∑ d ∈ (siftingProduct w).divisors.filter
      (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w), (if d ∣ l then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole, Finset.filter_filter]
  unfold psiErr
  congr 2
  exact Finset.filter_congr fun d _ => by tauto

/-- LEAF: display (4.13), the swap of sums and the interval count. MEDIUM.
For k = mnl in (x - y, x], psiErr l counts the d | P(w), gamma at most d below gamma w,
with d | l, that is mnd | k. The multiples of mnd in the window number at most
(y + 1)/(mnd) + 1, at most y/(mnd) + 2 as mnd is at least 1. Needs 0 at most y at most x.
Non-vacuity: a = b = 0 gives 0 at most 0; for a = b = 1 both sides are positive. -/
theorem leaf_err_count (a b : ℕ → ℂ) (M N w γ x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, conv2E a b M N w γ k ≤
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        ∑ d ∈ (siftingProduct w).divisors.filter (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w),
          ‖a m‖ * ‖b n‖ * (y / ((m : ℝ) * n * d) + 2) := by
  set D := (siftingProduct w).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)
    with hD
  have hDeq : (siftingProduct w).divisors.filter (fun d => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w) =
      D.image (fun d : ℕ => (d : ℝ)) := by
    ext r
    simp only [hD, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      simp at h1
      obtain ⟨a, ha, rfl⟩ := h1
      exact ⟨a, ⟨by simpa using ha, h2⟩, rfl⟩
    · rintro ⟨a, ⟨ha, h2⟩, rfl⟩
      refine ⟨?_, h2⟩
      simpa using ha
  rw [hDeq]
  simp_rw [Finset.sum_image (fun _ _ _ _ h => Nat.cast_injective h)]
  set W := Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊ with hW
  have hAB : ⌊x - y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
  have hwin : ((⌊x⌋₊ : ℕ) : ℝ) - ((⌊x - y⌋₊ : ℕ) : ℝ) ≤ y + 1 := by
    have h1 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h2 : x - y < ((⌊x - y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  unfold conv2E
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hm1 : 1 ≤ m := by rw [Finset.mem_Ioc] at hm; omega
  have hn1 : 1 ≤ n := by rw [Finset.mem_Ioc] at hn; omega
  have hmn : 0 < m * n := Nat.mul_pos hm1 hn1
  have hk : ∀ k ∈ W, (if m * n ∣ k then ‖a m‖ * ‖b n‖ * psiErr (k / (m * n)) w γ else 0) =
      ∑ d ∈ D, (if m * n * d ∣ k then ‖a m‖ * ‖b n‖ else 0) := by
    intro k _
    rw [psiErr_eq_sum, ← hD]
    split_ifs with h
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hdd : m * n * d ∣ k
      · rw [if_pos hdd, if_pos ((Nat.dvd_div_iff_mul_dvd h).2 hdd)]; ring
      · rw [if_neg hdd, if_neg (fun h' => hdd ((Nat.dvd_div_iff_mul_dvd h).1 h'))]; ring
    · symm
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [if_neg]
      intro h'
      exact h (Dvd.dvd.trans (Dvd.intro d rfl) h')
  rw [Finset.sum_congr rfl hk, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d hd
  have hd1 : 1 ≤ d := by
    have := Nat.pos_of_mem_divisors (Finset.mem_filter.1 hd).1
    omega
  have hq : 0 < m * n * d := Nat.mul_pos hmn hd1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcnt := count_mult_Ioc_le ⌊x - y⌋₊ ⌊x⌋₊ (m * n * d) hq hAB
  have hqR : (1 : ℝ) ≤ ((m * n * d : ℕ) : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < ((m * n * d : ℕ) : ℝ) := by linarith
  have hb : ((⌊x⌋₊ : ℝ) - (⌊x - y⌋₊ : ℝ)) / ((m * n * d : ℕ) : ℝ) + 1 ≤
      y / ((m : ℝ) * n * d) + 2 := by
    have hcast : ((m * n * d : ℕ) : ℝ) = (m : ℝ) * n * d := by push_cast; ring
    rw [← hcast]
    have : ((⌊x⌋₊ : ℝ) - (⌊x - y⌋₊ : ℝ)) / ((m * n * d : ℕ) : ℝ) ≤
        (y + 1) / ((m * n * d : ℕ) : ℝ) := div_le_div_of_nonneg_right hwin hq0.le
    have h1 : 1 / ((m * n * d : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hq0]; exact hqR
    rw [add_div] at this
    linarith
  have hab : 0 ≤ ‖a m‖ * ‖b n‖ := by positivity
  calc _ = (((W.filter (fun k => m * n * d ∣ k)).card : ℕ) : ℝ) * (‖a m‖ * ‖b n‖) := rfl
    _ ≤ (y / ((m : ℝ) * n * d) + 2) * (‖a m‖ * ‖b n‖) :=
        mul_le_mul_of_nonneg_right (hcnt.trans hb) hab
    _ = _ := by ring

/-- Proved glue, display (3.1) in the form used for (4.13): the dyadic sum of |a_m|/m with
|a_m| at most tau(m)^B and M at most x is at most C L^E, from the lab's PROVED
`Akeno2026.DecompJ267.divisor_moment_log_budget221` at X = 2x. -/
theorem moment_dyadic_le (B : ℝ) : ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ x : ℝ, 2 ≤ x →
    ∀ (M : ℝ) (a : ℕ → ℂ), M ≤ x → (∀ k, ‖a k‖ ≤ tau k ^ B) →
      ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖ / (m : ℝ) ≤ C * L x ^ E := by
  obtain ⟨C, E, hC, hE, hb⟩ :=
    LeanLab.Akeno2026.DecompJ267.divisor_moment_log_budget221 1 ⌈B⌉₊
  refine ⟨C * 2 ^ E, E, by positivity, hE, fun x hx M a hM ha => ?_⟩
  have h2x : (2 : ℝ) ≤ 2 * x := by linarith
  have hb' := hb (2 * x) h2x
  rw [Real.rpow_one] at hb'
  have hLx0 : 0 ≤ L x := by unfold L; exact Real.log_nonneg (by linarith)
  have hl : Real.log (2 * x) ≤ 2 * L x := by
    unfold L
    rw [Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hl0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hpow : Real.log (2 * x) ^ E ≤ 2 ^ E * L x ^ E := by
    rw [← Real.mul_rpow (by norm_num) hLx0]
    exact Real.rpow_le_rpow hl0 hl hE
  calc ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ‖a m‖ / (m : ℝ)
      ≤ ∑ m ∈ Finset.Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (m.divisors.card : ℝ) ^ (⌈B⌉₊) / m := by
        apply Finset.sum_le_sum
        intro m hm
        have hm1 : 1 ≤ m := by rw [Finset.mem_Ioc] at hm; omega
        exact div_le_div_of_nonneg_right ((ha m).trans (tau_rpow_le_card_pow B hm1))
          (Nat.cast_nonneg _)
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊2 * x⌋₊, (m.divisors.card : ℝ) ^ (⌈B⌉₊) / m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_Ioc] at hm
          rw [Finset.mem_Icc]
          exact ⟨by omega, le_trans hm.2 (Nat.floor_le_floor (by linarith))⟩
        · intro m _ _
          positivity
    _ ≤ C * Real.log (2 * x) ^ E := hb'
    _ ≤ C * (2 ^ E * L x ^ E) := mul_le_mul_of_nonneg_left hpow hC
    _ = C * 2 ^ E * L x ^ E := by ring

/-- LEAF: display (4.13), the main part. HARD.
The y1/(mnd) terms factor as y1 times the sum over m ~ M of |a_m|/m, the same over n, and
the reciprocal sum over d. Under (4.8) or (4.9), M, N are at most x, so by (3.1) each
factor is at most the sum over m up to 2x of tau(m)^|B| / m, at most C L^K.
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_main :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C K X0 : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * (y1 x / ((m : ℝ) * n * d)) ≤
          C * (y1 x * L x ^ K *
            ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ))) := by
  refine ⟨1, one_pos, ?_⟩
  intro ε hε hε1 B a b M N ha hb hr
  obtain ⟨C, E, hC, hE, hmom⟩ := moment_dyadic_le B
  refine ⟨C * C, E + E, 2, mul_nonneg hC hC, by linarith, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨hMx, hNx⟩ := MN_le_self_of_size hx1 hε1 (hr x)
  have hA := hmom x hx (M x) (a x) hMx (ha x)
  have hB := hmom x hx (N x) (b x) hNx (hb x)
  have hA0 : 0 ≤ ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hB0 : 0 ≤ ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hS0 : 0 ≤ ∑ d ∈ (siftingProduct (wof x)).divisors.filter
      (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) := by
    refine Finset.sum_nonneg fun i hi => ?_
    have hi2 := (Finset.mem_filter.1 hi).2.1
    have : (0 : ℝ) ≤ i := le_trans (by norm_num) (le_trans (le_max_left 2 _) hi2)
    positivity
  have hy : 0 ≤ y1 x := (y1_pos (by linarith)).le
  have hL : 0 < L x := by unfold L; exact Real.log_pos (by linarith)
  set D := (siftingProduct (wof x)).divisors.filter
      (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x) with hD
  set A := ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ‖a x m‖ / (m : ℝ) with hAdef
  set Bs := ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊, ‖b x n‖ / (n : ℝ) with hBdef
  have hfac : (∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
        ∑ d ∈ D, ‖a x m‖ * ‖b x n‖ * (y1 x / ((m : ℝ) * n * d))) =
      y1 x * (A * Bs) * ∑ d ∈ D, (1 / (d : ℝ)) := by
    calc _ = ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          y1 x * (‖a x m‖ / (m : ℝ) * (‖b x n‖ / (n : ℝ))) * ∑ d ∈ D, (1 / (d : ℝ)) := by
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ = (∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          y1 x * (‖a x m‖ / (m : ℝ) * (‖b x n‖ / (n : ℝ)))) * ∑ d ∈ D, (1 / (d : ℝ)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => (Finset.sum_mul _ _ _).symm
      _ = _ := by
          congr 1
          rw [hAdef, hBdef, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
  rw [hfac, Real.rpow_add hL]
  have h1 := mul_le_mul hA hB hB0 (le_trans hA0 hA)
  calc _ ≤ y1 x * ((C * L x ^ E) * (C * L x ^ E)) * ∑ d ∈ D, (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hy) hS0
    _ = _ := by ring

/-- LEAF: display (4.13), the remainder. HARD.
The + 2 terms total at most 2 (M + 1)(N + 1) gamma w max tau^|B| squared. Here gamma is
x^(ε/12), w = exp(L^(9/10)) and tau(m) are x^o(1), and MN is at most x^0.775 under (4.8)
or x^(0.92 + ε/4) under (4.9), so the total is below C x^0.96 once ε is small.
Non-vacuity: a = b = 0 makes the left side zero. -/
theorem leaf_err_remainder :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X0 ≤ x →
        ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * 2 ≤ C * x ^ (0.96 : ℝ) := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro ε hε hε1 B a b M N ha hb hr
  obtain ⟨Ca, hCa, hco⟩ := rem_coef_le B
  refine ⟨24 * Ca ^ 2, Real.exp (10 ^ 30), by positivity, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by positivity)) hx
  have hx0 : 0 < x := by linarith
  obtain ⟨hMx, hNx⟩ := MN_le_self_of_size hx1 (by linarith) (hr x)
  have hxe : 0 ≤ x ^ (1 / 1000 : ℝ) := Real.rpow_nonneg hx0.le _
  have hc0 : 0 ≤ Ca * x ^ (1 / 1000 : ℝ) := mul_nonneg hCa hxe
  have hcoef : ∀ (c : ℕ → ℂ) (K : ℝ), K ≤ x → (∀ k, ‖c k‖ ≤ tau k ^ B) →
      ∀ m ∈ Finset.Ioc ⌊K⌋₊ ⌊2 * K⌋₊, ‖c m‖ ≤ Ca * x ^ (1 / 1000 : ℝ) := by
    intro c K hK hc m hm
    rw [Finset.mem_Ioc] at hm
    have hm1 : 1 ≤ m := by omega
    have hmK : (m : ℝ) ≤ 2 * K := (Nat.le_floor_iff' (by omega)).1 hm.2
    exact (hc m).trans (hco x hx1 m hm1 (by linarith))
  have hcM := rem_card_Ioc_le (M x)
  have hcN := rem_card_Ioc_le (N x)
  have hsize := rem_size_le hx1 hε.le (hr x)
  have hA : ((Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊).card : ℝ) *
      ((Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊).card : ℝ) ≤ 4 * x ^ (0.92 + ε / 4) :=
    le_trans (mul_le_mul hcM hcN (Nat.cast_nonneg _)
      (by have := le_max_left (1 : ℝ) (M x); linarith)) hsize
  have hε12 : 1 ≤ x ^ (ε / 12) := Real.one_le_rpow hx1 (by linarith)
  have he1 : 1 ≤ x ^ (1 / 1000 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hγ : cutoff ε x ≤ 2 * x ^ (ε / 12) := by
    unfold cutoff
    exact max_le (by linarith) (by linarith)
  have hγ0 : 0 ≤ cutoff ε x := le_trans (by norm_num) (le_max_left 2 _)
  have hw := rem_wof_le hx
  have hw1 : 1 ≤ wof x := by
    unfold wof
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hcD := rem_card_D_le (cutoff ε x) (wof x) (mul_nonneg hγ0 (by linarith))
  have hB' : ((((siftingProduct (wof x)).divisors.filter
      (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x)).card : ℝ)) ≤
        3 * (x ^ (ε / 12) * x ^ (1 / 1000 : ℝ)) := by
    have h1 : cutoff ε x * wof x ≤ 2 * x ^ (ε / 12) * x ^ (1 / 1000 : ℝ) :=
      mul_le_mul hγ hw (by linarith) (by linarith)
    have h2 : 1 ≤ x ^ (ε / 12) * x ^ (1 / 1000 : ℝ) := one_le_mul_of_one_le_of_one_le hε12 he1
    nlinarith
  have hX1 : 0 ≤ x ^ (0.92 + ε / 4) := Real.rpow_nonneg hx0.le _
  have hX2 : 0 ≤ x ^ (ε / 12) := Real.rpow_nonneg hx0.le _
  calc _ ≤ ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            (Ca * x ^ (1 / 1000 : ℝ)) * (Ca * x ^ (1 / 1000 : ℝ)) * 2 :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun d _ =>
          mul_le_mul_of_nonneg_right (mul_le_mul (hcoef (a x) (M x) hMx (ha x) m hm)
            (hcoef (b x) (N x) hNx (hb x) n hn) (norm_nonneg _) hc0) (by norm_num)
    _ = (((Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊).card : ℝ) *
          ((Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊).card : ℝ)) *
          ((((siftingProduct (wof x)).divisors.filter
            (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x)).card : ℝ)) *
          ((Ca * x ^ (1 / 1000 : ℝ)) * (Ca * x ^ (1 / 1000 : ℝ)) * 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (4 * x ^ (0.92 + ε / 4)) * (3 * (x ^ (ε / 12) * x ^ (1 / 1000 : ℝ))) *
          ((Ca * x ^ (1 / 1000 : ℝ)) * (Ca * x ^ (1 / 1000 : ℝ)) * 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hA hB' (Nat.cast_nonneg _) (by linarith))
          (by positivity)
    _ = 24 * Ca ^ 2 * (x ^ (0.92 + ε / 4) * x ^ (ε / 12) * x ^ (1 / 1000 : ℝ) *
          x ^ (1 / 1000 : ℝ) * x ^ (1 / 1000 : ℝ)) := by ring
    _ = 24 * Ca ^ 2 * x ^ (0.92 + ε / 4 + ε / 12 + 1 / 1000 + 1 / 1000 + 1 / 1000) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0,
          ← Real.rpow_add hx0]
    _ ≤ 24 * Ca ^ 2 * x ^ (0.96 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num; linarith)) (by positivity)

/-- Proved glue: y1 x is at most x for x at least 1. -/
theorem y1_le_self {x : ℝ} (hx : 1 ≤ x) : y1 x ≤ x := by
  unfold y1
  have h0 : 0 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hx) _
  have h1 : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith

/-- `leaf_err_rearrange`, verbatim, from the PROVED `leaf_err_count`, `leaf_err_main` and
`leaf_err_remainder`. -/
theorem leaf_err_rearrange_split :
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
  obtain ⟨ε2, hε2, h2⟩ := leaf_err_main
  obtain ⟨ε3, hε3, h3⟩ := leaf_err_remainder
  refine ⟨min ε2 ε3, lt_min hε2 hε3, ?_⟩
  intro ε hε hεs B a b M N ha hb hr
  obtain ⟨C2, K, X2, hC2, hK, h2'⟩ :=
    h2 ε hε (hεs.trans_le (min_le_left _ _)) B a b M N ha hb hr
  obtain ⟨C3, X3, hC3, h3'⟩ :=
    h3 ε hε (hεs.trans_le (min_le_right _ _)) B a b M N ha hb hr
  refine ⟨C2 + C3, K, max (max X2 X3) 1, add_nonneg hC2 hC3, hK, ?_⟩
  intro x hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hy : 0 < y1 x := y1_pos (by linarith)
  have hyx : y1 x ≤ x := y1_le_self hx1
  set S := ∑ d ∈ (siftingProduct (wof x)).divisors.filter
    (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x), (1 / (d : ℝ)) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine Finset.sum_nonneg fun i hi => ?_
    have hi2 := (Finset.mem_filter.1 hi).2.1
    have : (0 : ℝ) ≤ i := le_trans (by norm_num) (le_trans (le_max_left 2 _) hi2)
    positivity
  have hL : 0 ≤ L x := Real.log_nonneg hx1
  have hmain0 : 0 ≤ y1 x * L x ^ K * S :=
    mul_nonneg (mul_nonneg hy.le (Real.rpow_nonneg hL _)) hS0
  have hp0 : 0 ≤ x ^ (0.96 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc _ ≤ _ := leaf_err_count (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) x (y1 x) hy.le hyx
    _ = (∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * (y1 x / ((m : ℝ) * n * d))) +
        ∑ m ∈ Finset.Ioc ⌊M x⌋₊ ⌊2 * M x⌋₊, ∑ n ∈ Finset.Ioc ⌊N x⌋₊ ⌊2 * N x⌋₊,
          ∑ d ∈ (siftingProduct (wof x)).divisors.filter
              (fun d => cutoff ε x ≤ (d : ℝ) ∧ (d : ℝ) < cutoff ε x * wof x),
            ‖a x m‖ * ‖b x n‖ * 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ C2 * (y1 x * L x ^ K * S) + C3 * x ^ (0.96 : ℝ) := add_le_add (h2' x hx2) (h3' x hx3)
    _ ≤ (C2 + C3) * (y1 x * L x ^ K * S + x ^ (0.96 : ℝ)) := by nlinarith

#print axioms leaf_err_count
#print axioms count_mult_Ioc_le
#print axioms psiErr_eq_sum
#print axioms y1_le_self
#print axioms leaf_err_rearrange_split
#print axioms leaf_err_main
#print axioms moment_dyadic_le
#print axioms leaf_err_remainder
#print axioms rem_coef_le
#print axioms rem_wof_le
#print axioms rem_card_D_le
#print axioms rem_card_Ioc_le
#print axioms rem_size_le
#print axioms tau_rpow_le_card_pow
#print axioms MN_le_self_of_size

end LeanLab.BakerHarmanPintz1997.Decomp409b
