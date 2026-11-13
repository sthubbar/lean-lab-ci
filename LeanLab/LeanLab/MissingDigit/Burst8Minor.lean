import LeanLab.MissingDigit.Burst8Range58

/-!
# Burst 8, a minor arc bound for `S♯₄` replacing Proposition 3.5 of Kim

Paper: P0057, J. Kim, arXiv 2412.19975v1, Proposition 3.5, page 13, states
`S♯₄(α; H) ≪ δH` on the minor arcs, by an inverse theorem for type I sums. Here a weaker bound
`S♯₄(α; H) ≪ H X^{-7ε/10}` is proved directly: `d♯₄` only involves divisors `m ≤ X^{3ε/20}`,
which lie below the major arc denominator bound `Q = X^ε`, so on the minor arcs every `mα` is
at least `mβ(δ)` from an integer, and each sum over multiples of `m` is bounded by summation
by parts. The weaker power saving still suffices for Proposition 2.5.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.MissingDigit.Burst8Minor

open Finset Real MeasureTheory Filter
open LeanLab.MissingDigit LeanLab.MissingDigit.Burst4Split LeanLab.MissingDigit.Burst8P2
  LeanLab.MissingDigit.Burst8L17 LeanLab.MissingDigit.Burst8Major
  LeanLab.MissingDigit.Burst8P23 LeanLab.MissingDigit.Burst8Range58

attribute [local instance] Classical.propDecidable

/-- If `|mα - b| ≤ mβ` for some `1 ≤ m ≤ M` and integer `b`, with `2M < Q`, `β < 1/Q` and
`α ∈ (1/Q, 1 + 1/Q]`, then `α` lies on a major arc. -/
theorem mem_majorArcs_of_close {ε : ℝ} {X : ℕ} {H : ℝ} {α : ℝ} (hα : α ∈ arcRange ε X)
    (hβ0 : 0 ≤ betaDelta ε X H) (hβQ : betaDelta ε X H < 1 / Qpar ε X) {m M : ℕ} (hm : 1 ≤ m)
    (hmM : m ≤ M) (hMQ : 2 * (M : ℝ) < Qpar ε X) {b : ℤ}
    (hb : |m * α - b| ≤ m * betaDelta ε X H) : α ∈ majorArcs ε X H := by
  set β := betaDelta ε X H
  set Qp := Qpar ε X
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hQp : 0 < Qp := by linarith
  have hα1 : 1 / Qp < α := hα.1
  have hα2 : α ≤ 1 + 1 / Qp := hα.2
  -- `|α - b/m| ≤ β`
  have hdist : |α - b / m| ≤ β := by
    have e : α - b / m = (m * α - b) / m := by field_simp
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < m), div_le_iff₀ (by linarith)]
    linarith
  rw [abs_le] at hdist
  -- `b ≥ 1`
  have hbpos : (0 : ℝ) < b := by
    have h1 : (0 : ℝ) < b / m := by
      have : β < 1 / Qp := hβQ
      linarith [hdist.1]
    have := mul_pos h1 (by linarith : (0 : ℝ) < m)
    rwa [div_mul_cancel₀ _ (by linarith)] at this
  obtain ⟨bn, rfl⟩ : ∃ bn : ℕ, b = bn := ⟨b.toNat, by
    have : (0 : ℤ) < b := by exact_mod_cast hbpos
    omega⟩
  push_cast at hdist hbpos
  -- reduce `bn/m`
  set g := Nat.gcd bn m with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  set q := m / g
  set r := bn / g
  have hcop : Nat.Coprime r q := Nat.coprime_div_gcd_div_gcd hg0
  have hgm : g ∣ m := Nat.gcd_dvd_right bn m
  have hgb : g ∣ bn := Nat.gcd_dvd_left bn m
  have hq1 : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd (by omega) hgm) hg0
  have hqm : q ≤ m := Nat.div_le_self m g
  have hfrac : (r : ℝ) / q = (bn : ℝ) / m := by
    have h1 : ((r : ℕ) : ℝ) = (bn : ℝ) / g := by rw [Nat.cast_div hgb (by exact_mod_cast hg0.ne')]
    have h2 : ((q : ℕ) : ℝ) = (m : ℝ) / g := by rw [Nat.cast_div hgm (by exact_mod_cast hg0.ne')]
    rw [h1, h2]
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqmR : (q : ℝ) ≤ m := by exact_mod_cast hqm
  -- `r ≥ 1` and `r ≤ q`
  have hr1 : 1 ≤ r := by
    have : (0 : ℝ) < r / q := by rw [hfrac]; exact div_pos hbpos (by linarith)
    have : (0 : ℝ) < r := by
      have := mul_pos this (by linarith : (0 : ℝ) < q)
      rwa [div_mul_cancel₀ _ (by linarith)] at this
    exact_mod_cast this
  have hrq : r ≤ q := by
    by_contra hcon
    push_neg at hcon
    have h1 : (q : ℝ) + 1 ≤ r := by exact_mod_cast hcon
    have h2 : 1 + 1 / (q : ℝ) ≤ r / q := by
      rw [le_div_iff₀ (by linarith)]; field_simp; linarith
    have h3 : 1 / (M : ℝ) ≤ 1 / q := one_div_le_one_div_of_le (by linarith) (by linarith)
    have h4 : 2 / Qp < 1 / (M : ℝ) := by
      rw [div_lt_div_iff₀ hQp (by linarith)]; linarith
    have h5 : (r : ℝ) / q ≤ 1 + 1 / Qp + β := by rw [hfrac]; linarith [hdist.2]
    have h6 : 1 / Qp + β < 2 / Qp := by
      have : 2 / Qp = 1 / Qp + 1 / Qp := by ring
      linarith
    linarith
  -- membership
  have hqQ : q ≤ ⌊Qp⌋₊ := Nat.le_floor (by
    have : (q : ℝ) ≤ M := le_trans hqmR hMR
    linarith)
  unfold majorArcs
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨q, Finset.mem_Icc.2 ⟨hq1, hqQ⟩, r,
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hr1, hrq⟩, hcop⟩, ?_⟩
  rw [hfrac]
  exact ⟨by linarith [hdist.2], by linarith [hdist.1]⟩

/-- On the minor arcs, `mα` is at distance more than `mβ(δ)` from every integer, for
`1 ≤ m ≤ M` with `2M < Q`. -/
theorem frac_far_of_minor {ε : ℝ} {X : ℕ} {H : ℝ} {α : ℝ}
    (hα : α ∈ arcRange ε X \ majorArcs ε X H)
    (hβ0 : 0 ≤ betaDelta ε X H) (hβQ : betaDelta ε X H < 1 / Qpar ε X) {m M : ℕ} (hm : 1 ≤ m)
    (hmM : m ≤ M) (hMQ : 2 * (M : ℝ) < Qpar ε X) :
    m * betaDelta ε X H < Int.fract (m * α) ∧
      m * betaDelta ε X H < 1 - Int.fract (m * α) := by
  constructor
  · by_contra h
    push_neg at h
    apply hα.2
    refine mem_majorArcs_of_close hα.1 hβ0 hβQ hm hmM hMQ (b := ⌊(m : ℝ) * α⌋) ?_
    rw [← Int.fract, abs_of_nonneg (Int.fract_nonneg _)]; exact h
  · by_contra h
    push_neg at h
    apply hα.2
    refine mem_majorArcs_of_close hα.1 hβ0 hβQ hm hmM hMQ (b := ⌊(m : ℝ) * α⌋ + 1) ?_
    have : (m : ℝ) * α - ((⌊(m : ℝ) * α⌋ + 1 : ℤ) : ℝ) = -(1 - Int.fract ((m : ℝ) * α)) := by
      rw [Int.fract]; push_cast; ring
    rw [this, abs_neg, abs_of_nonneg (by linarith [Int.fract_lt_one ((m : ℝ) * α)])]; exact h

/-- Partial sums of `e((K + i)θ)` are at most `1/(2x) + 1/(2(1-x))`, `x` the fractional part of
`θ`, when `0 < x < 1`. -/
theorem norm_partial_le (K : ℕ) (θ : ℝ) (h0 : 0 < Int.fract θ) (h1 : Int.fract θ < 1) (n : ℕ) :
    ‖∑ i ∈ range n, eC (((K + i : ℕ) : ℝ) * θ)‖ ≤
      1 / (2 * Int.fract θ) + 1 / (2 * (1 - Int.fract θ)) := by
  have e : ∑ i ∈ range n, eC (((K + i : ℕ) : ℝ) * θ) =
      eC (K * θ) * Gsum n (Int.fract θ) := by
    unfold Gsum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← eC_add]
    have : ((K + i : ℕ) : ℝ) * θ = (((i * ⌊θ⌋ : ℤ) : ℝ)) + (K * θ + i * Int.fract θ) := by
      rw [Int.fract]; push_cast; ring
    rw [this, eC_add, eC_int, one_mul]
  rw [e, norm_mul, norm_eC, one_mul]
  exact le_trans (norm_Gsum_le_inv_sin n h0 h1) (inv_sin_le _ h0 h1)

/-- Summation by parts: `|∑_{i<N} f(i) g(i)| ≤ A (B + N L)` when all partial sums of `g` are at
most `A`, `|f| ≤ B` and consecutive differences of `f` are at most `L`. -/
theorem norm_sum_by_parts_le {f : ℕ → ℝ} {g : ℕ → ℂ} (N : ℕ) {A B L : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hG : ∀ n, ‖∑ i ∈ range n, g i‖ ≤ A) (hf : ∀ i < N, |f i| ≤ B)
    (hΔ : ∀ i, i + 1 < N → |f (i + 1) - f i| ≤ L) :
    ‖∑ i ∈ range N, (f i : ℂ) * g i‖ ≤ A * (B + N * L) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [range_zero, Finset.sum_empty, norm_zero, CharP.cast_eq_zero, zero_mul, add_zero]
    positivity
  have e : ∑ i ∈ range N, (f i : ℂ) * g i = ∑ i ∈ range N, f i • g i := by
    simp_rw [Complex.real_smul]
  rw [e, Finset.sum_range_by_parts]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖f (N - 1) • ∑ i ∈ range N, g i‖ ≤ B * A := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hf _ (by omega)) (hG N) (norm_nonneg _) hB
  have h2 : ‖∑ i ∈ range (N - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ ≤
      (N - 1 : ℕ) * (L * A) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ i ∈ range (N - 1), ‖(f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ ≤ L * A := by
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hΔ i (by rw [Finset.mem_range] at hi; omega)) (hG _) (norm_nonneg _) hL
    refine le_trans (Finset.sum_le_sum this) ?_
    simp
  have h3 : ((N - 1 : ℕ) : ℝ) ≤ N := by
    have : N - 1 ≤ N := Nat.sub_le N 1
    exact_mod_cast this
  have h4 : ((N - 1 : ℕ) : ℝ) * (L * A) ≤ N * (L * A) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  nlinarith

/-- The sum over the multiples of one `m` on a minor arc point: at most `7 B₀ / (mβ)`. -/
theorem inner_m_bound {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 0 ≤ H) (hHX : H ≤ X) {m : ℕ}
    (hm : 1 ≤ m) (hmX : (m : ℝ) ≤ X) {R B₀ β α : ℝ} (hβ : 0 < β)
    (hB : ∀ u ∈ Set.Icc ((X : ℝ) / 2) (3 * X),
      |Pm R m (Real.log u)| ≤ B₀ ∧ |Pmd R m (Real.log u)| ≤ 3 * B₀)
    (hfar : m * β < Int.fract (m * α) ∧ m * β < 1 - Int.fract (m * α)) :
    ‖∑ n ∈ (Icc X (X + ⌊H⌋₊)).filter (fun n => m ∣ n),
        (Pm R m (Real.log n) : ℂ) * eC (n * α)‖ ≤ 7 * B₀ / (m * β) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith
  have hB₀ : 0 ≤ B₀ := le_trans (abs_nonneg _) (hB X ⟨by linarith, by linarith⟩).1
  rw [sum_dvd_eq_sum_c_j hm le_rfl]
  simp only [Finset.range_one, Finset.sum_singleton, one_mul, add_zero]
  have ha0 : 0 ≤ (((X : ℝ) / m - ((0 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ)) := by
    push_cast; simp only [sub_zero, div_one]; positivity
  rw [Jset_eq hm le_rfl (by omega) ha0]
  push_cast
  simp only [sub_zero, div_one]
  set K₀ := ⌈(X : ℝ) / m⌉₊
  set K₁ := ⌊((X : ℝ) + (⌊H⌋₊ : ℝ)) / m⌋₊
  have hK₀ : (X : ℝ) / m ≤ K₀ := Nat.le_ceil _
  have hK₁ : (K₁ : ℝ) ≤ ((X : ℝ) + (⌊H⌋₊ : ℝ)) / m := Nat.floor_le (by positivity)
  have hYm : (X : ℝ) + (⌊H⌋₊ : ℝ) ≤ X + H := by linarith [Nat.floor_le hH]
  have hKK : K₀ ≤ K₁ + 1 := le_trans (Nat.ceil_le_ceil (by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : (0 : ℝ) ≤ (⌊H⌋₊ : ℝ) := Nat.cast_nonneg _
      linarith)) (Nat.ceil_le_floor_add_one _)
  set N := K₁ + 1 - K₀
  have hsum : ∑ j ∈ Icc K₀ K₁, ((Pm R m (Real.log ((m : ℝ) * (j : ℝ))) : ℝ) : ℂ) *
      eC ((m : ℝ) * (j : ℝ) * α) =
      ∑ i ∈ range N, ((Pm R m (Real.log ((m : ℝ) * ((K₀ + i : ℕ) : ℝ))) : ℝ) : ℂ) *
        eC (((K₀ + i : ℕ) : ℝ) * ((m : ℝ) * α)) := by
    have e : Icc K₀ K₁ = Ico K₀ (K₁ + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [hsum]
  -- the bounds
  have hrange : ∀ t : ℝ, (K₀ : ℝ) ≤ t → t ≤ K₁ → (m : ℝ) * t ∈ Set.Icc ((X : ℝ) / 2) (3 * X) := by
    intro t h1 h2
    constructor
    · have : (X : ℝ) ≤ m * t := by
        have := mul_le_mul_of_nonneg_left (le_trans hK₀ h1) (by linarith : (0 : ℝ) ≤ m)
        rwa [mul_div_cancel₀ _ (by linarith)] at this
      linarith
    · have : (m : ℝ) * t ≤ X + H := by
        have := mul_le_mul_of_nonneg_left (le_trans h2 hK₁) (by linarith : (0 : ℝ) ≤ m)
        rw [mul_div_cancel₀ _ (by linarith)] at this
        linarith
      linarith
  set x := Int.fract ((m : ℝ) * α)
  have hA : ∀ n, ‖∑ i ∈ range n, eC (((K₀ + i : ℕ) : ℝ) * ((m : ℝ) * α))‖ ≤ 1 / (m * β) := by
    intro n
    refine le_trans (norm_partial_le K₀ _ (by linarith [hfar.1, mul_pos (by linarith : (0:ℝ) < m) hβ])
      (by linarith [hfar.2, mul_pos (by linarith : (0:ℝ) < m) hβ]) n) ?_
    have hmβ : 0 < (m : ℝ) * β := mul_pos (by linarith) hβ
    have h1 : 1 / (2 * x) ≤ 1 / (2 * (m * β)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hfar.1])
    have h2 : 1 / (2 * (1 - x)) ≤ 1 / (2 * (m * β)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hfar.2])
    have : 1 / (2 * ((m : ℝ) * β)) + 1 / (2 * (m * β)) = 1 / (m * β) := by field_simp; ring
    linarith
  have hf : ∀ i < N, |Pm R m (Real.log ((m : ℝ) * ((K₀ + i : ℕ) : ℝ)))| ≤ B₀ := by
    intro i hi
    refine (hB _ (hrange _ (by push_cast; linarith) ?_)).1
    have : K₀ + i ≤ K₁ := by omega
    exact_mod_cast this
  have hΔ : ∀ i, i + 1 < N → |Pm R m (Real.log ((m : ℝ) * ((K₀ + (i + 1) : ℕ) : ℝ))) -
      Pm R m (Real.log ((m : ℝ) * ((K₀ + i : ℕ) : ℝ)))| ≤ 3 * B₀ * m / X := by
    intro i hi
    set c := ((K₀ + i : ℕ) : ℝ)
    have hc1 : (K₀ : ℝ) ≤ c := by simp only [c]; push_cast; linarith
    have hcK : c + 1 ≤ K₁ := by
      have : K₀ + i + 1 ≤ K₁ := by omega
      simp only [c]; exact_mod_cast this
    have hcpos : 0 < c := by
      have : (0 : ℝ) < X / m := by positivity
      linarith
    have hderiv : ∀ t ∈ Set.Icc c (c + 1), HasDerivWithinAt (fun t => Pm R m (Real.log (m * t)))
        (Pmd R m (Real.log (m * t)) * ((m * t)⁻¹ * m)) (Set.Icc c (c + 1)) t := by
      intro t ht
      have htp : 0 < t := by linarith [ht.1]
      have hmt : (m : ℝ) * t ≠ 0 := by positivity
      have h1 := (hasDerivAt_Pm R m (Real.log (m * t))).comp t
        ((Real.hasDerivAt_log hmt).comp t ((hasDerivAt_id t).const_mul (m : ℝ)))
      simp only [mul_one] at h1
      exact h1.hasDerivWithinAt
    have hbound : ∀ t ∈ Set.Ico c (c + 1),
        ‖Pmd R m (Real.log (m * t)) * ((m * t)⁻¹ * m)‖ ≤ 3 * B₀ * m / X := by
      intro t ht
      have htp : 0 < t := by linarith [ht.1]
      have hmt := hrange t (by linarith [ht.1]) (by linarith [ht.2])
      have hX' : (X : ℝ) ≤ m * t := by
        have := mul_le_mul_of_nonneg_left (le_trans hK₀ (le_trans hc1 ht.1))
          (by linarith : (0 : ℝ) ≤ m)
        rwa [mul_div_cancel₀ _ (by linarith)] at this
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_inv, abs_of_pos (by positivity : (0:ℝ) < m * t),
        abs_of_pos (by linarith : (0 : ℝ) < m)]
      have h3 := (hB _ hmt).2
      have : (m * t)⁻¹ * (m : ℝ) ≤ m / X := by
        rw [inv_mul_eq_div]; exact div_le_div_of_nonneg_left (by linarith) hXp hX'
      calc |Pmd R m (Real.log (m * t))| * ((m * t)⁻¹ * m) ≤ (3 * B₀) * (m / X) :=
            mul_le_mul h3 this (by positivity) (by positivity)
        _ = 3 * B₀ * m / X := by ring
    have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (c + 1) ⟨by linarith, le_rfl⟩
    have e : ((K₀ + (i + 1) : ℕ) : ℝ) = c + 1 := by simp only [c]; push_cast; ring
    rw [e]
    rw [Real.norm_eq_abs] at this
    linarith
  have hL : 0 ≤ 3 * B₀ * m / X := by positivity
  have key := norm_sum_by_parts_le (f := fun i => Pm R m (Real.log ((m : ℝ) * ((K₀ + i : ℕ) : ℝ))))
    (g := fun i => eC (((K₀ + i : ℕ) : ℝ) * ((m : ℝ) * α))) N (by positivity) hB₀ hL hA hf hΔ
  refine le_trans key ?_
  have hN : (N : ℝ) * m ≤ 2 * X := by
    have h1 : (N : ℝ) ≤ K₁ + 1 - K₀ := by
      simp only [N]
      rw [Nat.cast_sub hKK]; push_cast; linarith
    have h2 : ((K₁ : ℝ) + 1 - K₀) * m ≤ H + m := by
      have a1 := mul_le_mul_of_nonneg_left hK₁ (by linarith : (0 : ℝ) ≤ m)
      have a2 := mul_le_mul_of_nonneg_left hK₀ (by linarith : (0 : ℝ) ≤ m)
      rw [mul_div_cancel₀ _ (by linarith)] at a1 a2
      nlinarith
    have : (N : ℝ) * m ≤ ((K₁ : ℝ) + 1 - K₀) * m := mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  have hmβ : 0 < (m : ℝ) * β := mul_pos (by linarith) hβ
  have h6 : (N : ℝ) * (3 * B₀ * m / X) ≤ 6 * B₀ := by
    rw [show (N : ℝ) * (3 * B₀ * m / X) = 3 * B₀ * (N * m) / X by ring, div_le_iff₀ hXp]
    nlinarith
  calc 1 / (m * β) * (B₀ + N * (3 * B₀ * m / X)) ≤ 1 / (m * β) * (7 * B₀) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 7 * B₀ / (m * β) := by ring

/-! ### The minor arc bound and Proposition 2.5 -/

theorem eventually_minor {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 3 ≤ x ^ (ε / 40) ∧ Real.log x ^ (3 ^ 6 + 1 : ℕ) ≤ x ^ ε ∧
      2 < x ^ ((3 : ℝ) / 5 - 3 * ε) ∧ 3 ≤ x ^ (17 * ε / 20) := by
  have h1 := (isLittleO_log_rpow_rpow_atTop ((3 ^ 6 + 1 : ℕ) : ℝ) hε).bound one_pos
  have h2 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 3 / 5 - 3 * ε)).eventually_gt_atTop 2
  have h3 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 17 * ε / 20)).eventually_ge_atTop 3
  have h4 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < ε / 40)).eventually_ge_atTop 3
  filter_upwards [eventually_ge_atTop 3, h1, h2, h3, h4] with x hx3 hx1 hx2 hx4 hx5
  refine ⟨hx3, hx5, ?_, hx2, hx4⟩
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul, Real.rpow_natCast] at hx1
  exact hx1

/-- A minor arc bound, PROVED, weaker than Kim's Proposition 3.5, page 13, which claims
`S♯₄(α; H) ≪ δH = H X^{-ε}`: here `S♯₄(α; H) ≪ H X^{-7ε/10}` for `α ∈ 𝔪`. -/
theorem prop_3_5_weak : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ C : ℝ, ∃ X₀ : ℕ,
    ∀ X : ℕ, X₀ ≤ X → ∀ H : ℝ,
      (X : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ (X : ℝ) ^ (1 - ε) →
      ∀ α ∈ arcRange ε X \ majorArcs ε X H,
        ‖S4sharp ε X H α‖ ≤ C * ((X : ℝ) ^ (-(7 / 10 * ε)) * H) := by
  refine ⟨1 / 10, by norm_num, fun ε hε hεε => ?_⟩
  set K₀ : ℝ := 80 / ε + 10 with hK₀
  have hK₀p : 0 < K₀ := by positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (eventually_minor hε hεε))
  refine ⟨105 * K₀ ^ 3, X₀, fun X hX H hlo hhi α hα => ?_⟩
  obtain ⟨hX3, hR3, hlogL, hX2, hX4⟩ := hX₀ X hX
  have hXp : (0 : ℝ) < X := by linarith
  have hX1 : 1 ≤ X := by exact_mod_cast (by linarith : (1 : ℝ) ≤ X)
  have hX1' : (1 : ℝ) < X := by linarith
  set R := R4 ε X with hRdef
  have hR3' : 3 ≤ R := hR3
  have hR6 : R ^ 6 = (X : ℝ) ^ (3 * ε / 20) := by
    rw [hRdef]; unfold R4; rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]; ring_nf
  have hLX : 0 < Real.log X := Real.log_pos hX1'
  have hlogR : Real.log R = ε / 40 * Real.log X := by
    rw [hRdef]; unfold R4; rw [Real.log_rpow hXp]
  have hK : (2 * Real.log X + 10 * Real.log R) / Real.log R = K₀ := by
    rw [hlogR, hK₀]; field_simp; ring
  set B₀ : ℝ := 15 * R ^ 6 * K₀ ^ 3 with hB₀def
  have hB₀p : 0 ≤ B₀ := by positivity
  have hbounds : ∀ (m : ℕ) u, u ∈ Set.Icc ((X : ℝ) / 2) (3 * X) →
      |Pm R m (Real.log u)| ≤ B₀ ∧ |Pmd R m (Real.log u)| ≤ 3 * B₀ := by
    intro m u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hlog : |Real.log u| ≤ 2 * Real.log X := by
      rw [abs_le]; constructor
      · have : 0 ≤ Real.log u := Real.log_nonneg (by linarith [hu.1])
        linarith
      · have : Real.log u ≤ Real.log ((X : ℝ) ^ 2) :=
          Real.log_le_log hu0 (by nlinarith [hu.2])
        rw [Real.log_pow] at this; push_cast at this; linarith
    have := Pm_bounds hR3' (by linarith) hlog m
    rw [hK] at this
    exact ⟨this.1, by rw [hB₀def]; linarith [this.2]⟩
  have hHX : H ≤ X := le_trans hhi (by
    calc (X : ℝ) ^ (1 - ε) ≤ (X : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = X := Real.rpow_one _)
  have hHp : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXp _) hlo
  -- `β` and `Q`
  set L := Real.log X ^ (3 ^ 6 + 1 : ℕ) with hLdef
  have hL1 : 1 ≤ L := by
    have : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hXp]
      exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
    exact one_le_pow₀ this
  have hHβ := H_mul_betaDelta (ε := ε) (X := X) hX1' hHp
  set β := betaDelta ε X H with hβdef
  have hXe : 0 < (X : ℝ) ^ ε := Real.rpow_pos_of_pos hXp _
  have hβp : 0 < β := by
    have : 0 < H * β := by rw [hHβ]; positivity
    exact pos_of_mul_pos_right this hHp.le
  have hQp : Qpar ε X = (X : ℝ) ^ ε := rfl
  have hβQ : β < 1 / Qpar ε X := by
    rw [hQp, lt_div_iff₀ hXe]
    -- `β X^ε H = X^{2ε} L ≤ X^{3ε} < X^{3/5+ε} ≤ H`
    have e1 : β * (X : ℝ) ^ ε * H = (X : ℝ) ^ ε * ((X : ℝ) ^ ε * L) := by rw [← hHβ]; ring
    have e2 : (X : ℝ) ^ ε * ((X : ℝ) ^ ε * L) ≤ (X : ℝ) ^ (3 * ε) := by
      have : (X : ℝ) ^ (3 * ε) = (X : ℝ) ^ ε * ((X : ℝ) ^ ε * (X : ℝ) ^ ε) := by
        rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]; ring_nf
      rw [this]
      apply mul_le_mul_of_nonneg_left _ hXe.le
      exact mul_le_mul_of_nonneg_left hlogL hXe.le
    have e3 : (X : ℝ) ^ (3 * ε) < (X : ℝ) ^ ((3 : ℝ) / 5 + ε) := by
      have : (X : ℝ) ^ ((3 : ℝ) / 5 + ε) = (X : ℝ) ^ ((3 : ℝ) / 5 - 3 * ε) * (X : ℝ) ^ (4 * ε) := by
        rw [← Real.rpow_add hXp]; ring_nf
      rw [this]
      have h4 : (X : ℝ) ^ (3 * ε) ≤ (X : ℝ) ^ (4 * ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have : 0 < (X : ℝ) ^ (3 * ε) := Real.rpow_pos_of_pos hXp _
      nlinarith
    have : β * (X : ℝ) ^ ε * H < 1 * H := by linarith
    exact lt_of_mul_lt_mul_right this hHp.le
  set M := ⌊R ^ 6⌋₊ with hMdef
  have hMR : (M : ℝ) ≤ R ^ 6 := Nat.floor_le (by positivity)
  have hMQ : 2 * (M : ℝ) < Qpar ε X := by
    have : Qpar ε X = (X : ℝ) ^ (3 * ε / 20) * (X : ℝ) ^ (17 * ε / 20) := by
      rw [hQp, ← Real.rpow_add hXp]; ring_nf
    rw [this, ← hR6]
    have : 0 < R ^ 6 := by positivity
    nlinarith
  have hMX : (M : ℝ) ≤ X := by
    refine le_trans hMR ?_
    rw [hR6]
    calc (X : ℝ) ^ (3 * ε / 20) ≤ (X : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = X := Real.rpow_one _
  -- the estimate
  rw [S4sharp_eq_sum_m ε hX1]
  have hterm : ∀ m ∈ Icc 1 M, ‖∑ n ∈ (Icc X (X + ⌊H⌋₊)).filter (fun n => m ∣ n),
      (Pm R m (Real.log n) : ℂ) * eC (n * α)‖ ≤ 7 * B₀ / β := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.1 hm).2
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmX : (m : ℝ) ≤ X := le_trans (by exact_mod_cast hmM) hMX
    have hfar := frac_far_of_minor hα hβp.le hβQ hm1 hmM hMQ
    refine le_trans (inner_m_bound hX1 hHp.le hHX hm1 hmX hβp (hbounds m) hfar) ?_
    rw [div_le_div_iff₀ (by positivity) hβp]
    have : 0 ≤ 7 * B₀ * β := by positivity
    nlinarith
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  -- `M · 7 B₀ / β ≤ 105 K₀³ X^{-7ε/10} H`
  have hinvβ : 1 / β ≤ (X : ℝ) ^ (-ε) * H := by
    rw [div_le_iff₀ hβp, Real.rpow_neg hXp.le]
    have : (X : ℝ) ^ ε ≤ (X : ℝ) ^ ε * L := le_mul_of_one_le_right hXe.le hL1
    have e : ((X : ℝ) ^ ε)⁻¹ * H * β = H * β / (X : ℝ) ^ ε := by ring
    rw [e, hHβ, le_div_iff₀ hXe]
    linarith
  have hR12 : R ^ 6 * R ^ 6 * (X : ℝ) ^ (-ε) = (X : ℝ) ^ (-(7 / 10 * ε)) := by
    rw [hR6, ← Real.rpow_add hXp, ← Real.rpow_add hXp]; ring_nf
  calc (M : ℝ) * (7 * B₀ / β) = 7 * (M * B₀) * (1 / β) := by ring
    _ ≤ 7 * (R ^ 6 * B₀) * ((X : ℝ) ^ (-ε) * H) := by
        apply mul_le_mul _ hinvβ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMR hB₀p) (by norm_num)
    _ = 105 * K₀ ^ 3 * ((R ^ 6 * R ^ 6 * (X : ℝ) ^ (-ε)) * H) := by rw [hB₀def]; ring
    _ = 105 * K₀ ^ 3 * ((X : ℝ) ^ (-(7 / 10 * ε)) * H) := by rw [hR12]

/-- Kim, Proposition 2.5, page 9, PROVED from `prop_3_5_weak` and `lemma_1_7_weak`, by the
paper's proof. Same statement as `Burst4Split.prop_2_5`. -/
theorem prop_2_5_p4 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h35⟩ := prop_3_5_weak
  set g₁ : ℕ := 3
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨C, X₀, hC⟩ := h35 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_smallS (by norm_num : (1 : ℝ) ≤ 4) (by positivity : (0 : ℝ) < 7 / 10 * ε)
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := lemma_1_7_weak hg3 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (max C 0 * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hXp : 0 < X := by linarith
  have hδH : 0 ≤ X ^ (-(7 / 10 * ε)) * H :=
    mul_nonneg (Real.rpow_pos_of_pos hXp _).le (by linarith)
  set M : ℝ := max C 0 * (X ^ (-(7 / 10 * ε)) * H)
  have hM0 : 0 ≤ M := mul_nonneg (le_max_right _ _) hδH
  have hbM : ∀ α ∈ arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H, ‖S4sharp ε (g ^ k) H α‖ ≤ M :=
    fun α hα => le_trans (hb α hα) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδH)
  have hmeas : MeasurableSet (arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H) :=
    measurableSet_Ioc.diff (measurableSet_majorArcs _ _ _)
  have hsub : arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H ⊆
      Set.Icc (1 / Qpar ε (g ^ k)) (1 + 1 / Qpar ε (g ^ k)) :=
    fun α hα => Set.Ioc_subset_Icc_self hα.1
  unfold minorInt
  refine le_trans (norm_sum_setIntegral_le hmeas hsub _ (S4sharp_cont _ _ _) _ hbM) ?_
  have hce := continuous_eC
  have hmono : ∫ α in arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H,
        ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖ ≤
      ∫ α in arcRange ε (g ^ k), ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖ := by
    apply setIntegral_mono_set
    · have hc : Continuous (fun α : ℝ => ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖) := by
        fun_prop
      exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    · exact Set.diff_subset.eventuallyLE
  rw [setIntegral_arcRange_norm] at hmono
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in arcRange ε (g ^ k) \ majorArcs ε (g ^ k) H,
        ‖∑ n ∈ starSet g b (g ^ k) H, eC (-(n * α))‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g) :=
        mul_le_mul_of_nonneg_left (le_trans hmono hL) hM0
    _ = max C 0 * C₂ * H * X ^ (-(7 / 10 * ε)) *
          ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g := by
        simp only [M]; ring
    _ ≤ _ := h2


/-- The minor arc leaf in the range `X^{5/8+ε} ≤ H`, from `prop_2_5_p4`. -/
theorem prop_2_5_58b : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨e, he, h⟩ := prop_2_5_p4
  refine ⟨e, he, fun ε hε hεe => ?_⟩
  obtain ⟨g₀, hg₀⟩ := h ε hε hεe
  refine ⟨g₀, fun g b hg hb hbg η hη => ?_⟩
  obtain ⟨K, hK⟩ := hg₀ g b hg hb hbg η hη
  exact ⟨K, fun k H hk hlo hhi => hK k H hk (lo_mono (by omega) hlo) hhi⟩

/-! ### The new top level theorems -/

/-- Kim, Theorem 1.1, NEW TOP LEVEL THEOREM of this burst: same statement as
`LeanLab.MissingDigit.kim_thm1_1`, same assembly as `Burst4Split.kim_thm1_1_of_split`, with the
leaves `prop_2_2_p3`, `major_arcs_bound_p4` and `prop_2_5_p4`. CONDITIONAL ON exactly two cited
inputs: `prop_2_1`, Kim's Proposition 2.1 as printed, see the QUESTION in `Burst8Range58`, and
`main_term_bound`, Kim's Section 2.2. -/
theorem kim_thm1_1_of_p6 : D4Bound (3 / 5) 7 := by
  obtain ⟨e1, he1, h1⟩ := prop_2_2_p3
  obtain ⟨e2, he2, h2⟩ := major_arcs_bound_p4
  obtain ⟨e3, he3, h3⟩ := prop_2_5_p4
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((3 : ℝ) / 5 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((3 : ℝ) / 5 + ε) = X ^ ((3 : ℝ) / 5 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((3 : ℝ) / 5 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

/-- Kim, Theorem 1.1 with `5/8` in place of `3/5`. CONDITIONAL ON exactly two cited inputs:
`prop_2_1_58`, which is MSTT Theorem 1.1 (iii) as printed, and `main_term_bound`, Kim's
Section 2.2. -/
theorem kim_thm1_1_58b : D4Bound (5 / 8) 7 := by
  obtain ⟨e1, he1, h1⟩ := prop_2_2_58
  obtain ⟨e2, he2, h2⟩ := major_arcs_bound_58
  obtain ⟨e3, he3, h3⟩ := prop_2_5_58b
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((5 : ℝ) / 8 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((5 : ℝ) / 8 + ε) = X ^ ((5 : ℝ) / 8 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((5 : ℝ) / 8 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

#check (kim_thm1_1_of_p6 : D4Bound (3 / 5) 7)
#check (kim_thm1_1_58b : D4Bound (5 / 8) 7)

#print axioms mem_majorArcs_of_close
#print axioms frac_far_of_minor
#print axioms norm_partial_le
#print axioms norm_sum_by_parts_le
#print axioms inner_m_bound
#print axioms prop_3_5_weak
#print axioms prop_2_5_p4
#print axioms kim_thm1_1_of_p6
#print axioms kim_thm1_1_58b

end LeanLab.MissingDigit.Burst8Minor
