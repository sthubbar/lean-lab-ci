import LeanLab.ExceptionalSet.Decomp523a

/-!
Split of the one sided trigonometric majorant input of `Decomp523a`.

`leaf_one_sided_majorant` asks for an absolute constant plus, for every half
open interval and cutoff, a constant coefficient and a family of coefficients
with three properties.  This file keeps that statement, name for name, as
`leaf_one_sided_majorant_split`, and moves its content into three concrete
leaves whose coefficients are written out in full, together with the
elementary cutoff one case, which the assembly itself proves.

* `leaf_fejer_convolution_majorant`: the squared exponential sum of the cutoff
  is the Fejer kernel; its mass on a short arc is bounded below, so the
  smoothed periodic indicator of the slightly enlarged interval dominates the
  interval indicator.
* `leaf_fejer_sum_representation`: the finite Fourier expansion identity, which
  turns the weighted cosine sum into the smoothed indicator minus its mean.
* `leaf_fourier_coefficient_le`: the k-th Fourier coefficient of a periodic
  interval indicator is at most one over pi k, which bounds the weights.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- LEAF. Analytic estimate, the Fejer convolution step: the squared exponential
sum of the cutoff is nonnegative and carries mass at least a fixed multiple of
one on the short arc of length twice the shrinking parameter, so the smoothed
periodic indicator of the enlarged interval dominates the half open interval
indicator at every point. -/
theorem leaf_fejer_convolution_majorant
    (a b : ℝ) (H : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hH : 2 ≤ H)
    (s : ℝ) (hs : 0 < s) (hs2 : 2 * s = 1 / ((H : ℝ) + 1)) :
    ∀ x : ℝ,
      (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        12 * (∫ t in (0 : ℝ)..1,
          (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
            (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
          + 12 * (b - a + 2 * s)
          - 12 * (∫ y in (0 : ℝ)..1,
              (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) := by
  sorry

/-- LEAF. Finite Fourier expansion identity: every coefficient family that
agrees with the weighted Fourier coefficients of the enlarged periodic
indicator has a truncated cosine sum equal to the fixed constant times the
difference of the smoothed indicator and its mean. -/
theorem leaf_fejer_sum_representation
    (a b s : ℝ) (H : ℕ) (hH : 1 ≤ H) (x : ℝ) (F : ℕ → ℂ)
    (hF : ∀ h, F h =
      (2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) •
        ∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
            eC (-(((h : ℝ) + 1) * y))) :
    (∑ h ∈ Finset.range H, (F h * eC (((h : ℝ) + 1) * x)).re) =
      12 * (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
      - 12 * (∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) := by
  sorry

/-- LEAF. Coefficient estimate: the k-th Fourier coefficient of a periodic half
open interval indicator has modulus at most one over pi k. -/
theorem leaf_fourier_coefficient_le (a b s : ℝ) (H : ℕ) :
    ∀ h ∈ Finset.range H,
      ‖∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
            eC (-(((h : ℝ) + 1) * y))‖ ≤ 1 / (Real.pi * ((h : ℝ) + 1)) := by
  sorry

/-- The target statement, assembled from the three leaves; the cutoff one case
is proved here, since a constant coefficient already dominates the indicator
at that cutoff. -/
theorem leaf_one_sided_majorant_split :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (H : ℕ),
      0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ H →
      ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
        c₀ ≤ C * (b - a + 1 / ((H : ℝ) + 1)) ∧
        (∀ h ∈ Finset.range H, ‖c h‖ ≤ C) ∧
        ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * x)).re := by
  refine ⟨12, by norm_num, ?_⟩
  intro a b H ha hab hb hH
  rcases eq_or_lt_of_le hH with h1 | h2
  · obtain rfl : H = 1 := h1.symm
    refine ⟨1, fun _ => 0, ?_, ?_, ?_⟩
    · have hcast : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
      rw [hcast]
      have hhalf : (1 : ℝ) / ((1 : ℝ) + 1) = 1 / 2 := by norm_num
      rw [hhalf]
      nlinarith
    · intro h hh
      simp
    · intro x
      simp only [zero_mul, Complex.zero_re]
      split_ifs <;> norm_num
  · have hH1 : 1 ≤ H := by omega
    have hH2 : 2 ≤ H := h2
    set s : ℝ := 1 / (2 * ((H : ℝ) + 1)) with hsdef
    have hs : 0 < s := by rw [hsdef]; positivity
    have hs2 : 2 * s = 1 / ((H : ℝ) + 1) := by rw [hsdef]; field_simp
    let D : ℕ → ℂ := fun h => ∫ y in (0 : ℝ)..1,
      (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
        eC (-(((h : ℝ) + 1) * y))
    let c : ℕ → ℂ := fun h => (2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) • D h
    refine ⟨12 * (b - a + 2 * s), c, ?_, ?_, ?_⟩
    · rw [hs2]
    · intro h hh
      have hhH : h + 1 ≤ H := by
        have := Finset.mem_range.mp hh
        omega
      have hHpos : (0 : ℝ) < (H : ℝ) := by
        have : (0 : ℕ) < H := by omega
        exact_mod_cast this
      have hkpos : (0 : ℝ) < (h : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
        linarith
      have hw0 : (0 : ℝ) ≤ ((h : ℝ) + 1) / (H : ℝ) := by positivity
      have hw1 : ((h : ℝ) + 1) / (H : ℝ) ≤ 1 := by
        rw [div_le_one hHpos]
        exact_mod_cast hhH
      have hw : |1 - ((h : ℝ) + 1) / (H : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have hD : ‖D h‖ ≤ 1 / (Real.pi * ((h : ℝ) + 1)) :=
        leaf_fourier_coefficient_le a b s H h hh
      have hnorm : ‖c h‖ = |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| * ‖D h‖ := by
        show ‖(2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) • D h‖ = _
        rw [norm_smul, Real.norm_eq_abs]
      have h24 : |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| ≤ 24 := by
        have hsplit : |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| =
            24 * |1 - ((h : ℝ) + 1) / (H : ℝ)| := by
          rw [show (2 : ℝ) * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ)) =
            24 * (1 - ((h : ℝ) + 1) / (H : ℝ)) from by ring, abs_mul]
          norm_num
        rw [hsplit]
        nlinarith [hw]
      calc ‖c h‖ = |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| * ‖D h‖ := hnorm
        _ ≤ 24 * (1 / (Real.pi * ((h : ℝ) + 1))) := by
            exact mul_le_mul h24 hD (norm_nonneg _) (by norm_num)
        _ ≤ 12 := by
            rw [mul_one_div, div_le_iff₀ (by positivity)]
            nlinarith [Real.pi_gt_three, hkpos]
    · intro x
      have hm := leaf_fejer_convolution_majorant a b H ha hab hb hH2 s hs hs2 x
      have hsum : (∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * x)).re) =
          12 * (∫ t in (0 : ℝ)..1,
            (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
              (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
          - 12 * (∫ y in (0 : ℝ)..1,
              (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) :=
        leaf_fejer_sum_representation a b s H hH1 x c (fun h => rfl)
      rw [hsum]
      linarith

end LeanLab.ExceptionalSet.Decomp523a
