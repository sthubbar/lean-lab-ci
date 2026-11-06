/-
P0093 pages 162 and 163. Weighted phase alignment from a cosine deficit.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.EntropyBridge412

namespace LeanLab.Linnik1951

open Finset Complex

/-- P0093 page 163 equation 7.10. For every positive radius there
is a positive cosine deficit threshold that forces distance to an
integer within that radius. Round supplies the nearest integer. -/
theorem cosine_deficit_radius435 (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : ℝ, 1 - Real.cos (2 * Real.pi * x) < d →
      ∃ z : ℤ, |x - z| ≤ ρ := by
  let t : ℝ := min ρ (1 / 4)
  have ht : 0 < t := lt_min hρ (by norm_num)
  have ht4 : t ≤ 1 / 4 := min_le_right _ _
  have htp : 2 * Real.pi * t ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (2 * Real.pi * t) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      htp (by positivity : (0 : ℝ) < 2 * Real.pi * t)
    simpa only [Real.cos_zero] using h
  refine ⟨1 - Real.cos (2 * Real.pi * t), by linarith, ?_⟩
  intro x hx
  refine ⟨round x, ?_⟩
  by_contra h
  have hr : ρ < |x - (round x : ℤ)| := lt_of_not_ge h
  have hrhalf : |x - (round x : ℤ)| ≤ (1 / 2 : ℝ) := abs_sub_round x
  have hcosx : Real.cos (2 * Real.pi * x) =
      Real.cos (2 * Real.pi * |x - (round x : ℤ)|) := by
    have he : 2 * Real.pi * x = 2 * Real.pi * (x - (round x : ℤ)) +
        (round x : ℤ) * (2 * Real.pi) := by ring
    rw [he, Real.cos_add_int_mul_two_pi, ← Real.cos_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2 * Real.pi * t by positivity)
    (show 2 * Real.pi * |x - (round x : ℤ)| ≤ Real.pi by nlinarith [Real.pi_pos])
    (show 2 * Real.pi * t ≤ 2 * Real.pi * |x - (round x : ℤ)| by
      exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hr.le) (by positivity))
  rw [hcosx] at hx
  linarith

/-- P0093 page 162 equation 7.8. A unit complex rotation is an
exponential of its argument. Multiplying a negative Fourier phase by
that rotation subtracts one common real phase inside the cosine. -/
theorem rotation_cosine435 (u : ℂ) (hu : ‖u‖ = 1) (x : ℝ) :
    (u * Complex.exp ((-(2 * Real.pi * x) : ℝ) * Complex.I)).re =
      Real.cos (2 * Real.pi * (x - u.arg / (2 * Real.pi))) := by
  have he : Complex.exp ((u.arg : ℂ) * Complex.I) = u := by
    simpa only [hu, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I u
  conv_lhs => rw [← he, ← Complex.exp_add]
  have ha : (u.arg : ℂ) * Complex.I +
      ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * (x - u.arg / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [ha, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- P0093 page 162 equations 7.8 and 7.9. The weighted cosine
deficit is small when the norm of the weighted phase sum is almost
its total weight. This is the finite scalar identity before counting
exceptional indices. -/
theorem weighted_deficit435 (M : ℕ) (w θ : ℕ → ℝ) (η : ℝ)
    (hw : ∀ m ∈ range M, 0 ≤ w m ∧ w m ≤ 1)
    (hη : 0 ≤ η)
    (hlarge : (1 - η) * (∑ m ∈ range M, w m) <
      ‖∑ m ∈ range M, (w m : ℂ) *
        Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)‖) :
    ∃ φ : ℝ, ∑ m ∈ range M, w m *
      (1 - Real.cos (2 * Real.pi * (θ m - φ))) < η * M := by
  let Z : ℂ := ∑ m ∈ range M, (w m : ℂ) *
    Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)
  obtain ⟨u, hu, huZ⟩ := LeanLab.Linnik.Gallagher1975Lemma1.exists_rot Z
  refine ⟨u.arg / (2 * Real.pi), ?_⟩
  have hs : (u * Z).re = ∑ m ∈ range M, w m *
      Real.cos (2 * Real.pi * (θ m - u.arg / (2 * Real.pi))) := by
    dsimp [Z]
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [show u * ((w m : ℂ) * Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)) =
      (w m : ℂ) * (u * Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      rotation_cosine435 u hu (θ m)]
  have hW : (∑ m ∈ range M, w m) ≤ (M : ℝ) := by
    calc
      _ ≤ ∑ _m ∈ range M, (1 : ℝ) := Finset.sum_le_sum (fun m hm => (hw m hm).2)
      _ = _ := by simp
  have heq : (∑ m ∈ range M, w m *
      (1 - Real.cos (2 * Real.pi * (θ m - u.arg / (2 * Real.pi))))) =
      (∑ m ∈ range M, w m) - ‖Z‖ := by
    calc
      _ = ∑ m ∈ range M, (w m - w m *
          Real.cos (2 * Real.pi * (θ m - u.arg / (2 * Real.pi)))) := by
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← hs, huZ]
  rw [heq]
  change (1 - η) * (∑ m ∈ range M, w m) < ‖Z‖ at hlarge
  nlinarith

end LeanLab.Linnik1951

namespace LeanLab.Linnik1951

/-- P0093 page 162 the exceptional index count between equations
7.8 and 7.9. Positive lower damping weights turn a small total
weighted deficit into a small number of indices above a fixed deficit.
Only finite sums and real inequalities occur here. -/
theorem weighted_bad_count435 (M : ℕ) (w D : ℕ → ℝ) (ε d : ℝ)
    (hε : 0 < ε) (hd : 0 < d)
    (hw : ∀ m ∈ Finset.range M, Real.exp (-1) ≤ w m)
    (hD : ∀ m ∈ Finset.range M, 0 ≤ D m)
    (hs : ∑ m ∈ Finset.range M, w m * D m <
      ε * d * Real.exp (-1) * M) :
    ((Finset.range M).filter (fun m => d ≤ D m)).card ≤ ε * (M : ℝ) := by
  classical
  let B := (Finset.range M).filter (fun m => d ≤ D m)
  have hb : (B.card : ℝ) * (d * Real.exp (-1)) ≤
      ∑ m ∈ Finset.range M, w m * D m := by
    calc
      _ = ∑ _m ∈ B, d * Real.exp (-1) := by simp
      _ ≤ ∑ m ∈ B, w m * D m := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hw' := hw m hm'.1
        simpa only [mul_comm] using
          (mul_le_mul hw' hm'.2 hd.le ((Real.exp_pos (-1)).le.trans hw'))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun m hm _ => mul_nonneg ((Real.exp_pos (-1)).le.trans (hw m hm)) (hD m hm))
  have hp : 0 < d * Real.exp (-1) := mul_pos hd (Real.exp_pos _)
  change (B.card : ℝ) ≤ ε * M
  nlinarith

/-- P0093 page 162 equations 7.8 and 7.9 through page 163 equation
7.10. The exact generic weighted alignment input follows from the
rotation identity, weighted deficit count and cosine radius bound. -/
theorem weighted_phase_alignment_proved435 (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∀ M : ℕ,
      ∀ w θ : ℕ → ℝ,
        (∀ m ∈ Finset.range M, Real.exp (-1) ≤ w m ∧ w m ≤ 1) →
        (1 - η) * (∑ m ∈ Finset.range M, w m) <
          ‖∑ m ∈ Finset.range M, (w m : ℂ) *
            Complex.exp ((-(2 * Real.pi * θ m) : ℝ) * Complex.I)‖ →
        ∃ φ : ℝ, ∃ S : Finset ℕ, S ⊆ Finset.range M ∧
          (1 - ε) * (M : ℝ) ≤ S.card ∧
          ∀ m ∈ S, ∃ z : ℤ, |θ m - φ - z| ≤ ρ := by
  classical
  obtain ⟨d, hd, hradius⟩ := cosine_deficit_radius435 ρ hρ
  let η : ℝ := min (ε * d * Real.exp (-1)) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ ε * d * Real.exp (-1) := min_le_left _ _
  refine ⟨η, hη, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro M w θ hw hlarge
  obtain ⟨φ, hsum⟩ := weighted_deficit435 M w θ η
    (fun m hm => ⟨(Real.exp_pos (-1)).le.trans (hw m hm).1, (hw m hm).2⟩) hη.le hlarge
  let D : ℕ → ℝ := fun m => 1 - Real.cos (2 * Real.pi * (θ m - φ))
  have hD : ∀ m ∈ Finset.range M, 0 ≤ D m := fun m _ =>
    sub_nonneg.mpr (Real.cos_le_one _)
  have hcount := weighted_bad_count435 M w D ε d hε hd
    (fun m hm => (hw m hm).1) hD
    (lt_of_lt_of_le hsum (mul_le_mul_of_nonneg_right hηsmall (Nat.cast_nonneg M)))
  let B := (Finset.range M).filter (fun m => d ≤ D m)
  let S := Finset.range M \ B
  refine ⟨φ, S, Finset.sdiff_subset, ?_, ?_⟩
  · have hB : B.card ≤ M := by
      simpa using (Finset.card_le_card (Finset.filter_subset (fun m => d ≤ D m) (Finset.range M)))
    have hc : (S.card : ℝ) = (M : ℝ) - B.card := by
      dsimp only [S]
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range,
        Nat.cast_sub hB]
    rw [hc]
    change (B.card : ℝ) ≤ ε * M at hcount
    linarith
  · intro m hm
    have hb := (Finset.mem_sdiff.mp hm).2
    have hm' := (Finset.mem_sdiff.mp hm).1
    have hlt : D m < d := by
      by_contra h
      exact hb (Finset.mem_filter.mpr ⟨hm', le_of_not_gt h⟩)
    exact hradius (θ m - φ) hlt

end LeanLab.Linnik1951
