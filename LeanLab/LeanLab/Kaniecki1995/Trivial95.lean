/-
P0022, pages 363 and 364, the elementary trivial zero correction in display 5.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.Kaniecki1995.Trivial95
open Real Set Finset

/-- The summand in display 5, page 363, with the index made real. -/
noncomputable def term (σ t u : ℝ) : ℝ :=
  (σ ^ 2 + 2 * u * σ + t ^ 2) / (2 * u * ((σ + 2 * u) ^ 2 + t ^ 2))

/-- An elementary antiderivative for the tail of display 5. -/
noncomputable def tail (σ t u : ℝ) : ℝ :=
  Real.log (((σ + 2 * u) ^ 2 + t ^ 2) / (4 * u ^ 2)) / 4

/-- Display 5, page 363. Each correction term is nonnegative. -/
theorem term_nonneg {σ t u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) :
    0 ≤ term σ t u := by
  unfold term
  positivity

/-- Display 5, page 363. The correction term splits into two decreasing factors. -/
theorem term_split {σ t u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) :
    term σ t u = σ / (2 * u * (σ + 2 * u)) +
      t ^ 2 / ((σ + 2 * u) * ((σ + 2 * u) ^ 2 + t ^ 2)) := by
  have hp : 0 < σ + 2 * u := by positivity
  have hq : 0 < (σ + 2 * u) ^ 2 + t ^ 2 := by positivity
  unfold term
  field_simp
  <;> ring

/-- Display 5, page 363. The real correction term decreases in its index. -/
theorem term_antitone {σ t : ℝ} (hσ : 0 ≤ σ) : AntitoneOn (term σ t) (Set.Ici 1) := by
  intro u hu v hv huv
  have hu0 : 0 < u := by simp only [Set.mem_Ici] at hu; linarith
  have hv0 : 0 < v := by linarith
  rw [term_split hσ hv0, term_split hσ hu0]
  apply add_le_add
  · apply div_le_div_of_nonneg_left hσ (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
    gcongr

/-- Display 5, page 363. The tail potential is nonnegative. -/
theorem tail_nonneg {σ t u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) :
    0 ≤ tail σ t u := by
  unfold tail
  apply div_nonneg _ (by norm_num)
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Display 5, page 363. The potential has derivative minus the correction term. -/
theorem tail_deriv {σ t u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) :
    HasDerivAt (tail σ t) (-term σ t u) u := by
  have hp : 0 < (σ + 2 * u) ^ 2 + t ^ 2 := by positivity
  have hu2 : (4 : ℝ) * u ^ 2 ≠ 0 := by positivity
  have hd := (((hasDerivAt_const u σ).add ((hasDerivAt_id u).const_mul 2)).pow 2).add_const (t ^ 2)
  have hb := ((hasDerivAt_id u).pow 2).const_mul 4
  have hn : ((σ + 2 * u) ^ 2 + t ^ 2) / (4 * u ^ 2) ≠ 0 := div_ne_zero hp.ne' hu2
  have h := ((hd.div hb hu2).log hn).div_const 4
  change HasDerivAt (fun v => Real.log (((σ + 2 * v) ^ 2 + t ^ 2) / (4 * v ^ 2)) / 4) _ u
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq,
    Nat.cast_ofNat, pow_one, zero_add, one_mul, mul_one]
  unfold term
  field_simp
  <;> ring

/-- Display 5, page 363. A unit step is bounded by the decrease of the potential. -/
theorem term_tel {σ t u : ℝ} (hσ : 0 ≤ σ) (hu : 1 ≤ u) :
    term σ t (u + 1) ≤ tail σ t u - tail σ t (u + 1) := by
  let φ : ℝ → ℝ := fun y => tail σ t y + y * term σ t (u + 1)
  have hd : ∀ y ∈ Set.Icc u (u + 1),
      HasDerivAt φ (-term σ t y + term σ t (u + 1)) y := by
    intro y hy
    have hy0 : 0 < y := by rcases hy with ⟨hy, _⟩; linarith
    convert (tail_deriv hσ hy0).add
      ((hasDerivAt_id y).mul_const (term σ t (u + 1))) using 1 <;> first | rfl | simp [φ]
  have hanti : AntitoneOn φ (Set.Icc u (u + 1)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc u (u + 1))
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun y hy => (hd y (Ioo_subset_Icc_self hy)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(hd y (Ioo_subset_Icc_self hy)).deriv]
      have hb := term_antitone (t := t) hσ
        (show y ∈ Set.Ici 1 by rcases hy with ⟨hy, _⟩; exact le_trans hu hy.le)
        (show u + 1 ∈ Set.Ici 1 by simp only [Set.mem_Ici]; linarith) hy.2.le
      linarith
  have h := hanti (show u ∈ Set.Icc u (u + 1) by simp)
    (show u + 1 ∈ Set.Icc u (u + 1) by simp) (by linarith)
  dsimp [φ] at h
  nlinarith

/-- Display 5, page 363. A finite tail telescopes against the potential. -/
theorem finite_tail {σ t : ℝ} (hσ : 0 ≤ σ) (N : ℕ) :
    (∑ n ∈ range N, term σ t (n + 2)) + tail σ t (N + 1) ≤ tail σ t 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h := term_tel (t := t) hσ
      (show (1 : ℝ) ≤ N + 1 by exact le_add_of_nonneg_left (Nat.cast_nonneg N))
    have hn : (N : ℝ) + 1 + 1 = N + 2 := by ring
    rw [hn] at h
    push_cast
    rw [hn]
    linarith

/-- Pages 363 and 364. The first correction term is at most one half. -/
theorem term_one_le {σ t : ℝ} (hσ : 0 ≤ σ) : term σ t 1 ≤ 1 / 2 := by
  unfold term
  have hp : 0 < (σ + 2 * 1) ^ 2 + t ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Pages 363 and 364. The potential at one is at most half of log t. -/
theorem tail_one_le {σ t : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 3 / 4) (ht : 14 ≤ t) :
    tail σ t 1 ≤ Real.log t / 2 := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < ((σ + 2 * 1) ^ 2 + t ^ 2) / (4 * 1 ^ 2) := by positivity
  have hb : ((σ + 2 * 1) ^ 2 + t ^ 2) / (4 * 1 ^ 2) ≤ t ^ 2 := by
    norm_num
    nlinarith [sq_nonneg (t - 14)]
  have hl := Real.log_le_log hp hb
  rw [Real.log_pow] at hl
  unfold tail
  linarith

/-- Pages 363 and 364, display 5. Every finite correction sum has the same bound. -/
theorem correction_partial_bound {σ t : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 3 / 4) (ht : 14 ≤ t) :
    ∀ N : ℕ, (∑ n ∈ range N, term σ t (n + 1)) ≤ 1 / 2 + Real.log t / 2 := by
  intro N
  cases N with
  | zero =>
    simp only [sum_range_zero]
    have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  | succ N =>
    rw [sum_range_succ']
    have hb := finite_tail (t := t) hσ N
    have hp := tail_nonneg (t := t) hσ (show (0 : ℝ) < N + 1 by positivity)
    have h1 := term_one_le (t := t) hσ
    have h2 := tail_one_le hσ hσ' ht
    push_cast at *
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at *
    convert_to (∑ n ∈ range N, term σ t (n + 2)) + term σ t 1 ≤
      1 / 2 + Real.log t / 2
    · congr 2
      funext n
      congr 1
      ring
    linarith


/-- Pages 363 and 364, display 5. The correction series converges. -/
theorem correction_summable {σ t : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 3 / 4) (ht : 14 ≤ t) :
    Summable (fun n : ℕ => term σ t (n + 1)) := by
  apply summable_of_sum_range_le (fun n => term_nonneg hσ (by positivity))
  exact correction_partial_bound hσ hσ' ht

/-- Pages 363 and 364, display 5. The complete correction is at most
one half plus half of log t. This suffices for display 7. -/
theorem correction_bound {σ t : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 3 / 4) (ht : 14 ≤ t) :
    (∑' n : ℕ, term σ t (n + 1)) ≤ 1 / 2 + Real.log t / 2 := by
  exact Real.tsum_le_of_sum_range_le (fun n => term_nonneg hσ (by positivity))
    (correction_partial_bound hσ hσ' ht)

/-- Pages 363 and 364. At sigma equal to five eighths and t equal to 14,
the correction series converges and is strictly positive. -/
theorem correction_instance :
    Summable (fun n : ℕ => term (5 / 8) 14 (n + 1)) ∧
      0 < ∑' n : ℕ, term (5 / 8) 14 (n + 1) := by
  have hs := correction_summable (σ := 5 / 8) (t := 14)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hs, ?_⟩
  have hfirst := hs.le_tsum 0 (fun n _ => term_nonneg (by norm_num) (by positivity))
  have hp : 0 < term (5 / 8) 14 1 := by norm_num [term]
  exact hp.trans_le (by simpa using hfirst)

end LeanLab.Kaniecki1995.Trivial95

#print axioms LeanLab.Kaniecki1995.Trivial95.term_nonneg
#print axioms LeanLab.Kaniecki1995.Trivial95.term_split
#print axioms LeanLab.Kaniecki1995.Trivial95.term_antitone
#print axioms LeanLab.Kaniecki1995.Trivial95.tail_nonneg
#print axioms LeanLab.Kaniecki1995.Trivial95.tail_deriv
#print axioms LeanLab.Kaniecki1995.Trivial95.term_tel
#print axioms LeanLab.Kaniecki1995.Trivial95.finite_tail
#print axioms LeanLab.Kaniecki1995.Trivial95.term_one_le
#print axioms LeanLab.Kaniecki1995.Trivial95.tail_one_le
#print axioms LeanLab.Kaniecki1995.Trivial95.correction_bound

#print axioms LeanLab.Kaniecki1995.Trivial95.correction_partial_bound
#print axioms LeanLab.Kaniecki1995.Trivial95.correction_summable

#print axioms LeanLab.Kaniecki1995.Trivial95.correction_instance
