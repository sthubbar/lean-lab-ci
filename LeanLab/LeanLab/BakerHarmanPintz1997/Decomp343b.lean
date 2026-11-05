/-
P0069 page 21, shifted phase cancellation for the discretization supply.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp90

namespace LeanLab.BakerHarmanPintz1997.Decomp343b
open Finset PortedVanDerCorput LowFrequency219 Progression219
attribute [local instance] Classical.propDecidable

/-- Page 21 supply bookkeeping. A natural initial segment is an integer closed interval. -/
theorem range_eq_int_sum (f : ℝ → ℂ) (n : ℕ) :
    (∑ k ∈ range (n + 1), f k) = ∑ k ∈ Icc (0 : ℤ) n, f k := by
  apply sum_bij (fun (k : ℕ) _ => (k : ℤ))
  · intro k hk
    simp only [mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le k
    · exact_mod_cast (show k ≤ n by have := mem_range.mp hk; omega)
  · intro k hk l hl h
    exact_mod_cast h
  · intro k hk
    refine ⟨k.toNat, mem_range.mpr ?_, ?_⟩
    · have h0 := (mem_Icc.mp hk).1
      have h1 := (mem_Icc.mp hk).2
      omega
    · exact Int.toNat_of_nonneg (mem_Icc.mp hk).1
  · intro k hk
    simp

/-- Page 21 supply infrastructure. Shifted logarithmic phases retain inverse frequency decay.
The frequency is normalized by two pi before using the proved first derivative test. -/
theorem shifted_phase_sum (a m : ℕ) (ha : 1 ≤ a) (hm : m ≤ a)
    (u t : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < |t|) (htsmall : |t| ≤ a) :
    ‖∑ k ∈ range m, ((a : ℝ) + k + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤
      8 * Real.pi * a / |t| := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  let T : ℝ := |t| / (2 * Real.pi)
  have hT : 0 < T := by dsimp [T]; positivity
  have hsmall : T ≤ (a : ℝ) / 2 := by
    dsimp [T]
    rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  cases m with
  | zero => simp; positivity
  | succ n =>
    have hn : (n : ℝ) + 1 ≤ a := by exact_mod_cast hm
    have hs := logarithmic_first_derivative (0 : ℤ) (n : ℤ)
      (a := 1) (T := T) (r := (a : ℝ) + u) (N := a)
      (by norm_num) hT ha0 ha1 (by simpa using hsmall)
      (by simp; linarith) (by push_cast; nlinarith)
    have heq : (∑ k ∈ range (n + 1),
        ((a : ℝ) + k + u : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        ∑ k ∈ range (n + 1), eK (t / (2 * Real.pi) *
          (-Real.log ((a : ℝ) + k + u))) := by
      apply sum_congr rfl
      intro k hk
      have hx : 0 < (a : ℝ) + k + u := by positivity
      have he := eK_log_eq_cpow hx t
      push_cast at he ⊢
      rw [← he]
      congr 1
      ring
    rw [heq, norm_sum_eK_abs]
    have habs : |t / (2 * Real.pi)| = T := by
      dsimp [T]
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    rw [habs, range_eq_int_sum (fun x => eK (T * (-Real.log ((a : ℝ) + x + u)))) n]
    have hid : 4 * (a : ℝ) / (T * 1) = 8 * Real.pi * a / |t| := by
      dsimp [T]
      field_simp
      ring
    rw [← hid]
    simpa only [one_mul, add_assoc, add_left_comm, add_comm] using hs

example : ‖∑ k ∈ range 2,
    ((4 : ℝ) + k + (1 / 2 : ℝ) : ℂ) ^ (-(1 : ℂ) * Complex.I)‖ ≤
      8 * Real.pi * 4 / |(1 : ℝ)| :=
  shifted_phase_sum 4 2 (by norm_num) (by norm_num) (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Page 21 partial summation infrastructure. Split a real amplitude from a pure phase. -/
theorem cpow_amplitude_phase {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    (x : ℂ) ^ ((σ : ℂ) - (t : ℂ) * Complex.I) =
      (x ^ σ : ℝ) • (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rw [show (σ : ℂ) - (t : ℂ) * Complex.I =
    (σ : ℂ) + (-(t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hx.ne'), ← Complex.ofReal_cpow hx.le]
  simp [Algebra.smul_def]

/-- Page 21 partial summation infrastructure. A decreasing real power costs its first amplitude. -/
theorem weighted_shifted_phase_sum (a m : ℕ) (ha : 1 ≤ a) (u σ t B : ℝ)
    (hu : 0 ≤ u) (hσ : σ ≤ 0) (hB : 0 ≤ B)
    (hs : ∀ k ≤ m, ‖∑ i ∈ range k,
      ((a : ℝ) + i + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ B) :
    ‖∑ k ∈ range m, ((a : ℝ) + k + u : ℂ) ^ ((σ : ℂ) - (t : ℂ) * Complex.I)‖ ≤
      (a : ℝ) ^ σ * B := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  let w : ℕ → ℝ := fun k => ((a : ℝ) + k + u) ^ σ
  let z : ℕ → ℂ := fun k => ((a : ℝ) + k + u : ℂ) ^ (-(t : ℂ) * Complex.I)
  have hw : ∀ k, 0 ≤ w k := by intro k; exact Real.rpow_nonneg (by positivity) _
  have hanti : Antitone w := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hσ
    have hreal : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hb := Decomp90.abel_bound w z m hB hw hanti hs
  have hterms : (∑ k ∈ range m,
      ((a : ℝ) + k + u : ℂ) ^ ((σ : ℂ) - (t : ℂ) * Complex.I)) =
      ∑ k ∈ range m, w k • z k := by
    apply sum_congr rfl
    intro k hk
    have hx : 0 < (a : ℝ) + k + u := by positivity
    have he := cpow_amplitude_phase hx σ t
    push_cast at he
    exact he
  rw [hterms]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ hB
  apply Real.rpow_le_rpow_of_nonpos ha0 _ hσ
  simp only [Nat.cast_zero, add_zero]
  linarith

/-- Page 21 supply infrastructure. The absolute phase bound also covers zero frequency. -/
theorem shifted_phase_trivial (a m : ℕ) (ha : 1 ≤ a) (u t : ℝ) (hu : 0 ≤ u) :
    ‖∑ k ∈ range m, ((a : ℝ) + k + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ m := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  calc
    _ ≤ ∑ k ∈ range m, ‖((a : ℝ) + k + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ = m := by
      have hp : ∀ k : ℕ, ‖((a : ℝ) + k + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖ = 1 := by
        intro k
        have hx : 0 < (a : ℝ) + k + u := by positivity
        have he := Complex.norm_cpow_eq_rpow_re_of_pos hx (-(t : ℂ) * Complex.I)
        push_cast at he
        simpa using he
      rw [sum_congr rfl (fun k _ => hp k)]
      simp

#print axioms shifted_phase_trivial
#print axioms cpow_amplitude_phase
#print axioms weighted_shifted_phase_sum
#print axioms range_eq_int_sum
#print axioms shifted_phase_sum
end LeanLab.BakerHarmanPintz1997.Decomp343b
