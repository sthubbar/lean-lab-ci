/-
PP1993 page 44 display 3, the remaining finite Fourier kernel comparison.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The Parseval and prime weight steps are separate clean support.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.FiniteParseval489
import LeanLab.Languasco2004.CoefficientGlue489

namespace LeanLab.Languasco2004.Decomp489g
open Finset Real MeasureTheory Decomp279b Decomp413a
noncomputable section

/-- Page 44 display 3: the number of even frequencies in the open left
window is at most H once H is at least two. -/
theorem even_window_card {N H : ℝ} (hN : 0 ≤ N) (hH : 2 ≤ H) :
    (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) ≤ H := by
  classical
  let s := (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even
  let t := Ioc ⌊N / 2⌋₊ ⌊(N + H) / 2⌋₊
  have hmaps : Set.MapsTo (fun n : ℕ => n / 2) s t := by
    intro n hn
    obtain ⟨hnI, heven⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hnI
    obtain ⟨k, hk⟩ := heven
    have hn2 : 2 ≤ n := by omega
    have hnpos : 0 < n := by omega
    have hreal : N < (n : ℝ) := (Nat.floor_lt' hnpos.ne').mp hlo
    have hupper : (n : ℝ) ≤ N + H :=
      (show (n : ℝ) ≤ (⌊N + H⌋₊ : ℝ) by exact_mod_cast hhi).trans (Nat.floor_le (by linarith))
    have heq : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n = 2 * (n / 2) by omega)
    apply Finset.mem_Ioc.mpr
    constructor
    · exact (Nat.floor_lt' (by omega : n / 2 ≠ 0)).mpr (by linarith)
    · exact (Nat.le_floor_iff (by linarith : 0 ≤ (N + H) / 2)).mpr (by linarith)
  have hinj : (s : Set ℕ).InjOn (fun n : ℕ => n / 2) := by
    intro n hn m hm heq
    change n / 2 = m / 2 at heq
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    omega
  have hc := Finset.card_le_card_of_injOn (fun n : ℕ => n / 2) hmaps hinj
  have hmono : ⌊N / 2⌋₊ ≤ ⌊(N + H) / 2⌋₊ := Nat.floor_mono (by linarith)
  have ht : (t.card : ℝ) ≤ H := by
    dsimp [t]
    rw [Nat.card_Ioc, Nat.cast_sub hmono]
    have hu := Nat.floor_le (show 0 ≤ (N + H) / 2 by linarith)
    have hl := Nat.lt_floor_add_one (N / 2)
    linarith
  exact (show (s.card : ℝ) ≤ (t.card : ℝ) by exact_mod_cast hc).trans ht

/-- Page 43: each phase has norm one. -/
theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Page 44 display 3: the finite even frequency sum satisfies the H cap,
including every integer pole. The reciprocal distance bound is separate. -/
theorem even_phase_cap {N H : ℝ} (hN : 0 ≤ N) (hH : 2 ≤ H) (x : ℝ) :
    ‖∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, phase ((m : ℝ) * x)‖ ≤ H := by
  calc ‖∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, phase ((m : ℝ) * x)‖ ≤
      ∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, ‖phase ((m : ℝ) * x)‖ := norm_sum_le _ _
    _ = (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) := by simp only [phase_norm, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ H := even_window_card hN hH

#print axioms even_window_card
#print axioms phase_norm
#print axioms even_phase_cap

/-- Page 44 display 3: a finite unit circle geometric sum is bounded
by two divided by the chord to one. -/
theorem unit_geometric_sum_bound {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [hz]

/-- Page 44 display 3: Jordan's inequality controls the phase chord
on a nearest integer cell. -/
theorem phase_gap_lower {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖phase t - 1‖ := by
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * t) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hcancel : (2 / Real.pi) * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [abs_mul, abs_of_pos Real.pi_pos, hcancel] at hs
  have heq : phase t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Page 44 display 3: the reciprocal distance bound for a finite
geometric progression on a punctured nearest integer cell. -/
theorem local_geometric_inverse_bound {t : ℝ} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, phase t ^ k‖ ≤ |t|⁻¹ := by
  have ha : 0 < |t| := abs_pos.mpr ht0
  have hgap := phase_gap_lower ht
  have hden : 0 < ‖phase t - 1‖ := by linarith
  have hne : phase t ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hden
    exact (lt_irrefl 0) hden
  have hgeom := unit_geometric_sum_bound (phase_norm t) hne n
  have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (show 0 < 4 * |t| by positivity) hgap
  have hlast : (2 : ℝ) / (4 * |t|) ≤ |t|⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * |t|) ha).mpr
    linarith
  exact hgeom.trans (hfrac.trans hlast)

#print axioms unit_geometric_sum_bound
#print axioms phase_gap_lower
#print axioms local_geometric_inverse_bound

/-- LEAF. Page 44 display 3, before Parseval and prime weight estimates.
The remaining finite even frequency kernel comparison and its integral
Cauchy Schwarz connection are expressed using only the minor S1 and S2
squared integrals. This has no density or prime weight input. -/
theorem finite_kernel_energy :
    ∀ N Y H B K : ℝ, 16 ≤ H → 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N Y H B ξ ≤ K) →
      (∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
        ‖minorCoefficient N Y H B m‖ ^ 2) ^ 2 ≤
        (∫ x in minorDomain N Y H B, ‖firstSum N Y x‖ ^ 2) ^ 2 *
          (∫ x in minorDomain N Y H B, ‖secondSum Y x‖ ^ 2) * K := by sorry

#print axioms finite_kernel_energy
end
end LeanLab.Languasco2004.Decomp489g
