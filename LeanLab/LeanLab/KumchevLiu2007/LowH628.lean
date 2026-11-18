/-
Exact short square energy below the square root scale.
This diagnoses the use of A2.3 in the unwritten large epsilon range.
It does not refute display 53 or assert a paper error.
Sources are P0088 page 2 display 5 and page 7 hypothesis A2.3.
The complete energy includes the initial interval after page 8 display 31.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628
namespace LeanLab.KumchevLiu2007.Task628
open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open LeanLab.BHP1997.Gallagher605
open LeanLab.Linnik.U1394Fejer (tri)
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- Page 7 A2.3, derived spacing fact. Distinct square window frequencies
are separated by at least square root Y. -/
theorem square_frequency_spacing {Y : ℝ} (_hY : 0 ≤ Y)
    {m n : ℕ} (hm : m ∈ squareWindow Y) (hn : n ∈ squareWindow Y) (hne : m ≠ n) :
    Real.sqrt Y ≤ |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
  have hmlo := (Finset.mem_filter.mp hm).2.1
  have hnlo := (Finset.mem_filter.mp hn).2.1
  have hgap : ∀ a b : ℝ, Real.sqrt Y / 2 ≤ a → Real.sqrt Y / 2 ≤ b →
      a + 1 ≤ b → Real.sqrt Y ≤ b ^ 2 - a ^ 2 := by
    intro a b ha hb hab
    have hs : 0 ≤ a + b := by linarith [Real.sqrt_nonneg Y]
    have hp := mul_nonneg (show 0 ≤ b - a - 1 by linarith) hs
    nlinarith
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · have hr : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hmn
    rw [abs_sub_comm]
    exact (hgap _ _ hmlo hnlo hr).trans (le_abs_self _)
  · have hr : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hnm
    exact (hgap _ _ hnlo hmlo hr).trans (le_abs_self _)

/-- Gallagher's exact overlap identity as used after page 8 display 31.
For H separated frequencies the complete short energy is H times the
coefficient energy, because every off diagonal overlap vanishes. -/
theorem separated_frequency_energy {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → ℝ) {H : ℝ} (hH : 0 < H)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → H ≤ |f i - f j|) :
    (∫ t : ℝ, ‖frequencyWindow s c f H t‖ ^ 2) = H * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  have hz : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → tri ((f i - f j) / H) = 0 := by
    intro i hi j hj hij
    unfold tri
    rw [abs_div, abs_of_pos hH, max_eq_left]
    exact sub_nonpos.mpr ((le_div_iff₀ hH).mpr (by simpa using hsep i hi j hj hij))
  have he := frequency_window_energy s c f hH
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * (starRingEnd ℂ) (c j) *
      (tri ((f i - f j) / H) : ℂ)) = ∑ i ∈ s, ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp [tri, Complex.mul_conj']
    · intro j hj hji
      rw [hz i hi j hj (Ne.symm hji)]
      simp
    · exact fun hn => (hn hi).elim
  rw [hsum] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.re_sum, Complex.im_sum, zero_mul, sub_zero] using hr

/-- Page 7 A2.3 and page 8 Gallagher, derived finite identity.
For positive H at most square root Y the complete rough short energy is
H times the squared rough indicator mass. There is no cancellation in alpha. -/
theorem rough_complete_energy_small_H (Y P H α : ℝ) (hY : 0 ≤ Y)
    (hH : 0 < H) (hsmall : H ≤ Real.sqrt Y) :
    ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
      ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) =
      H * ∑ m ∈ squareWindow Y,
        ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖ ^ 2 := by
  let c : ℕ → ℂ := fun m => roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m *
    fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))
  let f : ℕ → ℝ := fun m => (m : ℝ) ^ 2
  have hs := separated_frequency_energy (squareWindow Y) c f hH
    (fun i hi j hj hij => hsmall.trans (square_frequency_spacing hY hi hj hij))
  have hf : ∀ m ∈ squareWindow Y, Y / 4 ≤ f m ∧ f m ≤ Y := by
    intro m hm
    obtain ⟨_, hmlo, hmhi⟩ := Finset.mem_filter.mp hm
    have hm0 := Nat.cast_nonneg (α := ℝ) m
    have hlow := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt Y / 2) hm0).mpr hmlo
    have hhi := (sq_le_sq₀ hm0 (Real.sqrt_nonneg Y)).mpr hmhi.le
    dsimp [f]
    constructor <;> nlinarith [Real.sq_sqrt hY]
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun t => ‖roughShortSum Y P H α t‖ ^ 2) volume a b := fun a b =>
    Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow Y) c H a b
  have he := Task634.frequencyWindow_energy_interval (squareWindow Y) c f H
    (Y / 4) Y hH.le (by linarith) hf
  change (∫ t : ℝ, ‖frequencyWindow (squareWindow Y) c f H t‖ ^ 2) =
    (∫ t in (Y / 4 - H)..Y, ‖roughShortSum Y P H α t‖ ^ 2) at he
  calc
    _ = ∫ t in (Y / 4 - H)..Y, ‖roughShortSum Y P H α t‖ ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)
    _ = H * ∑ m ∈ squareWindow Y, ‖c m‖ ^ 2 := he.symm.trans hs
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      dsimp only [c]
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- Page 7 A2.3, derived quantitative restriction. Below square root Y an
energy bound C H squared over L to A forces rough mass at most C H over
L to A. CONDITIONAL ON the explicit upper bound. -/
theorem small_H_energy_forces_mass (Y P H α L A C : ℝ) (hY : 0 ≤ Y)
    (hH : 0 < H) (hsmall : H ≤ Real.sqrt Y)
    (henergy : ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
      ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) ≤ C * H ^ 2 / L ^ A) :
    (∑ m ∈ squareWindow Y,
      ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖ ^ 2) ≤ C * H / L ^ A := by
  rw [rough_complete_energy_small_H Y P H α hY hH hsmall] at henergy
  apply (mul_le_mul_iff_right₀ hH).mp
  nlinarith [show C * H ^ 2 / L ^ A = H * (C * H / L ^ A) by ring]

/-- Page 7 A2.3, finite obstruction criterion for the small H method.
If the rough mass exceeds C H over L to A, the complete short energy
strictly exceeds C H squared over L to A at every frequency. This is not
a counterexample to the separate display 53 exceptional count estimate. -/
theorem small_H_energy_bound_fails (Y P H α L A C : ℝ) (hY : 0 ≤ Y)
    (hH : 0 < H) (hsmall : H ≤ Real.sqrt Y)
    (hmass : C * H / L ^ A < ∑ m ∈ squareWindow Y,
      ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖ ^ 2) :
    C * H ^ 2 / L ^ A <
      ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
        ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) := by
  rw [rough_complete_energy_small_H Y P H α hY hH hsmall]
  have h := mul_lt_mul_of_pos_left hmass hH
  convert h using 1
  ring

/-- Page 16, a derived nonvacuity statement for the unwritten residue.
For epsilon above seventeen thirtieths and at most five sixths, every X
above one has a permitted low H interval below square root Y. Thus the
new residue includes the range where the complete energy has no frequency
cancellation. This is a parameter statement, not a paper error claim. -/
theorem low_H_below_root_nonempty (X ε : ℝ) (hX : 1 < X)
    (hε : 17 / 30 < ε) (hεhi : ε ≤ 5 / 6) :
    ∃ H : ℝ, X ^ (1 - ε) < H ∧ H < Real.sqrt (windowY X ε) ∧
      H ≤ windowY X ε ∧ H ≤ X ∧ H < X ^ (7 / 18 + ε) := by
  have hXpos : 0 < X := by linarith
  have hεpos : 0 < ε := by linarith
  have hr : Real.sqrt (windowY X ε) = X ^ (7 / 24 + ε / 4) := by
    rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hXpos.le]
    congr 1
    ring
  have hlo : X ^ (1 - ε) < Real.sqrt (windowY X ε) := by
    rw [hr]
    exact Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  have hrY : Real.sqrt (windowY X ε) ≤ windowY X ε := by
    rw [hr, windowY]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hYX : windowY X ε ≤ X := by
    unfold windowY
    calc X ^ (7 / 12 + ε / 2) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
      _ = X := Real.rpow_one X
  have hrT : Real.sqrt (windowY X ε) < X ^ (7 / 18 + ε) := by
    rw [hr]
    exact Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  refine ⟨(X ^ (1 - ε) + Real.sqrt (windowY X ε)) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith

/-- Page 7 A2.3, derived disjoint window bound. Below square root Y every
short square window contains at most one frequency. Its rough sum has
norm at most one, for every alpha and every t. -/
theorem rough_short_norm_le_one (Y P H α t : ℝ) (hY : 0 ≤ Y)
    (_hH : 0 < H) (hsmall : H ≤ Real.sqrt Y) :
    ‖roughShortSum Y P H α t‖ ≤ 1 := by
  let S := (squareWindow Y).filter
    (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)
  have hc : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro m hm n hn
    obtain ⟨hmw, hmlo, hmhi⟩ := Finset.mem_filter.mp hm
    obtain ⟨hnw, hnlo, hnhi⟩ := Finset.mem_filter.mp hn
    by_contra hne
    have hsep := hsmall.trans (square_frequency_spacing hY hmw hnw hne)
    have hdiff : |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| < H := by
      apply abs_lt.mpr
      constructor <;> linarith
    linarith
  unfold roughShortSum
  change ‖∑ m ∈ S, _‖ ≤ _
  calc
    _ ≤ ∑ _m ∈ S, (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro m _
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
      exact roughWeight_norm_le_one _ _
    _ = (S.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hc

/-- Page 7 A2.3, derived lower bound on the printed bulk interval.
Below square root Y the bulk energy is at least H times rough mass minus
one. The initial interval costs at most H. This is valid for every alpha
and needs no prime counting input. -/
theorem rough_bulk_energy_small_H_lower (Y P H α : ℝ) (hY : 0 ≤ Y)
    (hH : 0 < H) (hsmall : H ≤ Real.sqrt Y) :
    H * ((∑ m ∈ squareWindow Y,
      ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖ ^ 2) - 1) ≤
      ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2 := by
  have hi : IntervalIntegrable (fun t => ‖roughShortSum Y P H α t‖ ^ 2)
      volume (Y / 4 - H) (Y / 4) :=
    Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow Y)
      (fun m => roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
  have hinit : (∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) ≤ H := by
    calc
      _ ≤ ∫ _t in (Y / 4 - H)..(Y / 4), (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by linarith) hi intervalIntegrable_const
        intro t _
        have hn := rough_short_norm_le_one Y P H α t hY hH hsmall
        nlinarith [norm_nonneg (roughShortSum Y P H α t)]
      _ = H := by simp
  have he := rough_complete_energy_small_H Y P H α hY hH hsmall
  linarith

/-- Page 7 A2.3, a necessary rough mass condition in the low H regime.
CONDITIONAL ON the explicit bulk bound. Below square root Y such a bound
forces rough mass at most one plus C H over L to A. No asymptotic prime
count estimate or counterexample to display 53 is asserted here. -/
theorem small_H_bulk_bound_forces_mass (Y P H α L A C : ℝ) (hY : 0 ≤ Y)
    (hH : 0 < H) (hsmall : H ≤ Real.sqrt Y)
    (hbulk : (∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) ≤
      C * H ^ 2 / L ^ A) :
    (∑ m ∈ squareWindow Y,
      ‖roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m‖ ^ 2) ≤ 1 + C * H / L ^ A := by
  have hlo := rough_bulk_energy_small_H_lower Y P H α hY hH hsmall
  apply (mul_le_mul_iff_right₀ hH).mp
  nlinarith [show C * H ^ 2 / L ^ A = H * (C * H / L ^ A) by ring]

example : ∃ H : ℝ, (64 : ℝ) ^ (1 - (2 / 3 : ℝ)) < H ∧
    H < Real.sqrt (windowY 64 (2 / 3)) ∧ H ≤ windowY 64 (2 / 3) ∧
    H ≤ 64 ∧ H < 64 ^ (7 / 18 + (2 / 3 : ℝ)) :=
  low_H_below_root_nonempty 64 (2 / 3) (by norm_num) (by norm_num) (by norm_num)


example : Real.sqrt 16 ≤ |(2 : ℝ) ^ 2 - (3 : ℝ) ^ 2| := by
  apply square_frequency_spacing (m := 2) (n := 3) (by norm_num)
  · norm_num [squareWindow]
  · norm_num [squareWindow]
  · decide

example : (∫ t : ℝ, ‖frequencyWindow ({0, 3} : Finset ℕ)
    (fun _ => (1 : ℂ)) (fun n => (n : ℝ)) 1 t‖ ^ 2) = 2 := by
  have h := separated_frequency_energy ({0, 3} : Finset ℕ)
    (fun _ => (1 : ℂ)) (fun n => (n : ℝ)) (by norm_num : (0 : ℝ) < 1) (by
      intro i hi j hj hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num at *)
  simpa using h

example (α : ℝ) :
    (((∫ t in (16 / 4 - 1 : ℝ)..(16 / 4), ‖roughShortSum 16 1 1 α t‖ ^ 2) +
      ∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 1 α t‖ ^ 2) = 2) ∧
    (1 < ((∫ t in (16 / 4 - 1 : ℝ)..(16 / 4), ‖roughShortSum 16 1 1 α t‖ ^ 2) +
      ∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 1 α t‖ ^ 2)) ∧
    ((∑ m ∈ squareWindow 16,
      ‖roughWeight ((16 : ℝ) ^ (1 / 4 : ℝ) * (1 : ℝ) ^ (-2 : ℤ)) m‖ ^ 2) ≤ 2) ∧
    ‖roughShortSum 16 1 1 α (7 / 2)‖ ≤ 1 ∧
    1 ≤ (∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 1 α t‖ ^ 2) ∧
    (∑ m ∈ squareWindow 16,
      ‖roughWeight ((16 : ℝ) ^ (1 / 4 : ℝ) * (1 : ℝ) ^ (-2 : ℤ)) m‖ ^ 2) ≤ 3 := by
  have hcut : (16 : ℝ) ^ (1 / 4 : ℝ) * (1 : ℝ) ^ (-2 : ℤ) = 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hw (m : ℕ) : roughWeight ((16 : ℝ) ^ (1 / 4 : ℝ) * (1 : ℝ) ^ (-2 : ℤ)) m = 1 := by
    rw [hcut]
    unfold roughWeight
    apply ite_eq_left
    intro p hp _
    exact_mod_cast hp.two_le
  have hm : (∑ m ∈ squareWindow 16,
      ‖roughWeight ((16 : ℝ) ^ (1 / 4 : ℝ) * (1 : ℝ) ^ (-2 : ℤ)) m‖ ^ 2) = 2 := by
    simp_rw [hw]
    norm_num [squareWindow, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]
  have he : ((∫ t in (16 / 4 - 1 : ℝ)..(16 / 4), ‖roughShortSum 16 1 1 α t‖ ^ 2) +
      ∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 1 α t‖ ^ 2) = 2 := by
    have h := rough_complete_energy_small_H 16 1 1 α (by norm_num) (by norm_num) (by norm_num)
    simpa only [hm, one_mul] using h
  refine ⟨he, ?_, ?_, ?_, ?_, ?_⟩
  · have h := small_H_energy_bound_fails 16 1 1 α 1 1 1 (by norm_num)
      (by norm_num) (by norm_num) (by rw [hm]; norm_num)
    simpa using h
  · have h := small_H_energy_forces_mass 16 1 1 α 1 1 2 (by norm_num)
      (by norm_num) (by norm_num) (by rw [he]; norm_num)
    simpa using h


  · exact rough_short_norm_le_one 16 1 1 α (7 / 2) (by norm_num) (by norm_num) (by norm_num)
  · have h := rough_bulk_energy_small_H_lower 16 1 1 α (by norm_num) (by norm_num) (by norm_num)
    simpa only [hm, one_mul, show (2 : ℝ) - 1 = 1 by norm_num] using h
  · have hi0 : 0 ≤ (∫ t in (16 / 4 - 1 : ℝ)..(16 / 4), ‖roughShortSum 16 1 1 α t‖ ^ 2) :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t => sq_nonneg _)
    have hb : (∫ t in (16 / 4 : ℝ)..16, ‖roughShortSum 16 1 1 α t‖ ^ 2) ≤
        (2 : ℝ) * 1 ^ 2 / (1 : ℝ) ^ (1 : ℝ) := by
      norm_num
      linarith
    have h := small_H_bulk_bound_forces_mass 16 1 1 α 1 1 2 (by norm_num)
      (by norm_num) (by norm_num) hb
    simpa only [Real.rpow_one, one_pow, one_zpow, mul_one, one_mul, div_one,
      show (1 : ℝ) + 2 = 3 by norm_num] using h


end LeanLab.KumchevLiu2007.Task628
#print axioms LeanLab.KumchevLiu2007.Task628.square_frequency_spacing
#print axioms LeanLab.KumchevLiu2007.Task628.separated_frequency_energy
#print axioms LeanLab.KumchevLiu2007.Task628.rough_complete_energy_small_H
#print axioms LeanLab.KumchevLiu2007.Task628.small_H_energy_forces_mass

#print axioms LeanLab.KumchevLiu2007.Task628.small_H_energy_bound_fails
#print axioms LeanLab.KumchevLiu2007.Task628.low_H_below_root_nonempty

#print axioms LeanLab.KumchevLiu2007.Task628.rough_short_norm_le_one
#print axioms LeanLab.KumchevLiu2007.Task628.rough_bulk_energy_small_H_lower
#print axioms LeanLab.KumchevLiu2007.Task628.small_H_bulk_bound_forces_mass
