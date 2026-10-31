/-
P0070 Section 6, pages 368 to 372.
The inputs below state 39, 40 and the explicit formula 28.
They are cited Props. This file does not prove Estimate7Wide.
The last small conductor step also uses the zero free region 41.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Statements

namespace LeanLab.PerelliPintz1992.Section6
open Real Filter Topology ArithmeticFunction

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Nontrivial zeros with real part at least σ and height at most T. -/
def zeroRegion (σ T : ℝ) : Set ℂ :=
  {ρ | σ ≤ ρ.re ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Multiplicity count in the printed N of σ, T, χ. Infinite counts remain infinite. -/
def zeroCount {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) : ENNReal :=
  ∑' ρ : ℂ, if ρ ∈ zeroRegion σ T then (analyticOrderAt χ.LFunction ρ).toENNReal else 0

/-- The first sum on each line of 39 and 40. -/
def allCharacterCount (q : ℕ+) (σ T : ℝ) : ENNReal :=
  ∑' χ : DirichletCharacter ℂ (q : ℕ), zeroCount χ σ T

/-- The starred sum over primitive characters with conductor at most Q. -/
def primitiveCount (Q σ T : ℝ) : ENNReal :=
  ∑' q : ℕ+, if (q : ℝ) ≤ Q then
    ∑' χ : DirichletCharacter ℂ (q : ℕ), if χ.IsPrimitive then zeroCount χ σ T else 0
    else 0

/-- Equation 39, both estimates, page 368. The constants are uniform in σ, q, Q and T. -/
def Ingham39 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ T : ℝ,
    1 / 2 ≤ σ → σ ≤ 4 / 5 → 2 ≤ T →
    (∀ q : ℕ+, allCharacterCount q σ T ≤ ENNReal.ofReal
      (C * ((q : ℝ) * T) ^ (3 * (1 - σ) / (2 - σ)) * log ((q : ℝ) * T) ^ c)) ∧
    (∀ Q : ℝ, 1 ≤ Q → primitiveCount Q σ T ≤ ENNReal.ofReal
      (C * (Q ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) * log (Q * T) ^ c))

/-- Equation 40, both estimates, page 368. The endpoint σ = 1 is excluded. -/
def Huxley40 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ T : ℝ,
    4 / 5 ≤ σ → σ < 1 → 2 ≤ T →
    (∀ q : ℕ+, allCharacterCount q σ T ≤ ENNReal.ofReal
      (C * ((q : ℝ) * T) ^ ((5 / 2) * (1 - σ)) * log ((q : ℝ) * T) ^ c)) ∧
    (∀ Q : ℝ, 1 ≤ Q → primitiveCount Q σ T ≤ ENNReal.ofReal
      (C * (Q ^ 2 * T) ^ ((5 / 2) * (1 - σ)) * log (Q * T) ^ c))

/-- The zero sum in the explicit formula on page 365. Multiplicities are retained. -/
def explicitZeroSum {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (x T : ℝ) : ℂ :=
  ∑' ρ : ℂ, if ρ ∈ zeroRegion 0 T then
    (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ ρ / ρ else 0

/-- The error E in the explicit formula, with the sign printed on page 365. -/
def explicitError {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (x T : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ n) -
    (if χ = 1 then (x : ℂ) else 0) + explicitZeroSum χ x T

/-- Equation 28 and the preceding explicit formula, page 365. -/
def ExplicitFormula28 : Prop :=
  ∃ C N0 : ℝ, 0 < C ∧ ∀ N : ℕ, N0 ≤ N → ∀ q : ℕ+,
    (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / 2 →
    ∀ χ : DirichletCharacter ℂ (q : ℕ), ∀ x T : ℝ,
    (N : ℝ) / 2 ≤ x → x ≤ 3 * N → 2 ≤ T → T ≤ (N : ℝ) / 2 →
    ‖explicitError χ x T‖ ≤ C * ((N : ℝ) * L N ^ 2 / T + (N : ℝ) ^ (1 / 4 : ℝ) * L N)

/-- Split a finite zero sum at β = 4/5, the boundary between 39 and 40. -/
theorem split_zero_sum (Z : Finset ℂ) (w : ℂ → ℂ) :
    ∑ ρ ∈ Z, w ρ =
      (∑ ρ ∈ Z.filter (fun ρ => ρ.re ≤ 4 / 5), w ρ) +
      ∑ ρ ∈ Z.filter (fun ρ => 4 / 5 < ρ.re), w ρ := by
  classical
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not Z (fun ρ : ℂ => ρ.re ≤ 4 / 5) w).symm

#print axioms split_zero_sum


/-- The rational main exponent in 49, before its O of ε cubed remainder. -/
def gE (ε δ : ℝ) : ℝ :=
  3 * δ / (1 + δ) - 2 * δ + (1 + 2 * ε) * (2 * δ - 1) / (2 * (2 - δ))

/-- Equation 50: nonnegative ε only decreases the main exponent for δ ≤ 1/2. -/
theorem gE_le_g0 {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : δ ≤ 1 / 2) : gE ε δ ≤ g0 δ := by
  have hn : 2 * δ - 1 ≤ 0 := by linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hε hn
  have hf : (1 + 2 * ε) * (2 * δ - 1) ≤ 2 * δ - 1 := by nlinarith
  have hd : 0 ≤ 2 * (2 - δ) := by linarith
  have hh := div_le_div_of_nonneg_right hf hd
  unfold gE g0
  linarith

#print axioms gE_le_g0


/-- A uniform version of 50 on the Case 1 interval. -/
theorem g0_le_quadratic {δ : ℝ} (hδ : 1 / 5 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    g0 δ ≤ -(1 - 2 * δ) ^ 2 / 12 := by
  have hid := identity50 (δ := δ) (by linarith) (by linarith)
  have hg : g0 δ ≤ 0 := by
    rcases lt_or_eq_of_le hδ' with h | h
    · exact (g0_neg (by linarith) h).le
    · rw [h, g0_half]
  have hd : 2 * (2 - δ) * (1 + δ) ≤ 6 := by nlinarith [sq_nonneg δ]
  have hm := mul_le_mul_of_nonpos_right hd hg
  have hs : 0 ≤ (1 - 2 * δ) ^ 2 := sq_nonneg _
  have hp := mul_nonneg hs (show 0 ≤ 1 / 2 - δ by linarith)
  nlinarith

#print axioms g0_le_quadratic


/-- Absorb an explicit cubic remainder away from the endpoint in 49. -/
theorem gE_with_cubic_remainder {ε δ r : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 12)
    (hδ : 1 / 5 ≤ δ) (hδ' : δ ≤ 1 / 2 - ε) (hr : r ≤ ε ^ 3) :
    gE ε δ + r ≤ -(ε ^ 2) / 4 := by
  have hg := (gE_le_g0 hε.le (show δ ≤ 1 / 2 by linarith)).trans
    (g0_le_quadratic hδ (show δ ≤ 1 / 2 by linarith))
  have hs := mul_nonneg (show 0 ≤ 1 - 2 * δ - 2 * ε by linarith)
    (show 0 ≤ 1 - 2 * δ + 2 * ε by linarith)
  have he := mul_nonneg (sq_nonneg ε) (show 0 ≤ 1 / 12 - ε by linarith)
  nlinarith

#print axioms gE_with_cubic_remainder


/-- The three cases on page 369 give a common diagonal point for the f1 factors. -/
theorem diagonal_f1 {δ δ' : ℝ} (hδ : 1 / 5 ≤ δ) (hord : δ ≤ δ') (hδ' : δ' ≤ 1 / 2) :
    ∃ d : ℝ, δ ≤ d ∧ d ≤ δ' ∧ f1 δ ≤ f1 d ∧ f1 δ' ≤ f1 d := by
  let m := Real.sqrt (3 / 2) - 1
  by_cases hleft : δ' ≤ m
  · refine ⟨δ', hord, le_rfl, ?_, le_rfl⟩
    exact f1_monotoneOn ⟨hδ, hord.trans hleft⟩ ⟨hδ.trans hord, hleft⟩ hord
  · by_cases hright : m ≤ δ
    · refine ⟨δ, le_rfl, hord, le_rfl, ?_⟩
      exact f1_antitoneOn ⟨hright, hord.trans hδ'⟩ ⟨hright.trans hord, hδ'⟩ hord
    · refine ⟨m, (not_le.mp hright).le, (not_le.mp hleft).le, ?_, ?_⟩
      · change f1 δ ≤ f1 (Real.sqrt (3 / 2) - 1)
        rw [f1_at_max]
        exact f1_le_max (by linarith)
      · change f1 δ' ≤ f1 (Real.sqrt (3 / 2) - 1)
        rw [f1_at_max]
        exact f1_le_max (by linarith)

#print axioms diagonal_f1


/-- Split the actual L zero count at β = 4/5, without a finiteness assumption. -/
theorem zeroCount_split {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) :
    zeroCount χ σ T =
      (∑' ρ : ℂ, if ρ ∈ zeroRegion σ T ∧ ρ.re ≤ 4 / 5 then
        (analyticOrderAt χ.LFunction ρ).toENNReal else 0) +
      ∑' ρ : ℂ, if ρ ∈ zeroRegion σ T ∧ 4 / 5 < ρ.re then
        (analyticOrderAt χ.LFunction ρ).toENNReal else 0 := by
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro ρ
  by_cases hρ : ρ ∈ zeroRegion σ T
  · by_cases hβ : ρ.re ≤ 4 / 5
    · simp [hρ, hβ, not_lt.mpr hβ]
    · simp [hρ, hβ, not_le.mp hβ]
  · simp [hρ]

#print axioms zeroCount_split


/-- The middle range of Case 2 in 55 has a fixed power saving. -/
theorem case2_middle {R N δ : ℝ} (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hδ : 1 / 10 ≤ δ) (hδ' : δ ≤ 1 / 5) :
    R ^ (5 * δ / 2 - 1 / 2) * N ^ (-δ / 8) ≤ N ^ (-(1 / 80 : ℝ)) := by
  have hR' : R ^ (5 * δ / 2 - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hN' : N ^ (-δ / 8) ≤ N ^ (-(1 / 80 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  calc
    R ^ (5 * δ / 2 - 1 / 2) * N ^ (-δ / 8) ≤ 1 * N ^ (-δ / 8) := by
      exact mul_le_mul_of_nonneg_right hR' (Real.rpow_nonneg (by linarith) _)
    _ ≤ N ^ (-(1 / 80 : ℝ)) := by simpa using hN'

#print axioms case2_middle


/-- Small δ in 55 is controlled by the conductor factor when R is large. -/
theorem case2_large_conductor {R N δ : ℝ} (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10) :
    R ^ (5 * δ / 2 - 1 / 2) * N ^ (-δ / 8) ≤ R ^ (-(1 / 4 : ℝ)) := by
  have hR' : R ^ (5 * δ / 2 - 1 / 2) ≤ R ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hN' : N ^ (-δ / 8) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  calc R ^ (5 * δ / 2 - 1 / 2) * N ^ (-δ / 8)
      ≤ R ^ (-(1 / 4 : ℝ)) * 1 :=
        mul_le_mul hR' hN' (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
    _ = R ^ (-(1 / 4 : ℝ)) := mul_one _

#print axioms case2_large_conductor


/-- The small M range of Case 1 on page 371. -/
theorem case1_small_modulus {M N δ ν : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hδ : 1 / 5 ≤ δ) (hν : ν ≤ 1 / 2) :
    M ^ (ν - 1 / 2) * N ^ (9 * δ / (4 * (1 + δ)) - 2 * δ) ≤
      N ^ (-(1 / 40 : ℝ)) := by
  have hM' : M ^ (ν - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hN' : N ^ (9 * δ / (4 * (1 + δ)) - 2 * δ) ≤ N ^ (-(1 / 40 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [exponent_le_neg_one_fortieth hδ])
  calc
    M ^ (ν - 1 / 2) * N ^ (9 * δ / (4 * (1 + δ)) - 2 * δ)
        ≤ 1 * N ^ (9 * δ / (4 * (1 + δ)) - 2 * δ) :=
      mul_le_mul_of_nonneg_right hM' (Real.rpow_nonneg (by linarith) _)
    _ ≤ N ^ (-(1 / 40 : ℝ)) := by simpa using hN'

#print axioms case1_small_modulus


/-- The scalar envelope in 55 has no decay at δ = 1/log N and R = 1. -/
theorem case2_small_conductor_obstruction {N : ℝ} (hN : 1 < N) :
    (1 : ℝ) ^ (5 * (1 / log N) / 2 - 1 / 2) * N ^ (-(1 / log N) / 8) =
      exp (-(1 / 8 : ℝ)) := by
  rw [Real.one_rpow, one_mul, Real.rpow_def_of_pos (by linarith)]
  congr 1
  have hl : log N ≠ 0 := (Real.log_pos hN).ne'
  field_simp

#print axioms case2_small_conductor_obstruction


/-- Fixed power savings absorb every fixed logarithmic loss in Section 6. -/
theorem eventually_power_saving (c A η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, L N ^ c * (N : ℝ) ^ (-η) ≤ L N ^ (-A) := by
  have h := (isLittleO_log_rpow_rpow_atTop (c + A) hη).def (by norm_num : (0 : ℝ) < 1)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 2] with N hN hN2
  have hL := L_pos hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  simp only [Real.norm_eq_abs, one_mul] at hN
  change |L N ^ (c + A)| ≤ |(N : ℝ) ^ η| at hN
  rw [abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hNp.le _)] at hN
  change L N ^ (c + A) ≤ (N : ℝ) ^ η at hN
  rw [Real.rpow_add hL] at hN
  have hb := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hNp.le (-η))
  have hc : (N : ℝ) ^ η * (N : ℝ) ^ (-η) = 1 := by
    rw [← Real.rpow_add hNp]
    simp
  rw [hc] at hb
  rw [Real.rpow_neg hL.le]
  rw [← one_div (L N ^ A)]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

#print axioms eventually_power_saving


/-- CONDITIONAL ON 39 and 40: each count in their union of ranges is finite. -/
theorem zeroCount_ne_top_of_density (h39 : Ingham39) (h40 : Huxley40)
    {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) {σ T : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ' : σ < 1) (hT : 2 ≤ T) : zeroCount χ σ T ≠ ⊤ := by
  have hf : allCharacterCount q σ T < ⊤ := by
    by_cases hcut : σ ≤ 4 / 5
    · obtain ⟨C, c, _, _, h⟩ := h39
      exact lt_of_le_of_lt ((h σ T hσ hcut hT).1 q) ENNReal.ofReal_lt_top
    · obtain ⟨C, c, _, _, h⟩ := h40
      exact lt_of_le_of_lt ((h σ T (not_le.mp hcut).le hσ' hT).1 q)
        ENNReal.ofReal_lt_top
  exact ne_of_lt ((ENNReal.le_tsum (f := fun ψ => zeroCount ψ σ T) χ).trans_lt hf)

#print axioms zeroCount_ne_top_of_density


/-- A conservative quantitative cutoff from the balance condition in 46. -/
theorem balance_forces_cutoff {ε δ ν : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 12)
    (hδ : 1 / 5 ≤ δ) (hν : ν ≤ ε ^ 3)
    (hbalance : (1 + 2 * ε) * (1 + δ) ≤ 2 - δ + ν * (1 + δ)) :
    δ ≤ 1 / 2 - ε := by
  have he2 : ε ^ 2 ≤ 1 / 144 := by nlinarith
  have he3 := mul_nonneg hε.le (show 0 ≤ 1 / 3 - ε ^ 2 by linarith)
  have hv : ν ≤ ε / 3 := by nlinarith
  have hp := mul_nonneg (show 0 ≤ 2 * ε - ν by linarith)
    (show 0 ≤ δ - 1 / 5 by linarith)
  nlinarith

#print axioms balance_forces_cutoff


/-- The last scalar step on page 372, with its zero gap stated as a numerical hypothesis. -/
theorem case2_with_zero_gap {R N δ κ : ℝ} (hR : 1 ≤ R) (hN : 1 < N)
    (hδ : δ ≤ 1 / 5) (hgap : κ / log N ^ (4 / 5 : ℝ) ≤ δ) :
    R ^ (5 * δ / 2 - 1 / 2) * N ^ (-δ / 8) ≤
      exp (-(κ * log N ^ (1 / 5 : ℝ)) / 8) := by
  have hL : 0 < log N := Real.log_pos hN
  have hR' : R ^ (5 * δ / 2 - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hquot : log N / log N ^ (4 / 5 : ℝ) = log N ^ (1 / 5 : ℝ) := by
    rw [show (1 / 5 : ℝ) = 1 - 4 / 5 by norm_num, Real.rpow_sub hL, Real.rpow_one]
  have hm := mul_le_mul_of_nonneg_right hgap (show 0 ≤ log N / 8 by positivity)
  have hrewrite : κ / log N ^ (4 / 5 : ℝ) * (log N / 8) =
      κ * (log N / log N ^ (4 / 5 : ℝ)) / 8 := by ring
  rw [hrewrite, hquot] at hm
  calc
    R ^ (5 * δ / 2 - 1 / 2) * N ^ (-δ / 8) ≤ N ^ (-δ / 8) := by
      simpa using mul_le_mul_of_nonneg_right hR' (Real.rpow_nonneg (by linarith) (-δ / 8))
    _ = exp (log N * (-δ / 8)) := Real.rpow_def_of_pos (by linarith) _
    _ ≤ exp (-(κ * log N ^ (1 / 5 : ℝ)) / 8) := by
      apply Real.exp_le_exp.mpr
      nlinarith

#print axioms case2_with_zero_gap


/-- The stretched exponential on page 372 absorbs every fixed logarithmic loss. -/
theorem eventually_stretched_exp (c A κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop,
      L N ^ c * exp (-(κ * L N ^ (1 / 5 : ℝ)) / 8) ≤ L N ^ (-A) := by
  have h := (isLittleO_rpow_exp_pos_mul_atTop (5 * (c + A))
    (show 0 < κ / 8 by linarith)).def (by norm_num : (0 : ℝ) < 1)
  have hLlim : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hLlim
  have h' := htlim.eventually h
  filter_upwards [h', eventually_ge_atTop 2] with N hN hN2
  have hL := L_pos hN2
  have hp : (L N ^ (1 / 5 : ℝ)) ^ (5 * (c + A)) = L N ^ (c + A) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    ring
  change ‖(L N ^ (1 / 5 : ℝ)) ^ (5 * (c + A))‖ ≤
    1 * ‖exp (κ / 8 * L N ^ (1 / 5 : ℝ))‖ at hN
  rw [hp] at hN
  simp only [Real.norm_eq_abs, one_mul] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg hL.le _), abs_of_pos (Real.exp_pos _)] at hN
  have hb := mul_le_mul_of_nonneg_right hN
    (Real.exp_pos (-(κ * L N ^ (1 / 5 : ℝ)) / 8)).le
  have he : exp (κ / 8 * L N ^ (1 / 5 : ℝ)) *
      exp (-(κ * L N ^ (1 / 5 : ℝ)) / 8) = 1 := by
    rw [← Real.exp_add, show κ / 8 * L N ^ (1 / 5 : ℝ) +
      -(κ * L N ^ (1 / 5 : ℝ)) / 8 = 0 by ring, Real.exp_zero]
  rw [he, Real.rpow_add hL] at hb
  rw [Real.rpow_neg hL.le, ← one_div (L N ^ A)]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

#print axioms eventually_stretched_exp


/-- The elementary comparison of the two zero gaps on page 372. -/
theorem eventually_min_gap (D c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    ∀ᶠ N : ℕ in atTop,
      min c1 c2 / L N ^ (4 / 5 : ℝ) ≤
        min (c1 / L N ^ (1 / 2 : ℝ))
          (c2 / max (D * log (L N)) (L N ^ (4 / 5 : ℝ))) := by
  have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).const_mul_left D).def
    (by norm_num : (0 : ℝ) < 1)
  have hLlim : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h' := hLlim.eventually h
  filter_upwards [h', hLlim.eventually_ge_atTop 1] with N hN hL1
  have hLp : 0 < L N := by linarith
  have hD : D * log (L N) ≤ L N ^ (4 / 5 : ℝ) := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg hLp.le (4 / 5 : ℝ))] using hN
  have hpow : L N ^ (1 / 2 : ℝ) ≤ L N ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hκ : 0 < min c1 c2 := lt_min hc1 hc2
  rw [max_eq_right hD]
  apply le_min
  · calc
      min c1 c2 / L N ^ (4 / 5 : ℝ) ≤ min c1 c2 / L N ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left hκ.le (Real.rpow_pos_of_pos hLp _) hpow
      _ ≤ c1 / L N ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hLp.le _)
  · exact div_le_div_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hLp.le _)

#print axioms eventually_min_gap


/-- The choice ε double prime = 1/(2D) on page 372. -/
theorem small_conductor_parameters {R ℓ D : ℝ} (hℓ : 1 ≤ ℓ) (hD : 0 < D)
    (hR : 1 ≤ R) (hbound : R ≤ ℓ ^ D) :
    ℓ ^ (-(1 / 2 : ℝ)) ≤ R ^ (-(1 / (2 * D))) ∧ log R ≤ D * log ℓ := by
  have hℓp : 0 < ℓ := by linarith
  have hRp : 0 < R := by linarith
  have hd : -(1 / (2 * D)) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hp := Real.rpow_le_rpow_of_nonpos hRp hbound hd
  rw [← Real.rpow_mul hℓp.le] at hp
  have he : D * (-(1 / (2 * D))) = -(1 / 2 : ℝ) := by
    field_simp [hD.ne']
  rw [he] at hp
  refine ⟨hp, ?_⟩
  have hl := Real.log_le_log hRp hbound
  rwa [Real.log_rpow hℓp] at hl

#print axioms small_conductor_parameters


/-- Uniform scalar logarithmic saving from the explicit gap on page 372. -/
theorem case2_uniform_from_zero_gap (c A κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, ∀ R δ : ℝ, 1 ≤ R → δ ≤ 1 / 5 →
      κ / L N ^ (4 / 5 : ℝ) ≤ δ →
      L N ^ c * (R ^ (5 * δ / 2 - 1 / 2) * (N : ℝ) ^ (-δ / 8)) ≤ L N ^ (-A) := by
  filter_upwards [eventually_stretched_exp c A κ hκ, eventually_ge_atTop 2] with N hN hN2
  intro R δ hR hδ hgap
  have hNp : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hg := case2_with_zero_gap hR hNp hδ hgap
  exact (mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (L_pos hN2).le c)).trans hN

#print axioms case2_uniform_from_zero_gap

end
end LeanLab.PerelliPintz1992.Section6
