/-
Split unit for the exceptional-case short interval mean decay estimate of
LeanLab/Linnik/Decomp486c.lean. This file adds new declarations only: no existing
statement of the parent file is edited. The three leaf estimates below each bound one
range of the conductor sum, and the assembly combines the three into the parent statement.
-/
import LeanLab.Linnik.Decomp486c

namespace LeanLab.Linnik.Decomp486c

open Finset MeasureTheory Filter
open scoped Classical
open LeanLab.Linnik.Decomp466a LeanLab.Linnik.Decomp482a LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (excSet)

/-! ### Leaves, one per range of the conductor sum

The exceptional-case display bounds a double sum over the conductors up to the height and
the primitive characters of each conductor. The conductor sum is cut at one and at the
square root of the height, and each of the three ranges is carried by one leaf:

* `leaf_conductor_one_term`: the conductor-one range alone, where the principal main
  polynomial is subtracted;
* `leaf_low_conductor_range`: conductors from two up to the square root of the height,
  carried by the explicit formula together with the zero free region above the fifth power;
* `leaf_high_conductor_range`: conductors from the square root of the height up to the
  height itself, carried by the density estimate near one.
-/

open LeanLab.Linnik.ExplicitFormula in
/-- Per character and summed over an arbitrary set of conductors: a uniform window bound
`C₁ (N/P)/log N * W(k, χ)` for windows of length at most `N/(2P)` inside `[0, N]` gives the
Gallagher display 14 sum over `F` at most `4π C₁ (sqrt N / log N) Σ_{k ∈ F} Σ_χ W`.
This is `asm_mean_core` with `range ⌊N^θ⌋₊` replaced by `F`. -/
private lemma wip_mean_core_finset (N : ℕ) (θ C₁ : ℝ) (hN : 4 ≤ (N : ℝ)) (hP : 1 ≤ (N : ℝ) ^ θ)
    (hx : 1 ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ)) (hlog : 0 < Real.log N) (hC₁ : 0 ≤ C₁)
    (f : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℕ → ℂ)
    (W : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℝ) (hW0 : ∀ k χ, 0 ≤ W k χ)
    (hf0 : ∀ k χ, f k χ 0 = 0)
    (F : Finset ℕ) (hF : ∀ k ∈ F, k < ⌊(N : ℝ) ^ θ⌋₊)
    (hwin : ∀ k < ⌊(N : ℝ) ^ θ⌋₊, ∀ χ : DirichletCharacter ℂ (k + 1), χ.IsPrimitive →
      ∀ a b : ℕ, b ≤ a → a ≤ N → ((a : ℝ) - b) ≤ (N : ℝ) / (2 * (N : ℝ) ^ θ) →
        ‖∑ n ∈ Ioc b a, f k χ n‖ ≤ C₁ * ((N : ℝ) / (N : ℝ) ^ θ) / Real.log N * W k χ) :
    ∑ k ∈ F,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        Real.pi / (2 * ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊) *
          Real.sqrt (∑ m ∈ range (N + 1 + ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊),
            ‖LeanLab.PNTPort.Gallagher.win (f k χ) (N + 1)
              ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊ m‖ ^ 2)
      ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) *
        ∑ k ∈ F,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            W k χ := by
  set P := (N : ℝ) ^ θ with hPdef
  set L := ⌊(N : ℝ) / (2 * P)⌋₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.floor_pos.mpr hx))
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hkP : k < ⌊(N : ℝ) ^ θ⌋₊ := hF k hk
  rw [mul_sum]
  apply sum_le_sum
  intro χ hχ
  have hprim := (mem_filter.mp hχ).2
  set B := C₁ * ((N : ℝ) / P) / Real.log N * W k χ with hBdef
  have hP0 : 0 < P := by linarith
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have := hW0 k χ
    positivity
  have hsq := asm_win_sq_sum_le (f k χ) (hf0 k χ) N L hL1 hB0 (fun b a hba haN hab => by
    apply hwin k hkP χ hprim a b hba haN
    rw [← Nat.cast_sub hba]
    calc ((a - b : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hab
      _ ≤ _ := Nat.floor_le (by positivity))
  have hfac := asm_norm_factor_le hN hP hx
  have hpi := Real.pi_pos
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hD : 0 ≤ C₁ * W k χ / Real.log N := by
    have := hW0 k χ
    positivity
  calc Real.pi / (2 * (L : ℝ)) * Real.sqrt (∑ m ∈ range (N + 1 + L),
          ‖LeanLab.PNTPort.Gallagher.win (f k χ) (N + 1) L m‖ ^ 2)
      ≤ Real.pi / (2 * (L : ℝ)) * Real.sqrt (((N : ℝ) + 1 + L) * B ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (by positivity)
    _ = Real.pi / (2 * (L : ℝ)) * Real.sqrt ((N : ℝ) + 1 + L) * ((N : ℝ) / P) *
          (C₁ * W k χ / Real.log N) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB0, hBdef]
        ring
    _ ≤ 4 * Real.pi * Real.sqrt N * (C₁ * W k χ / Real.log N) :=
        mul_le_mul_of_nonneg_right hfac hD
    _ = 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * W k χ := by ring

open LeanLab.Linnik.ExplicitFormula in
/-- The exceptional-case display 14 bound, summed over an arbitrary Finset of conductors
`F ⊆ range ⌊N^θ⌋₊`. This is the proof of `ExplicitFormula.mean_decay_exceptional_max` with the
maximality hypothesis of `γ` dropped and the conductor sum restricted to `F`. -/
private theorem wip_exceptional_range_bound :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
          ∀ F : Finset ℕ, (∀ k ∈ F, k < ⌊(N : ℝ) ^ θ⌋₊) → (∀ k ∈ F, k = 0) →
          ∑ k ∈ F,
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
              Real.pi / (2 * ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊) *
                Real.sqrt (∑ m ∈ range (N + 1 + ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊),
                  ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                    ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊ m‖ ^ 2)
            ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  classical
  obtain ⟨C₁, θ₁, hC₁, hθ₁, hW⟩ := window_corr_bound
  set bz := Classical.choose page_zeta_box with hbzdef
  have hbz : 0 < bz := by rw [hbzdef]; exact (Classical.choose_spec page_zeta_box).1
  have hzbox : ∀ {T' : ℝ}, 2 ≤ T' → ∀ ρ : ℂ, 1 - bz / Real.log T' ≤ ρ.re → |ρ.im| ≤ T' →
      riemannZeta ρ ≠ 0 := by
    rw [hbzdef]; exact (Classical.choose_spec page_zeta_box).2
  have hes0 : 0 < exceptionalStrip := LeanLab.Linnik.Decomp466a.exceptionalStrip_pos
  set es := exceptionalStrip with hes
  set b := min es bz with hbdef
  have hb : 0 < b := lt_min hes0 hbz
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hZ⟩ := zero_sum_density_layer b hb
  refine ⟨c₂, 4 * Real.pi * C₁ * (C₂ + 2) + 1, min (min θ₁ θ₂) (1 / 11), hc₂,
    by positivity, lt_min (lt_min hθ₁ hθ₂) (by norm_num),
    (min_le_right _ _).trans (by norm_num), ?_⟩
  intro θ hθ hθ0
  have hθa : θ ≤ θ₁ := hθ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθb : θ ≤ θ₂ := hθ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθc : θ ≤ 1 / 11 := hθ0.trans (min_le_right _ _)
  obtain ⟨NW, hNW⟩ := hW θ hθ hθa
  obtain ⟨NZ, hNZ⟩ := hZ θ hθ hθb
  refine ⟨max (max NW NZ) (max 4 (max ⌈Real.exp (c₂ / θ ^ 2)⌉₊ ⌈Real.exp ((es + 1) / θ)⌉₊)), ?_⟩
  intro N hN x hx hxP γ hγz hγlo hγ1 F hF hF0
  have hNW' : NW ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNZ' : NZ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN4 : (4 : ℝ) ≤ N := by
    have : 4 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    exact_mod_cast this
  have hNe : Real.exp (c₂ / θ ^ 2) ≤ N := by
    have : ⌈Real.exp (c₂ / θ ^ 2)⌉₊ ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hNe' : Real.exp ((es + 1) / θ) ≤ N := by
    have : ⌈Real.exp ((es + 1) / θ)⌉₊ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlogc : c₂ / θ ^ 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe
  have hloge : (es + 1) / θ ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hNe'
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set P := (N : ℝ) ^ θ with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 hθ.le
  have hP0 : 0 < P := by linarith
  have hlogP : Real.log P = θ * Real.log N := by rw [hPdef, Real.log_rpow hN0]
  have hlogP' : es + 1 ≤ Real.log P := by
    rw [hlogP]
    have : es + 1 = θ * ((es + 1) / θ) := by field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hloge hθ.le
  set T := P ^ 5 with hTdef
  have hlogT : Real.log T = 5 * Real.log P := by rw [hTdef, Real.log_pow]; push_cast; ring
  have hlogT0 : 0 < Real.log T := by rw [hlogT]; linarith
  have hesT : es / Real.log T < 1 := by
    rw [div_lt_one hlogT0, hlogT]; linarith
  have hP2 : 2 ≤ P := by
    have h1 : Real.exp 1 ≤ P := by
      rw [← Real.exp_log hP0]; exact Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  have hPT : P ≤ T := by
    rw [hTdef]
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hT2 : 2 ≤ T := hP2.trans hPT
  have hγpos : 0 < γ := by linarith
  -- `2P ≤ N`
  have hPs : P ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsN : 2 ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN4)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hx2 : 1 ≤ (N : ℝ) / (2 * P) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `P^3 ≤ X = N/P^8`
  set X := (N : ℝ) / P ^ 8 with hXdef
  have hP11 : P ^ 11 ≤ N := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    calc (N : ℝ) ^ (θ * ((11 : ℕ) : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = N := Real.rpow_one _
  have hX3 : P ^ 3 ≤ X := by
    rw [hXdef, le_div_iff₀ (by positivity)]
    calc P ^ 3 * P ^ 8 = P ^ 11 := by ring
      _ ≤ (N : ℝ) := hP11
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX3
  have hXinv : X⁻¹ ≤ P⁻¹ ^ 3 := by
    rw [inv_pow]; exact inv_anti₀ (by positivity) hX3
  have hPe : P⁻¹ ≤ Real.exp (-c₂ / θ) := by
    rw [hPdef, Real.rpow_def_of_pos hN0, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have : c₂ / θ ≤ Real.log N * θ := by
      have h1 : c₂ / θ = θ * (c₂ / θ ^ 2) := by field_simp
      rw [h1, mul_comm (Real.log N)]
      exact mul_le_mul_of_nonneg_left hlogc hθ.le
    rw [neg_div]; linarith
  -- the weights, with the exceptional zero removed once
  let w : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℂ → ℝ := fun k χ ρ =>
    max ((mult χ ρ : ℝ) -
      (if k + 1 = x.1 + 1 ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0)) 0
  have hw0 : ∀ k χ ρ, 0 ≤ w k χ ρ := fun k χ ρ => le_max_right _ _
  have hwm : ∀ k χ ρ, w k χ ρ ≤ mult χ ρ := fun k χ ρ => by
    apply max_le _ (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ (if k + 1 = x.1 + 1 ∧ χ.LFunction (γ : ℂ) = 0 ∧ ρ = (γ : ℂ) then 1 else 0) := by
      split_ifs <;> norm_num
    linarith
  let W : (k : ℕ) → DirichletCharacter ℂ (k + 1) → ℝ := fun k χ =>
    ∑ ρ ∈ zerosTo χ (P ^ 10), w k χ ρ * X ^ (ρ.re - 1) + P⁻¹ ^ 3
  have hW0 : ∀ k χ, 0 ≤ W k χ := fun k χ => add_nonneg
    (sum_nonneg fun ρ _ => mul_nonneg (hw0 k χ ρ) (Real.rpow_nonneg hX0.le _))
    (by positivity)
  -- the per window bound, summed over the range `F`
  have hcore : ∑ k ∈ F,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        Real.pi / (2 * ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊) *
          Real.sqrt (∑ m ∈ range (N + 1 + ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊),
            ‖LeanLab.PNTPort.Gallagher.win (corrCoef χ (x.1 + 1) γ) (N + 1)
              ⌊(N : ℝ) / (2 * (N : ℝ) ^ θ)⌋₊ m‖ ^ 2)
      ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) *
        ∑ k ∈ F,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            W k χ := by
    exact wip_mean_core_finset N θ C₁ hN4 hP1 hx2 hlog hC₁
      (fun k χ => corrCoef χ (x.1 + 1) γ) W hW0 (fun k χ => asm_corrCoef_zero χ _ _) F
      (fun k hk => hF k hk) (by
      intro k hk χ hχ a b' hba haN hab
      have h := hNW N hNW' k hk χ hχ (x.1 + 1) γ (fun _ => ⟨hγpos, hγ1⟩) a b' hba (by omega) hab
      refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact add_le_add (sum_le_sum fun ρ _ =>
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hX0.le _)) le_rfl)  -- the zero density layer, supported on the conductors in `F` only
  let S : (k : ℕ) → DirichletCharacter ℂ (k + 1) → Finset ℂ := fun k χ =>
    if k ∈ F ∧ χ.IsPrimitive then (zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re) else ∅
  have hS : ∀ k χ ρ, ρ ∈ S k χ → χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ P ^ 10 ∧ (|ρ.im| ≤ P ^ 5 → ρ.re < 1 - b / Real.log (P ^ 5)) := by
    intro k χ ρ hρ
    simp only [S] at hρ
    split_ifs at hρ with hc
    · obtain ⟨hρz, hre⟩ := mem_filter.mp hρ
      obtain ⟨⟨hz, _, hne⟩, him⟩ := asm_mem_zerosTo hρz
      have hk0 : k = 0 := hF0 k hc.1
      subst hk0
      have hlt1 : ρ.re < 1 := by
        by_contra h1
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne) (not_lt.mp h1) hz
      refine ⟨hz, hre, hlt1, him, fun h5 => ?_⟩
      by_contra hge
      push_neg at hge
      have hzeta0 : riemannZeta ρ = 0 := by
        simpa only [DirichletCharacter.LFunction_modOne_eq] using hz
      exact hzbox (T' := T) hT2 ρ (by
        have hbzT : b / Real.log T ≤ bz / Real.log T :=
          div_le_div_of_nonneg_right (min_le_right _ _) hlogT0.le
        linarith) h5 hzeta0
    · simp at hρ
  have hZb := hNZ N hNZ' S hS
  have hZb' : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤ C₂ * Real.exp (-c₂ / θ) := hZb
  have hSsum : ∑ k ∈ F,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤ C₂ * Real.exp (-c₂ / θ) :=
    (sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.mpr (hF k hk))
      (fun k _ _ => sum_nonneg fun χ _ => sum_nonneg fun ρ _ =>
        mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _))).trans hZb'
  have hsumZ : ∑ k ∈ F,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        W k χ ≤
      ∑ k ∈ F,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
          (∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) + 2 * P⁻¹ ^ 3) := by
    apply sum_le_sum
    intro k hk
    apply sum_le_sum
    intro χ hχ
    have hprim := (mem_filter.mp hχ).2
    have hSe : S k χ = (zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re) := by
      simp only [S]; rw [if_pos ⟨hk, hprim⟩]
    have h1 := asm_zsum_split hprim (P ^ 10) X hX0 (w k χ) (hw0 k χ) (hwm k χ)
    have h2 : ∑ ρ ∈ (zerosTo χ (P ^ 10)).filter (fun ρ => 0 < ρ.re), w k χ ρ * X ^ (ρ.re - 1)
        ≤ ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) := by
      rw [hSe]
      exact sum_le_sum fun ρ _ =>
        mul_le_mul_of_nonneg_right (hwm k χ ρ) (Real.rpow_nonneg hX0.le _)
    simp only [W]
    linarith
  have hcountR : ∑ k ∈ range ⌊P⌋₊,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (2 * P⁻¹ ^ 3) ≤ 2 * Real.exp (-c₂ / θ) := by
    have hK : ((⌊P⌋₊ : ℕ) : ℝ) ≤ P := Nat.floor_le hP0.le
    calc _ = ∑ k ∈ range ⌊P⌋₊,
          (((univ : Finset (DirichletCharacter ℂ (k + 1))).filter
            (fun χ => χ.IsPrimitive)).card : ℝ) * (2 * P⁻¹ ^ 3) := by
          apply sum_congr rfl; intro k _; rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ range ⌊P⌋₊, P * (2 * P⁻¹ ^ 3) := by
          apply sum_le_sum; intro k hk
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h1 := asm_card_prim_le k
          have h2 : k + 1 ≤ ⌊P⌋₊ := mem_range.mp hk
          calc (_ : ℝ) ≤ ((⌊P⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
            _ ≤ P := hK
      _ = (⌊P⌋₊ : ℝ) * (P * (2 * P⁻¹ ^ 3)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ P * (P * (2 * P⁻¹ ^ 3)) := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = 2 * P⁻¹ := by field_simp
      _ ≤ 2 * Real.exp (-c₂ / θ) := by linarith
  have hcount : ∑ k ∈ F,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        (2 * P⁻¹ ^ 3) ≤ 2 * Real.exp (-c₂ / θ) :=
    (sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.mpr (hF k hk))
      (fun k _ _ => sum_nonneg fun χ _ => by positivity)).trans hcountR
  have htot : ∑ k ∈ F,
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
        W k χ ≤ (C₂ + 2) * Real.exp (-c₂ / θ) := by
    refine hsumZ.trans ?_
    calc _ = ∑ k ∈ F,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            ∑ ρ ∈ S k χ, (mult χ ρ : ℝ) * X ^ (ρ.re - 1) +
          ∑ k ∈ F,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            (2 * P⁻¹ ^ 3) := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro k _
          rw [← sum_add_distrib]
      _ ≤ C₂ * Real.exp (-c₂ / θ) + 2 * Real.exp (-c₂ / θ) := add_le_add hSsum hcount
      _ = (C₂ + 2) * Real.exp (-c₂ / θ) := by ring
  refine hcore.trans ?_
  have hA : 0 ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) := by positivity
  have hE : 0 ≤ Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N) := by positivity
  calc 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * _
      ≤ 4 * Real.pi * C₁ * (Real.sqrt N / Real.log N) * ((C₂ + 2) * Real.exp (-c₂ / θ)) :=
        mul_le_mul_of_nonneg_left htot hA
    _ = (4 * Real.pi * C₁ * (C₂ + 2)) * (Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N)) := by
        ring
    _ ≤ (4 * Real.pi * C₁ * (C₂ + 2) + 1) *
          (Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N)) :=
        mul_le_mul_of_nonneg_right (by linarith) hE
    _ = _ := by ring

/-- LEAF. The conductor-one range of the conductor sum. The single primitive character of
conductor one, with the principal main polynomial removed, contributes at most a constant
times e to the minus c over theta times the natural scale sqrt N over log N, uniformly over
every point of the exceptional set inside the window and every real zero of its character in
the strip. This is the first step of the exceptional-case display: the range where the
principal main polynomial is subtracted. -/
theorem leaf_conductor_one_term :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ Ico 0 1,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  obtain ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, hmain⟩ := wip_exceptional_range_bound
  refine ⟨c, C, θ₀, hc, hC, hθ₀, hθ₀2, ?_⟩
  intro θ hθ hθle
  obtain ⟨N₀, hN₀⟩ := hmain θ hθ hθle
  refine ⟨max N₀ 4, ?_⟩
  intro N hN x hx hxP γ hz hγlo hγ1
  have hN₀' : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hfl : 0 < ⌊(N : ℝ) ^ θ⌋₊ := Nat.floor_pos.mpr (Real.one_le_rpow hN1 hθ.le)
  have hkey := hN₀ N hN₀' x hx hxP γ hz hγlo hγ1 (Ico 0 1)
    (by intro k hk; simp only [mem_Ico] at hk; omega)
    (by intro k hk; simp only [mem_Ico] at hk; omega)
  simpa only [gallagherLength] using hkey


/-- LEAF. The low conductor range of the conductor sum. Over the conductors from two up to
the square root cut of the height, primitive characters only, the same double sum is at most
a constant times e to the minus c over theta times sqrt N over log N, uniformly in the point
of the exceptional set and in its real zero. This is the second step of the exceptional-case
display: the range carried by the explicit formula for the primitive L function together with
the zero free region above the fifth power of the height. -/
theorem leaf_low_conductor_range :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ Ico 1 ⌊(N : ℝ) ^ (θ / 2)⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-- LEAF. The high conductor range of the conductor sum. Over the conductors from the square
root cut of the height up to the height itself, primitive characters only, the same double
sum is at most a constant times e to the minus c over theta times sqrt N over log N,
uniformly in the point of the exceptional set and in its real zero. This is the third step of
the exceptional-case display: the range carried by the density estimate near one. -/
theorem leaf_high_conductor_range :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ Ico ⌊(N : ℝ) ^ (θ / 2)⌋₊ ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  sorry

/-! ### Assembly -/

/-- Adding two exponentially decaying pieces at a common rate. Both bounds carry a
nonnegative scale, and the rate of the sum is the smaller of the two rates while its
constant is twice the larger constant. With scale zero this is trivial, so nothing here
depends on the sizes involved. -/
private lemma add_two_exponential_bounds {E₁ E₂ c c₁ c₂ C₁ C₂ θ s : ℝ} (hθ : 0 < θ)
    (hs : 0 ≤ s) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂)
    (h₁ : E₁ ≤ C₁ * Real.exp (-c₁ / θ) * s)
    (h₂ : E₂ ≤ C₂ * Real.exp (-c₂ / θ) * s) :
    E₁ + E₂ ≤ (2 * max C₁ C₂) * Real.exp (-c / θ) * s := by
  have hexp₁ : Real.exp (-c₁ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hexp₂ : Real.exp (-c₂ / θ) ≤ Real.exp (-c / θ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hθ.le)
  have hpos : (0 : ℝ) ≤ Real.exp (-c / θ) := (Real.exp_pos _).le
  have h₁' : E₁ ≤ C₁ * Real.exp (-c / θ) * s :=
    h₁.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₁ hC₁) hs)
  have h₂' : E₂ ≤ C₂ * Real.exp (-c / θ) * s :=
    h₂.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp₂ hC₂) hs)
  have hmid : E₁ + E₂ ≤ (C₁ + C₂) * Real.exp (-c / θ) * s := by
    have hsplit : C₁ * Real.exp (-c / θ) * s + C₂ * Real.exp (-c / θ) * s
        = (C₁ + C₂) * Real.exp (-c / θ) * s := by ring
    linarith
  have hCC : C₁ + C₂ ≤ 2 * max C₁ C₂ := by
    have h₁'' := le_max_left C₁ C₂
    have h₂'' := le_max_right C₁ C₂
    linarith
  exact hmid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hpos) hs)

/-- The parent statement of this split, with the same statement text as
LeanLab/Linnik/Decomp486c.lean, proved from the three leaf estimates above. The parent
theorem of the same name is neither used nor restated as a hypothesis. -/
theorem short_interval_mean_decay_exceptional_split :
    ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ₀ ∧ θ₀ ≤ 1 / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
          ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ →
          ∀ γ : ℝ, x.2.LFunction (γ : ℂ) = 0 →
            1 - exceptionalStrip / Real.log (((N : ℝ) ^ θ) ^ 5) ≤ γ → γ < 1 →
        ∑ k ∈ range ⌊(N : ℝ) ^ θ⌋₊,
          ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive),
            Real.pi / (2 * gallagherLength N θ) *
              Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ),
                ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1)
                  (gallagherLength N θ) m‖ ^ 2)
          ≤ C * Real.exp (-c / θ) * (Real.sqrt N / Real.log N) := by
  obtain ⟨c₁, C₁, θ₁, hc₁, hC₁, hθ₁, hθ₁2, hleaf₁⟩ := leaf_conductor_one_term
  obtain ⟨c₂, C₂, θ₂, hc₂, hC₂, hθ₂, hθ₂2, hleaf₂⟩ := leaf_low_conductor_range
  obtain ⟨c₃, C₃, θ₃, hc₃, hC₃, hθ₃, hθ₃2, hleaf₃⟩ := leaf_high_conductor_range
  have hC₁₂ : (0 : ℝ) < 2 * max C₁ C₂ := by
    have h : (0 : ℝ) < max C₁ C₂ := lt_of_lt_of_le hC₁ (le_max_left _ _)
    linarith
  have hC : (0 : ℝ) < 2 * max (2 * max C₁ C₂) C₃ := by
    have h : (0 : ℝ) < max (2 * max C₁ C₂) C₃ := lt_of_lt_of_le hC₁₂ (le_max_left _ _)
    linarith
  refine ⟨min (min c₁ c₂) c₃, 2 * max (2 * max C₁ C₂) C₃, min (min θ₁ θ₂) θ₃,
    lt_min (lt_min hc₁ hc₂) hc₃, hC, lt_min (lt_min hθ₁ hθ₂) hθ₃, ?_, ?_⟩
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans hθ₁2)
  intro θ hθ hθle
  have hθ₁' : θ ≤ θ₁ := (hθle.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hθ₂' : θ ≤ θ₂ := (hθle.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hθ₃' : θ ≤ θ₃ := hθle.trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hleaf₁ θ hθ hθ₁'
  obtain ⟨N₂, hN₂⟩ := hleaf₂ θ hθ hθ₂'
  obtain ⟨N₃, hN₃⟩ := hleaf₃ θ hθ hθ₃'
  refine ⟨max (max (max N₁ N₂) N₃) 4, ?_⟩
  intro N hN x hx hxP γ hz hγlo hγ1
  have hN₄ : 4 ≤ N := (le_max_right _ _).trans hN
  have hN₁' : N₁ ≤ N :=
    ((le_max_left N₁ N₂).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hN₂' : N₂ ≤ N :=
    ((le_max_right N₁ N₂).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hN)
  have hN₃' : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have h₁ := hN₁ N hN₁' x hx hxP γ hz hγlo hγ1
  have h₂ := hN₂ N hN₂' x hx hxP γ hz hγlo hγ1
  have h₃ := hN₃ N hN₃' x hx hxP γ hz hγlo hγ1
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow : (N : ℝ) ^ (θ / 2) ≤ (N : ℝ) ^ θ :=
    Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hAK : ⌊(N : ℝ) ^ (θ / 2)⌋₊ ≤ ⌊(N : ℝ) ^ θ⌋₊ := Nat.floor_mono hpow
  have hbase : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hhalf : (0 : ℝ) ≤ θ / 2 := by linarith
  have hpowhalf : (1 : ℝ) ≤ (N : ℝ) ^ (θ / 2) := Real.one_le_rpow hN1r hhalf
  have hA1 : 1 ≤ ⌊(N : ℝ) ^ (θ / 2)⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg hbase (θ / 2))).mpr (by simpa using hpowhalf)
  have hs : (0 : ℝ) ≤ Real.sqrt N / Real.log N :=
    div_nonneg (Real.sqrt_nonneg _) (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).le
  set g : ℕ → ℝ := fun k => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (k + 1))).filter (fun χ => χ.IsPrimitive), Real.pi / (2 * gallagherLength N θ) * Real.sqrt (∑ m ∈ range (N + 1 + gallagherLength N θ), ‖LeanLab.PNTPort.Gallagher.win (correctedCoefficient χ (x.1 + 1) γ) (N + 1) (gallagherLength N θ) m‖ ^ 2) with hg
  have h₁g : ∑ k ∈ Ico 0 1, g k
      ≤ C₁ * Real.exp (-c₁ / θ) * (Real.sqrt N / Real.log N) := by
    rw [hg]
    exact h₁
  have h₂g : ∑ k ∈ Ico 1 ⌊(N : ℝ) ^ (θ / 2)⌋₊, g k
      ≤ C₂ * Real.exp (-c₂ / θ) * (Real.sqrt N / Real.log N) := by
    rw [hg]
    exact h₂
  have h₃g : ∑ k ∈ Ico ⌊(N : ℝ) ^ (θ / 2)⌋₊ ⌊(N : ℝ) ^ θ⌋₊, g k
      ≤ C₃ * Real.exp (-c₃ / θ) * (Real.sqrt N / Real.log N) := by
    rw [hg]
    exact h₃
  rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive g (Nat.zero_le _) hAK]
  rw [← Finset.sum_Ico_consecutive g (Nat.zero_le 1) hA1]
  have hcc₁ : min (min c₁ c₂) c₃ ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcc₂ : min (min c₁ c₂) c₃ ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hcc₃ : min (min c₁ c₂) c₃ ≤ c₃ := min_le_right _ _
  have hcomb := add_two_exponential_bounds hθ hs hC₁.le hC₂.le hcc₁ hcc₂ h₁g h₂g
  exact add_two_exponential_bounds hθ hs hC₁₂.le hC₃.le (le_refl _) hcc₃ hcomb h₃g

-- Axioms of the assembly: only the three leaves carry sorry.
#print axioms LeanLab.Linnik.Decomp486c.short_interval_mean_decay_exceptional_split
