/-
Split of bhp_minorant_progression_asymptotic from Feed1122Decomp379a.
Baker, Harman and Pintz 1997, P0069, page 3 Theorem 2 item i, display 1.7,
and page 4, proof of Theorem 3 part I: the section 4 minorant a0 satisfies
display 1.7 for every character modulo q up to a power of log, and integers
congruent to a modulo q are picked out using characters in standard fashion.
Page 41: the associated constant u0 exceeds 0.9953.
The character pick out and the comparison of the main term with the
logarithmic integral are proved here; only the display 1.7 input stays a LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp379a

namespace LeanLab.Ternary.MMS.Task379
open Finset Filter Topology

open Classical in
/-- LEAF: BHP 1997 page 3, Theorem 2 item i, display 1.7, for the section 4
minorant a0 of page 4 with associated constant u0 above 0.9953 from page 41,
applied as in the proof of Theorem 3 part I on page 4 with the interval I taken
to be the short interval itself and with A equal to 4. For every Dirichlet
character χ modulo d up to log squared, the twisted sum of a0 over the interval
equals δ_χ u0 over L per integer, up to an error O of the length over L to the 4.
HARD. -/
theorem bhp_minorant_character_sums (σ : ℝ) (hσ : 11 / 20 < σ) (hσ1 : σ < 1) :
    ∃ a0 : ℝ → ℕ → ℝ, (∀ y : ℝ, ∀ n : ℕ, a0 y n ≤ ρ n) ∧
      ∃ u0 : ℝ, 0.9953 < u0 ∧ ∃ C : ℝ, ∃ Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y →
        ∀ h : ℝ, y ^ σ ≤ h → h ≤ y / Real.log y → ∀ d : ℕ, 1 ≤ d →
        (d : ℝ) ≤ Real.log y ^ (2 : ℕ) → ∀ χ : DirichletCharacter ℂ d,
        ‖∑ n ∈ ints (y - h) y, (a0 y n : ℂ) * χ (n : ZMod d) -
            (if χ = 1 then ((u0 * (ints (y - h) y).card / Real.log y : ℝ) : ℂ) else 0)‖ ≤
          C * h / Real.log y ^ (4 : ℕ) := by
  sorry

/-- Character pick out of a residue class, BHP page 4 proof of Theorem 3 part I,
standard orthogonality of Dirichlet characters. -/
theorem class_sum_eq_char_sum (S : Finset ℕ) (f : ℕ → ℂ) {d c : ℕ} [NeZero d]
    (hcd : Nat.Coprime c d) :
    (d.totient : ℂ) * ∑ n ∈ S.filter (fun n => n ≡ c [MOD d]), f n =
      ∑ χ : DirichletCharacter ℂ d, χ ((c : ZMod d)⁻¹) * ∑ n ∈ S, f n * χ (n : ZMod d) := by
  have hu : IsUnit (c : ZMod d) := (ZMod.isUnit_iff_coprime c d).mpr hcd
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod d)
  have hre : ∑ χ : DirichletCharacter ℂ d, χ ((c : ZMod d)⁻¹) * (f n * χ (n : ZMod d)) =
      f n * ∑ χ : DirichletCharacter ℂ d, χ ((c : ZMod d)⁻¹) * χ (n : ZMod d) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun χ _ => by ring
  rw [hre, horth]
  have hiff : ((c : ZMod d) = (n : ZMod d)) ↔ n ≡ c [MOD d] := by
    rw [ZMod.natCast_eq_natCast_iff]; exact ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  by_cases h : n ≡ c [MOD d]
  · simp [h, hiff.mpr h]; ring
  · simp [h, (not_congr hiff).mpr h]

/-- The number of integers in the closed short interval differs from its length
by at most one. Elementary step in BHP page 4, proof of Theorem 3 part I. -/
theorem ints_card_bounds {y h : ℝ} (h1 : 1 ≤ h) (hyh : 0 ≤ y - h) :
    h - 1 ≤ ((ints (y - h) y).card : ℝ) ∧ ((ints (y - h) y).card : ℝ) ≤ h + 1 := by
  unfold ints
  rw [Nat.card_Icc]
  have ha1 : (⌈y - h⌉₊ : ℝ) < y - h + 1 := Nat.ceil_lt_add_one hyh
  have ha2 : y - h ≤ (⌈y - h⌉₊ : ℝ) := Nat.le_ceil _
  have hb1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hb2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hab : ⌈y - h⌉₊ ≤ ⌊y⌋₊ + 1 := by
    have : (⌈y - h⌉₊ : ℝ) < ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact (Nat.cast_lt.mp this).le
  rw [Nat.cast_sub hab]
  push_cast
  constructor <;> linarith

/-- The logarithmic integral of a short interval is at most its length over
the log of the left end. Elementary step behind the main term in BHP page 4. -/
theorem logIntegral_le_short {y h : ℝ} (hh : 0 ≤ h) (hyh : 1 < y - h) :
    ∫ t in (y - h)..y, 1 / Real.log t ≤ h / Real.log (y - h) := by
  have hl : 0 < Real.log (y - h) := Real.log_pos hyh
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc (y - h) y) := by
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (by linarith [ht.1] : (0 : ℝ) < t).ne')
    · intro t ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
  have hab : y - h ≤ y := by linarith
  have hmono : ∫ t in (y - h)..y, 1 / Real.log t ≤
      ∫ t in (y - h)..y, (1 / Real.log (y - h)) := by
    apply intervalIntegral.integral_mono_on hab
    · exact hcont.intervalIntegrable_of_Icc hab
    · exact intervalIntegrable_const
    · intro t ht
      exact one_div_le_one_div_of_le hl (Real.log_le_log (by linarith) ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have : (y - (y - h)) * (1 / Real.log (y - h)) = h / Real.log (y - h) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- Glue: the progression asymptotic of Feed1122Decomp379a from display 1.7
for characters, by the character pick out and the main term comparison.
CONDITIONAL ON bhp_minorant_character_sums. -/
theorem bhp_minorant_progression_asymptotic_of_leaves (σ : ℝ) (hσ : 11 / 20 < σ) (hσ1 : σ < 1) :
    ∃ a0 : ℝ → ℕ → ℝ, (∀ y : ℝ, ∀ n : ℕ, a0 y n ≤ ρ n) ∧
      ∃ u0 : ℝ, 0.9953 < u0 ∧ ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y →
        ∀ h : ℝ, y ^ σ ≤ h → h ≤ y / Real.log y → ∀ d c : ℕ,
        1 ≤ d → (d : ℝ) ≤ Real.log y ^ (2 : ℕ) → Nat.Coprime c d →
        |∑ n ∈ (ints (y - h) y).filter (fun n => n ≡ c [MOD d]), a0 y n -
            u0 / d.totient * ∫ t in (y - h)..y, 1 / Real.log t| ≤
          ε * h / (d.totient * Real.log y) := by
  classical
  obtain ⟨a0, ha0, u0, hu0, C, Y0, hY0, hA⟩ := bhp_minorant_character_sums σ hσ hσ1
  refine ⟨a0, ha0, u0, hu0, ?_⟩
  intro ε hε
  have hu0p : 0 < u0 := by linarith
  set δ : ℝ := ε / (4 * u0) with hδ
  have hδp : 0 < δ := by positivity
  set K : ℝ := max (max 4 (4 * (|C| + 1) / ε)) ((1 + δ) / δ) with hK
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop K
  have e2 := (tendsto_rpow_atTop (by linarith : (0:ℝ) < σ)).eventually_ge_atTop
    (4 * u0 / ε + 1)
  obtain ⟨Y1, hY1⟩ := Filter.eventually_atTop.mp (e1.and e2)
  refine ⟨max (max Y0 Y1) 2, lt_of_lt_of_le hY0 ((le_max_left _ _).trans (le_max_left _ _)),
    ?_⟩
  intro y hy h hlow hupp d c hd hdlog hcd
  have hyY0 : Y0 ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyY1 : Y1 ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy2 : 2 ≤ y := (le_max_right _ _).trans hy
  obtain ⟨hL, hpow⟩ := hY1 y hyY1
  have hL4 : 4 ≤ Real.log y := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLC : 4 * (|C| + 1) / ε ≤ Real.log y :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLδ : (1 + δ) / δ ≤ Real.log y := (le_max_right _ _).trans hL
  set L := Real.log y with hLdef
  have hLp : 0 < L := by linarith
  have hh : 4 * u0 / ε + 1 ≤ h := hpow.trans hlow
  have hq : 0 < 4 * u0 / ε := by positivity
  have hh1 : 1 ≤ h := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hhy : h ≤ y / 4 :=
    hupp.trans (div_le_div_of_nonneg_left (by linarith) (by norm_num) hL4)
  have hyh : 1 < y - h := by linarith
  have : NeZero d := ⟨by omega⟩
  set S := ints (y - h) y with hS
  have hφpos : 0 < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
  have hφle : (d.totient : ℝ) ≤ L ^ 2 :=
    (Nat.cast_le.mpr (Nat.totient_le d)).trans hdlog
  set M : ℝ := u0 * S.card / L with hM
  set cs : ℝ := ∑ n ∈ S.filter (fun n => n ≡ c [MOD d]), a0 y n with hcs
  have hu : IsUnit (c : ZMod d) := (ZMod.isUnit_iff_coprime c d).mpr hcd
  -- character pick out
  have hchar : ((d.totient * cs - M : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ d, χ ((c : ZMod d)⁻¹) *
        (∑ n ∈ S, (a0 y n : ℂ) * χ (n : ZMod d) - if χ = 1 then (M : ℂ) else 0) := by
    have h1 := class_sum_eq_char_sum S (fun n => (a0 y n : ℂ)) hcd
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← h1]
    have h2 : ∑ χ : DirichletCharacter ℂ d,
        χ ((c : ZMod d)⁻¹) * (if χ = 1 then (M : ℂ) else 0) = (M : ℂ) := by
      rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ d)]
      · have hui : IsUnit ((c : ZMod d)⁻¹) :=
          ⟨hu.unit⁻¹, by rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]⟩
        simp [MulChar.one_apply hui]
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2, hcs]
    push_cast
    rfl
  have hnorm : |d.totient * cs - M| ≤ d.totient * (|C| * h / L ^ (4 : ℕ)) := by
    have hnr := Complex.norm_real (d.totient * cs - M)
    rw [Real.norm_eq_abs] at hnr
    rw [← hnr, hchar]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)),
        ‖χ ((c : ZMod d)⁻¹) *
          (∑ n ∈ S, (a0 y n : ℂ) * χ (n : ZMod d) - if χ = 1 then (M : ℂ) else 0)‖ ≤
          |C| * h / L ^ (4 : ℕ) := by
      intro χ _
      rw [norm_mul]
      have hχ : ‖χ ((c : ZMod d)⁻¹)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hT := hA y hyY0 h hlow hupp d hd hdlog χ
      have hT' : C * h / L ^ (4 : ℕ) ≤ |C| * h / L ^ (4 : ℕ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_abs_self C) hh0
      have hT'' : ‖∑ n ∈ S, (a0 y n : ℂ) * χ (n : ZMod d) -
          (if χ = 1 then (M : ℂ) else 0)‖ ≤ |C| * h / L ^ (4 : ℕ) := by
        convert hT.trans hT' using 4
      calc _ ≤ 1 * ‖∑ n ∈ S, (a0 y n : ℂ) * χ (n : ZMod d) -
            (if χ = 1 then (M : ℂ) else 0)‖ :=
            mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hT''
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans (le_of_eq ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, nsmul_eq_mul]
  have hcsM : |cs - M / d.totient| ≤ |C| * h / L ^ (4 : ℕ) := by
    have : cs - M / d.totient = (d.totient * cs - M) / d.totient := by
      field_simp
    rw [this, abs_div, abs_of_pos hφpos, div_le_iff₀ hφpos]
    linarith [hnorm]
  -- main term
  have hIlo := logIntegral_ge_short hh0 hyh
  have hIhi := logIntegral_le_short hh0 hyh
  set I := ∫ t in (y - h)..y, 1 / Real.log t with hI
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlyh : L - 1 ≤ Real.log (y - h) := by
    have h2 : y / 2 ≤ y - h := by linarith
    have := Real.log_le_log (by linarith) h2
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  have hδL : 1 + δ ≤ δ * L := by
    have := (div_le_iff₀ hδp).mp hLδ; linarith
  have hlogyh : h / Real.log (y - h) ≤ (1 + δ) * h / L := by
    rw [div_le_div_iff₀ (by linarith) hLp]
    have : L ≤ (1 + δ) * Real.log (y - h) := by nlinarith
    nlinarith
  obtain ⟨hc1, hc2⟩ := ints_card_bounds hh1 (by linarith : 0 ≤ y - h)
  have hMI : |M - u0 * I| ≤ ε * h / (2 * L) := by
    have hcardL1 : ((S.card : ℝ) - h) / L ≤ 1 / L := by
      apply div_le_div_of_nonneg_right _ hLp.le; linarith
    have hcardL2 : -(1 / L) ≤ ((S.card : ℝ) - h) / L := by
      rw [← neg_div]; apply div_le_div_of_nonneg_right _ hLp.le; linarith
    have hMe : M - u0 * I = u0 * (((S.card : ℝ) - h) / L + (h / L - I)) := by
      rw [hM]; ring
    have hIa : h / L - I ≤ 0 := by linarith
    have hIb : -(δ * h / L) ≤ h / L - I := by
      have : (1 + δ) * h / L = h / L + δ * h / L := by ring
      linarith
    have hkey : |((S.card : ℝ) - h) / L + (h / L - I)| ≤ 1 / L + δ * h / L := by
      rw [abs_le]; constructor <;> linarith
    have hu0L : u0 * (1 / L) ≤ ε * h / (4 * L) := by
      rw [mul_one_div, div_le_div_iff₀ hLp (by positivity)]
      have : 4 * u0 ≤ ε * h := by
        have := (div_le_iff₀ hε).mp (by linarith : 4 * u0 / ε ≤ h); linarith
      calc u0 * (4 * L) = 4 * u0 * L := by ring
        _ ≤ ε * h * L := mul_le_mul_of_nonneg_right this hLp.le
    have hu0δ : u0 * (δ * h / L) = ε * h / (4 * L) := by
      rw [hδ]; field_simp
    rw [hMe, abs_mul, abs_of_pos hu0p]
    calc u0 * |((S.card : ℝ) - h) / L + (h / L - I)| ≤ u0 * (1 / L + δ * h / L) :=
          mul_le_mul_of_nonneg_left hkey hu0p.le
      _ = u0 * (1 / L) + u0 * (δ * h / L) := by ring
      _ ≤ ε * h / (4 * L) + ε * h / (4 * L) := by rw [hu0δ]; linarith
      _ = ε * h / (2 * L) := by ring
  -- combine
  have hsplit : cs - u0 / d.totient * I = (cs - M / d.totient) + (M - u0 * I) / d.totient := by
    field_simp; ring
  have hCbound : |C| * h / L ^ (4 : ℕ) ≤ ε * h / (2 * L * d.totient) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2C : 2 * |C| ≤ ε * L := by
      have := (div_le_iff₀ hε).mp hLC; nlinarith [abs_nonneg C]
    have : |C| * h * (2 * L * d.totient) ≤ |C| * h * (2 * L * L ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hφle (by positivity)
    have : |C| * h * (2 * L * L ^ 2) ≤ ε * h * L ^ (4 : ℕ) := by
      have : |C| * h * (2 * L * L ^ 2) = (2 * |C|) * (h * L ^ 3) := by ring
      rw [this]
      have : ε * h * L ^ (4 : ℕ) = (ε * L) * (h * L ^ 3) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h2C (by positivity)
    linarith
  have hMIφ : |(M - u0 * I) / d.totient| ≤ ε * h / (2 * L * d.totient) := by
    rw [abs_div, abs_of_pos hφpos, div_le_div_iff₀ hφpos (by positivity)]
    have := mul_le_mul_of_nonneg_right hMI (by positivity : (0:ℝ) ≤ 2 * L * d.totient)
    have e : ε * h / (2 * L) * (2 * L * d.totient) = ε * h * d.totient := by
      field_simp
    nlinarith
  rw [hsplit]
  calc |(cs - M / d.totient) + (M - u0 * I) / d.totient|
      ≤ |cs - M / d.totient| + |(M - u0 * I) / d.totient| := abs_add_le _ _
    _ ≤ ε * h / (2 * L * d.totient) + ε * h / (2 * L * d.totient) := by linarith
    _ = ε * h / (d.totient * L) := by field_simp; ring

end LeanLab.Ternary.MMS.Task379
