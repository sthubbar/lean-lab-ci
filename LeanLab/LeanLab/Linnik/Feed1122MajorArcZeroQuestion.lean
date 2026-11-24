/-
QUESTION record for the split `SPLIT_major_arc_energy_zero.lean`, burst 2026-11-22.

The split cuts the conductor zero frequency error of Gallagher 1975 p.127 Theorem 3 by the
triangle inequality into the major arc integral and the main term `J(n) 𝔖(n)`, and asks each
piece alone to be bounded by the small error term. But each piece alone has the size of the
main term. This file proves, with no sorry, that the main series leaf
`leaf_main_series_part_bound` is refuted as soon as two inputs hold:

* `‖𝔖(2)‖ ≥ 1`, where in fact `𝔖(2) = 2 ∏_{p > 2} (1 - 1/(p-1)²) ≈ 1.32`;
* for every positive θ there are arbitrarily large `N` with no exceptional character of
  conductor at most `N^θ` in the fixed strip, which holds under GRH and is expected
  unconditionally from Landau's theorem.

The proof uses the proved `Decomp486c.energy_decay_without_exception` and the trivial lower
bound `J(2) ≥ (N - 3)/log² N`. So the leaf is FALSE CONDITIONAL ON these two inputs, and the
split is not faithful. The parent `Decomp486b.major_arc_energy_zero` is untouched.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Decomp486b

namespace LeanLab.Linnik.Feed1122MajorArcZeroQuestion

open Finset MeasureTheory
open scoped Classical
open LeanLab.Linnik.Decomp466a
open LeanLab.Linnik.Decomp482a
open LeanLab.Linnik.Decomp482b
open LeanLab.Linnik.Decomp1532b (majorArcs Jn singSeries excSet)

/-- The trivial lower bound for the correlation count of Gallagher 1975 p.127 Theorem 3 at
frequency two: the pairs `(m + 2, m)` with `1 < m ≤ N - 2` each contribute at least
`1/log² N`. -/
theorem Jn_two_lower (N : ℕ) (hN : 3 ≤ N) :
    ((N : ℝ) - 3) / Real.log N ^ 2 ≤ Jn N 2 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hL : 0 < Real.log N := Real.log_pos hN1
  unfold Jn
  set A := (Ioc 1 N ×ˢ Ioc 1 N).filter (fun m : ℕ × ℕ => (m.1 : ℤ) - m.2 = 2) with hA
  have hsub : (Ioc 1 (N - 2)).image (fun m => (m + 2, m)) ⊆ A := by
    intro p hp
    simp only [mem_image, mem_Ioc] at hp
    obtain ⟨m, ⟨h1, h2⟩, rfl⟩ := hp
    simp only [hA, mem_filter, mem_product, mem_Ioc]
    refine ⟨⟨⟨by omega, by omega⟩, ⟨h1, by omega⟩⟩, ?_⟩
    push_cast; ring
  have hcard : ((Ioc 1 (N - 2)).image (fun m => (m + 2, m))).card = N - 3 := by
    rw [card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.snd h)]
    simp; omega
  have hterm : ∀ m ∈ A, 1 / Real.log N ^ 2 ≤ 1 / (Real.log m.1 * Real.log m.2) := by
    intro m hm
    simp only [hA, mem_filter, mem_product, mem_Ioc] at hm
    obtain ⟨⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩, -⟩ := hm
    have ha : (1 : ℝ) < m.1 := by exact_mod_cast a1
    have hb : (1 : ℝ) < m.2 := by exact_mod_cast b1
    have la := Real.log_pos ha
    have lb := Real.log_pos hb
    have la' : Real.log m.1 ≤ Real.log N :=
      Real.log_le_log (by linarith) (by exact_mod_cast a2)
    have lb' : Real.log m.2 ≤ Real.log N :=
      Real.log_le_log (by linarith) (by exact_mod_cast b2)
    apply one_div_le_one_div_of_le (mul_pos la lb)
    rw [sq]
    exact mul_le_mul la' lb' lb.le hL.le
  have h1 : ((A.card : ℕ) : ℝ) * (1 / Real.log N ^ 2) ≤
      ∑ m ∈ A, 1 / (Real.log m.1 * Real.log m.2) := by
    have := Finset.card_nsmul_le_sum A _ _ hterm
    rwa [nsmul_eq_mul] at this
  have h2 : ((N : ℝ) - 3) ≤ (A.card : ℝ) := by
    have := card_le_card hsub
    rw [hcard] at this
    have h3 : ((N - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by
      rw [Nat.cast_sub hN]; push_cast; ring
    rw [← h3]; exact_mod_cast this
  calc ((N : ℝ) - 3) / Real.log N ^ 2 = ((N : ℝ) - 3) * (1 / Real.log N ^ 2) := by ring
    _ ≤ (A.card : ℝ) * (1 / Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ _ := h1

/-- The normalized energy of Gallagher 1975 p.131 display 14 is nonnegative. -/
theorem normalizedEnergy_nonneg (N : ℕ) (θ : ℝ) (r : ℕ) (γ : ℝ) :
    0 ≤ normalizedEnergy N θ r γ := by
  unfold normalizedEnergy correctedEnergy
  apply div_nonneg
  · exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => Real.sqrt_nonneg _
  · rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast h)
      positivity

/-- `log P / P ≤ 2 / sqrt P` for `P > 0`. -/
theorem log_div_le_two_div_sqrt {P : ℝ} (hP : 0 < P) :
    Real.log P / P ≤ 2 / Real.sqrt P := by
  have hs : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hsq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP.le
  have hlog : Real.log P = 2 * Real.log (Real.sqrt P) := by
    rw [← Real.log_rpow hs, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      sq, hsq]
  have hle : Real.log (Real.sqrt P) ≤ Real.sqrt P := by
    have := Real.log_le_sub_one_of_pos hs; linarith
  rw [div_le_div_iff₀ hP hs, hlog]
  calc 2 * Real.log (Real.sqrt P) * Real.sqrt P ≤ 2 * Real.sqrt P * Real.sqrt P := by
        apply mul_le_mul_of_nonneg_right _ hs.le; linarith
    _ = 2 * P := by rw [mul_assoc, hsq]

/-- QUESTION, made precise. The main series leaf of `SPLIT_major_arc_energy_zero.lean`,
statement copied byte for byte, is refuted by the two inputs `hS` and `hgap` of the file
header. CONDITIONAL ON those two inputs; the leaf itself is not assumed. -/
theorem not_leaf_main_series_part_bound
    (hS : 1 ≤ ‖singSeries 2‖)
    (hgap : ∀ θ : ℝ, 0 < θ → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
        ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ) :
    ¬ (∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 →
          ‖(Jn N n : ℂ) * singSeries n‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0)) := by
  rintro ⟨K, θ₀, hK, hθ₀, -, hmain⟩
  obtain ⟨c, C, θ₁, hc, hC, hθ₁, -, hE⟩ := LeanLab.Linnik.Decomp486c.energy_decay_without_exception
  -- the target size of the energy term
  set δ : ℝ := 1 / (16 * K * (1 + C) * C + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]
    have : 0 ≤ 16 * K * (1 + C) * C := by positivity
    linarith
  have hlδ : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  set θ : ℝ := min (min θ₀ θ₁) (c / Real.log (1 / δ)) with hθdef
  have hθ : 0 < θ := lt_min (lt_min hθ₀ hθ₁) (div_pos hc hlδ)
  have hθ0 : θ ≤ θ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hθ1 : θ ≤ θ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hθc : θ ≤ c / Real.log (1 / δ) := min_le_right _ _
  have hexp : Real.exp (-c / θ) ≤ δ := by
    have h1 : Real.log (1 / δ) ≤ c / θ := by
      rw [le_div_iff₀ hθ]
      have := (le_div_iff₀ hlδ).mp hθc
      linarith
    have h2 : -c / θ ≤ Real.log δ := by
      rw [one_div, Real.log_inv] at h1
      rw [neg_div]; linarith
    calc Real.exp (-c / θ) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr h2
      _ = δ := Real.exp_log hδ0
  obtain ⟨N₁, hN₁⟩ := hmain θ hθ hθ0
  obtain ⟨N₂, hN₂⟩ := hE θ hθ hθ1
  -- a size of `N` making `log P / P` small
  set M : ℝ := 64 * K with hM
  set N₃ : ℕ := ⌈(M ^ 2) ^ (1 / θ)⌉₊ with hN₃
  obtain ⟨N, hN, hno⟩ := hgap θ hθ (max (max N₁ N₂) (max N₃ 5))
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN5 : 5 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNr : (5 : ℝ) ≤ N := by exact_mod_cast hN5
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  set P : ℝ := (N : ℝ) ^ θ with hPdef
  have hP0 : 0 < P := Real.rpow_pos_of_pos hN0 _
  have hPM : M ^ 2 ≤ P := by
    have h1 : (M ^ 2) ^ (1 / θ) ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN3)
    have h2 : ((M ^ 2) ^ (1 / θ)) ^ θ ≤ (N : ℝ) ^ θ :=
      Real.rpow_le_rpow (by positivity) h1 hθ.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ.ne', Real.rpow_one] at h2
  have hsP : M ≤ Real.sqrt P := by
    rw [show M = Real.sqrt (M ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hPM
  have hlogP : Real.log P / P ≤ 2 / M := by
    refine (log_div_le_two_div_sqrt hP0).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsP
  -- the energy term
  set E := normalizedEnergy N θ 0 0 with hEdef
  have hE0 : 0 ≤ E := normalizedEnergy_nonneg _ _ _ _
  have hEle : E ≤ C * δ := (hN₂ N hN2 hno).trans (mul_le_mul_of_nonneg_left hexp hC.le)
  have hEle1 : E ≤ C := hEle.trans (by nlinarith)
  have hEE : (1 + E) * E ≤ (1 + C) * C * δ := by
    calc (1 + E) * E ≤ (1 + C) * (C * δ) :=
          mul_le_mul (by linarith) hEle hE0 (by positivity)
      _ = _ := by ring
  have hKE : K * (2 * ((1 + C) * C * δ)) ≤ 1 / 8 := by
    have hden : 0 < 16 * K * (1 + C) * C + 2 := by positivity
    rw [hδ]
    rw [show K * (2 * ((1 + C) * C * (1 / (16 * K * (1 + C) * C + 2)))) =
      (2 * K * (1 + C) * C) / (16 * K * (1 + C) * C + 2) by field_simp]
    rw [div_le_iff₀ hden]
    nlinarith [show 0 ≤ K * (1 + C) * C by positivity]
  -- the arithmetic of `n = 2`
  have hdiv : (Int.natAbs (2 : ℤ)).divisors.card = 2 := by decide
  have htw : totientWeight (2 : ℤ) = 2 := by
    unfold totientWeight
    simp [Nat.totient_prime Nat.prime_two]
  have hbound := hN₁ N hN1 2 (by norm_num)
  rw [hdiv, htw] at hbound
  have hlhs : ((N : ℝ) - 3) / Real.log N ^ 2 ≤ ‖(Jn N 2 : ℂ) * singSeries 2‖ := by
    have hJ := Jn_two_lower N (by omega)
    have hJ0 : 0 ≤ Jn N 2 := le_trans (div_nonneg (by linarith) (by positivity)) hJ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hJ0]
    calc ((N : ℝ) - 3) / Real.log N ^ 2 ≤ Jn N 2 := hJ
      _ = Jn N 2 * 1 := (mul_one _).symm
      _ ≤ Jn N 2 * ‖singSeries 2‖ := mul_le_mul_of_nonneg_left hS hJ0
  have hrhs : K * ((N : ℝ) / Real.log N ^ 2) * 2 *
      (Real.log P / P * ((2 : ℕ) : ℝ) + (1 + E) * E) ≤
      ((N : ℝ) / Real.log N ^ 2) * (1 / 4) := by
    have hA : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
    have hlp : K * (2 * (Real.log P / P * 2)) ≤ 1 / 8 := by
      have : Real.log P / P * 2 ≤ 4 / M := by
        rw [show (4 : ℝ) / M = 2 / M * 2 by ring]; linarith
      calc K * (2 * (Real.log P / P * 2)) ≤ K * (2 * (4 / M)) := by
            apply mul_le_mul_of_nonneg_left _ hK.le; linarith
        _ = 1 / 8 := by rw [hM]; field_simp; ring
    have hsum : K * 2 * (Real.log P / P * ((2 : ℕ) : ℝ) + (1 + E) * E) ≤ 1 / 4 := by
      push_cast
      have h3 : K * (2 * ((1 + E) * E)) ≤ K * (2 * ((1 + C) * C * δ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK.le
      nlinarith
    calc K * ((N : ℝ) / Real.log N ^ 2) * 2 *
          (Real.log P / P * ((2 : ℕ) : ℝ) + (1 + E) * E)
        = ((N : ℝ) / Real.log N ^ 2) *
          (K * 2 * (Real.log P / P * ((2 : ℕ) : ℝ) + (1 + E) * E)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hA
  have hfin := hlhs.trans (hbound.trans hrhs)
  have hL2 : 0 < Real.log N ^ 2 := by positivity
  rw [div_le_iff₀ hL2, div_mul_eq_mul_div, mul_comm, ← mul_div_assoc, le_div_iff₀ hL2] at hfin
  nlinarith

/-- The arc integral leaf of `SPLIT_major_arc_energy_zero.lean`, statement copied byte for
byte, contradicts the parent conclusion of Gallagher 1975 p.127 Theorem 3 at conductor zero,
under the same two inputs: together with the parent conclusion it would give the main series
leaf by the triangle inequality. CONDITIONAL ON `hS`, `hgap` and the parent conclusion
`hparent`; neither leaf is assumed. -/
theorem not_leaf_arc_integral_part_bound_of_parent
    (hS : 1 ≤ ‖singSeries 2‖)
    (hgap : ∀ θ : ℝ, 0 < θ → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ¬ ∃ x ∈ excSet exceptionalStrip (((N : ℝ) ^ θ) ^ 5),
        ((x.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ θ)
    (hparent : ∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 → complexFrequencyError N θ n ≤
          K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
            (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
              (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0)) :
    ¬ (∃ K θ₀ : ℝ, 0 < K ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ n : ℤ, n ≠ 0 →
          ‖∫ α in majorArcs N ((N : ℝ) ^ θ),
              ((‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 : ℝ) : ℂ) *
                LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
            K * ((N : ℝ) / Real.log N ^ 2) * totientWeight n *
              (Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
                (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0)) := by
  rintro ⟨K₁, θ₁, hK₁, hθ₁, hθ₁', hz₁⟩
  obtain ⟨K₂, θ₂, hK₂, hθ₂, hθ₂', hz₂⟩ := hparent
  apply not_leaf_main_series_part_bound hS hgap
  refine ⟨K₁ + K₂, min θ₁ θ₂, by linarith, lt_min hθ₁ hθ₂,
    (min_le_left _ _).trans hθ₁', ?_⟩
  intro θ hθ hθm
  obtain ⟨N₁, hN₁⟩ := hz₁ θ hθ (hθm.trans (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := hz₂ θ hθ (hθm.trans (min_le_right _ _))
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN n hn
  have hI := hN₁ N ((le_max_left _ _).trans hN) n hn
  have hT := hN₂ N ((le_max_right _ _).trans hN) n hn
  unfold complexFrequencyError at hT
  set I := ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ((‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 : ℝ) : ℂ) *
        LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)
  set B := Real.log ((N : ℝ) ^ θ) / (N : ℝ) ^ θ * n.natAbs.divisors.card +
    (1 + normalizedEnergy N θ 0 0) * normalizedEnergy N θ 0 0
  have htri : ‖(Jn N n : ℂ) * singSeries n‖ ≤ ‖I‖ + ‖I - (Jn N n : ℂ) * singSeries n‖ := by
    have := norm_sub_le I (I - (Jn N n : ℂ) * singSeries n)
    rwa [sub_sub_cancel] at this
  calc ‖(Jn N n : ℂ) * singSeries n‖ ≤ ‖I‖ + ‖I - (Jn N n : ℂ) * singSeries n‖ := htri
    _ ≤ K₁ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n * B +
        K₂ * ((N : ℝ) / Real.log N ^ 2) * totientWeight n * B := add_le_add hI hT
    _ = (K₁ + K₂) * ((N : ℝ) / Real.log N ^ 2) * totientWeight n * B := by ring

end LeanLab.Linnik.Feed1122MajorArcZeroQuestion

#print axioms LeanLab.Linnik.Feed1122MajorArcZeroQuestion.not_leaf_main_series_part_bound
#print axioms LeanLab.Linnik.Feed1122MajorArcZeroQuestion.not_leaf_arc_integral_part_bound_of_parent
