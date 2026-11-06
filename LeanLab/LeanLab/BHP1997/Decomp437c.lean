/-
P0069, pages 12 and 13, dominance after displays 3.11 and 3.12.
These finite and algebraic steps use the named analytic inputs explicitly.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp414a

namespace LeanLab.BHP1997.Decomp437c
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a
open scoped BigOperators

/-- Page 13, the dominance threshold written directly in terms of the norm.
The power F to c of sigma is the maximum of F and the fourth power of the norm. -/
theorem dominance_power_eq_max {F : ℝ} (hF : 1 < F) (z : ℂ) :
    F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) = max F (‖z‖ ^ 4) := by
  have hF0 : 0 < F := by linarith
  have hlF : Real.log F ≠ 0 := ne_of_gt (Real.log_pos hF)
  by_cases hz : ‖z‖ = 0
  · norm_num [hz, Thm4.c, max_eq_left hF0.le]
  have hz0 : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  let σ : ℝ := 1 / 2 + Real.log ‖z‖ / Real.log F
  have he : F ^ (4 * σ - 2) = ‖z‖ ^ 4 := by
    rw [Real.rpow_def_of_pos hF0]
    have hh : Real.log F * (4 * σ - 2) = Real.log ‖z‖ * 4 := by
      dsimp [σ]
      field_simp [hlF]
      ring
    rw [hh, Real.exp_mul, Real.exp_log hz0]
    norm_num
  by_cases hσ : σ ≤ 3 / 4
  · have hv : ‖z‖ ^ 4 ≤ F := by
      rw [← he]
      exact (Real.rpow_le_rpow_of_exponent_le hF.le (by linarith : 4 * σ - 2 ≤ 1)).trans_eq
        (Real.rpow_one F)
    change F ^ Thm4.c σ = _
    rw [Thm4.c, if_pos hσ, Real.rpow_one, max_eq_left hv]
  · have hv : F ≤ ‖z‖ ^ 4 := by
      calc
        F = F ^ (1 : ℝ) := (Real.rpow_one F).symm
        _ ≤ F ^ (4 * σ - 2) := Real.rpow_le_rpow_of_exponent_le hF.le (by linarith)
        _ = _ := he
    change F ^ Thm4.c σ = _
    rw [Thm4.c, if_neg hσ, he, max_eq_right hv]

/-- Page 13, a dominant value above the character-time scale has fourth power at least qT. -/
theorem dominant_value_fourth {Q F : ℝ} (hF : 1 < F) (hQ : F < Q) {z : ℂ}
    (hz : dominanceFlag Q F z = true) : Q ≤ ‖z‖ ^ 4 := by
  have hh : Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) := of_decide_eq_true hz
  rw [dominance_power_eq_max hF] at hh
  exact (le_max_iff.mp hh).resolve_left (not_le.mpr hQ)

/-- Page 12, the one-polynomial version of the finite dyadic partition.
Summing a uniform square-moment bound over the actual norm levels costs
only the number of levels. -/
theorem square_sum_of_dyadic_cells {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    {U H : ℝ} (hU : ∀ p ∈ S, 1 ≤ ‖f p‖ ∧ ‖f p‖ ≤ U)
    (hc : ∀ k ∈ dyadicLevels 1 U,
      (∑ p ∈ S.filter (fun p => Int.log 2 ‖f p‖ = k), ‖f p‖ ^ 2) ≤ H) :
    (∑ p ∈ S, ‖f p‖ ^ 2) ≤ (dyadicLevels 1 U).card * H := by
  have he : (∑ k ∈ dyadicLevels 1 U,
      ∑ p ∈ S.filter (fun p => Int.log 2 ‖f p‖ = k), ‖f p‖ ^ 2) =
      ∑ p ∈ S, ‖f p‖ ^ 2 := by
    apply Finset.sum_fiberwise_of_maps_to
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Int.log_mono_right (by norm_num : (0 : ℝ) < 1) (hU p hp).1,
      Int.log_mono_right (by linarith [(hU p hp).1]) (hU p hp).2⟩
  rw [← he]
  exact (Finset.sum_le_sum hc).trans_eq (by simp)

/-- Page 13, displays 3.11 and 3.12. Within a dyadic cell, the large-value
estimate and Q at most sixteen V to the fourth give a uniform square sum.
The energy and the cited cardinality estimate are explicit scalar inputs. -/
theorem square_sum_of_cardinal_bound {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    {C L E F Q V : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hV : 0 < V) (hQ : Q ≤ 16 * V ^ 4)
    (hpoint : ∀ p ∈ S, ‖f p‖ ≤ 2 * V)
    (hcard : (S.card : ℝ) ≤ C * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6)) :
    (∑ p ∈ S, ‖f p‖ ^ 2) ≤ 4 * C * L ^ 2 * F * (E + 16 * E ^ 3) := by
  have hsum : (∑ p ∈ S, ‖f p‖ ^ 2) ≤ (S.card : ℝ) * (4 * V ^ 2) := by
    calc
      _ ≤ ∑ _p ∈ S, (2 * V) ^ 2 := Finset.sum_le_sum
        (fun p hp => pow_le_pow_left₀ (norm_nonneg _) (hpoint p hp) 2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard' := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 4 * V ^ 2)
  have heq : C * L ^ 2 * (E * F / V ^ 2 + E ^ 3 * F * Q / V ^ 6) * (4 * V ^ 2) =
      4 * C * L ^ 2 * F * (E + E ^ 3 * Q / V ^ 4) := by
    field_simp [hV.ne']
    <;> ring
  rw [heq] at hcard'
  apply hsum.trans (hcard'.trans _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hq : Q / V ^ 4 ≤ 16 := (div_le_iff₀ (by positivity)).mpr hQ
  have hh := mul_le_mul_of_nonneg_left hq (pow_nonneg hE 3)
  have he : E ^ 3 * Q / V ^ 4 = E ^ 3 * (Q / V ^ 4) := by ring
  rw [he]
  linarith

/-- Pages 12 and 13, displays 3.4 and 3.11 applied to one actual dominant cell.
Only the large-value input is used. The coefficient energy remains explicit.
CONDITIONAL on Lemma1LargeValues. -/
theorem dominant_dyadic_square_bound (hlarge : Lemma1LargeValues)
    (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x F T : ℝ, ∀ q : ℕ,
    ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
    CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 →
    1 ≤ q → (q : ℝ) ≤ x → F < (q : ℝ) * T →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
    ∀ k : ℤ,
      (∑ p ∈ S.filter (fun p => Int.log 2 ‖dirPoly a c1 c2 F p.2 (half p.1)‖ = k),
        ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
      4 * C * Real.log x ^ 2 * F * (energy a c1 c2 F + 16 * energy a c1 c2 F ^ 3) := by
  obtain ⟨C, hC, hc⟩ := hlarge B c1 c2 hc1 hc2
  refine ⟨C, hC, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hQ hspace htimes hdom k
  let f : (ℝ × DirichletCharacter ℂ q) → ℂ := fun p => dirPoly a c1 c2 F p.2 (half p.1)
  let P := S.filter (fun p => Int.log 2 ‖f p‖ = k)
  let V : ℝ := (2 : ℝ) ^ k
  have hV : 0 < V := by dsimp [V]; positivity
  have hE : 0 ≤ energy a c1 c2 F := Finset.sum_nonneg (fun n hn => by positivity)
  have hsub : P ⊆ S := Finset.filter_subset _ _
  have hfourth (p) (hp : p ∈ P) : (q : ℝ) * T ≤ ‖f p‖ ^ 4 :=
    dominant_value_fourth (by linarith) hQ (hdom p (hsub hp))
  have hpos (p) (hp : p ∈ P) : 0 < ‖f p‖ := by
    by_contra! hh
    have hz : ‖f p‖ = 0 := le_antisymm hh (norm_nonneg _)
    have hfour := hfourth p hp
    rw [hz] at hfour
    norm_num at hfour
    linarith
  have hlevels (p) (hp : p ∈ P) : V ≤ ‖f p‖ ∧ ‖f p‖ < 2 * V := by
    have he := (Finset.mem_filter.mp hp).2
    have hlo := Int.zpow_log_le_self (by norm_num : 1 < (2 : ℕ)) (hpos p hp)
    have hhi := Int.lt_zpow_succ_log_self (R := ℝ) (by norm_num : 1 < 2) ‖f p‖
    rw [he] at hlo hhi
    exact ⟨hlo, by simpa only [V, Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hhi⟩
  by_cases hempty : P = ∅
  · change (∑ p ∈ P, ‖f p‖ ^ 2) ≤ _
    rw [hempty, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hQcell : (q : ℝ) * T ≤ 16 * V ^ 4 := by
    calc
      _ ≤ ‖f p‖ ^ 4 := hfourth p hp
      _ ≤ (2 * V) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (hlevels p hp).2.le 4
      _ = _ := by ring
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have hcard := hc x F T V q P a ha hx hF hFx hT hTx hq hqx hV hsp
    (fun p hp => htimes p (hsub hp)) (fun p hp => (hlevels p hp).1)
  exact square_sum_of_cardinal_bound P f hC.le (Real.log_nonneg (by linarith)) hE
    (by linarith) hV hQcell (fun p hp => (hlevels p hp).2.le) (by simpa only [mul_assoc] using hcard)

end LeanLab.BHP1997.Decomp437c
