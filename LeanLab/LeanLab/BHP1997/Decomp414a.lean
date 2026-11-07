/-
P0069, pages 12 to 15. Theorem 4 split along its four dominance cases.
The three distinct analytic cases are OPEN. The fourth is symmetry.
The exact dyadic_mean_value assembly is CONDITIONAL on the OPEN cases.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.Decomp414a
open Classical Complex Thm4 MeanSquareC165 DecompC165c

/-- Page 13, the dominance test immediately above Case 1.
For a nonzero value z, sigma is one half plus log norm z divided by log F.
At zero the tag is harmless because the product summand is zero. -/
noncomputable def dominanceFlag (Q F : ℝ) (z : ℂ) : Bool :=
  decide (Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F))

/-- Pages 13 to 15, the part of a finite set with two prescribed dominance tags. -/
noncomputable def casePart {α : Type*} (S : Finset α) (f g : α → Bool)
    (u v : Bool) : Finset α := S.filter (fun p => f p = u ∧ g p = v)

/-- Pages 13 to 15, finite sum partition into the four dominance cases.
LeanSearch and Loogle find Finset.sum_filter_add_sum_filter_not.
The Boolean normal form below is its twice-refined partition. -/
theorem sum_four_parts {α : Type*} (S : Finset α) (f g : α → Bool) (w : α → ℝ) :
    ∑ p ∈ S, w p =
      (∑ p ∈ casePart S f g true true, w p) +
      (∑ p ∈ casePart S f g false false, w p) +
      (∑ p ∈ casePart S f g true false, w p) +
      (∑ p ∈ casePart S f g false true, w p) := by
  simp only [casePart, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  cases hf : f p <;> cases hg : g p <;> simp [hf, hg]

/-- Page 15, Case 4 interchanges the two dominance coordinates. -/
theorem casePart_swap {α : Type*} (S : Finset α) (f g : α → Bool) (u v : Bool) :
    casePart S f g u v = casePart S g f v u := by
  ext p
  simp [casePart, and_comm]

/-- Page 13, local consistency of the two sides of the dominance test.
The nonzero values 1 and 4 give opposite tags at Q equal to 8 and F equal to 4. -/
theorem dominance_flag_instances :
    dominanceFlag 8 4 1 = false ∧ dominanceFlag 8 4 4 = true := by
  have hl : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [dominanceFlag, Thm4.c, hl]


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




/-- Page 12, the logarithmic energy bound can use log x uniformly for F at most x.
The exponent is made nonnegative. No divisor moment estimate is asserted here.
CONDITIONAL on the explicit EnergyLogBound input. -/
theorem energy_log_uniform (henergy : EnergyLogBound)
    (B c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ a : ℕ → ℂ, CoeffBound a B →
    ∀ x F : ℝ, 1 ≤ Real.log x → 2 ≤ F → F ≤ x →
      energy a c1 c2 F ≤ C * Real.log x ^ K := by
  obtain ⟨K0, C0, hC0, he⟩ := henergy B c1 c2 hc1 hc2
  let C := C0 * (1 + Real.log 2 ^ K0)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, |K0|, hC, abs_nonneg _, ?_⟩
  intro a ha x F hx hF hFx
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlF : Real.log 2 ≤ Real.log F := Real.log_le_log (by norm_num) hF
  have hlFx : Real.log F ≤ Real.log x := Real.log_le_log (by linarith) hFx
  have hlx : 0 < Real.log x := by linarith
  have hK : 1 ≤ Real.log x ^ |K0| := Real.one_le_rpow hx (abs_nonneg _)
  have hpow : Real.log F ^ K0 ≤ (1 + Real.log 2 ^ K0) * Real.log x ^ |K0| := by
    by_cases hK0 : 0 ≤ K0
    · have hh : Real.log F ^ K0 ≤ Real.log x ^ |K0| := by
        rw [abs_of_nonneg hK0]
        exact Real.rpow_le_rpow (by linarith) hlFx hK0
      have ht : 0 ≤ Real.log 2 ^ K0 := Real.rpow_nonneg hl2.le _
      nlinarith [Real.rpow_nonneg hlx.le |K0|]
    · have hh : Real.log F ^ K0 ≤ Real.log 2 ^ K0 :=
        Real.rpow_le_rpow_of_nonpos hl2 hlF (le_of_not_ge hK0)
      have ht : 0 ≤ Real.log 2 ^ K0 := Real.rpow_nonneg hl2.le _
      nlinarith
  exact (he a ha F hF).trans (by
    have hh := mul_le_mul_of_nonneg_left hpow hC0.le
    convert hh using 1 <;> dsimp [C] <;> ring)

/-- Page 12, a fixed quadratic upper bound for the norm gives only logarithmically many levels.
This uses the existing exact finite dyadic count. -/
theorem quadratic_level_count {C x : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x)
    (hlx : 1 ≤ Real.log x) :
    ((dyadicLevels 1 (C * x ^ 2)).card : ℝ) ≤
      ((Real.log C + 2) / Real.log 2 + 2) * Real.log x := by
  have hC0 : 0 < C := by linarith
  have hx0 : 0 < x := by linarith
  have hU : 1 ≤ C * x ^ 2 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hx)
  have h := dyadic_level_count_le (by norm_num : (0 : ℝ) < 1) hU
  have he : Real.log (C * x ^ 2) = Real.log C + 2 * Real.log x := by
    rw [Real.log_mul hC0.ne' (pow_pos hx0 2).ne', Real.log_pow]
    norm_num
  rw [Real.logb, Real.logb, Real.log_one, zero_div, sub_zero, he] at h
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hh : (Real.log C + 2 * Real.log x) / Real.log 2 + 2 ≤
      ((Real.log C + 2) / Real.log 2 + 2) * Real.log x := by
    apply (le_of_sub_nonneg _)
    have heq : ((Real.log C + 2) / Real.log 2 + 2) * Real.log x -
        ((Real.log C + 2 * Real.log x) / Real.log 2 + 2) =
        (Real.log C / Real.log 2 + 2) * (Real.log x - 1) := by ring
    rw [heq]
    positivity
  exact h.trans hh

/-- Page 12, one nonnegative logarithmic energy exponent controls both energies in 3.4. -/
theorem energy_cubic_log_bound {E C K L : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (he : E ≤ C * L ^ K) :
    E + 16 * E ^ 3 ≤ (C + 16 * C ^ 3) * L ^ (3 * K) := by
  have hL0 : 0 < L := by linarith
  have he1 : E ≤ C * L ^ (3 * K) := he.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hC)
  have he3 : E ^ 3 ≤ C ^ 3 * L ^ (3 * K) := by
    calc
      _ ≤ (C * L ^ K) ^ 3 := pow_le_pow_left₀ hE he 3
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
        congr 2
        norm_num
        ring
  nlinarith




/-- Pages 12 and 13, displays 3.11 and 3.12, summed on the dominant values.
The low character-time range uses the mean square estimate directly.
The other range uses the actual dyadic cells and their logarithmic count.
CONDITIONAL on the three explicit analytic premises. No cited sorry is called. -/
theorem dominant_square_moment (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B c1 c2 : ℝ, 0 < c1 → c1 < c2 →
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ x F T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a : ℕ → ℂ, CoeffBound a B →
    2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    (∀ p ∈ S, dominanceFlag ((q : ℝ) * T) F (dirPoly a c1 c2 F p.2 (half p.1)) = true) →
    (∑ p ∈ S, ‖dirPoly a c1 c2 F p.2 (half p.1)‖ ^ 2) ≤
      C * F * Real.log x ^ D := by
  intro B c1 c2 hc1 hc2
  obtain ⟨Cm, hCm, hm⟩ := hmean B c1 c2 hc1 hc2
  obtain ⟨Cl, hCl, hcell⟩ := dominant_dyadic_square_bound hlarge B c1 c2 hc1 hc2
  obtain ⟨Ce, K, hCe, hK, he⟩ := energy_log_uniform henergy B c1 c2 hc1 hc2
  obtain ⟨Cn, hCn, hpoly⟩ := dirPoly_norm_uniform B c1 c2 hc1 (hc1.trans hc2)
  let J := (Real.log (Cn + 1) + 2) / Real.log 2 + 2
  have hJ : 0 < J := by
    have hh : 0 ≤ Real.log (Cn + 1) := Real.log_nonneg (by linarith)
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    dsimp [J]
    positivity
  let C := 2 * Cm * Ce + 4 * Cl * J * (Ce + 16 * Ce ^ 3)
  let D := 3 * K + 3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, D, hC, by dsimp [D]; linarith, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes hdom
  have hx3 : 3 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [Real.log_three_gt_d9]
  have hlx0 : 0 < Real.log x := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hE : 0 ≤ energy a c1 c2 F := Finset.sum_nonneg (fun n hn => by positivity)
  have henergyF := he a ha x F hlx hF hFx
  have hClo : 2 * Cm * Ce ≤ C := by
    dsimp [C]
    have hh : 0 ≤ 4 * Cl * J * (Ce + 16 * Ce ^ 3) := by positivity
    linarith
  have hChi : 4 * Cl * J * (Ce + 16 * Ce ^ 3) ≤ C := by
    dsimp [C]
    have hh : 0 ≤ 2 * Cm * Ce := by positivity
    linarith
  by_cases hQ : (q : ℝ) * T ≤ F
  · have hs := hm x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
    have hpow : Real.log x * Real.log x ^ K ≤ Real.log x ^ D := by
      have heq : Real.log x * Real.log x ^ K = Real.log x ^ (1 + K) := by
        rw [Real.rpow_add hlx0, Real.rpow_one]
      rw [heq]
      exact Real.rpow_le_rpow_of_exponent_le hlx (by dsimp [D]; linarith)
    calc
      _ ≤ Cm * Real.log x * ((q : ℝ) * T + F) * energy a c1 c2 F := hs
      _ ≤ Cm * Real.log x * (2 * F) * (Ce * Real.log x ^ K) := by gcongr <;> linarith
      _ = (2 * Cm * Ce) * F * (Real.log x * Real.log x ^ K) := by ring
      _ ≤ C * F * Real.log x ^ D := mul_le_mul
        (mul_le_mul_of_nonneg_right hClo hF0) hpow (by positivity) (by positivity)
  have hQ' : F < (q : ℝ) * T := lt_of_not_ge hQ
  let f : (ℝ × DirichletCharacter ℂ q) → ℂ := fun p => dirPoly a c1 c2 F p.2 (half p.1)
  let U : ℝ := (Cn + 1) * x ^ 2
  have hvalues : ∀ p ∈ S, 1 ≤ ‖f p‖ ∧ ‖f p‖ ≤ U := by
    intro p hp
    have hfour := dominant_value_fourth (by linarith : 1 < F) hQ' (hdom p hp)
    have hn1 : 1 ≤ ‖f p‖ := by
      by_contra! hn
      have hh := pow_lt_pow_left₀ hn (norm_nonneg (f p)) (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at hh
      change (q : ℝ) * T ≤ ‖f p‖ ^ 4 at hfour
      linarith
    refine ⟨hn1, ?_⟩
    calc
      _ ≤ Cn * F ^ 2 := hpoly a ha F (by linarith) q p.2 p.1
      _ ≤ (Cn + 1) * x ^ 2 := mul_le_mul (by linarith) (pow_le_pow_left₀ hF0 hFx 2)
        (sq_nonneg _) (by linarith)
  have hcount : ((dyadicLevels 1 U).card : ℝ) ≤ J * Real.log x :=
    quadratic_level_count (by linarith) (by linarith) hlx
  have hEcube := energy_cubic_log_bound hE hCe.le hK hlx henergyF
  have hsum := square_sum_of_dyadic_cells S f hvalues
    (fun k hk => hcell x F T q S a ha hx hF hFx hT hTx hq hqx hQ' hspace htimes hdom k)
  have hlogeq : Real.log x ^ (3 * K) * Real.log x ^ 2 * Real.log x = Real.log x ^ D := by
    calc
      _ = Real.log x ^ (3 * K) * Real.log x ^ (2 : ℝ) * Real.log x ^ (1 : ℝ) := by simp
      _ = Real.log x ^ (3 * K + 2 + 1) := by rw [← Real.rpow_add hlx0, ← Real.rpow_add hlx0]
      _ = _ := by congr 1; dsimp [D]; ring
  calc
    _ ≤ (dyadicLevels 1 U).card *
        (4 * Cl * Real.log x ^ 2 * F * (energy a c1 c2 F + 16 * energy a c1 c2 F ^ 3)) := hsum
    _ ≤ (J * Real.log x) *
        (4 * Cl * Real.log x ^ 2 * F * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K))) :=
      mul_le_mul hcount (mul_le_mul_of_nonneg_left hEcube (by positivity)) (by positivity) (by positivity)
    _ = (4 * Cl * J * (Ce + 16 * Ce ^ 3)) * F *
        (Real.log x ^ (3 * K) * Real.log x ^ 2 * Real.log x) := by ring
    _ = (4 * Cl * J * (Ce + 16 * Ce ^ 3)) * F * Real.log x ^ D := by rw [hlogeq]
    _ ≤ C * F * Real.log x ^ D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hChi hF0) (by positivity)





/-- Page 13, Case 1. Cauchy Schwarz combines the two dominant square moments.
The explicit hypotheses are finite moment bounds, not cited theorems. -/
theorem pair_of_square_bounds {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {C M N L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hf : (∑ p ∈ S, ‖f p‖ ^ 2) ≤ C * M * L)
    (hg : (∑ p ∈ S, ‖g p‖ ^ 2) ≤ C * N * L) :
    (∑ p ∈ S, ‖f p * g p‖) ≤ C * Real.sqrt M * Real.sqrt N * L := by
  simp_rw [norm_mul]
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => ‖f p‖) (fun p => ‖g p‖)
  have hs := mul_le_mul hf hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg (mul_nonneg hC hM) hL)
  have he : (C * Real.sqrt M * Real.sqrt N * L) ^ 2 = (C * M * L) * (C * N * L) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hN]
    ring
  have hp : 0 ≤ C * Real.sqrt M * Real.sqrt N * L := by positivity
  nlinarith

/-- Page 13, Case 1. Extract the uniform third-factor bound from the finite sum. -/
theorem triple_of_pair_bound {ι : Type*} (S : Finset ι) (f g e : ι → ℂ)
    {H U : ℝ} (hU : 0 ≤ U)
    (hpair : (∑ p ∈ S, ‖f p * g p‖) ≤ H)
    (he : ∀ p ∈ S, ‖e p‖ ≤ U) :
    (∑ p ∈ S, ‖f p * g p * e p‖) ≤ H * U := by
  calc
    _ ≤ ∑ p ∈ S, ‖f p * g p‖ * U := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he p hp) (norm_nonneg _)
    _ = (∑ p ∈ S, ‖f p * g p‖) * U := (Finset.sum_mul ..).symm
    _ ≤ H * U := mul_le_mul_of_nonneg_right hpair hU






/-- Page 13, the Case 2 split at sigma3 equal to three quarters.
The small part consists of third-factor norms at most length to one quarter. -/
noncomputable def thirdNormPart {ι : Type*} (S : Finset ι) (f : ι → ℂ) (L : ℝ)
    (small : Bool) : Finset ι := S.filter (fun p => decide (‖f p‖ ≤ L ^ (1 / 4 : ℝ)) = small)

/-- Page 13, both third-factor branches partition the actual finite norm sum. -/
theorem sum_third_parts {ι : Type*} (S : Finset ι) (f : ι → ℂ) (L : ℝ) (w : ι → ℝ) :
    ∑ p ∈ S, w p = (∑ p ∈ thirdNormPart S f L true, w p) +
      ∑ p ∈ thirdNormPart S f L false, w p := by
  simpa [thirdNormPart] using
    (Finset.sum_filter_add_sum_filter_not S (fun p => ‖f p‖ ≤ L ^ (1 / 4 : ℝ)) w).symm

/-- Page 13, a value on the nondominant side forces the character-time scale above the length. -/
theorem nondominant_scale_lt {Q F : ℝ} (hF : 1 < F) {z : ℂ}
    (hz : dominanceFlag Q F z = false) : F < Q := by
  have hh : ¬Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) := of_decide_eq_false hz
  rw [dominance_power_eq_max hF] at hh
  exact lt_of_not_ge (fun h => hh (h.trans (le_max_left _ _)))

/-- Page 13, the Case 2 power saving absorbs a fixed positive logarithmic loss.
The large base X is allowed to exceed x, as in the paper's two choices of X. -/
theorem power_saving_with_log {x X A δ k : ℝ} (hx : 1 < x) (hX : x ≤ X)
    (hA : 0 < A) (hδ : 0 < δ) (hk : 0 ≤ k) :
    X ^ (1 / 2 - δ) * Real.log x ^ k ≤
      (δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  have hA' : 0 < A + k := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlX : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hX
  have hsave := power_saving_to_log_saving (x := X) (β := 1 / 2)
    (lt_of_lt_of_le hx hX) hA' hδ
  have hlog : Real.log X ^ (-(A + k)) ≤ Real.log x ^ (-(A + k)) :=
    Real.rpow_le_rpow_of_nonpos hlx hlX (by linarith)
  have hconst : 0 ≤ (δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ ((δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log X ^ (-(A + k))) *
        Real.log x ^ k := mul_le_mul_of_nonneg_right hsave (Real.rpow_nonneg hlx.le _)
    _ ≤ ((δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + k))) *
        Real.log x ^ k := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hconst) (Real.rpow_nonneg hlx.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hlx]
      congr 2
      ring

/-- LEAF. Page 13, Case 2 i. The two mean squares control the pair,
while the third norm is at most its length to one quarter.
CONDITIONAL on the original three inputs. -/
theorem neither_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)  := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  let H := 2 * Cm * Ce
  let R := ((ε / 4) / (A + (K0 + 1))) ^ (-(A + (K0 + 1)))
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨H * R, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
  let M := X ^ α₁
  let N := X ^ α₂
  let L := X ^ (1 - α₁ - α₂)
  let Q : ℝ := (q : ℝ) * T
  let P := thirdNormPart (casePart S
    (fun p => dominanceFlag Q M (dirPoly a c₁ c₂ M p.2 (half p.1)))
    (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) false false)
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1)) L true
  have hsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hx3 : 3 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [Real.log_three_gt_d9]
  have hlx0 : 0 < Real.log x := by linarith
  have hXge : x ≤ X := by
    rcases hX with rfl | rfl
    · exact le_rfl
    · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
      calc
        x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hlog0 : 0 ≤ Real.log x ^ (K0 + 1) := Real.rpow_nonneg hlx0.le _
  by_cases hEmpty : P = ∅
  · change (∑ p ∈ P, _) ≤ _
    rw [hEmpty, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hMQ : M < Q := nondominant_scale_lt (by dsimp [M]; linarith) hcase.1
  have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hmoment (f : ℕ → ℂ) (F : ℝ) (hf : CoeffBound f B)
      (hF : 2 ≤ F) (hFx : F ≤ x) (hFQ : F ≤ Q) :
      (∑ p ∈ P, ‖dirPoly f c₁ c₂ F p.2 (half p.1)‖ ^ 2) ≤ H * Q * Real.log x ^ (K0 + 1) := by
    have hmF := hm x F T q P f hf hx hF hFx hT hTx hq hqx hsp htime
    have heF := he f hf x F hlx hF hFx
    have hEnonneg : 0 ≤ energy f c₁ c₂ F := Finset.sum_nonneg (fun n hn => by positivity)
    calc
      _ ≤ Cm * Real.log x * (Q + F) * energy f c₁ c₂ F := hmF
      _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
      _ = H * Q * (Real.log x ^ K0 * Real.log x) := by dsimp [H]; ring
      _ = _ := by rw [Real.rpow_add hlx0, Real.rpow_one]
  have hpair := pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le hQ0 hQ0 hlog0
    (hmoment a M ha hM hMx hMQ.le) (hmoment b N hb hN hNx hNQ.le)
  have hpair' : (∑ p ∈ P,
      ‖dirPoly a c₁ c₂ M p.2 (half p.1) * dirPoly b c₁ c₂ N p.2 (half p.1)‖) ≤
      H * Q * Real.log x ^ (K0 + 1) := by
    apply hpair.trans_eq
    calc
      _ = H * (Real.sqrt Q * Real.sqrt Q) * Real.log x ^ (K0 + 1) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hQ0]
  have htriple := triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
    (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
  have hpow : Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
    rw [show Q = X ^ (1 - θ) from hqT]
    dsimp [L]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have hh := case2i_margin hgam
    linarith
  have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
    (by linarith : 0 < ε / 4) (by linarith : 0 ≤ K0 + 1)
  calc
    _ ≤ (H * Q * Real.log x ^ (K0 + 1)) * L ^ (1 / 4 : ℝ) := htriple
    _ = H * (Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ (K0 + 1) := by ring
    _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ (K0 + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
    _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ (K0 + 1)) := by ring
    _ ≤ H * (R * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_left hsave hH.le
    _ = _ := by ring

/-- LEAF. Page 13, Case 2 ii, display 3.13 and the two following bounds.
Only the part above the third norm threshold remains. Apply the sixth
polynomial power bound and its two interpolation weights. OPEN.
CONDITIONAL on the original three inputs. -/
theorem neither_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry






/-- LEAF. Page 14, Case 3 i, display 3.14.
The third factor has norm at most its length to one quarter.
CONDITIONAL on the original three inputs. -/
theorem first_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  obtain ⟨Cd, Dd, hCd, hDd, hd⟩ := dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
  let D0 := max Dd (K0 + 1)
  have hD0 : 0 ≤ D0 := hDd.trans (le_max_left _ _)
  let H := Cd + 2 * Cm * Ce
  let R := ((ε / 4) / (A + D0)) ^ (-(A + D0))
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨H * R, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
  let M := X ^ α₁
  let N := X ^ α₂
  let L := X ^ (1 - α₁ - α₂)
  let Q : ℝ := (q : ℝ) * T
  let P := thirdNormPart (casePart S
    (fun p => dominanceFlag Q M (dirPoly a c₁ c₂ M p.2 (half p.1)))
    (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) true false)
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1)) L true
  have hsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hx3 : 3 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [Real.log_three_gt_d9]
  have hlx0 : 0 < Real.log x := by linarith
  have hXge : x ≤ X := by
    rcases hX with rfl | rfl
    · exact le_rfl
    · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
      calc
        x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hlog0 : 0 ≤ Real.log x ^ D0 := Real.rpow_nonneg hlx0.le _
  by_cases hEmpty : P = ∅
  · change (∑ p ∈ P, _) ≤ _
    rw [hEmpty, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hHc : Cd ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 2 * Cm * Ce := by positivity
    linarith
  have hHm : 2 * Cm * Ce ≤ H := by dsimp [H]; linarith
  have hlogd : Real.log x ^ Dd ≤ Real.log x ^ D0 :=
    Real.rpow_le_rpow_of_exponent_le hlx (le_max_left _ _)
  have hlogk : Real.log x ^ (K0 + 1) ≤ Real.log x ^ D0 :=
    Real.rpow_le_rpow_of_exponent_le hlx (le_max_right _ _)
  have hmomentM : (∑ p ∈ P, ‖dirPoly a c₁ c₂ M p.2 (half p.1)‖ ^ 2) ≤
      H * M * Real.log x ^ D0 := by
    have hh := hd x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
      (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1)
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hHc (by dsimp [M]; positivity))
      hlogd (by positivity) (by dsimp [M]; positivity))
  have hmomentN : (∑ p ∈ P, ‖dirPoly b c₁ c₂ N p.2 (half p.1)‖ ^ 2) ≤
      H * Q * Real.log x ^ D0 := by
    have hmF := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
    have heF := he b hb x N hlx hN hNx
    have hEnonneg : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
    calc
      _ ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hmF
      _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
      _ = (2 * Cm * Ce) * Q * (Real.log x ^ K0 * Real.log x) := by ring
      _ = (2 * Cm * Ce) * Q * Real.log x ^ (K0 + 1) := by rw [Real.rpow_add hlx0, Real.rpow_one]
      _ ≤ H * Q * Real.log x ^ D0 := mul_le_mul
        (mul_le_mul_of_nonneg_right hHm hQ0) hlogk (by positivity) (by positivity)
  have hpair' := pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le
    (by dsimp [M]; positivity) hQ0 (Real.rpow_nonneg hlx0.le D0) hmomentM hmomentN
  have htriple := triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
    (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
  have hpow : Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, show Q = X ^ (1 - θ) from hqT]
    dsimp [M, L]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
      ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have hab' := (abs_lt.mp hab).2
    linarith
  have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
    (by linarith : 0 < ε / 4) hD0
  calc
    _ ≤ (H * Real.sqrt M * Real.sqrt Q * Real.log x ^ D0) * L ^ (1 / 4 : ℝ) := htriple
    _ = H * (Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ D0 := by ring
    _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ D0 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
    _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ D0) := by ring
    _ ≤ H * (R * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_left hsave hH.le
    _ = _ := by ring

/-- LEAF. Page 14, Case 3 ii, displays 3.15 and 3.16.
Only the part above the third norm threshold remains. The bounded choice
of polynomial power and its level-set summation remain OPEN.
Retain the existing proved repair for the g equal to one branch.
CONDITIONAL on the original three inputs. -/
theorem first_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry







/-- LEAF. Page 13, Case 1, displays 3.11 and 3.12, followed by 3.2.
Dyadically sum only the part where both first terms dominate.
This uses the logarithmic energy bound, not a positive power substitute.
OPEN. CONDITIONAL on the three explicit analytic inputs. -/
theorem both_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C, D, hC, hD, hm⟩ := dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
  let A' := A + D
  have hA' : 0 < A' := by dsimp [A']; linarith
  refine ⟨C * |K A'|, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  let M := X ^ α₁
  let N := X ^ α₂
  let L := X ^ (1 - α₁ - α₂)
  let P := casePart S
    (fun p => dominanceFlag ((q : ℝ) * T) M (dirPoly a c₁ c₂ M p.2 (half p.1)))
    (fun p => dominanceFlag ((q : ℝ) * T) N (dirPoly b c₁ c₂ N p.2 (half p.1))) true true
  have hsub : P ⊆ S := Finset.filter_subset _ _
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hma := hm x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
    (by intro p hp; exact (Finset.mem_filter.mp hp).2.1)
  have hmb := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
    (by intro p hp; exact (Finset.mem_filter.mp hp).2.2)
  have hMN := pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hC.le
    (by dsimp [M]; positivity) (by dsimp [N]; positivity)
    (Real.rpow_nonneg (Real.log_nonneg (by linarith)) D) hma hmb
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hthird : ∀ p ∈ P, ‖dirPoly e c₁ c₂ L p.2 (half p.1)‖ ≤
      |K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
    intro p hp
    exact (hsmall A' hA' p (hsub hp)).trans (by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have htriple := triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by positivity : 0 ≤ |K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) hMN hthird
  have hXpos : 0 < X := by
    rcases hX with rfl | rfl
    · linarith
    · positivity
  have hsqrt : Real.sqrt M * Real.sqrt N * L ^ (1 / 2 : ℝ) = X ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    dsimp [M, N, L]
    rw [← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le,
      ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    congr 1
    ring
  have hlog : Real.log x ^ D * Real.log x ^ (-A') = Real.log x ^ (-A) := by
    rw [← Real.rpow_add (Real.log_pos (by linarith : 1 < x))]
    congr 1
    dsimp [A']
    ring
  calc
    _ ≤ (C * Real.sqrt M * Real.sqrt N * Real.log x ^ D) *
        (|K A'| * L ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) := htriple
    _ = C * |K A'| * (Real.sqrt M * Real.sqrt N * L ^ (1 / 2 : ℝ)) *
        (Real.log x ^ D * Real.log x ^ (-A')) := by ring
    _ = _ := by rw [hsqrt, hlog]



/-- LEAF. Page 13, Case 2 i and ii, displays 3.10 to 3.13.
Dyadically sum only the part where neither first term dominates.
The three branches of gamma provide the power savings.
OPEN. CONDITIONAL on the three explicit analytic inputs. -/
theorem neither_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := neither_small_third hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := neither_large_third hmean hlarge henergy B
  refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_third_parts _ (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
    (X ^ (1 - α₁ - α₂))]
  exact (add_le_add hs0 hs1).trans_eq (by ring)



/-- LEAF. Page 14, Case 3 i and ii, displays 3.14 to 3.16.
Dyadically sum only the part where the first polynomial dominates.
Use the repaired g equal to one branch already proved in DecompC165c.
The bounded power selection and the remaining summation are retained here.
OPEN. CONDITIONAL on the three explicit analytic inputs. -/
theorem first_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := first_small_third hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := first_large_third hmean hlarge henergy B
  refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_third_parts _ (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
    (X ^ (1 - α₁ - α₂))]
  exact (add_le_add hs0 hs1).trans_eq (by ring)


/-- Page 15, Case 4 follows from Case 3 by interchanging M and N.
CONDITIONAL on first_dominant and its three explicit analytic inputs. -/
theorem second_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η, hη, hcase⟩ := first_dominant hmean hlarge henergy B
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C, hC⟩ := hcase ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have h := hC θ α₂ α₁ x X T q S b a e hθ hθu
    (by simpa only [abs_sub_comm] using hab) (by convert hgam using 1 <;> ring)
    hx hX hq hqx hT hTx hqT hN hNx hM hMx
    (by convert hL using 1 <;> congr 1 <;> ring)
    (by convert hLx using 1 <;> congr 1 <;> ring)
    hspace htimes hb ha he (by convert hsmall using 1 <;> congr 1 <;> ring)
  convert h using 1
  · rw [casePart_swap]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    congr 1
    · ring
    · congr 2
      ring

/-- Pages 12 to 15, exact original dyadic_mean_value statement assembled
from the four smaller dominance parts. No direct sorry.
CONDITIONAL on the three OPEN cases and the original analytic inputs. -/
theorem dyadic_mean_value (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) : Thm4.Theorem4Paper := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := both_dominant hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := neither_dominant hmean hlarge henergy B
  obtain ⟨η2, hη2, h2⟩ := first_dominant hmean hlarge henergy B
  obtain ⟨η3, hη3, h3⟩ := second_dominant hmean hlarge henergy B
  refine ⟨min η0 (min η1 (min η2 η3)), by positivity, ?_⟩
  intro ε hε hεη
  have he0 : ε < η0 := lt_of_lt_of_le hεη (min_le_left _ _)
  have he1 : ε < η1 := lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_left _ _))
  have he2 : ε < η2 := lt_of_lt_of_le hεη
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he3 : ε < η3 := lt_of_lt_of_le hεη
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  intro c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε he0 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε he1 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C2, hc2⟩ := h2 ε hε he2 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C3, hc3⟩ := h3 ε hε he3 c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1 + C2 + C3, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb2 := hc2 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb3 := hc3 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_four_parts S
    (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
    (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1)))]
  calc
    _ ≤ C0 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C3 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
      add_le_add (add_le_add (add_le_add hb0 hb1) hb2) hb3
    _ = _ := by ring

end LeanLab.BHP1997.Decomp414a
