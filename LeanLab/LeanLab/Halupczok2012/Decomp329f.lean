import LeanLab.Halupczok2012.Decomp329e

/-!
Packing fixed power windows for the uniform Wu input.
Source: Halupczok page 345 and Wu arXiv 0705.1652 page 5 Theorem 5.
Only a count at one fixed exponent is required as an explicit input.
The proof uses disjoint windows spaced by twice the initial power length.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329f

open Finset
open scoped Classical

set_option maxHeartbeats 2000000 in
/-- Halupczok page 345, uniform lengths from one fixed power window estimate.
The global fixed power count remains an explicit input. -/
theorem extend_fixed_power_count (good : ℕ → Prop) {θ c X0 : ℝ}
    (hθ : (1 / 2 : ℝ) ≤ θ) (hθ1 : θ ≤ 1) (hc : 0 < c)
    (hfixed : ∀ X : ℝ, X0 ≤ X → 2 ≤ X →
      c * X ^ θ / (Real.log X) ^ 2 ≤ (((kRange X (X ^ θ)).filter good).card : ℝ)) :
    ∀ X Y : ℝ, max X0 4 ≤ Y → X ^ θ ≤ Y → Y ≤ X →
      (c / 64) * Y / (Real.log Y) ^ 2 ≤ (((kRange X Y).filter good).card : ℝ) := by
  intro X Y hY0 hlow hYX
  have hY4 : (4 : ℝ) ≤ Y := (le_max_right _ _).trans hY0
  have hX0 : X0 ≤ X := ((le_max_left _ _).trans hY0).trans hYX
  have hX2 : (2 : ℝ) ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hYp : 0 < Y := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLY : 0 < Real.log Y := Real.log_pos (by linarith)
  let H : ℝ := X ^ θ
  have hHp : 0 < H := Real.rpow_pos_of_pos hXp _
  have hθ0 : 0 ≤ θ := by linarith
  have hlog := Real.log_le_log hHp hlow
  change Real.log (X ^ θ) ≤ Real.log Y at hlog
  rw [Real.log_rpow hXp] at hlog
  have hθlog := mul_le_mul_of_nonneg_right hθ hLX.le
  have hcompare : Real.log X ≤ 2 * Real.log Y := by linarith
  have hsq : (Real.log X) ^ 2 ≤ 4 * (Real.log Y) ^ 2 := by nlinarith
  by_cases hsmall : Y ≤ 2 * H
  · have hlocal := Decomp329e.count_transfer_near_power good hX2 hθ hc hlow hsmall
      (hfixed X hX0 hX2)
    apply le_trans _ hlocal
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith : c / 64 ≤ c / 8) hYp.le
  have hlarge : 2 * H ≤ Y := (not_le.mp hsmall).le
  let N : ℕ := ⌊Y / (2 * H)⌋₊
  have ht1 : 1 ≤ Y / (2 * H) := (one_le_div (by positivity)).mpr hlarge
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff _).mpr ht1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNupper : 2 * (N : ℝ) * H ≤ Y := by
    have hfloor : (N : ℝ) ≤ Y / (2 * H) := Nat.floor_le (by positivity)
    have h := (le_div_iff₀ (by positivity : 0 < 2 * H)).mp hfloor
    nlinarith
  have hNlower : Y ≤ 4 * (N : ℝ) * H := by
    have hfloor : Y / (2 * H) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hfloor' : Y / (2 * H) < 2 * (N : ℝ) := by linarith
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * H)).mp hfloor'
    nlinarith
  let Z : ℕ → ℝ := fun i => X + 2 * (i : ℝ) * H
  let S : ℕ → Finset ℕ := fun i => (kRange (Z i) ((Z i) ^ θ)).filter good
  have hZlo : ∀ i : ℕ, X ≤ Z i := by
    intro i
    dsimp [Z]
    have hnonneg : 0 ≤ 2 * (i : ℝ) * H := by positivity
    linarith
  have hZhi : ∀ i ∈ range N, Z i ≤ 2 * X := by
    intro i hi
    have hiN : i ≤ N := (mem_range.mp hi).le
    have hiNR : (i : ℝ) ≤ N := by exact_mod_cast hiN
    have hmul := mul_le_mul_of_nonneg_right hiNR hHp.le
    dsimp [Z]
    linarith
  have hHlo : ∀ i : ℕ, H ≤ (Z i) ^ θ := by
    intro i
    exact Real.rpow_le_rpow hXp.le (hZlo i) hθ0
  have hHhi : ∀ i ∈ range N, (Z i) ^ θ ≤ 2 * H := by
    intro i hi
    calc
      (Z i) ^ θ ≤ (2 * X) ^ θ := Real.rpow_le_rpow (hXp.le.trans (hZlo i)) (hZhi i hi) hθ0
      _ = (2 : ℝ) ^ θ * X ^ θ := Real.mul_rpow (by norm_num) hXp.le
      _ ≤ 2 * H := by
        apply mul_le_mul_of_nonneg_right _ hHp.le
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1
  have hLog : ∀ i ∈ range N, Real.log (Z i) ≤ 2 * Real.log X := by
    intro i hi
    have h := Real.log_le_log (hXp.trans_le (hZlo i)) (hZhi i hi)
    rw [Real.log_mul (by norm_num) hXp.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX2
    linarith
  have hScount : ∀ i ∈ range N, c * H / (4 * (Real.log X) ^ 2) ≤ ((S i).card : ℝ) := by
    intro i hi
    have hZi : 0 < Z i := hXp.trans_le (hZlo i)
    have hLZi : 0 < Real.log (Z i) := Real.log_pos (by linarith [hZlo i])
    have hsqZi : (Real.log (Z i)) ^ 2 ≤ 4 * (Real.log X) ^ 2 := by
      have h := hLog i hi
      nlinarith
    have hbound := hfixed (Z i) (hX0.trans (hZlo i)) (hX2.trans (hZlo i))
    apply le_trans _ hbound
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      (c * H) * (Real.log (Z i)) ^ 2
          ≤ (c * H) * (4 * (Real.log X) ^ 2) :=
            mul_le_mul_of_nonneg_left hsqZi (by positivity)
      _ ≤ (c * (Z i) ^ θ) * (4 * (Real.log X) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hHlo i) hc.le
  have hSsub : ∀ i ∈ range N, S i ⊆ (kRange X Y).filter good := by
    intro i hi p hp
    obtain ⟨hwindow, hgood⟩ := mem_filter.mp hp
    obtain ⟨hplo, hphi⟩ := (Fourier398.window_mem _ _ _).mp hwindow
    have hiN : i + 1 ≤ N := Nat.succ_le_iff.mpr (mem_range.mp hi)
    have hiNR : (i : ℝ) + 1 ≤ N := by exact_mod_cast hiN
    have hmul := mul_le_mul_of_nonneg_right hiNR hHp.le
    refine mem_filter.mpr ⟨(Fourier398.window_mem _ _ _).mpr ⟨(hZlo i).trans_lt hplo, ?_⟩, hgood⟩
    have hH := hHhi i hi
    dsimp [Z] at hphi
    linarith
  have hdisj : (↑(range N) : Set ℕ).PairwiseDisjoint S := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hwi := (Fourier398.window_mem _ _ _).mp (mem_filter.mp hpi).1
    have hwj := (Fourier398.window_mem _ _ _).mp (mem_filter.mp hpj).1
    have hHi := hHhi i hi
    have hHj := hHhi j hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hgap : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr hij
      have hmul := mul_le_mul_of_nonneg_right hgap hHp.le
      dsimp [Z] at hwi hwj
      linarith
    · have hgap : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_iff.mpr hji
      have hmul := mul_le_mul_of_nonneg_right hgap hHp.le
      dsimp [Z] at hwi hwj
      linarith
  have hsumcard : (∑ i ∈ range N, ((S i).card : ℝ)) ≤
      (((kRange X Y).filter good).card : ℝ) := by
    have he := Finset.card_biUnion hdisj
    have hsub : (range N).biUnion S ⊆ (kRange X Y).filter good := by
      intro p hp
      obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hp
      exact hSsub i hi hpi
    have hcard := Finset.card_le_card hsub
    rw [he] at hcard
    exact_mod_cast hcard
  have hsum : (N : ℝ) * (c * H / (4 * (Real.log X) ^ 2)) ≤
      (((kRange X Y).filter good).card : ℝ) := by
    calc
      _ = ∑ i ∈ range N, c * H / (4 * (Real.log X) ^ 2) := by simp
      _ ≤ ∑ i ∈ range N, ((S i).card : ℝ) := sum_le_sum hScount
      _ ≤ _ := hsumcard
  have hmass : c * Y / (16 * (Real.log X) ^ 2) ≤
      (N : ℝ) * (c * H / (4 * (Real.log X) ^ 2)) := by
    have hYbound := mul_le_mul_of_nonneg_left hNlower hc.le
    have hden : 0 < (Real.log X) ^ 2 := by positivity
    apply (div_le_iff₀ (by positivity : 0 < 16 * (Real.log X) ^ 2)).mpr
    calc
      c * Y ≤ 4 * (N : ℝ) * c * H := by nlinarith
      _ = (N : ℝ) * (c * H / (4 * (Real.log X) ^ 2)) * (16 * (Real.log X) ^ 2) := by
        field_simp
        ring
  have hlogs : (c / 64) * Y / (Real.log Y) ^ 2 ≤ c * Y / (16 * (Real.log X) ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      (c / 64 * Y) * (16 * (Real.log X) ^ 2)
          ≤ (c / 64 * Y) * (16 * (4 * (Real.log Y) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (c * Y) * (Real.log Y) ^ 2 := by ring
  exact hlogs.trans (hmass.trans hsum)

set_option maxHeartbeats 1000000 in
/-- Halupczok page 345, the exact Wu leaf conclusion from a strictly smaller fixed exponent input.
The restricted fixed power count is an explicit analytic hypothesis. -/
theorem wu_of_fixed_power_count
    (hfixed : ∃ c > 0, ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 2 ≤ X →
      c * X ^ (0.971 : ℝ) / (Real.log X) ^ 2 ≤
        (((kRange X (X ^ (0.971 : ℝ))).filter
          (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card : ℝ)) :
    ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
      c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ
        (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))
        (Classical.decPred _) (kRange X Y)).card := by
  obtain ⟨c, hc, X0, hcount⟩ := hfixed
  refine ⟨c / 64, by positivity, max X0 4, by positivity, ?_⟩
  intro X Y hY0 hlow hYX
  have h := extend_fixed_power_count
    (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))
    (by norm_num : (1 / 2 : ℝ) ≤ 0.971) (by norm_num : (0.971 : ℝ) ≤ 1)
    hc (by
      intro Z hZ0 hZ2
      have hz := hcount Z hZ0 hZ2
      rw [@Finset.filter_congr_decidable ℕ _ _ _ (Classical.decPred _)] at hz
      exact hz) X Y hY0 hlow hYX
  exact h

end LeanLab.Halupczok2012.Decomp329f
