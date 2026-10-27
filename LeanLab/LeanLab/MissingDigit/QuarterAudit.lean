import LeanLab.MissingDigit.UnboundedSeries
import LeanLab.MissingDigit.SparseDigits

/-!
Kim 2024 page 6 section 1.3, audit of the upper half of the main term display.
The ordinary series is unbounded even on a fixed missing digit set in
intervals with X equal to g to the 4r and H equal to g to the 3r.
The issue is a QUESTION in the lab ledger. It does not prove or disprove
Kim's almost all Goldbach conclusion. The minor arcs stay CONDITIONAL.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
namespace LeanLab.MissingDigit.KimSeries

open Finset
attribute [local instance] Classical.propDecidable

/-- The series is unbounded on quarter intervals in any fixed even base. -/
theorem exists_digit_series_gt {g b : ℕ} (hg : 3 ≤ g) (hge : Even g)
    (hb : 2 ≤ b) (C : ℝ) (T : ℕ) :
    ∃ r m : ℕ, T ≤ r ∧ 1 ≤ r ∧
      m ∈ (starSet g b (g ^ (4 * r)) ((g ^ (3 * r) : ℕ) : ℝ)).filter Even ∧
      C < series m := by
  let A := 2 * LeanLab.ChenExplicit.twinC
  have hA : 0 < A := mul_pos (by norm_num) LeanLab.ChenExplicit.twinC_pos
  obtain ⟨s, hs, hC⟩ := exists_prime_sum_gt_above g (max (C / A) 1)
  have hsne : s.Nonempty := by
    by_contra hn
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hempty, sum_empty] at hC
    have hmax : (1 : ℝ) ≤ max (C / A) 1 := le_max_right _ _
    linarith
  let M := ∏ p ∈ s, p
  have hMpos : 0 < M := Finset.prod_pos (fun p hp => (hs p hp).1.pos)
  have hM : 2 ≤ M := by
    obtain ⟨p, hp⟩ := hsne
    have hle : p ≤ M := Nat.le_of_dvd hMpos (Finset.dvd_prod_of_mem id hp)
    exact le_trans (hs p hp).1.two_le hle
  have hcop : Nat.Coprime g M := by
    apply Nat.Coprime.prod_right
    intro p hp
    apply Nat.Coprime.symm
    apply (hs p hp).1.coprime_iff_not_dvd.mpr
    intro hdiv
    have hle := Nat.le_of_dvd (show 0 < g by omega) hdiv
    have hgt := (hs p hp).2
    omega
  obtain ⟨r, m, hTr, hr, hmem, hdiv⟩ := digit_multiple_quarter hg hge hb hM hcop T
  have hm : 1 ≤ m := by
    have h := (Finset.mem_filter.mp hmem).1
    simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast] at h
    omega
  have he : Even m := (Finset.mem_filter.mp hmem).2
  have hsodd : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    exact ⟨(hs p hp).1, by have := (hs p hp).2; omega⟩
  have hF := oddFactor_ge_prime_sum s hsodd (by omega : m ≠ 0)
    (fun p hp => dvd_trans (Finset.dvd_prod_of_mem id hp) hdiv)
  have hmax : C / A ≤ max (C / A) 1 := le_max_left _ _
  have hFgt : C / A < oddFactor m := by linarith
  refine ⟨r, m, hTr, hr, hmem, ?_⟩
  rw [series_even_eq hm he]
  have h := (div_lt_iff₀ hA).mp hFgt
  change C < A * oddFactor m
  nlinarith

/-- These intervals satisfy Theorem 1.2's size conditions with epsilon equal to 1/24. -/
theorem quarter_interval_admissible {g r : ℕ} (hg : 1 ≤ g) :
    (((g ^ (4 * r) : ℕ) : ℝ) ^ ((2 : ℝ) / 3 + 1 / 24) ≤ (g ^ (3 * r) : ℕ)) ∧
    ((g ^ (3 * r) : ℕ) : ℝ) ≤ ((g ^ (4 * r) : ℕ) : ℝ) ^ (1 - (1 : ℝ) / 24) := by
  have hX : (1 : ℝ) ≤ ((g ^ (4 * r) : ℕ) : ℝ) := pow_ge_one_real hg
  have heq : ((g ^ (4 * r) : ℕ) : ℝ) ^ ((3 : ℝ) / 4) = ((g ^ (3 * r) : ℕ) : ℝ) := by
    calc
      ((g ^ (4 * r) : ℕ) : ℝ) ^ ((3 : ℝ) / 4) =
          ((g : ℝ) ^ (((4 * r : ℕ) : ℝ))) ^ ((3 : ℝ) / 4) := by
            simp only [Real.rpow_natCast, Nat.cast_pow]
      _ = (g : ℝ) ^ ((((4 * r : ℕ) : ℝ)) * ((3 : ℝ) / 4)) :=
        (Real.rpow_mul (Nat.cast_nonneg g) _ _).symm
      _ = (g : ℝ) ^ (((3 * r : ℕ) : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = ((g ^ (3 * r) : ℕ) : ℝ) := by simp only [Real.rpow_natCast, Nat.cast_pow]
  constructor
  · rw [← heq]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  · rw [← heq]
    exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

/-- Even with the fixed count, a uniform constant upper bound on the main term is false. -/
theorem not_uniform_fixed_mainTerm_upper {g b : ℕ} (hg : 3 ≤ g) (hge : Even g)
    (hb : 2 ≤ b) :
    ¬ ∃ (C : ℝ) (K₀ : ℕ), ∀ r : ℕ, K₀ ≤ r → ∀ m : ℕ,
      m ∈ (starSet g b (g ^ (4 * r)) ((g ^ (3 * r) : ℕ) : ℝ)).filter Even →
      (MstarFixed (g ^ (4 * r)) (g ^ (3 * r)) m : ℝ) * series m ≤
        C * (g ^ (3 * r) : ℕ) := by
  rintro ⟨C, K₀, hC⟩
  obtain ⟨r, m, hTr, hr, hmem, hgt⟩ := exists_digit_series_gt hg hge hb C K₀
  have hbounds := (Finset.mem_filter.mp hmem).1
  simp only [starSet, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast] at hbounds
  have hHX : g ^ (3 * r) ≤ g ^ (4 * r) := Nat.pow_le_pow_right (by omega) (by omega)
  have h := hC r hTr m hmem
  rw [MstarFixed_eq hHX hbounds.1.1.le hbounds.1.2] at h
  have hH : (0 : ℝ) < (g ^ (3 * r) : ℕ) := by positivity
  have hbad := mul_lt_mul_of_pos_left hgt hH
  nlinarith

end LeanLab.MissingDigit.KimSeries
