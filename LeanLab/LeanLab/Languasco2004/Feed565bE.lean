/-
Jia 1996 pages 267 to 269 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Feed565bC.pair_prime_sum_lower_rest, burst-20261122, session S140.
The unselected group five pair domain contains the product domain
Y^(89/462) < p at most Y^(17/54), Y^(16/135) < q < p^(-29/48) Y^(89/288),
and on that domain the reciprocal pair sum tends to the integral behind mainRest.
Analytic leaves stay OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Source565
import LeanLab.Languasco2004.Numeric565
import LeanLab.Languasco2004.Decomp588b
import LeanLab.Languasco2004.Decomp316c

namespace LeanLab.Languasco2004.Feed565bE
open Real Finset Decomp279a Decomp316a Source565 Decomp588b Decomp316c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 283 and 285: the reciprocal pair sum over the product domain of regions 2, 3, 5,
7, 9, 12 and 15, namely Y^(89/462) < p at most Y^(17/54) and Y^(16/135) < q below the common
upper edge p^(-29/48) Y^(89/288) of those seven regions, with the finite cap n. -/
def restProductSum (Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ powerPrimes Y (89 / 462) (17 / 54),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧ Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ)),
      1 / ((p : ℝ) * (q : ℝ))

/-- Pages 267 to 269 display 52: if the six inequalities of region j hold in logarithmic form
and every earlier label fails its upper p bound, then j is the first matching region. -/
theorem regionIndex_eq_of_logs (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p)
    (hq0 : (0 : ℝ) < q) (j : ℕ)
    (a1 : (regionData j 0 : ℝ) * Real.log Y < Real.log p)
    (a2 : Real.log p ≤ (regionData j 1 : ℝ) * Real.log Y)
    (a3 : (regionData j 2 : ℝ) * Real.log p + (regionData j 3 : ℝ) * Real.log Y < Real.log q)
    (a4 : Real.log q < (regionData j 4 : ℝ) * Real.log p + (regionData j 5 : ℝ) * Real.log Y)
    (hj : j ∈ Icc 1 69)
    (hlt : ∀ i < j, i = 0 ∨ (regionData i 1 : ℝ) * Real.log Y < Real.log p) :
    regionIndex Y p q = j := by
  have hY0 : 0 < Y := by linarith
  have P : j ∈ Icc 1 69 ∧
      Y ^ (regionData j 0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (regionData j 1 : ℝ) ∧
      (p : ℝ) ^ (regionData j 2 : ℝ) * Y ^ (regionData j 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData j 4 : ℝ) * Y ^ (regionData j 5 : ℝ) := by
    refine ⟨hj, ?_, ?_, ?_, ?_⟩
    · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hp0, Real.log_rpow hY0]; exact a1
    · rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]; exact a2
    · rw [← Real.log_lt_log_iff (by positivity) hq0, Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hp0, Real.log_rpow hY0]; exact a3
    · rw [← Real.log_lt_log_iff hq0 (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hp0, Real.log_rpow hY0]; exact a4
  unfold regionIndex
  rw [dif_pos ⟨j, P⟩, Nat.find_eq_iff]
  refine ⟨P, fun i hi hPi => ?_⟩
  rcases hlt i hi with h0 | hb
  · subst h0; simp at hPi
  · have h2 := hPi.2.2.1
    have := Real.log_le_log hp0 h2
    rw [Real.log_rpow hY0] at this
    linarith


/-- Pages 267 to 269 with page 285: on the product domain the first matching region is one
of regions 2, 3, 5, 7, 9, 12, 15, chosen by the p range. -/
theorem rest_regionIndex_mem (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p)
    (hq0 : (0 : ℝ) < q)
    (h1 : (89 / 462) * Real.log Y < Real.log p) (h2 : Real.log p ≤ (17 / 54) * Real.log Y)
    (h3 : (16 / 135) * Real.log Y < Real.log q)
    (h4 : Real.log q < (-29 / 48) * Real.log p + (89 / 288) * Real.log Y) :
    regionIndex Y p q ∈ ({2, 3, 5, 7, 9, 12, 15} : Finset ℕ) := by
  have hL : 0 < Real.log Y := Real.log_pos hY
  have ej : ∀ j : ℕ, j ∈ ({2, 3, 5, 7, 9, 12, 15} : Finset ℕ) →
      (regionData j 0 : ℝ) * Real.log Y < Real.log p →
      Real.log p ≤ (regionData j 1 : ℝ) * Real.log Y →
      (∀ i < j, i = 0 ∨ (regionData i 1 : ℝ) * Real.log Y < Real.log p) →
      (regionData j 2 : ℝ) = 0 → (regionData j 3 : ℝ) = 16 / 135 →
      (regionData j 4 : ℝ) = -29 / 48 → (regionData j 5 : ℝ) = 89 / 288 →
      regionIndex Y p q ∈ ({2, 3, 5, 7, 9, 12, 15} : Finset ℕ) := by
    intro j hjm a1 a2 hlt c2 c3 c4 c5
    rw [regionIndex_eq_of_logs Y hY p q hp0 hq0 j a1 a2 (by rw [c2, c3]; linarith)
      (by rw [c4, c5]; linarith) (by simp only [mem_insert, mem_singleton] at hjm; simp only [mem_Icc]; omega) hlt]
    exact hjm

  have hcase : Real.log p ≤ (41 / 180) * Real.log Y ∨
      ((41 / 180) * Real.log Y < Real.log p ∧ Real.log p ≤ (8 / 33) * Real.log Y) ∨
      ((8 / 33) * Real.log Y < Real.log p ∧ Real.log p ≤ (37 / 150) * Real.log Y) ∨
      ((37 / 150) * Real.log Y < Real.log p ∧ Real.log p ≤ (17 / 63) * Real.log Y) ∨
      ((17 / 63) * Real.log Y < Real.log p ∧ Real.log p ≤ (17 / 57) * Real.log Y) ∨
      ((17 / 57) * Real.log Y < Real.log p ∧ Real.log p ≤ (31 / 99) * Real.log Y) ∨
      (31 / 99) * Real.log Y < Real.log p := by
    by_cases c1 : Real.log p ≤ (41 / 180) * Real.log Y
    · exact Or.inl c1
    by_cases c2 : Real.log p ≤ (8 / 33) * Real.log Y
    · exact Or.inr (Or.inl ⟨not_le.mp c1, c2⟩)
    by_cases c3 : Real.log p ≤ (37 / 150) * Real.log Y
    · exact Or.inr (Or.inr (Or.inl ⟨not_le.mp c2, c3⟩))
    by_cases c4 : Real.log p ≤ (17 / 63) * Real.log Y
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨not_le.mp c3, c4⟩)))
    by_cases c5 : Real.log p ≤ (17 / 57) * Real.log Y
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨not_le.mp c4, c5⟩))))
    by_cases c6 : Real.log p ≤ (31 / 99) * Real.log Y
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨not_le.mp c5, c6⟩)))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (not_le.mp c6))))))
  rcases hcase with hc | ⟨hl, hc⟩ | ⟨hl, hc⟩ | ⟨hl, hc⟩ | ⟨hl, hc⟩ | ⟨hl, hc⟩ | hl
  · refine ej 2 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 2 0 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 2 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 2 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 2 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 2 5 = (89/288 : ℚ) from rfl]; push_cast; ring
  · refine ej 3 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 3 0 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 3 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 3 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 3 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 3 5 = (89/288 : ℚ) from rfl]; push_cast; ring
  · refine ej 5 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 5 0 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 5 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 5 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 5 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 5 5 = (89/288 : ℚ) from rfl]; push_cast; ring
  · refine ej 7 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 7 0 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 7 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 7 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 7 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 7 5 = (89/288 : ℚ) from rfl]; push_cast; ring
  · refine ej 9 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 9 0 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 9 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 9 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 9 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 9 5 = (89/288 : ℚ) from rfl]; push_cast; ring
  · refine ej 12 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 12 0 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 12 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 12 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 12 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 12 5 = (89/288 : ℚ) from rfl]; push_cast; ring
  · refine ej 15 (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [show regionData 15 0 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · intro i hi
      interval_cases i
      · exact Or.inl rfl
      · right; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
      · right; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · simp only [show regionData 15 2 = (0 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 15 3 = (16/135 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 15 4 = (-29/48 : ℚ) from rfl]; push_cast; ring
    · simp only [show regionData 15 5 = (89/288 : ℚ) from rfl]; push_cast; ring

/-- Pages 269 and 285: regions 2, 3, 5, 7, 9, 12 and 15 lie in group five. -/
theorem groupOf_rest (i : ℕ) (h : i ∈ ({2, 3, 5, 7, 9, 12, 15} : Finset ℕ)) : groupOf i = 5 := by
  simp only [mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide


/-- PROVED, formerly LEAF: Jia pages 267 to 269 region table with page 285: every prime pair of the product
domain lies in the unselected group five pair domain, since its first matching region is the
one of regions 2, 3, 5, 7, 9, 12, 15 whose p range contains p; all earlier regions fail on
the p range alone, and the clipping q < min p sqrt(2Y/p) follows from t > 89/462. MEDIUM -/
theorem restProductSum_le_pairDomain :
    ∀ Y : ℝ, 1 < Y → ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
      restProductSum Y n ≤ ∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  intro Y hY n hn
  have hY0 : 0 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Q : ℕ → ℕ → Prop := fun p q => q.Prime ∧ Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ) with hQ
  have e : restProductSum Y n = ∑ x ∈ (powerPrimes Y (89 / 462) (17 / 54) ×ˢ range (n + 1)).filter
      (fun x => Q x.1 x.2), 1 / ((x.1 : ℝ) * (x.2 : ℝ)) := by
    rw [sum_filter, sum_product]
    unfold restProductSum
    apply sum_congr rfl
    intro p _
    rw [sum_filter]
  rw [e]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨hx1, hq, hqa, hqb⟩ := mem_filter.mp hx
    obtain ⟨hpP, hqR⟩ := mem_product.mp hx1
    obtain ⟨hp, hpa, hpb⟩ := (mem_powerPrimes hY0.le x.1).mp hpP
    have hp0 : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < x.2 := by exact_mod_cast hq.pos
    have l1 : (89 / 462) * Real.log Y < Real.log x.1 := by
      have := Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hpa
      rwa [Real.log_rpow hY0] at this
    have l2 : Real.log x.1 ≤ (17 / 54) * Real.log Y := by
      have := Real.log_le_log hp0 hpb
      rwa [Real.log_rpow hY0] at this
    have l3 : (16 / 135) * Real.log Y < Real.log x.2 := by
      have := Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hqa
      rwa [Real.log_rpow hY0] at this
    have l4 : Real.log x.2 < (-29 / 48) * Real.log x.1 + (89 / 288) * Real.log Y := by
      have := Real.log_lt_log hq0 hqb
      rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0,
        Real.log_rpow hY0] at this
    have hmem := rest_regionIndex_mem Y hY x.1 x.2 hp0 hq0 l1 l2 l3 l4
    have hpn : x.1 < n + 1 := by
      have h1 : (x.1 : ℝ) ≤ Y := by
        refine hpb.trans ?_
        calc Y ^ (17 / 54 : ℝ) ≤ Y ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num)
          _ = Y := Real.rpow_one Y
      have : (x.1 : ℝ) ≤ n := by linarith
      have : x.1 ≤ n := by exact_mod_cast this
      omega
    unfold pairDomain
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hpn, hqR⟩, hp, ?_, ?_, hq, hqa,
      lt_min ?_ ?_, groupOf_rest _ hmem, ?_, fun h => absurd h (by simp)⟩
    · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hp0, Real.log_rpow hY0]
      linarith
    · rw [Real.le_sqrt hp0.le (by positivity),
        ← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow,
        Real.log_mul (by norm_num) hY0.ne']
      push_cast; linarith
    · rw [← Real.log_lt_log_iff hq0 hp0]; linarith
    · rw [Real.lt_sqrt hq0.le, ← Real.log_lt_log_iff (by positivity) (by positivity),
        Real.log_pow, Real.log_div (by positivity) hp0.ne', Real.log_mul (by norm_num) hY0.ne']
      push_cast; linarith
    · have : regionIndex Y x.1 x.2 ≠ 1 := by
        intro h1; rw [h1] at hmem; simp at hmem
      simpa using this
  · intro x _ _
    positivity


/-- LEAF: Jia page 285 remaining region formula: by the Mertens estimate for the inner sum
over q, which gives log of (135/16)(89/288 - 29/48 t), and the prime number theorem Riemann
sum over p = Y^t, the product domain reciprocal sum is at least the integral of
log (1335/512 - 1305/256 t) / t over 89/462 to 17/54, up to any fixed loss. HARD -/
theorem restProductSum_lower :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        (∫ t in (89 / 462 : ℝ)..(17 / 54 : ℝ), log (1335 / 512 + (-1305 / 256) * t) / t) - η ≤
          restProductSum Y n := by
  sorry

/-- Jia page 285: the exact content of Feed565bC.pair_prime_sum_lower_rest, written with the
reciprocal sum spelled out. CONDITIONAL ON the two leaves above. -/
theorem pair_prime_sum_lower_rest_from_leaves :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) → Numeric565.mainRest + 0.000001 - η ≤
        (0.5612 * (135 / 16)) * ∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  intro η hη
  obtain ⟨Y₀, h⟩ := restProductSum_lower (η / (0.5612 * (135 / 16))) (by positivity)
  refine ⟨max Y₀ 2, fun Y hY n hn => ?_⟩
  have hY1 : 1 < Y := by linarith [le_max_right Y₀ 2]
  have h1 := h Y ((le_max_left _ _).trans hY) n hn
  have h2 := restProductSum_le_pairDomain Y hY1 n hn
  have hc : (0 : ℝ) < 0.5612 * (135 / 16) := by norm_num
  have e : (0.5612 * (135 / 16)) * (η / (0.5612 * (135 / 16))) = η := by field_simp
  unfold Numeric565.mainRest
  nlinarith

#print axioms restProductSum
#print axioms regionIndex_eq_of_logs
#print axioms rest_regionIndex_mem
#print axioms groupOf_rest
#print axioms restProductSum_le_pairDomain
#print axioms restProductSum_lower
#print axioms pair_prime_sum_lower_rest_from_leaves
end
end LeanLab.Languasco2004.Feed565bE
