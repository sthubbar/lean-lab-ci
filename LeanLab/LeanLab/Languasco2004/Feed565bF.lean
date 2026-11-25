/-
Jia 1996 pages 267 to 269 and 284 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Feed565bD.triple_prime_sum_upper_rest, burst-20261122, session S140.
The unselected group five pair domain lies inside the product domain
Y^(89/462) < p at most Y^(17/54), Y^(16/135) < q < p^(-29/48) Y^(89/288),
and on that domain the weighted reciprocal triple sum tends to restOne + restTwo + restThree.
Analytic leaves stay OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Feed565bC

namespace LeanLab.Languasco2004.Feed565bF
open Real Finset Decomp279a Decomp316a Source565 Decomp588b Decomp316c Feed565bC Numeric565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 284 and 285: the weighted reciprocal triple sum over the product domain of regions
2, 3, 5, 7, 9, 12 and 15, with Lemma 20 weight 0.5617 below the middle boundary
p q^2 at most Y^(71/135) and 0.5644 above it, the same weights as Feed565bD.triplePrimeModelRest. -/
def tripleProductSum (Y : ℝ) (n : ℕ) : ℝ :=
  (135 / 16) * ∑ pq ∈ (powerPrimes Y (89 / 462) (17 / 54) ×ˢ range (n + 1)).filter
      (fun pq : ℕ × ℕ => pq.2.Prime ∧ Y ^ (16 / 135 : ℝ) < (pq.2 : ℝ) ∧
        (pq.2 : ℝ) < (pq.1 : ℝ) ^ (-29 / 48 : ℝ) * Y ^ (89 / 288 : ℝ)),
    ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
        then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))

/-- Pages 267 to 269 and 285: on the unselected pair domain the region data give
89/462 log Y < log p at most 17/54 log Y and log q below -29/48 log p + 89/288 log Y. -/
theorem rest_logs_product {Y : ℝ} {n : ℕ} (hY : 1 < Y) (pq : ℕ × ℕ)
    (h : pq ∈ pairDomain false Y n) :
    (89 / 462) * Real.log Y < Real.log pq.1 ∧ Real.log pq.1 ≤ (17 / 54) * Real.log Y ∧
      Real.log pq.2 < (-29 / 48) * Real.log pq.1 + (89 / 288) * Real.log Y := by
  obtain ⟨-, hp, -, -, hq, -, -, hg, hsel, -⟩ := mem_filter.mp h
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
  have h1 : regionIndex Y pq.1 pq.2 ≠ 1 := by simpa using hsel
  have hmem := group5_labels _ hg
  have h0 : regionIndex Y pq.1 pq.2 ≠ 0 := by
    intro h0; rw [h0] at hmem; simp at hmem
  obtain ⟨s1, -, -, -⟩ := regionIndex_spec_rest Y pq.1 pq.2 h0
  have l1 := Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) s1
  rw [Real.log_rpow hY0] at l1
  obtain ⟨l2, l4⟩ := region_logs_rest Y hY pq.1 pq.2 hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
  generalize regionIndex Y pq.1 pq.2 = i at h1 hmem l1 l2 l4
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · simp only [show regionData 2 0 = (89/462 : ℚ) from rfl, show regionData 2 1 = (41/180 : ℚ) from rfl, show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 3 0 = (41/180 : ℚ) from rfl, show regionData 3 1 = (8/33 : ℚ) from rfl, show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 5 0 = (8/33 : ℚ) from rfl, show regionData 5 1 = (37/150 : ℚ) from rfl, show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 7 0 = (37/150 : ℚ) from rfl, show regionData 7 1 = (17/63 : ℚ) from rfl, show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 9 0 = (17/63 : ℚ) from rfl, show regionData 9 1 = (17/57 : ℚ) from rfl, show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 12 0 = (17/57 : ℚ) from rfl, show regionData 12 1 = (31/99 : ℚ) from rfl, show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · simp only [show regionData 15 0 = (31/99 : ℚ) from rfl, show regionData 15 1 = (17/54 : ℚ) from rfl, show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl] at l1 l2 l4
    push_cast at l1 l2 l4
    refine ⟨?_, ?_, ?_⟩ <;> linarith
/-- PROVED: Jia pages 267 to 269 with page 285: the unselected pair domain lies inside the
product domain, so the weighted triple sum over it is at most tripleProductSum. -/
theorem triple_rest_le_product :
    ∀ Y : ℝ, 1 < Y → ∀ n : ℕ,
      (135 / 16) * ∑ pq ∈ pairDomain false Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
            then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) ≤
        tripleProductSum Y n := by
  intro Y hY n
  have hY0 : 0 < Y := by linarith
  unfold tripleProductSum
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum_of_subset_of_nonneg
  · intro pq h
    obtain ⟨l1, l2, l4⟩ := rest_logs_product hY pq h
    obtain ⟨hcap, hp, -, -, hq, hqa, -⟩ := mem_filter.mp h
    have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < pq.2 := by exact_mod_cast hq.pos
    refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, (mem_product.mp hcap).2⟩, hq, hqa, ?_⟩
    · rw [mem_powerPrimes hY0.le]
      refine ⟨hp, ?_, ?_⟩
      · rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hY0 _) hp0, Real.log_rpow hY0]
        exact l1
      · rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]
        exact l2
    · rw [← Real.log_lt_log_iff hq0 (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow hp0, Real.log_rpow hY0]
      exact l4
  · intro pq _ _
    apply sum_nonneg
    intro r hr
    obtain ⟨-, hrp, -⟩ := mem_filter.mp hr
    have : (0 : ℝ) < r := by exact_mod_cast hrp.pos
    apply div_nonneg (by split_ifs <;> norm_num)
    positivity

/-- LEAF: Jia page 285 remaining region formula: by the Mertens estimate for the inner sums
over r and q and the prime number theorem Riemann sum over p = Y^t, the weighted triple sum
over the product domain is at most restOne + restTwo + restThree, up to any fixed excess;
restOne is the 0.5617 part below the middle boundary for t up to 13/45, restTwo and restThree
the 0.5644 part above it. HARD -/
theorem tripleProductSum_upper :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        tripleProductSum Y n ≤ restOne + restTwo + restThree + η := by
  sorry

/-- Jia page 285: the exact content of Feed565bD.triple_prime_sum_upper_rest, written with the
weighted sum spelled out. CONDITIONAL ON tripleProductSum_upper. -/
theorem triple_prime_sum_upper_rest_from_leaves :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        (135 / 16) * ∑ pq ∈ pairDomain false Y n,
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
            (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
              then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) ≤
          restOne + restTwo + restThree + η := by
  intro η hη
  obtain ⟨Y₀, h⟩ := tripleProductSum_upper η hη
  exact ⟨max Y₀ 2, fun Y hY n hn =>
    (triple_rest_le_product Y (by linarith [le_max_right Y₀ 2]) n).trans
      (h Y ((le_max_left _ _).trans hY) n hn)⟩

#print axioms tripleProductSum
#print axioms rest_logs_product
#print axioms triple_rest_le_product
#print axioms tripleProductSum_upper
#print axioms triple_prime_sum_upper_rest_from_leaves
end
end LeanLab.Languasco2004.Feed565bF
