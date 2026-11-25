/-
Jia 1996 pages 261, 262 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp565b.model_pair_lower, the remaining regions of Lemma 28 group five.
The rough integer comparison and the prime pair summation are separate leaves.
Analytic leaves stay OPEN. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578c
import LeanLab.Languasco2004.Feed565bE

namespace LeanLab.Languasco2004.Feed565bC
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Numeric565 Reserve578 Decomp578c
open Decomp316c Decomp588b Decomp588c Sieve565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 285 remaining region formula with page 283 display 60: the constant lower
approximation to the reciprocal pair prime sum over the unselected pair domain.
Lemma 20 part iii gives the weight 0.5612, as for Decomp578c.pairPrimeModel. -/
def pairPrimeModelRest (Y : ℝ) (n : ℕ) : ℝ :=
  (0.5612 * (135 / 16)) *
    ∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))

/-- Pages 267 to 269 display 52: the least matching region satisfies its own six defining
inequalities. Same statement as Feed564bPrime.regionIndex_spec, repeated so this module stays
off the Decomp564b feed branch. -/
theorem regionIndex_spec_rest (Y : ℝ) (p q : ℕ) (h : regionIndex Y p q ≠ 0) :
    Y ^ (regionData (regionIndex Y p q) 0 : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ Y ^ (regionData (regionIndex Y p q) 1 : ℝ) ∧
      (p : ℝ) ^ (regionData (regionIndex Y p q) 2 : ℝ) *
        Y ^ (regionData (regionIndex Y p q) 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData (regionIndex Y p q) 4 : ℝ) *
        Y ^ (regionData (regionIndex Y p q) 5 : ℝ) := by
  unfold regionIndex at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Nat.find_spec hex).2
  · exact absurd rfl h

/-- Pages 267 to 269: the upper p bound and the upper q bound of the region in logarithmic form. -/
theorem region_logs_rest (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : regionIndex Y p q ≠ 0) :
    Real.log p ≤ (regionData (regionIndex Y p q) 1 : ℝ) * Real.log Y ∧
      Real.log q < (regionData (regionIndex Y p q) 4 : ℝ) * Real.log p +
        (regionData (regionIndex Y p q) 5 : ℝ) * Real.log Y := by
  obtain ⟨-, h2, -, h4⟩ := regionIndex_spec_rest Y p q h
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  refine ⟨?_, ?_⟩
  · have := Real.log_le_log hp0 h2
    rwa [Real.log_rpow hY0] at this
  · have := Real.log_lt_log hq0 h4
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hp0,
      Real.log_rpow hY0] at this

/-- Page 285 and Lemma 28 on page 282: the labels of group five. -/
theorem group5_labels (i : ℕ) (h : groupOf i = 5) :
    i ∈ ({1, 2, 3, 5, 7, 9, 12, 15} : Finset ℕ) := by
  unfold groupOf at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> first | exact h5 | norm_num at h

/-- Page 285: on the unselected pair domain, regions 2, 3, 5, 7, 9, 12 and 15, one has
p at most Y^(17/54) and pq at most Y^(1/2), in logarithmic form. -/
theorem rest_logs {Y : ℝ} {n : ℕ} (hY : 1 < Y) (pq : ℕ × ℕ) (h : pq ∈ pairDomain false Y n) :
    Real.log pq.1 ≤ (17 / 54) * Real.log Y ∧
      Real.log pq.1 + Real.log pq.2 ≤ (1 / 2) * Real.log Y := by
  obtain ⟨-, hp, -, -, hq, -, -, hg, hsel, -⟩ := mem_filter.mp h
  have h1 : regionIndex Y pq.1 pq.2 ≠ 1 := by simpa using hsel
  have hmem := group5_labels _ hg
  have h0 : regionIndex Y pq.1 pq.2 ≠ 0 := by
    intro h0; rw [h0] at hmem; simp at hmem
  obtain ⟨l2, l4⟩ := region_logs_rest Y hY pq.1 pq.2 hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
  have hp1 : 0 ≤ Real.log (pq.1 : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  generalize regionIndex Y pq.1 pq.2 = i at h1 hmem l2 l4
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · simp only [show regionData 2 1 = (41/180 : ℚ) from rfl, show regionData 2 4 = (-29/48 : ℚ) from rfl, show regionData 2 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith
  · simp only [show regionData 3 1 = (8/33 : ℚ) from rfl, show regionData 3 4 = (-29/48 : ℚ) from rfl, show regionData 3 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith
  · simp only [show regionData 5 1 = (37/150 : ℚ) from rfl, show regionData 5 4 = (-29/48 : ℚ) from rfl, show regionData 5 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith
  · simp only [show regionData 7 1 = (17/63 : ℚ) from rfl, show regionData 7 4 = (-29/48 : ℚ) from rfl, show regionData 7 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith
  · simp only [show regionData 9 1 = (17/57 : ℚ) from rfl, show regionData 9 4 = (-29/48 : ℚ) from rfl, show regionData 9 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith
  · simp only [show regionData 12 1 = (31/99 : ℚ) from rfl, show regionData 12 4 = (-29/48 : ℚ) from rfl, show regionData 12 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith
  · simp only [show regionData 15 1 = (17/54 : ℚ) from rfl, show regionData 15 4 = (-29/48 : ℚ) from rfl, show regionData 15 5 = (89/288 : ℚ) from rfl] at l2 l4
    push_cast at l2 l4
    constructor <;> linarith

/-- Page 285 support: the unselected pair cofactor is at least Y^(1/2). -/
theorem rest_cofactor_ge {Y : ℝ} {n : ℕ} (hY : 1 < Y) (pq : ℕ × ℕ)
    (h : pq ∈ pairDomain false Y n) :
    Y ^ (1 / 2 : ℝ) ≤ Y / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  obtain ⟨-, hlpq⟩ := rest_logs hY pq h
  obtain ⟨-, hp, -, -, hq, -⟩ := mem_filter.mp h
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < pq.2 := by exact_mod_cast hq.pos
  have hprod : (pq.1 : ℝ) * pq.2 ≤ Y ^ (1 / 2 : ℝ) := by
    rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hY0 _),
      Real.log_mul hp0.ne' hq0.ne', Real.log_rpow hY0]
    linarith
  rw [le_div_iff₀ (mul_pos hp0 hq0)]
  calc Y ^ (1 / 2 : ℝ) * ((pq.1 : ℝ) * pq.2) ≤ Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = Y := by rw [← Real.rpow_add hY0]; norm_num

/-- Page 285 with Geometry565.mainRest_argument: a cofactor of size at least Y^(1/2) has
Buchstab argument at least four. -/
theorem rest_argument_ge_four {Y t : ℝ} (hY : 1 < Y) (ht : Y ^ (1 / 2 : ℝ) ≤ t) :
    4 ≤ log t / log (Y ^ (16 / 135 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hP : 0 < Y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hY0 _
  have hlY : 0 < log Y := Real.log_pos hY
  have hlog := Real.log_le_log hP ht
  rw [Real.log_rpow hY0] at hlog
  rw [Real.log_rpow hY0, le_div_iff₀ (by positivity : 0 < (16 / 135 : ℝ) * log Y)]
  nlinarith

/-- Page 285 support: uniform bound on the reciprocal unselected pair sum, from two blocks of
the proved lab Mertens bound Decomp588c.power_prime_sum_le_six. -/
theorem rest_reciprocal_le {Y : ℝ} {n : ℕ} (hY : 1 < Y)
    (hlog : 28 ≤ (16 / 135 : ℝ) * log Y) :
    (∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) ≤ 144 := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hlY : 0 < log Y := Real.log_pos hY
  have hsub : pairDomain false Y n ⊆
      powerPrimes Y (16 / 135) (64 / 135) ×ˢ powerPrimes Y (16 / 135) (64 / 135) := by
    intro pq h
    obtain ⟨hlp, -⟩ := rest_logs hY pq h
    obtain ⟨-, hp, hpa, -, hq, hqa, hqp, -⟩ := mem_filter.mp h
    have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
    have hqp' : (pq.2 : ℝ) < pq.1 := lt_of_lt_of_le hqp (min_le_left _ _)
    have hpb : (pq.1 : ℝ) ≤ Y ^ (64 / 135 : ℝ) := by
      rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos (by linarith) _),
        Real.log_rpow (by linarith)]
      linarith
    rw [mem_product, mem_powerPrimes hY0, mem_powerPrimes hY0]
    exact ⟨⟨hp, hpa, hpb⟩, ⟨hq, hqa, hqp'.le.trans hpb⟩⟩
  have hP : (∑ p ∈ powerPrimes Y (16 / 135) (64 / 135), (1 : ℝ) / p) ≤ 12 := by
    have hsplit : powerPrimes Y (16 / 135) (64 / 135) ⊆
        powerPrimes Y (16 / 135) (32 / 135) ∪ powerPrimes Y (32 / 135) (64 / 135) := by
      intro p hp
      rw [mem_powerPrimes hY0] at hp
      rw [mem_union, mem_powerPrimes hY0, mem_powerPrimes hY0]
      by_cases h : (p : ℝ) ≤ Y ^ (32 / 135 : ℝ)
      · exact Or.inl ⟨hp.1, hp.2.1, h⟩
      · exact Or.inr ⟨hp.1, not_le.mp h, hp.2.2⟩
    have h1 := power_prime_sum_le_six hY (by norm_num : (16 / 135 : ℝ) ≤ 32 / 135)
      (by norm_num) hlog
    have h2 := power_prime_sum_le_six hY (by norm_num : (32 / 135 : ℝ) ≤ 64 / 135)
      (by norm_num) (by linarith)
    have hu := sum_union_inter (s₁ := powerPrimes Y (16 / 135) (32 / 135))
      (s₂ := powerPrimes Y (32 / 135) (64 / 135)) (f := fun p : ℕ => (1 : ℝ) / p)
    have hi : 0 ≤ ∑ p ∈ powerPrimes Y (16 / 135) (32 / 135) ∩
        powerPrimes Y (32 / 135) (64 / 135), (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
    have hs := sum_le_sum_of_subset_of_nonneg hsplit
      (f := fun p : ℕ => (1 : ℝ) / p) (fun _ _ _ => by positivity)
    linarith
  have hP0 : 0 ≤ ∑ p ∈ powerPrimes Y (16 / 135) (64 / 135), (1 : ℝ) / p :=
    sum_nonneg fun _ _ => by positivity
  calc _ ≤ ∑ pq ∈ powerPrimes Y (16 / 135) (64 / 135) ×ˢ powerPrimes Y (16 / 135) (64 / 135),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ p ∈ powerPrimes Y (16 / 135) (64 / 135), (1 : ℝ) / p) *
        (∑ p ∈ powerPrimes Y (16 / 135) (64 / 135), (1 : ℝ) / p) := by
        rw [sum_product, sum_mul_sum]
        simp only [one_div_mul_one_div]
    _ ≤ 12 * 12 := mul_le_mul hP hP hP0 (by norm_num)
    _ = 144 := by norm_num

/-- PROVED, formerly LEAF: Jia page 283 display 60 transferred to the page 285 remaining regions, first model equality and application of Lemma 20. MEDIUM.
CONDITIONAL ON the explicit Buchstab existence, global bounds and Lemma 21 inputs.
The Buchstab argument is at least four by Geometry565.mainRest_argument.
Only the individual rough integer counts are replaced by the reciprocal prime sum. -/
theorem pair_rough_lower_rest
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        (pairPrimeModelRest Y n - η) * (Y / log Y) ≤
          pairMass true false 0 Y n (Y ^ (16 / 135 : ℝ)) := by
  intro η hη
  let ξ := η / 1216
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  obtain ⟨w, hw, hi, hr⟩ := hex
  obtain ⟨T, Z, hT, hZ, hcount⟩ := h21 w hw hi hr ξ hξ
  obtain ⟨Y1, h1⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (Filter.eventually_ge_atTop T))
  obtain ⟨Y2, h2⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 16 / 135)).eventually
      (Filter.eventually_ge_atTop Z))
  obtain ⟨Y3, h3⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (28 / (16 / 135 : ℝ))))
  refine ⟨max 2 (max Y1 (max Y2 Y3)), ?_⟩
  intro Y hY n hn
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 < Y := by linarith
  have hYa : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYb : Y2 ≤ Y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYc : Y3 ≤ Y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hlog : 28 ≤ (16 / 135 : ℝ) * log Y := by
    have := h3 Y hYc
    rw [div_le_iff₀ (by norm_num)] at this
    linarith
  have hscale : 0 ≤ Y / log Y := div_nonneg (by linarith) (Real.log_pos hY1).le
  have hsum := rest_reciprocal_le (n := n) hY1 hlog
  have hterms : ∀ pq ∈ pairDomain false Y n,
      (0.5612 - ξ) * ((Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) / log (Y ^ (16 / 135 : ℝ))) ≤
        ((sieved (sourceSet true 0 Y n (pq.1 * pq.2)) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
    intro pq hpq
    have hcof := rest_cofactor_ge hY1 pq hpq
    obtain ⟨hcap, hp, hpa, hpS, hq, hqa, hqp, hg, hreg, hB⟩ := mem_filter.mp hpq
    have htT : T ≤ Y / ((pq.1 : ℝ) * (pq.2 : ℝ)) := (h1 Y hYa).trans hcof
    have hzt : Y ^ (16 / 135 : ℝ) ≤ Y / ((pq.1 : ℝ) * (pq.2 : ℝ)) :=
      (Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num)).trans hcof
    have hc' := hcount (Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) (Y ^ (16 / 135 : ℝ))
      htT (h2 Y hYb) hzt
    have hwlow := ((h20 w hw hi hr).2 _ (rest_argument_ge_four hY1 hcof)).1
    have hres := pair_rescale_card_ge (by linarith : 0 < Y) hn hp hq hpa hqa
    push_cast at hres
    have hs : 0 ≤ (Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) / log (Y ^ (16 / 135 : ℝ)) := by
      rw [Real.log_rpow (by linarith : 0 < Y)]
      positivity
    have ha := (abs_le.mp hc').1
    have hm := mul_le_mul_of_nonneg_right hwlow hs
    have hcard : ((sieved (Ioc ⌊Y / ((pq.1 : ℝ) * (pq.2 : ℝ))⌋₊
        ⌊2 * (Y / ((pq.1 : ℝ) * (pq.2 : ℝ)))⌋₊) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ) ≤
        ((sieved (sourceSet true 0 Y n (pq.1 * pq.2)) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
      exact_mod_cast hres
    linarith
  have hsumterms := sum_le_sum hterms
  set S := ∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) with hS
  have heq : (∑ pq ∈ pairDomain false Y n,
      (0.5612 - ξ) * ((Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) / log (Y ^ (16 / 135 : ℝ)))) =
      ((0.5612 * (135 / 16)) * S - (ξ * (135 / 16)) * S) * (Y / log Y) := by
    calc _ = ((0.5612 - ξ) * (135 / 16) * (Y / log Y)) * S := by
          rw [hS, mul_sum]
          apply sum_congr rfl
          intro pq hpq
          have hp := (mem_filter.mp hpq).2.1
          have hq := (mem_filter.mp hpq).2.2.2.2.1
          have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
          have hq0 : (0 : ℝ) < pq.2 := by exact_mod_cast hq.pos
          rw [cofactor_normalization hY1 (mul_pos hp0 hq0)]
          ring
      _ = _ := by ring
  rw [heq] at hsumterms
  have herr : (ξ * (135 / 16)) * S ≤ η := by
    calc _ ≤ (ξ * (135 / 16)) * 144 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ η := by dsimp [ξ]; linarith
  change _ ≤ ∑ pq ∈ pairDomain false Y n,
    ((sieved (sourceSet true 0 Y n (pq.1 * pq.2)) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ)
  have hmodel : pairPrimeModelRest Y n = (0.5612 * (135 / 16)) * S := rfl
  rw [hmodel]
  exact (mul_le_mul_of_nonneg_right (by linarith :
    (0.5612 * (135 / 16)) * S - η ≤
      (0.5612 * (135 / 16)) * S - (ξ * (135 / 16)) * S) hscale).trans hsumterms


/-- SPLIT, formerly LEAF: Jia page 285 remaining region formula, the pair prime sum to double integral step behind mainRest. HARD.
CONDITIONAL ON Feed565bE.restProductSum_le_pairDomain, MEDIUM, and Feed565bE.restProductSum_lower, HARD, S140.
Only the reciprocal pair prime sum over the unselected domain is estimated.
The untruncated integral is mainRest plus its source reserve 0.000001. -/
theorem pair_prime_sum_lower_rest :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) → mainRest + 0.000001 - η ≤ pairPrimeModelRest Y n :=
  Feed565bE.pair_prime_sum_lower_rest_from_leaves

/-- Page 285 support: the B pair mass has no dependence on the ambient prime location N. -/
theorem pair_model_independent_rest (N Y : ℝ) (n : ℕ) (z : ℝ) :
    pairMass true false N Y n z = pairMass true false 0 Y n z := by rfl

/-- Jia page 285 with display 60: exact type of Decomp565b.model_pair_lower.
CONDITIONAL ON the two leaves above and the Buchstab inputs of Decomp578c.
The model estimate is pointwise for large N, so its exceptional set is empty. -/
theorem model_pair_lower_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        modelPair false N (localization N ε) n < (mainRest + 0.0000004) * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := pair_rough_lower_rest buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.0000003 (by norm_num)
  obtain ⟨Y2, h2⟩ := pair_prime_sum_lower_rest 0.0000003 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      modelPair false N (localization N ε) n <
        (mainRest + 0.0000004) * scale N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_lower N (localization N ε)
      (pairPrimeModelRest (localization N ε) n - 0.0000003)
      (pairMass true false 0 (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : mainRest + 0.0000004 ≤ pairPrimeModelRest (localization N ε) n - 0.0000003 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← pair_model_independent_rest N] at hnorm
    change (pairPrimeModelRest (localization N ε) n - 0.0000003) * scale N (localization N ε) n ≤
      modelPair false N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms pairPrimeModelRest
#print axioms group5_labels
#print axioms rest_logs
#print axioms rest_cofactor_ge
#print axioms rest_reciprocal_le
#print axioms pair_rough_lower_rest
#print axioms pair_prime_sum_lower_rest
#print axioms pair_model_independent_rest
#print axioms model_pair_lower_from_leaves
end
end LeanLab.Languasco2004.Feed565bC
