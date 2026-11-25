/-
Jia 1996 pages 261, 262 and 284 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp565b.model_triple_upper, the remaining regions of Lemma 28 group five.
The rough integer comparison and the prime triple summation are separate leaves.
Analytic leaves stay OPEN. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578c
import LeanLab.Languasco2004.Feed565bC
import LeanLab.Languasco2004.Decomp578d
import LeanLab.Languasco2004.Feed565bF

namespace LeanLab.Languasco2004.Feed565bD
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Numeric565 Reserve578 Decomp578c
open Decomp316c Decomp588b Decomp588c Sieve565 Feed565bC Decomp578d
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 284 and 285 remaining region formula: the weighted reciprocal triple prime sum
over the unselected pair domain. Below the middle boundary Lemma 20 gives 0.5617,
above it 0.5644, the same weights as Decomp578d.triplePrimeModel. -/
def triplePrimeModelRest (Y : ℝ) (n : ℕ) : ℝ :=
  (135 / 16) * ∑ pq ∈ pairDomain false Y n,
    ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
        then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))

/-- Pages 267 to 269 and 285: on the unselected group five pair domain, log p at most
17/54 log Y and log p + 2 log q at most 3/5 log Y, from the region data of regions
2, 3, 5, 7, 9, 12 and 15 and the lower cut p > Y^(16/135). -/
theorem rest_logs_triple {Y : ℝ} {n : ℕ} (hY : 1 < Y) (pq : ℕ × ℕ)
    (h : pq ∈ pairDomain false Y n) :
    Real.log pq.1 ≤ (17 / 54) * Real.log Y ∧
      Real.log pq.1 + 2 * Real.log pq.2 ≤ (3 / 5) * Real.log Y := by
  obtain ⟨-, hp, hpa, -, hq, -, -, hg, hsel, -⟩ := mem_filter.mp h
  have hY0 : 0 < Y := by linarith
  have l1 : (16 / 135) * Real.log Y < Real.log pq.1 := by
    have := Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hpa
    rwa [Real.log_rpow hY0] at this
  have h1 : regionIndex Y pq.1 pq.2 ≠ 1 := by simpa using hsel
  have hmem := group5_labels _ hg
  have h0 : regionIndex Y pq.1 pq.2 ≠ 0 := by
    intro h0; rw [h0] at hmem; simp at hmem
  obtain ⟨l2, l4⟩ := region_logs_rest Y hY pq.1 pq.2 hp hq h0
  have hL : 0 < Real.log Y := Real.log_pos hY
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

/-- Finite union bound for nonnegative summands. -/
theorem sum_union_le_of_nonneg (s t : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ x ∈ s ∩ t, f x := sum_nonneg fun x _ => hf x
  linarith

/-- Page 285 support: the reciprocal prime sum over Y^(1/10) to Y^(64/135) is at most 18,
from three blocks of the proved lab Mertens bound Decomp588c.power_prime_sum_le_six. -/
theorem rest_prime_recip_le {Y : ℝ} (hY : 1 < Y) (hlog : 28 ≤ (1 / 10 : ℝ) * log Y) :
    (∑ p ∈ powerPrimes Y (1 / 10) (64 / 135), (1 : ℝ) / p) ≤ 18 := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsplit : powerPrimes Y (1 / 10) (64 / 135) ⊆
      (powerPrimes Y (1 / 10) (1 / 5) ∪ powerPrimes Y (1 / 5) (2 / 5)) ∪
        powerPrimes Y (2 / 5) (64 / 135) := by
    intro p hp
    rw [mem_powerPrimes hY0] at hp
    rw [mem_union, mem_union, mem_powerPrimes hY0, mem_powerPrimes hY0, mem_powerPrimes hY0]
    by_cases h1 : (p : ℝ) ≤ Y ^ (1 / 5 : ℝ)
    · exact Or.inl (Or.inl ⟨hp.1, hp.2.1, h1⟩)
    · by_cases h2 : (p : ℝ) ≤ Y ^ (2 / 5 : ℝ)
      · exact Or.inl (Or.inr ⟨hp.1, not_le.mp h1, h2⟩)
      · exact Or.inr ⟨hp.1, not_le.mp h2, hp.2.2⟩
  have hl : 0 < log Y := Real.log_pos hY
  have a1 := power_prime_sum_le_six hY (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5) (by norm_num) hlog
  have a2 := power_prime_sum_le_six hY (by norm_num : (1 / 5 : ℝ) ≤ 2 / 5) (by norm_num)
    (by linarith)
  have a3 := power_prime_sum_le_six hY (by norm_num : (2 / 5 : ℝ) ≤ 64 / 135) (by norm_num)
    (by linarith)
  have hf : ∀ x : ℕ, 0 ≤ (1 : ℝ) / x := fun x => by positivity
  have hs := sum_le_sum_of_subset_of_nonneg hsplit (f := fun p : ℕ => (1 : ℝ) / p)
    (fun x _ _ => hf x)
  have u1 := sum_union_le_of_nonneg (powerPrimes Y (1 / 10) (1 / 5) ∪ powerPrimes Y (1 / 5) (2 / 5))
    (powerPrimes Y (2 / 5) (64 / 135)) (fun p : ℕ => (1 : ℝ) / p) hf
  have u2 := sum_union_le_of_nonneg (powerPrimes Y (1 / 10) (1 / 5))
    (powerPrimes Y (1 / 5) (2 / 5)) (fun p : ℕ => (1 : ℝ) / p) hf
  linarith

/-- Page 285 support: uniform bound on the reciprocal unselected triple sum. -/
theorem rest_triple_recip_le {Y : ℝ} {n : ℕ} (hY : 1 < Y) (hlog : 28 ≤ (1 / 10 : ℝ) * log Y) :
    ∑ pq ∈ pairDomain false Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) ≤ 5832 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlY : 0 < log Y := Real.log_pos hY
  set P := powerPrimes Y (1 / 10) (64 / 135) with hPdef
  have hP := rest_prime_recip_le hY hlog
  have hP0 : 0 ≤ ∑ p ∈ P, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
  have hlow : Y ^ (1 / 10 : ℝ) < Y ^ (16 / 135 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num)
  have hdom : ∀ pq ∈ pairDomain false Y n, pq.1 ∈ P ∧ pq.2 ∈ P ∧
      (pq.2 : ℝ) ≤ Y ^ (64 / 135 : ℝ) := by
    intro pq h
    obtain ⟨hlp, -⟩ := rest_logs_triple hY pq h
    obtain ⟨-, hp, hpa, -, hq, hqa, hqp, -⟩ := mem_filter.mp h
    have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
    have hqp' : (pq.2 : ℝ) < pq.1 := lt_of_lt_of_le hqp (min_le_left _ _)
    have hpb : (pq.1 : ℝ) ≤ Y ^ (64 / 135 : ℝ) := by
      rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]
      linarith
    rw [hPdef, mem_powerPrimes hY0.le, mem_powerPrimes hY0.le]
    exact ⟨⟨hp, hlow.trans hpa, hpb⟩, ⟨hq, hlow.trans hqa, hqp'.le.trans hpb⟩,
      hqp'.le.trans hpb⟩
  have hr : ∀ pq ∈ pairDomain false Y n,
      ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / r ≤ 18 := by
    intro pq h
    obtain ⟨-, -, hqb⟩ := hdom pq h
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) hP
    intro r hr'
    obtain ⟨-, hrp, hra, hrq⟩ := mem_filter.mp hr'
    rw [mem_powerPrimes hY0.le]
    exact ⟨hrp, hlow.trans_le hra, hrq.le.trans hqb⟩
  have hpair : ∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) ≤ 18 * 18 := by
    have hsub : pairDomain false Y n ⊆ P ×ˢ P := fun pq h =>
      mem_product.mpr ⟨(hdom pq h).1, (hdom pq h).2.1⟩
    calc _ ≤ ∑ pq ∈ P ×ˢ P, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (∑ p ∈ P, (1 : ℝ) / p) * (∑ p ∈ P, (1 : ℝ) / p) := by
          rw [sum_product, sum_mul_sum]
          simp only [one_div_mul_one_div]
      _ ≤ 18 * 18 := mul_le_mul hP hP hP0 (by norm_num)
  calc _ = ∑ pq ∈ pairDomain false Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) *
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / r := by
        refine sum_congr rfl fun pq _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ ∑ pq ∈ pairDomain false Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) * 18 :=
        sum_le_sum fun pq h => mul_le_mul_of_nonneg_left (hr pq h) (by positivity)
    _ = (∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) * 18 := by
        rw [sum_mul]
    _ ≤ (18 * 18) * 18 := mul_le_mul_of_nonneg_right hpair (by norm_num)
    _ = 5832 := by norm_num

/-- Pages 284 and 285: the unselected triple mass as a double sum of sieved counts.
Same proof as Decomp578d.tripleMass_eq_double_sum. -/
theorem tripleMass_rest_eq (Y : ℝ) (n : ℕ) :
    tripleMass true false 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ))
      = ∑ pq ∈ pairDomain false Y n,
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1
            (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
  simp only [tripleMass, tripleSieved, ite_true]
  refine Finset.sum_congr rfl (fun pq _ => ?_)
  refine Finset.sum_congr ?_ (fun r _ => rfl)
  ext r
  simp only [mem_filter]
  constructor
  · intro ⟨hm, h1, h2, h3⟩
    exact ⟨hm, h1, h2, h3.1⟩
  · intro ⟨hm, h1, h2, h3⟩
    exact ⟨hm, h1, h2, h3, fun hd => by
      have h := Nat.dvd_one.mp hd
      have := h1.two_le
      omega⟩

/-- Page 284: below the middle boundary p q^2 at most Y^(71/135) the argument is at least 4.
Same proof as the private Decomp578d.triple_argument_ge_four. -/
theorem triple_rest_argument_ge_four {Y p q r : ℝ} (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hrq : r < q) (hsmall : p * q ^ 2 ≤ Y ^ (71 / 135 : ℝ)) :
    4 ≤ Real.log (Y / (p * q * r)) / Real.log (Y ^ (16 / 135 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hgrowth : p * q * r < p * q ^ 2 := by
    calc p * q * r < p * q * q := by
          exact mul_lt_mul_of_pos_left hrq (by positivity)
      _ = p * q ^ 2 := by ring
  have hlt : Real.log (p * q * r) < Real.log (p * q ^ 2) :=
    Real.log_lt_log (by positivity) hgrowth
  have hsmall' : Real.log (p * q ^ 2) ≤ (71 / 135) * Real.log Y := by
    calc Real.log (p * q ^ 2) ≤ Real.log (Y ^ (71 / 135 : ℝ)) :=
          Real.log_le_log (by positivity) hsmall
      _ = (71 / 135) * Real.log Y := Real.log_rpow hY0 _
  have hlogpqr : Real.log (p * q * r) < (71 / 135) * Real.log Y := lt_of_lt_of_le hlt hsmall'
  have hsplit : Real.log (Y / (p * q * r)) = Real.log Y - Real.log (p * q * r) :=
    Real.log_div hY0.ne' (by positivity)
  have hlogα : Real.log (Y ^ (16 / 135 : ℝ)) = (16 / 135) * Real.log Y := Real.log_rpow hY0 _
  rw [hsplit, hlogα, le_div_iff₀ (by nlinarith)]
  nlinarith

/-- Page 285 with Geometry565.triple_three_remainder_argument: a cofactor of size at least
Y^(2/5) has Buchstab argument at least 27/8, above 3. -/
theorem rest_argument_ge_three {Y t : ℝ} (hY : 1 < Y) (ht : Y ^ (2 / 5 : ℝ) ≤ t) :
    3 ≤ Real.log t / Real.log (Y ^ (16 / 135 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hP : 0 < Y ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hY0 _
  have hlY : 0 < Real.log Y := Real.log_pos hY
  have hlog := Real.log_le_log hP ht
  rw [Real.log_rpow hY0] at hlog
  rw [Real.log_rpow hY0, le_div_iff₀ (by positivity : 0 < (16 / 135 : ℝ) * Real.log Y)]
  nlinarith

/-- Page 285 support: on the unselected domain the triple cofactor Y/(pqr) is at least Y^(2/5). -/
theorem rest_triple_cofactor_ge {Y : ℝ} {n : ℕ} (hY : 1 < Y) (pq : ℕ × ℕ)
    (h : pq ∈ pairDomain false Y n) (r : ℕ) (hr : r.Prime) (hrq : (r : ℝ) < pq.2) :
    Y ^ (2 / 5 : ℝ) ≤ Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) := by
  obtain ⟨-, hl⟩ := rest_logs_triple hY pq h
  obtain ⟨-, hp, -, -, hq, -⟩ := mem_filter.mp h
  have hY0 : 0 < Y := by linarith
  have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < pq.2 := by exact_mod_cast hq.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hlr := Real.log_lt_log hr0 hrq
  have hcast : ((pq.1 * pq.2 * r : ℕ) : ℝ) = (pq.1 : ℝ) * pq.2 * r := by push_cast; ring
  rw [hcast]
  have hprod : (pq.1 : ℝ) * pq.2 * r ≤ Y ^ (3 / 5 : ℝ) := by
    rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hY0 _),
      Real.log_mul (by positivity) hr0.ne', Real.log_mul hp0.ne' hq0.ne', Real.log_rpow hY0]
    linarith
  rw [le_div_iff₀ (by positivity)]
  calc Y ^ (2 / 5 : ℝ) * ((pq.1 : ℝ) * pq.2 * r) ≤ Y ^ (2 / 5 : ℝ) * Y ^ (3 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = Y := by rw [← Real.rpow_add hY0]; norm_num

/-- PROVED, formerly LEAF: Jia page 284 after display 63 transferred to the page 285 remaining regions, the model triple count to prime sum comparison. MEDIUM.
CONDITIONAL ON the explicit Buchstab existence, Lemma 20 and Lemma 21 inputs.
The argument ranges are Geometry565.triple_four_argument and
Geometry565.triple_three_remainder_argument. Only individual rough counts are replaced. -/
theorem triple_rough_upper_rest
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        tripleMass true false 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ)) ≤
          (triplePrimeModelRest Y n + η) * (Y / log Y) := by
  intro η hη
  obtain ⟨w, hw, hi, hrec⟩ := hex
  set η₁ : ℝ := η / 93312 with hη₁def
  have hη₁ : 0 < η₁ := by rw [hη₁def]; positivity
  obtain ⟨T0, Z0, hT0, hZ0, hcount⟩ := h21 w hw hi hrec η₁ hη₁
  obtain ⟨Y1, h1⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).eventually
      (Filter.eventually_ge_atTop T0))
  obtain ⟨Y2, h2⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 16 / 135)).eventually
      (Filter.eventually_ge_atTop Z0))
  obtain ⟨Y3, h3⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (280 : ℝ)))
  refine ⟨max 2 (max Y1 (max Y2 Y3)), ?_⟩
  intro Y hY n hn
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hYa : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYb : Y2 ≤ Y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYc : Y3 ≤ Y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hlog : 28 ≤ (1 / 10 : ℝ) * log Y := by linarith [h3 Y hYc]
  have hlY : 0 < log Y := Real.log_pos hY1
  have hA0 : 0 ≤ (135 / 16) * (Y / log Y) := by positivity
  set A : ℝ := (135 / 16) * (Y / log Y) with hAdef
  have hterm : ∀ pq ∈ pairDomain false Y n,
      ∀ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1
          (Y ^ (16 / 135 : ℝ))).card : ℝ) ≤
        A * ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
          then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))) +
        η₁ * A * (1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))) := by
    intro pq hpq r hr
    obtain ⟨-, hrp, hra, hrq⟩ := mem_filter.mp hr
    obtain ⟨-, hp, hpa, -, hq, hqa, hqp, -⟩ := mem_filter.mp hpq
    have hqp' : (pq.2 : ℝ) < pq.1 := lt_of_lt_of_le hqp (min_le_left _ _)
    have hrqN : r < pq.2 := by exact_mod_cast hrq
    have hqpN : pq.2 < pq.1 := by exact_mod_cast hqp'
    have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < pq.2 := by exact_mod_cast hq.pos
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hrp.pos
    have hcof := rest_triple_cofactor_ge hY1 pq hpq r hrp hrq
    have hcast : ((pq.1 * pq.2 * r : ℕ) : ℝ) = (pq.1 : ℝ) * pq.2 * r := by push_cast; ring
    set t : ℝ := Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) with htdef
    have htT : T0 ≤ t := (h1 Y hYa).trans hcof
    have hzt : Y ^ (16 / 135 : ℝ) ≤ t :=
      (Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num)).trans hcof
    have hc' := hcount t (Y ^ (16 / 135 : ℝ)) htT (h2 Y hYb) hzt
    have hres := triple_rescale_card_le Y n hp hq hrp hrqN hqpN hY0
    have hnorm : t / Real.log (Y ^ (16 / 135 : ℝ)) =
        A * (1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))) := by
      rw [htdef, hcast, cofactor_normalization hY1 (by positivity)]
    have hs : 0 ≤ t / Real.log (Y ^ (16 / 135 : ℝ)) := by
      rw [hnorm]; positivity
    have hwle : w (Real.log t / Real.log (Y ^ (16 / 135 : ℝ))) ≤
        (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
          then 0.5617 else 0.5644) := by
      split_ifs with hsmall
      · have := triple_rest_argument_ge_four hY1 hp0 hq0 hr0 hrq hsmall
        rw [htdef, hcast]
        exact ((h20 w hw hi hrec).2 _ this).2
      · exact (h20 w hw hi hrec).1 _ (rest_argument_ge_three hY1 hcof)
    have hup := (abs_le.mp hc').2
    have hm := mul_le_mul_of_nonneg_right hwle hs
    have hcard : ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1
          (Y ^ (16 / 135 : ℝ))).card : ℝ) ≤
        ((sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
      exact_mod_cast hres
    have hdiv : (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
          then (0.5617 : ℝ) else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) =
        (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
          then (0.5617 : ℝ) else 0.5644) * (1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))) := by
      rw [mul_one_div]
    rw [hnorm] at hm hup
    rw [hdiv]
    nlinarith
  rw [tripleMass_rest_eq]
  have hC := rest_triple_recip_le (n := n) hY1 hlog
  calc _ ≤ ∑ pq ∈ pairDomain false Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        (A * ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
          then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))) +
        η₁ * A * (1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)))) :=
        sum_le_sum fun pq h => sum_le_sum fun r hr => hterm pq h r hr
    _ = (Y / log Y) * triplePrimeModelRest Y n + η₁ * A *
        ∑ pq ∈ pairDomain false Y n,
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) := by
        simp only [sum_add_distrib, ← mul_sum, triplePrimeModelRest, hAdef]
        ring
    _ ≤ (Y / log Y) * triplePrimeModelRest Y n + η₁ * A * 5832 := by
        have : 0 ≤ η₁ * A := mul_nonneg hη₁.le hA0
        nlinarith
    _ ≤ (triplePrimeModelRest Y n + η) * (Y / log Y) := by
        have hb : η₁ * A * 5832 ≤ η * (Y / log Y) := by
          rw [hAdef, hη₁def]
          have : 0 ≤ Y / log Y := by positivity
          nlinarith
        nlinarith


/-- SPLIT, formerly LEAF: Jia page 285 remaining region formula, the triple prime sum to the three reduced logarithmic integrals restOne, restTwo and restThree. HARD.
CONDITIONAL ON Feed565bF.tripleProductSum_upper, HARD; the domain inclusion Feed565bF.triple_rest_le_product is proved, S140.
Only the weighted reciprocal triple prime sum over the unselected domain is estimated. -/
theorem triple_prime_sum_upper_rest :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        triplePrimeModelRest Y n ≤ restOne + restTwo + restThree + η :=
  Feed565bF.triple_prime_sum_upper_rest_from_leaves

/-- Page 285 support: the B triple mass has no dependence on the ambient prime location N. -/
theorem triple_model_independent_rest (N Y : ℝ) (n : ℕ) (α z : ℝ) :
    tripleMass true false N Y n α z = tripleMass true false 0 Y n α z := by rfl

/-- Jia pages 284 and 285: exact type of Decomp565b.model_triple_upper.
CONDITIONAL ON the two leaves above and the Buchstab inputs of Decomp578c.
The model estimate is pointwise for large N, so its exceptional set is empty. -/
theorem model_triple_upper_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        (restOne + restTwo + restThree + 0.0000001) * scale N (localization N ε) n < modelTriple false N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := triple_rough_upper_rest buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.00000005 (by norm_num)
  obtain ⟨Y2, h2⟩ := triple_prime_sum_upper_rest 0.00000005 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      (restOne + restTwo + restThree + 0.0000001) * scale N (localization N ε) n <
        modelTriple false N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_upper N (localization N ε)
      (triplePrimeModelRest (localization N ε) n + 0.00000005)
      (tripleMass true false 0 (localization N ε) n
        ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : triplePrimeModelRest (localization N ε) n + 0.00000005 ≤
        restOne + restTwo + restThree + 0.0000001 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← triple_model_independent_rest N] at hnorm
    change modelTriple false N (localization N ε) n ≤
      (triplePrimeModelRest (localization N ε) n + 0.00000005) * scale N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms triplePrimeModelRest
#print axioms rest_logs_triple
#print axioms rest_prime_recip_le
#print axioms rest_triple_recip_le
#print axioms tripleMass_rest_eq
#print axioms rest_triple_cofactor_ge
#print axioms triple_rough_upper_rest
#print axioms triple_prime_sum_upper_rest
#print axioms triple_model_independent_rest
#print axioms model_triple_upper_from_leaves
end
end LeanLab.Languasco2004.Feed565bD
