/-
Jia 1996 page 283 display 60 with Lemmas 20 and 21 on pages 261 and 262.
Source https://doi.org/10.4064/aa-77-3-207-287.
Finite rescaling and uniform error summation for the rough pair model.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp588b
import LeanLab.PNTSieve.MertensLower

namespace LeanLab.Languasco2004.Decomp588c
open Real Finset intervalIntegral Source565 Sieve565 Decomp588b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 283 display 60 support: an elementary block bound controls the sum of termwise errors.
This uses the proved lab Mertens block upper bound, with no asymptotic prime input. -/
theorem power_prime_sum_le_six {Y a b : ℝ} (hY : 1 < Y) (hab : a ≤ b) (hb : b ≤ 2 * a)
    (hlog : 28 ≤ a * log Y) :
    (∑ p ∈ powerPrimes Y a b, (1 : ℝ) / p) ≤ 6 := by
  let X := Y ^ a
  let Z := Y ^ b
  let y := ⌊X⌋₊
  let v := ⌊Z⌋₊
  have hX0 : 0 < X := Real.rpow_pos_of_pos (by linarith) _
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos (by linarith) _
  have hLX : 28 ≤ log X := by simpa only [X, Real.log_rpow (by linarith : 0 < Y)] using hlog
  have hX29 : 29 ≤ X := by linarith [Real.log_le_sub_one_of_pos hX0]
  have hy2 : 2 ≤ y := Nat.le_floor (by linarith : (2 : ℝ) ≤ X)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hyX : X / 2 ≤ (y : ℝ) := by
    have h := Nat.lt_floor_add_one X
    change X < (y : ℝ) + 1 at h
    linarith
  have hlogy : log X - 1 ≤ log y := by
    have h := Real.log_le_log (by positivity : 0 < X / 2) hyX
    rw [Real.log_div hX0.ne' (by norm_num)] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hyv : y ≤ v := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hY.le hab)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < y) hyv)
  have hlogv : log v ≤ 2 * log X := by
    have h1 := Real.log_le_log hv0 (Nat.floor_le hZ0.le)
    have hlY : 0 ≤ log Y := (Real.log_pos hY).le
    have h2 := mul_le_mul_of_nonneg_right hb hlY
    dsimp [Z, X] at *
    rw [Real.log_rpow (by linarith : 0 < Y)] at h1 ⊢
    linarith
  have hB := LeanLab.PNTSieve.Mertens.sum_inv_primes_block y v hy2 hyv
  have hly' : 0 < log y := by linarith
  change (∑ p ∈ (Ioc y v).filter Nat.Prime, (1 : ℝ) / p) ≤ 6
  apply hB.trans
  rw [div_le_iff₀ hly']
  linarith

/-- Page 283 display 60 support: uniform bound on the reciprocal selected pair sum. -/
theorem pair_reciprocal_le {Y : ℝ} {n : ℕ} (hY : 1 < Y) (hn : 2 * Y ≤ (n : ℝ))
    (hlog : 28 ≤ (16 / 135 : ℝ) * log Y) :
    (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) ≤ 36 := by
  have hS := power_prime_sum_le_six hY
    (by norm_num : (16 / 135 : ℝ) ≤ 89 / 462 - 0.00000001)
    (by norm_num : (89 / 462 - 0.00000001 : ℝ) ≤ 2 * (16 / 135)) hlog
  have hS0 : 0 ≤ ∑ p ∈ powerPrimes Y (16 / 135) (89 / 462 - 0.00000001), (1 : ℝ) / p :=
    sum_nonneg (fun p _ => by positivity)
  have hD0 : 0 ≤ ∑ p ∈ powerPrimes Y (16 / 135) (89 / 462 - 0.00000001), ((1 : ℝ) / p)^2 :=
    sum_nonneg (fun p _ => sq_nonneg _)
  rw [pair_reciprocal_eq hY hn]
  nlinarith

/-- Page 283 display 60 support: multiply a rough cofactor by its two large prime factors.
The finite cap n at least 2Y retains every image integer. -/
theorem pair_rescale_card_ge {Y z : ℝ} {n p q : ℕ} (hY : 0 < Y)
    (hn : 2 * Y ≤ (n : ℝ)) (hp : p.Prime) (hq : q.Prime)
    (hpz : z < (p : ℝ)) (hqz : z < (q : ℝ)) :
    (sieved (Ioc ⌊Y / ((p * q : ℕ) : ℝ)⌋₊ ⌊2 * (Y / ((p * q : ℕ) : ℝ))⌋₊) 1 z).card ≤
      (sieved (sourceSet true 0 Y n (p * q)) 1 z).card := by
  let d := p * q
  have hd0 : 0 < d := Nat.mul_pos hp.pos hq.pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  apply Finset.card_le_card_of_injOn (fun m => d * m)
  · intro m hm
    obtain ⟨hmI, hmS⟩ := mem_filter.mp hm
    have hlow : Y / (d : ℝ) < (m : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp hmI).1
    have hhigh : (m : ℝ) ≤ 2 * (Y / (d : ℝ)) :=
      (Nat.cast_le.mpr (mem_Ioc.mp hmI).2).trans (Nat.floor_le (by positivity))
    have hdmL : Y < ((d * m : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hdR] at hlow
      push_cast
      nlinarith
    have hdmU : ((d * m : ℕ) : ℝ) ≤ 2 * Y := by
      have h := mul_le_mul_of_nonneg_right hhigh hdR.le
      have he : 2 * (Y / (d : ℝ)) * (d : ℝ) = 2 * Y := by field_simp
      rw [he] at h
      push_cast
      nlinarith
    apply mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right d m, ?_⟩
      · have : (0 : ℝ) < ((d * m : ℕ) : ℝ) := hY.trans hdmL
        have : 0 < d * m := by exact_mod_cast this
        exact this
      · exact_mod_cast hdmU.trans hn
      · simpa only [ite_true] using And.intro hdmL hdmU
    · intro r hr hrz hr1 hrdm
      rcases hr.dvd_mul.mp hrdm with hrd | hrm
      · rcases hr.dvd_mul.mp hrd with hrp | hrq
        · have he : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
          subst r
          linarith
        · have he : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
          subst r
          linarith
      · exact hmS r hr hrz hr1 hrm
  · intro m hm k hk hmk
    exact Nat.eq_of_mul_eq_mul_left hd0 hmk

/-- Page 283 display 60 support: the smallest cofactor grows as a fixed positive power of Y. -/
theorem pair_cofactor_ge_power {Y p q : ℝ} (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hqp : q ≤ p) (hpB : p ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)) :
    Y ^ (1 - 2 * (89 / 462 - 0.00000001) : ℝ) ≤ Y / (p * q) := by
  have hY0 : 0 < Y := by linarith
  have hqB := hqp.trans hpB
  have hprod : p * q ≤ Y ^ (2 * (89 / 462 - 0.00000001) : ℝ) := by
    calc p * q ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) * Y ^ (89 / 462 - 0.00000001 : ℝ) :=
          mul_le_mul hpB hqB hq.le (by positivity)
      _ = Y ^ (2 * (89 / 462 - 0.00000001) : ℝ) := by
          rw [← Real.rpow_add hY0]
          congr 1
          ring
  rw [le_div_iff₀ (mul_pos hp hq)]
  calc Y ^ (1 - 2 * (89 / 462 - 0.00000001) : ℝ) * (p * q) ≤
      Y ^ (1 - 2 * (89 / 462 - 0.00000001) : ℝ) * Y ^ (2 * (89 / 462 - 0.00000001) : ℝ) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = Y := by
      rw [← Real.rpow_add hY0]
      norm_num

/-- Page 283 display 60 support: the pair cofactor argument lies in the global lower bound range. -/
theorem pair_argument_ge_four {Y t : ℝ} (hY : 1 < Y)
    (ht : Y ^ (1 - 2 * (89 / 462 - 0.00000001) : ℝ) ≤ t) :
    4 ≤ log t / log (Y ^ (16 / 135 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hP : 0 < Y ^ (1 - 2 * (89 / 462 - 0.00000001) : ℝ) := Real.rpow_pos_of_pos hY0 _
  have ht0 : 0 < t := hP.trans_le ht
  have hlY : 0 < log Y := Real.log_pos hY
  have hlog := Real.log_le_log hP ht
  rw [Real.log_rpow hY0] at hlog
  rw [Real.log_rpow hY0, le_div_iff₀ (by positivity : 0 < (16 / 135 : ℝ) * log Y)]
  nlinarith [Real.log_pos hY]

/-- Page 283 display 60 support: the cutoff logarithm gives the exact reciprocal weight. -/
theorem cofactor_normalization {Y d : ℝ} (hY : 1 < Y) (hd : 0 < d) :
    (Y / d) / log (Y ^ (16 / 135 : ℝ)) =
      (135 / 16) * (Y / log Y) * (1 / d) := by
  rw [Real.log_rpow (by linarith : 0 < Y)]
  field_simp
  <;> ring

/-- Jia page 283 display 60: exact supplied rough pair lower estimate.
CONDITIONAL ON the explicit source solution existence and Lemmas 20 and 21.
All finite rescaling, argument bounds, normalization and error summation are proved. -/
theorem pair_rough_from_inputs
    (hex : ∃ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) ∧
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) ∧
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t))
    (h20 : ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) →
      (∀ u : ℝ, 3 ≤ u → w u ≤ 0.5644) ∧
      (∀ u : ℝ, 4 ≤ u → 0.5612 ≤ w u ∧ w u ≤ 0.5617))
    (h21 : ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
      ∀ η : ℝ, 0 < η → ∃ T Z : ℝ, 1 < T ∧ 1 < Z ∧
        ∀ t z : ℝ, T ≤ t → Z ≤ z → z ≤ t →
          |((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
              w (log t / log z) * (t / log z)| ≤ η * (t / log z)) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        ((0.5612 * (135 / 16)) *
          (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) - η) * (Y / log Y) ≤
          pairMass true true 0 Y n (Y ^ (16 / 135 : ℝ)) := by
  intro η hη
  let ξ := η / 304
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  obtain ⟨w, hw, hi, hr⟩ := hex
  obtain ⟨T, Z, hT, hZ, hcount⟩ := h21 w hw hi hr ξ hξ
  let c : ℝ := 1 - 2 * (89 / 462 - 0.00000001)
  have hc : 0 < c := by norm_num [c]
  obtain ⟨Y1, h1⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hc).eventually (Filter.eventually_ge_atTop T))
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
  have hYb : Y2 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYc : Y3 ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hlog : 28 ≤ (16 / 135 : ℝ) * log Y := by linarith [h3 Y hYc]
  have hscale : 0 ≤ Y / log Y := div_nonneg (by linarith) (Real.log_pos hY1).le
  have hsum := pair_reciprocal_le hY1 hn hlog
  have herr : (ξ * (135 / 16)) *
      (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) ≤ η := by
    calc _ ≤ (ξ * (135 / 16)) * 36 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ η := by dsimp [ξ]; linarith
  have hterms : ∀ pq ∈ pairDomain true Y n,
      (0.5612 - ξ) * ((Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) / log (Y ^ (16 / 135 : ℝ))) ≤
        ((sieved (sourceSet true 0 Y n (pq.1 * pq.2)) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
    intro pq hpq
    obtain ⟨hcap, hp, hpa, hpS, hq, hqa, hqp, hg, hreg, hB⟩ := mem_filter.mp hpq
    have hp0 : (0 : ℝ) < pq.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < pq.2 := by exact_mod_cast hq.pos
    have hqp' : (pq.2 : ℝ) ≤ pq.1 := (lt_of_lt_of_le hqp (min_le_left _ _)).le
    have hcof := pair_cofactor_ge_power hY1 hp0 hq0 hqp' (hB rfl)
    have htT : T ≤ Y / ((pq.1 : ℝ) * (pq.2 : ℝ)) := (h1 Y hYa).trans hcof
    have hzt : Y ^ (16 / 135 : ℝ) ≤ Y / ((pq.1 : ℝ) * (pq.2 : ℝ)) :=
      (Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num [c])).trans hcof
    have hc' := hcount (Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) (Y ^ (16 / 135 : ℝ))
      htT (h2 Y hYb) hzt
    have hwlow := ((h20 w hw hi hr).2 _ (pair_argument_ge_four hY1 hcof)).1
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
  have heq : (∑ pq ∈ pairDomain true Y n,
      (0.5612 - ξ) * ((Y / ((pq.1 : ℝ) * (pq.2 : ℝ))) / log (Y ^ (16 / 135 : ℝ)))) =
      ((0.5612 * (135 / 16)) *
        (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) -
        (ξ * (135 / 16)) *
        (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)))) * (Y / log Y) := by
    calc _ = ((0.5612 - ξ) * (135 / 16) * (Y / log Y)) *
        (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) := by
          rw [mul_sum]
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
  change _ ≤ ∑ pq ∈ pairDomain true Y n,
    ((sieved (sourceSet true 0 Y n (pq.1 * pq.2)) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ)
  exact (mul_le_mul_of_nonneg_right (by linarith :
    (0.5612 * (135 / 16)) * (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) - η ≤
      (0.5612 * (135 / 16)) * (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) -
        (ξ * (135 / 16)) * (∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)))) hscale).trans hsumterms

#print axioms pair_cofactor_ge_power
#print axioms pair_argument_ge_four
#print axioms cofactor_normalization
#print axioms pair_rough_from_inputs
#print axioms power_prime_sum_le_six
#print axioms pair_reciprocal_le
#print axioms pair_rescale_card_ge
end
end LeanLab.Languasco2004.Decomp588c
