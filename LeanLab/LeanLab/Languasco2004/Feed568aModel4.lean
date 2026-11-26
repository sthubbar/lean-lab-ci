/-
Jia 1996 pages 262 and 279, Lemma 21 and the Omega4 model after displays 53 to 56:
split of `Decomp568a.model4_asymptotic` into the uniform rough count, the weight bound
and the prime double sum against the Buchstab integral.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
pair_weight_upper is PROVED from the explicit Mertens block bound of Decomp1528b.
The LEAF inputs rough_count_lower and kernel_sum_lower remain OPEN; the assembly below is
proved from the three leaves.
-/
import LeanLab.Languasco2004.Decomp568a
import LeanLab.AlmostPrimes.Decomp1528b

namespace LeanLab.Languasco2004.Feed568aModel4
open Finset Real Decomp568a BuchstabInitial316
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 262, Lemma 21, the Buchstab asymptotic for rough integers,
applied uniformly to the Omega4 pairs of page 279. HARD.
For q < p primes of the Omega4 domain, the multiples a of p q in the interval Y to 2Y
free of primes below q are m p q with m in the interval Y / p q to 2 Y / p q free of
primes below q; the exponent log of Y / p q over log q lies in 17/8 to 3, where the
explicit initial Buchstab formula holds, so the count is at least the main term
minus η times Y / p q log q for all large Y, uniformly in the pair. -/
theorem rough_count_lower :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ p q : ℕ, p.Prime → q.Prime →
      Y ^ (41 / 180 : ℝ) < (p : ℝ) → (p : ℝ) ≤ Y ^ (8 / 33 : ℝ) →
      (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) → (q : ℝ) < p →
      (buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) - η) *
          (Y / ((p : ℝ) * q * Real.log q)) ≤ (modelSifted Y (p * q) q : ℝ) := by
  sorry

/-- LEAF: Jia page 279, the error weights of Lemma 21 summed over the Omega4 pairs are
of the order Y / log Y. HARD.
Here log q is at least 211/990 log Y and the reciprocal prime sums over the dyadic
ranges of p and q are bounded by Mertens' theorem. -/
theorem pair_weight_upper :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          Y / ((p : ℝ) * q * Real.log q) ≤ K * (Y / Real.log Y) := by
  refine ⟨4 * (990 / 211), by norm_num, Real.exp 19, ?_⟩
  intro Y hY
  have hY1 : 1 < Y := by
    have := Real.add_one_lt_exp (by norm_num : (19 : ℝ) ≠ 0)
    linarith
  have hY0 : 0 < Y := by linarith
  have hL : 19 ≤ Real.log Y := by
    have := Real.log_le_log (Real.exp_pos 19) hY
    rwa [Real.log_exp] at this
  set L := Real.log Y with hLdef
  have hLpos : 0 < L := by linarith
  set a := Y ^ (211 / 990 : ℝ) with ha
  set b := Y ^ (8 / 33 : ℝ) with hb
  have hapos : 0 < a := Real.rpow_pos_of_pos hY0 _
  have hbpos : 0 < b := Real.rpow_pos_of_pos hY0 _
  have hla : Real.log a = 211 / 990 * L := Real.log_rpow hY0 _
  have hlb : Real.log b = 8 / 33 * L := Real.log_rpow hY0 _
  have hla4 : 4 ≤ Real.log a := by rw [hla]; linarith
  have ha2 : 2 ≤ a := by
    have h1 := Real.exp_log hapos
    have h2 := Real.exp_le_exp.mpr hla4
    have h3 := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num)
  set T := (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime with hT
  set S := ∑ n ∈ T, (1 : ℝ) / n with hS
  have hS2 : S ≤ 2 := by
    have h := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block ha2 hab
    have h1 := (abs_le.mp h).2
    have hll : Real.log (Real.log b) - Real.log (Real.log a) ≤ 1 := by
      rw [← Real.log_div (by rw [hlb]; positivity) (by rw [hla]; positivity), hlb, hla]
      have e : 8 / 33 * L / (211 / 990 * L) = 240 / 211 := by
        have := hLpos.ne'; field_simp; ring
      rw [e]
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 240 / 211)
      linarith
    have h4 : 4 / Real.log a ≤ 1 := by rw [div_le_one (by linarith)]; exact hla4
    linarith
  have hS0 : 0 ≤ S := sum_nonneg (fun _ _ => by positivity)
  set c := 990 / 211 * (Y / L) with hc
  have hc0 : 0 ≤ c := by positivity
  have memT : ∀ n : ℕ, n.Prime → a < n → (n : ℝ) ≤ b → n ∈ T := by
    intro n hn h1 h2
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt hapos.le).mpr h1, Nat.le_floor h2⟩, hn⟩
  have hab' : a = b⁻¹ * Y ^ (41 / 90 : ℝ) := by
    rw [ha, hb, ← Real.rpow_neg hY0.le, ← Real.rpow_add hY0]
    norm_num
  have hqa : ∀ p q : ℕ, 0 < (p : ℝ) → (p : ℝ) ≤ b →
      (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < q → a < q := by
    intro p q hp hpb hq
    rw [hab']
    calc b⁻¹ * Y ^ (41 / 90 : ℝ) ≤ (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hp hpb) (by positivity)
      _ < q := hq
  have step1 :
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ b),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          Y / ((p : ℝ) * q * Real.log q) ≤
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ b), c * (1 / (p : ℝ)) * S := by
    apply sum_le_sum
    intro p hp
    obtain ⟨_, hpP, _, hp2⟩ := mem_filter.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    rw [hS, mul_sum]
    refine (sum_le_sum ?_).trans (sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · intro q hq
      obtain ⟨_, hqP, hq1, _⟩ := mem_filter.mp hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hqP.pos
      have haq := hqa p q hp0 hp2 hq1
      have hlq : 211 / 990 * L ≤ Real.log q := by
        rw [← hla]; exact Real.log_le_log hapos haq.le
      have e : c * (1 / (p : ℝ)) * (1 / (q : ℝ)) = Y / ((p : ℝ) * q * (211 / 990 * L)) := by
        have := hp0.ne'; have := hq0.ne'; have := hLpos.ne'
        rw [hc]; field_simp
      rw [e]
      exact div_le_div_of_nonneg_left hY0.le (by positivity)
        (mul_le_mul_of_nonneg_left hlq (by positivity))
    · intro q hq
      obtain ⟨_, hqP, hq1, hq2⟩ := mem_filter.mp hq
      exact memT q hqP (hqa p q hp0 hp2 hq1) (hq2.le.trans hp2)
    · intro q _ _
      positivity
  have step2 :
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ b), c * (1 / (p : ℝ)) * S ≤
      ∑ p ∈ T, c * (1 / (p : ℝ)) * S := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨_, hpP, hp1, hp2⟩ := mem_filter.mp hp
      have hA : a ≤ Y ^ (41 / 180 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num)
      exact memT p hpP (hA.trans_lt hp1) hp2
    · intro p _ _
      positivity
  have step3 : ∑ p ∈ T, c * (1 / (p : ℝ)) * S = c * S * S := by
    rw [← sum_mul, ← mul_sum]
  have hSS : S * S ≤ 4 := by nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = c * S * S := step3
    _ ≤ c * 4 := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hSS hc0
    _ = 4 * (990 / 211) * (Y / L) := by rw [hc]; ring

/-- LEAF: Jia page 279 after displays 53 to 56, the prime double sum of the Buchstab main
terms is at least the Omega4 integral times Y / log Y for large Y. HARD.
With t = log p / log Y and u = log q / log Y the summand is Y / log Y times
the kernel of `Kernel568.region4_kernel` divided by p q, and the prime number theorem
with partial summation turns the double reciprocal prime sum into the integral `integral4`. -/
theorem kernel_sum_lower :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (integral4 - η) * (Y / Real.log Y) ≤
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) *
            (Y / ((p : ℝ) * q * Real.log q)) := by
  sorry

/-- Jia page 279: the exact statement of `Decomp568a.model4_asymptotic`, proved from the
LEAF inputs `rough_count_lower`, `pair_weight_upper` and `kernel_sum_lower`. -/
theorem model4_asymptotic_from_leaves :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (integral4 - η) * (Y / Real.log Y) ≤ model4 Y := by
  intro η hη
  obtain ⟨K, hK, Y1, hW⟩ := pair_weight_upper
  obtain ⟨Y2, hM⟩ := kernel_sum_lower (η / 2) (by positivity)
  have hη' : 0 < η / (2 * (K + 1)) := by positivity
  obtain ⟨Y3, hR⟩ := rough_count_lower (η / (2 * (K + 1))) hη'
  refine ⟨max 1 (max Y1 (max Y2 Y3)), ?_⟩
  intro Y hY
  have hY0 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hY2 : Y2 ≤ Y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hY3 : Y3 ≤ Y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  set e := η / (2 * (K + 1)) with he
  have hpair :
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          (buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) - e) *
            (Y / ((p : ℝ) * q * Real.log q)) ≤ model4 Y := by
    unfold model4
    apply sum_le_sum
    intro p hp
    obtain ⟨_, hpP, hp1, hp2⟩ := mem_filter.mp hp
    apply sum_le_sum
    intro q hq
    obtain ⟨_, hqP, hq1, hq2⟩ := mem_filter.mp hq
    exact hR Y hY3 p q hpP hqP hp1 hp2 hq1 hq2
  have hexp :
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          (buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) - e) *
            (Y / ((p : ℝ) * q * Real.log q)) =
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) *
            (Y / ((p : ℝ) * q * Real.log q)) -
      e * ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          Y / ((p : ℝ) * q * Real.log q) := by
    simp only [sub_mul, sum_sub_distrib, mul_sum]
  have hWY := hW Y hY1
  have hMY := hM Y hY2
  have hs : 0 ≤ Y / Real.log Y := div_nonneg (by linarith) (Real.log_nonneg hY0)
  have heK : e * K ≤ η / 2 := by
    rw [he, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hfin := mul_le_mul_of_nonneg_left hWY hη'.le
  have hfin2 := mul_le_mul_of_nonneg_right heK hs
  rw [hexp] at hpair
  nlinarith

#print axioms rough_count_lower
#print axioms pair_weight_upper
#print axioms kernel_sum_lower
#print axioms model4_asymptotic_from_leaves
end
end LeanLab.Languasco2004.Feed568aModel4
