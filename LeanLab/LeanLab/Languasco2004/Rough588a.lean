/-
Jia 1996 page 262 Lemma 21 and page 261 displays 40 and 41.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp588a.rough_below_square_root into two cited leaves:
the uniform Buchstab count of rough integers up to x, the source Lemma 5 of reference 9,
and the Lipschitz regularity of the Buchstab function from displays 40 and 41.
The dyadic interval form is then proved from the leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Sieve565
import LeanLab.Languasco2004.Buchstab578

namespace LeanLab.Languasco2004.Rough588a
open Real Finset intervalIntegral
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 262 Lemma 21, the cited Lemma 5 of reference 9 in its initial segment form. HARD.
Uniform Buchstab asymptotic for the count of integers in the range one to x free of primes below z,
for z at least Z and z squared at most 2 x. This is the de Bruijn form, Tenenbaum III.6 Theorem 3,
where the term z over log z is absorbed by the tolerance since z squared is at most 2 x.
The proof is the induction on u through the Buchstab identity with the prime number theorem base. -/
theorem rough_initial_asymptotic :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ X Z : ℝ, 1 < X ∧ 1 < Z ∧
      ∀ x z : ℝ, X ≤ x → Z ≤ z → z ^ 2 ≤ 2 * x →
        |((Sieve565.sieved (Ioc 0 ⌊x⌋₊) 1 z).card : ℝ) -
            w (log x / log z) * (x / log z)| ≤ η * (x / log z) := by sorry

/-- LEAF: Jia page 261 displays 40 and 41, Lipschitz regularity of the Buchstab function. MEDIUM.
On the segment one to two w is 1 over u with derivative bounded by one, and beyond two
display 41 gives the derivative as w of u minus one minus w of u, all over u, which is bounded
once w is bounded by one, itself an induction on display 41. -/
theorem buchstab_lipschitz :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → |w u - w v| ≤ L * |u - v| := by
  intro w hw hi hr
  have hint : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable w MeasureTheory.volume a b := by
    intro a b ha hb
    refine (hw.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.mem_uIcc] at hx
    simp only [Set.mem_Ici]
    rcases hx with hx | hx <;> linarith [hx.1]
  -- display 41 by induction: w is bounded by one on [1, n + 2]
  have hb : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → |w u| ≤ 1 := by
    intro n
    induction n with
    | zero =>
      intro u h1 h2
      rw [hi u h1 (by simpa using h2), abs_of_pos (by positivity)]
      rw [div_le_one (by linarith)]; exact h1
    | succ k ih =>
      intro u h1 h2
      by_cases hu : u ≤ (k : ℝ) + 2
      · exact ih u h1 hu
      push Not at hu
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have u2 : 2 ≤ u := by linarith
      have heq := hr u u2
      have hI : ‖∫ s in (1 : ℝ)..(u - 1), w s‖ ≤ 1 * |u - 1 - 1| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [Set.uIoc_of_le (by linarith)] at hx
        rw [Real.norm_eq_abs]
        exact ih x (by linarith [hx.1]) (by push_cast at h2; linarith [hx.2])
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - 1 - 1)] at hI
      have hu0 : 0 < u := by linarith
      have hwu : w u = (1 + ∫ s in (1 : ℝ)..(u - 1), w s) / u := by
        field_simp; linarith
      rw [hwu, abs_div, abs_of_pos hu0, div_le_one hu0]
      calc |1 + ∫ s in (1 : ℝ)..(u - 1), w s| ≤ |(1 : ℝ)| + |∫ s in (1 : ℝ)..(u - 1), w s| :=
            abs_add_le _ _
        _ ≤ u := by rw [abs_one]; linarith
  have hB : ∀ u : ℝ, 1 ≤ u → |w u| ≤ 1 := fun u hu =>
    hb ⌈u⌉₊ u hu (by have := Nat.le_ceil u; linarith)
  -- display 41: beyond two, the difference quotient is bounded
  have h2 : ∀ u v : ℝ, 2 ≤ u → 2 ≤ v → |w u - w v| ≤ |u - v| := by
    intro u v hu hv
    have hdiff : u * w u - v * w v = ∫ s in (v - 1)..(u - 1), w s := by
      rw [hr u hu, hr v hv, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (hint 1 (u - 1) le_rfl (by linarith))
          (hint 1 (v - 1) le_rfl (by linarith))]
    have hI : ‖∫ s in (v - 1)..(u - 1), w s‖ ≤ 1 * |u - 1 - (v - 1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs]
      apply hB
      have := hx.1
      have : 1 ≤ min (v - 1) (u - 1) := le_min (by linarith) (by linarith)
      linarith
    rw [Real.norm_eq_abs, ← hdiff, one_mul, show u - 1 - (v - 1) = u - v by ring] at hI
    have hu0 : 0 < u := by linarith
    have hkey : w u - w v = ((u * w u - v * w v) - (u - v) * w v) / u := by
      field_simp; ring
    rw [hkey, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    have hv1 : |(u - v) * w v| ≤ |u - v| := by
      rw [abs_mul]
      have := hB v (by linarith)
      nlinarith [abs_nonneg (u - v)]
    calc |u * w u - v * w v - (u - v) * w v|
        ≤ |u * w u - v * w v| + |(u - v) * w v| := abs_sub _ _
      _ ≤ |u - v| + |u - v| := add_le_add hI hv1
      _ ≤ |u - v| * u := by nlinarith [abs_nonneg (u - v)]
  -- display 40: on the segment one to two, w is 1 over u
  have h1 : ∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 1 ≤ v → v ≤ 2 → |w u - w v| ≤ |u - v| := by
    intro u v hu1 hu2 hv1 hv2
    rw [hi u hu1 hu2, hi v hv1 hv2]
    have hu0 : 0 < u := by linarith
    have hv0 : 0 < v := by linarith
    rw [div_sub_div _ _ hu0.ne' hv0.ne', abs_div, abs_of_pos (mul_pos hu0 hv0),
      div_le_iff₀ (mul_pos hu0 hv0), one_mul, mul_one, abs_sub_comm v u]
    have huv : 1 ≤ u * v := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left huv (abs_nonneg (u - v))]
  refine ⟨2, by norm_num, ?_⟩
  -- mixed case: through the point two
  have hmix : ∀ u v : ℝ, 1 ≤ u → u ≤ 2 → 2 ≤ v → |w u - w v| ≤ 2 * |u - v| := by
    intro u v hu1 hu2 hv
    have ha := h1 u 2 hu1 hu2 (by norm_num) le_rfl
    have hc := h2 2 v le_rfl hv
    calc |w u - w v| ≤ |w u - w 2| + |w 2 - w v| := abs_sub_le _ _ _
      _ ≤ |u - 2| + |2 - v| := add_le_add ha hc
      _ ≤ 2 * |u - v| := by
        rw [abs_of_nonpos (by linarith : u - 2 ≤ 0), abs_of_nonpos (by linarith : 2 - v ≤ 0),
          abs_of_nonpos (by linarith : u - v ≤ 0)]
        linarith
  intro u v hu hv
  rcases le_total u 2 with hu2 | hu2 <;> rcases le_total v 2 with hv2 | hv2
  · linarith [h1 u v hu hu2 hv hv2, abs_nonneg (u - v)]
  · exact hmix u v hu hu2 hv2
  · rw [abs_sub_comm, abs_sub_comm u v]; exact hmix v u hv hv2 hu2
  · linarith [h2 u v hu2 hv2, abs_nonneg (u - v)]

/-- Page 262 Lemma 21 support: the dyadic rough count is a difference of two initial counts. -/
theorem dyadic_card_sub {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) =
      ((Sieve565.sieved (Ioc 0 ⌊2 * t⌋₊) 1 z).card : ℝ) -
        ((Sieve565.sieved (Ioc 0 ⌊t⌋₊) 1 z).card : ℝ) := by
  have hab : ⌊t⌋₊ ≤ ⌊2 * t⌋₊ := Nat.floor_mono (by linarith)
  have hU : Ioc 0 ⌊2 * t⌋₊ = Ioc 0 ⌊t⌋₊ ∪ Ioc ⌊t⌋₊ ⌊2 * t⌋₊ :=
    (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab).symm
  have hD : Disjoint (Ioc 0 ⌊t⌋₊) (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact absurd (mem_Ioc.mp ha).2 (not_le.mpr (mem_Ioc.mp hb).1)
  have hc : (Sieve565.sieved (Ioc 0 ⌊2 * t⌋₊) 1 z).card =
      (Sieve565.sieved (Ioc 0 ⌊t⌋₊) 1 z).card +
        (Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card := by
    unfold Sieve565.sieved
    rw [hU, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hD)]
  rw [hc]; push_cast; ring

/-- Jia page 262 Lemma 21 below the square root cutoff, proved from the two leaves above.
CONDITIONAL ON rough_initial_asymptotic and buchstab_lipschitz.
Same type as Decomp588a.rough_below_square_root. -/
theorem rough_below_square_root_from_leaves :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ T Z : ℝ, 1 < T ∧ 1 < Z ∧
      ∀ t z : ℝ, T ≤ t → Z ≤ z → z ≤ t → z ^ 2 ≤ 2 * t →
        |((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
            w (log t / log z) * (t / log z)| ≤ η * (t / log z) := by
  intro w hw hi hr η hη
  obtain ⟨X, Z, hX, hZ, hA⟩ := rough_initial_asymptotic w hw hi hr (η / 8) (by positivity)
  obtain ⟨L, hL0, hL⟩ := buchstab_lipschitz w hw hi hr
  set K : ℝ := 4 * L * log 2 / η
  refine ⟨X, max Z (exp K), hX, hZ.trans_le (le_max_left _ _), ?_⟩
  intro t z ht hz hzt hsq
  have hz1 : 1 < z := hZ.trans_le ((le_max_left _ _).trans hz)
  have hlz : 0 < log z := Real.log_pos hz1
  have hKz : K ≤ log z := by
    have := (le_max_right Z (exp K)).trans hz
    calc K = log (exp K) := (Real.log_exp K).symm
      _ ≤ log z := Real.log_le_log (exp_pos K) this
  have ht0 : 0 < t := by linarith
  have h2t : X ≤ 2 * t := by linarith
  have hE1 := hA t z ht ((le_max_left _ _).trans hz) hsq
  have hE2 := hA (2 * t) z h2t ((le_max_left _ _).trans hz) (by linarith)
  have hu1 : 1 ≤ log t / log z :=
    (le_div_iff₀ hlz).mpr (by simpa using Real.log_le_log (by linarith) hzt)
  have hlog2t : log (2 * t) = log 2 + log t := Real.log_mul (by norm_num) ht0.ne'
  have hu2 : log (2 * t) / log z = log t / log z + log 2 / log z := by
    rw [hlog2t, add_div, add_comm]
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hu2' : 1 ≤ log (2 * t) / log z := by
    rw [hu2]; have : 0 ≤ log 2 / log z := by positivity
    linarith
  have hLip := hL _ _ hu2' hu1
  rw [hu2, add_sub_cancel_left, abs_of_pos (by positivity : 0 < log 2 / log z)] at hLip
  rw [← hu2] at hLip
  have hsmall : L * (log 2 / log z) ≤ η / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hlz]
    have hK : 4 * L * log 2 / η ≤ log z := hKz
    rw [div_le_iff₀ hη] at hK
    nlinarith
  set M : ℝ := t / log z with hM
  have hM0 : 0 < M := by positivity
  have h2M : 2 * t / log z = 2 * M := by rw [hM]; ring
  rw [h2M] at hE2
  rw [dyadic_card_sub ht0.le z]
  set w1 := w (log t / log z)
  set w2 := w (log (2 * t) / log z)
  set P1 := ((Sieve565.sieved (Ioc 0 ⌊t⌋₊) 1 z).card : ℝ)
  set P2 := ((Sieve565.sieved (Ioc 0 ⌊2 * t⌋₊) 1 z).card : ℝ)
  have hd : |w2 - w1| ≤ η / 4 := hLip.trans hsmall
  have hdM : |(w2 - w1) * M| ≤ η / 4 * M := by
    rw [abs_mul, abs_of_pos hM0]
    exact mul_le_mul_of_nonneg_right hd hM0.le
  rw [abs_le] at hE1 hE2 hdM ⊢
  constructor <;> nlinarith [hE1.1, hE1.2, hE2.1, hE2.2, hdM.1, hdM.2]

#print axioms rough_initial_asymptotic
#print axioms buchstab_lipschitz
#print axioms dyadic_card_sub
#print axioms rough_below_square_root_from_leaves
end
end LeanLab.Languasco2004.Rough588a
