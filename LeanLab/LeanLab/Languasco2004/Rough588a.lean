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
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → |w u - w v| ≤ L * |u - v| := by sorry

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
