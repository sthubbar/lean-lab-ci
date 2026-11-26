/-
Jia 1996 page 262 Lemma 21, the cited Lemma 5 of reference 9, initial segment form.
Split of Rough588a.rough_initial_asymptotic into three cited leaves by the two regimes
of the de Bruijn argument, Tenenbaum III.6:
the bounded range of u, done by induction on u through the Buchstab identity with the
prime number theorem base, Tenenbaum III.6 Theorem 3;
the large range of u, where the fundamental lemma of the sieve and the Mertens product
give the count as exp of minus gamma times x over log z, Tenenbaum III.6 Theorem 2 with
Mertens third theorem;
and the limit of the Buchstab function at infinity, Tenenbaum III.6 Theorem 7.
The assembly rough_initial_asymptotic_from_leaves is proved here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Sieve565

namespace LeanLab.Languasco2004.Rough588aSplit
open Real Finset
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Jia page 262 Lemma 21 support, Tenenbaum III.6 display 6.4: the layer of least prime r
in one to N is r times the r rough integers up to N over r. -/
theorem layer_card_eq (N r : ℕ) (hr : r.Prime) :
    (Sieve565.layer (Ioc 0 N) 1 r).card =
      (Sieve565.sieved (Ioc 0 (N / r)) 1 r).card := by
  unfold Sieve565.layer Sieve565.sieved
  have hr0 := hr.pos
  apply Finset.card_nbij' (fun a => a / r) (fun b => r * b)
  · intro a ha
    rw [mem_coe, mem_filter, mem_filter, mem_Ioc] at ha
    rw [mem_coe, mem_filter, mem_Ioc]
    obtain ⟨⟨⟨ha0, haN⟩, hs⟩, hra⟩ := ha
    refine ⟨⟨Nat.div_pos (Nat.le_of_dvd ha0 hra) hr0, Nat.div_le_div_right haN⟩, ?_⟩
    intro p hp hpr h1 hpa
    exact hs p hp hpr h1 (hpa.trans (Nat.div_dvd_of_dvd hra))
  · intro b hb
    rw [mem_coe, mem_filter, mem_Ioc] at hb
    rw [mem_coe, mem_filter, mem_filter, mem_Ioc]
    obtain ⟨⟨hb0, hbN⟩, hs⟩ := hb
    refine ⟨⟨⟨Nat.mul_pos hr0 hb0, (Nat.mul_le_mul_left r hbN).trans (Nat.mul_div_le N r)⟩, ?_⟩,
      dvd_mul_right r b⟩
    intro p hp hpr h1 hpa
    rcases (Nat.Prime.dvd_mul hp).mp hpa with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp hr).mp h
      subst this; exact lt_irrefl _ hpr
    · exact hs p hp hpr h1 h
  · intro a ha
    rw [mem_coe, mem_filter] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro b _
    exact Nat.mul_div_cancel_left b hr0
/-- Jia page 262 Lemma 21 support, the Buchstab identity, Tenenbaum III.6 display 6.4:
the z rough count up to N is the Z rough count plus the sum over primes r in z to Z
of the r rough count up to N over r. -/
theorem buchstab_identity (N : ℕ) (z Z : ℝ) (hz : z ≤ Z) :
    ((Sieve565.sieved (Ioc 0 N) 1 z).card : ℝ) =
      ((Sieve565.sieved (Ioc 0 N) 1 Z).card : ℝ) +
        ∑ r ∈ Sieve565.cutPrimes (Ioc 0 N) 1 z Z,
          ((Sieve565.sieved (Ioc 0 (N / r)) 1 r).card : ℝ) := by
  have h := Sieve565.low_cutoff_cancellation (Ioc 0 N) 1 z Z
    (fun a ha => (mem_Ioc.mp ha).1) hz
  unfold Sieve565.lowLayers at h
  rw [Finset.sum_congr rfl (fun r hr => by
    rw [layer_card_eq N r (mem_filter.mp hr).2.1])] at h
  linarith


/-- LEAF: Jia page 262 Lemma 21, cited Lemma 5 of reference 9, bounded range of u. HARD.
For each fixed bound U on u equal to log x over log z, the count of integers in one to x
free of primes below z is w of u times x over log z up to any tolerance, for z at least Z
and z squared at most 2 x. Tenenbaum III.6 Theorem 3: induction on the integer part of u
through buchstab_identity above,
with the prime number theorem as base for u at most 2. -/
theorem rough_bounded_u :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ U η : ℝ, 0 < η → ∃ X Z : ℝ, 1 < X ∧ 1 < Z ∧
      ∀ x z : ℝ, X ≤ x → Z ≤ z → z ^ 2 ≤ 2 * x → log x ≤ U * log z →
        |((Sieve565.sieved (Ioc 0 ⌊x⌋₊) 1 z).card : ℝ) -
            w (log x / log z) * (x / log z)| ≤ η * (x / log z) := by sorry

/-- LEAF: Jia page 262 Lemma 21, cited Lemma 5 of reference 9, large range of u. HARD.
When log x is at least U times log z with U large, the count of integers in one to x
free of primes below z is exp of minus gamma times x over log z up to any tolerance.
Tenenbaum III.6 Theorem 2, the fundamental lemma form of the count, together with the
Mertens third theorem for the product of one minus 1 over p over p below z. -/
theorem rough_large_u :
    ∀ η : ℝ, 0 < η → ∃ U X Z : ℝ, 1 < X ∧ 1 < Z ∧
      ∀ x z : ℝ, X ≤ x → Z ≤ z → U * log z ≤ log x →
        |((Sieve565.sieved (Ioc 0 ⌊x⌋₊) 1 z).card : ℝ) -
            exp (-eulerMascheroniConstant) * (x / log z)| ≤ η * (x / log z) := by sorry

/-- LEAF: Jia page 261 displays 40 and 41, limit of the Buchstab function. HARD.
Any solution w of displays 40 and 41 tends to exp of minus gamma at infinity,
Tenenbaum III.6 Theorem 7, by the Laplace transform of display 41. -/
theorem buchstab_limit :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ U : ℝ, ∀ u : ℝ, U ≤ u → |w u - exp (-eulerMascheroniConstant)| ≤ η := by
  sorry

/-- Jia page 262 Lemma 21 initial segment form, proved from the three leaves above.
CONDITIONAL ON rough_bounded_u, rough_large_u and buchstab_limit.
Same type as Rough588a.rough_initial_asymptotic. -/
theorem rough_initial_asymptotic_from_leaves :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ X Z : ℝ, 1 < X ∧ 1 < Z ∧
      ∀ x z : ℝ, X ≤ x → Z ≤ z → z ^ 2 ≤ 2 * x →
        |((Sieve565.sieved (Ioc 0 ⌊x⌋₊) 1 z).card : ℝ) -
            w (log x / log z) * (x / log z)| ≤ η * (x / log z) := by
  intro w hw hi hr η hη
  obtain ⟨U1, X1, Z1, hX1, hZ1, hB⟩ := rough_large_u (η / 2) (by positivity)
  obtain ⟨U2, hC⟩ := buchstab_limit w hw hi hr (η / 2) (by positivity)
  obtain ⟨XA, ZA, hXA, hZA, hA⟩ := rough_bounded_u w hw hi hr (max U1 U2) η hη
  refine ⟨max XA X1, max ZA Z1, lt_max_of_lt_left hXA, lt_max_of_lt_left hZA, ?_⟩
  intro x z hx hz hsq
  have hz1 : 1 < z := hZA.trans_le ((le_max_left _ _).trans hz)
  have hlz : 0 < log z := Real.log_pos hz1
  by_cases hU : log x ≤ max U1 U2 * log z
  · exact hA x z ((le_max_left _ _).trans hx) ((le_max_left _ _).trans hz) hsq hU
  push Not at hU
  have hU1 : U1 * log z ≤ log x :=
    (mul_le_mul_of_nonneg_right (le_max_left U1 U2) hlz.le).trans hU.le
  have hU2 : U2 ≤ log x / log z := by
    rw [le_div_iff₀ hlz]
    exact (mul_le_mul_of_nonneg_right (le_max_right U1 U2) hlz.le).trans hU.le
  have hb := hB x z ((le_max_right _ _).trans hx) ((le_max_right _ _).trans hz) hU1
  have hc := hC _ hU2
  have hx0 : 0 < x := by linarith [le_max_left XA X1]
  set M : ℝ := x / log z
  have hM0 : 0 < M := by positivity
  have hcM : |(w (log x / log z) - exp (-eulerMascheroniConstant)) * M| ≤ η / 2 * M := by
    rw [abs_mul, abs_of_pos hM0]
    exact mul_le_mul_of_nonneg_right hc hM0.le
  rw [abs_le] at hb hcM ⊢
  constructor <;> nlinarith [hb.1, hb.2, hcM.1, hcM.2]

#print axioms layer_card_eq
#print axioms buchstab_identity
#print axioms rough_bounded_u
#print axioms rough_large_u
#print axioms buchstab_limit
#print axioms rough_initial_asymptotic_from_leaves
end
end LeanLab.Languasco2004.Rough588aSplit
