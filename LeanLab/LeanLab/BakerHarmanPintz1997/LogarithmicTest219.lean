/-
Baker, Harman and Pintz 1997, page 21, display 3.35.
A proved iterated derivative test for the affine logarithmic phase.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.LogPhase219
import LeanLab.BakerHarmanPintz1997.DerivativeTest219

namespace LeanLab.BakerHarmanPintz1997.LogarithmicTest219
open Finset PortedVanDerCorput LogPhase219 DerivativeTest219

/-- Page 21. The lower second difference scale for a prescribed list of shifts. -/
noncomputable def logDifferenceScale (a t M : ℝ) (hs : List ℤ) : ℝ :=
  t * ((1 :: 1 :: hs.map (fun h : ℤ => (h : ℝ))).map (a * ·)).prod *
    (hs.length + 1).factorial / M ^ (hs.length + 2)

/-- Page 21. Factor the lower scale into the derivative scale and the product of shifts. -/
theorem logDifferenceScale_factor (a t M : ℝ) (hs : List ℤ) :
    logDifferenceScale a t M hs =
      t * (a / M) ^ (hs.length + 2) *
        (hs.map (fun h : ℤ => (h : ℝ))).prod * (hs.length + 1).factorial := by
  have hp : ((1 :: 1 :: hs.map (fun h : ℤ => (h : ℝ))).map (a * ·)).prod =
      a ^ (hs.length + 2) * (hs.map (fun h : ℤ => (h : ℝ))).prod := by
    have h := List.prod_map_mul (l := 1 :: 1 :: hs.map (fun h : ℤ => (h : ℝ)))
      (f := fun _ : ℝ => a) (g := id)
    simpa only [List.map_const', List.prod_replicate, List.map_id, List.map_id', id_eq, List.length_cons,
      List.length_map, List.prod_cons, one_mul, Nat.add_assoc, Nat.reduceAdd] using h
  unfold logDifferenceScale
  rw [hp, div_pow]
  ring

/-- Page 21. The scale on the interval from N to 4N has an order dependent constant. -/
theorem logDifferenceScale_four (a t N : ℝ) (hs : List ℤ) :
    logDifferenceScale a t (4 * N) hs =
      ((hs.length + 1).factorial / (4 : ℝ) ^ (hs.length + 2)) *
        (t * (a / N) ^ (hs.length + 2)) * (hs.map (fun h : ℤ => (h : ℝ))).prod := by
  rw [logDifferenceScale_factor, div_pow, mul_pow, div_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Page 21. Uniform shift bounds give a uniform window for every terminal scale. -/
theorem logDifferenceScale_window (hs : List ℤ) {a t N L δ : ℝ}
    (hN : 1 ≤ N) (ht : 0 ≤ t) (hL : L ≤ N ^ δ)
    (hδ : δ * hs.length ≤ 1 / 4)
    (hhs : ∀ h ∈ hs, 1 ≤ (h : ℝ) ∧ (h : ℝ) ≤ L)
    (hlo : N ^ (-3 / 2 : ℝ) ≤ t * (a / N) ^ (hs.length + 2))
    (hhi : t * (a / N) ^ (hs.length + 2) ≤ N ^ (-1 / 2 : ℝ)) :
    let K := (hs.length + 1).factorial / (4 : ℝ) ^ (hs.length + 2)
    K * N ^ (-3 / 2 : ℝ) ≤ logDifferenceScale a t (4 * N) hs ∧
      logDifferenceScale a t (4 * N) hs ≤ K * N ^ (-1 / 4 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hprods : ∀ xs : List ℤ, (∀ h ∈ xs, 1 ≤ (h : ℝ) ∧ (h : ℝ) ≤ L) →
      1 ≤ (xs.map (fun h : ℤ => (h : ℝ))).prod ∧
      (xs.map (fun h : ℤ => (h : ℝ))).prod ≤ (N ^ δ) ^ xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons h xs ih =>
      intro hh
      have hh0 := hh h (by simp)
      have htail := ih (fun z hz => hh z (by simp [hz]))
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hh0.1) (sub_nonneg.mpr htail.1)]
      · calc
          _ ≤ N ^ δ * (N ^ δ) ^ xs.length :=
            mul_le_mul (hh0.2.trans hL) htail.2 (by linarith [htail.1]) (Real.rpow_nonneg hN0.le _)
          _ = _ := mul_comm _ _
  have hprodlo := (hprods hs hhs).1
  have hprodhi : (hs.map (fun h : ℤ => (h : ℝ))).prod ≤ N ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (N ^ δ) ^ hs.length := (hprods hs hhs).2
      _ = N ^ (δ * hs.length) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hδ
  have hbase : 0 ≤ t * (a / N) ^ (hs.length + 2) :=
    (Real.rpow_nonneg hN0.le _).trans hlo
  dsimp only
  rw [logDifferenceScale_four]
  have hK : 0 ≤ (hs.length + 1).factorial / (4 : ℝ) ^ (hs.length + 2) := by positivity
  constructor
  · calc
      _ ≤ ((hs.length + 1).factorial / (4 : ℝ) ^ (hs.length + 2)) *
          (t * (a / N) ^ (hs.length + 2)) := mul_le_mul_of_nonneg_left hlo hK
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hK hbase) hprodlo
  · calc
      _ ≤ ((hs.length + 1).factorial / (4 : ℝ) ^ (hs.length + 2)) *
          N ^ (-1 / 2 : ℝ) * N ^ (1 / 4 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hhi hK) hprodhi (by linarith) (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hN0]; norm_num

/-- Page 21. The affine logarithmic phase satisfies iterated van der Corput with explicit scales. -/
theorem logarithmic_iterated_bound (d : ℕ) (p q : ℤ) (L : ℕ)
    {a t r N M U eps : ℝ} (ha : 0 < a) (ht : 0 < t) (hN : 0 < N) (hNM : N ≤ M)
    (hleft : N ≤ a * p + r) (hright : a * (q + 2) + r ≤ M)
    (hL : 1 ≤ L) (hU : 0 < U) (hLU : (L : ℝ) ≤ U)
    (hsize : ((Icc p q).card : ℝ) ≤ U) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ d))
    (hterminal : ∀ hs : List ℤ, hs.length = d →
      (∀ h ∈ hs, 1 ≤ h ∧ h < L) →
      8 * ((M / N) ^ (d + 2) * U * Real.sqrt (logDifferenceScale a t M hs) +
        1 / Real.sqrt (logDifferenceScale a t M hs)) ≤ U * eps ^ (2 ^ d)) :
    ‖∑ n ∈ Icc p q, eK (t * (-Real.log (a * n + r)))‖ ≤ 4 * U * eps := by
  have hM : 0 < M := hN.trans_le hNM
  have hc : 1 ≤ (M / N) ^ (d + 2) := one_le_pow₀ ((le_div_iff₀ hN).mpr (by simpa using hNM))
  apply iterated_of_second_difference_bounds d (fun z => t * (-Real.log (a * z + r)))
    p q L U eps ((M / N) ^ (d + 2)) (logDifferenceScale a t M)
    hL hU hLU hsize heps heps1 hLin hc
  · intro hs hlen hhs
    unfold logDifferenceScale
    apply div_pos
    · apply mul_pos
      · apply mul_pos ht
        apply List.prod_pos
        intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        apply mul_pos ha
        rcases List.mem_cons.mp hy with rfl | hy
        · norm_num
        rcases List.mem_cons.mp hy with rfl | hy
        · norm_num
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hy
        have := (hhs h hh).1
        exact_mod_cast (show (0 : ℤ) < h by omega)
      · exact_mod_cast Nat.factorial_pos _
    · positivity
  · intro hs hlen hhs n hn
    have hshifts : ∀ h ∈ hs.map (fun h : ℤ => (h : ℝ)), 0 < h := by
      intro y hy
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hy
      have := (hhs h hh).1
      exact_mod_cast (show (0 : ℤ) < h by omega)
    have hsum : (hs.map (fun h : ℤ => (h : ℝ))).sum = (hs.sum : ℝ) := by
      induction hs with
      | nil => simp
      | cons h hs ih => simp [ih]
    have hlo : N ≤ a * (n : ℝ) + r := hleft.trans (by
      have hpn : (p : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      nlinarith)
    have hupper : a * ((n : ℝ) + 2 + (hs.map (fun h : ℤ => (h : ℝ))).sum) + r ≤ M := by
      rw [hsum]
      have hnn : (n : ℝ) + (hs.sum : ℝ) ≤ q := by
        exact_mod_cast (show n + hs.sum ≤ q by have := (mem_Ico.mp hn).2; omega)
      nlinarith [hright]
    have hb := log_phase_second_difference_bounds _ hshifts ha ht.le hN hlo hupper
    simp only [List.length_map, hlen] at hb
    have heq : (M / N) ^ (d + 2) * logDifferenceScale a t M hs =
        t * ((1 :: 1 :: hs.map (fun h : ℤ => (h : ℝ))).map (a * ·)).prod *
          (d + 1).factorial / N ^ (d + 2) := by
      unfold logDifferenceScale
      rw [hlen, div_pow]
      field_simp
    constructor
    · simpa only [logDifferenceScale, hlen, mul_assoc] using hb.1
    · rw [heq]
      simpa only [mul_assoc] using hb.2
  · exact hterminal

#print axioms logDifferenceScale_factor
#print axioms logDifferenceScale_four
#print axioms logDifferenceScale_window
#print axioms logarithmic_iterated_bound
end LeanLab.BakerHarmanPintz1997.LogarithmicTest219
