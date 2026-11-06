import LeanLab.ExceptionalSet.U1423MVMinor
import LeanLab.ExceptionalSet.SPLIT_theorem51

/-!
Supply for the fixed minor arc fourth moment.
Source: Montgomery and Vaughan 1975 page 356 displays 3.2 and 3.3.
The wider arcs in SPLIT_theorem51 have a smaller complement.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp428a

open Real Filter Finset ZMod
open LeanLab.ExceptionalSet.MV
open LeanLab.ExceptionalSet.MV75U1423

/-- LEAF. Page 355 display 2.4 and page 356 display 3.3.
If three times P is at most Q, the Montgomery and Vaughan major arcs
are contained in the fixed width arcs of the discrete skeleton. -/
theorem minor_subset (x : ℕ) (hx : 1 ≤ x) (P Q : ℝ)
    (hPQ : 3 * P ≤ Q) (hP : 0 ≤ P) :
    minorArcs x Q ⊆ mvMinor x P := by
  classical
  intro k hk
  apply Finset.mem_compl.mpr
  intro hkm
  apply (Finset.mem_compl.mp hk)
  simp only [mvMajor, Finset.mem_filter, Finset.mem_univ, true_and] at hkm
  obtain ⟨q, hq, hqP, a, ha⟩ := hkm
  simp only [majorArcs, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨q, hq, hqP.trans ?_, a, ha.trans ?_⟩
  · linarith
  · have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hM : (Mx x : ℝ) = 2 * x + 1 := by simp [Mx]
    rw [div_le_div_iff₀ (by positivity) (by rw [hM]; positivity)]
    have hQ : 0 ≤ Q := by linarith
    have hM3 : (Mx x : ℝ) ≤ 3 * x := by rw [hM]; linarith
    calc P * (Mx x : ℝ) ≤ P * (3 * x) := mul_le_mul_of_nonneg_left hM3 hP
      _ ≤ Q * x := by nlinarith
      _ ≤ Q * (q * x) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (by positivity) hqr) hQ

/-- LEAF. Page 356 display 3.2. Shrinking the minor set and increasing
the positive threshold can only decrease its normalized fourth moment. -/
theorem moment_mono (x : ℕ) (s t : Finset (ZMod (Mx x))) (hs : s ⊆ t)
    (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    (Mx x : ℝ) * (∑ k ∈ s, ‖𝓕 (logPrimes x) k‖ ^ 4) / B ^ 2 ≤
      (Mx x : ℝ) * (∑ k ∈ t, ‖𝓕 (logPrimes x) k‖ ^ 4) / A ^ 2 := by
  apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
  · exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity))
      (Nat.cast_nonneg _)
  · exact pow_le_pow_left₀ hA.le hAB 2

/-- LEAF. Page 356 displays 3.2 and 3.3. The fixed level x to one tenth
eventually contains the smaller level x to one twentieth. Its threshold
Mx times x over four exceeds Mx times x to fifty nine sixtieths. -/
theorem parameters_eventually : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
    1 ≤ x ∧ 3 * (x : ℝ) ^ (1 / 20 : ℝ) ≤ (x : ℝ) ^ (1 / 10 : ℝ) ∧
      (Mx x : ℝ) * (x : ℝ) ^ (59 / 60 : ℝ) ≤ (Mx x : ℝ) * x / 4 := by
  have ht (a : ℝ) (ha : 0 < a) :
      Tendsto (fun x : ℕ => (x : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (ht (1 / 20) (by norm_num)).eventually_ge_atTop 3,
    (ht (1 / 60) (by norm_num)).eventually_ge_atTop 4] with x hx h20 h60
  have hxp : (0 : ℝ) < x := by exact_mod_cast hx
  refine ⟨hx, ?_, ?_⟩
  · have hp : (x : ℝ) ^ (1 / 10 : ℝ) = (x : ℝ) ^ (1 / 20 : ℝ) * (x : ℝ) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_add hxp]; norm_num
    rw [hp]
    nlinarith [Real.rpow_pos_of_pos hxp (1 / 20 : ℝ)]
  · have hp : (x : ℝ) = (x : ℝ) ^ (59 / 60 : ℝ) * (x : ℝ) ^ (1 / 60 : ℝ) := by
      rw [← Real.rpow_add hxp]; norm_num
    have hb : 4 * (x : ℝ) ^ (59 / 60 : ℝ) ≤ x := by
      calc _ ≤ (x : ℝ) ^ (1 / 60 : ℝ) * (x : ℝ) ^ (59 / 60 : ℝ) := by gcongr
        _ = x := by rw [mul_comm]; exact hp.symm
    have hM : (0 : ℝ) ≤ Mx x := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hb hM]

/-- Exact supply for SPLIT_theorem51.minor_arc_l4_power.
Source: page 356 display 3.2. All analytic inputs are already proved in
U1423MVMinor. The old admission is preserved for review. -/
theorem minor_arc_l4_power_supplied :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        (Mx x : ℝ) * (∑ k ∈ minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)), ‖𝓕 (logPrimes x) k‖ ^ 4)
            / ((Mx x : ℝ) * x / 4) ^ 2 ≤ C * (x : ℝ) ^ θ := by
  obtain ⟨C, X₀, h⟩ := minorTerm_33
  obtain ⟨X₁, hp⟩ := parameters_eventually
  refine ⟨119 / 120, 27 * C ^ 2 * (10 / (1 / 120 : ℝ)) ^ 10,
    max 1 (max X₀ X₁), by norm_num, by norm_num, by positivity, le_max_left _ _, ?_⟩
  intro x hx
  have hx₀ : X₀ ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx₁ : X₁ ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  obtain ⟨hx1, hPQ, hT⟩ := hp x hx₁
  have hxp : (0 : ℝ) < x := by exact_mod_cast hx1
  have hM : (0 : ℝ) < Mx x := by exact_mod_cast (show 0 < Mx x by simp [Mx])
  have hs := minor_subset x hx1 _ _ hPQ (Real.rpow_nonneg hxp.le _)
  have hc := moment_mono x _ _ hs _ _
    (mul_pos hM (Real.rpow_pos_of_pos hxp (59 / 60 : ℝ))) hT
  have hb := h (1 / 120) (by norm_num) (by norm_num) x hx₀
  norm_num only at hb
  exact hc.trans (by norm_num only; exact hb)

end LeanLab.ExceptionalSet.Decomp428a
