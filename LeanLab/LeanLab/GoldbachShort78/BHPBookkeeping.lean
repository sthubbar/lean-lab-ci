import Mathlib

/-!
AI wrote the Lean code, Codex task57. Binary Goldbach is OPEN.
Baker, Harman and Pintz 2001, Lemma 10, p. 542, equations 3.14 to 3.19.
https://doi.org/10.1112/plms/83.3.532
The sum-bound core uses only the last term being smallest, the common upper bound,
and the half-weight cap. It does not need the least-index condition on h.
-/

namespace LeanLab.GoldbachShort78

/-- The upper bound alpha-star in BHP equation 3.16. -/
noncomputable def bhpAlphaStar (θ α : ℝ) (h : ℕ) : ℝ :=
  max ((2 * h * (1 - θ) - α) / (2 * h - 1))
    ((2 * ((h : ℝ) - 1) * θ + α) / (2 * h - 1))

/-- The elementary sum-bound core of BHP 2001 Lemma 10, including k equal to zero. -/
theorem bhp_lemma10_sum_bound {θ α : ℝ} {h k : ℕ} {u : ℕ → ℝ}
    (hh : 1 ≤ h) (hαθ : α ≤ θ)
    (hnonneg : ∀ i < k, 0 ≤ u i)
    (hupper : ∀ i < k, u i ≤ 2 * (θ - α) / (2 * h - 1))
    (hlast : ∀ i < k, u (k - 1) ≤ u i)
    (hcap : 0 < k → α + (∑ i ∈ Finset.range (k - 1), u i) + (1 / 2 : ℝ) * u (k - 1) ≤ 1 - θ) :
    α + (∑ i ∈ Finset.range k, u i) ≤ bhpAlphaStar θ α h := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hD : (0 : ℝ) < 2 * h - 1 := by linarith
  by_cases hkh : h ≤ k
  · have hkpos : 0 < k := by omega
    have hkr : k - 1 + 1 = k := by omega
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hhkR : (h : ℝ) ≤ k := by exact_mod_cast hkh
    have hlast0 := hnonneg (k - 1) (by omega)
    have hsumlast : ((k - 1 : ℕ) : ℝ) * u (k - 1) ≤ ∑ i ∈ Finset.range (k - 1), u i := by
      calc
        ((k - 1 : ℕ) : ℝ) * u (k - 1) = ∑ i ∈ Finset.range (k - 1), u (k - 1) := by simp
        _ ≤ ∑ i ∈ Finset.range (k - 1), u i := by
          apply Finset.sum_le_sum
          intro i hi
          exact hlast i (by have := Finset.mem_range.mp hi; omega)
    have hprior : ((h : ℝ) - 1) * u (k - 1) ≤ ∑ i ∈ Finset.range (k - 1), u i := by
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - h by linarith) hlast0]
    have hcap' := hcap hkpos
    have hlastbound : u (k - 1) ≤ 2 * (1 - θ - α) / (2 * h - 1) := by
      apply (le_div_iff₀ hD).mpr
      nlinarith
    have hsum_eq : (∑ i ∈ Finset.range k, u i) =
        (∑ i ∈ Finset.range (k - 1), u i) + u (k - 1) := by
      simpa only [hkr] using Finset.sum_range_succ u (k - 1)
    have hfirst : α + (∑ i ∈ Finset.range k, u i) ≤
        (2 * h * (1 - θ) - α) / (2 * h - 1) := by
      calc
        α + (∑ i ∈ Finset.range k, u i) ≤ 1 - θ + (1 / 2 : ℝ) * u (k - 1) := by
          rw [hsum_eq]
          linarith
        _ ≤ 1 - θ + (1 / 2 : ℝ) * (2 * (1 - θ - α) / (2 * h - 1)) := by linarith
        _ = (2 * h * (1 - θ) - α) / (2 * h - 1) := by
          apply (eq_div_iff (ne_of_gt hD)).mpr
          have hc := div_mul_cancel₀ (2 * (1 - θ - α)) (ne_of_gt hD)
          calc
            (1 - θ + (1 / 2 : ℝ) * (2 * (1 - θ - α) / (2 * h - 1))) * (2 * h - 1) =
                (1 - θ) * (2 * h - 1) + (1 / 2 : ℝ) *
                  ((2 * (1 - θ - α) / (2 * h - 1)) * (2 * h - 1)) := by ring
            _ = 2 * h * (1 - θ) - α := by rw [hc]; ring
    exact le_trans hfirst (le_max_left _ _)
  · have hkh' : k < h := by omega
    have hkR : (k : ℝ) + 1 ≤ h := by exact_mod_cast hkh'
    have hM : 0 ≤ 2 * (θ - α) / (2 * h - 1) := by positivity
    have hsum : (∑ i ∈ Finset.range k, u i) ≤
        (k : ℝ) * (2 * (θ - α) / (2 * h - 1)) := by
      calc
        (∑ i ∈ Finset.range k, u i) ≤ ∑ i ∈ Finset.range k, 2 * (θ - α) / (2 * h - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hupper i (Finset.mem_range.mp hi)
        _ = (k : ℝ) * (2 * (θ - α) / (2 * h - 1)) := by simp
    have hsecond : α + (∑ i ∈ Finset.range k, u i) ≤
        (2 * ((h : ℝ) - 1) * θ + α) / (2 * h - 1) := by
      calc
        α + (∑ i ∈ Finset.range k, u i) ≤ α + ((h : ℝ) - 1) * (2 * (θ - α) / (2 * h - 1)) := by
          nlinarith [mul_nonneg (show 0 ≤ (h : ℝ) - 1 - k by linarith) hM]
        _ = (2 * ((h : ℝ) - 1) * θ + α) / (2 * h - 1) := by
          apply (eq_div_iff (ne_of_gt hD)).mpr
          have hc := div_mul_cancel₀ (2 * (θ - α)) (ne_of_gt hD)
          calc
            (α + ((h : ℝ) - 1) * (2 * (θ - α) / (2 * h - 1))) * (2 * h - 1) =
                α * (2 * h - 1) + ((h : ℝ) - 1) *
                  ((2 * (θ - α) / (2 * h - 1)) * (2 * h - 1)) := by ring
            _ = 2 * ((h : ℝ) - 1) * θ + α := by rw [hc]; ring
    exact le_trans hsecond (le_max_right _ _)

/-- BHP Lemma 10 with the printed least-index and decreasing-sequence hypotheses.
The sufficiently small epsilon convention is made explicit. -/
theorem bhp_lemma10 {θ α ε : ℝ} {h k : ℕ} {u : ℕ → ℝ}
    (_hε : 0 < ε) (hεsmall : ε ≤ θ - 1 / 2) (_hα0 : 0 ≤ α) (hαε : α ≤ 1 / 2 + ε)
    (hh : IsLeast {j : ℕ | 0 < j ∧ (1 / 2 : ℝ) - 2 * j * (θ - 1 / 2) ≤ α} h)
    (hmono : AntitoneOn u (Set.Iio k)) (hpos : ∀ i < k, 0 < u i)
    (hfirst : 0 < k → u 0 ≤ 2 * (θ - α) / (2 * h - 1))
    (hcap : 0 < k → α + (∑ i ∈ Finset.range (k - 1), u i) + (1 / 2 : ℝ) * u (k - 1) ≤ 1 - θ) :
    α + (∑ i ∈ Finset.range k, u i) ≤ bhpAlphaStar θ α h := by
  have hh1 : 1 ≤ h := by have := hh.1.1; omega
  apply bhp_lemma10_sum_bound hh1 (by linarith) (fun i hi => (hpos i hi).le)
  · intro i hi
    have hk : 0 < k := by omega
    exact le_trans (hmono hk hi (Nat.zero_le i)) (hfirst hk)
  · intro i hi
    exact hmono hi (show k - 1 < k by omega) (by omega)
  · exact hcap

/-- BHP equation 3.19, the last-term bound in the case k at least h. -/
theorem bhp_lemma10_last_term_bound {θ α : ℝ} {h k : ℕ} {u : ℕ → ℝ}
    (hh : 1 ≤ h) (hk : h ≤ k) (hmono : AntitoneOn u (Set.Iio k))
    (hlast0 : 0 ≤ u (k - 1))
    (hcap : α + (∑ i ∈ Finset.range (k - 1), u i) + (1 / 2 : ℝ) * u (k - 1) ≤ 1 - θ) :
    u (k - 1) ≤ (1 - θ - α) / ((h : ℝ) - 1 / 2) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhkR : (h : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < k := by omega
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hlo : ((k : ℝ) - 1) * u (k - 1) ≤ ∑ i ∈ Finset.range (k - 1), u i := by
    calc
      ((k : ℝ) - 1) * u (k - 1) = ∑ i ∈ Finset.range (k - 1), u (k - 1) := by
        rw [← hkcast]
        simp
      _ ≤ ∑ i ∈ Finset.range (k - 1), u i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact hmono (show i < k by omega) (show k - 1 < k by omega) (by omega)
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (h : ℝ) - 1 / 2)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hhkR) hlast0]

/-- The elementary core of BHP Lemma 11. A non-strict crossing already suffices. -/
theorem bhp_lemma11_gap_core {θ α : ℝ} {h k : ℕ} {u : ℕ → ℝ}
    (hh : 1 ≤ h) (hαθ : α ≤ θ)
    (hstart : (1 / 2 : ℝ) - 2 * h * (θ - 1 / 2) ≤ α)
    (hmono : AntitoneOn u (Set.Iio (k + 1))) (hnonneg : ∀ i < k + 1, 0 ≤ u i)
    (hupper : ∀ i < k + 1, u i ≤ 2 * (θ - α) / (2 * h - 1))
    (hcap : 0 < k → α + (∑ i ∈ Finset.range (k - 1), u i) + (1 / 2 : ℝ) * u (k - 1) ≤ 1 - θ)
    (hcross : 1 - θ ≤ α + (∑ i ∈ Finset.range k, u i) + (1 / 2 : ℝ) * u k) :
    |(α + (∑ i ∈ Finset.range k, u i)) -
      (1 - (α + (∑ i ∈ Finset.range (k + 1), u i)))| ≤ 2 * θ - 1 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hD : (0 : ℝ) < 2 * h - 1 := by linarith
  have hdiff : (α + (∑ i ∈ Finset.range k, u i)) -
      (1 - (α + (∑ i ∈ Finset.range (k + 1), u i))) =
      2 * (α + (∑ i ∈ Finset.range k, u i)) + u k - 1 := by
    rw [Finset.sum_range_succ]
    ring
  rw [hdiff]
  apply abs_le.mpr
  constructor
  · linarith
  · by_cases hkh : h ≤ k
    · have hkpos : 0 < k := by omega
      have hmono' : AntitoneOn u (Set.Iio k) := by
        intro i hi j hj hij
        change i < k at hi
        change j < k at hj
        exact hmono (show i < k + 1 by omega) (show j < k + 1 by omega) hij
      have hlast0 := hnonneg (k - 1) (by omega)
      have hlastB := bhp_lemma10_last_term_bound hh hkh hmono' hlast0 (hcap hkpos)
      have hlast : u (k - 1) ≤ 2 * θ - 1 := by
        apply le_trans hlastB
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < (h : ℝ) - 1 / 2)).mpr
        nlinarith
      have huk : u k ≤ u (k - 1) :=
        hmono (show k - 1 < k + 1 by omega) (Nat.lt_succ_self k) (by omega)
      have hkr : k - 1 + 1 = k := by omega
      have hsum_eq : (∑ i ∈ Finset.range k, u i) =
          (∑ i ∈ Finset.range (k - 1), u i) + u (k - 1) := by
        simpa only [hkr] using Finset.sum_range_succ u (k - 1)
      rw [hsum_eq]
      have hc := hcap hkpos
      linarith
    · have hkh' : k < h := by omega
      have hkR : (k : ℝ) + 1 ≤ h := by exact_mod_cast hkh'
      let M : ℝ := 2 * (θ - α) / (2 * h - 1)
      have hM : 0 ≤ M := by dsimp [M]; positivity
      have hsum : (∑ i ∈ Finset.range k, u i) ≤ (k : ℝ) * M := by
        calc
          (∑ i ∈ Finset.range k, u i) ≤ ∑ i ∈ Finset.range k, M := by
            apply Finset.sum_le_sum
            intro i hi
            exact hupper i (by have := Finset.mem_range.mp hi; omega)
          _ = (k : ℝ) * M := by simp
      have huk : u k ≤ M := hupper k (Nat.lt_succ_self k)
      have hcancel : (2 * (h : ℝ) - 1) * M = 2 * (θ - α) := by
        calc
          (2 * (h : ℝ) - 1) * M = M * (2 * h - 1) := by ring
          _ = 2 * (θ - α) := div_mul_cancel₀ _ (ne_of_gt hD)
      have hfactor := mul_nonneg (show 0 ≤ (2 * (h : ℝ) - 1) - (2 * k + 1) by linarith) hM
      nlinarith

/-- BHP Lemma 11 with the printed strict crossing and positive decreasing terms. -/
theorem bhp_lemma11 {θ α ε : ℝ} {h k : ℕ} {u : ℕ → ℝ}
    (_hε : 0 < ε) (hεsmall : ε ≤ θ - 1 / 2) (_hα0 : 0 ≤ α) (hαε : α ≤ 1 / 2 + ε)
    (hh : IsLeast {j : ℕ | 0 < j ∧ (1 / 2 : ℝ) - 2 * j * (θ - 1 / 2) ≤ α} h)
    (hmono : AntitoneOn u (Set.Iio (k + 1))) (hpos : ∀ i < k + 1, 0 < u i)
    (hfirst : u 0 ≤ 2 * (θ - α) / (2 * h - 1))
    (hcap : 0 < k → α + (∑ i ∈ Finset.range (k - 1), u i) + (1 / 2 : ℝ) * u (k - 1) ≤ 1 - θ)
    (hcross : 1 - θ < α + (∑ i ∈ Finset.range k, u i) + (1 / 2 : ℝ) * u k) :
    |(α + (∑ i ∈ Finset.range k, u i)) -
      (1 - (α + (∑ i ∈ Finset.range (k + 1), u i)))| ≤ 2 * θ - 1 := by
  have hh1 : 1 ≤ h := by have := hh.1.1; omega
  apply bhp_lemma11_gap_core hh1 (by linarith) hh.1.2 hmono (fun i hi => (hpos i hi).le)
  · intro i hi
    exact le_trans (hmono (Nat.succ_pos k) hi (Nat.zero_le i)) hfirst
  · exact hcap
  · exact hcross.le

/-- All three comparisons in BHP equation 3.20. -/
theorem bhp_alphaStar_bounds {θ α ε : ℝ} {h : ℕ}
    (hθ : (1 / 2 : ℝ) ≤ θ) (hε : 0 ≤ ε) (hαε : α ≤ 1 / 2 + ε)
    (hh : IsLeast {j : ℕ | 0 < j ∧ (1 / 2 : ℝ) - 2 * j * (θ - 1 / 2) ≤ α} h) :
    1 - θ ≤ ((h : ℝ) - θ) / (2 * h - 1) ∧
      ((h : ℝ) - θ) / (2 * h - 1) ≤ bhpAlphaStar θ α h ∧
      bhpAlphaStar θ α h ≤ 1 / 2 + ε := by
  have hh1 : 1 ≤ h := by have := hh.1.1; omega
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hD : (0 : ℝ) < 2 * h - 1 := by linarith
  have hstart := hh.1.2
  have hA : (2 * h * (1 - θ) - α) / (2 * h - 1) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have hB : (2 * ((h : ℝ) - 1) * θ + α) / (2 * h - 1) ≤ 1 / 2 + ε := by
    by_cases h1 : h = 1
    · convert hαε using 1 <;> norm_num [h1]
    · have hprev : α < (1 / 2 : ℝ) - 2 * (h - 1 : ℕ) * (θ - 1 / 2) := by
        by_contra hp
        have hmem : h - 1 ∈ {j : ℕ | 0 < j ∧ (1 / 2 : ℝ) - 2 * j * (θ - 1 / 2) ≤ α} :=
          ⟨by omega, le_of_not_gt hp⟩
        have hmin := hh.2 hmem
        omega
      have hcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
        rw [Nat.cast_sub hh1, Nat.cast_one]
      rw [hcast] at hprev
      apply (div_le_iff₀ hD).mpr
      nlinarith [mul_nonneg hε hD.le]
  refine ⟨?_, ?_, max_le (le_trans hA (by linarith)) hB⟩
  · apply (le_div_iff₀ hD).mpr
    nlinarith [mul_nonneg (show 0 ≤ (h : ℝ) - 1 by linarith)
      (show 0 ≤ 2 * θ - 1 by linarith)]
  · have hmaxA : (2 * h * (1 - θ) - α) / (2 * h - 1) ≤ bhpAlphaStar θ α h := le_max_left _ _
    have hmaxB : (2 * ((h : ℝ) - 1) * θ + α) / (2 * h - 1) ≤ bhpAlphaStar θ α h := le_max_right _ _
    have hmaxA' := (div_le_iff₀ hD).mp hmaxA
    have hmaxB' := (div_le_iff₀ hD).mp hmaxB
    apply (div_le_iff₀ hD).mpr
    nlinarith

/-- The subsum step used in the proof of BHP Lemma 5 on p. 539. -/
theorem bhp_small_terms_subsum {ι : Type*} (s : Finset ι) (f : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hnonneg : ∀ i ∈ s, 0 ≤ f i) (hupper : ∀ i ∈ s, f i ≤ a)
    (hsum : a ≤ ∑ i ∈ s, f i) :
    ∃ t : Finset ι, t ⊆ s ∧ a ≤ (∑ i ∈ t, f i) ∧ (∑ i ∈ t, f i) ≤ 2 * a := by
  classical
  revert hnonneg hupper hsum
  induction s using Finset.induction_on with
  | empty =>
      intro hnonneg hupper hsum
      refine ⟨∅, by simp, ?_, ?_⟩
      · simpa using hsum
      · simpa using (show (0 : ℝ) ≤ 2 * a by linarith)
  | @insert i s hi ih =>
      intro hnonneg hupper hsum
      by_cases hrest : a ≤ ∑ j ∈ s, f j
      · obtain ⟨t, ht, hlo, hhi⟩ := ih
          (fun j hj => hnonneg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hupper j (Finset.mem_insert_of_mem hj)) hrest
        exact ⟨t, fun j hj => Finset.mem_insert_of_mem (ht hj), hlo, hhi⟩
      · refine ⟨insert i s, Finset.Subset.refl _, hsum, ?_⟩
        rw [Finset.sum_insert hi]
        have hfi := hupper i (Finset.mem_insert_self i s)
        have hsmall : (∑ j ∈ s, f j) < a := lt_of_not_ge hrest
        linarith

/-- Exact arithmetic behind the printed coefficient and the remaining input limitations. -/
theorem bhp_remaining_input_budget :
    (1 : ℝ) - 0.3 - 0.06 - 0.21 - 0.34 = 9 / 100 ∧
    (9 / 100 : ℝ) / 16 = 9 / 1600 ∧
    (0 : ℝ) < 9 / 1600 ∧ (9 / 1600 : ℝ) < 1 / 2 ∧
    (9 / 100 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 21.5 < 0.525 ∧ (0.525 : ℝ) < 0.535 := by
  norm_num

/-- BHP equation 3.5, extended from positive c to every real c by convexity. -/
theorem bhp_exp_chord (c y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (c * y) - 1 ≤ (Real.exp c - 1) * y := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ c)
    (sub_nonneg.mpr hy1) hy0 (show (1 - y) + y = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm y c] at h
  nlinarith

end LeanLab.GoldbachShort78
