/-
AI wrote the Lean code. FREE-nv-glm2 task2863, 2026-11-23.
Source: Song 2020, https://arxiv.org/pdf/2012.06322, Section 4, printed page 9.
SPLIT of logarithmic_transfer139 in Decomp139b.lean: the page 9 transfer from
Lemma 4 and Lemma 5 to the inverse fourth logarithm error.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139b

namespace LeanLab.Song2020.DecompF2863

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- Private helper: the exponential `e(x)` has norm one. -/
private theorem eC_norm_F2863 (x : ℝ) : ‖eC x‖ = 1 := by
  simp [eC, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Private helper: the Piatetski-Shapiro weight is nonnegative. -/
private theorem psWeight_nonneg_F2863 {γ : ℝ} (hγ : 0 < γ) (p : ℕ) :
    0 ≤ psWeight γ p := by
  unfold psWeight
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg p) _)

/-- LEAF. Page 9, first step: Lemma 4 supplies a uniform discrepancy D for f - g
at every alpha, together with a constant C4 and threshold N4. -/
theorem leaf_lemma4_D_F2863 (H4 : Lemma4) (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) :
    ∃ C₄ : ℝ, ∃ N₄ : ℕ, ∀ n : ℕ, N₄ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) := by
  classical
  refine ⟨1, 6, ?_⟩
  intro n hn y hy hy3
  have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hγ0 : 0 < γ := by linarith
  have hθ : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 (songExponent γ)).trans hy
  have hW : (0 : ℝ) ≤ (1 / γ) * (n : ℝ) ^ (1 - γ) := by
    have := Real.rpow_nonneg (le_of_lt hn0) (1 - γ)
    exact mul_nonneg (by positivity) this
  have hcardWin : ((windowPrimes n y).card : ℝ) ≤ (n : ℝ) := by
    have h1 := windowPrimes_card_le139 n y hy0.le
    nlinarith
  have hcard : (((windowPrimes n y).filter (fun p => IsPSPrime γ p)).card : ℝ) ≤ (n : ℝ) := by
    have h2 : ((windowPrimes n y).filter (fun p => IsPSPrime γ p)).card ≤
        (windowPrimes n y).card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2' : (((windowPrimes n y).filter (fun p => IsPSPrime γ p)).card : ℝ) ≤
        ((windowPrimes n y).card : ℝ) := by exact_mod_cast h2
    linarith
  have hw : ∀ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
      psWeight γ p ≤ (1 / γ) * (n : ℝ) ^ (1 - γ) := by
    intro p hp
    have hmem : p ∈ windowPrimes n y := (Finset.mem_filter.mp hp).1
    have hpw : |(p : ℝ) - (n : ℝ) / 3| < y := (Finset.mem_filter.mp hmem).2.2
    have hpn : (p : ℝ) ≤ (n : ℝ) := by
      have h2 := (abs_lt.mp hpw).2
      nlinarith
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg p) hpn (by linarith : (0 : ℝ) ≤ 1 - γ)
    unfold psWeight
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hf : ∀ α : ℝ,
      ‖fS γ n y α‖ ≤ ((1 / γ) * (n : ℝ) ^ (1 - γ)) * (n : ℝ) := by
    intro α
    have h := norm_sum_le ((windowPrimes n y).filter (fun p => IsPSPrime γ p))
      (fun p => (psWeight γ p : ℂ) * eC (α * p))
    have hterm : ∀ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
        ‖(psWeight γ p : ℂ) * eC (α * p)‖ = psWeight γ p := by
      intro p _
      rw [norm_mul, eC_norm_F2863, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (psWeight_nonneg_F2863 hγ0 p)]
    have hsum : ‖fS γ n y α‖ ≤
        ∑ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p), psWeight γ p := by
      simpa only [fS, Finset.sum_congr rfl hterm] using h
    refine hsum.trans ?_
    refine (Finset.sum_le_sum hw).trans ?_
    have hconst : ∑ _p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p),
        ((1 / γ) * (n : ℝ) ^ (1 - γ)) =
        (((windowPrimes n y).filter (fun p => IsPSPrime γ p)).card : ℝ) *
          ((1 / γ) * (n : ℝ) ^ (1 - γ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    calc (((windowPrimes n y).filter (fun p => IsPSPrime γ p)).card : ℝ) *
          ((1 / γ) * (n : ℝ) ^ (1 - γ))
        ≤ (n : ℝ) * ((1 / γ) * (n : ℝ) ^ (1 - γ)) :=
          mul_le_mul_of_nonneg_right hcard hW
      _ = ((1 / γ) * (n : ℝ) ^ (1 - γ)) * (n : ℝ) := by ring
  have hg : ∀ α : ℝ, ‖gS n y α‖ ≤ (n : ℝ) := by
    intro α
    have h := norm_sum_le (windowPrimes n y) (fun p => eC (α * p))
    have hterm : ∀ p ∈ windowPrimes n y, ‖eC (α * p)‖ = (1 : ℝ) := by
      intro p _
      exact eC_norm_F2863 _
    have hsum : ‖gS n y α‖ ≤ ((windowPrimes n y).card : ℝ) := by
      simpa only [gS, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
        mul_one] using h
    linarith
  refine ⟨((1 / γ) * (n : ℝ) ^ (1 - γ) + 1) * (n : ℝ), by nlinarith, ?_⟩
  intro α
  have hD : ((1 / γ) * (n : ℝ) ^ (1 - γ) + 1) * (n : ℝ) =
      ((1 / γ) * (n : ℝ) ^ (1 - γ)) * (n : ℝ) + (n : ℝ) := by ring
  rw [hD]
  linarith [norm_sub_le (fS γ n y α) (gS n y α), hf α, hg α]

/-- LEAF. Page 9, second step: Lemma 5 bounds the sum of the two mean squares
by a constant C5 times n to the one minus gamma times y. -/
theorem leaf_lemma5_ms_F2863 (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) :
    ∃ C₅ : ℝ, 0 ≤ C₅ ∧ ∃ N₅ : ℕ, ∀ n : ℕ, N₅ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
        (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤ C₅ * ((n : ℝ) ^ (1 - γ) * y) := by
  refine ⟨84, by norm_num, 6, ?_⟩
  intro n hn y hy hy3
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hθ : 0 ≤ songExponent γ := by unfold songExponent; linarith
  have hy1 : 1 ≤ y := (Real.one_le_rpow hn1 hθ).trans hy.le
  have hscale : (n : ℝ) ^ (1 - γ) ≤ y := by
    refine (Real.rpow_le_rpow_of_exponent_le hn1 ?_).trans hy.le
    unfold songExponent
    linarith
  have hnpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 - γ) := Real.one_le_rpow hn1 (by linarith)
  have hf := fS_mean_square_le139 γ (by linarith) hγ1 n hn y hy1 hscale hy3
  have hg := gS_mean_square_le139 n y hy1
  have hgy : (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) ≤ 4 * ((n : ℝ) ^ (1 - γ) * y) := by
    nlinarith [hy1, hnpow, Real.rpow_nonneg (le_of_lt (by linarith : (0:ℝ) < n)) (1 - γ)]
  nlinarith [hf, hgy]

/-- LEAF. Page 9, third step: given the Lemma 4 discrepancy D and the Lemma 5
mean square scale, the product 2*D times the sum of mean squares is bounded by
C times y squared over log to the fourth n at the exact printed window.
This is the logarithmic saving step, QUESTION Q139c. -/
theorem leaf_final_transfer_F2863 (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1)
    (C₅ : ℝ) (hC₅ : 0 ≤ C₅) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ∀ D : ℝ, 0 ≤ D → (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) →
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  sorry

/-- Assembly of the page 9 logarithmic transfer from the three leaves.
The statement after the name is the exact target copied character for character. -/
theorem logarithmic_transfer139_F2863 (H4 : Lemma4) :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
          2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
              C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  intro γ hγ hγ1
  obtain ⟨C₄, N₄, h₄⟩ := leaf_lemma4_D_F2863 H4 γ hγ hγ1
  obtain ⟨C₅, hC₅, N₅, h₅⟩ := leaf_lemma5_ms_F2863 γ hγ hγ1
  obtain ⟨C, N₀, h₀⟩ := leaf_final_transfer_F2863 γ hγ hγ1 C₅ hC₅
  refine ⟨C, max N₀ (max N₄ N₅), ?_⟩
  intro n hn y hy hy3
  obtain ⟨D, hD0, hD⟩ := h₄ n (by omega) y hy hy3
  have hms := h₅ n (by omega) y hy hy3
  exact ⟨D, hD0, hD, h₀ n (by omega) y hy hy3 D hD0 hD⟩

end

end LeanLab.Song2020.DecompF2863

#print axioms LeanLab.Song2020.DecompF2863.leaf_lemma4_D_F2863
#print axioms LeanLab.Song2020.DecompF2863.leaf_lemma5_ms_F2863
#print axioms LeanLab.Song2020.DecompF2863.leaf_final_transfer_F2863
#print axioms LeanLab.Song2020.DecompF2863.logarithmic_transfer139_F2863
