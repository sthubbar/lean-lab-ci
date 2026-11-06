/-
P0069 pages 26 and 27, supply decomposition of the exact repaired Lemma 12.
The finite Moebius truncation and domination algebra are already proved in Decomp1518.
The three analytic displays remain explicit OPEN leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp1518

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Filter Topology Decomp1518
attribute [local instance] Classical.propDecidable

/-- Page 26, gamma equals x to epsilon/12 for all large x.
The maximum with two only supplies harmless small x values for the global interface. -/
def cutoff (ε x : ℝ) : ℝ := max 2 (x ^ (ε / 12))

/-- Page 26, the regularized cutoff agrees eventually with the printed cutoff. -/
theorem cutoff_eventually_eq {ε : ℝ} (hε : 0 < ε) :
    Ev fun x => cutoff ε x = x ^ (ε / 12) := by
  have he : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (ε / 12) :=
    (tendsto_rpow_atTop (by linarith : 0 < ε / 12)).eventually_ge_atTop 2
  exact eventually_atTop.1 (he.mono fun x hx => max_eq_right hx)

/-- Page 27, both divisor cutoffs cost at most x to epsilon/8 in polynomial length. -/
theorem cutoff_inflation {ε : ℝ} (hε : 0 < ε) :
    Ev fun x => cutoff ε x ≤ x ^ (ε / 8) ∧
      cutoff ε x * wof x ≤ x ^ (ε / 8) := by
  obtain ⟨Xc, hc⟩ := cutoff_eventually_eq hε
  obtain ⟨Xw, hw⟩ := wof_le_rpow_ev (ε / 24) (by linarith)
  refine ⟨max Xc (max Xw 1), ?_⟩
  intro x hx
  have hxc : Xc ≤ x := (le_max_left _ _).trans hx
  have hxw : Xw ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : 1 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := by linarith
  rw [hc x hxc]
  refine ⟨Real.rpow_le_rpow_of_exponent_le hx1 (by linarith), ?_⟩
  calc
    _ ≤ x ^ (ε / 12) * x ^ (ε / 24) :=
      mul_le_mul_of_nonneg_left (hw x hxw) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (ε / 8) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring

/-- LEAF. OPEN. Page 26 display 4.10 and page 27 first paragraph.
This is the character transfer for the truncated coefficient family c prime only.
The missing MN below T0 case is retained in the range. No false large L leaf is used. -/
theorem truncated_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      Holds42 ε fun x k => conv2T (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k := by
  sorry

/-- LEAF. OPEN. Page 26 display 4.11 and page 27 second paragraph.
This is the transfer of the nonnegative truncation error coefficient c double prime.
Its divisor window is gamma at most d below gamma w as defined on page 26. -/
theorem error_transfer :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      Holds42 ε fun x k =>
        ((conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k : ℝ) : ℂ) := by
  sorry

/-- LEAF. OPEN. Page 26 display 4.12, reduced by page 27 display 4.13.
This is an untwisted long interval average of c double prime only.
The source invokes Hildebrand reference 13 Theorem 1 for the reciprocal smooth tail. -/
theorem error_average :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (B : ℝ) (a b : ℝ → ℕ → ℂ) (M N : ℝ → ℝ),
      (∀ x k, ‖a x k‖ ≤ tau k ^ B) → (∀ x k, ‖b x k‖ ≤ tau k ^ B) →
      (∀ x, max (x ^ (0.45 : ℝ)) (M x) * max (x ^ (0.225 : ℝ)) (N x) ≤ x ^ (0.775 : ℝ) ∨
        max (M x) (N x) ≤ x ^ (0.46 + ε / 8)) →
      ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
        ∑ k ∈ Finset.Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊,
          conv2E (a x) (b x) (M x) (N x) (wof x) (cutoff ε x) k ≤
            C * y1 x / L x ^ A := by
  sorry

/-- Pages 26 and 27, exact Lemma12 from the three smaller analytic displays.
CONDITIONAL ON truncated_transfer, error_transfer and error_average.
The pointwise Moebius truncation and the transfer domination are proved inputs. -/
theorem lemma12_decomposed : Lemma12 := by
  obtain ⟨εa, hεa, ha⟩ := truncated_transfer
  obtain ⟨εb, hεb, hb⟩ := error_transfer
  obtain ⟨εc, hεc, hc⟩ := error_average
  refine ⟨min εa (min εb εc), lt_min hεa (lt_min hεb hεc), ?_⟩
  intro ε hε hεsmall B a b M N z hca hcb hcond
  have hεa' : ε < εa := hεsmall.trans_le (min_le_left _ _)
  have hεb' : ε < εb := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεc' : ε < εc := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrange := fun x => (hcond x).2
  have h410 := ha ε hε hεa' B a b M N hca hcb hrange
  have h411 := hb ε hε hεb' B a b M N hca hcb hrange
  have h412 := hc ε hε hεc' B a b M N hca hcb hrange
  have hs := lemma12_of_410_411_412 a b M N (cutoff ε)
    (fun x => lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)) h410 h411 h412
  have hz : z = wof := funext fun x => (hcond x).1
  subst z
  exact hs

#print axioms cutoff
#print axioms cutoff_eventually_eq
#print axioms cutoff_inflation
#print axioms truncated_transfer
#print axioms error_transfer
#print axioms error_average
#print axioms lemma12_decomposed

end LeanLab.BakerHarmanPintz1997.Decomp409b
