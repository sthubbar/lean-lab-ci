/-
P0069, page 13, the two third-factor branches of Case 2.
The small-value branch uses mean squares directly.
The large-value branch retains the higher moment and dyadic work.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437a

namespace LeanLab.BHP1997.Decomp437f
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a Decomp437c Decomp437d
open scoped BigOperators

/-- Page 13, the Case 2 split at sigma3 equal to three quarters.
The small part consists of third-factor norms at most length to one quarter. -/
noncomputable def thirdNormPart {ι : Type*} (S : Finset ι) (f : ι → ℂ) (L : ℝ)
    (small : Bool) : Finset ι := S.filter (fun p => decide (‖f p‖ ≤ L ^ (1 / 4 : ℝ)) = small)

/-- Page 13, both third-factor branches partition the actual finite norm sum. -/
theorem sum_third_parts {ι : Type*} (S : Finset ι) (f : ι → ℂ) (L : ℝ) (w : ι → ℝ) :
    ∑ p ∈ S, w p = (∑ p ∈ thirdNormPart S f L true, w p) +
      ∑ p ∈ thirdNormPart S f L false, w p := by
  simpa [thirdNormPart] using
    (Finset.sum_filter_add_sum_filter_not S (fun p => ‖f p‖ ≤ L ^ (1 / 4 : ℝ)) w).symm

/-- Page 13, a value on the nondominant side forces the character-time scale above the length. -/
theorem nondominant_scale_lt {Q F : ℝ} (hF : 1 < F) {z : ℂ}
    (hz : dominanceFlag Q F z = false) : F < Q := by
  have hh : ¬Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F) := of_decide_eq_false hz
  rw [dominance_power_eq_max hF] at hh
  exact lt_of_not_ge (fun h => hh (h.trans (le_max_left _ _)))

/-- Page 13, the Case 2 power saving absorbs a fixed positive logarithmic loss.
The large base X is allowed to exceed x, as in the paper's two choices of X. -/
theorem power_saving_with_log {x X A δ k : ℝ} (hx : 1 < x) (hX : x ≤ X)
    (hA : 0 < A) (hδ : 0 < δ) (hk : 0 ≤ k) :
    X ^ (1 / 2 - δ) * Real.log x ^ k ≤
      (δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  have hA' : 0 < A + k := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlX : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hX
  have hsave := power_saving_to_log_saving (x := X) (β := 1 / 2)
    (lt_of_lt_of_le hx hX) hA' hδ
  have hlog : Real.log X ^ (-(A + k)) ≤ Real.log x ^ (-(A + k)) :=
    Real.rpow_le_rpow_of_nonpos hlx hlX (by linarith)
  have hconst : 0 ≤ (δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ ((δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log X ^ (-(A + k))) *
        Real.log x ^ k := mul_le_mul_of_nonneg_right hsave (Real.rpow_nonneg hlx.le _)
    _ ≤ ((δ / (A + k)) ^ (-(A + k)) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + k))) *
        Real.log x ^ k := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hconst) (Real.rpow_nonneg hlx.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hlx]
      congr 2
      ring

/-- LEAF. Page 13, Case 2 i. The two mean squares control the pair,
while the third norm is at most its length to one quarter.
CONDITIONAL on the original three inputs. -/
theorem neither_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)  := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  let H := 2 * Cm * Ce
  let R := ((ε / 4) / (A + (K0 + 1))) ^ (-(A + (K0 + 1)))
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨H * R, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
  let M := X ^ α₁
  let N := X ^ α₂
  let L := X ^ (1 - α₁ - α₂)
  let Q : ℝ := (q : ℝ) * T
  let P := thirdNormPart (casePart S
    (fun p => dominanceFlag Q M (dirPoly a c₁ c₂ M p.2 (half p.1)))
    (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) false false)
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1)) L true
  have hsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hx3 : 3 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [Real.log_three_gt_d9]
  have hlx0 : 0 < Real.log x := by linarith
  have hXge : x ≤ X := by
    rcases hX with rfl | rfl
    · exact le_rfl
    · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
      calc
        x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hlog0 : 0 ≤ Real.log x ^ (K0 + 1) := Real.rpow_nonneg hlx0.le _
  by_cases hEmpty : P = ∅
  · change (∑ p ∈ P, _) ≤ _
    rw [hEmpty, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hMQ : M < Q := nondominant_scale_lt (by dsimp [M]; linarith) hcase.1
  have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hmoment (f : ℕ → ℂ) (F : ℝ) (hf : CoeffBound f B)
      (hF : 2 ≤ F) (hFx : F ≤ x) (hFQ : F ≤ Q) :
      (∑ p ∈ P, ‖dirPoly f c₁ c₂ F p.2 (half p.1)‖ ^ 2) ≤ H * Q * Real.log x ^ (K0 + 1) := by
    have hmF := hm x F T q P f hf hx hF hFx hT hTx hq hqx hsp htime
    have heF := he f hf x F hlx hF hFx
    have hEnonneg : 0 ≤ energy f c₁ c₂ F := Finset.sum_nonneg (fun n hn => by positivity)
    calc
      _ ≤ Cm * Real.log x * (Q + F) * energy f c₁ c₂ F := hmF
      _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
      _ = H * Q * (Real.log x ^ K0 * Real.log x) := by dsimp [H]; ring
      _ = _ := by rw [Real.rpow_add hlx0, Real.rpow_one]
  have hpair := Decomp437a.pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le hQ0 hQ0 hlog0
    (hmoment a M ha hM hMx hMQ.le) (hmoment b N hb hN hNx hNQ.le)
  have hpair' : (∑ p ∈ P,
      ‖dirPoly a c₁ c₂ M p.2 (half p.1) * dirPoly b c₁ c₂ N p.2 (half p.1)‖) ≤
      H * Q * Real.log x ^ (K0 + 1) := by
    apply hpair.trans_eq
    calc
      _ = H * (Real.sqrt Q * Real.sqrt Q) * Real.log x ^ (K0 + 1) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hQ0]
  have htriple := Decomp437a.triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
    (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
  have hpow : Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
    rw [show Q = X ^ (1 - θ) from hqT]
    dsimp [L]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have hh := case2i_margin hgam
    linarith
  have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
    (by linarith : 0 < ε / 4) (by linarith : 0 ≤ K0 + 1)
  calc
    _ ≤ (H * Q * Real.log x ^ (K0 + 1)) * L ^ (1 / 4 : ℝ) := htriple
    _ = H * (Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ (K0 + 1) := by ring
    _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ (K0 + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
    _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ (K0 + 1)) := by ring
    _ ≤ H * (R * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_left hsave hH.le
    _ = _ := by ring

/-- LEAF. Page 13, Case 2 ii, display 3.13 and the two following bounds.
Only the part above the third norm threshold remains. Apply the sixth
polynomial power bound and its two interpolation weights. OPEN.
CONDITIONAL on the original three inputs. -/
theorem neither_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- Page 13, exact original Case 2 statement assembled from its two written branches.
CONDITIONAL on the two smaller branches and the original inputs. -/
theorem neither_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := neither_small_third hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := neither_large_third hmean hlarge henergy B
  refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_third_parts _ (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
    (X ^ (1 - α₁ - α₂))]
  exact (add_le_add hs0 hs1).trans_eq (by ring)

end LeanLab.BHP1997.Decomp437f
