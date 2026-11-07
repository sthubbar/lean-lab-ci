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

/-! ### Private helpers for the large third-factor branch -/

/-- A dyadic integer level is a real power of `X`, measured against a length `F = X ^ m`. -/
private lemma two_zpow_eq_rpow_level {X m : ℝ} (hX : 1 < X) (hm : 0 < m) (k : ℤ) :
    (2 : ℝ) ^ k = X ^ (m * ((1 / 2 + (k : ℝ) * Real.log 2 / (m * Real.log X)) - 1 / 2)) := by
  have hlX : 0 < Real.log X := Real.log_pos hX
  have hmX : m * Real.log X ≠ 0 := by positivity
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < X),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp
  ring

/-- The minimum of two powers of `X` at least one is the power of their minimum. -/
private lemma rpow_min_eq {X : ℝ} (hX : 1 ≤ X) {a b : ℝ} :
    min (X ^ a) (X ^ b) = X ^ min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Real.rpow_le_rpow_of_exponent_le hX h)]
  · rw [min_eq_right h, min_eq_right (Real.rpow_le_rpow_of_exponent_le hX h)]

/-- `(X ^ b) ^ n = X ^ (b * n)`. -/
private lemma rpow_pow_nat {X b : ℝ} (hX : 0 < X) (n : ℕ) : (X ^ b) ^ n = X ^ (b * n) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero]
  | succ n ih => rw [pow_succ, ih, ← Real.rpow_add hX]; congr 1; push_cast; ring

/-- `1 / X ^ a = X ^ (-a)`. -/
private lemma one_div_rpow {X a : ℝ} (hX : 0 < X) : 1 / X ^ a = X ^ (-a) := by
  rw [show (1 : ℝ) = X ^ (0 : ℝ) from (Real.rpow_zero X).symm, ← Real.rpow_sub hX]
  congr 1
  ring

/-- The first displayed cardinality term of display 3.10 in the exponent scale. -/
private lemma level_first_term {X F V : ℝ} {m σ : ℝ} (hX : 0 < X) (_hm : 0 < m)
    (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) :
    F / V ^ 2 = X ^ (m * (2 - 2 * σ)) := by
  subst hF hV
  rw [rpow_pow_nat hX 2, ← Real.rpow_sub hX]
  congr 1
  ring

/-- The second displayed cardinality term of display 3.10 in the exponent scale, first alternative. -/
private lemma level_second_one {X V : ℝ} {m σ : ℝ} (hX : 0 < X) (_hm : 0 < m)
    (hV : V = X ^ (m * (σ - 1 / 2))) :
    1 / V ^ 2 = X ^ (m * (1 - 2 * σ)) := by
  subst hV
  rw [rpow_pow_nat hX 2, one_div_rpow hX]
  congr 1
  ring

/-- The second displayed cardinality term of display 3.10 in the exponent scale, second alternative. -/
private lemma level_second_six {X F V : ℝ} {m σ : ℝ} (hX : 0 < X) (_hm : 0 < m)
    (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) :
    F / V ^ 6 = X ^ (m * (4 - 6 * σ)) := by
  subst hF hV
  rw [rpow_pow_nat hX 6, ← Real.rpow_sub hX]
  congr 1
  ring

/-- The three cell levels combine into one power of `X`. -/
private lemma cell_level_mul {X : ℝ} (hX : 0 < X) {m n l σ1 σ2 σ3 : ℝ} {k1 k2 k3 : ℤ}
    (h1 : (2 : ℝ) ^ k1 = X ^ (m * (σ1 - 1 / 2)))
    (h2 : (2 : ℝ) ^ k2 = X ^ (n * (σ2 - 1 / 2)))
    (h3 : (2 : ℝ) ^ k3 = X ^ (l * (σ3 - 1 / 2))) :
    (2 : ℝ) ^ k1 * (2 : ℝ) ^ k2 * (2 : ℝ) ^ k3 =
      X ^ (m * (σ1 - 1 / 2) + n * (σ2 - 1 / 2) + l * (σ3 - 1 / 2)) := by
  rw [h1, h2, h3, ← Real.rpow_add hX, ← Real.rpow_add hX]

/-- The exponent of a tiny-value contribution stays below one half. -/
private lemma tiny_exponent {θ ε m n l : ℝ} (hε : 0 < ε) (hεu : ε ≤ 1 / 2)
    (h38 : 1 / 2 + ε < θ) (h36 : |m - n| < 2 * θ - 1 - ε)
    (hθ : θ < 7 / 12) (h37 : l < Thm4.gam θ - ε) (hsum : m + n + l = 1) (hl : 0 < l) :
    (max m (1 - θ) + max (1 - θ) l) / 2 ≤ 1 / 2 - ε / 4 := by
  have hm_th : m < θ - ε / 2 := by
    have h1 := (abs_lt.mp h36).2
    linarith
  have hgam := Thm4.gam_le_one θ
  rcases le_or_gt m (1 - θ) with hm1 | hm1
  · rcases le_or_gt l (1 - θ) with hl1 | hl1
    · rw [max_eq_right hm1, max_eq_left hl1]; linarith
    · rw [max_eq_right hm1, max_eq_right hl1.le]; linarith
  · rcases le_or_gt l (1 - θ) with hl1 | hl1
    · rw [max_eq_left hm1.le, max_eq_left hl1]; linarith
    · rw [max_eq_left hm1.le, max_eq_right hl1.le]
      have hn : ε / 2 ≤ n := by
        by_contra hn
        push_neg at hn
        have hm2 : m < 2 * θ - 1 - ε / 2 := by
          have := (abs_lt.mp h36).2; linarith
        have : 2 - 2 * θ < l := by linarith
        linarith
      linarith

/-- The logarithmic allowance of display 3.10 combines with a coefficient-energy bound. -/
private theorem card_le_of_parts {R C Ce K e1 e2 Qterm E x X : ℝ}
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hE : 0 ≤ E) (hQterm : 0 ≤ Qterm)
    (hlog : 1 ≤ Real.log x) (hX : 1 ≤ X)
    (hcard : R ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm))
    (hEbd : E ≤ Ce * Real.log x ^ K) (hQ : Qterm ≤ X ^ e2) :
    R ≤ (C * (Ce + 16 * Ce ^ 3) * 4) * Real.log x ^ (2 + 3 * K) * X ^ max e1 e2 := by
  have hlx0 : 0 < Real.log x := by linarith
  have hcube : E + 16 * E ^ 3 ≤ (Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K) :=
    energy_cubic_log_bound hE hCe hK hlog hEbd
  have hEE : E + E ^ 3 ≤ (Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K) := by
    have := pow_nonneg hE 3
    nlinarith
  have hXE0 : 0 ≤ X ^ e1 := Real.rpow_nonneg (by linarith) _
  have hXmax : X ^ e1 + Qterm ≤ 2 * X ^ max e1 e2 := by
    have h1 : X ^ e1 ≤ X ^ max e1 e2 := Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _)
    have h2 : Qterm ≤ X ^ max e1 e2 := hQ.trans (Real.rpow_le_rpow_of_exponent_le hX (le_max_right _ _))
    linarith
  have hloglog : Real.log x + Real.log x ^ 2 ≤ 2 * Real.log x ^ 2 := by nlinarith
  have hlogpos : 0 ≤ Real.log x := le_trans (by norm_num) hlog
  have hcombine : (Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K) ≤
      2 * Real.log x ^ (2 + 3 * K) := by
    have h1 : (Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K) ≤
        (2 * Real.log x ^ 2) * Real.log x ^ (3 * K) :=
      mul_le_mul_of_nonneg_right hloglog (Real.rpow_nonneg hlogpos _)
    have h2 : (2 * Real.log x ^ 2) * Real.log x ^ (3 * K) = 2 * Real.log x ^ (2 + 3 * K) := by
      rw [Real.rpow_add hlx0, Real.rpow_two]
      ring
    linarith
  have hfin : (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
      (X ^ e1 + Qterm) ≤
      (C * (Ce + 16 * Ce ^ 3) * 4) * Real.log x ^ (2 + 3 * K) * X ^ max e1 e2 := by
    have hA : 0 ≤ C * (Ce + 16 * Ce ^ 3) := by positivity
    have h1 := mul_le_mul hcombine hXmax (by linarith) (by positivity)
    calc (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
        (X ^ e1 + Qterm)
        = (C * (Ce + 16 * Ce ^ 3)) * (((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
          (X ^ e1 + Qterm)) := by ring
      _ ≤ (C * (Ce + 16 * Ce ^ 3)) * ((2 * Real.log x ^ (2 + 3 * K)) *
          (2 * X ^ max e1 e2)) := mul_le_mul_of_nonneg_left h1 hA
      _ = _ := by ring
  have hstep : C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm) ≤
      (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
        (X ^ e1 + Qterm) := by
    have h1 : C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) ≤
        C * (Real.log x + Real.log x ^ 2) * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K)) := by
      apply mul_le_mul_of_nonneg_left hEE
      positivity
    calc C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm)
        = (C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3)) * (X ^ e1 + Qterm) := by ring
      _ ≤ (C * (Real.log x + Real.log x ^ 2) * ((Ce + 16 * Ce ^ 3) * Real.log x ^ (3 * K))) *
            (X ^ e1 + Qterm) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = _ := by ring
  calc R ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) * (X ^ e1 + Qterm) := hcard
    _ ≤ (C * (Ce + 16 * Ce ^ 3)) * ((Real.log x + Real.log x ^ 2) * Real.log x ^ (3 * K)) *
          (X ^ e1 + Qterm) := hstep
    _ ≤ _ := hfin

/-- The three displayed cardinality terms of display 3.10 for a fixed power `g`. -/
private lemma level_pow_terms {X F V : ℝ} {l σ : ℝ} {g : ℕ} (hX : 0 < X)
    (hF : F = X ^ l) (hV : V = X ^ (l * (σ - 1 / 2))) :
    F ^ g / V ^ (2 * g) = X ^ ((g : ℝ) * l * (2 - 2 * σ)) ∧
    1 / V ^ (2 * g) = X ^ ((g : ℝ) * l * (1 - 2 * σ)) ∧
    F ^ g / V ^ (6 * g) = X ^ ((g : ℝ) * l * (4 - 6 * σ)) := by
  subst hF hV
  have h1 : (X ^ l) ^ g = X ^ (l * (g : ℝ)) := rpow_pow_nat hX g
  have h2 : (X ^ (l * (σ - 1 / 2))) ^ (2 * g) =
      X ^ ((l * (σ - 1 / 2)) * (2 * (g : ℝ))) := by
    rw [rpow_pow_nat hX (2 * g)]
    push_cast
    ring_nf
  have h6 : (X ^ (l * (σ - 1 / 2))) ^ (6 * g) =
      X ^ ((l * (σ - 1 / 2)) * (6 * (g : ℝ))) := by
    rw [rpow_pow_nat hX (6 * g)]
    push_cast
    ring_nf
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, h2, ← Real.rpow_sub hX]; congr 1; ring
  · rw [h2, one_div_rpow hX]; congr 1; ring
  · rw [h1, h6, ← Real.rpow_sub hX]; congr 1; ring

/-- Display 3.10, first power: the minimum-form second term is `qT` times `X` to `f` of sigma. -/
private theorem bracket_one {X F V Q θ m σ : ℝ} (hX : 0 < X) (hX1 : 1 ≤ X) (_hm : 0 < m)
    (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) (hQ : Q = X ^ (1 - θ)) :
    Q * min (1 / V ^ 2) (F / V ^ 6) ≤ X ^ (1 - θ + m * Thm4.f σ) := by
  have hmin : min (m * (1 - 2 * σ)) (m * (4 - 6 * σ)) = m * Thm4.f σ := by
    unfold Thm4.f
    rcases le_total (1 - 2 * σ) (4 - 6 * σ) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  rw [level_second_one hX _hm hV, level_second_six hX _hm hF hV, hQ, rpow_min_eq hX1,
    ← Real.rpow_add hX, hmin]

/-- Display 3.10, fixed power `g`: the second term is at most `qT` times its sixth-moment branch. -/
private theorem bracket_gen {X F V Q θ l σ : ℝ} {g : ℕ} (hX : 0 < X) (hX1 : 1 ≤ X)
    (_hl : 0 < l) (_hg : 1 ≤ g)
    (hF : F = X ^ l) (hV : V = X ^ (l * (σ - 1 / 2))) (hQ : Q = X ^ (1 - θ)) :
    Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) ≤
      X ^ (1 - θ + (g : ℝ) * l * (4 - 6 * σ)) := by
  obtain ⟨-, -, h6⟩ := level_pow_terms hX hF hV (g := g)
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hmin := min_le_right (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))
  calc Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))
      ≤ Q * (F ^ g / V ^ (6 * g)) := mul_le_mul_of_nonneg_left hmin hQ0
    _ = X ^ (1 - θ) * X ^ ((g : ℝ) * l * (4 - 6 * σ)) := by rw [h6, hQ]
    _ = X ^ (1 - θ + (g : ℝ) * l * (4 - 6 * σ)) := by rw [← Real.rpow_add hX]

/-- A nonnegative factor distributes over a minimum. -/
private lemma mul_min_of_nonneg {a b c : ℝ} (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) := by
  rcases le_total b c with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith)]
  · rw [min_eq_right h, min_eq_right (by nlinarith)]

/-- A cell's cardinality obeys the smallest of its three level-set bounds. -/
private theorem card_le_three_min {R C D s1 s2 s3 x X : ℝ}
    (hlog : 1 ≤ Real.log x) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (h1 : R ≤ C * Real.log x ^ D * X ^ s1)
    (h2 : R ≤ C * Real.log x ^ D * X ^ s2)
    (h3 : R ≤ C * Real.log x ^ D * X ^ s3) :
    R ≤ C * Real.log x ^ D * X ^ min s1 (min s2 s3) := by
  have hCL : 0 ≤ C * Real.log x ^ D := by
    have : 0 ≤ Real.log x ^ D := Real.rpow_nonneg (le_trans (by norm_num) hlog) _
    positivity
  have hXs : X ^ min s1 (min s2 s3) = min (X ^ s1) (min (X ^ s2) (X ^ s3)) := by
    rw [rpow_min_eq hX, rpow_min_eq hX]
  have heq : C * Real.log x ^ D * X ^ min s1 (min s2 s3) =
      min (C * Real.log x ^ D * X ^ s1)
        (min (C * Real.log x ^ D * X ^ s2) (C * Real.log x ^ D * X ^ s3)) := by
    rw [hXs, mul_min_of_nonneg hCL, mul_min_of_nonneg hCL]
  rw [heq]
  exact le_min h1 (le_min h2 h3)

/-- Raise the constant and the logarithmic allowance of a cell bound. -/
private theorem card_le_weaken {R C Cg D Dg s x X : ℝ}
    (hlog : 1 ≤ Real.log x) (hC : 0 ≤ C) (hCg : C ≤ Cg) (hD : D ≤ Dg) (hX : 1 ≤ X)
    (h : R ≤ C * Real.log x ^ D * X ^ s) : R ≤ Cg * Real.log x ^ Dg * X ^ s := by
  have hL0 : 0 ≤ Real.log x ^ D := Real.rpow_nonneg (le_trans (by norm_num) hlog) _
  have hL : Real.log x ^ D ≤ Real.log x ^ Dg := Real.rpow_le_rpow_of_exponent_le hlog hD
  have hXs : 0 ≤ X ^ s := Real.rpow_nonneg (by linarith) _
  have hCg0 : 0 ≤ Cg := le_trans hC hCg
  have hLg0 : 0 ≤ Real.log x ^ Dg := Real.rpow_nonneg (le_trans (by norm_num) hlog) _
  calc R ≤ C * Real.log x ^ D * X ^ s := h
    _ ≤ Cg * Real.log x ^ Dg * X ^ s := by
        exact mul_le_mul (mul_le_mul hCg hL hL0 hCg0) le_rfl hXs (mul_nonneg hCg0 hLg0)

/-- The non-dominant tag, read at a dyadic cell level, forces the case-3 second length scale. -/
private theorem nondominant_exponent {X N Q θ n σ : ℝ} {z : ℂ} {k : ℤ}
    (hX : 1 < X) (hn : 0 < n) (hN : N = X ^ n) (hQ : Q = X ^ (1 - θ)) (hσ : 1 / 2 ≤ σ)
    (hV : (2 : ℝ) ^ k = X ^ (n * (σ - 1 / 2))) (hlevel : (2 : ℝ) ^ k ≤ ‖z‖)
    (hNQ : N < Q) (hz : dominanceFlag Q N z = false) :
    n * Thm4.c σ < 1 - θ := by
  have hX0 : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos hX
  have hN1 : 1 < N := by rw [hN]; exact Real.one_lt_rpow hX hn
  have hmax : ¬ (Q ≤ max N (‖z‖ ^ 4)) := by
    intro h
    exact (of_decide_eq_false hz) (by rw [dominance_power_eq_max hN1]; exact h)
  have hQgt : ‖z‖ ^ 4 < Q := by
    have h := not_le.mp (fun hc => hmax (le_trans hc (le_max_right _ _)))
    exact h
  have hlev4 : X ^ (4 * (n * (σ - 1 / 2))) ≤ ‖z‖ ^ 4 := by
    have hpow : (X ^ (n * (σ - 1 / 2))) ^ 4 = X ^ (4 * (n * (σ - 1 / 2))) := by
      rw [rpow_pow_nat hX0 4]; congr 1; ring
    rw [← hpow]
    exact pow_le_pow_left₀ (by positivity) (by rw [← hV]; exact hlevel) 4
  have h4 : 4 * (n * (σ - 1 / 2)) < 1 - θ := by
    have hlt : X ^ (4 * (n * (σ - 1 / 2))) < X ^ (1 - θ) := by
      rw [hQ] at hQgt
      exact lt_of_le_of_lt hlev4 hQgt
    have hlog := Real.log_lt_log (by positivity) hlt
    rw [Real.log_rpow hX0, Real.log_rpow hX0] at hlog
    exact lt_of_mul_lt_mul_right hlog hlX.le
  have hNQex : n < 1 - θ := by
    have hlt : X ^ n < X ^ (1 - θ) := by simpa only [hN, hQ] using hNQ
    have hlog := Real.log_lt_log (by positivity) hlt
    rw [Real.log_rpow hX0, Real.log_rpow hX0] at hlog
    exact lt_of_mul_lt_mul_right hlog hlX.le
  unfold Thm4.c
  split_ifs with h
  · linarith
  · nlinarith

/-- A dyadic cell sum costs at most the cube of the level count. -/
private theorem sum_over_cells {q : ℕ} {S : Finset (ℝ × DirichletCharacter ℂ q)}
    {f1 f2 f3 : ℝ × DirichletCharacter ℂ q → ℂ} {x V H Clev : ℝ}
    (hlog : 1 ≤ Real.log x) (hV : 0 < V) (hClev : 0 ≤ Clev) (hH : 0 ≤ H)
    (h1 : ∀ p ∈ S, 1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ V)
    (h2 : ∀ p ∈ S, 1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ V)
    (h3 : ∀ p ∈ S, 1 ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ V)
    (hcell : ∀ k ∈ dyadicLevels 1 V ×ˢ dyadicLevels 1 V ×ˢ dyadicLevels 1 V,
      (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤ H)
    (hlev : ((dyadicLevels 1 V).card : ℝ) ≤ Clev * Real.log x) :
    (∑ p ∈ S, ‖f1 p * f2 p * f3 p‖) ≤ (Clev * Real.log x) ^ 3 * H := by
  have hsum := dyadic_sum_bound S f1 f2 f3 (H := H) (v := 1) (V := V) one_pos h1 h2 h3 hcell
  have hcard0 : (0 : ℝ) ≤ ((dyadicLevels 1 V).card : ℝ) := by positivity
  have hcube : (((dyadicLevels 1 V).card : ℝ)) ^ 3 ≤ (Clev * Real.log x) ^ 3 :=
    pow_le_pow_left₀ hcard0 hlev 3
  exact hsum.trans (mul_le_mul_of_nonneg_right hcube hH)

/-- Display 3.10 at a dyadic cell level, in the exponent form the cell sum needs.
One instantiation serves the first and second factors at `g = 1` and the third at the
selected power `g`. -/
private theorem cell_card_of_level {q : ℕ} {S : Finset (ℝ × DirichletCharacter ℂ q)}
    {x X θ F V Q m σ e1 e2 : ℝ} {g : ℕ} {C Ce K E : ℝ}
    (hlog : 1 ≤ Real.log x) (hX1 : 1 ≤ X) (hm : 0 < m)
    (hF : F = X ^ m) (hV : V = X ^ (m * (σ - 1 / 2))) (hQ : Q = X ^ (1 - θ))
    (hFpos : 0 < F) (hVpos : 0 < V) (hV1 : 1 ≤ V)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hb1 : F ^ g / V ^ (2 * g) = X ^ e1)
    (hb2 : Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) ≤ X ^ e2)
    (hcard : (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
      (F ^ g / V ^ (2 * g) + Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))))
    (hEbd : E ≤ Ce * Real.log x ^ K) :
    (S.card : ℝ) ≤ (C * (Ce + 16 * Ce ^ 3) * 4) * Real.log x ^ (2 + 3 * K) * X ^ max e1 e2 := by
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hinner : 0 < min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) :=
    lt_min (by positivity) (by positivity)
  have hQn : 0 ≤ Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)) := le_of_lt (mul_pos hQpos hinner)
  exact card_le_of_parts (R := (S.card : ℝ)) (C := C) (Ce := Ce) (K := K) (e1 := e1)
    (e2 := e2) (Qterm := Q * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g))) (E := E)
    (x := x) (X := X) hC hCe hK hE hQn hlog hX1 (by simpa only [← hb1] using hcard) hEbd hb2

/-- Where one of the first two factors is at most one, the mean squares of the three
factors and the exponent inequality `tiny_exponent` give the whole contribution. -/
private theorem tiny_final {q : ℕ} {P TIN : Finset (ℝ × DirichletCharacter ℂ q)}
    {f1 f2 f3 : ℝ × DirichletCharacter ℂ q → ℂ} {x X ε D HB a b e : ℝ}
    (hlog : 1 ≤ Real.log x) (hX1 : 1 ≤ X) (hHB : 0 ≤ HB) (hD : 0 ≤ D) (hε : 0 < ε)
    (hsub : TIN ⊆ P)
    (htiny : ∀ p ∈ TIN, ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1)
    (hA : (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ HB * X ^ a * Real.log x ^ D)
    (hB : (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ HB * X ^ b * Real.log x ^ D)
    (hE : (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ HB * X ^ e * Real.log x ^ D)
    (hexp : max a b + e ≤ 1 - ε / 2) :
    (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ≤ (4 * HB) * Real.log x ^ D * X ^ (1 / 2 - ε / 4) := by
  have hlx0 : 0 < Real.log x := lt_of_lt_of_le one_pos hlog
  -- one of the first two factors is at most one, so it costs nothing
  have hstep : ∀ p ∈ TIN, ‖f1 p * f2 p * f3 p‖ ≤ max ‖f1 p‖ ‖f2 p‖ * ‖f3 p‖ := by
    intro p hp
    rw [norm_mul, norm_mul]
    have h3 : (0 : ℝ) ≤ ‖f3 p‖ := norm_nonneg _
    rcases htiny p hp with h | h
    · have : ‖f1 p‖ * ‖f2 p‖ ≤ max ‖f1 p‖ ‖f2 p‖ := by
        calc ‖f1 p‖ * ‖f2 p‖ ≤ 1 * ‖f2 p‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
          _ = ‖f2 p‖ := one_mul _
          _ ≤ _ := le_max_right _ _
      exact mul_le_mul_of_nonneg_right this h3
    · have : ‖f1 p‖ * ‖f2 p‖ ≤ max ‖f1 p‖ ‖f2 p‖ := by
        calc ‖f1 p‖ * ‖f2 p‖ ≤ ‖f1 p‖ * 1 := mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = ‖f1 p‖ := mul_one _
          _ ≤ _ := le_max_left _ _
      exact mul_le_mul_of_nonneg_right this h3
  -- Cauchy-Schwarz for the pair of first factors against the third
  have hS2 : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ^ 2 ≤
      (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2) * (∑ p ∈ TIN, ‖f3 p‖ ^ 2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq TIN
      (fun p => max ‖f1 p‖ ‖f2 p‖) (fun p => ‖f3 p‖)
    calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ^ 2
        ≤ (∑ p ∈ TIN, max ‖f1 p‖ ‖f2 p‖ * ‖f3 p‖) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => norm_nonneg _))
            (Finset.sum_le_sum hstep) 2
      _ ≤ _ := hcs
  have hmax2 : (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2) ≤
      HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D := by
    have hpt : ∀ p ∈ P, (max ‖f1 p‖ ‖f2 p‖) ^ 2 ≤ ‖f1 p‖ ^ 2 + ‖f2 p‖ ^ 2 := by
      intro p _
      rcases le_total ‖f1 p‖ ‖f2 p‖ with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg ‖f1 p‖]
      · rw [max_eq_left h]; nlinarith [sq_nonneg ‖f2 p‖]
    have hmono1 : (∑ p ∈ TIN, ‖f1 p‖ ^ 2) ≤ ∑ p ∈ P, ‖f1 p‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have hmono2 : (∑ p ∈ TIN, ‖f2 p‖ ^ 2) ≤ ∑ p ∈ P, ‖f2 p‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    calc (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2)
        ≤ ∑ p ∈ TIN, (‖f1 p‖ ^ 2 + ‖f2 p‖ ^ 2) :=
          Finset.sum_le_sum (fun p hp => hpt p (hsub hp))
      _ = (∑ p ∈ TIN, ‖f1 p‖ ^ 2) + ∑ p ∈ TIN, ‖f2 p‖ ^ 2 := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hmono1.trans hA) (hmono2.trans hB)
  have hEmono : (∑ p ∈ TIN, ‖f3 p‖ ^ 2) ≤ HB * X ^ e * Real.log x ^ D :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans hE
  -- the product of the two bounds is below the square of the target
  have hXmax : X ^ a + X ^ b ≤ 2 * X ^ max a b := by
    have h1 : X ^ a ≤ X ^ max a b := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
    have h2 : X ^ b ≤ X ^ max a b := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
    linarith
  have hlog2 : Real.log x ^ D * Real.log x ^ D = Real.log x ^ (D + D) :=
    (Real.rpow_add hlx0 _ _).symm
  have hXe : X ^ max a b * X ^ e = X ^ (max a b + e) := (Real.rpow_add (by linarith : (0:ℝ) < X) _ _).symm
  have hXfin : X ^ (max a b + e) ≤ X ^ (1 - ε / 2) := Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hR2 : (4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4)) ^ 2 =
      16 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (1 - ε / 2) := by
    have h1 : (X ^ (1 / 2 - ε / 4)) ^ 2 = X ^ (2 * (1 / 2 - ε / 4)) := by
      rw [rpow_pow_nat (by linarith : (0:ℝ) < X) 2]; congr 1; ring
    have h2 : (Real.log x ^ D) ^ 2 = Real.log x ^ (D + D) := by
      rw [rpow_pow_nat hlx0 2]; congr 1; ring
    rw [mul_pow, mul_pow, mul_pow, h1, h2]
    ring_nf
  have hprod : (HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D) *
      (HB * X ^ e * Real.log x ^ D) ≤
      (4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4)) ^ 2 := by
    rw [hR2]
    have hXp : 0 ≤ X ^ max a b := Real.rpow_nonneg (by linarith) _
    have hexp0 : 0 ≤ X ^ e := Real.rpow_nonneg (by linarith) _
    have hlogD : 0 ≤ Real.log x ^ D := Real.rpow_nonneg hlx0.le _
    have h1 : HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D ≤
        2 * HB * Real.log x ^ D * X ^ max a b := by
      have := mul_le_mul_of_nonneg_left hXmax (by positivity : (0:ℝ) ≤ HB * Real.log x ^ D)
      nlinarith
    have h2 : (2 * HB * Real.log x ^ D * X ^ max a b) * (HB * X ^ e * Real.log x ^ D) =
        2 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (max a b + e) := by
      rw [← hlog2, ← hXe]; ring
    have h3 : 2 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (max a b + e) ≤
        16 * HB ^ 2 * Real.log x ^ (D + D) * X ^ (1 - ε / 2) := by
      have := mul_le_mul_of_nonneg_left hXfin (by positivity : (0:ℝ) ≤ Real.log x ^ (D + D))
      have hHB2 : 0 ≤ HB ^ 2 := sq_nonneg HB
      nlinarith
    calc (HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D) *
          (HB * X ^ e * Real.log x ^ D)
        ≤ (2 * HB * Real.log x ^ D * X ^ max a b) * (HB * X ^ e * Real.log x ^ D) := by
          apply mul_le_mul_of_nonneg_right h1
          exact mul_nonneg (mul_nonneg hHB (by positivity)) (by positivity)
      _ = _ := h2
      _ ≤ _ := h3
  have hmid : (∑ p ∈ TIN, (max ‖f1 p‖ ‖f2 p‖) ^ 2) * (∑ p ∈ TIN, ‖f3 p‖ ^ 2) ≤
      (HB * X ^ a * Real.log x ^ D + HB * X ^ b * Real.log x ^ D) *
        (HB * X ^ e * Real.log x ^ D) :=
    mul_le_mul hmax2 hEmono (Finset.sum_nonneg (fun p _ => by positivity)) (by positivity)
  have hfin : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ^ 2 ≤
      (4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4)) ^ 2 :=
    hS2.trans (hmid.trans hprod)
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖ :=
    Finset.sum_nonneg (fun p _ => norm_nonneg _)
  have hR0 : (0 : ℝ) ≤ 4 * HB * Real.log x ^ D * X ^ (1 / 2 - ε / 4) := by positivity
  nlinarith [hfin, hS0, hR0]

/-- One dyadic cell, once its cardinality is below `X ^ s` and the classification has put
`s + E` below one half minus `ε/72`, contributes that much. -/
private theorem cell_sum_combine {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q))
    (f1 f2 f3 : ℝ × DirichletCharacter ℂ q → ℂ) (k : ℤ × ℤ × ℤ)
    {x X s E Ccell Dcell ε : ℝ} (hX0 : 0 < X) (hX1 : 1 ≤ X) (hε : 0 < ε)
    (hCcell : 0 ≤ Ccell) (hlog : 1 ≤ Real.log x)
    (hpos : ∀ p ∈ S, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖)
    (hcard : ((dyadicCell S f1 f2 f3 k).card : ℝ) ≤ Ccell * Real.log x ^ Dcell * X ^ s)
    (hlevels : 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 = 8 * X ^ E)
    (hclass : s + E ≤ 1 / 2 - ε / 72) :
    (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
      8 * Ccell * Real.log x ^ Dcell * X ^ (1 / 2 - ε / 72) := by
  have hcell := dyadic_cell_sum_le S f1 f2 f3 k hpos
  have hmul : ((dyadicCell S f1 f2 f3 k).card : ℝ) *
      (8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) ≤
      (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E) := by
    rw [hlevels]
    exact mul_le_mul hcard (le_refl _) (by positivity) (by positivity)
  have heq : (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E) =
      8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) := by
    calc (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E)
        = 8 * (Ccell * Real.log x ^ Dcell) * (X ^ s * X ^ E) := by ring
      _ = 8 * (Ccell * Real.log x ^ Dcell) * X ^ (s + E) := by rw [Real.rpow_add hX0]
      _ = 8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) := by ring
  have hstep : X ^ (s + E) ≤ X ^ (1 / 2 - ε / 72) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hclass
  have hfin : 8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) ≤
      8 * Ccell * Real.log x ^ Dcell * X ^ (1 / 2 - ε / 72) := by
    apply mul_le_mul_of_nonneg_left hstep
    positivity
  calc (∑ p ∈ dyadicCell S f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖)
      ≤ ((dyadicCell S f1 f2 f3 k).card : ℝ) *
          (8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := hcell
    _ ≤ (Ccell * Real.log x ^ Dcell * X ^ s) * (8 * X ^ E) := hmul
    _ = 8 * Ccell * Real.log x ^ Dcell * X ^ (s + E) := heq
    _ ≤ _ := hfin
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
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
  -- ## constants, all named before `θ`
  obtain ⟨Cn, hCn, hnorm⟩ := dirPoly_norm_uniform B c₁ c₂ hc₁ (hc₁.trans hc₂)
  have hCn1 : 0 < max Cn 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, hen⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce1, K1, hCe1, hK1, hen1⟩ := energy_log_uniform henergy
    (((1 : ℕ) : ℝ) * (max B 0 + 1)) (c₁ ^ 1) (c₂ ^ 1)
    (pow_pos hc₁ 1) (pow_lt_pow_left₀ hc₂ hc₁.le (by omega))
  obtain ⟨Ce3, K3, hCe3, hK3, hen3⟩ := energy_log_uniform henergy
    (((3 : ℕ) : ℝ) * (max B 0 + 1)) (c₁ ^ 3) (c₂ ^ 3)
    (pow_pos hc₁ 3) (pow_lt_pow_left₀ hc₂ hc₁.le (by omega))
  obtain ⟨Cp1, hCp1, hcard1⟩ := power_level_min hmean hlarge B c₁ c₂ hc₁ hc₂ 1 (by norm_num)
  obtain ⟨Cp3, hCp3, hcard3⟩ := power_level_min hmean hlarge B c₁ c₂ hc₁ hc₂ 3 (by norm_num)
  let Ce1' : ℝ := Ce1 * max 1 ((3 : ℝ) ^ K1)
  let Ce3' : ℝ := Ce3 * max 1 ((3 : ℝ) ^ K3)
  have hCe1'0 : 0 < Ce1' := by
    dsimp [Ce1']
    exact mul_pos hCe1 (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hCe3'0 : 0 < Ce3' := by
    dsimp [Ce3']
    exact mul_pos hCe3 (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  let Cf1 : ℝ := Cp1 * (Ce1' + 16 * Ce1' ^ 3) * 4
  let Df1 : ℝ := 2 + 3 * K1
  let Cf3 : ℝ := Cp3 * (Ce3' + 16 * Ce3' ^ 3) * 4
  let Df3 : ℝ := 2 + 3 * K3
  let Cst : ℝ := max Cf1 Cf3
  let Dst : ℝ := max (max Df1 Df3) (K0 + 1) + 2
  have hCf10 : 0 ≤ Cf1 := by
    dsimp [Cf1]
    have := hCe1'0.le
    have := hCp1.le
    positivity
  have hCf30 : 0 ≤ Cf3 := by
    dsimp [Cf3]
    have := hCe3'0.le
    have := hCp3.le
    positivity
  have hCst0 : 0 ≤ Cst := le_trans hCf10 (le_max_left _ _)
  have hCf1le : Cf1 ≤ Cst := le_max_left _ _
  have hCf3le : Cf3 ≤ Cst := le_max_right _ _
  have hDf1le : Df1 ≤ Dst := by
    have h : Df1 ≤ max (max Df1 Df3) (K0 + 1) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    dsimp only [Dst]; linarith
  have hDf3le : Df3 ≤ Dst := by
    have h : Df3 ≤ max (max Df1 Df3) (K0 + 1) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    dsimp only [Dst]; linarith
  have hK0le : K0 + 1 ≤ Dst := by
    have h : K0 + 1 ≤ max (max Df1 Df3) (K0 + 1) := le_max_right _ _
    dsimp only [Dst]; linarith
  have hDst0 : 0 ≤ Dst := by linarith
  have hDst2 : (2 : ℝ) ≤ Dst := by
    have h1 : 0 ≤ Df1 := by dsimp [Df1]; linarith
    have h : (0 : ℝ) ≤ max (max Df1 Df3) (K0 + 1) := le_trans h1 (le_trans (le_max_left _ _) (le_max_left _ _))
    linarith
  let H : ℝ := 2 * Cm * Ce + 1
  have hH0 : 0 < H := by
    dsimp [H]
    have := mul_pos hCm hCe
    linarith
  have hHm : 2 * Cm * Ce ≤ H := by dsimp [H]; linarith
  let Clev : ℝ := (Real.log (max Cn 1) + 2) / Real.log 2 + 2
  have hClev0 : 0 ≤ Clev := by
    have h1 : 0 ≤ Real.log (max Cn 1) := Real.log_nonneg (le_max_right _ _)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [Clev]; positivity
  let R1 : ℝ := ((ε / 4) / (A + Dst)) ^ (-(A + Dst))
  let R2 : ℝ := ((ε / 72) / (A + (3 + Dst))) ^ (-(A + (3 + Dst)))
  have hR10 : 0 ≤ R1 := Real.rpow_nonneg (by positivity) _
  have hR20 : 0 ≤ R2 := Real.rpow_nonneg (by positivity) _
  refine ⟨4 * H * R1 + 8 * Cst * Clev ^ 3 * R2, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
  let M : ℝ := X ^ α₁
  let N : ℝ := X ^ α₂
  let L : ℝ := X ^ (1 - α₁ - α₂)
  let Q : ℝ := (q : ℝ) * T
  let f1 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly a c₁ c₂ M p.2 (half p.1)
  let f2 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly b c₁ c₂ N p.2 (half p.1)
  let f3 : ℝ × DirichletCharacter ℂ q → ℂ := fun p => dirPoly e c₁ c₂ L p.2 (half p.1)
  let P : Finset (ℝ × DirichletCharacter ℂ q) := thirdNormPart (casePart S
    (fun p => dominanceFlag Q M (f1 p))
    (fun p => dominanceFlag Q N (f2 p)) false false) f3 L false
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
  have hXlt : 1 < X := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ : Q = X ^ (1 - θ) := hqT
  have hα₁ : 0 < α₁ := by
    rcases le_or_gt α₁ 0 with h | h
    · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
    · exact h
  have hα₂ : 0 < α₂ := by
    rcases le_or_gt α₂ 0 with h | h
    · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
    · exact h
  have hl : 0 < 1 - α₁ - α₂ := by
    rcases le_or_gt (1 - α₁ - α₂) 0 with h | h
    · have := Real.rpow_le_one_of_one_le_of_nonpos hX1 h; linarith
    · exact h
  have hml : 0 ≤ 1 - α₁ - α₂ := hl.le
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hL0 : 0 < L := by dsimp [L]; positivity
  have hL1 : 1 ≤ L := by linarith
  have hmsum : α₁ + α₂ + (1 - α₁ - α₂) = 1 := by ring
  have hLQ : L ≤ Q := by
    rw [hQ]
    dsimp [L]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have hg1 := Thm4.gam_le_one θ
    nlinarith
  have hmemP : ∀ p ∈ P, dominanceFlag Q M (f1 p) = false ∧
      dominanceFlag Q N (f2 p) = false ∧ L ^ (1 / 4 : ℝ) < ‖f3 p‖ := by
    intro p hp
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨(Finset.mem_filter.mp h1).2.1, (Finset.mem_filter.mp h1).2.2,
      not_le.mp (of_decide_eq_false (Finset.mem_filter.mp hp).2)⟩
  have hPsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hPsub hp) p' (hPsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hPsub hp)
  have hf3big : ∀ p ∈ P, 1 ≤ ‖f3 p‖ := by
    intro p hp
    have h := (hmemP p hp).2.2
    have h1 : (1 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    linarith
  have hgoal : (∑ p ∈ P, ‖f1 p * f2 p * f3 p‖) ≤
      (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
    by_cases hEmpty : P = ∅
    · rw [hEmpty, Finset.sum_empty]
      have h2 : (0 : ℝ) ≤ R2 := hR20
      have h1 : (0 : ℝ) ≤ R1 := hR10
      positivity
    obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hMQ : M < Q := nondominant_scale_lt (by dsimp [M]; linarith) (hmemP p₀ hp₀).1
    have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) (hmemP p₀ hp₀).2.1
    have hlogD : ∀ {d : ℝ}, d ≤ Dst → Real.log x ^ d ≤ Real.log x ^ Dst :=
      fun hd' => Real.rpow_le_rpow_of_exponent_le hlx hd'
    -- ## the three mean squares on `P`
    have hmomentM : (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
      have hh := hm x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
      have hQM : Q + M ≤ 2 * Q := by linarith
      have heM : energy a c₁ c₂ M ≤ Ce * Real.log x ^ K0 := hen a ha x M hlx hM hMx
      have hEnn : 0 ≤ energy a c₁ c₂ M := Finset.sum_nonneg (fun n hn => by positivity)
      have hstep : Cm * Real.log x * (Q + M) * energy a c₁ c₂ M ≤
          Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
        have h1 : 0 ≤ Cm * Real.log x := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hQM h1) heM hEnn (by positivity)
      have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
        rw [Real.rpow_add hlx0, Real.rpow_one]
      have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
          H * Q * Real.log x ^ Dst := by
        have h1 : 2 * Cm * Ce ≤ H := hHm
        have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0le
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
          (Real.rpow_nonneg hlx0.le _) (by positivity)
      calc (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ Cm * Real.log x * (Q + M) * energy a c₁ c₂ M := hh
        _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
        _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
        _ ≤ H * Q * Real.log x ^ Dst := hfin
        _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
    have hmomentN : (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
      have hh := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
      have hQN : Q + N ≤ 2 * Q := by linarith
      have heN : energy b c₁ c₂ N ≤ Ce * Real.log x ^ K0 := hen b hb x N hlx hN hNx
      have hEnn : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
      have hstep : Cm * Real.log x * (Q + N) * energy b c₁ c₂ N ≤
          Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
        have h1 : 0 ≤ Cm * Real.log x := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hQN h1) heN hEnn (by positivity)
      have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
        rw [Real.rpow_add hlx0, Real.rpow_one]
      have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
          H * Q * Real.log x ^ Dst := by
        have h1 : 2 * Cm * Ce ≤ H := hHm
        have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0le
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
          (Real.rpow_nonneg hlx0.le _) (by positivity)
      calc (∑ p ∈ P, ‖f2 p‖ ^ 2) ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hh
        _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
        _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
        _ ≤ H * Q * Real.log x ^ Dst := hfin
        _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
    have hmomentE : (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ H * X ^ (1 - θ) * Real.log x ^ Dst := by
      have hh := hm x L T q P e hecoeff hx hL hLx hT hTx hq hqx hsp htime
      have hQL : Q + L ≤ 2 * Q := by linarith
      have heL : energy e c₁ c₂ L ≤ Ce * Real.log x ^ K0 := hen e hecoeff x L hlx hL hLx
      have hEnn : 0 ≤ energy e c₁ c₂ L := Finset.sum_nonneg (fun n hn => by positivity)
      have hstep : Cm * Real.log x * (Q + L) * energy e c₁ c₂ L ≤
          Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by
        have h1 : 0 ≤ Cm * Real.log x := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hQL h1) heL hEnn (by positivity)
      have hlog : Real.log x ^ K0 * Real.log x = Real.log x ^ (K0 + 1) := by
        rw [Real.rpow_add hlx0, Real.rpow_one]
      have hfin : 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) ≤
          H * Q * Real.log x ^ Dst := by
        have h1 : 2 * Cm * Ce ≤ H := hHm
        have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0le
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
          (Real.rpow_nonneg hlx0.le _) (by positivity)
      calc (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ Cm * Real.log x * (Q + L) * energy e c₁ c₂ L := hh
        _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
        _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
        _ ≤ H * Q * Real.log x ^ Dst := hfin
        _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
    -- ## one factor at most one: the tiny part
    let TIN : Finset (ℝ × DirichletCharacter ℂ q) := P.filter (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1)
    let MAIN : Finset (ℝ × DirichletCharacter ℂ q) :=
      P.filter (fun p => ¬ (‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1))
    have hTINsub : TIN ⊆ P := Finset.filter_subset _ _
    have hMAINsub : MAIN ⊆ P := Finset.filter_subset _ _
    have hsplit : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) +
        (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) = ∑ p ∈ P, ‖f1 p * f2 p * f3 p‖ :=
      Finset.sum_filter_add_sum_filter_not P (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1) _
    have hexptiny : max (1 - θ) (1 - θ) + (1 - θ) ≤ 1 - ε / 2 := by
      rw [max_self]
      linarith
    have htinyA : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ≤
        4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
      have hbase := tiny_final (q := q) (P := P) (TIN := TIN) (f1 := f1) (f2 := f2) (f3 := f3)
        (x := x) (X := X) (ε := ε) (D := Dst) (HB := H) (a := 1 - θ) (b := 1 - θ) (e := 1 - θ)
        hlx hX1 hH0.le hDst0 hε hTINsub (fun p hp => (Finset.mem_filter.mp hp).2)
        hmomentM hmomentN hmomentE hexptiny
      have hsave1 : X ^ (1 / 2 - ε / 4) * Real.log x ^ Dst ≤
          R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        power_saving_with_log (x := x) (X := X) (A := A) (δ := ε / 4) (k := Dst)
          (by linarith) hXge hA (by linarith) hDst0
      calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖)
          ≤ 4 * H * Real.log x ^ Dst * X ^ (1 / 2 - ε / 4) := hbase
        _ = 4 * H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ Dst) := by ring
        _ ≤ 4 * H * (R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hsave1 (by positivity)
        _ = 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
    have hMAINA : (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) ≤
        8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
      have hV1 : 1 ≤ max Cn 1 * x ^ 2 := by
        have h1 : 1 ≤ max Cn 1 := le_max_right _ _
        have h2 : 1 ≤ x ^ 2 := one_le_pow₀ (by linarith)
        exact one_le_mul_of_one_le_of_one_le h1 h2
      have hbig1 : ∀ p ∈ MAIN, 1 ≤ ‖f1 p‖ ∧ ‖f1 p‖ ≤ max Cn 1 * x ^ 2 := by
        intro p hp
        have hntiny := (Finset.mem_filter.mp hp).2
        push_neg at hntiny
        refine ⟨le_of_lt hntiny.1, ?_⟩
        have hb1 := hnorm a ha M (by linarith : 1 ≤ M) q p.2 p.1
        have hMx2 : M ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hM0.le hMx 2
        calc ‖f1 p‖ ≤ Cn * M ^ 2 := hb1
          _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hMx2 hCn.le
          _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have hbig2 : ∀ p ∈ MAIN, 1 ≤ ‖f2 p‖ ∧ ‖f2 p‖ ≤ max Cn 1 * x ^ 2 := by
        intro p hp
        have hntiny := (Finset.mem_filter.mp hp).2
        push_neg at hntiny
        refine ⟨le_of_lt hntiny.2, ?_⟩
        have hb2 := hnorm b hb N (by linarith : 1 ≤ N) q p.2 p.1
        have hNx2 : N ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hN0.le hNx 2
        calc ‖f2 p‖ ≤ Cn * N ^ 2 := hb2
          _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hNx2 hCn.le
          _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have hbig3 : ∀ p ∈ MAIN, 1 ≤ ‖f3 p‖ ∧ ‖f3 p‖ ≤ max Cn 1 * x ^ 2 := by
        intro p hp
        refine ⟨hf3big p (hMAINsub hp), ?_⟩
        have hb3 := hnorm e hecoeff L (by linarith : 1 ≤ L) q p.2 p.1
        have hLx2 : L ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hL0.le hLx 2
        calc ‖f3 p‖ ≤ Cn * L ^ 2 := hb3
          _ ≤ Cn * x ^ 2 := mul_le_mul_of_nonneg_left hLx2 hCn.le
          _ ≤ max Cn 1 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have hClev' : ((dyadicLevels 1 (max Cn 1 * x ^ 2)).card : ℝ) ≤ Clev * Real.log x :=
        quadratic_level_count (le_max_right _ _) (by linarith) hlx
      have hzp : ∀ j : ℤ, 0 ≤ j → (1 : ℝ) ≤ (2 : ℝ) ^ j := by
        intro j hj
        rw [← zpow_zero (2 : ℝ)]
        exact zpow_le_zpow_right₀ (by norm_num) hj
      have hcell : ∀ k ∈ dyadicLevels 1 (max Cn 1 * x ^ 2) ×ˢ dyadicLevels 1 (max Cn 1 * x ^ 2) ×ˢ
          dyadicLevels 1 (max Cn 1 * x ^ 2),
          (∑ p ∈ dyadicCell MAIN f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) ≤
            8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72) := by
        intro k hk
        obtain ⟨hk1, hk23⟩ := Finset.mem_product.mp hk
        obtain ⟨hk2, hk3⟩ := Finset.mem_product.mp hk23
        have hk1nn : (0 : ℤ) ≤ k.1 := by
          have h := (Finset.mem_Icc.mp hk1).1
          rwa [Int.log_one_right] at h
        have hk2nn : (0 : ℤ) ≤ k.2.1 := by
          have h := (Finset.mem_Icc.mp hk2).1
          rwa [Int.log_one_right] at h
        have hk3nn : (0 : ℤ) ≤ k.2.2 := by
          have h := (Finset.mem_Icc.mp hk3).1
          rwa [Int.log_one_right] at h
        let V1 : ℝ := (2 : ℝ) ^ k.1
        let V2 : ℝ := (2 : ℝ) ^ k.2.1
        let V3 : ℝ := (2 : ℝ) ^ k.2.2
        have hV1ge : (1 : ℝ) ≤ V1 := by simpa only [V1] using hzp k.1 hk1nn
        have hV2ge : (1 : ℝ) ≤ V2 := by simpa only [V2] using hzp k.2.1 hk2nn
        have hV3ge : (1 : ℝ) ≤ V3 := by simpa only [V3] using hzp k.2.2 hk3nn
        have hV1pos : 0 < V1 := lt_of_lt_of_le zero_lt_one hV1ge
        have hV2pos : 0 < V2 := lt_of_lt_of_le zero_lt_one hV2ge
        have hV3pos : 0 < V3 := lt_of_lt_of_le zero_lt_one hV3ge
        let σ1 : ℝ := 1 / 2 + (k.1 : ℝ) * Real.log 2 / (α₁ * Real.log X)
        let σ2 : ℝ := 1 / 2 + (k.2.1 : ℝ) * Real.log 2 / (α₂ * Real.log X)
        let σ3 : ℝ := 1 / 2 + (k.2.2 : ℝ) * Real.log 2 / ((1 - α₁ - α₂) * Real.log X)
        have hlev1 : V1 = X ^ (α₁ * (σ1 - 1 / 2)) := by
          simpa only [V1, σ1] using two_zpow_eq_rpow_level (X := X) (m := α₁) hXlt hα₁ k.1
        have hlev2 : V2 = X ^ (α₂ * (σ2 - 1 / 2)) := by
          simpa only [V2, σ2] using two_zpow_eq_rpow_level (X := X) (m := α₂) hXlt hα₂ k.2.1
        have hlev3 : V3 = X ^ ((1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
          simpa only [V3, σ3] using two_zpow_eq_rpow_level (X := X) (m := 1 - α₁ - α₂) hXlt hl k.2.2
        have hσ1 : 1 / 2 ≤ σ1 := by
          have hk : (0 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast hk1nn
          have hnum : 0 ≤ (k.1 : ℝ) * Real.log 2 := by
            have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
          have hden : 0 < α₁ * Real.log X := by
            have := Real.log_pos hXlt; positivity
          have h := div_nonneg hnum hden.le
          simp only [σ1]; linarith
        have hσ2 : 1 / 2 ≤ σ2 := by
          have hk : (0 : ℝ) ≤ (k.2.1 : ℝ) := by exact_mod_cast hk2nn
          have hnum : 0 ≤ (k.2.1 : ℝ) * Real.log 2 := by
            have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
          have hden : 0 < α₂ * Real.log X := by
            have := Real.log_pos hXlt; positivity
          have h := div_nonneg hnum hden.le
          simp only [σ2]; linarith
        have hσ3 : 1 / 2 ≤ σ3 := by
          have hk : (0 : ℝ) ≤ (k.2.2 : ℝ) := by exact_mod_cast hk3nn
          have hnum : 0 ≤ (k.2.2 : ℝ) * Real.log 2 := by
            have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
          have hden : 0 < (1 - α₁ - α₂) * Real.log X := by
            have := Real.log_pos hXlt; positivity
          have h := div_nonneg hnum hden.le
          simp only [σ3]; linarith
        let Cell : Finset (ℝ × DirichletCharacter ℂ q) := dyadicCell MAIN f1 f2 f3 k
        have hCellMain : Cell ⊆ MAIN := Finset.filter_subset _ _
        have hCellP : Cell ⊆ P := fun p hp => hMAINsub (hCellMain hp)
        have hCellS : Cell ⊆ S := fun p hp => hPsub (hCellP hp)
        have hspC : WellSpaced Cell := by
          intro p hp p' hp' hne heq
          exact hspace p (hCellS hp) p' (hCellS hp') hne heq
        have htimeC : ∀ p ∈ Cell, |p.1| ≤ T := fun p hp => htimes p (hCellS hp)
        have hposC : ∀ p ∈ Cell, 0 < ‖f1 p‖ ∧ 0 < ‖f2 p‖ ∧ 0 < ‖f3 p‖ := by
          intro p hp
          have h1 : 1 ≤ ‖f1 p‖ := (hbig1 p (hCellMain hp)).1
          have h2 : 1 ≤ ‖f2 p‖ := (hbig2 p (hCellMain hp)).1
          have h3 : 1 ≤ ‖f3 p‖ := (hbig3 p (hCellMain hp)).1
          exact ⟨by linarith, by linarith, by linarith⟩
        have hlow1 : ∀ p ∈ Cell, V1 ≤ ‖f1 p‖ := fun p hp => by
          simpa only [V1] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
            (hposC p hp).2.1 (hposC p hp).2.2).1
        have hlow2 : ∀ p ∈ Cell, V2 ≤ ‖f2 p‖ := fun p hp => by
          simpa only [V2] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
            (hposC p hp).2.1 (hposC p hp).2.2).2.2.1
        have hlow3 : ∀ p ∈ Cell, V3 ≤ ‖f3 p‖ := fun p hp => by
          simpa only [V3] using (dyadic_cell_bounds MAIN f1 f2 f3 k hp (hposC p hp).1
            (hposC p hp).2.1 (hposC p hp).2.2).2.2.2.2.1
        by_cases hEmp : Cell = ∅
        · have hzero : (∑ p ∈ dyadicCell MAIN f1 f2 f3 k, ‖f1 p * f2 p * f3 p‖) = 0 := by
            rw [show dyadicCell MAIN f1 f2 f3 k = Cell from rfl, hEmp, Finset.sum_empty]
          rw [hzero]
          have h1 : 0 ≤ Cst := hCst0
          have h2 : 0 ≤ Real.log x ^ Dst := Real.rpow_nonneg hlx0.le _
          have h3 : 0 ≤ X ^ (1 / 2 - ε / 72) := Real.rpow_nonneg hX0.le _
          positivity
        obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmp
        -- ## the first factor at power one
        have hEa : energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) ≤
            Ce1' * Real.log x ^ K1 := by
          have hbase := hen1 (truncatedCoeffs a c₁ c₂ M ^ 1).coeff
            (truncated_power_bound (c2 := c₂) ha hc₁.le hM0.le 1) x (M ^ 1) hlx
            (by simpa using hM) (by simpa using hMx)
          have hg1 : (1 : ℝ) ≤ max 1 ((3 : ℝ) ^ K1) := le_max_left _ _
          have h3 : 0 ≤ Real.log x ^ K1 := Real.rpow_nonneg hlx0.le _
          have h4 : 0 ≤ Ce1 := hCe1.le
          have hmul : Real.log x ^ K1 ≤ max 1 ((3 : ℝ) ^ K1) * Real.log x ^ K1 := by
            simpa using mul_le_mul_of_nonneg_right hg1 h3
          calc energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1)
              ≤ Ce1 * Real.log x ^ K1 := hbase
            _ ≤ Ce1 * (max 1 ((3 : ℝ) ^ K1) * Real.log x ^ K1) :=
                mul_le_mul_of_nonneg_left hmul h4
            _ = Ce1' * Real.log x ^ K1 := by dsimp [Ce1']; ring
        have hEa0 : (0 : ℝ) ≤
            energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) :=
          Finset.sum_nonneg (fun n hn => by positivity)
        have hcca : (Cell.card : ℝ) ≤ Cf1 * Real.log x ^ Df1 *
            X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := by
          have hcarda := hcard1 x M T V1 q Cell a ha hx hM hMx
            hT hTx hq hqx hV1pos hspC htimeC hlow1
          have hc := cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := M)
            (V := V1) (Q := Q) (m := α₁) (σ := σ1)
            (e1 := α₁ * (2 - 2 * σ1)) (e2 := 1 - θ + α₁ * Thm4.f σ1) (g := 1)
            (C := Cp1) (Ce := Ce1') (K := K1)
            (E := energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1))
            hlx hX1 hα₁ rfl hlev1 hQ hM0 hV1pos hV1ge
            hCp1.le hCe1'0.le hK1 hEa0
            (by simpa using level_first_term hX0 hα₁ rfl hlev1)
            (by simpa using bracket_one hX0 hX1 hα₁ rfl hlev1 hQ)
            hcarda hEa
          simpa only [Cf1, Df1] using hc
        have hcca' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
            X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) :=
          card_le_weaken (R := (Cell.card : ℝ)) (C := Cf1) (Cg := Cst)
            (D := Df1) (Dg := Dst) hlx hCf10 hCf1le hDf1le hX1 hcca
        -- ## the second factor at power one
        have hEb : energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) ≤
            Ce1' * Real.log x ^ K1 := by
          have hbase := hen1 (truncatedCoeffs b c₁ c₂ N ^ 1).coeff
            (truncated_power_bound (c2 := c₂) hb hc₁.le hN0.le 1) x (N ^ 1) hlx
            (by simpa using hN) (by simpa using hNx)
          have hg1 : (1 : ℝ) ≤ max 1 ((3 : ℝ) ^ K1) := le_max_left _ _
          have h3 : 0 ≤ Real.log x ^ K1 := Real.rpow_nonneg hlx0.le _
          have h4 : 0 ≤ Ce1 := hCe1.le
          have hmul : Real.log x ^ K1 ≤ max 1 ((3 : ℝ) ^ K1) * Real.log x ^ K1 := by
            simpa using mul_le_mul_of_nonneg_right hg1 h3
          calc energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1)
              ≤ Ce1 * Real.log x ^ K1 := hbase
            _ ≤ Ce1 * (max 1 ((3 : ℝ) ^ K1) * Real.log x ^ K1) :=
                mul_le_mul_of_nonneg_left hmul h4
            _ = Ce1' * Real.log x ^ K1 := by dsimp [Ce1']; ring
        have hEb0 : (0 : ℝ) ≤
            energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) :=
          Finset.sum_nonneg (fun n hn => by positivity)
        have hccb : (Cell.card : ℝ) ≤ Cf1 * Real.log x ^ Df1 *
            X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) := by
          have hcardb := hcard1 x N T V2 q Cell b hb hx hN hNx
            hT hTx hq hqx hV2pos hspC htimeC hlow2
          have hc := cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := N)
            (V := V2) (Q := Q) (m := α₂) (σ := σ2)
            (e1 := α₂ * (2 - 2 * σ2)) (e2 := 1 - θ + α₂ * Thm4.f σ2) (g := 1)
            (C := Cp1) (Ce := Ce1') (K := K1)
            (E := energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1))
            hlx hX1 hα₂ rfl hlev2 hQ hN0 hV2pos hV2ge
            hCp1.le hCe1'0.le hK1 hEb0
            (by simpa using level_first_term hX0 hα₂ rfl hlev2)
            (by simpa using bracket_one hX0 hX1 hα₂ rfl hlev2 hQ)
            hcardb hEb
          simpa only [Cf1, Df1] using hc
        have hccb' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
            X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
          card_le_weaken (R := (Cell.card : ℝ)) (C := Cf1) (Cg := Cst)
            (D := Df1) (Dg := Dst) hlx hCf10 hCf1le hDf1le hX1 hccb
        -- ## the third factor at the sixth power
        have hEe : energy (truncatedCoeffs e c₁ c₂ L ^ 3).coeff (c₁ ^ 3) (c₂ ^ 3) (L ^ 3) ≤
            Ce3' * Real.log x ^ K3 := by
          have hambg : 1 ≤ Real.log (x ^ 3) := by
            rw [Real.log_pow]
            show (1 : ℝ) ≤ 3 * Real.log x
            linarith
          have hFL : L ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hL0.le hLx 3
          have hbase := hen3 (truncatedCoeffs e c₁ c₂ L ^ 3).coeff
            (truncated_power_bound (c2 := c₂) hecoeff hc₁.le hL0.le 3) (x ^ 3) (L ^ 3) hambg
            (by simpa using hL.trans (le_self_pow₀ hL1 (by norm_num : 3 ≠ 0)))
            (by simpa using hFL)
          have hrw : Real.log (x ^ 3) ^ K3 = (3 : ℝ) ^ K3 * Real.log x ^ K3 := by
            rw [Real.log_pow, Real.mul_rpow (by norm_num) hlx0.le]
            norm_num
          rw [hrw] at hbase
          have hg1 : (3 : ℝ) ^ K3 ≤ max 1 ((3 : ℝ) ^ K3) := le_max_right _ _
          have h3 : 0 ≤ Real.log x ^ K3 := Real.rpow_nonneg hlx0.le _
          have h4 : 0 ≤ Ce3 := hCe3.le
          calc energy (truncatedCoeffs e c₁ c₂ L ^ 3).coeff (c₁ ^ 3) (c₂ ^ 3) (L ^ 3)
              ≤ Ce3 * ((3 : ℝ) ^ K3 * Real.log x ^ K3) := hbase
            _ ≤ Ce3 * (max 1 ((3 : ℝ) ^ K3) * Real.log x ^ K3) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg1 h3) h4
            _ = Ce3' * Real.log x ^ K3 := by dsimp [Ce3']; ring
        have hEe0 : (0 : ℝ) ≤
            energy (truncatedCoeffs e c₁ c₂ L ^ 3).coeff (c₁ ^ 3) (c₂ ^ 3) (L ^ 3) :=
          Finset.sum_nonneg (fun n hn => by positivity)
        obtain ⟨hpow1, hpow2, hpow3⟩ := level_pow_terms (X := X) (F := L)
          (V := V3) (l := 1 - α₁ - α₂) (σ := σ3) (g := 3) hX0 rfl hlev3
        have hcce : (Cell.card : ℝ) ≤ Cf3 * Real.log x ^ Df3 *
            X ^ max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
              (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3)) := by
          have hcarde := hcard3 x L T V3 q Cell e hecoeff hx hL hLx
            hT hTx hq hqx hV3pos hspC htimeC hlow3
          have hc := cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := L)
            (V := V3) (Q := Q) (m := 1 - α₁ - α₂) (σ := σ3)
            (e1 := (3 : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
            (e2 := 1 - θ + (3 : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) (g := 3)
            (C := Cp3) (Ce := Ce3') (K := K3)
            (E := energy (truncatedCoeffs e c₁ c₂ L ^ 3).coeff (c₁ ^ 3) (c₂ ^ 3) (L ^ 3))
            hlx hX1 hl rfl hlev3 hQ hL0 hV3pos hV3ge
            hCp3.le hCe3'0.le hK3 hEe0
            (by simpa using hpow1)
            (by simpa using bracket_gen hX0 hX1 hl (by norm_num : 1 ≤ 3) rfl hlev3 hQ)
            hcarde hEe
          simpa only [Cf3, Df3] using hc
        have hcce' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
            X ^ max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
              (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3)) :=
          card_le_weaken (R := (Cell.card : ℝ)) (C := Cf3) (Cg := Cst)
            (D := Df3) (Dg := Dst) hlx hCf30 hCf3le hDf3le hX1 hcce
        -- ## the smallest of the three cardinality bounds
        let s3 : ℝ := max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
          (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3))
        let sall : ℝ := min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
          (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
        have hcardmin : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ sall :=
          card_le_three_min hlx hCst0 hX1 hcca' hccb' (by simpa only [s3] using hcce')
        have hs1 : sall ≤ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := min_le_left _ _
        have hs2 : sall ≤ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
          (min_le_right _ _).trans (min_le_left _ _)
        have hs3 : sall ≤ s3 := (min_le_right _ _).trans (min_le_right _ _)
        -- ## the two non-dominance tags
        have hcnd1 : α₁ * Thm4.c σ1 < 1 - θ :=
          nondominant_exponent (X := X) (N := M) (Q := Q) (θ := θ) (n := α₁) (σ := σ1)
            (z := f1 p₀) (k := k.1) hXlt hα₁ rfl hQ hσ1 hlev1 (hlow1 p₀ hp₀) hMQ
            ((hmemP p₀ (hCellP hp₀)).1)
        have hcnd2 : α₂ * Thm4.c σ2 < 1 - θ :=
          nondominant_exponent (X := X) (N := N) (Q := Q) (θ := θ) (n := α₂) (σ := σ2)
            (z := f2 p₀) (k := k.2.1) hXlt hα₂ rfl hQ hσ2 hlev2 (hlow2 p₀ hp₀) hNQ
            ((hmemP p₀ (hCellP hp₀)).2.1)
        have hnn1 : α₁ * (2 - 2 * σ1) ≤ 1 - θ + α₁ * Thm4.f σ1 := by
          by_contra hcon
          push_neg at hcon
          exact absurd (Thm4.dominance.mp hcon.le) (not_le.mpr hcnd1)
        have hnn2 : α₂ * (2 - 2 * σ2) ≤ 1 - θ + α₂ * Thm4.f σ2 := by
          by_contra hcon
          push_neg at hcon
          exact absurd (Thm4.dominance.mp hcon.le) (not_le.mpr hcnd2)
        have hMred : sall ≤ 1 - θ + α₁ * Thm4.f σ1 := by
          refine hs1.trans ?_
          rw [max_eq_right hnn1]
        have hNred : sall ≤ 1 - θ + α₂ * Thm4.f σ2 := by
          refine hs2.trans ?_
          rw [max_eq_right hnn2]
        have hLred : sall ≤ max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
            (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3)) := hs3
        -- ## the Case 2 ii cell exponent
        have hclassF : sall + α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
            (1 - α₁ - α₂) * (σ3 - 1 / 2) ≤ 1 / 2 - ε / 72 :=
          (case2_cell_exponent (θ := θ) (ε := ε) (m := α₁) (n := α₂)
            (l := 1 - α₁ - α₂) (σ1 := σ1) (σ2 := σ2) (σ3 := σ3) (s := sall)
            hε hα₁.le hα₂.le hml hmsum (by linarith) hMred hNred hLred).le
        have hclass : sall + (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
            (1 - α₁ - α₂) * (σ3 - 1 / 2)) ≤ 1 / 2 - ε / 72 := by linarith
        have hlevels : 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
            8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
              (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
          have hmul : (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
              X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
                (1 - α₁ - α₂) * (σ3 - 1 / 2)) :=
            cell_level_mul hX0 (by simpa only [V1] using hlev1)
              (by simpa only [V2] using hlev2) (by simpa only [V3] using hlev3)
          calc 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
              8 * ((2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2) := by ring
            _ = 8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) +
                  (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by rw [hmul]
        exact cell_sum_combine MAIN f1 f2 f3 k hX0 hX1 hε hCst0 hlx
          (fun p hp => ⟨lt_of_lt_of_le zero_lt_one (hbig1 p hp).1,
            lt_of_lt_of_le zero_lt_one (hbig2 p hp).1,
            lt_of_lt_of_le zero_lt_one (hbig3 p hp).1⟩)
          hcardmin hlevels hclass
      have hsum := sum_over_cells (q := q) (S := MAIN) (f1 := f1) (f2 := f2) (f3 := f3)
        (x := x) (V := max Cn 1 * x ^ 2)
        (H := 8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72)) (Clev := Clev)
        hlx (by positivity) hClev0 (by positivity) hbig1 hbig2 hbig3 hcell hClev'
      have h3r : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := Real.rpow_natCast _ _
      have hlog3 : Real.log x ^ (3 + Dst) = Real.log x ^ 3 * Real.log x ^ Dst := by
        rw [Real.rpow_add hlx0 (3 : ℝ) Dst, h3r]
      have hsave2 : X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst) ≤
          R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        power_saving_with_log (x := x) (X := X) (A := A) (δ := ε / 72) (k := 3 + Dst)
          (by linarith) hXge hA (by linarith) (by linarith)
      calc (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
          ≤ (Clev * Real.log x) ^ 3 *
              (8 * Cst * Real.log x ^ Dst * X ^ (1 / 2 - ε / 72)) := hsum
        _ = 8 * Cst * Clev ^ 3 * (Real.log x ^ 3 * Real.log x ^ Dst) *
              X ^ (1 / 2 - ε / 72) := by ring
        _ = 8 * Cst * Clev ^ 3 * Real.log x ^ (3 + Dst) * X ^ (1 / 2 - ε / 72) := by
            rw [← hlog3]
        _ = 8 * Cst * Clev ^ 3 * (X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst)) := by ring
        _ ≤ 8 * Cst * Clev ^ 3 * (R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hsave2 (by positivity)
        _ = 8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
    rw [← hsplit]
    calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) + (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
        ≤ 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
          8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        add_le_add htinyA hMAINA
      _ = (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
          ring
  exact hgoal

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
