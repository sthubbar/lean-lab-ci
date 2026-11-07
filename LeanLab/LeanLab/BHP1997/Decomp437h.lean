/-
P0069, page 14, the two third-factor branches of mixed Case 3.
The small branch uses the completed dominant square moment and a mean square.
The large branch retains the bounded-power interpolation work.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437f

namespace LeanLab.BHP1997.Decomp437h
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a Decomp437c Decomp437d Decomp437f
open scoped BigOperators

/-- LEAF. Page 14, Case 3 i, display 3.14.
The third factor has norm at most its length to one quarter.
CONDITIONAL on the original three inputs. -/
theorem first_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
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
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  obtain ⟨Cd, Dd, hCd, hDd, hd⟩ := Decomp437e.dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
  let D0 := max Dd (K0 + 1)
  have hD0 : 0 ≤ D0 := hDd.trans (le_max_left _ _)
  let H := Cd + 2 * Cm * Ce
  let R := ((ε / 4) / (A + D0)) ^ (-(A + D0))
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
    (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) true false)
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
  have hlog0 : 0 ≤ Real.log x ^ D0 := Real.rpow_nonneg hlx0.le _
  by_cases hEmpty : P = ∅
  · change (∑ p ∈ P, _) ≤ _
    rw [hEmpty, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hHc : Cd ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 2 * Cm * Ce := by positivity
    linarith
  have hHm : 2 * Cm * Ce ≤ H := by dsimp [H]; linarith
  have hlogd : Real.log x ^ Dd ≤ Real.log x ^ D0 :=
    Real.rpow_le_rpow_of_exponent_le hlx (le_max_left _ _)
  have hlogk : Real.log x ^ (K0 + 1) ≤ Real.log x ^ D0 :=
    Real.rpow_le_rpow_of_exponent_le hlx (le_max_right _ _)
  have hmomentM : (∑ p ∈ P, ‖dirPoly a c₁ c₂ M p.2 (half p.1)‖ ^ 2) ≤
      H * M * Real.log x ^ D0 := by
    have hh := hd x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
      (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1)
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hHc (by dsimp [M]; positivity))
      hlogd (by positivity) (by dsimp [M]; positivity))
  have hmomentN : (∑ p ∈ P, ‖dirPoly b c₁ c₂ N p.2 (half p.1)‖ ^ 2) ≤
      H * Q * Real.log x ^ D0 := by
    have hmF := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
    have heF := he b hb x N hlx hN hNx
    have hEnonneg : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
    calc
      _ ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hmF
      _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
      _ = (2 * Cm * Ce) * Q * (Real.log x ^ K0 * Real.log x) := by ring
      _ = (2 * Cm * Ce) * Q * Real.log x ^ (K0 + 1) := by rw [Real.rpow_add hlx0, Real.rpow_one]
      _ ≤ H * Q * Real.log x ^ D0 := mul_le_mul
        (mul_le_mul_of_nonneg_right hHm hQ0) hlogk (by positivity) (by positivity)
  have hpair' := Decomp437a.pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le
    (by dsimp [M]; positivity) hQ0 (Real.rpow_nonneg hlx0.le D0) hmomentM hmomentN
  have htriple := Decomp437a.triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
    (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
  have hpow : Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, show Q = X ^ (1 - θ) from hqT]
    dsimp [M, L]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
      ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have hab' := (abs_lt.mp hab).2
    linarith
  have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
    (by linarith : 0 < ε / 4) hD0
  calc
    _ ≤ (H * Real.sqrt M * Real.sqrt Q * Real.log x ^ D0) * L ^ (1 / 4 : ℝ) := htriple
    _ = H * (Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ D0 := by ring
    _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ D0 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
    _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ D0) := by ring
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

set_option maxHeartbeats 4000000 in
/-- LEAF. Page 14, Case 3 ii, displays 3.15 and 3.16.
Only the part above the third norm threshold remains. The bounded choice
of polynomial power and its level-set summation remain OPEN.
Retain the existing proved repair for the g equal to one branch.
CONDITIONAL on the original three inputs. -/
theorem first_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
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
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro ε hε hεu' c₁ c₂ hc₁ hc₂ Kfun A hA
  have hεu : ε ≤ 1 / 2 := le_of_lt hεu'
  -- ## constants, all named before `θ`
  obtain ⟨Cn, hCn, hnorm⟩ := dirPoly_norm_uniform B c₁ c₂ hc₁ (hc₁.trans hc₂)
  have hCn1 : 0 < max Cn 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨g0', hg0'1, hcut'⟩ := exists_uniform_power_cutoff hε
  let g0 : ℕ := max g0' 3
  have hg0 : 3 ≤ g0 := le_max_right _ _
  have hg01 : 1 ≤ g0 := le_trans hg0'1 (le_max_left _ _)
  have hlevel_pkg : ∀ g : ℕ, 1 ≤ g → ∃ C : ℝ, 0 < C ∧ ∀ x F T V : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q), ∀ a : ℕ → ℂ,
      CoeffBound a B → 2 ≤ x → 2 ≤ F → F ≤ x → 2 < T → T ≤ x / 4 → 1 ≤ q → (q : ℝ) ≤ x →
      0 < V → WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
      (∀ p ∈ S, V ≤ ‖dirPoly a c₁ c₂ F p.2 (half p.1)‖) →
      (let E := energy (truncatedCoeffs a c₁ c₂ F ^ g).coeff (c₁ ^ g) (c₂ ^ g) (F ^ g);
        (S.card : ℝ) ≤ C * (Real.log x + Real.log x ^ 2) * (E + E ^ 3) *
          (F ^ g / V ^ (2 * g) +
            (q : ℝ) * T * min (1 / V ^ (2 * g)) (F ^ g / V ^ (6 * g)))) := by
    intro g hg
    exact power_level_min hmean hlarge B c₁ c₂ hc₁ hc₂ g hg
  choose Cpm hCpmpos hCpm using hlevel_pkg
  have henergy_pkg : ∀ g : ℕ, 1 ≤ g → ∃ Ce K : ℝ, 0 < Ce ∧ 0 ≤ K ∧
      ∀ f : ℕ → ℂ, CoeffBound f ((g : ℝ) * (max B 0 + 1)) → ∀ x F : ℝ,
        1 ≤ Real.log x → 2 ≤ F → F ≤ x →
        energy f (c₁ ^ g) (c₂ ^ g) F ≤ Ce * Real.log x ^ K := by
    intro g hg
    exact energy_log_uniform henergy ((g : ℝ) * (max B 0 + 1)) (c₁ ^ g) (c₂ ^ g)
      (pow_pos hc₁ g) (pow_lt_pow_left₀ hc₂ hc₁.le (by omega))
  choose Cem Kem hCempos hKem hEn using henergy_pkg
  obtain ⟨Cd, Dd, hCd, hDd, hd⟩ :=
    Decomp437e.dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, hen⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  let Cfam : ℕ → ℝ := fun g => if h : 1 ≤ g then Cpm g h else 1
  let Cefam : ℕ → ℝ := fun g => if h : 1 ≤ g then Cem g h * max 1 ((g0 : ℝ) ^ Kem g h) else 1
  let Kfam : ℕ → ℝ := fun g => if h : 1 ≤ g then Kem g h else 0
  have hCfam : ∀ g (hg : 1 ≤ g), Cfam g = Cpm g hg := fun g hg => by
    dsimp [Cfam]; rw [dif_pos hg]
  have hCefam : ∀ g (hg : 1 ≤ g),
      Cefam g = Cem g hg * max 1 ((g0 : ℝ) ^ Kem g hg) := fun g hg => by
    dsimp [Cefam]; rw [dif_pos hg]
  have hKfam : ∀ g (hg : 1 ≤ g), Kfam g = Kem g hg := fun g hg => by
    dsimp [Kfam]; rw [dif_pos hg]
  have hCfam0 : ∀ g, 1 ≤ g → 0 < Cfam g := fun g hg => by
    rw [hCfam g hg]; exact hCpmpos g hg
  have hCefam0 : ∀ g, 1 ≤ g → 0 < Cefam g := fun g hg => by
    rw [hCefam g hg]
    exact mul_pos (hCempos g hg) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hKfam0 : ∀ g, 1 ≤ g → 0 ≤ Kfam g := fun g hg => by
    rw [hKfam g hg]; exact hKem g hg
  let Cf : ℕ → ℝ := fun g => Cfam g * (Cefam g + 16 * Cefam g ^ 3) * 4
  let Df : ℕ → ℝ := fun g => 2 + 3 * Kfam g
  have hCf0 : ∀ g, 1 ≤ g → 0 ≤ Cf g := fun g hg => by
    have h1 := (hCfam0 g hg).le
    have h2 : 0 ≤ Cefam g + 16 * Cefam g ^ 3 := by
      have := (hCefam0 g hg).le; positivity
    dsimp [Cf]; positivity
  have hDf0 : ∀ g, 1 ≤ g → 0 ≤ Df g := fun g hg => by
    have := hKfam0 g hg; dsimp [Df]; linarith
  let Sg : Finset ℕ := Finset.Icc 1 g0
  have hSgne : Sg.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩⟩
  let Cst : ℝ := ∑ g ∈ Sg, Cf g
  let Dsum : ℝ := ∑ g ∈ Sg, Df g
  let Dst : ℝ := Dsum + Dd + (K0 + 1) + 2
  have hCst0 : 0 ≤ Cst :=
    Finset.sum_nonneg (fun g hg => hCf0 g (Finset.mem_Icc.mp hg).1)
  have hDsum0 : 0 ≤ Dsum :=
    Finset.sum_nonneg (fun g hg => hDf0 g (Finset.mem_Icc.mp hg).1)
  have hDst0 : 0 ≤ Dst := by dsimp [Dst]; linarith
  have hCf_le : ∀ g ∈ Sg, Cf g ≤ Cst := fun g hg =>
    Finset.single_le_sum (fun i hi => hCf0 i (Finset.mem_Icc.mp hi).1) hg
  have hDf_le : ∀ g ∈ Sg, Df g ≤ Dst := fun g hg => by
    have h1 : Df g ≤ Dsum :=
      Finset.single_le_sum (fun i hi => hDf0 i (Finset.mem_Icc.mp hi).1) hg
    have h2 : 0 ≤ Dd := hDd
    have h3 : 0 ≤ K0 + 1 := by linarith
    dsimp [Dst]; linarith
  have hDd_le : Dd ≤ Dst := by dsimp [Dst]; linarith
  have hK0_le : K0 + 1 ≤ Dst := by dsimp [Dst]; linarith [hDd]
  have h2_le : (2 : ℝ) ≤ Dst := by dsimp [Dst]; linarith [hDd, hK0]
  let Clev : ℝ := (Real.log (max Cn 1) + 2) / Real.log 2 + 2
  let H : ℝ := Cd + 2 * Cm * Ce + Cn + 1
  have hCmCe : 2 * Cm * Ce ≤ H := by dsimp [H]; nlinarith [hCd, hCn]
  have hHd : Cd ≤ H := by dsimp [H]; nlinarith [hCm, hCe, hCn]
  have hHn : Cn ≤ H := by dsimp [H]; nlinarith [hCd, hCm, hCe]
  have hH0 : 0 < H := lt_of_lt_of_le hCd hHd
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
    (fun p => dominanceFlag Q N (f2 p)) true false) f3 L false
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
  have hθ5 : θ ≤ 3 / 5 := by linarith
  have hcut : θ - ε / 2 < Thm4.d θ g0 :=
    (hcut' θ (by linarith) (by linarith)).trans_le
      (Thm4.d_mono (by linarith) (Nat.cast_nonneg _) (by exact_mod_cast le_max_left g0' 3))
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
  have hmemP : ∀ p ∈ P, dominanceFlag Q M (f1 p) = true ∧
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
    · rw [hEmpty, Finset.sum_empty]; positivity
    obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) (hmemP p₀ hp₀).2.1
    have hlogD : ∀ {d : ℝ}, d ≤ Dst → Real.log x ^ d ≤ Real.log x ^ Dst :=
      fun hd' => Real.rpow_le_rpow_of_exponent_le hlx hd'
    have hmomentM : (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ H * X ^ α₁ * Real.log x ^ Dst := by
      have hh := hd x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
        (fun p hp => (hmemP p hp).1)
      have h1 : Real.log x ^ Dd ≤ Real.log x ^ Dst := hlogD hDd_le
      have h2 : Cd * M ≤ H * M := mul_le_mul_of_nonneg_right hHd hM0.le
      calc (∑ p ∈ P, ‖f1 p‖ ^ 2) ≤ Cd * M * Real.log x ^ Dd := hh
        _ ≤ H * M * Real.log x ^ Dst :=
            mul_le_mul h2 h1 (Real.rpow_nonneg hlx0.le _) (by positivity)
        _ = H * X ^ α₁ * Real.log x ^ Dst := by rw [show M = X ^ α₁ from rfl]
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
        have h1 : 2 * Cm * Ce ≤ H := hCmCe
        have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
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
        have h1 : 2 * Cm * Ce ≤ H := hCmCe
        have h2 : Real.log x ^ (K0 + 1) ≤ Real.log x ^ Dst := hlogD hK0_le
        exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hQ0) h2
          (Real.rpow_nonneg hlx0.le _) (by positivity)
      calc (∑ p ∈ P, ‖f3 p‖ ^ 2) ≤ Cm * Real.log x * (Q + L) * energy e c₁ c₂ L := hh
        _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := hstep
        _ = 2 * Cm * Ce * Q * Real.log x ^ (K0 + 1) := by rw [← hlog]; ring
        _ ≤ H * Q * Real.log x ^ Dst := hfin
        _ = H * X ^ (1 - θ) * Real.log x ^ Dst := by rw [hQ]
    -- ## the large-value part over the dyadic cells
    let TIN : Finset (ℝ × DirichletCharacter ℂ q) := P.filter (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1)
    let MAIN : Finset (ℝ × DirichletCharacter ℂ q) :=
      P.filter (fun p => ¬ (‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1))
    have hTINsub : TIN ⊆ P := Finset.filter_subset _ _
    have hMAINsub : MAIN ⊆ P := Finset.filter_subset _ _
    have hsplit : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) +
        (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖) = ∑ p ∈ P, ‖f1 p * f2 p * f3 p‖ :=
      Finset.sum_filter_add_sum_filter_not P (fun p => ‖f1 p‖ ≤ 1 ∨ ‖f2 p‖ ≤ 1) _
    have hexptiny : max α₁ (1 - θ) + (1 - θ) ≤ 1 - ε / 2 := by
      have hα : α₁ < θ - ε / 2 := by
        have h1 := (abs_lt.mp hab).2
        have h2 : α₁ + α₂ < 1 := by linarith
        linarith
      rcases le_or_gt α₁ (1 - θ) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h.le]; linarith
    have htinyA : (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) ≤
        4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
      have hbase := tiny_final (q := q) (P := P) (TIN := TIN) (f1 := f1) (f2 := f2) (f3 := f3)
        (x := x) (X := X) (ε := ε) (D := Dst) (HB := H) (a := α₁) (b := 1 - θ) (e := 1 - θ)
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
      -- the energy of a fixed power at the enlarged ambient point
      have hamb : ∀ (g : ℕ) (hg : 1 ≤ g) (F : ℝ), 2 ≤ F → F ≤ x →
          1 ≤ Real.log (x ^ g) := by
        intro g hg F hF hFx
        rw [Real.log_pow]
        have h1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
        nlinarith
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
        have hm1mem : (1 : ℕ) ∈ Sg := Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩
        have hConeq : Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4 = Cf 1 := by
          dsimp only [Cf]; rw [hCfam 1 (by norm_num)]
        have hDoneq : 2 + 3 * Kfam 1 = Df 1 := by
          dsimp only [Df]
        -- the first factor at power one
        have hEa : energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) ≤
            Cefam 1 * Real.log x ^ Kfam 1 := by
          have hbase := hEn 1 (by norm_num) (truncatedCoeffs a c₁ c₂ M ^ 1).coeff
            (truncated_power_bound (c2 := c₂) ha hc₁.le hM0.le 1) x (M ^ 1) hlx
            (by simpa using hM) (by simpa using hMx)
          have hmax1 : (1 : ℝ) ≤ max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) := le_max_left _ _
          have hC0 : 0 ≤ Cem 1 (by norm_num) := (hCempos 1 (by norm_num)).le
          have hlogn : 0 ≤ Real.log x ^ Kem 1 (by norm_num) := Real.rpow_nonneg hlx0.le _
          rw [hCefam 1 (by norm_num), hKfam 1 (by norm_num)]
          calc energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1)
              ≤ Cem 1 (by norm_num) * Real.log x ^ Kem 1 (by norm_num) := hbase
            _ = Cem 1 (by norm_num) * 1 * Real.log x ^ Kem 1 (by norm_num) := by ring
            _ ≤ Cem 1 (by norm_num) * max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) *
                  Real.log x ^ Kem 1 (by norm_num) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax1 hC0) hlogn
            _ = _ := by ring
        have hEa0 : (0 : ℝ) ≤
            energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1) :=
          Finset.sum_nonneg (fun n hn => by positivity)
        have hcca' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
            X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := by
          have hcarda := hCpm 1 (by norm_num) x M T V1 q Cell a ha hx hM hMx
            hT hTx hq hqx hV1pos hspC htimeC hlow1
          have hcca : (Cell.card : ℝ) ≤
              (Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) *
              Real.log x ^ (2 + 3 * Kfam 1) *
              X ^ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) :=
            cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := M)
              (V := V1) (Q := Q) (m := α₁) (σ := σ1)
              (e1 := α₁ * (2 - 2 * σ1)) (e2 := 1 - θ + α₁ * Thm4.f σ1) (g := 1)
              (C := Cpm 1 (by norm_num)) (Ce := Cefam 1) (K := Kfam 1)
              (E := energy (truncatedCoeffs a c₁ c₂ M ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (M ^ 1))
              hlx hX1 hα₁ rfl hlev1 hQ hM0 hV1pos hV1ge
              (hCpmpos 1 (by norm_num)).le (hCefam0 1 (by norm_num)).le
              (hKfam0 1 (by norm_num)) hEa0
              (by simpa using level_first_term hX0 hα₁ rfl hlev1)
              (by simpa using bracket_one hX0 hX1 hα₁ rfl hlev1 hQ)
              hcarda hEa
          refine card_le_weaken (C := Cpm 1 (by norm_num) *
              (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) (Cg := Cst)
            (D := 2 + 3 * Kfam 1) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hcca
          · have h1 := (hCpmpos 1 (by norm_num)).le
            have h2 := (hCefam0 1 (by norm_num)).le
            positivity
          · rw [hConeq]; exact hCf_le 1 hm1mem
          · rw [hDoneq]; exact hDf_le 1 hm1mem
        -- the second factor at power one
        have hEb : energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) ≤
            Cefam 1 * Real.log x ^ Kfam 1 := by
          have hbase := hEn 1 (by norm_num) (truncatedCoeffs b c₁ c₂ N ^ 1).coeff
            (truncated_power_bound (c2 := c₂) hb hc₁.le hN0.le 1) x (N ^ 1) hlx
            (by simpa using hN) (by simpa using hNx)
          have hmax1 : (1 : ℝ) ≤ max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) := le_max_left _ _
          have hC0 : 0 ≤ Cem 1 (by norm_num) := (hCempos 1 (by norm_num)).le
          have hlogn : 0 ≤ Real.log x ^ Kem 1 (by norm_num) := Real.rpow_nonneg hlx0.le _
          rw [hCefam 1 (by norm_num), hKfam 1 (by norm_num)]
          calc energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1)
              ≤ Cem 1 (by norm_num) * Real.log x ^ Kem 1 (by norm_num) := hbase
            _ = Cem 1 (by norm_num) * 1 * Real.log x ^ Kem 1 (by norm_num) := by ring
            _ ≤ Cem 1 (by norm_num) * max 1 ((g0 : ℝ) ^ Kem 1 (by norm_num)) *
                  Real.log x ^ Kem 1 (by norm_num) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax1 hC0) hlogn
            _ = _ := by ring
        have hEb0 : (0 : ℝ) ≤
            energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1) :=
          Finset.sum_nonneg (fun n hn => by positivity)
        have hccb' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
            X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) := by
          have hcardb := hCpm 1 (by norm_num) x N T V2 q Cell b hb hx hN hNx
            hT hTx hq hqx hV2pos hspC htimeC hlow2
          have hccb : (Cell.card : ℝ) ≤
              (Cpm 1 (by norm_num) * (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) *
              Real.log x ^ (2 + 3 * Kfam 1) *
              X ^ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
            cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := N)
              (V := V2) (Q := Q) (m := α₂) (σ := σ2)
              (e1 := α₂ * (2 - 2 * σ2)) (e2 := 1 - θ + α₂ * Thm4.f σ2) (g := 1)
              (C := Cpm 1 (by norm_num)) (Ce := Cefam 1) (K := Kfam 1)
              (E := energy (truncatedCoeffs b c₁ c₂ N ^ 1).coeff (c₁ ^ 1) (c₂ ^ 1) (N ^ 1))
              hlx hX1 hα₂ rfl hlev2 hQ hN0 hV2pos hV2ge
              (hCpmpos 1 (by norm_num)).le (hCefam0 1 (by norm_num)).le
              (hKfam0 1 (by norm_num)) hEb0
              (by simpa using level_first_term hX0 hα₂ rfl hlev2)
              (by simpa using bracket_one hX0 hX1 hα₂ rfl hlev2 hQ)
              hcardb hEb
          refine card_le_weaken (C := Cpm 1 (by norm_num) *
              (Cefam 1 + 16 * Cefam 1 ^ 3) * 4) (Cg := Cst)
            (D := 2 + 3 * Kfam 1) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hccb
          · have h1 := (hCpmpos 1 (by norm_num)).le
            have h2 := (hCefam0 1 (by norm_num)).le
            positivity
          · rw [hConeq]; exact hCf_le 1 hm1mem
          · rw [hDoneq]; exact hDf_le 1 hm1mem
        -- the third factor at a general power of at most `g0`
        let fam : ℕ → ℝ := fun g => max ((g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
          (1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3))
        have hfam3 : fam 3 = max (3 * (1 - α₁ - α₂) * (2 - 2 * σ3))
            (1 - θ + 3 * (1 - α₁ - α₂) * (4 - 6 * σ3)) := by
          dsimp only [fam]; norm_num
        have hcce : ∀ g, 1 ≤ g → g ≤ g0 →
            (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ fam g := by
          intro g hg1 hgg0
          have hCgeq : Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4 = Cf g := by
            dsimp only [Cf]; rw [hCfam g hg1]
          have hDgeq : 2 + 3 * Kfam g = Df g := by
            dsimp only [Df]
          have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
          have hgx : (g : ℝ) ≤ (g0 : ℝ) := by exact_mod_cast hgg0
          have hEe : energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g) ≤
              Cefam g * Real.log x ^ Kfam g := by
            have hambg : 1 ≤ Real.log (x ^ g) := by
              rw [Real.log_pow]
              nlinarith
            have hFL : L ^ g ≤ x ^ g := pow_le_pow_left₀ hL0.le hLx g
            have hbase := hEn g hg1 (truncatedCoeffs e c₁ c₂ L ^ g).coeff
              (truncated_power_bound (c2 := c₂) hecoeff hc₁.le hL0.le g) (x ^ g) (L ^ g) hambg
              (by simpa using hL.trans (le_self_pow₀ hL1 (by omega)))
              (by simpa using hFL)
            rw [hCefam g hg1, hKfam g hg1]
            have hrw : Real.log (x ^ g) ^ Kem g hg1 =
                (g : ℝ) ^ Kem g hg1 * Real.log x ^ Kem g hg1 := by
              rw [Real.log_pow, Real.mul_rpow (by linarith) hlx0.le]
            rw [hrw] at hbase
            have h1 : (g : ℝ) ^ Kem g hg1 ≤ max 1 ((g0 : ℝ) ^ Kem g hg1) :=
              (Real.rpow_le_rpow (by linarith) hgx (hKem g hg1)).trans (le_max_right _ _)
            have h3 : 0 ≤ Real.log x ^ Kem g hg1 := Real.rpow_nonneg hlx0.le _
            have h4 : 0 ≤ Cem g hg1 := (hCempos g hg1).le
            calc energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g)
                ≤ Cem g hg1 * ((g : ℝ) ^ Kem g hg1 * Real.log x ^ Kem g hg1) := hbase
              _ ≤ Cem g hg1 * (max 1 ((g0 : ℝ) ^ Kem g hg1) * Real.log x ^ Kem g hg1) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h3) h4
              _ = (Cem g hg1 * max 1 ((g0 : ℝ) ^ Kem g hg1)) * Real.log x ^ Kem g hg1 := by ring
          have hEe0 : (0 : ℝ) ≤
              energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g) :=
            Finset.sum_nonneg (fun n hn => by positivity)
          obtain ⟨hpow1, hpow2, hpow3⟩ := level_pow_terms (X := X) (F := L)
            (V := V3) (l := 1 - α₁ - α₂) (σ := σ3) (g := g) hX0 rfl hlev3
          have hcarde := hCpm g hg1 x L T V3 q Cell e hecoeff hx hL hLx
            hT hTx hq hqx hV3pos hspC htimeC hlow3
          have hccgen : (Cell.card : ℝ) ≤
              (Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4) *
              Real.log x ^ (2 + 3 * Kfam g) *
              X ^ max ((g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
                (1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) :=
            cell_card_of_level (S := Cell) (x := x) (X := X) (θ := θ) (F := L)
              (V := V3) (Q := Q) (m := 1 - α₁ - α₂) (σ := σ3)
              (e1 := (g : ℝ) * (1 - α₁ - α₂) * (2 - 2 * σ3))
              (e2 := 1 - θ + (g : ℝ) * (1 - α₁ - α₂) * (4 - 6 * σ3)) (g := g)
              (C := Cpm g hg1) (Ce := Cefam g) (K := Kfam g)
              (E := energy (truncatedCoeffs e c₁ c₂ L ^ g).coeff (c₁ ^ g) (c₂ ^ g) (L ^ g))
              hlx hX1 hl rfl hlev3 hQ hL0 hV3pos hV3ge
              (hCpmpos g hg1).le (hCefam0 g hg1).le (hKfam0 g hg1) hEe0
              (by simpa using hpow1)
              (by simpa using bracket_gen hX0 hX1 hl hg1 rfl hlev3 hQ)
              hcarde hEe
          refine card_le_weaken (C := Cpm g hg1 * (Cefam g + 16 * Cefam g ^ 3) * 4)
            (Cg := Cst) (D := 2 + 3 * Kfam g) (Dg := Dst) hlx ?_ ?_ ?_ hX1 hccgen
          · have h1 := (hCpmpos g hg1).le
            have h2 := (hCefam0 g hg1).le
            positivity
          · rw [hCgeq]; exact hCf_le g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩)
          · rw [hDgeq]; exact hDf_le g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩)
        let Vals : Finset ℝ := Sg.image fam
        have hValsne : Vals.Nonempty :=
          ⟨fam 1, Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hg01⟩, rfl⟩⟩
        let s3 : ℝ := Vals.min' hValsne
        have hs3le : ∀ g ∈ Sg, s3 ≤ fam g := fun g hg =>
          Finset.min'_le Vals (fam g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
        have hcce' : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst * X ^ s3 := by
          obtain ⟨g1, hg1, hg1eq⟩ := Finset.mem_image.mp (Finset.min'_mem Vals hValsne)
          have h := hcce g1 (Finset.mem_Icc.mp hg1).1 (Finset.mem_Icc.mp hg1).2
          rwa [hg1eq] at h
        have hs1 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
            (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
            ≤ max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1) := min_le_left _ _
        have hs2 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
            (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
            ≤ max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2) :=
          (min_le_right _ _).trans (min_le_left _ _)
        have hs3' : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
            (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) ≤ s3 :=
          (min_le_right _ _).trans (min_le_right _ _)
        have hs3g : ∀ g ∈ Sg, min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
            (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) ≤ fam g :=
          fun g hg => hs3'.trans (hs3le g hg)
        have hcardmin : (Cell.card : ℝ) ≤ Cst * Real.log x ^ Dst *
            X ^ min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
              (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) :=
          card_le_three_min hlx hCst0 hX1 hcca' hccb' hcce'
        have hcnd : α₂ * Thm4.c σ2 < 1 - θ :=
          nondominant_exponent (X := X) (N := N) (Q := Q) (θ := θ) (n := α₂) (σ := σ2)
            (z := f2 p₀) (k := k.2.1) hXlt hα₂ rfl hQ hσ2 hlev2 (hlow2 p₀ hp₀) hNQ
            (hmemP p₀ (hCellP hp₀)).2.1
        have hnn : α₂ * (2 - 2 * σ2) ≤ 1 - θ + α₂ * Thm4.f σ2 := by
          by_contra hcon
          push_neg at hcon
          exact absurd (Thm4.dominance.mp hcon.le) (not_le.mpr hcnd)
        have hNred : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
            (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
            ≤ 1 - θ + α₂ * Thm4.f σ2 := by
          refine hs2.trans ?_
          rw [max_eq_right hnn]
        have hclass : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
            (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3) +
            (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) + (1 - α₁ - α₂) * (σ3 - 1 / 2)) ≤
            1 / 2 - ε / 72 := by
          by_cases hdM : 1 - θ ≤ α₁ * Thm4.c σ1
          · have hdom : 1 - θ + α₁ * Thm4.f σ1 ≤ α₁ * (2 - 2 * σ1) := Thm4.dominance.mpr hdM
            have hMred : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
                ≤ α₁ * (2 - 2 * σ1) := by
              refine hs1.trans ?_
              rw [max_eq_left hdom]
            have hcl := mixed_cell_exponent (m := α₁) (n := α₂) (σ1 := σ1) (σ2 := σ2)
              (σ3 := σ3)
              (s := min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)) (g0 := g0)
              hε hεu hθu hα₂.le hml hab hgam hcut hcnd hMred hNred
              (fun g hg1 hgg0 => hs3g g (Finset.mem_Icc.mpr ⟨hg1, hgg0⟩))
            linarith
          · have hMred2 : min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3)
                ≤ 1 - θ + α₁ * Thm4.f σ1 := by
              refine hs1.trans ?_
              rw [max_eq_right ?_]
              by_contra hcon
              push_neg at hcon
              exact hdM (Thm4.dominance.mp hcon.le)
            have h3 := hs3g 3 (Finset.mem_Icc.mpr ⟨by norm_num, hg0⟩)
            rw [hfam3] at h3
            have hc2 := case2_cell_exponent (m := α₁) (n := α₂) (l := 1 - α₁ - α₂)
              (σ1 := σ1) (σ2 := σ2) (σ3 := σ3)
              (s := min (max (α₁ * (2 - 2 * σ1)) (1 - θ + α₁ * Thm4.f σ1))
                (min (max (α₂ * (2 - 2 * σ2)) (1 - θ + α₂ * Thm4.f σ2)) s3))
              hε hα₁.le hα₂.le hml hmsum (by linarith : 1 - α₁ - α₂ < Thm4.gam θ - ε)
              hMred2 hNred h3
            linarith
        have hlevels : 8 * (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2.1 * (2 : ℝ) ^ k.2.2 =
            8 * X ^ (α₁ * (σ1 - 1 / 2) + α₂ * (σ2 - 1 / 2) + (1 - α₁ - α₂) * (σ3 - 1 / 2)) := by
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
        _ = 8 * Cst * Clev ^ 3 * Real.log x ^ (3 + Dst) * X ^ (1 / 2 - ε / 72) := by rw [← hlog3]
        _ = 8 * Cst * Clev ^ 3 * (X ^ (1 / 2 - ε / 72) * Real.log x ^ (3 + Dst)) := by ring
        _ ≤ 8 * Cst * Clev ^ 3 * (R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hsave2 (by positivity)
        _ = 8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
    rw [← hsplit]
    calc (∑ p ∈ TIN, ‖f1 p * f2 p * f3 p‖) + (∑ p ∈ MAIN, ‖f1 p * f2 p * f3 p‖)
        ≤ 4 * H * R1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
          8 * Cst * Clev ^ 3 * R2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
        add_le_add htinyA hMAINA
      _ = (4 * H * R1 + 8 * Cst * Clev ^ 3 * R2) * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
  exact hgoal

/-- Page 14, exact original mixed-case target from its two written branches.
CONDITIONAL on the large-third-factor leaf and original inputs. -/
theorem first_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
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
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := first_small_third hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := first_large_third hmean hlarge henergy B
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

/-- Page 15, Case 4 follows from the new exact Case 3 supply by symmetry.
CONDITIONAL on the same explicit inputs and the OPEN mixed large-third-factor leaf. -/
theorem second_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
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
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η, hη, hcase⟩ := first_dominant hmean hlarge henergy B
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C, hC⟩ := hcase ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have h := hC θ α₂ α₁ x X T q S b a e hθ hθu
    (by simpa only [abs_sub_comm] using hab) (by convert hgam using 1 <;> ring)
    hx hX hq hqx hT hTx hqT hN hNx hM hMx
    (by convert hL using 1 <;> congr 1 <;> ring)
    (by convert hLx using 1 <;> congr 1 <;> ring)
    hspace htimes hb ha he (by convert hsmall using 1 <;> congr 1 <;> ring)
  convert h using 1
  · rw [casePart_swap]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    congr 1
    · ring
    · congr 2
      ring

end LeanLab.BHP1997.Decomp437h
