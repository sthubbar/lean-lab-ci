/-
# Pintz and Althöfer 2026, Section 4.3: the linear model `V_X` and `V_X² = Vfun`

Unit U-1200, T2 FRONTIER, idea I-0080, PC run 20261020T0902Z-22676.

Source: arXiv 2610.15559v1, Section 4.3, read on the page this run: with `P = X^{1/3}`,
`𝔐` is the union of the arcs `|α − a/q| ≤ P/(qX)`, `q ≤ P`, `(a, q) = 1`, "disjoint for all
sufficiently large X, since 2P² < X", and `V_X(α) = μ(q)/(φ(q)(X⁻¹ − 2πi(α − a/q)))` on the arc
about `a/q`, `0` off `𝔐`.

What is here, all PROVED unconditional:
* `hLin X δ`, the linear arc profile `1_{|β|≤δ}(X⁻¹ − 2πiβ)⁻¹` on `ℝ/ℤ`; `hLin_sq`, its square
  is `hArc X δ`; `hLin_support`, it vanishes off the arc.
* `arcs_disjoint`: if `2P² < X`, `q, q' ≤ P`, `a < q`, `a' < q'` with `(a,q) = (a',q') = 1`, and
  `z` lies on both the arc about `a/q` and the arc about `a'/q'`, then `q = q'` and `a = a'`.
  This is the paper's disjointness claim, in Lean.
* `Vlin X P Q`, the paper's `V_X`, and `Vlin_sq`: `V_X(z)² = Vfun X P Q z` for every `z` when
  `Q ≤ P` and `2P² < X`. So `Vfun`, whose Fourier coefficients are `v_X(n)`, IS the paper's `V_X²`.
* `Vlin_sq_P3`: the same at `P = Q = ⌊x^{1/3}⌋`, `x ≥ 9`.

KNOWN mathematics, the paper's own construction. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Cube

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Linear

open Finset Real MeasureTheory AddCircle LeanLab.ExceptionalSet.PintzAlthofer2026
open LeanLab.ExceptionalSet.PintzAlthofer2026Model LeanLab.ExceptionalSet.PintzAlthofer2026Cube

attribute [local instance] Classical.propDecidable

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-- `(X⁻¹ − 2πiβ)⁻¹`. -/
def lprof (X β : ℝ) : ℂ := 1 / (((1 / X : ℝ) : ℂ) - ((2 * π * β : ℝ) : ℂ) * Complex.I)

theorem lprof_sq (X β : ℝ) : lprof X β ^ 2 = prof X β := by
  unfold lprof prof; rw [div_pow, one_pow]

def gLin (X δ : ℝ) : ℝ → ℂ := Set.indicator (Set.Ioc (-δ) δ) (lprof X)

/-- The linear arc profile on the circle. -/
def hLin (X δ : ℝ) : 𝕋 → ℂ := AddCircle.liftIoc 1 (-(1 / 2)) (gLin X δ)

theorem hLin_sq (X δ : ℝ) (z : 𝕋) : hLin X δ z ^ 2 = hArc X δ z := by
  unfold hLin hArc AddCircle.liftIoc
  simp only [Function.comp_apply, Set.domRestrict_apply]
  unfold gLin gArc
  set w : ℝ := ((AddCircle.equivIoc 1 (-(1 / 2)) z : Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1)) : ℝ)
  by_cases h : w ∈ Set.Ioc (-δ) δ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, lprof_sq]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring

theorem coe_equivIoc (z : 𝕋) :
    (((AddCircle.equivIoc 1 (-(1 / 2)) z : Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1)) : ℝ) : 𝕋) = z := by
  have h := (AddCircle.equivIoc 1 (-(1 / 2) : ℝ)).symm_apply_apply z
  rw [AddCircle.equivIoc, QuotientAddGroup.equivIocMod_symm_apply] at h
  exact h

/-- `hLin` vanishes off the arc: a nonzero value comes from some `β ∈ (−δ, δ]` with `(β) = z`. -/
theorem hLin_support {X δ : ℝ} {z : 𝕋} (hz : hLin X δ z ≠ 0) :
    ∃ β : ℝ, β ∈ Set.Ioc (-δ) δ ∧ (β : 𝕋) = z := by
  unfold hLin AddCircle.liftIoc at hz
  simp only [Function.comp_apply, Set.domRestrict_apply] at hz
  unfold gLin at hz
  set w : ℝ := ((AddCircle.equivIoc 1 (-(1 / 2)) z : Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1)) : ℝ)
    with hw
  refine ⟨w, ?_, coe_equivIoc z⟩
  by_contra h
  exact hz (Set.indicator_of_notMem h _)

/-! ### The arcs are disjoint -/

/-- **`arcs_disjoint`**, the paper's claim "these arcs are disjoint ... since 2P² < X". -/
theorem arcs_disjoint {X P : ℝ} (hX : 0 < X) (hPX : 2 * P ^ 2 < X)
    {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : (q : ℝ) ≤ P) (hq'P : (q' : ℝ) ≤ P)
    (ha : a < q) (ha' : a' < q') (hc : Nat.Coprime a q) (hc' : Nat.Coprime a' q')
    {z : 𝕋} {β β' : ℝ} (hβ : β ∈ Set.Ioc (-(P / (q * X))) (P / (q * X)))
    (hβ' : β' ∈ Set.Ioc (-(P / (q' * X))) (P / (q' * X)))
    (hz : (β : 𝕋) = z - (((a : ℝ) / q : ℝ) : 𝕋)) (hz' : (β' : 𝕋) = z - (((a' : ℝ) / q' : ℝ) : 𝕋)) :
    q = q' ∧ a = a' := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast (show 0 < q' by omega)
  -- the two representations of `z` differ by an integer
  have heq : (((a : ℝ) / q + β : ℝ) : 𝕋) = (((a' : ℝ) / q' + β' : ℝ) : 𝕋) := by
    rw [AddCircle.coe_add, AddCircle.coe_add, hz, hz']; abel
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at heq
  obtain ⟨k, hk⟩ := heq
  simp only [zsmul_eq_mul, mul_one] at hk
  -- multiply by q q'
  set m : ℤ := (a : ℤ) * q' - (a' : ℤ) * q - k * q * q'
  have hm : (m : ℝ) = (β' - β) * q * q' := by
    simp only [m]; push_cast
    field_simp at hk
    linear_combination -hk
  have hP0 : 0 ≤ P := le_trans hqr.le hqP
  have hb : |β' - β| ≤ P / (q * X) + P / (q' * X) := by
    rw [abs_le]; constructor
    · linarith [hβ.1, hβ.2, hβ'.1, hβ'.2]
    · linarith [hβ.1, hβ.2, hβ'.1, hβ'.2]
  have hmabs : |(m : ℝ)| < 1 := by
    rw [hm, abs_mul, abs_mul, abs_of_pos hqr, abs_of_pos hq'r]
    have h1 : (P / (q * X) + P / (q' * X)) * q * q' = P * (q + q') / X := by
      field_simp; ring
    have h2 : P * (q + q') / X ≤ 2 * P ^ 2 / X := by
      apply div_le_div_of_nonneg_right _ hX.le
      nlinarith
    have h3 : 2 * P ^ 2 / X < 1 := by rw [div_lt_one hX]; exact hPX
    calc |β' - β| * q * q' ≤ (P / (q * X) + P / (q' * X)) * q * q' := by
          apply mul_le_mul_of_nonneg_right _ hq'r.le
          exact mul_le_mul_of_nonneg_right hb hqr.le
      _ = P * (q + q') / X := h1
      _ < 1 := lt_of_le_of_lt h2 h3
  have hm0 : m = 0 := by
    have : |m| < 1 := by exact_mod_cast hmabs
    rw [abs_lt] at this; omega
  -- so a q' − a' q = k q q', and |a q' − a' q| < q q' forces k = 0
  have hk0 : k = 0 := by
    have hA : (a : ℤ) * q' - (a' : ℤ) * q = k * q * q' := by simp only [m] at hm0; linarith
    have hlo : -((q : ℤ) * q') < (a : ℤ) * q' - (a' : ℤ) * q := by
      have : (a' : ℤ) < q' := by exact_mod_cast ha'
      have : (0 : ℤ) ≤ a := by positivity
      nlinarith
    have hhi : (a : ℤ) * q' - (a' : ℤ) * q < (q : ℤ) * q' := by
      have : (a : ℤ) < q := by exact_mod_cast ha
      have : (0 : ℤ) ≤ a' := by positivity
      nlinarith
    rw [hA] at hlo hhi
    have hqq : (0 : ℤ) < (q : ℤ) * q' := by positivity
    by_contra hk
    rcases lt_or_gt_of_ne hk with h | h
    · have : k * (q : ℤ) * q' ≤ -((q : ℤ) * q') := by nlinarith
      linarith
    · have : (q : ℤ) * q' ≤ k * (q : ℤ) * q' := by nlinarith
      linarith
  have hcross : a * q' = a' * q := by
    have : (a : ℤ) * q' = (a' : ℤ) * q := by simp only [m, hk0] at hm0; linarith
    exact_mod_cast this
  have hdq : q ∣ q' := by
    have : q ∣ a * q' := ⟨a', by rw [hcross]; ring⟩
    exact (Nat.Coprime.symm hc).dvd_of_dvd_mul_left this
  have hdq' : q' ∣ q := by
    have : q' ∣ a' * q := ⟨a, by rw [← hcross]; ring⟩
    exact (Nat.Coprime.symm hc').dvd_of_dvd_mul_left this
  have hqq : q = q' := Nat.dvd_antisymm hdq hdq'
  refine ⟨hqq, ?_⟩
  subst hqq
  exact Nat.eq_of_mul_eq_mul_right (by omega) hcross

/-! ### The linear model and `V_X² = Vfun` -/

/-- The index set of the arcs: pairs `⟨q, a⟩`, `1 ≤ q ≤ Q`, `a < q`, `(a, q) = 1`. -/
def arcIdx (Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 Q).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))

/-- One arc of the linear model, `μ(q)/φ(q) · hLin(z − a/q)`. -/
def linTerm (X P : ℝ) (i : Σ _ : ℕ, ℕ) (z : 𝕋) : ℂ :=
  (((ArithmeticFunction.moebius i.1 : ℝ) / (i.1.totient : ℝ) : ℝ) : ℂ) *
    hLin X (P / (i.1 * X)) (z - (((i.2 : ℝ) / i.1 : ℝ) : 𝕋))

/-- **The paper's `V_X`**: `μ(q)/(φ(q)(X⁻¹ − 2πi(α − a/q)))` on the arc about `a/q`. -/
def Vlin (X P : ℝ) (Q : ℕ) (z : 𝕋) : ℂ := ∑ i ∈ arcIdx Q, linTerm X P i z

theorem linTerm_sq (X P : ℝ) (i : Σ _ : ℕ, ℕ) (z : 𝕋) :
    linTerm X P i z ^ 2 =
      (((ArithmeticFunction.moebius i.1 : ℝ) ^ 2 / (i.1.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        hArc X (P / (i.1 * X)) (z - (((i.2 : ℝ) / i.1 : ℝ) : 𝕋)) := by
  unfold linTerm
  rw [mul_pow, hLin_sq]; push_cast; ring

theorem Vfun_eq_sigma (X P : ℝ) (Q : ℕ) (z : 𝕋) :
    Vfun X P Q z = ∑ i ∈ arcIdx Q, linTerm X P i z ^ 2 := by
  unfold Vfun arcIdx
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  rw [linTerm_sq]

/-- Two different arcs never both contribute at `z`. -/
theorem linTerm_mul_eq_zero {X P : ℝ} (hX : 0 < X) (hPX : 2 * P ^ 2 < X) {Q : ℕ}
    (hQP : (Q : ℝ) ≤ P) {i j : Σ _ : ℕ, ℕ} (hi : i ∈ arcIdx Q) (hj : j ∈ arcIdx Q) (hij : i ≠ j)
    (z : 𝕋) : linTerm X P i z * linTerm X P j z = 0 := by
  by_contra hne
  have hi0 : linTerm X P i z ≠ 0 := left_ne_zero_of_mul hne
  have hj0 : linTerm X P j z ≠ 0 := right_ne_zero_of_mul hne
  unfold linTerm at hi0 hj0
  obtain ⟨β, hβ, hβz⟩ := hLin_support (right_ne_zero_of_mul hi0)
  obtain ⟨β', hβ', hβz'⟩ := hLin_support (right_ne_zero_of_mul hj0)
  obtain ⟨q, a⟩ := i
  obtain ⟨q', a'⟩ := j
  simp only [arcIdx, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi hj
  have hqP : (q : ℝ) ≤ P := le_trans (by exact_mod_cast hi.1.2) hQP
  have hq'P : (q' : ℝ) ≤ P := le_trans (by exact_mod_cast hj.1.2) hQP
  obtain ⟨h1, h2⟩ := arcs_disjoint hX hPX hi.1.1 hj.1.1 hqP hq'P hi.2.1 hj.2.1 hi.2.2 hj.2.2
    hβ hβ' hβz hβz'
  subst h1; subst h2
  exact hij rfl

/-- **`Vlin_sq`**: when `Q ≤ P` and `2P² < X`, `V_X(z)² = Vfun X P Q z` for every `z`. -/
theorem Vlin_sq {X P : ℝ} (hX : 0 < X) (hPX : 2 * P ^ 2 < X) {Q : ℕ} (hQP : (Q : ℝ) ≤ P)
    (z : 𝕋) : Vlin X P Q z ^ 2 = Vfun X P Q z := by
  rw [Vfun_eq_sigma, Vlin, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j hj hji
    exact linTerm_mul_eq_zero hX hPX hQP hi hj (Ne.symm hji) z
  · intro h; exact absurd hi h

/-- At the paper's `P = Q = ⌊x^{1/3}⌋`: `V_x² = Vfun x P P`, for `x ≥ 9`. -/
theorem Vlin_sq_P3 (x : ℕ) (hx : 9 ≤ x) (z : 𝕋) :
    Vlin x (P3 x) (P3 x) z ^ 2 = Vfun x (P3 x) (P3 x) z :=
  Vlin_sq (by exact_mod_cast (show 0 < x by omega)) (two_P3_sq_lt x hx) le_rfl z

/-! ### Vacuity -/

/-- `arcIdx 3` has the arcs `0/1, 1/2, 1/3, 2/3`. -/
example : (arcIdx 3).card = 4 := by decide

end

end LeanLab.ExceptionalSet.PintzAlthofer2026Linear
