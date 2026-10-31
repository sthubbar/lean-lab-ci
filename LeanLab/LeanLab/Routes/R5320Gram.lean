/-
R-5320, CLOUD 20261021T0117Z-cloud55, unit U-6789, T3 MOONSHOT.
AI wrote this Lean code. Not progress on binary Goldbach, which is OPEN.

The Gram, or positive semidefinite, route.  With `x` the indicator of the
primes on `0..N`, the Goldbach count is the quadratic form `x^T J x` of the
reflection matrix `J a b = [a + b = N]`.  A positivity certificate of the
simplest semidefinite kind writes `J = K + E` with `K` positive semidefinite and
`E` entrywise nonnegative, so `x^T J x ≥ x^T K x ≥ 0` for `x ≥ 0`.

Plain math twins:

* `qf_two`: the form at `s e_i + t e_j`, `i ≠ j`, is
  `s² K_ii + s t (K_ij + K_ji) + t² K_jj`.
* `psd_diag_zero_row`: a positive semidefinite `K` with `K_ii ≤ 0` has
  `K_ij + K_ji = 0` for every `j`; for symmetric `K` the whole row is zero.
* `psd_minorant_reflection`: if `K` is symmetric positive semidefinite and
  `K ≤ J` entrywise, then `K a b = 0` unless `a = b` and `2 a = N`.  So the
  PSD part of every such certificate sees only the centre, `N = p + p`.
* `psd_minorant_qf`: consequently `x^T K x = K_cc x_c²` when `2 c = N`, and
  `x^T K x = 0` for odd `N`.
* `reflection_not_psd`: vacuity test, `J` itself is not positive
  semidefinite for `N ≥ 1`, the form is `-2` at `e_0 - e_N`.
* `centre_minorant`: non-vacuity, the single centre entry is a PSD minorant
  of `J`, so the hypotheses are satisfiable by a nonzero matrix.
-/
import Mathlib

namespace LeanLab.Routes.R5320

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form `x^T K x`. -/
def qf (K : ι → ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * K i j * x j

/-- Positive semidefinite as a quadratic form. -/
def PSD (K : ι → ι → ℝ) : Prop := ∀ x, 0 ≤ qf K x

/-- The vector `s e_i + t e_j`. -/
def two (i j : ι) (s t : ℝ) : ι → ℝ := fun k => if k = i then s else if k = j then t else 0

lemma sum_two (i j : ι) (hij : i ≠ j) (s t : ℝ) (f : ι → ℝ) :
    ∑ k, two i j s t k * f k = s * f i + t * f j := by
  rw [Fintype.sum_eq_add i j hij]
  · simp [two, Ne.symm hij]
  · intro k ⟨hki, hkj⟩
    simp [two, hki, hkj]

theorem qf_two (K : ι → ι → ℝ) (i j : ι) (hij : i ≠ j) (s t : ℝ) :
    qf K (two i j s t) = s * s * K i i + s * t * (K i j + K j i) + t * t * K j j := by
  unfold qf
  have h : ∀ k, ∑ l, two i j s t k * K k l * two i j s t l
      = two i j s t k * (s * K k i + t * K k j) := by
    intro k
    rw [← sum_two i j hij s t (fun l => K k l)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  simp_rw [h]
  rw [sum_two i j hij s t (fun k => s * K k i + t * K k j)]
  ring

/-- A PSD form with nonpositive diagonal entry at `i` has zero symmetrised row `i`. -/
theorem psd_diag_zero_row (K : ι → ι → ℝ) (hK : PSD K) (i j : ι) (hij : i ≠ j)
    (hii : K i i ≤ 0) : K i j + K j i = 0 := by
  have hii0 : K i i = 0 := by
    have := hK (two i j 1 0)
    rw [qf_two K i j hij] at this
    linarith
  -- 2 t (K_ij + K_ji) + K_jj ≥ 0 for all t forces K_ij + K_ji = 0
  set b := K i j + K j i
  have hq : ∀ t : ℝ, 0 ≤ t * b + K j j := by
    intro t
    have := hK (two i j t 1)
    rw [qf_two K i j hij, hii0] at this
    linarith
  by_contra hb
  have h1 := hq ((-(K j j) - 1) / b)
  rw [div_mul_cancel₀ _ hb] at h1
  linarith

/-- The reflection matrix `J a b = [a + b = N]` on `0..N`. -/
def refl (N : ℕ) (a b : Fin (N + 1)) : ℝ := if (a : ℕ) + b = N then 1 else 0

/-- Every symmetric PSD entrywise minorant of the reflection matrix lives on the centre. -/
theorem psd_minorant_reflection (N : ℕ) (K : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hsym : ∀ a b, K a b = K b a) (hK : PSD K) (hle : ∀ a b, K a b ≤ refl N a b)
    (a b : Fin (N + 1)) (hab : ¬ (a = b ∧ 2 * (a : ℕ) = N)) : K a b = 0 := by
  -- a diagonal entry off the centre is ≤ 0
  have diag : ∀ c : Fin (N + 1), 2 * (c : ℕ) ≠ N → K c c ≤ 0 := by
    intro c hc
    have := hle c c
    unfold refl at this
    rw [if_neg (by omega)] at this
    exact this
  have row : ∀ c d : Fin (N + 1), 2 * (c : ℕ) ≠ N → K c d = 0 := by
    intro c d hc
    by_cases hcd : c = d
    · subst hcd
      have h0 := diag c hc
      -- K c c ≥ 0 from PSD at e_c; need another index
      have : 0 ≤ K c c := by
        have hx := hK (fun k => if k = c then 1 else 0)
        unfold qf at hx
        simpa [ite_mul, mul_ite] using hx
      linarith
    · have := psd_diag_zero_row K hK c d hcd (diag c hc)
      rw [hsym d c] at this
      linarith
  by_cases ha : 2 * (a : ℕ) = N
  · have hne : a ≠ b := fun h => hab ⟨h, ha⟩
    have hb : 2 * (b : ℕ) ≠ N := by
      intro hb; apply hne; ext; omega
    rw [hsym]; exact row b a hb
  · exact row a b ha

/-- The form of such a minorant is `K_cc x_c²`, the `p + p` term only. -/
theorem psd_minorant_qf (N : ℕ) (K : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hsym : ∀ a b, K a b = K b a) (hK : PSD K) (hle : ∀ a b, K a b ≤ refl N a b)
    (x : Fin (N + 1) → ℝ) :
    qf K x = ∑ c : Fin (N + 1), if 2 * (c : ℕ) = N then x c * K c c * x c else 0 := by
  unfold qf
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single c]
  · split_ifs with h
    · rfl
    · rw [psd_minorant_reflection N K hsym hK hle c c (by tauto)]; ring
  · intro d _ hdc
    rw [psd_minorant_reflection N K hsym hK hle c d (by tauto)]; ring
  · simp

/-- For odd `N` every PSD minorant certificate is identically zero. -/
theorem psd_minorant_odd (N : ℕ) (hN : N % 2 = 1) (K : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hsym : ∀ a b, K a b = K b a) (hK : PSD K) (hle : ∀ a b, K a b ≤ refl N a b)
    (x : Fin (N + 1) → ℝ) : qf K x = 0 := by
  rw [psd_minorant_qf N K hsym hK hle x]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [if_neg (by omega)]

/-- Vacuity test: the reflection matrix itself is not PSD once `N ≥ 1`. -/
theorem reflection_not_psd (N : ℕ) (hN : 1 ≤ N) : ¬ PSD (refl N) := by
  intro h
  have h0N : (0 : Fin (N + 1)) ≠ Fin.last N := by
    intro e; have := congrArg Fin.val e; simp at this; omega
  have := h (two 0 (Fin.last N) 1 (-1))
  rw [qf_two _ _ _ h0N] at this
  have r00 : refl N 0 0 = 0 := by
    unfold refl; rw [if_neg]; simp only [Fin.val_zero]; omega
  have r0L : refl N 0 (Fin.last N) = 1 := by
    unfold refl; rw [if_pos]; simp only [Fin.val_zero, Fin.val_last]; omega
  have rL0 : refl N (Fin.last N) 0 = 1 := by
    unfold refl; rw [if_pos]; simp only [Fin.val_zero, Fin.val_last]; omega
  have rLL : refl N (Fin.last N) (Fin.last N) = 0 := by
    unfold refl; rw [if_neg]; simp only [Fin.val_last]; omega
  rw [r00, r0L, rL0, rLL] at this
  linarith

/-- The centre matrix: one entry `1` at `(m, m)` on `0..2m`. -/
def centreK (m : ℕ) (a b : Fin (2 * m + 1)) : ℝ :=
  if (a : ℕ) = m ∧ (b : ℕ) = m then 1 else 0

/-- Non-vacuity: the centre entry alone is a symmetric PSD minorant of `J`. -/
theorem centre_minorant (m : ℕ) :
    (∀ a b, centreK m a b = centreK m b a) ∧ PSD (centreK m) ∧
      (∀ a b, centreK m a b ≤ refl (2 * m) a b) ∧
      centreK m ⟨m, by omega⟩ ⟨m, by omega⟩ = 1 := by
  set c : Fin (2 * m + 1) := ⟨m, by omega⟩ with hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b; simp only [centreK]; split_ifs <;> tauto
  · intro x
    unfold qf
    have h : ∀ i, ∑ j, x i * centreK m i j * x j = if i = c then x c * x c else 0 := by
      intro i
      by_cases hi : i = c
      · rw [if_pos hi, Finset.sum_eq_single c]
        · simp [centreK, hi, hc]
        · intro b _ hb
          have : (b : ℕ) ≠ m := fun e => hb (Fin.ext (by simp [hc, e]))
          simp [centreK, this]
        · simp
      · have : (i : ℕ) ≠ m := fun e => hi (Fin.ext (by simp [hc, e]))
        rw [if_neg hi]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [centreK, this]
    simp_rw [h]
    simp [mul_self_nonneg]
  · intro a b
    simp only [centreK, refl]
    split_ifs with h1 h2 <;> try norm_num
    exfalso; apply h2; omega
  · simp [centreK, hc]

end LeanLab.Routes.R5320

#print axioms LeanLab.Routes.R5320.qf_two
#print axioms LeanLab.Routes.R5320.psd_diag_zero_row
#print axioms LeanLab.Routes.R5320.psd_minorant_reflection
#print axioms LeanLab.Routes.R5320.psd_minorant_qf
#print axioms LeanLab.Routes.R5320.psd_minorant_odd
#print axioms LeanLab.Routes.R5320.reflection_not_psd
#print axioms LeanLab.Routes.R5320.centre_minorant
