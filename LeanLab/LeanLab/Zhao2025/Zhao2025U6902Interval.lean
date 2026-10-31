import Mathlib
import LeanLab.Zhao2025.Zhao2025U6901Grid

/-!
# A checked interval evaluator over `ℚ` for expressions in `e^{-(10/3)t}` and `G` of (3.22)

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6902, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

`Ex` is a small expression language: rational constants, `e^{-(10/3)t}`, `G(z)`, `+`, `-`, `×` of
nonnegative factors, `/` by a positive denominator and `max(·, 0)`.  `Ex.val` is its real value,
`Ex.iv` a rational interval and `Ex.ok` the side conditions, all computable by the kernel.
`Ex.sound`, PROVED: if `ok` holds then `val` lies in `iv`.  This is lab infrastructure for the
R bounds (3.38), (3.42), (3.43) and reusable for any finite expression in these functions.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6841

inductive Ex where
  | c : ℚ → Ex
  | ex : ℚ → Ex
  | g : ℚ → Ex
  | add : Ex → Ex → Ex
  | sub : Ex → Ex → Ex
  | mul : Ex → Ex → Ex
  | dv : Ex → Ex → Ex
  | pos : Ex → Ex

/-- The real value; `ex t = e^{-(10/3)t}`, `g z = G(z)`. -/
noncomputable def Ex.val : Ex → ℝ
  | .c q => q
  | .ex t => Real.exp (-(10 / 3 * (t : ℝ)))
  | .g z => Gz z
  | .add a b => a.val + b.val
  | .sub a b => a.val - b.val
  | .mul a b => a.val * b.val
  | .dv a b => a.val / b.val
  | .pos a => max a.val 0

/-- Rational enclosure of `G(z)`. -/
def Giv (z : ℚ) : ℚ × ℚ :=
  if z = 0 then (8 / 9, 8 / 9)
  else if 0 < z then (G2lo z, 4 * (z + 1) ^ 2 * eupq (2 * z) / z ^ 6 + Rq z)
  else (G1lo z, G1hi z)

/-- Side conditions for `Giv`. -/
def Gok (z : ℚ) : Bool :=
  decide (z = 0) || (decide (0 < z) && decide (2 * z ≤ 8)) ||
    (decide (z < 0) && decide (-2 * z ≤ 8) && decide (0 < eloq (-2 * z)))

def Ex.iv : Ex → ℚ × ℚ
  | .c q => (q, q)
  | .ex t => (eloq (10 / 3 * t), eupq (10 / 3 * t))
  | .g z => Giv z
  | .add a b => (a.iv.1 + b.iv.1, a.iv.2 + b.iv.2)
  | .sub a b => (a.iv.1 - b.iv.2, a.iv.2 - b.iv.1)
  | .mul a b => (a.iv.1 * b.iv.1, a.iv.2 * b.iv.2)
  | .dv a b => (min (a.iv.1 / b.iv.1) (a.iv.1 / b.iv.2), max (a.iv.2 / b.iv.1) (a.iv.2 / b.iv.2))
  | .pos a => (max a.iv.1 0, max a.iv.2 0)

def Ex.ok : Ex → Bool
  | .c _ => true
  | .ex t => decide (0 ≤ t) && decide (10 / 3 * t ≤ 8)
  | .g z => Gok z
  | .add a b => a.ok && b.ok
  | .sub a b => a.ok && b.ok
  | .mul a b => a.ok && b.ok && decide (0 ≤ a.iv.1) && decide (0 ≤ b.iv.1)
  | .dv a b => a.ok && b.ok && decide (0 < b.iv.1)
  | .pos a => a.ok

theorem Gz_zero : Gz 0 = 8 / 9 := by
  have := G_zero; unfold Gz; simpa using this

theorem G2_upper (z : ℚ) (hz : 0 < z) :
    Gz (z : ℝ) ≤ ((4 * (z + 1) ^ 2 * eupq (2 * z) / z ^ 6 + Rq z : ℚ) : ℝ) := by
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  rw [Gz_eq _ hz'.ne']
  push_cast; rw [Rq_cast]
  have he := eupq_ge (2 * z) (by linarith)
  push_cast at he
  have hc : 0 ≤ 4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 := by positivity
  have := mul_le_mul_of_nonneg_left he hc
  have e1 : 4 * ((z : ℝ) + 1) ^ 2 * ((eupq (2 * z) : ℚ) : ℝ) / (z : ℝ) ^ 6 =
      4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * ((eupq (2 * z) : ℚ) : ℝ) := by ring
  have e2 : 4 * ((z : ℝ) + 1) ^ 2 * Real.exp (-(2 * (z : ℝ))) / (z : ℝ) ^ 6 =
      4 * ((z : ℝ) + 1) ^ 2 / (z : ℝ) ^ 6 * Real.exp (-(2 * (z : ℝ))) := by ring
  rw [e1, e2]; linarith

theorem Giv_sound (z : ℚ) (h : Gok z = true) :
    ((Giv z).1 : ℝ) ≤ Gz z ∧ Gz z ≤ ((Giv z).2 : ℝ) := by
  unfold Gok at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Giv
  by_cases h0 : z = 0
  · subst h0; simp [Gz_zero]
  · rw [if_neg h0]
    by_cases hp : 0 < z
    · rw [if_pos hp]
      have h8 : 2 * z ≤ 8 := by
        rcases h with (h | ⟨_, h⟩) | ⟨⟨h, _⟩, _⟩
        · exact absurd h h0
        · exact h
        · exact absurd hp (not_lt.mpr h.le)
      exact ⟨G2lo_le z hp h8, G2_upper z hp⟩
    · rw [if_neg hp]
      have hn : z < 0 := lt_of_le_of_ne (not_lt.mp hp) h0
      obtain ⟨h8, hpos⟩ : -2 * z ≤ 8 ∧ 0 < eloq (-2 * z) := by
        rcases h with (h | ⟨h, _⟩) | ⟨⟨_, h8⟩, hpos⟩
        · exact absurd h h0
        · exact absurd h hp
        · exact ⟨h8, hpos⟩
      exact G1_bounds z hn h8 hpos

theorem div_mem {a b alo ahi blo bhi : ℝ} (ha1 : alo ≤ a) (ha2 : a ≤ ahi) (hb1 : blo ≤ b)
    (hb2 : b ≤ bhi) (hb : 0 < blo) :
    min (alo / blo) (alo / bhi) ≤ a / b ∧ a / b ≤ max (ahi / blo) (ahi / bhi) := by
  have hb0 : 0 < b := lt_of_lt_of_le hb hb1
  have hbh : 0 < bhi := lt_of_lt_of_le hb0 hb2
  constructor
  · have h1 : alo / b ≤ a / b := div_le_div_of_nonneg_right ha1 hb0.le
    rcases le_total 0 alo with h | h
    · exact (min_le_right _ _).trans ((div_le_div_of_nonneg_left h hb0 hb2).trans h1)
    · refine (min_le_left _ _).trans (le_trans ?_ h1)
      rw [div_le_div_iff₀ hb hb0]; nlinarith
  · have h1 : a / b ≤ ahi / b := div_le_div_of_nonneg_right ha2 hb0.le
    rcases le_total 0 ahi with h | h
    · exact h1.trans ((div_le_div_of_nonneg_left h hb hb1).trans (le_max_left _ _))
    · refine h1.trans (le_trans ?_ (le_max_right _ _))
      rw [div_le_div_iff₀ hb0 hbh]; nlinarith

/-- PROVED: a checked expression's value lies in its rational interval. -/
theorem Ex.sound : ∀ e : Ex, e.ok = true → (e.iv.1 : ℝ) ≤ e.val ∧ e.val ≤ (e.iv.2 : ℝ)
  | .c q, _ => by simp [Ex.iv, Ex.val]
  | .ex t, h => by
    simp only [Ex.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Ex.iv, Ex.val]
    constructor
    · have := eloq_le (10 / 3 * t) (by linarith [h.1]) h.2
      push_cast at this; exact this
    · have := eupq_ge (10 / 3 * t) (by linarith [h.1])
      push_cast at this; exact this
  | .g z, h => by simp only [Ex.iv, Ex.val, Ex.ok] at h ⊢; exact Giv_sound z h
  | .add a b, h => by
    simp only [Ex.ok, Bool.and_eq_true] at h
    have ha := Ex.sound a h.1; have hb := Ex.sound b h.2
    simp only [Ex.iv, Ex.val]; push_cast; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  | .sub a b, h => by
    simp only [Ex.ok, Bool.and_eq_true] at h
    have ha := Ex.sound a h.1; have hb := Ex.sound b h.2
    simp only [Ex.iv, Ex.val]; push_cast; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  | .mul a b, h => by
    simp only [Ex.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have ha := Ex.sound a h1; have hb := Ex.sound b h2
    have h3' : (0 : ℝ) ≤ a.iv.1 := by exact_mod_cast h3
    have h4' : (0 : ℝ) ≤ b.iv.1 := by exact_mod_cast h4
    simp only [Ex.iv, Ex.val]; push_cast
    constructor
    · exact mul_le_mul ha.1 hb.1 h4' (h3'.trans ha.1)
    · exact mul_le_mul ha.2 hb.2 (h4'.trans hb.1) ((h3'.trans ha.1).trans ha.2)
  | .dv a b, h => by
    simp only [Ex.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ha := Ex.sound a h1; have hb := Ex.sound b h2
    have h3' : (0 : ℝ) < b.iv.1 := by exact_mod_cast h3
    simp only [Ex.iv, Ex.val]; push_cast
    exact div_mem ha.1 ha.2 hb.1 hb.2 h3'
  | .pos a, h => by
    simp only [Ex.ok] at h
    have ha := Ex.sound a h
    simp only [Ex.iv, Ex.val]; push_cast
    exact ⟨max_le_max ha.1 le_rfl, max_le_max ha.2 le_rfl⟩

end LeanLab.Zhao2025.U6900
