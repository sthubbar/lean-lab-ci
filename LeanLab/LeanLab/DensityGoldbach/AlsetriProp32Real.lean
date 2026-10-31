/-
P0085 Alsetri 2025, arXiv 2505.09648, Proposition 3.2, the real-number core: three
non-increasing sequences a, b, c of length 4 in [0, 1] (the sorted values of f₁, f₂, f₃ on the
four units ≡ 1 mod 3 of Z_15). If aᵢ + bⱼ + cₖ ≤ 3/2 whenever i + j + k ≥ 4 and aᵢ, bⱼ, cₖ > 0,
then F₁F₂ + F₂F₃ + F₃F₁ ≤ 2(F₁ + F₂ + F₃) with Fᵢ the sums. Split by the support sizes
(5³ cases): one support empty, then the two others sum to at most 4 each; supports {1,4,4},
{2,4,4} up to order, a further split and a product certificate found by linear programming;
otherwise linarith finds F₁ + F₂ + F₃ ≤ 6.
Note: the paper's claim that F₁ + F₂ + F₃ ≤ 6 in all other cases is false for supports
(0, 4, 4) (bound 8) and (0, 3, 4) (bound 7); those cases are harmless, handled by `tzero`.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.DensityGoldbach

lemma tS6 (F1 F2 F3 : ℝ) (h1 : 0 ≤ F1) (h2 : 0 ≤ F2) (h3 : 0 ≤ F3) (hS : F1 + F2 + F3 ≤ 6) :
    F1 * F2 + F2 * F3 + F3 * F1 ≤ 2 * (F1 + F2 + F3) := by
  have hq : F1 * F2 + F2 * F3 + F3 * F1 ≤ (F1 + F2 + F3) ^ 2 / 3 := by
    nlinarith [sq_nonneg (F1 - F2), sq_nonneg (F2 - F3), sq_nonneg (F3 - F1)]
  have : (F1 + F2 + F3) ^ 2 ≤ 6 * (F1 + F2 + F3) := by nlinarith
  linarith

lemma tzero_aux (F2 F3 : ℝ) (h2 : 0 ≤ F2) (h2' : F2 ≤ 4) (h3 : 0 ≤ F3) (h3' : F3 ≤ 4) :
    F2 * F3 ≤ 2 * (F2 + F3) := by
  rcases le_total F2 2 with a | a <;> rcases le_total F3 2 with b | b <;> nlinarith

lemma tzero1 (F1 F2 F3 : ℝ) (h1 : F1 = 0) (h2 : 0 ≤ F2) (h2' : F2 ≤ 4) (h3 : 0 ≤ F3)
    (h3' : F3 ≤ 4) : F1 * F2 + F2 * F3 + F3 * F1 ≤ 2 * (F1 + F2 + F3) := by
  subst h1; have := tzero_aux F2 F3 h2 h2' h3 h3'; linarith

lemma tzero2 (F1 F2 F3 : ℝ) (h1 : F2 = 0) (h2 : 0 ≤ F1) (h2' : F1 ≤ 4) (h3 : 0 ≤ F3)
    (h3' : F3 ≤ 4) : F1 * F2 + F2 * F3 + F3 * F1 ≤ 2 * (F1 + F2 + F3) := by
  subst h1; have := tzero_aux F3 F1 h3 h3' h2 h2'; linarith

lemma tzero3 (F1 F2 F3 : ℝ) (h1 : F3 = 0) (h2 : 0 ≤ F1) (h2' : F1 ≤ 4) (h3 : 0 ≤ F2)
    (h3' : F2 ≤ 4) : F1 * F2 + F2 * F3 + F3 * F1 ≤ 2 * (F1 + F2 + F3) := by
  subst h1; have := tzero_aux F1 F2 h2 h2' h3 h3'; linarith

/-- The support pattern of a non-increasing non-negative 4-tuple. -/
lemma pat4 (y0 y1 y2 y3 : ℝ) (p : 0 ≤ y3) (m1 : y1 ≤ y0) (m2 : y2 ≤ y1) (m3 : y3 ≤ y2) :
    (y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0) ∨ (0 < y0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0) ∨
      (0 < y0 ∧ 0 < y1 ∧ y2 = 0 ∧ y3 = 0) ∨ (0 < y0 ∧ 0 < y1 ∧ 0 < y2 ∧ y3 = 0) ∨
      (0 < y0 ∧ 0 < y1 ∧ 0 < y2 ∧ 0 < y3) := by
  by_cases h3 : 0 < y3
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith, h3⟩)))
  have e3 : y3 = 0 := le_antisymm (not_lt.1 h3) p
  by_cases h2 : 0 < y2
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, h2, e3⟩)))
  have e2 : y2 = 0 := le_antisymm (not_lt.1 h2) (by linarith)
  by_cases h1 : 0 < y1
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h1, e2, e3⟩))
  have e1 : y1 = 0 := le_antisymm (not_lt.1 h1) (by linarith)
  by_cases h0 : 0 < y0
  · exact Or.inr (Or.inl ⟨h0, e1, e2, e3⟩)
  exact Or.inl ⟨le_antisymm (not_lt.1 h0) (by linarith), e1, e2, e3⟩

lemma spec144 (x0 y0 y1 y2 y3 z0 z1 z2 z3 : ℝ)
    (px0 : 0 ≤ x0)
    (ux0 : x0 ≤ 1)
    (my1 : y1 ≤ y0)
    (my2 : y2 ≤ y1)
    (my3 : y3 ≤ y2)
    (py3 : 0 ≤ y3)
    (uy0 : y0 ≤ 1)
    (mz1 : z1 ≤ z0)
    (mz2 : z2 ≤ z1)
    (mz3 : z3 ≤ z2)
    (pz3 : 0 ≤ z3)
    (uz0 : z0 ≤ 1)
    (t013 : x0 + y1 + z3 ≤ 3 / 2)
    (t022 : x0 + y2 + z2 ≤ 3 / 2)
    (t023 : x0 + y2 + z3 ≤ 3 / 2)
    (t031 : x0 + y3 + z1 ≤ 3 / 2)
    (t032 : x0 + y3 + z2 ≤ 3 / 2)
    (t033 : x0 + y3 + z3 ≤ 3 / 2) :
    x0 * (y0 + y1 + y2 + y3) + (y0 + y1 + y2 + y3) * (z0 + z1 + z2 + z3) + (z0 + z1 + z2 + z3) * x0 ≤ 2 * (x0 + (y0 + y1 + y2 + y3) + (z0 + z1 + z2 + z3)) := by
  rcases le_total (x0) (1 / 2) with hs | hs
  · linarith [mul_nonneg px0 (sub_nonneg.2 t033),
      mul_nonneg (sub_nonneg.2 ux0) (sub_nonneg.2 my1),
      mul_nonneg (sub_nonneg.2 ux0) (sub_nonneg.2 mz1),
      mul_nonneg (sub_nonneg.2 ux0) pz3,
      mul_nonneg (sub_nonneg.2 my1) (sub_nonneg.2 uy0),
      mul_nonneg (sub_nonneg.2 my1) (sub_nonneg.2 t022),
      mul_nonneg (sub_nonneg.2 my1) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 uy0),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 uz0),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t032),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t033),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 uy0),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 uz0),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t022),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t023),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t033),
      mul_nonneg py3 (sub_nonneg.2 uz0),
      mul_nonneg py3 (sub_nonneg.2 t013),
      mul_nonneg py3 (sub_nonneg.2 t031),
      mul_nonneg py3 (sub_nonneg.2 t033),
      mul_nonneg (sub_nonneg.2 uy0) (sub_nonneg.2 mz2),
      mul_nonneg (sub_nonneg.2 uy0) (sub_nonneg.2 mz3),
      mul_nonneg (sub_nonneg.2 uy0) pz3,
      mul_nonneg (sub_nonneg.2 mz1) (sub_nonneg.2 uz0),
      mul_nonneg (sub_nonneg.2 mz1) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 mz1) (sub_nonneg.2 t032),
      mul_nonneg (sub_nonneg.2 mz2) (sub_nonneg.2 uz0),
      mul_nonneg (sub_nonneg.2 mz2) (sub_nonneg.2 t022),
      mul_nonneg (sub_nonneg.2 mz2) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 uz0),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t022),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t031),
      mul_nonneg pz3 (sub_nonneg.2 t013),
      mul_nonneg pz3 (sub_nonneg.2 t022),
      mul_nonneg pz3 (sub_nonneg.2 t031),
      mul_nonneg pz3 (sub_nonneg.2 t032),
      sq_nonneg (x0 - y3),
      sq_nonneg (y0 - z0),
      sq_nonneg (y0 - z1),
      sq_nonneg (y1 - z0),
      sq_nonneg (y1 - z1),
      sq_nonneg (y2 - z1),
      sq_nonneg (y2 - z2),
      sq_nonneg (y3 - z2)]
  · exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

lemma spec244 (x0 x1 y0 y1 y2 y3 z0 z1 z2 z3 : ℝ)
    (mx1 : x1 ≤ x0)
    (px1 : 0 ≤ x1)
    (ux0 : x0 ≤ 1)
    (my1 : y1 ≤ y0)
    (my2 : y2 ≤ y1)
    (my3 : y3 ≤ y2)
    (py3 : 0 ≤ y3)
    (uy0 : y0 ≤ 1)
    (mz1 : z1 ≤ z0)
    (mz2 : z2 ≤ z1)
    (mz3 : z3 ≤ z2)
    (pz3 : 0 ≤ z3)
    (uz0 : z0 ≤ 1)
    (t013 : x0 + y1 + z3 ≤ 3 / 2)
    (t022 : x0 + y2 + z2 ≤ 3 / 2)
    (t023 : x0 + y2 + z3 ≤ 3 / 2)
    (t031 : x0 + y3 + z1 ≤ 3 / 2)
    (t032 : x0 + y3 + z2 ≤ 3 / 2)
    (t033 : x0 + y3 + z3 ≤ 3 / 2)
    (t103 : x1 + y0 + z3 ≤ 3 / 2)
    (t112 : x1 + y1 + z2 ≤ 3 / 2)
    (t113 : x1 + y1 + z3 ≤ 3 / 2)
    (t121 : x1 + y2 + z1 ≤ 3 / 2)
    (t122 : x1 + y2 + z2 ≤ 3 / 2)
    (t123 : x1 + y2 + z3 ≤ 3 / 2)
    (t130 : x1 + y3 + z0 ≤ 3 / 2)
    (t131 : x1 + y3 + z1 ≤ 3 / 2)
    (t132 : x1 + y3 + z2 ≤ 3 / 2)
    (t133 : x1 + y3 + z3 ≤ 3 / 2) :
    (x0 + x1) * (y0 + y1 + y2 + y3) + (y0 + y1 + y2 + y3) * (z0 + z1 + z2 + z3) + (z0 + z1 + z2 + z3) * (x0 + x1) ≤ 2 * ((x0 + x1) + (y0 + y1 + y2 + y3) + (z0 + z1 + z2 + z3)) := by
  rcases le_total (x0 + x1) 1 with hs | hs
  · linarith [mul_nonneg (sub_nonneg.2 mx1) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 mx1) (sub_nonneg.2 t103),
      mul_nonneg (sub_nonneg.2 mx1) (sub_nonneg.2 t130),
      mul_nonneg px1 (sub_nonneg.2 uy0),
      mul_nonneg px1 (sub_nonneg.2 t121),
      mul_nonneg px1 (sub_nonneg.2 t130),
      mul_nonneg px1 (sub_nonneg.2 t133),
      mul_nonneg (sub_nonneg.2 ux0) py3,
      mul_nonneg (sub_nonneg.2 my1) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 my1) (sub_nonneg.2 t103),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t103),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t112),
      mul_nonneg (sub_nonneg.2 my2) (sub_nonneg.2 t123),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t022),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t103),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t121),
      mul_nonneg (sub_nonneg.2 my3) (sub_nonneg.2 t130),
      mul_nonneg py3 (sub_nonneg.2 uz0),
      mul_nonneg py3 (sub_nonneg.2 t013),
      mul_nonneg py3 (sub_nonneg.2 t031),
      mul_nonneg py3 (sub_nonneg.2 t113),
      mul_nonneg py3 (sub_nonneg.2 t132),
      mul_nonneg (sub_nonneg.2 mz1) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 mz1) (sub_nonneg.2 t130),
      mul_nonneg (sub_nonneg.2 mz2) (sub_nonneg.2 t013),
      mul_nonneg (sub_nonneg.2 mz2) (sub_nonneg.2 t130),
      mul_nonneg (sub_nonneg.2 mz2) (sub_nonneg.2 t131),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t022),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t023),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t031),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t032),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t103),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t121),
      mul_nonneg (sub_nonneg.2 mz3) (sub_nonneg.2 t130),
      mul_nonneg pz3 (sub_nonneg.2 t022),
      mul_nonneg pz3 (sub_nonneg.2 t023),
      mul_nonneg pz3 (sub_nonneg.2 t031),
      mul_nonneg pz3 (sub_nonneg.2 t103),
      mul_nonneg pz3 (sub_nonneg.2 t131),
      sq_nonneg (x0 - y1),
      sq_nonneg (x0 - y2),
      sq_nonneg (x0 - z1),
      sq_nonneg (x1 - z2),
      sq_nonneg (x1 - z3),
      sq_nonneg (y0 - z0),
      sq_nonneg (y0 - z1),
      sq_nonneg (y1 - z0),
      sq_nonneg (y1 - z1),
      sq_nonneg (y1 - z2),
      sq_nonneg (y2 - z1),
      sq_nonneg (y2 - z2),
      sq_nonneg (y2 - z3),
      sq_nonneg (y3 - z3)]
  · exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

set_option maxHeartbeats 4000000 in
/-- **The real core of Alsetri Proposition 3.2.** -/
lemma p32_core (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : ℝ)
    (pa3 : 0 ≤ a3) (ua0 : a0 ≤ 1) (ma1 : a1 ≤ a0) (ma2 : a2 ≤ a1) (ma3 : a3 ≤ a2)
    (pb3 : 0 ≤ b3) (ub0 : b0 ≤ 1) (mb1 : b1 ≤ b0) (mb2 : b2 ≤ b1) (mb3 : b3 ≤ b2)
    (pc3 : 0 ≤ c3) (uc0 : c0 ≤ 1) (mc1 : c1 ≤ c0) (mc2 : c2 ≤ c1) (mc3 : c3 ≤ c2)
    (h013 : 0 < a0 → 0 < b1 → 0 < c3 → a0 + b1 + c3 ≤ 3 / 2)
    (h022 : 0 < a0 → 0 < b2 → 0 < c2 → a0 + b2 + c2 ≤ 3 / 2)
    (h023 : 0 < a0 → 0 < b2 → 0 < c3 → a0 + b2 + c3 ≤ 3 / 2)
    (h031 : 0 < a0 → 0 < b3 → 0 < c1 → a0 + b3 + c1 ≤ 3 / 2)
    (h032 : 0 < a0 → 0 < b3 → 0 < c2 → a0 + b3 + c2 ≤ 3 / 2)
    (h033 : 0 < a0 → 0 < b3 → 0 < c3 → a0 + b3 + c3 ≤ 3 / 2)
    (h103 : 0 < a1 → 0 < b0 → 0 < c3 → a1 + b0 + c3 ≤ 3 / 2)
    (h112 : 0 < a1 → 0 < b1 → 0 < c2 → a1 + b1 + c2 ≤ 3 / 2)
    (h113 : 0 < a1 → 0 < b1 → 0 < c3 → a1 + b1 + c3 ≤ 3 / 2)
    (h121 : 0 < a1 → 0 < b2 → 0 < c1 → a1 + b2 + c1 ≤ 3 / 2)
    (h122 : 0 < a1 → 0 < b2 → 0 < c2 → a1 + b2 + c2 ≤ 3 / 2)
    (h123 : 0 < a1 → 0 < b2 → 0 < c3 → a1 + b2 + c3 ≤ 3 / 2)
    (h130 : 0 < a1 → 0 < b3 → 0 < c0 → a1 + b3 + c0 ≤ 3 / 2)
    (h131 : 0 < a1 → 0 < b3 → 0 < c1 → a1 + b3 + c1 ≤ 3 / 2)
    (h132 : 0 < a1 → 0 < b3 → 0 < c2 → a1 + b3 + c2 ≤ 3 / 2)
    (h133 : 0 < a1 → 0 < b3 → 0 < c3 → a1 + b3 + c3 ≤ 3 / 2)
    (h202 : 0 < a2 → 0 < b0 → 0 < c2 → a2 + b0 + c2 ≤ 3 / 2)
    (h203 : 0 < a2 → 0 < b0 → 0 < c3 → a2 + b0 + c3 ≤ 3 / 2)
    (h211 : 0 < a2 → 0 < b1 → 0 < c1 → a2 + b1 + c1 ≤ 3 / 2)
    (h212 : 0 < a2 → 0 < b1 → 0 < c2 → a2 + b1 + c2 ≤ 3 / 2)
    (h213 : 0 < a2 → 0 < b1 → 0 < c3 → a2 + b1 + c3 ≤ 3 / 2)
    (h220 : 0 < a2 → 0 < b2 → 0 < c0 → a2 + b2 + c0 ≤ 3 / 2)
    (h221 : 0 < a2 → 0 < b2 → 0 < c1 → a2 + b2 + c1 ≤ 3 / 2)
    (h222 : 0 < a2 → 0 < b2 → 0 < c2 → a2 + b2 + c2 ≤ 3 / 2)
    (h223 : 0 < a2 → 0 < b2 → 0 < c3 → a2 + b2 + c3 ≤ 3 / 2)
    (h230 : 0 < a2 → 0 < b3 → 0 < c0 → a2 + b3 + c0 ≤ 3 / 2)
    (h231 : 0 < a2 → 0 < b3 → 0 < c1 → a2 + b3 + c1 ≤ 3 / 2)
    (h232 : 0 < a2 → 0 < b3 → 0 < c2 → a2 + b3 + c2 ≤ 3 / 2)
    (h233 : 0 < a2 → 0 < b3 → 0 < c3 → a2 + b3 + c3 ≤ 3 / 2)
    (h301 : 0 < a3 → 0 < b0 → 0 < c1 → a3 + b0 + c1 ≤ 3 / 2)
    (h302 : 0 < a3 → 0 < b0 → 0 < c2 → a3 + b0 + c2 ≤ 3 / 2)
    (h303 : 0 < a3 → 0 < b0 → 0 < c3 → a3 + b0 + c3 ≤ 3 / 2)
    (h310 : 0 < a3 → 0 < b1 → 0 < c0 → a3 + b1 + c0 ≤ 3 / 2)
    (h311 : 0 < a3 → 0 < b1 → 0 < c1 → a3 + b1 + c1 ≤ 3 / 2)
    (h312 : 0 < a3 → 0 < b1 → 0 < c2 → a3 + b1 + c2 ≤ 3 / 2)
    (h313 : 0 < a3 → 0 < b1 → 0 < c3 → a3 + b1 + c3 ≤ 3 / 2)
    (h320 : 0 < a3 → 0 < b2 → 0 < c0 → a3 + b2 + c0 ≤ 3 / 2)
    (h321 : 0 < a3 → 0 < b2 → 0 < c1 → a3 + b2 + c1 ≤ 3 / 2)
    (h322 : 0 < a3 → 0 < b2 → 0 < c2 → a3 + b2 + c2 ≤ 3 / 2)
    (h323 : 0 < a3 → 0 < b2 → 0 < c3 → a3 + b2 + c3 ≤ 3 / 2)
    (h330 : 0 < a3 → 0 < b3 → 0 < c0 → a3 + b3 + c0 ≤ 3 / 2)
    (h331 : 0 < a3 → 0 < b3 → 0 < c1 → a3 + b3 + c1 ≤ 3 / 2)
    (h332 : 0 < a3 → 0 < b3 → 0 < c2 → a3 + b3 + c2 ≤ 3 / 2)
    (h333 : 0 < a3 → 0 < b3 → 0 < c3 → a3 + b3 + c3 ≤ 3 / 2) :
    (a0 + a1 + a2 + a3) * (b0 + b1 + b2 + b3) + (b0 + b1 + b2 + b3) * (c0 + c1 + c2 + c3) + (c0 + c1 + c2 + c3) * (a0 + a1 + a2 + a3) ≤ 2 * ((a0 + a1 + a2 + a3) + (b0 + b1 + b2 + b3) + (c0 + c1 + c2 + c3)) := by
  rcases pat4 a0 a1 a2 a3 pa3 ma1 ma2 ma3 with ⟨A0, A1, A2, A3⟩ | ⟨A0, A1, A2, A3⟩ | ⟨A0, A1, A2, A3⟩ | ⟨A0, A1, A2, A3⟩ | ⟨A0, A1, A2, A3⟩ <;>
  rcases pat4 b0 b1 b2 b3 pb3 mb1 mb2 mb3 with ⟨B0, B1, B2, B3⟩ | ⟨B0, B1, B2, B3⟩ | ⟨B0, B1, B2, B3⟩ | ⟨B0, B1, B2, B3⟩ | ⟨B0, B1, B2, B3⟩ <;>
  rcases pat4 c0 c1 c2 c3 pc3 mc1 mc2 mc3 with ⟨C0, C1, C2, C3⟩ | ⟨C0, C1, C2, C3⟩ | ⟨C0, C1, C2, C3⟩ | ⟨C0, C1, C2, C3⟩ | ⟨C0, C1, C2, C3⟩
  · subst A0 A1 A2 A3 B0 B1 B2 B3 C0 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B0 B1 B2 B3 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B0 B1 B2 B3 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B0 B1 B2 B3 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B0 B1 B2 B3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B1 B2 B3 C0 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B1 B2 B3 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B1 B2 B3 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B1 B2 B3 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B1 B2 B3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B2 B3 C0 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B2 B3 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B2 B3 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B2 B3 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B2 B3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B3 C0 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B3 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B3 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B3 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 B3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 C0 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 C1 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 C2 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3 C3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A0 A1 A2 A3
    exact tzero1 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B0 B1 B2 B3 C0 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B0 B1 B2 B3 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B0 B1 B2 B3 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B0 B1 B2 B3 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B0 B1 B2 B3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B1 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B1 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B1 B2 B3 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B1 B2 B3 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B1 B2 B3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B2 B3 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B2 B3 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B2 B3
    have := h013 A0 B1 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B3 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B3 C3
    have := h022 A0 B2 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 B3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 C2 C3
    have := h031 A0 B3 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3 C3
    have := h022 A0 B2 C2
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A1 A2 A3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h033 A0 B3 C3
    linarith [spec144 a0 b0 b1 b2 b3 c0 c1 c2 c3 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · subst A2 A3 B0 B1 B2 B3 C0 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B0 B1 B2 B3 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B0 B1 B2 B3 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B0 B1 B2 B3 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B0 B1 B2 B3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B1 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B1 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B1 B2 B3 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B1 B2 B3 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B1 B2 B3
    have := h103 A1 B0 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B2 B3 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B2 B3 C3
    have := h112 A1 B1 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B2 B3
    have := h013 A0 B1 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B3 C2 C3
    have := h121 A1 B2 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B3 C3
    have := h022 A0 B2 C2
    have := h112 A1 B1 C2
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 B3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h123 A1 B2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 C1 C2 C3
    have := h130 A1 B3 C0
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 C2 C3
    have := h031 A0 B3 C1
    have := h121 A1 B2 C1
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3 C3
    have := h022 A0 B2 C2
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h112 A1 B1 C2
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h132 A1 B3 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A2 A3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h033 A0 B3 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h123 A1 B2 C3
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h132 A1 B3 C2
    have := h133 A1 B3 C3
    linarith [spec244 a0 a1 b0 b1 b2 b3 c0 c1 c2 c3 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · subst A3 B0 B1 B2 B3 C0 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B0 B1 B2 B3 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B0 B1 B2 B3 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B0 B1 B2 B3 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B0 B1 B2 B3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B1 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B1 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B1 B2 B3 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B1 B2 B3 C3
    have := h202 A2 B0 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B1 B2 B3
    have := h103 A1 B0 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B2 B3 C2 C3
    have := h211 A2 B1 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B2 B3 C3
    have := h112 A1 B1 C2
    have := h202 A2 B0 C2
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B2 B3
    have := h013 A0 B1 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h213 A2 B1 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B3 C1 C2 C3
    have := h220 A2 B2 C0
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B3 C2 C3
    have := h121 A1 B2 C1
    have := h211 A2 B1 C1
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B3 C3
    have := h022 A0 B2 C2
    have := h112 A1 B1 C2
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h202 A2 B0 C2
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 B3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h123 A1 B2 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h213 A2 B1 C3
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h223 A2 B2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 C1 C2 C3
    have := h130 A1 B3 C0
    have := h220 A2 B2 C0
    have := h230 A2 B3 C0
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 C2 C3
    have := h031 A0 B3 C1
    have := h121 A1 B2 C1
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h211 A2 B1 C1
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h230 A2 B3 C0
    have := h231 A2 B3 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3 C3
    have := h022 A0 B2 C2
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h112 A1 B1 C2
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h132 A1 B3 C2
    have := h202 A2 B0 C2
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h230 A2 B3 C0
    have := h231 A2 B3 C1
    have := h232 A2 B3 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst A3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h033 A0 B3 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h123 A1 B2 C3
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h132 A1 B3 C2
    have := h133 A1 B3 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h213 A2 B1 C3
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h223 A2 B2 C3
    have := h230 A2 B3 C0
    have := h231 A2 B3 C1
    have := h232 A2 B3 C2
    have := h233 A2 B3 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B0 B1 B2 B3 C0 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B0 B1 B2 B3 C1 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B0 B1 B2 B3 C2 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B0 B1 B2 B3 C3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B0 B1 B2 B3
    exact tzero2 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B1 B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B1 B2 B3 C1 C2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B1 B2 B3 C2 C3
    have := h301 A3 B0 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B1 B2 B3 C3
    have := h202 A2 B0 C2
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B1 B2 B3
    have := h103 A1 B0 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h303 A3 B0 C3
    linarith [spec144 b0 a0 a1 a2 a3 c0 c1 c2 c3 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · subst B2 B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B2 B3 C1 C2 C3
    have := h310 A3 B1 C0
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B2 B3 C2 C3
    have := h211 A2 B1 C1
    have := h301 A3 B0 C1
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B2 B3 C3
    have := h112 A1 B1 C2
    have := h202 A2 B0 C2
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h312 A3 B1 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B2 B3
    have := h013 A0 B1 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h213 A2 B1 C3
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h303 A3 B0 C3
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h312 A3 B1 C2
    have := h313 A3 B1 C3
    linarith [spec244 b0 b1 a0 a1 a2 a3 c0 c1 c2 c3 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · subst B3 C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B3 C1 C2 C3
    have := h220 A2 B2 C0
    have := h310 A3 B1 C0
    have := h320 A3 B2 C0
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B3 C2 C3
    have := h121 A1 B2 C1
    have := h211 A2 B1 C1
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h301 A3 B0 C1
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h320 A3 B2 C0
    have := h321 A3 B2 C1
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B3 C3
    have := h022 A0 B2 C2
    have := h112 A1 B1 C2
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h202 A2 B0 C2
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h312 A3 B1 C2
    have := h320 A3 B2 C0
    have := h321 A3 B2 C1
    have := h322 A3 B2 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst B3
    have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h123 A1 B2 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h213 A2 B1 C3
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h223 A2 B2 C3
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h303 A3 B0 C3
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h312 A3 B1 C2
    have := h313 A3 B1 C3
    have := h320 A3 B2 C0
    have := h321 A3 B2 C1
    have := h322 A3 B2 C2
    have := h323 A3 B2 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · subst C0 C1 C2 C3
    exact tzero3 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  · subst C1 C2 C3
    have := h130 A1 B3 C0
    have := h220 A2 B2 C0
    have := h230 A2 B3 C0
    have := h310 A3 B1 C0
    have := h320 A3 B2 C0
    have := h330 A3 B3 C0
    linarith [spec144 c0 a0 a1 a2 a3 b0 b1 b2 b3 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · subst C2 C3
    have := h031 A0 B3 C1
    have := h121 A1 B2 C1
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h211 A2 B1 C1
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h230 A2 B3 C0
    have := h231 A2 B3 C1
    have := h301 A3 B0 C1
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h320 A3 B2 C0
    have := h321 A3 B2 C1
    have := h330 A3 B3 C0
    have := h331 A3 B3 C1
    linarith [spec244 c0 c1 a0 a1 a2 a3 b0 b1 b2 b3 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
  · subst C3
    have := h022 A0 B2 C2
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h112 A1 B1 C2
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h132 A1 B3 C2
    have := h202 A2 B0 C2
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h230 A2 B3 C0
    have := h231 A2 B3 C1
    have := h232 A2 B3 C2
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h312 A3 B1 C2
    have := h320 A3 B2 C0
    have := h321 A3 B2 C1
    have := h322 A3 B2 C2
    have := h330 A3 B3 C0
    have := h331 A3 B3 C1
    have := h332 A3 B3 C2
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)
  · have := h013 A0 B1 C3
    have := h022 A0 B2 C2
    have := h023 A0 B2 C3
    have := h031 A0 B3 C1
    have := h032 A0 B3 C2
    have := h033 A0 B3 C3
    have := h103 A1 B0 C3
    have := h112 A1 B1 C2
    have := h113 A1 B1 C3
    have := h121 A1 B2 C1
    have := h122 A1 B2 C2
    have := h123 A1 B2 C3
    have := h130 A1 B3 C0
    have := h131 A1 B3 C1
    have := h132 A1 B3 C2
    have := h133 A1 B3 C3
    have := h202 A2 B0 C2
    have := h203 A2 B0 C3
    have := h211 A2 B1 C1
    have := h212 A2 B1 C2
    have := h213 A2 B1 C3
    have := h220 A2 B2 C0
    have := h221 A2 B2 C1
    have := h222 A2 B2 C2
    have := h223 A2 B2 C3
    have := h230 A2 B3 C0
    have := h231 A2 B3 C1
    have := h232 A2 B3 C2
    have := h233 A2 B3 C3
    have := h301 A3 B0 C1
    have := h302 A3 B0 C2
    have := h303 A3 B0 C3
    have := h310 A3 B1 C0
    have := h311 A3 B1 C1
    have := h312 A3 B1 C2
    have := h313 A3 B1 C3
    have := h320 A3 B2 C0
    have := h321 A3 B2 C1
    have := h322 A3 B2 C2
    have := h323 A3 B2 C3
    have := h330 A3 B3 C0
    have := h331 A3 B3 C1
    have := h332 A3 B3 C2
    have := h333 A3 B3 C3
    exact tS6 _ _ _ (by linarith) (by linarith) (by linarith) (by linarith)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.p32_core
