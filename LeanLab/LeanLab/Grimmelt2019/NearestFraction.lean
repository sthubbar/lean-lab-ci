/-
AI wrote this Lean code for CODEX task03.
P0074 page 8, the nearest fraction step in Lemma 3.1.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Lemma31

namespace LeanLab.Grimmelt2019.MainTerm
open LeanLab.PNTPort.LargeSieve

/-- Distance to the nearest integer satisfies the triangle inequality. -/
theorem dist0_triangle (u v : ℝ) : dist0 (u + v) ≤ dist0 u + dist0 v := by
  have h := dist0_le_abs_sub_int (u + v) (round u + round v)
  unfold dist0 at *
  push_cast at h
  calc
    |u + v - round (u + v)| ≤ |u + v - (round u + round v)| := h
    _ = |(u - round u) + (v - round v)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

/-- Every point except a nearest point is at least half the pair separation away. -/
theorem nearest_fraction_separated {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (α δ : ℝ) (p0 : ι)
    (hnear : ∀ p ∈ S, dist0 (α - f p0) ≤ dist0 (α - f p))
    (hsep : ∀ p ∈ S, p ≠ p0 → δ ≤ dist0 (f p - f p0)) :
    ∀ p ∈ S, p ≠ p0 → δ / 2 ≤ dist0 (α - f p) := by
  intro p hp hne
  have ht := dist0_triangle (f p - α) (α - f p0)
  rw [sub_add_sub_cancel, dist0_sub_comm (f p) α] at ht
  have hs := hsep p hp hne
  have hn := hnear p hp
  linarith

#print axioms dist0_triangle
#print axioms nearest_fraction_separated
end LeanLab.Grimmelt2019.MainTerm
