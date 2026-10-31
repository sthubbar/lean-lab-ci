/-
P0030 Goldston 1990 page 285. Shared declarations moved verbatim from Goldston1990.lean.
The source statements and proofs keep their text. This split prevents an import cycle.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.ChirreHagen2025.Improved

namespace LeanLab.GoldbachGaps.Goldston1990
open Real

/-- Goldston's Goldbach number: an even number that is a sum of two primes. -/
def GNum (n : ℕ) : Prop := Even n ∧ IsGoldbachSum n

/-- Chirre-Hagen's Goldbach numbers, sums of two odd primes, are Goldston's. -/
theorem gnum_of_chirreHagen {n : ℕ} (h : ChirreHagen2025.IsGoldbachNumber n) : GNum n := by
  obtain ⟨p, q, hp, hq, hop, hoq, rfl⟩ := h
  exact ⟨hop.add_odd hoq, p, q, hp, hq, rfl⟩

/-- Kátai, Montgomery-Vaughan form. -/
def KataiMV : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
    ∃ n : ℕ, GNum n ∧ N ≤ n ∧ (n : ℝ) ≤ N + C * Real.log N ^ 2

/-- Linnik's form. -/
def LinnikRH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
    ∃ n : ℕ, GNum n ∧ N ≤ n ∧ (n : ℝ) ≤ N + Real.log N ^ (3 + ε)

/-- The Kátai, Montgomery-Vaughan form gives Linnik's. -/
theorem linnikRH_of_kataiMV (h : KataiMV) : LinnikRH := by
  obtain ⟨C, hC, N0, hN0⟩ := h
  intro ε hε
  refine ⟨max N0 (Real.exp (max C 1)), fun N hN => ?_⟩
  obtain ⟨n, hn, h1, h2⟩ := hN0 N (le_trans (le_max_left _ _) hN)
  refine ⟨n, hn, h1, h2.trans ?_⟩
  have hexp : Real.exp (max C 1) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlog : max C 1 ≤ Real.log N := by
    rw [← Real.log_exp (max C 1)]; exact Real.log_le_log (Real.exp_pos _) hexp
  have hL1 : 1 ≤ Real.log N := le_trans (le_max_right _ _) hlog
  have hLC : C ≤ Real.log N := le_trans (le_max_left _ _) hlog
  have h3 : Real.log N ^ (3 : ℝ) ≤ Real.log N ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h3' : Real.log N ^ (3 : ℝ) = Real.log N * Real.log N ^ 2 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hL0 : 0 ≤ Real.log N ^ 2 := sq_nonneg _
  have hCL : C * Real.log N ^ 2 ≤ Real.log N * Real.log N ^ 2 :=
    mul_le_mul_of_nonneg_right hLC hL0
  calc N + C * Real.log N ^ 2 ≤ N + Real.log N ^ (3 : ℝ) := by rw [h3']; linarith
    _ ≤ N + Real.log N ^ (3 + ε) := by linarith

/-- The lab's I-0010 gives the Kátai, Montgomery-Vaughan form with `C = 62`. -/
theorem kataiMV_of_62
    (h : ∀ x : ℝ, 2 ≤ x →
      ∃ n : ℕ, ChirreHagen2025.IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 62 * Real.log x ^ 2) :
    KataiMV := by
  refine ⟨62, by norm_num, 2, fun N hN => ?_⟩
  obtain ⟨n, hn, h1, h2⟩ := h N hN
  exact ⟨n, gnum_of_chirreHagen hn, h1.le, h2.le⟩

/-- Under RH, both quoted results from Chirre-Hagen's Theorem 3, cited, and the even check to
`4 · 10^18`, cited. -/
theorem kataiMV_linnik_of_chirreHagen
    (h3 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
      ChirreHagen2025.Jtheta x δ ≤ 2.5571 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2)
    (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    RiemannHypothesis → KataiMV ∧ LinnikRH := by
  intro hRH
  have hK := kataiMV_of_62 (ChirreHagen2025.goldbach_62 h3 hE hRH)
  exact ⟨hK, linnikRH_of_kataiMV hK⟩

end LeanLab.GoldbachGaps.Goldston1990
