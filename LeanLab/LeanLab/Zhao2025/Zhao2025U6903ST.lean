import Mathlib
import LeanLab.Zhao2025.Zhao2025U6902Interval

/-!
# Zhao 2025, the `sT` input: (3.15) with general `k` at the five layout C cases, certified

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6903, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

(3.15): `T(Λ) ≤ (1 + ε) e^{-(10/3 - k)Λ} C(x, y, z, Λ, λ₀)` for `k ∈ [0, 10/3]`, with `C` of (3.5)
and `B` of (2.15) as transcribed in `Zhao2025U6825Lemma31`, and `k = 2(2ϕ + 3x + y + z)` of (3.3) when
`M` is not `O(1)`.  `chkT` encloses both `B` factors with `Ex`, takes a rational `b ≥ √(B₁B₂)` and
checks `e^{-(10/3-k)Λ} C (1 + 10⁻⁸) ≤ target`.

* `T315_le`, PROVED: a passing check gives `(1 + ε) e^{-(10/3-k)Λ} C ≤ target` for `0 ≤ ε ≤ 10⁻⁸`.
* `sT_of_315`, CONDITIONAL ON (3.15) as a hypothesis: `T ≤ target`.
* `c060_sT_ok` to `c068_sT_ok`, PROVED by kernel computation, the five `sT` values of U-6837.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Zhao2025.U6825

/-- `B(t₀, l, l₀)` of (2.15) as an `Ex`, `e^{-a}` written as `ex (3a/10)`. -/
def eB (t0 l l0 : ℚ) : Ex :=
  .add (.add (.dv (.sub (.c 1) (.ex (3 / 10 * (2 * (l + l0) * t0)))) (.c (6 * (l + l0))))
    (.dv (.sub (.c 1) (.ex (3 / 10 * (l * t0)))) (.c (l * (l + l0)))))
    (.dv (.sub (.ex (3 / 10 * (2 * (l + l0) * t0))) (.ex (3 / 10 * (l * t0))))
      (.c ((l + l0) * (l + 2 * l0))))

/-- `k` of (3.3), general case, `ϕ = 1/3`. -/
def kq (x y z : ℚ) : ℚ := 2 * (2 / 3 + 3 * x + y + z)

def chkT (x y z L l0 b t : ℚ) : Bool :=
  decide (0 < x) && decide (0 < y) && decide (0 < z) && decide (0 ≤ L) &&
  decide (kq x y z ≤ 10 / 3) &&
  (eB (1 / 3 + x + y) L l0).ok && (eB z L l0).ok &&
  decide (0 ≤ (eB (1 / 3 + x + y) L l0).iv.1) && decide (0 ≤ (eB z L l0).iv.1) &&
  decide (0 ≤ b) && decide ((eB (1 / 3 + x + y) L l0).iv.2 * (eB z L l0).iv.2 ≤ b ^ 2) &&
  decide (eupq ((10 / 3 - kq x y z) * L) * (1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)) * b *
    (1 + 1 / 10 ^ 8) ≤ t)

theorem hex (a : ℚ) : Real.exp (-(10 / 3 * ((3 / 10 * a : ℚ) : ℝ))) = Real.exp (-(a : ℝ)) := by
  congr 1; push_cast; ring

theorem val_eB (t0 l l0 : ℚ) (hs : (l : ℝ) + l0 ≠ 0) :
    (eB t0 l l0).val = B (t0 : ℝ) (l : ℝ) (l0 : ℝ) := by
  simp only [eB, Ex.val, hex, B]
  push_cast
  field_simp
  ring

/-- PROVED: a passing check bounds `(1 + ε) e^{-(10/3-k)Λ} C(x, y, z, Λ, λ₀)` by the target. -/
theorem T315_le (x y z L l0 b t : ℚ) (hl0 : 0 ≤ l0) (hL : 0 < L) (h : chkT x y z L l0 b t = true)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10 ^ 8) :
    (1 + ε) * (Real.exp (-((10 / 3 - (kq x y z : ℝ)) * L)) * C x y z L l0) ≤ t := by
  simp only [chkT, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hy⟩, hz⟩, _⟩, hk⟩, h1⟩, h2⟩, h10⟩, h20⟩, hb⟩, hbb⟩, hfin⟩ := h
  have hs : ((L : ℝ) + l0) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    have : (0 : ℝ) ≤ l0 := by exact_mod_cast hl0
    linarith
  have s1 := Ex.sound _ h1; have s2 := Ex.sound _ h2
  rw [val_eB _ _ _ hs] at s1 s2
  push_cast at s1 s2
  have h10' : (0 : ℝ) ≤ ((eB (1 / 3 + x + y) L l0).iv.1 : ℝ) := by exact_mod_cast h10
  have h20' : (0 : ℝ) ≤ ((eB z L l0).iv.1 : ℝ) := by exact_mod_cast h20
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hbb' : ((eB (1 / 3 + x + y) L l0).iv.2 : ℝ) * ((eB z L l0).iv.2 : ℝ) ≤ (b : ℝ) ^ 2 := by
    exact_mod_cast hbb
  have hprod : B (1 / 3 + (x : ℝ) + y) L l0 * B z L l0 ≤ (b : ℝ) ^ 2 := by
    have := mul_le_mul s1.2 s2.2 (h20'.trans s2.1) (h10'.trans (s1.1.trans s1.2))
    linarith
  have hsq : Real.sqrt (B (1 / 3 + (x : ℝ) + y) L l0 * B z L l0) ≤ b := by
    rw [Real.sqrt_le_left hb']; exact hprod
  have hkL : (0 : ℝ) ≤ (10 / 3 - (kq x y z : ℝ)) * L := by
    have : ((0 : ℚ) : ℝ) ≤ (((10 / 3 - kq x y z) * L : ℚ) : ℝ) := by
      exact_mod_cast mul_nonneg (by linarith) hL.le
    push_cast at this; exact this
  have he := eupq_ge ((10 / 3 - kq x y z) * L) (by exact_mod_cast (by
    have : (0 : ℚ) ≤ (10 / 3 - kq x y z) * L := mul_nonneg (by linarith) hL.le
    exact this))
  push_cast at he
  have hc0 : (0 : ℝ) ≤ 1 / ((x : ℝ) * z) * (1 / 2 + (1 / 3 + x) / y) := by
    have : (0 : ℝ) < x := by exact_mod_cast hx
    have : (0 : ℝ) < y := by exact_mod_cast hy
    have : (0 : ℝ) < z := by exact_mod_cast hz
    positivity
  have hfin' : (((eupq ((10 / 3 - kq x y z) * L) * (1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)) * b *
      (1 + 1 / 10 ^ 8) : ℚ) : ℝ) ≤ t) := by exact_mod_cast hfin
  push_cast at hfin'
  unfold C
  set E := Real.exp (-((10 / 3 - (kq x y z : ℝ)) * L))
  set Cc := 1 / ((x : ℝ) * z) * (1 / 2 + (1 / 3 + x) / y)
  set Eu := ((eupq ((10 / 3 - kq x y z) * L) : ℚ) : ℝ)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hS0 := Real.sqrt_nonneg (B (1 / 3 + (x : ℝ) + y) L l0 * B z L l0)
  have step1 : E * (Cc * Real.sqrt (B (1 / 3 + (x : ℝ) + y) L l0 * B z L l0)) ≤ Eu * (Cc * b) :=
    mul_le_mul he (mul_le_mul_of_nonneg_left hsq hc0) (mul_nonneg hc0 hS0) (hE0.trans he)
  have step2 : (1 + ε) * (E * (Cc * Real.sqrt (B (1 / 3 + (x : ℝ) + y) L l0 * B z L l0))) ≤
      (1 + 1 / 10 ^ 8) * (Eu * (Cc * b)) :=
    mul_le_mul (by linarith) step1 (mul_nonneg hE0 (mul_nonneg hc0 hS0)) (by norm_num)
  have e3 : (1 + 1 / 10 ^ 8) * (Eu * (Cc * b)) = Eu * Cc * b * (1 + 1 / 10 ^ 8) := by ring
  rw [e3] at step2
  calc (1 + ε) * (E * (Cc * Real.sqrt (B (1 / 3 + (x : ℝ) + y) L l0 * B z L l0))) ≤ _ := step2
    _ ≤ t := hfin'

/-- CONDITIONAL ON Zhao (3.15) with general `k`, as the hypothesis `h315` with `0 ≤ ε ≤ 10⁻⁸`:
the sum `T ≤ target`. -/
theorem sT_of_315 (x y z L l0 b t : ℚ) (hl0 : 0 ≤ l0) (hL : 0 < L) (h : chkT x y z L l0 b t = true)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 10 ^ 8) (T : ℝ)
    (h315 : T ≤ (1 + ε) * (Real.exp (-((10 / 3 - (kq x y z : ℝ)) * L)) * C x y z L l0)) :
    T ≤ t := h315.trans (T315_le x y z L l0 b t hl0 hL h ε hε0 hε)

end LeanLab.Zhao2025.U6900
