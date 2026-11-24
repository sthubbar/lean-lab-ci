import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Termwise

/-!
# Proof of the LEAF `mv_619_weights` of `Lemma3MV617Integral`

Burst burst-20261122, step mv619_weights, run by a Claude cloud session S112.

Source P0015, Montgomery and Vaughan 1975, page 365, display (6.19) and the display after it,
with Lemma 5.2, Lemma 5.4 display (5.1) and display (5.2) of page 358.

* `tauInd_norm_sq_le`: `|τ(χ̃χ₀)|² ≤ r̃` for the character mod `q` induced by primitive `χ̃`
  mod `r̃`, Lemmas 5.1 and 5.2, through the lab's `Lemma2MVSplit.mv_lemma52` and `mv_lemma51_norm_le`.
* `ramanujan_norm_le`: `|c_q(-n)| ≤ φ(q)/φ(q/(q,n))` for every `q ≥ 1`, squarefree or not,
  display (5.2), from the lab's `Lemma2MVSplit.mv_cchi_bound` at the principal character.
* `ramanujanInd_norm_le`: `|c_{χ̃χ₀}(-n)| ≤ r̃^{1/2} φ(q)/φ(q/(q,n))` for every `q` with
  `r̃ ∣ q`, Lemma 5.4 display (5.1), again from `mv_cchi_bound`, the conductor of `χ̃χ₀` being
  `r̃`. This holds without squarefree `q`, so the factor `μ(q)` is only bounded by one.
* `mv_619_weights_proved`: the exact type twin of `Lemma3MV617Integral.mv_619_weights`, with
  `C = 2`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV619Weights

open Real Finset DirichletCharacter
open LeanLab.ExceptionalSet.U1539 (eC)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (ramanujan rem66_cchi mv_lemma52 mv_cchi_bound
  mv_lemma51_norm_le rem66_cchi_one_eq_gaussSum)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
  (tauInd ramanujanInd excWeight crossWeight)

/-- Ramanujan's sum is the twisted sum of the principal character, P0015 page 354. -/
theorem ramanujan_eq_cchi_one (q : ℕ) [NeZero q] (m : ℤ) :
    ramanujan q m = rem66_cchi (1 : DirichletCharacter ℂ q) m := by
  unfold ramanujan rem66_cchi
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hc : Nat.Coprime h q
  · have hu : IsUnit (h : ZMod q) := (ZMod.isUnit_iff_coprime h q).mpr hc
    rw [if_pos hc, MulChar.one_apply hu, one_mul]
  · have hu : ¬ IsUnit (h : ZMod q) := fun hu => hc ((ZMod.isUnit_iff_coprime h q).mp hu)
    rw [if_neg hc, MulChar.map_nonunit _ hu, zero_mul]

/-- P0015 display (5.2): `|c_q(-n)| ≤ φ(q)/φ(q/(q,n))` for every `q ≥ 1`, PROVED. -/
theorem ramanujan_norm_le (q n : ℕ) (hq : 1 ≤ q) :
    ‖ramanujan q (-(n : ℤ))‖ ≤ (q.totient : ℝ) / ((q / Nat.gcd q n).totient : ℝ) := by
  have : NeZero q := ⟨by omega⟩
  rw [ramanujan_eq_cchi_one]
  have h := mv_cchi_bound mv_lemma52 q 1 hq (-(n : ℤ))
  rw [conductor_one, if_pos (one_dvd _)] at h
  simpa [Int.natAbs_neg, Int.natAbs_natCast] using h

/-- The twisted sum of (6.4̃) is the lab's `rem66_cchi` of the induced character at `-n`. -/
theorem ramanujanInd_eq {r : ℕ} (χ : DirichletCharacter ℂ r) (q n : ℕ) (h : r ∣ q) :
    ramanujanInd χ q n = rem66_cchi (changeLevel h χ) (-(n : ℤ)) := by
  unfold ramanujanInd rem66_cchi
  rw [dif_pos h]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  push_cast
  ring

/-- P0015 Lemma 5.4 display (5.1) in norm form: `|c_{χ̃χ₀}(-n)| ≤ r̃^{1/2} φ(q)/φ(q/(q,n))` for
the character mod `q` induced by primitive `χ̃` mod `r̃`, any `q ≥ 1` with `r̃ ∣ q`, PROVED. -/
theorem ramanujanInd_norm_le {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (q n : ℕ) (hq : 1 ≤ q) (h : r ∣ q) :
    ‖ramanujanInd χ q n‖ ≤
      Real.sqrt r * ((q.totient : ℝ) / ((q / Nat.gcd q n).totient : ℝ)) := by
  have : NeZero q := ⟨by omega⟩
  rw [ramanujanInd_eq χ q n h]
  have hb := mv_cchi_bound mv_lemma52 q (changeLevel h χ) hq (-(n : ℤ))
  rw [conductor_changeLevel, (isPrimitive_def χ).mp hχ] at hb
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at hb
  refine hb.trans ?_
  split_ifs
  · exact le_rfl
  · positivity

/-- P0015 Lemmas 5.1 and 5.2: `|τ(χ̃χ₀)| ≤ r̃^{1/2}`, PROVED. -/
theorem tauInd_norm_le {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (q : ℕ) : ‖tauInd χ q‖ ≤ Real.sqrt r := by
  unfold tauInd
  split_ifs with h
  · have : NeZero q := ⟨h.2⟩
    have hr : 1 ≤ r := Nat.pos_of_ne_zero (NeZero.ne r)
    rw [← rem66_cchi_one_eq_gaussSum, mv_lemma52 r q χ h.1 (Nat.pos_of_ne_zero h.2) hχ,
      norm_mul, norm_mul]
    have h1 : ‖((ArithmeticFunction.moebius (q / r) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖χ ((q / r : ℕ) : ZMod r)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h3 := mv_lemma51_norm_le r χ hr
    calc _ ≤ 1 * 1 * Real.sqrt r := by gcongr
      _ = _ := by ring
  · simp

/-- P0015 Lemmas 5.1 and 5.2: `|τ(χ̃χ₀)|² ≤ r̃`, PROVED. -/
theorem tauInd_norm_sq_le {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) (q : ℕ) : ‖tauInd χ q‖ ^ 2 ≤ (r : ℝ) := by
  have h := tauInd_norm_le χ hχ q
  have h0 := norm_nonneg (tauInd χ q)
  calc ‖tauInd χ q‖ ^ 2 ≤ Real.sqrt r ^ 2 := by gcongr
    _ = (r : ℝ) := Real.sq_sqrt (Nat.cast_nonneg r)

/-- PROVED twin of the LEAF `Lemma3MV617Integral.mv_619_weights`, P0015 page 365, with `C = 2`. -/
theorem mv_619_weights_proved :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral.mv_619_weights := by
  refine ⟨2, by norm_num, ?_⟩
  intro r _ χ hχ _ q n hq hrq _
  have hg : Int.gcd (n : ℤ) (q : ℤ) = Nat.gcd q n := by
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm]
  rw [hg]
  set A : ℝ := (q.totient : ℝ) with hA
  set B : ℝ := ((q / Nat.gcd q n).totient : ℝ) with hB
  have hA0 : 0 < A := by
    rw [hA]; exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hgpos : 0 < Nat.gcd q n := Nat.gcd_pos_of_pos_left _ (by omega)
  have hq1 : 0 < q / Nat.gcd q n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hgpos
  have hB0 : 0 < B := by
    rw [hB]; exact_mod_cast Nat.totient_pos.mpr hq1
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := Real.mul_self_sqrt hr0
  have hτ2 := tauInd_norm_sq_le χ hχ q
  have hτ := tauInd_norm_le χ hχ q
  have hc := ramanujan_norm_le q n hq
  have hci := ramanujanInd_norm_le χ hχ q n hq hrq
  rw [← hA, ← hB] at hc hci
  have hnA : ‖(q.totient : ℂ)‖ = A := by rw [hA, Complex.norm_natCast]
  have hmu : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h1 : ‖excWeight χ q n‖ ≤ (r : ℝ) * (1 / (A * B)) := by
    unfold excWeight
    rw [norm_mul, norm_div, norm_pow, norm_pow, hnA]
    calc ‖tauInd χ q‖ ^ 2 / A ^ 2 * ‖ramanujan q (-(n : ℤ))‖
        ≤ (r : ℝ) / A ^ 2 * (A / B) := by
          gcongr
      _ = (r : ℝ) * (1 / (A * B)) := by field_simp
  have h2 : ‖crossWeight χ q n‖ ≤ (r : ℝ) * (1 / (A * B)) := by
    unfold crossWeight
    rw [norm_div, norm_mul, norm_mul, norm_pow, hnA]
    calc ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ * ‖ramanujanInd χ q n‖ * ‖tauInd χ q‖ / A ^ 2
        ≤ 1 * (Real.sqrt r * (A / B)) * Real.sqrt r / A ^ 2 := by
          gcongr
      _ = (Real.sqrt r * Real.sqrt r) * (1 / (A * B)) := by field_simp
      _ = (r : ℝ) * (1 / (A * B)) := by rw [hsq]
  linarith

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV619Weights

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV619Weights.mv_619_weights_proved
