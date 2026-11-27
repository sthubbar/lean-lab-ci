/-
ROUTE BURST S10, burst-20261124, step prop81merged, supporting file. What Lemma 4.2 of P0029,
page 16, does give for the minor arc count of the Proposition 8.1 sketch, page 31: for every
`ε > 0` the minor arc part `r_𝔪(N)` exceeds `X^{1−ε/4}` for at most `C_ε X^{3/5+ε}` even
`N ≤ X`, with `R = X^ϑ`, `2/5 ≤ ϑ < 4/9`. Here the threshold exponent depends on `ε`, unlike
the printed sentence of page 31 where `ε₀` is fixed before `ε`; see the QUESTION in
notes/burst-20261124/BhowmikGrimmelt2026-prop81merged.md. Proved from `lemma42` of
Minor84.lean by Chebyshev, `card_le_of_sum_sq` of Statements.lean. No new definitions.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.Minor84

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- Page 16 to 17 and page 31: Lemma 4.2 with Chebyshev gives, for every `ε > 0`, at most
`C_ε X^{3/5+ε}` integers `N ≤ X` with `|r_𝔪(N)| > X^{1−ε/4}`, at `R = X^ϑ`, `2/5 ≤ ϑ < 4/9`.
PROVED from `lemma42`. -/
theorem minor_count_eps_S10 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ≤ X ^ (1 - ε / 4))).card : ℕ) : ℝ) ≤
        C * X ^ (3 / 5 + ε) := by
  set a : ℝ := (ϑ + 1 / 2) / 2 with ha
  have hεa : 0 < 1 / 2 - a := by rw [ha]; linarith
  have haϑ : 0 < a - ϑ := by rw [ha]; linarith
  have ha0 : 0 < a := by rw [ha]; linarith
  obtain ⟨Cl, hCl⟩ := lemma42 (1 / 2 - a) hεa
  set X0 : ℝ := ((2 : ℝ) ^ a) ^ (1 / (a - ϑ)) with hX0
  have hX0pos : 0 ≤ X0 := by positivity
  refine ⟨X0 + 2 * |Cl| * (18 / ε) ^ 9, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  set n : ℕ := ⌊X⌋₊ with hn
  have hnX : (n : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hn2 : 2 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hX)
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnhalf : X / 2 ≤ n := by
    have := Nat.lt_floor_add_one X
    rw [← hn] at this
    linarith
  have hP : (0 : ℝ) ≤ X ^ (3 / 5 + ε) := Real.rpow_nonneg hXpos.le _
  have hP1 : (1 : ℝ) ≤ X ^ (3 / 5 + ε) := Real.one_le_rpow hX1 (by linarith)
  have hS : (((Finset.Icc 1 n).filter (fun N => Even N ∧
          ¬ ‖rMinor n (X ^ ϑ) N‖ ≤ X ^ (1 - ε / 4))).card : ℝ) ≤
      (((Finset.Icc 1 n).filter (fun N => X ^ (1 - ε / 4) ≤ |‖rMinor n (X ^ ϑ) N‖|)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (fun N hN => by
      rw [Finset.mem_filter] at hN ⊢
      exact ⟨hN.1, by rw [abs_of_nonneg (norm_nonneg _)]; exact (not_le.mp hN.2.2).le⟩)
  by_cases hbig : (2 : ℝ) ^ a < X ^ (a - ϑ)
  · -- main case: Lemma 4.2 applies
    have hR1 : (1 : ℝ) ≤ X ^ ϑ := Real.one_le_rpow hX1 (by linarith)
    have hRlt : X ^ ϑ < (n : ℝ) ^ (1 / 2 - (1 / 2 - a)) := by
      rw [show (1 / 2 - (1 / 2 - a) : ℝ) = a by ring]
      have h1 : (X / 2) ^ a ≤ (n : ℝ) ^ a :=
        Real.rpow_le_rpow (by positivity) hnhalf ha0.le
      have h2 : (X / 2) ^ a = X ^ a / 2 ^ a := Real.div_rpow hXpos.le (by norm_num) a
      have h3 : X ^ a = X ^ (a - ϑ) * X ^ ϑ := by
        rw [← Real.rpow_add hXpos]; ring_nf
      have h2a : (0 : ℝ) < 2 ^ a := by positivity
      have hXϑ : 0 < X ^ ϑ := by positivity
      have : X ^ ϑ < X ^ a / 2 ^ a := by
        rw [lt_div_iff₀ h2a, h3]
        calc X ^ ϑ * 2 ^ a < X ^ ϑ * X ^ (a - ϑ) := mul_lt_mul_of_pos_left hbig hXϑ
          _ = _ := by ring
      linarith
    have hB := hCl n hn2 (X ^ ϑ) hR1 hRlt
    have hT : (0 : ℝ) < X ^ (1 - ε / 4) := by positivity
    have hcheb := card_le_of_sum_sq (s := Finset.Icc 1 n)
      (f := fun N => ‖rMinor n (X ^ ϑ) N‖) hT (by simpa using hB)
    -- bound the Lemma 4.2 right side
    set L : ℝ := Real.log X with hL
    have hlogn : Real.log n ≤ L := Real.log_le_log (by linarith) hnX
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hLb : L ≤ X ^ (ε / 18) / (ε / 18) :=
      Real.log_le_rpow_div hXpos.le (by positivity)
    have hL9 : Real.log n ^ 9 ≤ (18 / ε) ^ 9 * X ^ (ε / 2) := by
      have h1 : Real.log n ^ 9 ≤ (X ^ (ε / 18) / (ε / 18)) ^ 9 :=
        pow_le_pow_left₀ hlogn0 (hlogn.trans hLb) 9
      have h2 : (X ^ (ε / 18) / (ε / 18)) ^ 9 = (18 / ε) ^ 9 * X ^ (ε / 2) := by
        rw [div_pow, ← Real.rpow_natCast (X ^ (ε / 18)), ← Real.rpow_mul hXpos.le]
        field_simp
        ring_nf
      linarith
    have hfirst : (n : ℝ) ^ 2 / X ^ ϑ ≤ X ^ (8 / 5 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have : X ^ (8 / 5 : ℝ) * X ^ ϑ = X ^ (2 : ℝ) * X ^ (ϑ - 2 / 5) := by
        rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]; ring_nf
      rw [this]
      have h1 : (n : ℝ) ^ 2 ≤ X ^ (2 : ℝ) := by
        rw [Real.rpow_two]; exact pow_le_pow_left₀ (by positivity) hnX 2
      have h2 : (1 : ℝ) ≤ X ^ (ϑ - 2 / 5) := Real.one_le_rpow hX1 (by linarith)
      have h3 : 0 ≤ X ^ (2 : ℝ) := by positivity
      exact h1.trans (le_mul_of_one_le_right h3 h2)
    have hsecond : (n : ℝ) ^ (8 / 5 : ℝ) ≤ X ^ (8 / 5 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hnX (by norm_num)
    have hbr : 0 ≤ (n : ℝ) ^ 2 / X ^ ϑ + (n : ℝ) ^ (8 / 5 : ℝ) := by positivity
    have hRHS : Cl * ((n : ℝ) ^ 2 / X ^ ϑ + (n : ℝ) ^ (8 / 5 : ℝ)) * n * Real.log n ^ 9 ≤
        |Cl| * (2 * X ^ (8 / 5 : ℝ)) * X * ((18 / ε) ^ 9 * X ^ (ε / 2)) := by
      have hpow0 : 0 ≤ Real.log n ^ 9 := by positivity
      calc Cl * ((n : ℝ) ^ 2 / X ^ ϑ + (n : ℝ) ^ (8 / 5 : ℝ)) * n * Real.log n ^ 9
          ≤ |Cl| * ((n : ℝ) ^ 2 / X ^ ϑ + (n : ℝ) ^ (8 / 5 : ℝ)) * n * Real.log n ^ 9 := by
            gcongr; exact le_abs_self _
        _ ≤ |Cl| * (2 * X ^ (8 / 5 : ℝ)) * X * ((18 / ε) ^ 9 * X ^ (ε / 2)) := by
            gcongr
            · linarith
    have hT2 : (X ^ (1 - ε / 4)) ^ 2 = X ^ (2 - ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; ring_nf
    have hcomb : X ^ (8 / 5 : ℝ) * X * X ^ (ε / 2) = X ^ (3 / 5 + ε) * X ^ (2 - ε / 2) := by
      rw [← Real.rpow_add hXpos, show X ^ (8 / 5 : ℝ) * X = X ^ (8 / 5 + 1 : ℝ) by
        rw [Real.rpow_add hXpos, Real.rpow_one], ← Real.rpow_add hXpos]
      ring_nf
    have hT2pos : 0 < X ^ (2 - ε / 2) := by positivity
    have hfinal : |Cl| * (2 * X ^ (8 / 5 : ℝ)) * X * ((18 / ε) ^ 9 * X ^ (ε / 2)) /
        (X ^ (1 - ε / 4)) ^ 2 = 2 * |Cl| * (18 / ε) ^ 9 * X ^ (3 / 5 + ε) := by
      rw [hT2, div_eq_iff hT2pos.ne']
      calc |Cl| * (2 * X ^ (8 / 5 : ℝ)) * X * ((18 / ε) ^ 9 * X ^ (ε / 2))
          = 2 * |Cl| * (18 / ε) ^ 9 * (X ^ (8 / 5 : ℝ) * X * X ^ (ε / 2)) := by ring
        _ = _ := by rw [hcomb]; ring
    have hdiv : Cl * ((n : ℝ) ^ 2 / X ^ ϑ + (n : ℝ) ^ (8 / 5 : ℝ)) * n * Real.log n ^ 9 /
        (X ^ (1 - ε / 4)) ^ 2 ≤ 2 * |Cl| * (18 / ε) ^ 9 * X ^ (3 / 5 + ε) := by
      rw [← hfinal]; gcongr
    have hcheb' := hcheb.trans hdiv
    calc _ ≤ _ := hS
      _ ≤ 2 * |Cl| * (18 / ε) ^ 9 * X ^ (3 / 5 + ε) := hcheb'
      _ ≤ (X0 + 2 * |Cl| * (18 / ε) ^ 9) * X ^ (3 / 5 + ε) := by nlinarith
  · -- small case: `X ≤ X0`, trivial count
    push_neg at hbig
    have hXle : X ≤ X0 := by
      have : X = (X ^ (a - ϑ)) ^ (1 / (a - ϑ)) := by
        rw [← Real.rpow_mul hXpos.le, mul_one_div_cancel haϑ.ne', Real.rpow_one]
      rw [this, hX0]
      exact Real.rpow_le_rpow (by positivity) hbig (by positivity)
    have hcard : (((Finset.Icc 1 n).filter (fun N => Even N ∧
          ¬ ‖rMinor n (X ^ ϑ) N‖ ≤ X ^ (1 - ε / 4))).card : ℝ) ≤ n := by
      have := Finset.card_filter_le (Finset.Icc 1 n) (fun N => Even N ∧
          ¬ ‖rMinor n (X ^ ϑ) N‖ ≤ X ^ (1 - ε / 4))
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    have h2 : 0 ≤ 2 * |Cl| * (18 / ε) ^ 9 * X ^ (3 / 5 + ε) := by positivity
    calc _ ≤ (n : ℝ) := hcard
      _ ≤ X0 := hnX.trans hXle
      _ ≤ X0 * X ^ (3 / 5 + ε) := le_mul_of_one_le_right hX0pos hP1
      _ ≤ (X0 + 2 * |Cl| * (18 / ε) ^ 9) * X ^ (3 / 5 + ε) := by nlinarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_count_eps_S10
