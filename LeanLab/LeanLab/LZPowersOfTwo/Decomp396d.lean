/-
P0079 pages 6 to 7 and 11, the paired moment input for the ordinary minor arc.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.PairedMoment396
import LeanLab.LZPowersOfTwo.Arithmetic293
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- LEAF. P0079 pages 6 to 7, Lemma 4 and displays 25 to 28.
The one-pair second moment has coefficient log 2 plus C Sprime q.
The epsilon log 2 slack absorbs the stated O of eta X L remainder.
This leaf contains no other prime factor and no minor-arc decomposition.
Parsell pages 368 to 369 give the cited earlier counting proof with its older constant. -/
theorem paired_second_moment396 (s : ℕ) (μ : ℕ → ℝ) (l m η ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hl : l ≠ 0) (hm : m ≠ 0)
    (r : ℚ) (hr : (r : ℝ) = l / m) (hη : 0 < η) (hη' : η < |l / r.num|)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ᶠ X : ℝ in atTop,
      (∫ α : ℝ, pairedMoment396 l m (cutoff293 s μ ε X) η ε X α) ≤
        (log 2 + bigC * Sprime r.den) * η * X * (cutoff293 s μ ε X) ^ 2 := by
  sorry

/-- P0079 page 11, display 41. CONDITIONAL ON paired_second_moment396.
This is the exact minor_good353 statement. Weighted Cauchy Schwarz and
the good power-sum bounds supply the rest without an OPEN reduction leaf. -/
theorem minor_good396 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X),
        integrand293 s l1 l2 μ γ η ε X α‖ ≤
          (ν ^ (s - 2) * Cq r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  have hν : 0 ≤ ν := by
    rcases hc with h | h
    · rw [h.1]; exact nuTr_pos.le
    · rw [h.1]; exact nuAlg_pos.le
  have hA : 0 < log 2 + bigC * Sprime r1.den := add_pos_of_pos_of_nonneg
    (log_pos (by norm_num)) (mul_nonneg (by norm_num [bigC]) (Sprime_pos293 _).le)
  have hB : 0 < log 2 + bigC * Sprime r2.den := add_pos_of_pos_of_nonneg
    (log_pos (by norm_num)) (mul_nonneg (by norm_num [bigC]) (Sprime_pos293 _).le)
  let a := sqrt (log 2 + bigC * Sprime r1.den)
  let b := sqrt (log 2 + bigC * Sprime r2.den)
  have ha : 0 < a := sqrt_pos.mpr hA
  have hb : 0 < b := sqrt_pos.mpr hB
  intro δ hδ
  filter_upwards [paired_second_moment396 s μ l1 (μ 0) η ε hM (by linarith) (hμ 0)
    r1 hr1 hη hη1 hε hε1,
    paired_second_moment396 s μ l2 (μ 1) η ε hM (by linarith) (hμ 1)
    r2 hr2 hη hη2 hε hε1,
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (2 : ℝ)] with X hm1 hm2 hL hX
  let E := minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hE : MeasurableSet E := by
    apply MeasurableSet.diff _ hbad
    unfold minor293
    measurability
  have hG : ∀ α ∈ E, ∀ i : Fin s,
      ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ ν * cutoff293 s μ ε X := by
    intro α hα i
    by_contra H
    exact hα.2 ⟨i, lt_of_not_ge H⟩
  have hm1' : (∫ α : ℝ, pairedMoment396 l1 (μ 0) (cutoff293 s μ ε X) η ε X α) ≤
      a ^ 2 * (η * X * (cutoff293 s μ ε X) ^ 2) := by
    simpa only [a, sq_sqrt hA.le, mul_assoc] using hm1
  have hm2' : (∫ α : ℝ, pairedMoment396 l2 (μ 1) (cutoff293 s μ ε X) η ε X α) ≤
      b ^ 2 * (η * X * (cutoff293 s μ ε X) ^ 2) := by
    simpa only [b, sq_sqrt hB.le, mul_assoc] using hm2
  have H := paired_integral_bound396 s l1 l2 μ γ η ε X (ν * cutoff293 s μ ε X)
    a b (η * X * (cutoff293 s μ ε X) ^ 2) E hE hs (mul_nonneg hν hL) ha hb hG hm1' hm2'
  have hp : (cutoff293 s μ ε X) ^ (s - 2) * (cutoff293 s μ ε X) ^ 2 =
      (cutoff293 s μ ε X) ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have he : (ν * cutoff293 s μ ε X) ^ (s - 2) * a * b *
      (η * X * (cutoff293 s μ ε X) ^ 2) =
        ν ^ (s - 2) * Cq r1.den r2.den * η * X * (cutoff293 s μ ε X) ^ s := by
    calc
      _ = ν ^ (s - 2) * Cq r1.den r2.den * η * X *
          ((cutoff293 s μ ε X) ^ (s - 2) * (cutoff293 s μ ε X) ^ 2) := by
        dsimp [a, b, Cq]
        rw [mul_pow]
        ring
      _ = _ := by rw [hp]
  apply H.trans
  rw [he]
  have hW : 0 ≤ η * X * (cutoff293 s μ ε X) ^ s := by positivity
  nlinarith only [mul_nonneg hδ.le hW]

end LeanLab.LZPowersOfTwo
