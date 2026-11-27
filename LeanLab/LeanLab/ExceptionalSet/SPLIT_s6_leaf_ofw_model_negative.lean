import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_arc_energy_offwindow

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_ofw_model_negative`, the negative
frequencies of the truncated arc model `V_X = Vfun X √X √X` of P0083 Pintz 2026, as used in the off
window energy of P0029 Bhowmik and Grimmelt 2026.

The model is `V_X = Σ_{q ≤ √X} μ(q)²/φ(q)² A_q` with the arc sum
`A_q(z) = Σ_{(a,q)=1} hArc_{√X/(qX)}(z - a/q)`, so `v̂_X(n) = Σ_q μ(q)²/φ(q)² Â_q(n)`, proved here
by linearity.  Cauchy-Schwarz in the form of Sedrakyan's lemma with the weights
`λ_q = q²/φ(q)²` then gives, for every `n < 0`,
`|v̂_X(n)|² ≤ (Σ_q λ_q) Σ_q (μ(q)⁴/φ(q)⁴/λ_q) |Â_q(n)|²`, and summing over `n < 0`
reduces the parent leaf to two leaves:

* `leaf_ofw_arc_negative_energy`: the negative frequency energy of one arc sum `A_q` is
  `O(q⁴ X^{3/2})`, uniformly in `1 ≤ q ≤ √X`;
* `leaf_totient_lower`: `q ≤ C_η φ(q) q^η` for every `η > 0`.

With them `Σ_{q ≤ √X} λ_q ≪ X^{1/2 + η}` and the parent energy is `≪ X^{5/2 + ε}`, below
`X^{3/2 + 2Θ + ε}`; `leaf_ofw_model_negative_of_leaves` is that assembly.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwModelNegative

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- LEAF: the negative frequency energy of one arc sum.  For `1 ≤ q ≤ √X` the arc sum
`A_q(z) = Σ_{a < q, (a,q)=1} hArc_δ(z - a/q)`, `δ = √X/(qX)`, has coefficients
`Â_q(n) = c_q(n) ĥ_δ(n)` up to conjugation, with `c_q` the Ramanujan sum.  At `n < 0` the full line
profile `(X⁻¹ − 2πiβ)⁻²` has coefficient zero, so `ĥ_δ(n)` is minus the integral over `|β| > δ`,
of size `O(min(δ⁻¹, |n|⁻¹ δ⁻²))`; with the mean value `φ(q)` of `|c_q(n)|²` over blocks of length
`q ≤ δ⁻¹`, the energy over `n < 0` is `O(φ(q) δ⁻³) = O(q⁴ X^{3/2})`.  This is the truncation loss
of the arcs named in the parent leaf.  MEDIUM: the Fourier transform of `t e^{-t/X} 1_{t>0}`, one
integration by parts on the tails, and Ramanujan sum orthogonality. -/
theorem leaf_ofw_arc_negative_energy :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt X →
      (∑' n : ℤ, if n < 0 then
        ‖fourierCoeff (fun z : AddCircle (1 : ℝ) =>
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            hArc X ((Nat.sqrt X : ℝ) / (q * X))
              (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) n‖ ^ 2
        else 0)
        ≤ K * (q : ℝ) ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

/-- LEAF: the lower bound of Euler's function, `q ≤ C_η φ(q) q^η` for every `η > 0`, Hardy and
Wright Theorem 327 in the weak form `q/φ(q) ≪_η q^η`.  It controls the weights `q²/φ(q)²` of the
Cauchy-Schwarz step over `q ≤ √X`.  EASY: elementary, from `q/φ(q) = Π_{p ∣ q} (1 - 1/p)⁻¹`. -/
theorem leaf_totient_lower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ C * (q.totient : ℝ) * (q : ℝ) ^ η := by
  sorry

/-- The model coefficient as a weighted sum of the arc sum coefficients. -/
private lemma coeff_V_expand (X : ℕ) (hX : 0 < X) (n : ℤ) :
    fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n =
      ∑ q ∈ Icc 1 (Nat.sqrt X),
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (fun z : AddCircle (1 : ℝ) =>
            ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
              hArc X ((Nat.sqrt X : ℝ) / (q * X))
                (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) n := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have h1 : Vfun X (Nat.sqrt X) (Nat.sqrt X) = ∑ q ∈ Icc 1 (Nat.sqrt X),
      (fun z : AddCircle (1 : ℝ) =>
        (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
          ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            hArc X ((Nat.sqrt X : ℝ) / (q * X))
              (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) := by
    funext z; simp only [Vfun, Finset.sum_apply, Finset.mul_sum]
  have hint : ∀ q : ℕ, Integrable (fun z : AddCircle (1 : ℝ) =>
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          hArc X ((Nat.sqrt X : ℝ) / (q * X))
            (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) haarAddCircle := by
    intro q
    have hm : MemLp (fun z : AddCircle (1 : ℝ) =>
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          hArc X ((Nat.sqrt X : ℝ) / (q * X))
            (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) 2 haarAddCircle :=
      memLp_finsetSum (f := fun (a : ℕ) (z : AddCircle (1 : ℝ)) =>
          hArc X ((Nat.sqrt X : ℝ) / (q * X)) (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) _
        (fun a _ => memLp_translate (memLp_hArc hX0 _) _)
    exact (hm.const_mul _).integrable one_le_two
  rw [h1, fourierCoeff.sum (Icc 1 (Nat.sqrt X)) (fun (q : ℕ) (z : AddCircle (1 : ℝ)) =>
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          hArc X ((Nat.sqrt X : ℝ) / (q * X))
            (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) (fun q _ => hint q),
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact fourierCoeff.const_mul _ _ _

/-- Assembly: the statement of `leaf_ofw_model_negative` from the arc energy leaf and the totient
leaf. -/
theorem leaf_ofw_model_negative_of_leaves (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n < 0 then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨K, hK, hE⟩ := leaf_ofw_arc_negative_energy
  obtain ⟨C, hC, hphi⟩ := leaf_totient_lower (ε / 4) (by positivity)
  refine ⟨K * C ^ 4, by positivity, 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set Q := Nat.sqrt X with hQ
  let w : ℕ → ℝ := fun q => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2
  let A : ℕ → AddCircle (1 : ℝ) → ℂ := fun q z =>
    ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      hArc X ((Q : ℝ) / (q * X)) (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))
  let lam : ℕ → ℝ := fun q => (q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2
  let x : ℕ → ℤ → ℝ := fun q n => if n < 0 then ‖fourierCoeff (A q) n‖ ^ 2 else 0
  have hqS : ∀ q ∈ Icc 1 Q, 1 ≤ q ∧ q ≤ Q := fun q hq => Finset.mem_Icc.1 hq
  have hphipos : ∀ q ∈ Icc 1 Q, (0 : ℝ) < (q.totient : ℝ) := fun q hq => by
    have := (hqS q hq).1
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hlam : ∀ q ∈ Icc 1 Q, 0 < lam q := fun q hq => by
    have := (hqS q hq).1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have := hphipos q hq
    positivity
  have hw0 : ∀ q, 0 ≤ w q := fun q => by positivity
  have hmu : ∀ q : ℕ, (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := fun q => by
    have h := ArithmeticFunction.abs_moebius_le_one (n := q)
    have h' : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by exact_mod_cast h
    nlinarith [abs_nonneg (ArithmeticFunction.moebius q : ℝ), sq_abs (ArithmeticFunction.moebius q : ℝ)]
  have hwle : ∀ q ∈ Icc 1 Q, w q ^ 2 * (q : ℝ) ^ 4 ≤ lam q ^ 2 := fun q hq => by
    have hp := hphipos q hq
    have hw : w q ≤ 1 / (q.totient : ℝ) ^ 2 := by
      simp only [w]
      exact div_le_div_of_nonneg_right (hmu q) (by positivity)
    have hw' : w q ^ 2 ≤ (1 / (q.totient : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (hw0 q) hw 2
    have : lam q ^ 2 = (1 / (q.totient : ℝ) ^ 2) ^ 2 * (q : ℝ) ^ 4 := by
      simp only [lam]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hw' (by positivity)
  have hsum : ∀ q ∈ Icc 1 Q, Summable (x q) := fun q _ => by
    have hm : MemLp (A q) 2 haarAddCircle :=
      memLp_finsetSum (f := fun (a : ℕ) (z : AddCircle (1 : ℝ)) =>
          hArc X ((Q : ℝ) / (q * X)) (z - (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))) _
        (fun a _ => memLp_translate (memLp_hArc hX0 _) _)
    have hh := hasSum_sq_fourierCoeff (hm.toLp (A q))
    have hcoef : fourierCoeff ((hm.toLp (A q) : Lp ℂ 2 haarAddCircle) :
        AddCircle (1 : ℝ) → ℂ) = fourierCoeff (A q) :=
      fourierCoeff_congr_ae (MemLp.coeFn_toLp hm)
    rw [hcoef] at hh
    exact Summable.of_nonneg_of_le (fun n => by simp only [x]; split_ifs <;> positivity)
      (fun n => by simp only [x]; split_ifs <;> first | exact le_rfl | positivity) hh.summable
  set L := ∑ q ∈ Icc 1 Q, lam q with hL
  have hpt : ∀ n : ℤ, (if n < 0 then
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0) ≤
      L * ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * x q n := by
    intro n
    by_cases hn : n < 0
    · rw [if_pos hn, coeff_V_expand X hXpos n]
      have h1 : ‖∑ q ∈ Icc 1 Q, ((w q : ℝ) : ℂ) * fourierCoeff (A q) n‖ ≤
          ∑ q ∈ Icc 1 Q, w q * ‖fourierCoeff (A q) n‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 q)]
      have h2 := Finset.sq_sum_div_le_sum_sq_div (Icc 1 Q)
        (fun q => w q * ‖fourierCoeff (A q) n‖) hlam
      have hLpos : 0 < L := by
        have hQ1 : 1 ≤ Q := by
          rw [hQ]; exact Nat.le_sqrt.2 (by simpa using hX)
        exact Finset.sum_pos hlam ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hQ1⟩⟩
      rw [div_le_iff₀ hLpos] at h2
      have h3 : ∑ q ∈ Icc 1 Q, (w q * ‖fourierCoeff (A q) n‖) ^ 2 / lam q =
          ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * x q n := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [x, if_pos hn]
        ring
      rw [h3] at h2
      have h0 : 0 ≤ ‖∑ q ∈ Icc 1 Q, ((w q : ℝ) : ℂ) * fourierCoeff (A q) n‖ := norm_nonneg _
      have h4 : ‖∑ q ∈ Icc 1 Q, ((w q : ℝ) : ℂ) * fourierCoeff (A q) n‖ ^ 2 ≤
          (∑ q ∈ Icc 1 Q, w q * ‖fourierCoeff (A q) n‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      have h5 : (∑ q ∈ Icc 1 Q, w q * ‖fourierCoeff (A q) n‖) ^ 2 ≤
          L * ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * x q n := by linarith
      exact h4.trans h5
    · rw [if_neg hn]
      have : ∀ q, x q n = 0 := fun q => by simp only [x, if_neg hn]
      simp [this]
  have hRsum : Summable (fun n : ℤ => L * ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * x q n) :=
    (summable_sum fun q hq => (hsum q hq).mul_left _).mul_left _
  have hLsum : Summable (fun n : ℤ => if n < 0 then
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpt hRsum
  have hlamle : ∀ q ∈ Icc 1 Q, lam q ≤ C ^ 2 * ((Q : ℝ) ^ (ε / 4)) ^ 2 := fun q hq => by
    have hq1 := (hqS q hq).1
    have hp := hphipos q hq
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have h1 : (q : ℝ) / q.totient ≤ C * (q : ℝ) ^ (ε / 4) := by
      rw [div_le_iff₀ hp]
      have := hphi q hq1
      linarith
    have h2 : (q : ℝ) ^ (ε / 4) ≤ (Q : ℝ) ^ (ε / 4) :=
      Real.rpow_le_rpow hq0 (by exact_mod_cast (hqS q hq).2) (by positivity)
    have h3 : (q : ℝ) / q.totient ≤ C * (Q : ℝ) ^ (ε / 4) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hC)
    have h4 : lam q = ((q : ℝ) / q.totient) ^ 2 := by simp only [lam]; rw [div_pow]
    rw [h4]
    have h5 : 0 ≤ (q : ℝ) / q.totient := by positivity
    calc ((q : ℝ) / q.totient) ^ 2 ≤ (C * (Q : ℝ) ^ (ε / 4)) ^ 2 := pow_le_pow_left₀ h5 h3 2
      _ = C ^ 2 * ((Q : ℝ) ^ (ε / 4)) ^ 2 := by ring
  have hLle : L ≤ (Q : ℝ) * (C ^ 2 * ((Q : ℝ) ^ (ε / 4)) ^ 2) := by
    have := Finset.sum_le_sum hlamle
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
    simpa using this
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun q hq => (hlam q hq).le
  have hE' : ∀ q ∈ Icc 1 Q, ∑' n, x q n ≤ K * (q : ℝ) ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ) :=
    fun q hq => hE X hX q (hqS q hq).1 (hqS q hq).2
  have hQX : ((Q : ℝ)) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have hQX' : (Q : ℝ) ≤ X := by exact_mod_cast Nat.sqrt_le_self X
  have hQ4 : ((Q : ℝ) ^ (ε / 4)) ^ 4 = (Q : ℝ) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hQε : (Q : ℝ) ^ ε ≤ (X : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hQX' hε.le
  have hXpow : (X : ℝ) ^ (3 / 2 : ℝ) * (X : ℝ) * (X : ℝ) ^ ε = (X : ℝ) ^ (5 / 2 + ε) := by
    rw [Real.rpow_add hX0, show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hX0,
      Real.rpow_one]
  have hpow : (X : ℝ) ^ (5 / 2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc (∑' n : ℤ, if n < 0 then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0)
      ≤ ∑' n : ℤ, L * ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * x q n :=
        hLsum.tsum_le_tsum hpt hRsum
    _ = L * ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * ∑' n, x q n := by
        rw [tsum_mul_left, Summable.tsum_finsetSum (fun q hq => (hsum q hq).mul_left _)]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [tsum_mul_left]
    _ ≤ L * ∑ q ∈ Icc 1 Q, (w q ^ 2 / lam q) * (K * (q : ℝ) ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hL0
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (hE' q hq) (div_nonneg (sq_nonneg _) (hlam q hq).le)
    _ ≤ L * ∑ q ∈ Icc 1 Q, lam q * (K * (X : ℝ) ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hL0
        apply Finset.sum_le_sum
        intro q hq
        have hl := hlam q hq
        have hw := hwle q hq
        have hKX : 0 ≤ K * (X : ℝ) ^ (3 / 2 : ℝ) := by positivity
        rw [div_mul_eq_mul_div, div_le_iff₀ hl]
        have : w q ^ 2 * (K * (q : ℝ) ^ 4 * (X : ℝ) ^ (3 / 2 : ℝ)) =
            (w q ^ 2 * (q : ℝ) ^ 4) * (K * (X : ℝ) ^ (3 / 2 : ℝ)) := by ring
        rw [this]
        have : lam q * (K * (X : ℝ) ^ (3 / 2 : ℝ)) * lam q =
            lam q ^ 2 * (K * (X : ℝ) ^ (3 / 2 : ℝ)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hw hKX
    _ = K * (X : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 := by rw [← Finset.sum_mul, ← hL]; ring
    _ ≤ K * (X : ℝ) ^ (3 / 2 : ℝ) * ((Q : ℝ) * (C ^ 2 * ((Q : ℝ) ^ (ε / 4)) ^ 2)) ^ 2 := by
        gcongr
    _ = K * C ^ 4 * ((X : ℝ) ^ (3 / 2 : ℝ) * (Q : ℝ) ^ 2 * ((Q : ℝ) ^ (ε / 4)) ^ 4) := by ring
    _ ≤ K * C ^ 4 * ((X : ℝ) ^ (3 / 2 : ℝ) * (X : ℝ) * (X : ℝ) ^ ε) := by
        rw [hQ4]
        gcongr
    _ = K * C ^ 4 * (X : ℝ) ^ (5 / 2 + ε) := by rw [hXpow]
    _ ≤ K * C ^ 4 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by gcongr

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a.OfwModelNegative
