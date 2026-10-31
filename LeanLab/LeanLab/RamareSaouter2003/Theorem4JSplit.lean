import Mathlib
import LeanLab.RamareSaouter2003.Theorem4Assembly

/-!
# Ramaré-Saouter 2003, JLower split into display (15) and Lemma 3

P0099, unit U-6751, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

`JLower` of `Theorem4Assembly.lean`, display (16) of p. 20, is PROVED here from two inputs that
separate the paper's two steps:

* `JLower15 NT Zs T0`, display (15) of p. 20, the lower bound for `J/(uX)` with the zero sum
  `Σ_{|γ| > T} X^(β - 1)/|γ|^(m+1)` written `Zs m T X / X`. In the paper it comes from
  Lemma 4, RH verified to `T0` for the zeros with `|γ| ≤ T` and the `m` integrations by
  parts (14).
* `Lemma3Bound Zs T0`, Lemma 3 of p. 15 for `Zs m T x = Σ_{|γ| > T} x^β/|γ|^(m+1)`, together with
  the trivial `0 ≤ Zs m T x`. In the paper it comes from Lemma 2, hence Lemma 1, and RH to `T0`.

`Zs` is an abstract function: the two inputs are consistent statements about the same
zero sum, which the true sum satisfies by the paper. The step from (15) to (16) uses
`e^u + 1 ≤ 2.0001` for `u ≤ 5 · 10^-5`, PROVED.

Headlines: `jLower_of`, `theorem4Fm_of_split`, `theorem2At1e20_of_split`.
-/

namespace LeanLab.RamareSaouter2003.Thm4JSplit

open Real Chebyshev LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Thm4Parts
  LeanLab.RamareSaouter2003.Thm4Assembly

/-- **Lemma 3 of Ramaré-Saouter 2003, p. 15**, for an abstract zero sum
`Zs m T x = Σ_{|γ| > T} x^β/|γ|^(m+1)`, with the trivial `0 ≤ Zs m T x`. CITED. -/
def Lemma3Bound (Zs : ℕ → ℝ → ℝ → ℝ) (T0 : ℝ) : Prop :=
  ∀ (m : ℕ) (T x : ℝ), 1 ≤ m → 1000 ≤ T → T ≤ T0 → 10 ^ 5 ≤ x →
    0 ≤ Zs m T x ∧ Zs m T x ≤ sm m T * √x / T ^ m + sm m T0 * x / (2 * T0 ^ m)

/-- **Display (15) of Ramaré-Saouter 2003, p. 20**, for `f = f_m`, multiplied out by
`u X ||f_m||_1`; `Zs m T X / X` is the sum `Σ_{|γ| > T} X^(β - 1)/|γ|^(m+1)`. CITED. -/
def JLower15 (NT : ℝ → ℝ) (Zs : ℕ → ℝ → ℝ → ℝ) (T0 : ℝ) : Prop :=
  ∀ (m : ℕ) (X u δ T : ℝ), 2 ≤ m → 10 ^ 12 ≤ X → 0 < u → u ≤ 0.00005 → 0 < δ → δ ≤ 0.0001 →
    1000 ≤ T → T ≤ T0 →
    u * X * (1 - 1 / X ^ 2 - (1 + δ) * (2 * NT T) / √X -
        (1 + δ) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * δ ^ m)) * (Zs m T X / X)) *
        (∫ t in (0 : ℝ)..1, fm m t) ≤
      ∫ t in (0 : ℝ)..1, Dψ X u δ t * fm m t

/-- (16) from (15) and Lemma 3. PROVED CONDITIONAL ON `JLower15` and `Lemma3Bound`. -/
theorem jLower_of {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ} {T0 : ℝ} (h15 : JLower15 NT Zs T0)
    (hL3 : Lemma3Bound Zs T0) : JLower NT T0 := by
  intro m X u δ T hm hX hu0 hu hδ0 hδ hT hTT
  have h := h15 m X u δ T hm hX hu0 hu hδ0 hδ hT hTT
  obtain ⟨hz0, hz⟩ := hL3 m T X (by omega) hT hTT (by linarith)
  have hXpos : 0 < X := by linarith
  have hsX : 0 < √X := Real.sqrt_pos.mpr hXpos
  have hXs : √X * √X = X := Real.mul_self_sqrt hXpos.le
  have hTpos : 0 < T := by linarith
  have hT0pos : 0 < T0 := by linarith
  have hTm : 0 < T ^ m := pow_pos hTpos m
  have hT0m : 0 < T0 ^ m := pow_pos hT0pos m
  -- Zs / X ≤ S
  have hZS : Zs m T X / X ≤ sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m) := by
    rw [div_le_iff₀ hXpos]
    have e0 : ∀ s : ℝ, 0 < s → (sm m T / (s * T ^ m) + sm m T0 / (2 * T0 ^ m)) * (s * s) =
        sm m T * s / T ^ m + sm m T0 * (s * s) / (2 * T0 ^ m) := by
      intro s hs; field_simp
    have e := e0 √X hsX
    rw [hXs] at e
    rw [e]; exact hz
  have he : Real.exp u + 1 ≤ 2.0001 := by
    have h1 := exp_sub_one_le hu0.le (by linarith)
    have h2 : u ^ 2 ≤ 0.00005 * u := by rw [sq]; exact mul_le_mul_of_nonneg_right hu hu0.le
    linarith
  have hD : 0 < u * δ ^ m := mul_pos hu0 (pow_pos hδ0 m)
  have hc : 0 ≤ (1 + δ) ^ (m + 1) * muStar m :=
    mul_nonneg (pow_nonneg (by linarith) _) (muStar_nonneg m)
  have hZX : 0 ≤ Zs m T X / X := div_nonneg hz0 hXpos.le
  have hterm : (1 + δ) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * δ ^ m)) * (Zs m T X / X) ≤
      (1 + δ) ^ (m + 1) * muStar m * (2.0001 / (u * δ ^ m)) *
        (sm m T / (√X * T ^ m) + sm m T0 / (2 * T0 ^ m)) := by
    rw [mul_assoc, mul_assoc ((1 + δ) ^ (m + 1) * muStar m)]
    apply mul_le_mul_of_nonneg_left _ hc
    exact mul_le_mul (div_le_div_of_nonneg_right he hD.le) hZS hZX (by positivity)
  have hF : 0 ≤ ∫ t in (0 : ℝ)..1, fm m t := by rw [norm_fm]; positivity
  have huX : 0 ≤ u * X := by positivity
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_right _ hF
  apply mul_le_mul_of_nonneg_left _ huX
  linarith

/-- **Theorem 4 for `f_m`.** PROVED CONDITIONAL ON `MVBrunTitchmarsh`,
`SchoenfeldPT 0.998697 1.001093`, `JLower15` and `Lemma3Bound`. -/
theorem theorem4Fm_of_split (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ} {T0 : ℝ} (h15 : JLower15 NT Zs T0)
    (hL3 : Lemma3Bound Zs T0) : Theorem4Fm NT T0 :=
  theorem4Fm_of hMV hS (jLower_of h15 hL3)

/-- **Table 1 row one.** PROVED CONDITIONAL ON `MVBrunTitchmarsh`, `SchoenfeldPT`, `JLower15`,
`Lemma3Bound` with `T0 = 3.3e9`, and `Lemma1Upper NT`, which `RosserNUpper NT` gives by
`Lemma1Rosser.lemma1Upper_of_rosser`. -/
theorem theorem2At1e20_of_split (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} {Zs : ℕ → ℝ → ℝ → ℝ} (h15 : JLower15 NT Zs 3300000000)
    (hL3 : Lemma3Bound Zs 3300000000) (hN : Row1.Lemma1Upper NT) : Theorem2At1e20 :=
  theorem2At1e20_of_inputs hMV hS (jLower_of h15 hL3) hN

end LeanLab.RamareSaouter2003.Thm4JSplit

#print axioms LeanLab.RamareSaouter2003.Thm4JSplit.jLower_of
#print axioms LeanLab.RamareSaouter2003.Thm4JSplit.theorem4Fm_of_split
#print axioms LeanLab.RamareSaouter2003.Thm4JSplit.theorem2At1e20_of_split
