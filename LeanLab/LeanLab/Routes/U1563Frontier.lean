/-
AI wrote this Lean code. Claude, for the Lean Lab, PC run 20261026T2003Z-2973, unit U-1563,
T2 FRONTIER, the Goldbach exceptional set exponent, idea I-0133.

Question: Pintz 2018, arXiv 1804.09084, and Zhao 2025, arXiv 2511.05631v2, both fix the
Burgess-type parameter `ϕ = 1/3` of Heath-Brown 1992, Lemma 2.5, p. 10:
`L(σ + it, χ) ≪ q^{ϕ(1-σ)(1+1/k)+ε} (1 + |t|)` for `1 - 1/k ≤ σ`, with `ϕ(χ) = 1/4` when `q`
is cube-free or `χ` has order at most `log q`, and `ϕ = 1/3` otherwise.  `ϕ` enters Zhao's
weighted density bound only through three places: `ξ = (ϕ/2) x g(0)/G(-λ₀/x)` in (3.26),
the term `ϕ/2 · (1 - e^{-2ωy})/y` of `B` in (2.15), and `k = 2(2ϕ + 3x + y + z)` in (3.3).
How far does Zhao's weight floor `W*`, exponent `1 - 1/W*`, move if `ϕ = 1/4` held for every
modulus?  MODEL numerics, Routes/gen/u1563_phi_scan.py: `W*` is 3.330 at `ϕ = 1/3`, 3.183 at
`0.30`, 3.101 at `0.28`, 2.991 at `ϕ = 1/4`, exponent 0.6657, below 2/3, with Lemma 2.4 and
the Theorem G cuts kept at their `ϕ = 1/3` values, which is conservative.

This file:
* `BurgessPhi ϕ`, Heath-Brown's Lemma 2.5 for every primitive character, a sealed Prop; CITED at
  `ϕ = 1/3`; at `ϕ = 1/4` for all moduli it is OPEN, known for cube-free moduli only.
* PROVED unconditional: `burgessPhi_mono`; the `ϕ`-parametrised `Bphi`, `Deltaphi`, `kphi`, which
  agree with the lab's `ϕ = 1/3` definitions; their monotonicity in `ϕ`; `Gz_pos`; the transfer
  `theoremI_anti` and `section4_mono_phi`: every Section 4 closing at `ϕ` also closes at any
  smaller `ϕ`; `section4_mono_W`; exponent arithmetic; vacuity instances.
* CONDITIONAL: `target_of_inputs`, `E(X) ≪ X^{2/3+ε}`, CONDITIONAL ON `ZhaoMethod I`, a CITED lab
  generalisation of Zhao's Sections 2 and 3 to a free `ϕ`, on `BurgessPhi (1/4)`, OPEN, and on
  `Section4Closes (1/4) 3 I`, OPEN and TESTED numerically only.
Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements
import LeanLab.Zhao2025.Zhao2025U6841N0

open Real

noncomputable section
namespace LeanLab.Routes.U1563

attribute [local instance] Classical.propDecidable

/-! ## 1. Heath-Brown's Lemma 2.5 as a hypothesis on `ϕ` -/

/-- Heath-Brown 1992, Lemma 2.5, p. 10, for EVERY nonprincipal primitive character, at the
parameter `ϕ`: for each `k ≥ 3` and `ε > 0`, `‖L(s, χ)‖ ≤ C q^{ϕ(1-σ)(1+1/k)+ε} (1 + |t|)` on
`1 - 1/k ≤ σ ≤ 1`.  CITED at `ϕ = 1/3`.  At `ϕ = 1/4` it is OPEN in general; Heath-Brown proves it
for cube-free `q` and for characters of order at most `log q`.  The upper limit `σ ≤ 1` is a
restriction of the printed `σ ≤ 1 + 1/log log q`, so this Prop is weaker than the printed lemma. -/
def BurgessPhi (φ : ℝ) : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, 1 - 1 / (k : ℝ) ≤ s.re → s.re ≤ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        C * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|)

/-- A smaller `ϕ` is a stronger hypothesis: `BurgessPhi ϕ → BurgessPhi ϕ'` for `ϕ ≤ ϕ'`. -/
theorem burgessPhi_mono {φ φ' : ℝ} (h : φ ≤ φ') (hB : BurgessPhi φ) : BurgessPhi φ' := by
  intro k hk ε hε
  obtain ⟨C, hC⟩ := hB k hk ε hε
  refine ⟨max C 0, ?_⟩
  intro q _ χ hχ h1 s hs1 hs2
  have hq : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hb := hC q χ hχ h1 s hs1 hs2
  have ht : 0 ≤ 1 + |s.im| := by positivity
  have hk0 : (0 : ℝ) ≤ 1 + 1 / (k : ℝ) := by positivity
  have hexp : φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε ≤ φ' * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε := by
    have h1s : 0 ≤ 1 - s.re := by linarith
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h h1s) hk0
    linarith
  have hpow : (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) ≤
      (q : ℝ) ^ (φ' * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hq hexp
  have hp0 : 0 ≤ (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) := by positivity
  calc ‖DirichletCharacter.LFunction χ s‖
      ≤ C * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) := hb
    _ ≤ max C 0 * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (q : ℝ) ^ (φ' * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) := by
        gcongr

/-! ## 2. Zhao's three `ϕ`-dependent quantities -/

/-- Zhao (2.15), Pintz (4.5) form, with a free `ϕ`. -/
def Bphi (φ t0 l l0 : ℝ) : ℝ :=
  φ / 2 * ((1 - Real.exp (-(2 * (l + l0) * t0))) / (l + l0)) +
    (1 - Real.exp (-(l * t0))) / (l * (l + l0)) +
    (Real.exp (-(2 * (l + l0) * t0)) - Real.exp (-(l * t0))) / ((l + l0) * (l + 2 * l0))

theorem Bphi_third (t0 l l0 : ℝ) : Bphi (1 / 3) t0 l l0 = Zhao2025.U6825.B t0 l l0 := by
  unfold Bphi Zhao2025.U6825.B; ring

theorem Bphi_mono {φ φ' t0 l l0 : ℝ} (h : φ ≤ φ') (hs : 0 < l + l0) (ht : 0 ≤ t0) :
    Bphi φ t0 l l0 ≤ Bphi φ' t0 l l0 := by
  unfold Bphi
  have he : Real.exp (-(2 * (l + l0) * t0)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ 2 * (l + l0) * t0 := by positivity
    linarith
  have hq : 0 ≤ (1 - Real.exp (-(2 * (l + l0) * t0))) / (l + l0) :=
    div_nonneg (by linarith) hs.le
  have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2)) hq
  linarith

/-- `Δ` of Zhao (3.26) with a free `ϕ`, `g(0) = 16/15`. -/
def Deltaphi (φ x L l0 : ℝ) : ℝ :=
  Zhao2025.U6841.Gz ((L - l0) / x) / Zhao2025.U6841.Gz (-l0 / x) -
    φ / 2 * x * (16 / 15) / Zhao2025.U6841.Gz (-l0 / x)

theorem Deltaphi_third (x L l0 : ℝ) : Deltaphi (1 / 3) x L l0 = Zhao2025.U6841.Delta x L l0 := by
  unfold Deltaphi Zhao2025.U6841.Delta; norm_num

theorem Deltaphi_anti {φ φ' x L l0 : ℝ} (h : φ ≤ φ') (hx : 0 ≤ x)
    (hG : 0 < Zhao2025.U6841.Gz (-l0 / x)) : Deltaphi φ' x L l0 ≤ Deltaphi φ x L l0 := by
  unfold Deltaphi
  have : φ / 2 * x * (16 / 15) / Zhao2025.U6841.Gz (-l0 / x) ≤
      φ' / 2 * x * (16 / 15) / Zhao2025.U6841.Gz (-l0 / x) := by
    apply div_le_div_of_nonneg_right _ hG.le
    have := mul_le_mul_of_nonneg_right h hx
    nlinarith
  linarith

/-- `G(z) > 0` for every real `z`: the weight `g` of (3.21) is positive on `(0, 2)`. -/
theorem Gz_pos (z : ℝ) : 0 < Zhao2025.U6841.Gz z := by
  unfold Zhao2025.U6841.Gz
  have hc : Continuous (fun u : ℝ => Zhao2025.U6841.gpoly u * Real.exp (-(u * z))) := by
    unfold Zhao2025.U6841.gpoly; fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ (by norm_num)
  intro u hu
  obtain ⟨h0, h2⟩ := hu
  apply mul_pos _ (Real.exp_pos _)
  rw [Zhao2025.U6841.gpoly_factored]
  have : 0 < 2 - u := by linarith
  positivity

/-- `k` of Zhao (3.3), general case, with a free `ϕ`. -/
def kphi (φ x y z : ℝ) : ℝ := 2 * (2 * φ + 3 * x + y + z)

theorem kphi_mono {φ φ' x y z : ℝ} (h : φ ≤ φ') : kphi φ x y z ≤ kphi φ' x y z := by
  unfold kphi; linarith

/-- At `ϕ = 1/4` the Lemma 3.1 constraint `k ≤ W` gains `1/3` over `ϕ = 1/3`. -/
theorem kphi_gain (x y z : ℝ) : kphi (1 / 3) x y z - kphi (1 / 4) x y z = 1 / 3 := by
  unfold kphi; ring

/-! ## 3. Theorem I at `ϕ` and the Section 4 closing condition -/

/-- Pintz's Theorem I in Zhao's form (3.26) at the parameter `ϕ`, for a finite list `zs` of
normalised zero distances `λ = (1 - β) log q`: for every lower bound `λ₀` of the list, every
`Λ`, and every `x ≥ max(4λ₀/5, 3/5)` with `Δ > 0`, the count `N(Λ)` of `λ ≤ Λ` satisfies
`N(Λ)(Δ² - 10⁻⁸) ≤ 1`.  The `10⁻⁸` is the lab's `ε` of U-6900. -/
def TheoremIAt (φ : ℝ) (zs : List ℝ) : Prop :=
  ∀ l0 L x : ℝ, (∀ t ∈ zs, l0 ≤ t) → max (4 * l0 / 5) (3 / 5) ≤ x → 0 < Deltaphi φ x L l0 →
    (zs.countP (fun t => decide (t ≤ L)) : ℝ) * (Deltaphi φ x L l0 ^ 2 - 1 / 10 ^ 8) ≤ 1

/-- Vacuity: the empty zero list satisfies Theorem I at every `ϕ`. -/
theorem theoremI_nil (φ : ℝ) : TheoremIAt φ [] := by
  intro l0 L x _ _ _; simp

/-- Theorem I at a smaller `ϕ` implies Theorem I at a larger one. -/
theorem theoremI_anti {φ φ' : ℝ} (h : φ ≤ φ') {zs : List ℝ} (hI : TheoremIAt φ zs) :
    TheoremIAt φ' zs := by
  intro l0 L x hl hx hD
  have hx0 : 0 ≤ x := le_trans (by norm_num) (le_trans (le_max_right _ _) hx)
  have hmono := Deltaphi_anti (L := L) h hx0 (Gz_pos (-l0 / x))
  have hD' : 0 < Deltaphi φ x L l0 := lt_of_lt_of_le hD hmono
  have hb := hI l0 L x hl hx hD'
  have hsq : Deltaphi φ' x L l0 ^ 2 ≤ Deltaphi φ x L l0 ^ 2 :=
    pow_le_pow_left₀ hD.le hmono 2
  have hN : (0 : ℝ) ≤ (zs.countP (fun t => decide (t ≤ L)) : ℝ) := Nat.cast_nonneg _
  calc (zs.countP (fun t => decide (t ≤ L)) : ℝ) * (Deltaphi φ' x L l0 ^ 2 - 1 / 10 ^ 8)
      ≤ (zs.countP (fun t => decide (t ≤ L)) : ℝ) * (Deltaphi φ x L l0 ^ 2 - 1 / 10 ^ 8) := by
        apply mul_le_mul_of_nonneg_left _ hN; linarith
    _ ≤ 1 := hb

/-- The weighted class sum `S_ν = Σ e^{-Wλ}` of Pintz (2.44), Zhao (1.10). -/
def classSum (W : ℝ) (c : List ℝ) : ℝ := (c.map (fun t => Real.exp (-(W * t)))).sum

/-- The Section 4 closing condition at `(ϕ, W)`, relative to a predicate `Inputs` that carries
every other zero input of Zhao's Sections 2 to 4, Theorems G, H, J and Lemma 2.4, all at
`ϕ = 1/3`: every configuration of zero classes with nonnegative `λ` meeting `Inputs` and
Theorem I at `ϕ` has `Σ_ν S_ν² < 1`.  OPEN as a Lean statement for Zhao's `Inputs`; TESTED by the
MODEL scan at `(1/4, 3)`. -/
def Section4Closes (φ W : ℝ) (Inputs : List (List ℝ) → Prop) : Prop :=
  ∀ cls : List (List ℝ), (∀ c ∈ cls, ∀ t ∈ c, 0 ≤ t) → Inputs cls → TheoremIAt φ cls.flatten →
    (cls.map (fun c => classSum W c ^ 2)).sum < 1

/-- Vacuity: with only the empty configuration admitted, Section 4 closes at every `(ϕ, W)`. -/
theorem section4_vacuity (φ W : ℝ) : Section4Closes φ W (fun cls => cls = []) := by
  intro cls _ h _; subst h; simp

/-- Closing at `ϕ'` gives closing at every smaller `ϕ`: lowering `ϕ` is conservative. -/
theorem section4_mono_phi {φ φ' W : ℝ} {I : List (List ℝ) → Prop} (h : φ ≤ φ')
    (hS : Section4Closes φ' W I) : Section4Closes φ W I :=
  fun cls hnn hI hT => hS cls hnn hI (theoremI_anti h hT)

theorem classSum_anti {W W' : ℝ} (h : W ≤ W') {c : List ℝ} (hc : ∀ t ∈ c, 0 ≤ t) :
    classSum W' c ≤ classSum W c := by
  unfold classSum
  apply List.sum_le_sum
  intro t ht
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right h (hc t ht)
  linarith

theorem classSum_nonneg (W : ℝ) (c : List ℝ) : 0 ≤ classSum W c := by
  unfold classSum
  apply List.sum_nonneg
  intro a ha
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
  exact (Real.exp_pos _).le

/-- Closing at weight `W` gives closing at every larger weight. -/
theorem section4_mono_W {φ W W' : ℝ} {I : List (List ℝ) → Prop} (h : W ≤ W')
    (hS : Section4Closes φ W I) : Section4Closes φ W' I := by
  intro cls hnn hI hT
  refine lt_of_le_of_lt ?_ (hS cls hnn hI hT)
  apply List.sum_le_sum
  intro c hc
  exact pow_le_pow_left₀ (classSum_nonneg W' c) (classSum_anti h (hnn c hc)) 2

/-! ## 4. The method, the target and the conditional theorem -/

/-- CITED, a LAB GENERALISATION, MODEL: Zhao's Sections 2 and 3, with Pintz 2018's reduction
(2.33) and A = 1/ϑ = W, run with Heath-Brown's Lemma 2.5 at a free `ϕ` in `[1/4, 1/3]`:
`BurgessPhi ϕ` and Section 4 closing at `(ϕ, W)` give `E(X) ≪ X^{1-1/W+ε}`.  Zhao prints only
`ϕ = 1/3`, `W = 10/3`; that the rest of his argument is uniform in `ϕ` is the lab's reading of
Pintz pp. 11 to 21, where `ϕ` enters only through `ϕ ≥ max ϕ(χ)` in Theorems C, D, H, I. -/
def ZhaoMethod (I : List (List ℝ) → Prop) : Prop :=
  ∀ φ W : ℝ, 1 / 4 ≤ φ → φ ≤ 1 / 3 → 3 ≤ W → BurgessPhi φ → Section4Closes φ W I →
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (1 - 1 / W + ε)

/-- The I-0133 target: `E(X) ≪ X^{2/3+ε}` for every `ε > 0`. -/
def Target0133 : Prop := ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (2 / 3 + ε)

/-- CONDITIONAL ON `ZhaoMethod I` CITED, `BurgessPhi (1/4)` OPEN, `Section4Closes (1/4) 3 I`
OPEN and TESTED: the exceptional set exponent `2/3`. -/
theorem target_of_inputs {I : List (List ℝ) → Prop} (hM : ZhaoMethod I)
    (hB : BurgessPhi (1 / 4)) (hS : Section4Closes (1 / 4) 3 I) : Target0133 := by
  intro ε hε
  have := hM (1 / 4) 3 (le_refl _) (by norm_num) (le_refl _) hB hS ε hε
  rwa [show (1 : ℝ) - 1 / 3 + ε = 2 / 3 + ε by ring] at this

/-- Zhao's printed case, for comparison, through the same method: `ϕ = 1/3`, `W = 10/3`. -/
theorem zhao_printed_of_inputs {I : List (List ℝ) → Prop} (hM : ZhaoMethod I)
    (hB : BurgessPhi (1 / 3)) (hS : Section4Closes (1 / 3) (10 / 3) I) :
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (7 / 10 + ε) := by
  intro ε hε
  have := hM (1 / 3) (10 / 3) (by norm_num) (le_refl _) (by norm_num) hB hS ε hε
  rwa [show (1 : ℝ) - 1 / (10 / 3) + ε = 7 / 10 + ε by ring] at this

/-- Exponents: `1 - 1/3 = 2/3 < 7/10 < 0.72`, and the scan floor `W = 2.9912` gives below `2/3`. -/
theorem exponents :
    (1 : ℝ) - 1 / 3 = 2 / 3 ∧ (2 : ℝ) / 3 < 7 / 10 ∧ (7 : ℝ) / 10 < 72 / 100 ∧
      (1 : ℝ) - 1 / 2.9912 < 0.6657 := by
  norm_num

/-- `1 - 1/W` is increasing in `W > 0`. -/
theorem exponent_mono {W W' : ℝ} (hW : 0 < W) (h : W ≤ W') : 1 - 1 / W ≤ 1 - 1 / W' := by
  have := one_div_le_one_div_of_le hW h
  linarith

end LeanLab.Routes.U1563

end

#print axioms LeanLab.Routes.U1563.burgessPhi_mono
#print axioms LeanLab.Routes.U1563.Bphi_third
#print axioms LeanLab.Routes.U1563.Bphi_mono
#print axioms LeanLab.Routes.U1563.Deltaphi_third
#print axioms LeanLab.Routes.U1563.Deltaphi_anti
#print axioms LeanLab.Routes.U1563.Gz_pos
#print axioms LeanLab.Routes.U1563.kphi_mono
#print axioms LeanLab.Routes.U1563.kphi_gain
#print axioms LeanLab.Routes.U1563.theoremI_nil
#print axioms LeanLab.Routes.U1563.theoremI_anti
#print axioms LeanLab.Routes.U1563.section4_vacuity
#print axioms LeanLab.Routes.U1563.section4_mono_phi
#print axioms LeanLab.Routes.U1563.classSum_anti
#print axioms LeanLab.Routes.U1563.classSum_nonneg
#print axioms LeanLab.Routes.U1563.section4_mono_W
#print axioms LeanLab.Routes.U1563.target_of_inputs
#print axioms LeanLab.Routes.U1563.zhao_printed_of_inputs
#print axioms LeanLab.Routes.U1563.exponents
#print axioms LeanLab.Routes.U1563.exponent_mono
