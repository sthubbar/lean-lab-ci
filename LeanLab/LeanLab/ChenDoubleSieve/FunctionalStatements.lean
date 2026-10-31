import LeanLab.ChenDoubleSieve.Section3
import LeanLab.ChenDoubleSieve.SigmaIntegral

/-!
# Wu 2004 Propositions 3 and 4 as explicit analytic inputs

Source: https://arxiv.org/pdf/0705.1652, pages 14, 15, 22, 25 and 26.
The multidimensional domains include their boundaries, which have measure zero.
No cited analytic proposition is asserted as a theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Wu04Functional
open Wu04Integral (sigma0)

/-- Parameters used in the weighted inequality and the functional inequalities. -/
structure Params where
  s : ℝ
  sp : ℝ
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ

/-- The nine auxiliary endpoints preceding Proposition 3. -/
def alpha (p : Params) : Fin 9 → ℝ :=
  ![p.k1 - 2, p.sp - 2, p.sp - p.sp / p.s - 1,
    p.sp - p.sp / p.k2 - 1, p.sp - p.sp / p.k3 - 1, p.sp - 2 * p.sp / p.k2,
    p.sp - p.sp / p.k1 - p.sp / p.k3,
    p.sp - p.sp / p.k1 - p.sp / p.k2, p.k1 - p.k1 / p.k2 - 1]

/-- Proposition 3's full parameter range. -/
def Admissible3 (s sp : ℝ) : Prop :=
  2 ≤ s ∧ s ≤ 3 ∧ 3 ≤ sp ∧ sp ≤ 5 ∧ 2 ≤ sp - sp / s

/-- Proposition 4's full parameter range. -/
def Admissible4 (p : Params) : Prop :=
  Admissible3 p.s p.sp ∧ p.s ≤ p.k3 ∧ p.k3 < p.k2 ∧ p.k2 < p.k1 ∧ p.k1 ≤ p.sp ∧
    (∀ j, 1 ≤ alpha p j ∧ alpha p j ≤ 3) ∧ alpha p 0 < alpha p 3 ∧ alpha p 4 < alpha p 7

/-- The interval indicator in the printed kernels. -/
def ind (a b t : ℝ) : ℝ := if a ≤ t ∧ t ≤ b then 1 else 0

/-- Xi1 from equation 3.21. -/
def Xi1 (s sp t : ℝ) : ℝ :=
  sigma0 t / (2 * t) * log (16 / ((s - 1) * (sp - 1))) +
  ind (sp - 2) 3 t / (2 * t) * log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) +
  ind (sp - sp / s - 1) (sp - 2) t / (2 * t) *
    log ((t + 1) / ((s - 1) * (sp - 1 - t)))

/-- Xi2 from equation 3.22. -/
def Xi2 (p : Params) (t : ℝ) : ℝ :=
  let P := (p.s - 1) * (p.sp - 1) * (p.k1 - 1) * (p.k2 - 1) * (p.k3 - 1)
  let a := alpha p
  let q := 5 * t * (1 - t / p.sp)
  sigma0 t / (5 * t) * log (1024 / P) +
  ind (a 1) 3 t / (5 * t) * log ((t + 1) ^ 5 / P) +
  ind (a 8) (a 0) t / (5 * t) * log ((t + 1) / ((p.k2 - 1) * (p.k1 - 1 - t))) +
  ind (a 4) (a 1) t / (5 * t) * log ((t + 1) / ((p.k3 - 1) * (p.sp - 1 - t))) +
  ind (a 2) (a 1) t / (5 * t) * log ((t + 1) / ((p.s - 1) * (p.sp - 1 - t))) +
  ind (a 0) (a 1) t / (5 * t) * log ((t + 1) ^ 2 / ((p.k1 - 1) * (p.k2 - 1))) +
  ind (a 6) (a 4) t / q * log (p.sp ^ 2 /
    ((p.k1 * p.sp - p.sp - p.k1 * t) * (p.k3 * p.sp - p.sp - p.k3 * t))) +
  ind (a 4) (a 7) t / q * log (p.sp * (p.sp - 1 - t) / (p.k1 * p.sp - p.sp - p.k1 * t)) +
  ind (a 5) (a 7) t / q * log (p.sp / (p.k2 * p.sp - p.sp - p.k2 * t)) +
  ind (a 7) (a 1) t / q * log (p.sp - 1 - t)

/-- A box intersected with the ordered simplex. -/
def domain {n : ℕ} (lo hi : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | Monotone x ∧ ∀ j, lo j ≤ x j ∧ x j ≤ hi j}

/-- The common Buchstab integral for dimensions n + 2.
The extra denominator factor squares the penultimate variable. -/
def buchstabIntegral (ω : ℝ → ℝ) (n : ℕ) (lo hi : Fin (n + 2) → ℝ) (φ : ℝ) : ℝ :=
  ∫ x in domain lo hi,
    ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) / ((∏ j, x j) * x ⟨n, by omega⟩)

/-- The maximum in Wu's definitions is encoded as a supremum.
Its finiteness and attainment remain analytic obligations. -/
def buchstabSup (ω : ℝ → ℝ) (n : ℕ) (lo hi : Fin (n + 2) → ℝ) : ℝ :=
  sSup {v | ∃ φ : ℝ, 2 ≤ φ ∧ v = buchstabIntegral ω n lo hi φ}

/-- I1 from Lemma 5.1. -/
def I1 (ω : ℝ → ℝ) (s sp : ℝ) : ℝ := buchstabSup ω 1 (fun _ => 1 / sp) (fun _ => 1 / s)

/-- The thirteen terms I2,9 to I2,21 from Lemma 5.2. -/
def I2 (ω : ℝ → ℝ) (p : Params) : Fin 13 → ℝ :=
  ![buchstabSup ω 1 (fun _ => 1 / p.k1) (fun _ => 1 / p.k3),
    buchstabSup ω 1 ![1/p.k1, 1/p.k1, 1/p.k2] ![1/p.k2, 1/p.k2, 1/p.s],
    buchstabSup ω 1 ![1/p.k1, 1/p.k2, 1/p.k2] ![1/p.k2, 1/p.k3, 1/p.k3],
    buchstabSup ω 1 ![1/p.sp, 1/p.sp, 1/p.k3] ![1/p.k1, 1/p.k1, 1/p.s],
    buchstabSup ω 1 ![1/p.sp, 1/p.k1, 1/p.k2] ![1/p.k1, 1/p.k2, 1/p.s],
    buchstabSup ω 1 ![1/p.sp, 1/p.k2, 1/p.k2] ![1/p.k1, 1/p.s, 1/p.s],
    buchstabSup ω 1 ![1/p.k1, 1/p.k2, 1/p.k3] ![1/p.k2, 1/p.k3, 1/p.s],
    buchstabSup ω 2 (fun _ => 1/p.k2) (fun _ => 1/p.k3),
    buchstabSup ω 2 ![1/p.k2, 1/p.k2, 1/p.k2, 1/p.k3] ![1/p.k3, 1/p.k3, 1/p.k3, 1/p.s],
    buchstabSup ω 2 ![1/p.k2, 1/p.k2, 1/p.k3, 1/p.k3] ![1/p.k3, 1/p.k3, 1/p.s, 1/p.s],
    buchstabSup ω 2 ![1/p.k1, 1/p.k3, 1/p.k3, 1/p.k3] ![1/p.k2, 1/p.s, 1/p.s, 1/p.s],
    buchstabSup ω 3 ![1/p.k2, 1/p.k3, 1/p.k3, 1/p.k3, 1/p.k3] ![1/p.k3, 1/p.s, 1/p.s, 1/p.s, 1/p.s],
    buchstabSup ω 4 (fun _ => 1/p.k3) (fun _ => 1/p.s)]

/-- The logarithmic integral used in Psi1 and Psi2. -/
def J (a b : ℝ) : ℝ := ∫ t in a..b, log (t - 1) / t

/-- The other logarithmic integral used in Psi1 and Psi2. -/
def K (r a b : ℝ) : ℝ := ∫ t in a..b, log (r * t - 1) / (t * (1 - t))

/-- Psi1 from Lemma 5.1. -/
def Psi1 (ω : ℝ → ℝ) (s sp : ℝ) : ℝ :=
  -J 2 (sp - 1) + K sp (1 - 1 / s) (1 - 1 / sp) / 2 - I1 ω s sp

/-- Psi2 from Lemma 5.2. -/
def Psi2 (ω : ℝ → ℝ) (p : Params) : ℝ :=
  -2 / 5 * J 2 (p.sp - 1) - 2 / 5 * J 2 (p.k1 - 1) - 1 / 5 * J 2 (p.k2 - 1) +
    1 / 5 * K p.sp (1 - 1 / p.s) (1 - 1 / p.sp) +
    1 / 5 * K p.k1 (1 - 1 / p.k3) (1 - 1 / p.k1) - 2 / 5 * ∑ j, I2 ω p j

/-- Proposition 3, stated as an analytic input. -/
def Proposition3 (H ω : ℝ → ℝ) : Prop :=
  ∀ s sp : ℝ, Admissible3 s sp →
    Psi1 ω s sp + (∫ t in (1 : ℝ)..3, H t * Xi1 s sp t) ≤ H s

/-- Proposition 4, stated as an analytic input. -/
def Proposition4 (H ω : ℝ → ℝ) : Prop :=
  ∀ p : Params, Admissible4 p →
    Psi2 ω p + (∫ t in (1 : ℝ)..3, H t * Xi2 p t) ≤ H p.s

/-- The defining equations for the linear sieve pair in equation 2.6. -/
def IsLinearSieve (F f : ℝ → ℝ) : Prop :=
  ContinuousOn F (Ioi 0) ∧ ContinuousOn f (Ioi 0) ∧
    (∀ u : ℝ, 0 < u → u ≤ 2 → F u = 2 * exp eulerMascheroniConstant / u ∧ f u = 0) ∧
    (∀ u : ℝ, 2 < u → HasDerivAt (fun v => v * F v) (f (u - 1)) u ∧
      HasDerivAt (fun v => v * f v) (F (u - 1)) u)

/-- Buchstab's function as specified in Lemma 2.10. -/
def IsBuchstab (ω : ℝ → ℝ) : Prop :=
  ContinuousOn ω (Ici 1) ∧ (∀ u : ℝ, 1 ≤ u → u ≤ 2 → ω u = 1 / u) ∧
    (∀ u : ℝ, 2 < u → HasDerivAt (fun v => v * ω v) (ω (u - 1)) u)

/-- A real correction pair representing the extended real Section 3 definitions.
This requires finiteness and is an analytic input. -/
def RepresentsCorrections (F f : ℝ → ℝ) (δ : ℝ) (H h : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, s ∈ Icc 1 10 → (H s : EReal) = Wu04.H F δ s ∧ (h s : EReal) = Wu04.h f δ s

/-- The four rows of Table 1 that use Proposition 4. -/
def tableParams : Fin 4 → Params :=
  ![⟨2.2, 4.54, 3.53, 2.90, 2.44⟩, ⟨2.3, 4.50, 3.54, 2.88, 2.43⟩,
    ⟨2.4, 4.46, 3.57, 2.87, 2.40⟩, ⟨2.5, 4.12, 3.56, 2.91, 2.50⟩]

/-- Every printed Proposition 4 parameter row meets all nine endpoint conditions. -/
theorem tableParams_admissible : ∀ i : Fin 4, Admissible4 (tableParams i) := by
  intro i
  fin_cases i <;> norm_num [Admissible4, Admissible3, tableParams, alpha, Fin.forall_fin_succ]

/-- The grid used in Section 7, with zero based vector coordinates. -/
def grid (j : Fin 10) : ℝ := if j = 0 then 1 else 2 + (j.val + 1) / 10

/-- The Table 1 lower entries for Psi, written exactly as rationals. -/
def tablePsi : Fin 9 → ℝ :=
  ![0.015826357, 0.015247971, 0.013898757, 0.011776059, 0.009405211,
    0.006558950, 0.003536751, 0.001056651, 0]

/-- The five rows of Table 1 that use Proposition 3. -/
def tableSp : Fin 5 → ℝ := ![3.58, 3.47, 3.34, 3.19, 3.00]

/-- The displayed Psi values are lower bound inputs, not proved decimal identities. -/
def Table1PsiBounds (ω : ℝ → ℝ) : Prop :=
  (∀ i : Fin 4, tablePsi ⟨i.val, by omega⟩ ≤ Psi2 ω (tableParams i)) ∧
  (∀ i : Fin 5, tablePsi ⟨i.val + 4, by omega⟩ ≤
    Psi1 ω (grid ⟨i.val + 5, by omega⟩) (tableSp i))

end LeanLab.ChenDoubleSieve.Wu04Functional

#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.tableParams_admissible
