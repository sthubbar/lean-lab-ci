import Mathlib

namespace LeanLab.Pintz2018
open Real

/-- The zero-free region `R(α, T)` is `σ ≥ 1 - α / log q`, `|t| ≤ T`. -/
def RegionR (q : ℕ) (α T : ℝ) (s : ℂ) : Prop :=
  1 - α / Real.log (q : ℝ) ≤ s.re ∧ |s.im| ≤ T

/-- Theorem E of arXiv 1804.09084. For `q > q_0(T, ε)`, `M(s) = ∏_χ L(s, χ)` has at most one zero
in `R(0.44, T)`. If it exists, it is real and simple and belongs to a non-principal character.
We just state the condition of being a zero in the region for a character `χ`. -/
def ZeroInRegion (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α T : ℝ) (s : ℂ) : Prop :=
  RegionR q α T s ∧ DirichletCharacter.LFunction χ s = 0

/-- At most one character has a zero in the region, and it is at most one simple zero. We express
the non-existence of two distinct zeros (either for different characters or the same). -/
def TheoremE (T : ℝ) : Prop :=
  ∃ q0 : ℕ, ∀ q : ℕ, [NeZero q] → q0 ≤ q →
    ∀ (χ1 χ2 : DirichletCharacter ℂ q) (s1 s2 : ℂ),
      ZeroInRegion q χ1 (44 / 100) T s1 →
      ZeroInRegion q χ2 (44 / 100) T s2 →
      χ1 = χ2 ∧ s1 = s2

/-- Theorem F: `M(s)` has at most two zeros in `R(0.702, T)`. -/
def TheoremF (T : ℝ) : Prop :=
  ∃ q0 : ℕ, ∀ q : ℕ, [NeZero q] → q0 ≤ q →
    ∀ (χ1 χ2 χ3 : DirichletCharacter ℂ q) (s1 s2 s3 : ℂ),
      ZeroInRegion q χ1 (702 / 1000) T s1 →
      ZeroInRegion q χ2 (702 / 1000) T s2 →
      ZeroInRegion q χ3 (702 / 1000) T s3 →
      (χ1 = χ2 ∧ s1 = s2) ∨ (χ1 = χ3 ∧ s1 = s3) ∨ (χ2 = χ3 ∧ s2 = s3)

/-- Vacuity instance: the region `R(1, 1)` mod `3` contains `s = 1`, so `RegionR` is
satisfiable at a genuine modulus with `log q > 0`. Review fix: the original instance used
`q = 1`, where `log q = 0`. -/
theorem vacuity_RegionR : RegionR 3 1 1 1 := by
  unfold RegionR
  have h : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨?_, by simp⟩
  have : 0 ≤ (1 : ℝ) / Real.log ((3 : ℕ) : ℝ) := by
    rw [Nat.cast_ofNat]; exact le_of_lt (div_pos one_pos h)
  simp only [Complex.one_re]
  linarith

/-- Theorem G: Suppose that `χ` is a real non-principal character mod `q` with
`L(1 - λ / log q, χ) = 0`, `0 < λ ≤ 0.44`. Then `M(s)` has only the zero `1 - λ / log q`
in the region `R(Λ(λ), T) ∪ R(1.18, T)`, with
`Λ(λ) = min((12/11 - ε) log(1/λ), (1/3) log log log q)` as in (4.15).
Since `R(α, T)` grows with `α`, the union is `R(max(Λ(λ), 1.18), T)`.
Review fix: `Λ` was an arbitrary function argument, which made the Prop false for large `Λ`;
it is now the printed (4.15), depending on `ε` and `q`. Primitivity of `χ` is an extra
hypothesis, so this Prop is weaker than the printed Theorem G. -/
noncomputable def LambdaG (ε l : ℝ) (q : ℕ) : ℝ :=
  min ((12 / 11 - ε) * Real.log (1 / l)) ((1 / 3) * Real.log (Real.log (Real.log (q : ℝ))))

def TheoremG (T ε : ℝ) : Prop :=
  ∃ q0 : ℕ, ∀ q : ℕ, [NeZero q] → q0 ≤ q →
    ∀ (χ : DirichletCharacter ℂ q) (l : ℝ),
      χ.IsPrimitive → (∀ a, (χ a).im = 0) →
      0 < l → l ≤ 0.44 →
      DirichletCharacter.LFunction χ (1 - l / Real.log (q : ℝ)) = 0 →
      ∀ (χ2 : DirichletCharacter ℂ q) (s : ℂ),
        ZeroInRegion q χ2 (max (LambdaG ε l q) 1.18) T s →
        χ2 = χ ∧ s = 1 - l / Real.log (q : ℝ)

/-- Theorem D of arXiv 1804.09084: log-free zero-density theorem restricted to a set of characters
$K$ with bounded conductor of pairwise product. -/
def TheoremD_condition {q : ℕ} [NeZero q] (K : Set (DirichletCharacter ℂ q)) (ε : ℝ) : Prop :=
  ∀ χi χj : DirichletCharacter ℂ q, χi ∈ K → χj ∈ K →
    (DirichletCharacter.conductor (χi * χj) : ℝ) ≤ (q : ℝ) ^ ε

/-- Theorem D condition on ϕ and x0: x0 = ϕ + 3c1 + c2, ϕ ≥ max_{χ ∈ K} ϕ(χ).
We state these structural equalities used in the statement of Theorem D. -/
def TheoremD_parameters (phi x0 c1 c2 : ℝ) : Prop :=
  x0 = phi + 3 * c1 + c2

/-- Theorem I condition: H is a set of characters χ mod q with cond(χχ') ≤ q^ε for χ, χ' ∈ H. -/
def TheoremI_condition {q : ℕ} [NeZero q] (H : Set (DirichletCharacter ℂ q)) (ε : ℝ) : Prop :=
  ∀ χ χ' : DirichletCharacter ℂ q, χ ∈ H → χ' ∈ H →
    (DirichletCharacter.conductor (χ * χ') : ℝ) ≤ (q : ℝ) ^ ε

/-- Theorem K of arXiv 1804.09084: The optimal choice for a constrained maximization problem
involving `F(d_0 - d_j) - F(d_0)`. -/
def TheoremK_OptimalChoice (r : ℕ) (d_opt e : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j < r → d_opt j = e j

/-- Theorem J, (4.36) p. 17: `D(Λ) ≤ (1 - ξ + O(ε)) / (2Δ)`. Here `x` stands for `ξ`,
`D_var` for `Δ`, and `e` is an explicit stand-in for the `O(ε)` term. -/
def TheoremJ_bound (D : ℝ → ℝ) (x e D_var : ℝ) : Prop :=
  ∀ Λ, D Λ ≤ (1 - x + e) / (2 * D_var)

/-- Theorem H condition: ∆^2 > ξ + ε -/
def TheoremH_condition (Delta xi ε : ℝ) : Prop :=
  xi + ε < Delta ^ 2

/-- Theorem L from arXiv 1804.09084: For variables subject to bounds `c(m)`,
the maximum is achieved when equality holds. We formalize just the condition
`c(m + 1) - c(m) ≤ c(m) - c(m - 1)` defining the sequence of bounds. -/
def TheoremL_condition (c : ℕ → ℝ) : Prop :=
  ∀ m, 2 ≤ m → c (m + 1) - c m ≤ c m - c (m - 1)

/-- Lemma 6 bounds from the paper, (9.5) p. 38: `max b_i ≤ c_j^*` in Case `j`.
Review fix: the printed (9.5) value `c_4^* = 0.715` is used here. The agent wrote `0.0715`,
the value (9.28) uses; the lab found in FINDINGS that `0.0715` does not follow from
Theorem I, recomputed Case 4 is about `0.0755`. -/
def Lemma6_bounds (b_max : ℝ) (case_j : ℕ) : Prop :=
  (case_j = 1 → b_max ≤ 0.0722) ∧
  (case_j = 2 → b_max ≤ 0.0751) ∧
  (case_j = 3 → b_max ≤ 0.0826) ∧
  (case_j = 4 → b_max ≤ 0.715)

/-- Lemma 7, (9.14) p. 40: `∑_{i ≤ I} a_i ≤ c̃_ν`. Review fix: the agent wrote
`Real.exp c_nu`, an OCR misreading of the tilde in `c̃_ν`; the PDF page shows no exponential. -/
def Lemma7_bound (a : ℕ → ℝ) (I : ℕ) (c_nu : ℝ) : Prop :=
  (∑ i ∈ Finset.Icc 1 I, a i) ≤ c_nu

/-- The printed constants `c̃_1, …, c̃_5` of (9.15) p. 40. -/
noncomputable def Lemma7_const : ℕ → ℝ
  | 1 => 0.612
  | 2 => 0.622
  | 3 => 0.564
  | 4 => 0.453
  | 5 => 0.483
  | _ => 0

/-- Corollary 2 bounds from the paper: N(Λ) < E_i e^{8Λ/3} for Λ ≥ Λ_i. -/
def Corollary2_bound (N_bound : ℝ → ℝ) (E_i Lambda_i : ℝ) : Prop :=
  ∀ Lambda, Lambda ≥ Lambda_i → N_bound Lambda < E_i * Real.exp (8 * Lambda / 3)

/-- Theorem B of arXiv 1804.09084. If there is a Siegel zero,
then Goldbach holds for almost all even numbers. We formulate the condition
of existence of a Siegel zero `β_1 > 1 - h / log X` for a character with conductor
`cond χ_1 ≤ X^{4/9 - ε'}`. -/
def SiegelZeroCondition (X h ε' : ℝ) : Prop :=
  ∃ q : ℕ, ∃ _ : NeZero q, (q : ℝ) ≤ X ^ (4 / 9 - ε') ∧
    ∃ χ1 : DirichletCharacter ℂ q, χ1.IsPrimitive ∧
      ∃ β1 : ℝ, 1 - h / Real.log X < β1 ∧ DirichletCharacter.LFunction χ1 β1 = 0

end LeanLab.Pintz2018
