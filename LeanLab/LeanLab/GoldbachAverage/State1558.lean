import LeanLab.GoldbachAverage.FourierMass124
import LeanLab.GoldbachAverage.BSPDecomp82
import LeanLab.GoldbachAverage.LZTheorem1RH

/-!
# P0050 Bhowmik and Schlage-Puchta 2010, the statements not yet stated

Source: arXiv 0806.3295v3, read 2026-10-26 by unit U-1558, run 20261026T1604Z-17563.
Theorem 1.1 on pages 1 and 2 is over REAL x. The lab so far stated the error only at integers N,
`E N` in Links.lean and `ErrSmallO` in BSPOmega.lean. Here:

* the real variable error `Ereal`, the real forms of both parts of Theorem 1.1;
* Lemma 1, Selberg, page 2; Lemma 2, Gallagher, page 3; Lemma 3, page 3;
  Lemma 4, Gallagher 1970 Theorem 7, page 5; all as sealed Props, cited inputs;
* the paper's two derivations as OPEN bridges with sorry:
  Lemmas 1 and 2 give Lemma 3, and Lemma 4 gives the large values of G;
* assemblies with zero sorry: the real Omega part from large values of G,
  and the real upper part from the proved integer bound plus a named floor step input.

AI wrote this Lean code. Checked only by the Lean kernel. Binary Goldbach is OPEN; these are
averages over n, not statements about each n.
-/

open Finset Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage.State1558
open LeanLab.GoldbachAverage

/-! ## Theorem 1.1 over real x -/

/-- The error in Theorem 1.1 at real `x`: `|Σ_{n ≤ x} G(n) - x²/2 - H(x)|` with
`H(x) = -2 Σ_ρ x^{1+ρ}/(ρ(1+ρ)) = -2 Z1 x`. -/
def Ereal (x : ℝ) : ℝ :=
  ‖((∑ n ∈ range (⌊x⌋₊ + 1), G n : ℝ) : ℂ) - (x : ℂ) ^ 2 / 2 + 2 * Z1 x‖

/-- The real error is `o(x log log x)`. -/
def ErrSmallOReal : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → Ereal x ≤ ε * x * Real.log (Real.log x)

/-- Theorem 1.1, first display, page 2, over real x: under RH the error is `O(x log⁵ x)`. -/
def Thm1_1UpperRealStatement : Prop :=
  RiemannHypothesis → ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → Ereal x ≤ K * x * Real.log x ^ 5

/-- Theorem 1.1, second display, page 2, over real x: under RH the error is
`Ω(x log log x)`, read as in the paper on page 4: not `o(x log log x)`. -/
def Thm1_1OmegaRealStatement : Prop := RiemannHypothesis → ¬ ErrSmallOReal

/-- Theorem 1.1, both parts, over real x. -/
def Thm1_1Statement : Prop := Thm1_1UpperRealStatement ∧ Thm1_1OmegaRealStatement

/-- The large values input, pages 4 and 5: `G(n) = Ω(n log log n)`.
Same type as `BSPDecomp82.large_G`. -/
def LargeGStatement : Prop := ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    c * N * Real.log (Real.log N) ≤ G N

/-- Floor step input for the real upper bound: under RH the zero sum moves by
`O(x log⁵ x)` between `⌊x⌋` and `x`. Under RH the truth is `O(x^{1/2} log² x)`. -/
def ZeroSumFloorStepStatement : Prop :=
  RiemannHypothesis → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    ‖Z1 x - Z1 (⌊x⌋₊ : ℝ)‖ ≤ C * x * Real.log x ^ 5

/-! ## Lemmas 1 to 4 -/

/-- `e(α) = exp(2πiα)`. -/
def eA (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

/-- Lemma 1, Selberg 1943 eq. 13, page 2: under RH,
`∫_1^x |ψ(t+h) - ψ(t) - h|² dt ≪ x h log² x`. The paper gives no range for h; we take
`1 ≤ h ≤ x`. -/
def Lemma1SelbergStatement : Prop :=
  RiemannHypothesis → ∃ K : ℝ, ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ x →
    ∫ t in (1 : ℝ)..x, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2
      ≤ K * x * h * Real.log x ^ 2

/-- Lemma 2, Gallagher, Montgomery LNM 227 Lemma 1.9, page 3: for `c_1, ..., c_N` and
`S(t) = Σ c_n e(tn)`, `∫_{-1/y}^{1/y} |S(t)|² dt ≪ y^{-2} ∫ |A(x)|² dx`,
`A(x) = Σ_{n ≤ N, |n - x| ≤ y/4} c_n`. -/
def Lemma2GallagherStatement : Prop :=
  ∃ K : ℝ, ∀ (N : ℕ) (c : ℕ → ℂ) (y : ℝ), 0 < y →
    ∫ t in (-(1 / y))..(1 / y), ‖∑ n ∈ Icc 1 N, c n * eA (t * n)‖ ^ 2
      ≤ K * y⁻¹ ^ 2 * ∫ x : ℝ,
        ‖∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |(n : ℝ) - x| ≤ y / 4), c n‖ ^ 2

/-- `R(α) = S(α) - T(α) = Σ_{n ≤ x} (Λ(n) - 1) e(αn)`, page 2. -/
def Rsum (x α : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℂ) - 1) * eA (α * n)

/-- Lemma 3, page 3: under RH, for `y ≤ x`,
`y^{-1} ∫_{-1/y}^{1/y} |R(α)|² dα ≪ (x/y) log⁴ x`. We take `1 ≤ y ≤ x`. -/
def Lemma3Statement : Prop :=
  RiemannHypothesis → ∃ K : ℝ, ∀ x y : ℝ, 2 ≤ x → 1 ≤ y → y ≤ x →
    y⁻¹ * ∫ α in (-(1 / y))..(1 / y), ‖Rsum x α‖ ^ 2 ≤ K * (x / y) * Real.log x ^ 4

/-- `Σ_{x ≤ n ≤ x+h} Λ(n) χ(n)` for a character mod `q`. -/
def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x h : ℝ) : ℂ :=
  ∑ n ∈ Icc ⌈x⌉₊ ⌊x + h⌋₊, (Λ n : ℂ) * χ (n : ZMod q)

open Classical in
/-- Lemma 4, Gallagher 1970 Invent. Math. 11 Theorem 7, page 5:
`|h - Σ_{x ≤ n ≤ x+h} Λ(n)| + Σ_{1<q≤Q} Σ*_χ |Σ_{x ≤ n ≤ x+h} Λ(n) χ(n)| ≪ h exp(-c log x / log Q)`
for `x/Q ≤ h ≤ x`, `exp(log^{1/2} x) ≤ Q ≤ x^c`, the star sum over primitive χ mod q, the one
possible exceptional real character omitted. The exception depends on `Q` only: real
characters mod one modulus `q₁ = q₁(Q)` are dropped; `q₁ = 0` means none. The paper prints
`|x - Σ Λ(n)|`; `h` is meant, FILED misprint. -/
def Lemma4GallagherStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ Q : ℝ, ∃ q₁ : ℕ, ∀ x h : ℝ, 2 ≤ x →
    x / Q ≤ h → h ≤ x → Real.exp (Real.sqrt (Real.log x)) ≤ Q → Q ≤ x ^ c →
    |h - ∑ n ∈ Icc ⌈x⌉₊ ⌊x + h⌋₊, Λ n| +
      ∑ q ∈ range (⌊Q⌋₊ - 1),
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 2))).filter
            (fun χ => χ.IsPrimitive ∧ ¬ (q + 2 = q₁ ∧ χ ^ 2 = 1)),
          ‖psiChi χ x h‖
      ≤ K * h * Real.exp (-(c * Real.log x / Real.log Q))

/-! ## The paper's derivations, OPEN bridges -/

/-- OPEN bridge, page 3: Lemma 3 from Lemmas 1 and 2 with `c_n = Λ(n) - 1`, `N = x`. -/
theorem lemma3_of_lemma1_lemma2 (_h1 : Lemma1SelbergStatement)
    (_h2 : Lemma2GallagherStatement) : Lemma3Statement := by
  intro _hRH
  refine ⟨144, fun x y hx hy _hyx => ?_⟩
  have hb := FourierMass124.coarse_local_mean_square hx hy
  change (∫ α in (-(1 / y))..(1 / y), ‖Rsum x α‖ ^ 2) ≤
    144 * x * Real.log x ^ 4 at hb
  have hi := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (show 0 ≤ y by linarith))
  convert hi using 1 <;> ring

/-- OPEN bridge, pages 4 and 5: large values of G from Lemma 4, the primorial
`q = Π_{p < h, p ≠ p₁} p`, `S(x,q,a) ≥ x/φ(q)`, the sum over multiples of q and Mertens. -/
theorem largeG_of_lemma4 (_h4 : Lemma4GallagherStatement) : LargeGStatement := by
  sorry

/-! ## Assemblies, zero sorry -/

theorem Ereal_natCast (N : ℕ) : Ereal (N : ℝ) = E N := by
  simp [Ereal, E, Nat.floor_natCast]

/-- The real Omega part follows from the integer one: a real `o` bound restricts to integers.
PROVED, zero sorry. -/
theorem omega_real_of_integer (h : RiemannHypothesis → ¬ ErrSmallO) :
    Thm1_1OmegaRealStatement := by
  intro hRH hreal
  apply h hRH
  intro ε hε
  obtain ⟨X0, hX0⟩ := hreal ε hε
  refine ⟨⌈X0⌉₊, fun N hN => ?_⟩
  have hx : X0 ≤ (N : ℝ) := le_trans (Nat.le_ceil X0) (by exact_mod_cast hN)
  have := hX0 N hx
  rwa [Ereal_natCast] at this

/-- Theorem 1.1 Omega part over real x, CONDITIONAL ON the large values input. Zero sorry. -/
theorem omega_real_of_largeG (hL : LargeGStatement) : Thm1_1OmegaRealStatement :=
  omega_real_of_integer (fun hRH => OmegaTransfer82.bsp_omega_of_large_values hRH hL)

/-- The same through the lab's cited leaf `BSPDecomp82.large_G`; carries its sorryAx. -/
theorem omega_real_cited : Thm1_1OmegaRealStatement :=
  omega_real_of_largeG BSPDecomp82.large_G

theorem log_pow_five_ge {x : ℝ} (hx : 2 ≤ x) : (1 : ℝ) / 7 ≤ Real.log x ^ 5 := by
  have h2 : (0.69 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have : (0.69 : ℝ) ^ 5 ≤ Real.log x ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
  nlinarith

/-- Theorem 1.1 upper part over real x, CONDITIONAL ON the floor step input only, from the
lab's proved integer bound `bsp_upper_proved` under RH. Zero sorry. -/
theorem upper_real_of_floor_step (hZ : ZeroSumFloorStepStatement) :
    Thm1_1UpperRealStatement := by
  intro hRH
  obtain ⟨K, hK⟩ := bsp_upper_proved hRH
  obtain ⟨C, hC, hc⟩ := hZ hRH
  refine ⟨|K| + 7 + 2 * C, fun x hx => ?_⟩
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hn2 : 2 ≤ n := by
    have : (2 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact this
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogn : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hL5 : Real.log n ^ 5 ≤ Real.log x ^ 5 := pow_le_pow_left₀ hlog0 hlogn 5
  have hLx := log_pow_five_ge hx
  have hEn := hK n hn2
  -- split the real error
  set A : ℂ := ((∑ m ∈ range (n + 1), G m : ℝ) : ℂ) - (n : ℂ) ^ 2 / 2 + 2 * Z1 n
  have hsplit : ((∑ m ∈ range (n + 1), G m : ℝ) : ℂ) - (x : ℂ) ^ 2 / 2 + 2 * Z1 x
      = A + (((((n : ℝ) ^ 2 / 2 - x ^ 2 / 2 : ℝ)) : ℂ)) + 2 * (Z1 x - Z1 (n : ℝ)) := by
    simp only [A]; push_cast; ring
  have hEA : ‖A‖ = E n := rfl
  have hq : |(n : ℝ) ^ 2 / 2 - x ^ 2 / 2| ≤ x := by
    rw [abs_le]; constructor <;> nlinarith
  have hstep := hc x hx
  have hEreal : Ereal x ≤ E n + x + 2 * (C * x * Real.log x ^ 5) := by
    unfold Ereal
    rw [← hn, hsplit]
    calc ‖A + ((((n : ℝ) ^ 2 / 2 - x ^ 2 / 2 : ℝ)) : ℂ) + 2 * (Z1 x - Z1 (n : ℝ))‖
        ≤ ‖A‖ + ‖((((n : ℝ) ^ 2 / 2 - x ^ 2 / 2 : ℝ)) : ℂ)‖ + ‖2 * (Z1 x - Z1 (n : ℝ))‖ :=
          norm_add₃_le
      _ ≤ E n + x + 2 * (C * x * Real.log x ^ 5) := by
          rw [hEA, Complex.norm_real, Real.norm_eq_abs, norm_mul]
          have : ‖(2 : ℂ)‖ = 2 := by simp
          rw [this]
          linarith
  have hK1 : E n ≤ |K| * x * Real.log x ^ 5 := by
    calc E n ≤ K * n * Real.log n ^ 5 := hEn
      _ ≤ |K| * n * Real.log n ^ 5 := by
          have : 0 ≤ (n : ℝ) * Real.log n ^ 5 := by positivity
          nlinarith [le_abs_self K]
      _ ≤ |K| * x * Real.log x ^ 5 := by
          have h1 : (n : ℝ) * Real.log n ^ 5 ≤ x * Real.log x ^ 5 :=
            mul_le_mul hnx hL5 (by positivity) hx0
          have := abs_nonneg K
          nlinarith
  have hx7 : x ≤ 7 * x * Real.log x ^ 5 := by nlinarith
  nlinarith

/-- Theorem 1.1 over real x, both parts, CONDITIONAL ON the floor step input and the large
values input. Zero sorry. -/
theorem thm1_1_of_inputs (hZ : ZeroSumFloorStepStatement) (hL : LargeGStatement) :
    Thm1_1Statement :=
  ⟨upper_real_of_floor_step hZ, omega_real_of_largeG hL⟩

/-- The paper's own route for the Omega part: Lemma 4 gives it, through the OPEN bridge. -/
theorem omega_real_of_lemma4 (h4 : Lemma4GallagherStatement) : Thm1_1OmegaRealStatement :=
  omega_real_of_largeG (largeG_of_lemma4 h4)

/-- The two types agree with the lab's earlier leaf. -/
example : LargeGStatement = type_of% BSPDecomp82.large_G := rfl

/-! ## Vacuity instances -/

/-- Lemmas 1 and 3 and Theorem 1.1: the ranges hold at `x = 2`, `h = y = 1`. -/
example : (2 : ℝ) ≤ 2 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 := by norm_num

/-- Lemma 2: the hypothesis `0 < y` holds at `y = 1`. -/
example : (0 : ℝ) < 1 := by norm_num

/-- Lemma 4 at `c = 1`: `x = e⁴`, `Q = e²`, `h = x` satisfy all four range conditions. -/
example : (2 : ℝ) ≤ Real.exp 4 ∧ Real.exp 4 / Real.exp 2 ≤ Real.exp 4 ∧
    Real.exp 4 ≤ Real.exp 4 ∧
    Real.exp (Real.sqrt (Real.log (Real.exp 4))) ≤ Real.exp 2 ∧
    Real.exp 2 ≤ Real.exp 4 ^ (1 : ℝ) := by
  have h4 : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ); linarith
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have he24 : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
  have hsq : Real.sqrt (Real.log (Real.exp 4)) = 2 := by
    rw [Real.log_exp, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨h4, ?_, le_rfl, by rw [hsq], by rw [Real.rpow_one]; exact he24⟩
  rw [div_le_iff₀ he2]
  have : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  nlinarith [Real.exp_pos 4]

/-- The floor step input: at `x = 2`, `⌊x⌋ = x`, so the step is zero. PROVED. -/
example : ‖Z1 (2 : ℝ) - Z1 ((⌊(2 : ℝ)⌋₊ : ℕ) : ℝ)‖ ≤ 0 * 2 * Real.log 2 ^ 5 := by
  have : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [this]; simp

end LeanLab.GoldbachAverage.State1558

#print axioms LeanLab.GoldbachAverage.State1558.Ereal_natCast
#print axioms LeanLab.GoldbachAverage.State1558.omega_real_of_integer
#print axioms LeanLab.GoldbachAverage.State1558.omega_real_of_largeG
#print axioms LeanLab.GoldbachAverage.State1558.omega_real_cited
#print axioms LeanLab.GoldbachAverage.State1558.log_pow_five_ge
#print axioms LeanLab.GoldbachAverage.State1558.upper_real_of_floor_step
#print axioms LeanLab.GoldbachAverage.State1558.thm1_1_of_inputs
#print axioms LeanLab.GoldbachAverage.State1558.omega_real_of_lemma4
#print axioms LeanLab.GoldbachAverage.State1558.lemma3_of_lemma1_lemma2
#print axioms LeanLab.GoldbachAverage.State1558.largeG_of_lemma4
