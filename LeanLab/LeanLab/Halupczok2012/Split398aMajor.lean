import LeanLab.Halupczok2012.Decomp398a
import LeanLab.Halupczok2012.Split398aMajorA4

/-!
Split of the open statement `Decomp398a.major_energy` into faithful leaves.
Source: A. Perelli and J. Pintz, On the exceptional set for Goldbach's problem in short
intervals, J. London Math. Soc. 47, 1993, pages 41 to 49, cited below as PP1993.
The statement split is PP1993 page 44 display 4, proved in section 4 on pages 45 to 46.
The plan follows the reread note of 2026-11-22, Part 2, leaves A1 to A10, which was
checked against the page images; there is no PP1993 copy in papers, so the note is the
source authority for page and display numbers.
Leaves A5, A6 and A8 are citation walls: Vaughan 1981 chapter 3 and Perelli Pintz
Saffari 1985 Invent. Math. 79, copy at papers/PPS1985-InventMath79.pdf.
The long Siegel Walfisz input of A8 is derived from the short interval A6 at Y = N.
The wiring result `major_energy_of_leaves` has exactly the statement of
`Decomp398a.major_energy` and is proved from the leaves with no sorry of its own.
Status: A1, A2, A3, A9 and the assembly A10 are proved; A4 and A7 are MEDIUM leaves
still carrying sorry; A5, A6 and A8 are HARD citation walls carrying sorry.
A2 is proved given A1, A4 is stated given A3, A7 given A6, and A8 given the long
Siegel Walfisz form, which is proved from A6.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMajor

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a

/-! ## Definitions of PP1993 page 43 -/

/-- PP1993 page 43, the exponent B equal to 3 over epsilon times 2A + 25. -/
noncomputable def bigB (ε A : ℝ) : ℝ := 3 / ε * (2 * A + 25)

/-- PP1993 page 43, the moduli q of the major arcs, 1 at most q at most L^B with L = log N. -/
noncomputable def majorQ (N ε A : ℝ) : Finset ℕ :=
  Icc 1 ⌊Real.log N ^ bigB ε A⌋₊

/-- PP1993 page 43, the reduced residues a with 1 at most a at most q and a coprime to q. -/
def redRes (q : ℕ) : Finset ℕ := (Icc 1 q).filter (fun a => a.Coprime q)

/-- PP1993 page 43, the half width L^{2B} over qY of the major arc I'_{q,a}. -/
noncomputable def arcWidth (N Y ε A : ℝ) (q : ℕ) : ℝ :=
  Real.log N ^ (2 * bigB ε A) / ((q : ℝ) * Y)

/-- PP1993 page 43, the major arc I'_{q,a}, centre a over q. -/
noncomputable def arcAt (N Y ε A : ℝ) (q a : ℕ) : Set ℝ :=
  {α | |α - (a : ℝ) / q| < arcWidth N Y ε A q}

/-- PP1993 page 45, the shifted arc xi'_q, the eta with modulus below L^{2B} over qY. -/
noncomputable def xiArc (N Y ε A : ℝ) (q : ℕ) : Set ℝ :=
  Set.Ioo (-arcWidth N Y ε A q) (arcWidth N Y ε A q)

/-- PP1993 page 43, T1 of eta, the sum of e of h eta over N - Y below h at most N. -/
noncomputable def firstT (N Y η : ℝ) : ℂ :=
  ∑ h ∈ kRange (N - Y) Y, phase ((h : ℝ) * η)

/-- PP1993 page 43, T2 of eta, the sum of e of j eta over j at most Y. -/
noncomputable def secondT (Y η : ℝ) : ℂ :=
  ∑ j ∈ kRange 0 Y, phase ((j : ℝ) * η)

/-- PP1993 page 43, R1 of eta q a, equal to S1 at a/q + eta minus mu q over phi q times T1. -/
noncomputable def firstR (N Y : ℝ) (q a : ℕ) (η : ℝ) : ℂ :=
  firstPoly N Y ((a : ℝ) / q + η) - ((μ q : ℂ) / (Nat.totient q : ℂ)) * firstT N Y η

/-- PP1993 page 43, R2 of eta q a, equal to S2 at a/q + eta minus mu q over phi q times T2. -/
noncomputable def secondR (Y : ℝ) (q a : ℕ) (η : ℝ) : ℂ :=
  secondPoly Y ((a : ℝ) / q + η) - ((μ q : ℂ) / (Nat.totient q : ℂ)) * secondT Y η

/-- PP1993 page 43, the Ramanujan sum c_q of n, the sum of e of an/q over reduced a. -/
noncomputable def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ redRes q, phase ((a : ℝ) * (n : ℝ) / q)

/-- PP1993 page 45, the tail of the Ramanujan series of the singular series at m,
the sum over q above X of mu^2 q over phi^2 q times c_q of -m. -/
noncomputable def ramanujanTail (m : ℕ) (X : ℝ) : ℂ :=
  ∑' q : ℕ, if X < (q : ℝ) then
    ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q (-(m : ℤ)) else 0

/-- PP1993 page 45 display 7, the main piece Sigma_1. -/
noncomputable def sigma1 (N Y ε A : ℝ) (m : ℕ) : ℂ :=
  ∑ q ∈ majorQ N ε A, ∑ a ∈ redRes q, phase (-(m : ℝ) * a / q) *
    (((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-(m : ℝ) * η))

/-- PP1993 page 45 display 7, the mixed piece Sigma_2. -/
noncomputable def sigma2 (N Y ε A : ℝ) (m : ℕ) : ℂ :=
  ∑ q ∈ majorQ N ε A, ∑ a ∈ redRes q, phase (-(m : ℝ) * a / q) *
    (((μ q : ℂ)) / (Nat.totient q : ℂ) *
      ∫ η in xiArc N Y ε A q, (firstT N Y η * secondR Y q a η +
        secondT Y η * firstR N Y q a η) * phase (-(m : ℝ) * η))

/-- PP1993 page 45 display 7, the error piece Sigma_3. -/
noncomputable def sigma3 (N Y ε A : ℝ) (m : ℕ) : ℂ :=
  ∑ q ∈ majorQ N ε A, ∑ a ∈ redRes q, phase (-(m : ℝ) * a / q) *
    ∫ η in xiArc N Y ε A q, firstR N Y q a η * secondR Y q a η * phase (-(m : ℝ) * η)

/-- PP1993 page 45, the principal character indicator delta_chi. -/
noncomputable def deltaChi {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  if χ = 1 then 1 else 0

/-! ## Statements of the leaves, as propositions consumed by the assembly A10 -/

/-- Statement of leaf A1, PP1993 page 43 definitions of I'_{q,a} and M. -/
def A1Stmt : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    (∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q, ∀ q' ∈ majorQ N ε A, ∀ a' ∈ redRes q',
        (q, a) ≠ (q', a') → Disjoint (arcAt N Y ε A q a) (arcAt N Y ε A q' a')) ∧
      (∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q, arcAt N Y ε A q a ⊆ arcBase Y ε) ∧
      majorArcs N Y ε A = ⋃ q ∈ majorQ N ε A, ⋃ a ∈ redRes q, arcAt N Y ε A q a

/-- Statement of leaf A2, PP1993 page 45 display 7. -/
def A2Stmt : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℝ, ∀ N Y : ℝ, ∀ m : ℕ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    arcCoeff N Y m (majorArcs N Y ε A) =
      sigma1 N Y ε A m + sigma2 N Y ε A m + sigma3 N Y ε A m

/-- Statement of leaf A3, PP1993 page 45, unnumbered display after display 7. -/
def A3Stmt : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ, ∀ q m : ℕ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → q ∈ majorQ N ε A →
    ‖(∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-(m : ℝ) * η)) -
        (ppM m N Y : ℂ)‖ ≤
      C * q * Y / Real.log N ^ (2 * bigB ε A)

/-- Statement of leaf A4, PP1993 page 45, two unnumbered displays. -/
def A4Stmt : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ, ∀ k : ℕ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2) →
    ‖sigma1 N Y ε A (2 * k) - ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ≤
      C * (Y * ‖ramanujanTail (2 * k) (Real.log N ^ bigB ε A)‖ +
        Y * Real.log N ^ (-bigB ε A))

/-- Statement of leaf A5, PP1993 page 45, last unnumbered display, giving display 8. -/
def A5Stmt : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖ramanujanTail (2 * k) (Real.log N ^ bigB ε A)‖ ^ 2 ≤
      C * Y ^ (1 / 3 + ε) * Real.log N ^ (-A)

/-- Statement of leaf A6, PP1993 page 45 display 6: short interval Siegel Walfisz from
PPS 1985, uniform in q at most L^D and every character chi mod q. -/
def ShortSW : Prop :=
  ∀ ε D C' : ℝ, 0 < ε → 0 < D → 0 < C' → ∃ K N0 : ℝ, ∀ N Y : ℝ, ∀ q : ℕ,
    ∀ χ : DirichletCharacter ℂ q,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ D →
    ‖(∑ n ∈ kRange (N - Y) Y, (Λ n : ℂ) * χ (n : ZMod q)) - deltaChi χ * (Y : ℂ)‖ ≤
      K * Y * Real.log N ^ (-C')

/-- The long Siegel Walfisz form used for S2 in leaf A8, the instance Y = N of A6. -/
def LongSW : Prop :=
  ∀ D C' : ℝ, 0 < D → 0 < C' → ∃ K x0 : ℝ, ∀ x : ℝ, ∀ q : ℕ,
    ∀ χ : DirichletCharacter ℂ q,
    x0 ≤ x → 1 ≤ q → (q : ℝ) ≤ Real.log x ^ D →
    ‖(∑ n ∈ kRange 0 x, (Λ n : ℂ) * χ (n : ZMod q)) - deltaChi χ * (x : ℂ)‖ ≤
      K * x * Real.log x ^ (-C')

/-- Statement of leaf A7, PP1993 page 46 display 12, for every C'. -/
def A7Stmt : Prop :=
  ∀ ε A C' : ℝ, 0 < ε → 0 < A → 0 < C' → ∃ C N0 : ℝ, ∀ N Y : ℝ, ∀ q a : ℕ, ∀ η : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → q ∈ majorQ N ε A → a ∈ redRes q →
    η ∈ xiArc N Y ε A q →
    ‖firstR N Y q a η‖ ≤ C * Y * Real.log N ^ (2 * bigB ε A - C')

/-- Statement of leaf A8, PP1993 page 46 display 11, for every C'. -/
def A8Stmt : Prop :=
  ∀ ε A C' : ℝ, 0 < ε → 0 < A → 0 < C' → ∃ C N0 : ℝ, ∀ N Y : ℝ, ∀ q a : ℕ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N → q ∈ majorQ N ε A → a ∈ redRes q →
    ∫ η in xiArc N Y ε A q, ‖secondR Y q a η‖ ^ 2 ≤ C * Y * Real.log N ^ (-C')

/-- Statement of leaf A9, PP1993 page 46 displays 9 and 10, Cauchy Schwarz, pointwise in m. -/
def A9Stmt : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ N0 : ℝ, ∀ N Y M1 M2 : ℝ, ∀ m : ℕ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    (∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
      ∫ η in xiArc N Y ε A q, ‖firstR N Y q a η‖ ^ 2 ≤ M1) →
    (∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
      ∫ η in xiArc N Y ε A q, ‖secondR Y q a η‖ ^ 2 ≤ M2) →
    ‖sigma2 N Y ε A m‖ ≤
        Real.sqrt (Y + 1) * Real.log N ^ bigB ε A * (Real.sqrt M1 + Real.sqrt M2) ∧
      ‖sigma3 N Y ε A m‖ ≤
        Real.log N ^ (2 * bigB ε A) * (Real.sqrt M1 * Real.sqrt M2)

/-! ## The leaves -/

/-- For any power r of log and any positive exponent s, log x ^ r is at most c x^s eventually. -/
theorem log_rpow_le_eventually (r : ℝ) {s : ℝ} (hs : 0 < s) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ r ≤ c * x ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop r hs).bound hc
  filter_upwards [h, Filter.eventually_ge_atTop 1] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  exact hx

/-- Reduced fractions with equal cross products are equal. -/
theorem reduced_eq {q a q' a' : ℕ} (hq : 0 < q) (ha : a.Coprime q) (ha' : a'.Coprime q')
    (h : a * q' = a' * q) : q = q' ∧ a = a' := by
  have h1 : q ∣ q' := by
    have : q ∣ a * q' := ⟨a', by rw [h]; ring⟩
    exact (Nat.Coprime.symm ha).dvd_of_dvd_mul_left this
  have h2 : q' ∣ q := by
    have : q' ∣ a' * q := ⟨a, by rw [← h]; ring⟩
    exact (Nat.Coprime.symm ha').dvd_of_dvd_mul_left this
  have hqq := Nat.dvd_antisymm h1 h2
  subst hqq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq h⟩

/-- LEAF: PP1993 p. 43 definitions of I'_{q,a} and M, the major arcs with q at most L^B
and reduced a are pairwise disjoint, lie in the base interval from 1/Q to 1 + 1/Q, and
their union is majorArcs, for N at least N0. Class MEDIUM. PROVED. -/
theorem a1_arcs_disjoint : A1Stmt := by
  intro ε A hε hA
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  set B := bigB ε A with hBdef
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (((log_rpow_le_eventually (3 * B) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 / 4 by norm_num)).and
    (log_rpow_le_eventually (2 * B) (show (0 : ℝ) < 7 / 36 by norm_num)
      (show (0 : ℝ) < 1 / 16 by norm_num))).and
    ((log_rpow_le_eventually (4 * B) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)).and (Filter.eventually_ge_atTop (Real.exp 1))))
  refine ⟨N0, ?_⟩
  intro N Y hN hlow hYN
  obtain ⟨⟨c3, c2⟩, c4, hNe⟩ := hN0 N hN
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hNpos : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hL0 : 0 ≤ Real.log N := by linarith
  set L := Real.log N with hLdef
  set X := L ^ B with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hL1 hB.le
  have hXn : ∀ n : ℕ, X ^ n = L ^ ((n : ℝ) * B) := by
    intro n
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
    ring_nf
  have hW : L ^ (2 * B) = X ^ 2 := by rw [hXn]; norm_num
  rw [show (3 : ℝ) * B = ((3 : ℕ) : ℝ) * B by norm_num, ← hXn] at c3
  rw [show (2 : ℝ) * B = ((2 : ℕ) : ℝ) * B by norm_num, ← hXn] at c2
  rw [show (4 : ℝ) * B = ((4 : ℕ) : ℝ) * B by norm_num, ← hXn] at c4
  set P := N ^ ((7 : ℝ) / 12) with hPdef
  have hPY : P ≤ Y := (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hlow
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 (by norm_num)
  have hY1 : 1 ≤ Y := hP1.trans hPY
  have hY0 : 0 < Y := by linarith
  have hε5 : ε ≤ 5 / 12 := by
    by_contra hc
    rw [not_le] at hc
    have hN1' : 1 < N := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
    have := Real.rpow_lt_rpow_of_exponent_lt hN1' (show (1 : ℝ) < 7 / 12 + ε by linarith)
    rw [Real.rpow_one] at this
    linarith
  set H := Y ^ (1 / 3 + ε) with hHdef
  have hH0 : 0 ≤ H := Real.rpow_nonneg hY0.le _
  have hHY : H ≤ Y := by
    calc H ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
      _ = Y := Real.rpow_one Y
  have hP3 : N ^ ((7 : ℝ) / 36) ≤ H := by
    calc N ^ ((7 : ℝ) / 36) = P ^ ((1 : ℝ) / 3) := by
          rw [hPdef, ← Real.rpow_mul hNpos.le]; norm_num
      _ ≤ Y ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by linarith) hPY (by norm_num)
      _ ≤ H := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  -- the width bounds
  have hX3 : 4 * X ^ 3 ≤ Y := by linarith
  have hWY : X ^ 2 ≤ Y / 4 := by nlinarith [pow_le_pow_right₀ hX1 (show 2 ≤ 3 by norm_num)]
  have hsqH : 4 * X ≤ Real.sqrt H := by
    rw [Real.le_sqrt (by linarith) hH0]
    nlinarith
  have hsqY : X ^ 2 ≤ Real.sqrt Y := by
    rw [Real.le_sqrt (by positivity) hY0.le]
    nlinarith
  have hQ : 1 / (Real.sqrt H / 2) = 2 / Real.sqrt H := by
    field_simp
  have hsqHpos : 0 < Real.sqrt H := by linarith
  have hupper : X ^ 2 / Y ≤ 2 / Real.sqrt H := by
    rw [div_le_div_iff₀ hY0 hsqHpos]
    have h1 : Real.sqrt H ≤ Real.sqrt Y := Real.sqrt_le_sqrt hHY
    have h2 : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
    calc X ^ 2 * Real.sqrt H ≤ Real.sqrt Y * Real.sqrt Y :=
          mul_le_mul hsqY h1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ 2 * Y := by linarith
  have hwidth : ∀ q : ℕ, 1 ≤ q → arcWidth N Y ε A q = X ^ 2 / q / Y := by
    intro q hq
    unfold arcWidth
    rw [← hBdef, hW, div_div, mul_comm]
  have hmemQ : ∀ q : ℕ, q ∈ majorQ N ε A ↔ 1 ≤ q ∧ (q : ℝ) ≤ X := by
    intro q
    unfold majorQ
    rw [Finset.mem_Icc, Nat.le_floor_iff (by linarith)]
  have hsub : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q, arcAt N Y ε A q a ⊆ arcBase Y ε := by
    intro q hq a ha α hα
    obtain ⟨hq1, hqX⟩ := (hmemQ q).mp hq
    have ha' := Finset.mem_filter.mp ha
    obtain ⟨ha1, haq⟩ := Finset.mem_Icc.mp ha'.1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    simp only [arcAt, Set.mem_ofPred_eq, hwidth q hq1] at hα
    rw [abs_sub_lt_iff] at hα
    unfold arcBase
    rw [← hHdef, hQ, Set.mem_Icc]
    have hw0 : X ^ 2 / q / Y ≤ X ^ 2 / Y := by
      rw [div_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact le_mul_of_one_le_left hY0.le (by exact_mod_cast hq1)
    have haq' : (a : ℝ) / q ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast haq
    have ha1' : 1 / (q : ℝ) ≤ (a : ℝ) / q := by
      apply div_le_div_of_nonneg_right _ hqpos.le; exact_mod_cast ha1
    constructor
    · have hw1 : X ^ 2 / q / Y ≤ 1 / (2 * q) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hq2 : 1 / (2 * X) ≤ 1 / (2 * q) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hX2 : 2 / Real.sqrt H ≤ 1 / (2 * X) := by
        rw [div_le_div_iff₀ hsqHpos (by positivity)]
        linarith
      have : 1 / (q : ℝ) = 1 / (2 * q) + 1 / (2 * q) := by field_simp; ring
      linarith
    · linarith
  refine ⟨?_, hsub, ?_⟩
  · intro q hq a ha q' hq' a' ha' hne
    obtain ⟨hq1, hqX⟩ := (hmemQ q).mp hq
    obtain ⟨hq1', hqX'⟩ := (hmemQ q').mp hq'
    have hac := (Finset.mem_filter.mp ha).2
    have hac' := (Finset.mem_filter.mp ha').2
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hqpos' : (0 : ℝ) < q' := by exact_mod_cast hq1'
    rw [Set.disjoint_left]
    intro α h1 h2
    simp only [arcAt, Set.mem_ofPred_eq, hwidth q hq1, hwidth q' hq1'] at h1 h2
    set d : ℤ := (a : ℤ) * q' - (a' : ℤ) * q with hd
    have hd0 : d ≠ 0 := by
      intro h0
      apply hne
      have : a * q' = a' * q := by
        have : (a : ℤ) * q' = (a' : ℤ) * q := by linarith
        exact_mod_cast this
      obtain ⟨e1, e2⟩ := reduced_eq hq1 hac hac' this
      rw [e1, e2]
    have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by
      have := Int.one_le_abs hd0
      exact_mod_cast this
    have hdiff : (a : ℝ) / q - (a' : ℝ) / q' = (d : ℝ) / (q * q') := by
      rw [hd]; push_cast; field_simp
    have htri : |(a : ℝ) / q - (a' : ℝ) / q'| < X ^ 2 / q / Y + X ^ 2 / q' / Y := by
      rw [abs_sub_lt_iff] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')] at htri
    have hD : (0 : ℝ) < q * q' := by positivity
    have key : |(d : ℝ)| * Y < X ^ 2 * (q' + q) := by
      have e : (X ^ 2 / q / Y + X ^ 2 / q' / Y) = X ^ 2 * (q' + q) / (q * q' * Y) := by
        field_simp
      rw [e, div_lt_div_iff₀ hD (by positivity)] at htri
      have h' : |(d : ℝ)| * Y * (q * q') < X ^ 2 * (q' + q) * (q * q') := by
        calc |(d : ℝ)| * Y * (q * q') = |(d : ℝ)| * (q * q' * Y) := by ring
          _ < X ^ 2 * (q' + q) * (q * q') := htri
      exact lt_of_mul_lt_mul_right h' hD.le
    have h3 : X ^ 2 * (q' + q) ≤ X ^ 2 * (X + X) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : X ^ 2 * (X + X) = 2 * X ^ 3 := by ring
    have h5 : Y ≤ |(d : ℝ)| * Y := le_mul_of_one_le_left hY0.le hd1
    linarith
  · unfold majorArcs
    ext α
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨-, q, a, hq1, hqX, ha1, haq, hac, hα⟩
      refine ⟨q, (hmemQ q).mpr ⟨hq1, by rw [hXdef, hLdef, hBdef]; exact hqX⟩, a,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haq⟩, hac⟩, ?_⟩
      simp only [arcAt, arcWidth, Set.mem_ofPred_eq]
      exact hα
    · rintro ⟨q, hq, a, ha, hα⟩
      refine ⟨hsub q hq a ha hα, ?_⟩
      obtain ⟨hq1, hqX⟩ := (hmemQ q).mp hq
      have ha' := Finset.mem_filter.mp ha
      obtain ⟨ha1, haq⟩ := Finset.mem_Icc.mp ha'.1
      refine ⟨q, a, hq1, by rw [hXdef, hLdef, hBdef] at hqX; exact hqX, ha1, haq, ha'.2, ?_⟩
      simp only [arcAt, arcWidth, Set.mem_ofPred_eq] at hα
      exact hα

/-- LEAF: PP1993 p. 45 display 7, given A1 the major arc integral of S1 S2 e of -m alpha
splits into Sigma_1 + Sigma_2 + Sigma_3 after writing S_i at a/q + eta as mu over phi
times T_i plus R_i. Class MEDIUM. PROVED. -/
theorem a2_split (h1 : A1Stmt) : A2Stmt := by
  intro ε A hε hA
  obtain ⟨N0, hN0⟩ := h1 ε A hε hA
  refine ⟨max N0 1, ?_⟩
  intro N Y m hN hlow hYN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hY0 : 0 ≤ Y := (Real.rpow_nonneg (by linarith) _).trans hlow
  obtain ⟨hdisj, -, hU⟩ := hN0 N Y ((le_max_left _ _).trans hN) hlow hYN
  set F : ℝ → ℂ := fun α => firstPoly N Y α * secondPoly Y α * phase (-(m : ℝ) * α) with hF
  have hc : Continuous F := by
    simp only [hF]
    unfold firstPoly secondPoly phase LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hU' : (⋃ q ∈ majorQ N ε A, ⋃ a ∈ redRes q, arcAt N Y ε A q a) =
      ⋃ p ∈ (majorQ N ε A).sigma redRes, arcAt N Y ε A p.1 p.2 := by
    ext α
    simp only [Set.mem_iUnion, Finset.mem_sigma, exists_prop, Sigma.exists]
    constructor
    · rintro ⟨q, hq, a, ha, h⟩
      exact ⟨q, a, ⟨hq, ha⟩, h⟩
    · rintro ⟨q, a, ⟨hq, ha⟩, h⟩
      exact ⟨q, hq, a, ha, h⟩
  have hIoo : ∀ q a : ℕ, arcAt N Y ε A q a = Set.Ioo ((a : ℝ) / q - arcWidth N Y ε A q)
      ((a : ℝ) / q + arcWidth N Y ε A q) := by
    intro q a
    ext α
    simp only [arcAt, Set.mem_ofPred_eq, Set.mem_Ioo, abs_sub_lt_iff]
    constructor
    · intro h
      constructor <;> linarith [h.1, h.2]
    · intro h
      constructor <;> linarith [h.1, h.2]
  have hw : ∀ q : ℕ, 0 ≤ arcWidth N Y ε A q := fun q =>
    div_nonneg (Real.rpow_nonneg (Real.log_nonneg hN1) _) (mul_nonneg q.cast_nonneg hY0)
  have hshift : ∀ q a : ℕ, (∫ α in arcAt N Y ε A q a, F α) =
      ∫ η in xiArc N Y ε A q, F ((a : ℝ) / q + η) := by
    intro q a
    rw [hIoo, xiArc, ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [hw q]),
      ← intervalIntegral.integral_of_le (by linarith [hw q]),
      intervalIntegral.integral_comp_add_left, ← sub_eq_add_neg]
  have hint : ∀ q : ℕ, ∀ f : ℝ → ℂ, Continuous f → IntegrableOn f (xiArc N Y ε A q) :=
    fun q f hf => (hf.integrableOn_Icc (a := -arcWidth N Y ε A q)
      (b := arcWidth N Y ε A q)).mono_set Set.Ioo_subset_Icc_self
  unfold arcCoeff
  rw [hU, hU', integral_biUnion_finset _ (fun p _ => by rw [hIoo]; exact measurableSet_Ioo)
    (fun p hp p' hp' hne => by
      have h1' := Finset.mem_sigma.mp (Finset.mem_coe.mp hp)
      have h2' := Finset.mem_sigma.mp (Finset.mem_coe.mp hp')
      exact hdisj p.1 h1'.1 p.2 h1'.2 p'.1 h2'.1 p'.2 h2'.2 (by
        intro h; exact hne (Sigma.ext (congrArg Prod.fst h)
          (heq_of_eq (congrArg Prod.snd h)))))
    (fun p _ => by rw [hIoo]; exact (hc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self),
    Finset.sum_sigma]
  unfold sigma1 sigma2 sigma3
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [hshift]
  have hT1 : Continuous (firstT N Y) := by
    unfold firstT phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hT2 : Continuous (secondT Y) := by
    unfold secondT phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hR1 : Continuous (firstR N Y q a) := by
    unfold firstR firstT firstPoly phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hR2 : Continuous (secondR Y q a) := by
    unfold secondR secondT secondPoly phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hP : Continuous (fun η : ℝ => phase (-(m : ℝ) * η)) := by
    unfold phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  set c : ℂ := phase (-(m : ℝ) * a / q) with hcdef
  have hpt : ∀ η : ℝ, F ((a : ℝ) / q + η) =
      c * (((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
        (firstT N Y η * secondT Y η * phase (-(m : ℝ) * η))) +
      c * (((μ q : ℂ)) / (Nat.totient q : ℂ) *
        ((firstT N Y η * secondR Y q a η + secondT Y η * firstR N Y q a η) *
          phase (-(m : ℝ) * η))) +
      c * (firstR N Y q a η * secondR Y q a η * phase (-(m : ℝ) * η)) := by
    intro η
    have hph : phase (-(m : ℝ) * ((a : ℝ) / q + η)) = c * phase (-(m : ℝ) * η) := by
      rw [hcdef, show -(m : ℝ) * ((a : ℝ) / q + η) = -(m : ℝ) * a / q + -(m : ℝ) * η by ring]
      exact LeanLab.PNTPort.LargeSieve.e_add _ _
    simp only [hF, hph, firstR, secondR]
    ring
  simp_rw [hpt]
  have i1 := hint q (fun η => c * (((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
        (firstT N Y η * secondT Y η * phase (-(m : ℝ) * η)))) (by fun_prop)
  have i2 := hint q (fun η => c * (((μ q : ℂ)) / (Nat.totient q : ℂ) *
        ((firstT N Y η * secondR Y q a η + secondT Y η * firstR N Y q a η) *
          phase (-(m : ℝ) * η)))) (by fun_prop)
  have i3 := hint q (fun η => c * (firstR N Y q a η * secondR Y q a η *
    phase (-(m : ℝ) * η))) (by fun_prop)
  rw [integral_add ?_ i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]
  exact i1.add i2

/-- The additive count with unit weights is M star of page 43. -/
theorem ones_convolution (N Y : ℝ) (hYN : Y ≤ N) (m : ℕ) :
    (∑ h ∈ kRange (N - Y) Y, ∑ j ∈ kRange 0 Y, if h + j = m then (1 : ℂ) else 0) =
      (ppM m N Y : ℂ) := by
  have hval : ∀ h ∈ kRange (N - Y) Y,
      (∑ j ∈ kRange 0 Y, if h + j = m then (1 : ℂ) else 0) =
      if h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y then (1 : ℂ) else 0 := by
    intro h hh
    by_cases hp : h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)]
      have hj : m - h ∈ kRange 0 Y := by
        rw [Fourier398.window_mem]
        refine ⟨by exact_mod_cast (show 0 < m - h by omega), by simpa using hp.2⟩
      rw [sum_eq_single (m - h)]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : h + (m - h) = m))]
      · intro j hj hne
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ (h + j = m)))]
      · exact fun hn => False.elim (hn hj)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)]
      apply sum_eq_zero
      intro j hj
      rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]
      intro he
      have hj' := (Fourier398.window_mem _ _ _).mp hj
      have hjpos : 0 < j := by exact_mod_cast hj'.1
      have hjm : j = m - h := by omega
      exact hp ⟨by omega, by simpa [hjm] using hj'.2⟩
  have hset : (kRange (N - Y) Y).filter (fun h => h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y) =
      (Ioo 0 m).filter (ppCond m N Y) := by
    ext h
    simp only [mem_filter, Fourier398.window_mem, mem_Ioo, ppCond]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hm, hY⟩
      have hp : (0 : ℝ) < h := by linarith
      exact ⟨⟨by exact_mod_cast hp, hm⟩, hlo, by linarith, hY⟩
    · rintro ⟨⟨h0, hm⟩, hlo, hhi, hY⟩
      exact ⟨⟨hlo, by linarith⟩, hm, hY⟩
  rw [sum_congr rfl hval, Finset.sum_boole, hset, ppM]
  push_cast
  rfl

/-- On the interval from -1/2 to 1/2 the distance to the nearest integer is the modulus. -/
theorem abs_le_dist0 {η : ℝ} (h : |η| ≤ 1 / 2) : |η| ≤ LeanLab.PNTPort.LargeSieve.dist0 η := by
  unfold LeanLab.PNTPort.LargeSieve.dist0
  by_cases hn : round η = 0
  · rw [hn, Int.cast_zero, sub_zero]
  · have h1 : (1 : ℝ) ≤ |((round η : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have h2 := abs_sub_abs_le_abs_sub ((round η : ℤ) : ℝ) η
    rw [abs_sub_comm] at h2
    linarith

/-- The window polynomial is a shifted geometric sum, so it is at most 1/(2|eta|). -/
theorem window_bound (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) {η : ℝ} (h0 : 0 < |η|)
    (h1 : |η| ≤ 1 / 2) :
    ‖∑ k ∈ kRange X R, phase ((k : ℝ) * η)‖ ≤ 1 / (2 * |η|) := by
  set k0 := ⌊X⌋₊ + 1
  set n := ⌊X + R⌋₊ + 1 - k0
  have hmap : kRange X R = (range n).map ⟨fun j => j + k0, add_left_injective k0⟩ := by
    ext k
    rw [Fourier398.window_mem, Finset.mem_map]
    simp only [Function.Embedding.coeFn_mk, Finset.mem_range]
    rw [← Nat.floor_lt hX, ← Nat.le_floor_iff (by linarith)]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨k - k0, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hmap, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have he : ∀ j : ℕ, phase (((j + k0 : ℕ) : ℝ) * η) =
      phase ((k0 : ℝ) * η) * LeanLab.PNTPort.LargeSieve.e (j * η) := by
    intro j
    rw [show (((j + k0 : ℕ) : ℝ) * η) = (k0 : ℝ) * η + j * η by push_cast; ring]
    exact LeanLab.PNTPort.LargeSieve.e_add _ _
  simp_rw [he]
  have hn : ‖phase ((k0 : ℝ) * η)‖ = 1 := LeanLab.PNTPort.LargeSieve.norm_e _
  rw [← Finset.mul_sum, norm_mul, hn, one_mul]
  have hd := abs_le_dist0 h1
  refine (LeanLab.PNTPort.LargeSieve.norm_geom_le n (by linarith)).trans ?_
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The integral of 1/(4 eta^2) over the complement of the arc of half width w. -/
theorem tail_integral {w : ℝ} (hw : 0 < w) (hw2 : w ≤ 1 / 2) :
    ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w, 1 / (4 * η ^ 2) ≤ 1 / (2 * w) := by
  have hS : Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w =
      Set.Icc (-(1 / 2 : ℝ)) (-w) ∪ Set.Icc w (1 / 2) := by
    ext η
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_union, not_and_or, not_lt]
    constructor
    · rintro ⟨⟨a, b⟩, c | c⟩
      · exact Or.inl ⟨a, c⟩
      · exact Or.inr ⟨c, b⟩
    · rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact ⟨⟨a, by linarith⟩, Or.inl b⟩
      · exact ⟨⟨by linarith, b⟩, Or.inr a⟩
  have hF : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun y : ℝ => -(1 / (4 * y))) (1 / (4 * x ^ 2)) x := by
    intro x hx
    have := ((hasDerivAt_id x).const_mul 4).inv (by simpa using hx)
    convert this.neg using 1
    · ext y; simp [one_div]
    · simp only [id]; field_simp
  have hcont : ∀ a b : ℝ, 0 < a ∨ b < 0 → a ≤ b →
      ContinuousOn (fun η : ℝ => 1 / (4 * η ^ 2)) (Set.uIcc a b) := by
    intro a b hab hle
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have : x ≠ 0 := by rcases hab with h | h <;> intro h0 <;> rw [h0] at hx <;>
      linarith [hx.1, hx.2]
    positivity
  have hpiece : ∀ a b : ℝ, 0 < a ∨ b < 0 → a ≤ b →
      ∫ η in Set.Icc a b, 1 / (4 * η ^ 2) = -(1 / (4 * b)) - -(1 / (4 * a)) := by
    intro a b hab hle
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hle] at hx
      apply hF
      rcases hab with h | h <;> intro h0 <;> rw [h0] at hx <;> linarith [hx.1, hx.2]
    · exact (hcont a b hab hle).intervalIntegrable
  have hint : ∀ a b : ℝ, 0 < a ∨ b < 0 → a ≤ b →
      IntegrableOn (fun η : ℝ => 1 / (4 * η ^ 2)) (Set.Icc a b) := by
    intro a b hab hle
    have := (hcont a b hab hle)
    rw [Set.uIcc_of_le hle] at this
    exact this.integrableOn_Icc
  rw [hS, setIntegral_union _ measurableSet_Icc (hint _ _ (Or.inr (by linarith)) (by linarith))
    (hint _ _ (Or.inl hw) hw2), hpiece _ _ (Or.inr (by linarith)) (by linarith),
    hpiece _ _ (Or.inl hw) hw2]
  · have : -(1 / (4 * -w)) - -(1 / (4 * -(1 / 2 : ℝ))) + (-(1 / (4 * (1 / 2 : ℝ))) - -(1 / (4 * w)))
        = 1 / (2 * w) - 1 := by field_simp; ring
    linarith
  · rw [Set.disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1]

/-- LEAF: PP1993 p. 45, unnumbered display after display 7, the integral over xi'_q of
T1 T2 e of -m eta equals M* at m plus O of qY over L^{2B}, uniformly in m and q at most
L^B. Class MEDIUM. PROVED. -/
theorem a3_T_integral : A3Stmt := by
  intro ε A hε hA
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    ((log_rpow_le_eventually (2 * bigB ε A) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)).and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨1, N0, ?_⟩
  intro N Y q m hN hlow hYN hq
  obtain ⟨hw2, hNe⟩ := hN0 N hN
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hNpos : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hP : N ^ ((7 : ℝ) / 12) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hlow
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hN1 (by norm_num)).trans hP
  have hY0 : 0 < Y := by linarith
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  set w := arcWidth N Y ε A q with hwdef
  have hWpos : 0 < Real.log N ^ (2 * bigB ε A) := Real.rpow_pos_of_pos (by linarith) _
  have hw0 : 0 < w := by rw [hwdef]; unfold arcWidth; positivity
  have hw : w ≤ 1 / 2 := by
    rw [hwdef]; unfold arcWidth
    have hqY : Y ≤ (q : ℝ) * Y := le_mul_of_one_le_left hY0.le (by exact_mod_cast hq1)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set G : ℝ → ℂ := fun η => firstT N Y η * secondT Y η * phase (-(m : ℝ) * η) with hG
  have hGc : Continuous G := by
    simp only [hG]; unfold firstT secondT phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hsub : xiArc N Y ε A q ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro η hη
    exact ⟨by linarith [hη.1], by linarith [hη.2]⟩
  have hfull : ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), G η = (ppM m N Y : ℂ) := by
    have h := Fourier398.finite_convolution (kRange (N - Y) Y) (kRange 0 Y)
      (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) m (-(1 / 2))
    rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num] at h
    simp only [one_mul, mul_one] at h
    rw [← ones_convolution N Y hYN m, ← h]
    rfl
  have hGi' : IntegrableOn G (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) volume := hGc.integrableOn_Icc
  have hsd := setIntegral_sdiff (measurableSet_Ioo (a := -w) (b := w)) hGi' hsub
  have hdiff : (∫ η in xiArc N Y ε A q, G η) - (ppM m N Y : ℂ) =
      -∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w, G η := by
    have hx : xiArc N Y ε A q = Set.Ioo (-w) w := rfl
    rw [← hfull, hsd, hx]
    ring
  have hpt : ∀ η ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w,
      ‖G η‖ ≤ 1 / (4 * η ^ 2) := by
    intro η hη
    have habs1 : |η| ≤ 1 / 2 := abs_le.mpr ⟨hη.1.1, hη.1.2⟩
    have habs0 : w ≤ |η| := by
      by_contra hc
      rw [not_le, abs_lt] at hc
      exact hη.2 hc
    have hpos : 0 < |η| := by linarith
    have b1 := window_bound (N - Y) Y (by linarith) hY0.le hpos habs1
    have b2 := window_bound 0 Y le_rfl hY0.le hpos habs1
    simp only [hG]
    have hn : ‖phase (-(m : ℝ) * η)‖ = 1 := LeanLab.PNTPort.LargeSieve.norm_e _
    rw [norm_mul, norm_mul, hn, mul_one]
    calc ‖firstT N Y η‖ * ‖secondT Y η‖ ≤ 1 / (2 * |η|) * (1 / (2 * |η|)) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ = 1 / (4 * η ^ 2) := by
          rw [show η ^ 2 = |η| ^ 2 from (sq_abs η).symm]; field_simp; ring
  have hScomp : IsCompact (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w) :=
    isCompact_Icc.diff isOpen_Ioo
  have hint2 : IntegrableOn (fun η : ℝ => 1 / (4 * η ^ 2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) \ Set.Ioo (-w) w) := by
    apply ContinuousOn.integrableOn_compact hScomp
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    have : w ≤ |x| := by
      by_contra hc
      rw [not_le, abs_lt] at hc
      exact hx.2 hc
    have : x ≠ 0 := by intro h0; rw [h0, abs_zero] at this; linarith
    positivity
  rw [hdiff, norm_neg]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hGi : IntegrableOn (fun η => ‖G η‖) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) volume :=
    hGc.norm.integrableOn_Icc
  refine (setIntegral_mono_on (hGi.mono_set Set.sdiff_subset) hint2
    (measurableSet_Icc.diff measurableSet_Ioo) hpt).trans ?_
  refine (tail_integral hw0 hw).trans ?_
  rw [hwdef]
  unfold arcWidth
  rw [one_mul]
  have : 1 / (2 * (Real.log N ^ (2 * bigB ε A) / (q * Y))) =
      q * Y / (2 * Real.log N ^ (2 * bigB ε A)) := by field_simp
  rw [this]
  apply div_le_div_of_nonneg_left (by positivity) hWpos
  linarith

/-- The trivial bound |c_q(n)| at most phi q for the Ramanujan sum. -/
theorem ramanujanSum_norm_le (q : ℕ) (n : ℤ) :
    ‖ramanujanSum q n‖ ≤ (Nat.totient q : ℝ) := by
  have hcard : (redRes q).card = Nat.totient q := by
    rw [← Nat.filter_coprime_Ico_eq_totient q 1]
    unfold redRes
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Nat.coprime_comm]
    omega
  unfold ramanujanSum
  refine (norm_sum_le _ _).trans ?_
  simp only [phase, LeanLab.PNTPort.LargeSieve.norm_e, sum_const, hcard, nsmul_eq_mul,
    mul_one, le_refl]

/-- PP1993 p. 45: the sum over reduced a of e of -m a/q in Sigma_1 is the Ramanujan sum. -/
theorem sigma1_regroup (N Y ε A : ℝ) (m : ℕ) :
    sigma1 N Y ε A m = ∑ q ∈ majorQ N ε A, ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ramanujanSum q (-(m : ℤ)) *
      ∫ η in xiArc N Y ε A q, firstT N Y η * secondT Y η * phase (-(m : ℝ) * η) := by
  unfold sigma1 ramanujanSum
  refine sum_congr rfl fun q _ => ?_
  rw [show ∀ x y z : ℂ, x * y * z = y * (x * z) from fun x y z => by ring, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  congr 2
  push_cast
  ring

/-- The weight of q in Sigma_1 has norm at most 1 over phi q. -/
theorem weight_norm_le {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ‖((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 * ramanujanSum q n‖ ≤
      1 / (Nat.totient q : ℝ) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hμ : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_intCast, Complex.norm_natCast]
  have h2 : |(μ q : ℝ)| ^ 2 ≤ 1 := by
    have := abs_nonneg (μ q : ℝ); nlinarith
  calc |(μ q : ℝ)| ^ 2 / (Nat.totient q : ℝ) ^ 2 * ‖ramanujanSum q n‖
      ≤ 1 / (Nat.totient q : ℝ) ^ 2 * (Nat.totient q : ℝ) := by
        apply mul_le_mul (div_le_div_of_nonneg_right h2 (by positivity))
          (ramanujanSum_norm_le q n) (norm_nonneg _) (by positivity)
    _ = 1 / (Nat.totient q : ℝ) := by field_simp

/-- LEAF: PP1993 p. 45, two unnumbered displays, given A3 the piece Sigma_1 equals
M* at 2k times the singular series plus O of Y times the Ramanujan tail over q above L^B
plus O of Y L^{-B}; this uses the singular series of p. 41 as the full Ramanujan series of
mu^2 over phi^2 times c_q of -2k, the Euler product algebra of U1457SingSeries
local_factor, euler_expand and truncS_expand. Class MEDIUM. -/
theorem a4_sigma1 (h3 : A3Stmt) : A4Stmt := by
  intro ε A hε hA
  obtain ⟨C, N0, hC⟩ := h3 ε A hε hA
  obtain ⟨c, hc0, hc⟩ := Split398aMajorA4.sum_div_totient_le
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  refine ⟨2 + max C 0 * c, max N0 3, ?_⟩
  intro N Y k hN hlow hYN hk
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hY1 : 1 ≤ Y := (Real.one_le_rpow (by linarith) (by positivity)).trans hlow
  have hk1 : 1 ≤ k := by
    unfold kRange at hk
    rw [Finset.mem_filter] at hk
    have h1 : (0 : ℝ) < k := by linarith [hk.2.1]
    exact_mod_cast h1
  set L := Real.log N with hLdef
  set X := L ^ bigB ε A with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos (by linarith) _
  set f : ℕ → ℂ := fun q => ((μ q : ℂ)) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ramanujanSum q (-((2 * k : ℕ) : ℤ)) with hf
  set I : ℕ → ℂ := fun q => ∫ η in xiArc N Y ε A q,
      firstT N Y η * secondT Y η * phase (-((2 * k : ℕ) : ℝ) * η) with hI
  set P : ℂ := ((LeanLab.Halupczok2012.ppM (2 * k) N Y : ℝ) : ℂ) with hP
  have hS : HasSum f ((S (2 * k) : ℝ) : ℂ) := Split398aMajorA4.singular_ramanujan k hk1
  have hf0 : f 0 = 0 := by simp [hf]
  -- the tail
  have hmem : ∀ q : ℕ, 1 ≤ q → (q ∈ majorQ N ε A ↔ ¬ X < q) := by
    intro q hq
    unfold majorQ
    rw [Finset.mem_Icc, not_lt, ← Nat.le_floor_iff hX0.le]
    simp only [hq, true_and]
    rfl
  have hg : HasSum (fun q => if q ∈ majorQ N ε A then f q else 0)
      (∑ q ∈ majorQ N ε A, f q) := by
    have h0 : HasSum (fun q => if q ∈ majorQ N ε A then f q else 0)
        (∑ q ∈ majorQ N ε A, (if q ∈ majorQ N ε A then f q else 0)) :=
      hasSum_sum_of_ne_finset_zero (by intro q hq; simp [hq])
    rwa [Finset.sum_congr rfl (g := f) (fun q hq => by simp [hq])] at h0
  have htail : ramanujanTail (2 * k) X = (S (2 * k) : ℂ) - ∑ q ∈ majorQ N ε A, f q := by
    unfold ramanujanTail
    apply HasSum.tsum_eq
    convert hS.sub hg using 1
    funext q
    rcases Nat.eq_zero_or_pos q with h0 | hq
    · subst h0; simp [hf0]
    · by_cases hx : X < (q : ℝ)
      · have : q ∉ majorQ N ε A := fun h => (hmem q hq).mp h hx
        simp [hx, this, hf]
      · have : q ∈ majorQ N ε A := (hmem q hq).mpr hx
        simp [hx, this, hf]
  have hreg := sigma1_regroup N Y ε A (2 * k)
  have hdecomp : sigma1 N Y ε A (2 * k) - ((S (2 * k) * LeanLab.Halupczok2012.ppM (2 * k) N Y : ℝ) : ℂ)
      = ∑ q ∈ majorQ N ε A, f q * (I q - P) - ramanujanTail (2 * k) X * P := by
    rw [hreg, htail]
    simp only [hf, hI, hP, mul_sub, sum_sub_distrib, Complex.ofReal_mul, ← sum_mul]
    ring
  -- bounds
  set C' := max C 0 with hC'
  have hW : 0 < L ^ (2 * bigB ε A) := Real.rpow_pos_of_pos (by linarith) _
  have hterm : ∀ q ∈ majorQ N ε A, ‖f q * (I q - P)‖ ≤
      C' * Y / L ^ (2 * bigB ε A) * ((q : ℝ) / (Nat.totient q : ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
    have h1 := weight_norm_le hq1 (-((2 * k : ℕ) : ℤ))
    have h2 := hC N Y q (2 * k) hN0 hlow hYN hq
    have h2' : ‖I q - P‖ ≤ C' * q * Y / L ^ (2 * bigB ε A) := by
      refine h2.trans ?_
      apply div_le_div_of_nonneg_right _ hW.le
      have : (0 : ℝ) ≤ q * Y := by positivity
      nlinarith [le_max_left C 0]
    rw [norm_mul]
    calc ‖f q‖ * ‖I q - P‖ ≤ 1 / (Nat.totient q : ℝ) * (C' * q * Y / L ^ (2 * bigB ε A)) :=
          mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hsum := hc ⌊X⌋₊
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpow : L ^ (2 * bigB ε A) = X * X := by
    rw [hXdef, ← Real.rpow_add (by linarith)]; ring_nf
  have hneg : L ^ (-bigB ε A) = 1 / X := by
    rw [Real.rpow_neg (by linarith), hXdef, one_div]
  have hfirst : ‖∑ q ∈ majorQ N ε A, f q * (I q - P)‖ ≤ C' * c * (Y * L ^ (-bigB ε A)) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← mul_sum]
    calc C' * Y / L ^ (2 * bigB ε A) * ∑ q ∈ majorQ N ε A, (q : ℝ) / (Nat.totient q : ℝ)
        ≤ C' * Y / L ^ (2 * bigB ε A) * (c * X) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (hsum.trans ?_)
          exact mul_le_mul_of_nonneg_left hfl hc0
      _ = C' * c * (Y * L ^ (-bigB ε A)) := by
          rw [hpow, hneg]; field_simp
  have hPle : ‖P‖ ≤ Y := by
    rw [hP, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by unfold LeanLab.Halupczok2012.ppM; positivity)]
    exact Split398aMajorA4.ppM_le _ _ _ (by linarith)
  have hsecond : ‖ramanujanTail (2 * k) X * P‖ ≤ Y * ‖ramanujanTail (2 * k) X‖ := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hPle (norm_nonneg _)
  rw [hdecomp]
  refine (norm_sub_le _ _).trans ?_
  have hT : 0 ≤ Y * ‖ramanujanTail (2 * k) X‖ := by positivity
  have hE : 0 ≤ Y * L ^ (-bigB ε A) := by
    have : 0 ≤ L ^ (-bigB ε A) := Real.rpow_nonneg (by linarith) _
    positivity
  have hCc : 0 ≤ C' * c := mul_nonneg hC'0 hc0
  nlinarith

/-- LEAF: PP1993 p. 45, last unnumbered display, giving display 8, the mean square over
N below 2k at most N + H of the Ramanujan tail over q above L^B is at most H L^{-A}.
Class HARD. Citation wall: Vaughan 1981 chapter 3, PP1993 ref 12,
copy copies/Vaughan1981-ch3.pdf, not in papers. -/
theorem a5_tail_mean_square : A5Stmt := by
  sorry

/-- LEAF: PP1993 p. 45 display 6, short interval Siegel Walfisz: for N^{7/12+eps} at most
Y at most N, q at most L^D and any chi mod q, psi of N chi minus psi of N - Y chi equals
delta_chi Y plus O of Y L^{-C'} for every C'. Class HARD. Citation wall: Perelli Pintz
Saffari 1985 Invent. Math. 79, PP1993 ref 6, copy papers/PPS1985-InventMath79.pdf. -/
theorem a6_short_siegel_walfisz : ShortSW := by
  sorry

/-- Proved, not a leaf. The long Siegel Walfisz form needed by A8 is the instance Y = N of A6,
taken with eps = 1/12. -/
theorem longSW_of_shortSW (h6 : ShortSW) : LongSW := by
  intro D C' hD hC'
  obtain ⟨K, N0, hK⟩ := h6 (1 / 12) D C' (by norm_num) hD hC'
  refine ⟨K, max N0 1, ?_⟩
  intro x q χ hx hq hqx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hxN : N0 ≤ x := (le_max_left _ _).trans hx
  have hpow : x ^ ((7 : ℝ) / 12 + 1 / 12) ≤ x := by
    calc x ^ ((7 : ℝ) / 12 + 1 / 12) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have h := hK x x q χ hxN hpow le_rfl hq hqx
  rwa [sub_self] at h

/-- LEAF: PP1993 p. 46 display 12, given A6 the remainder R1 of eta q a is at most a
constant times Y L^{2B-C'}, uniformly for eta in xi'_q, q at most L^B and reduced a; from
the character expansion of R1, tau of chi at most q^{1/2} and partial summation.
Class MEDIUM. -/
theorem a7_R1_sup (h6 : ShortSW) : A7Stmt := by
  sorry

/-- LEAF: PP1993 p. 46 display 11, given the long Siegel Walfisz form, the integral over
xi'_q of the square of R2 is at most a constant times Y L^{-C'} for every C'. Class HARD.
Citation wall: Vaughan 1981 chapter 3, PP1993 ref 12, copy copies/Vaughan1981-ch3.pdf,
not in papers; its Siegel Walfisz input is A6 at Y = N, see longSW_of_shortSW. -/
theorem a8_R2_mean_square (hL : LongSW) : A8Stmt := by
  sorry

/-- Real form of Cauchy Schwarz: from 2K at most tI + J/t for every t above 0. -/
theorem cs_real {K I J : ℝ} (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : ∀ t : ℝ, 0 < t → 2 * K ≤ t * I + J / t) : K ≤ Real.sqrt I * Real.sqrt J := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set a := Real.sqrt I with ha
  set b := Real.sqrt J with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hIa : I = a ^ 2 := (Real.sq_sqrt hI).symm
  have hJb : J = b ^ 2 := (Real.sq_sqrt hJ).symm
  set δ := ε / (a + b + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ * (a + b) ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have ht0 : 0 < (b + δ) / (a + δ) := by positivity
  have h1 := h _ ht0
  have e1 : (b + δ) / (a + δ) * I ≤ (b + δ) * a := by
    rw [hIa, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (add_nonneg hb0 hδ0.le) ha0]
  have e2 : J / ((b + δ) / (a + δ)) ≤ b * (a + δ) := by
    rw [hJb, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hb0 (add_nonneg ha0 hδ0.le)]
  nlinarith

/-- Cauchy Schwarz on a set, for real functions with integrable squares and product. -/
theorem cs_set {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun x => f x ^ 2) s) (hg : IntegrableOn (fun x => g x ^ 2) s)
    (hfg : IntegrableOn (fun x => f x * g x) s) :
    ∫ x in s, f x * g x ≤
      Real.sqrt (∫ x in s, f x ^ 2) * Real.sqrt (∫ x in s, g x ^ 2) := by
  apply cs_real (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  intro t ht
  have hpt : ∀ x, 2 * (f x * g x) ≤ t * f x ^ 2 + g x ^ 2 / t := by
    intro x
    have e : t * f x ^ 2 + g x ^ 2 / t - 2 * (f x * g x) = (t * f x - g x) ^ 2 / t := by
      field_simp
      ring
    have : 0 ≤ (t * f x - g x) ^ 2 / t := by positivity
    linarith
  have hm : ∫ x in s, 2 * (f x * g x) ≤ ∫ x in s, (t * f x ^ 2 + g x ^ 2 / t) :=
    integral_mono (hfg.const_mul 2) ((hf.const_mul t).add (hg.div_const t)) hpt
  rw [integral_add (hf.const_mul t) (hg.div_const t)] at hm
  simp only [integral_const_mul, integral_div] at hm
  exact hm

/-- Parseval for the indicator polynomial of a window, on a subset of a unit interval. -/
theorem parseval_window (X R : ℝ) (hR : 0 ≤ R) {s : Set ℝ}
    (hsub : s ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ∫ η in s, ‖∑ h ∈ kRange X R, phase ((h : ℝ) * η)‖ ^ 2 ≤ R + 1 := by
  set K := kRange X R
  set M := ⌈X + R⌉₊ + 1
  have hK : K ⊆ range M := by
    intro k hk
    have := (Finset.mem_filter.mp hk).1
    rw [Finset.mem_Icc] at this
    rw [Finset.mem_range]
    omega
  have hfilt : (range M).filter (fun m => m ∈ K) = K := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mp (hK h), h⟩⟩
  set b : ℕ → ℂ := fun m => if m ∈ K then 1 else 0
  have hsum : ∀ η : ℝ, (∑ h ∈ K, phase ((h : ℝ) * η)) =
      ∑ m ∈ range M, b m * LeanLab.PNTPort.LargeSieve.e (m * η) := by
    intro η
    have : ∀ m, b m * LeanLab.PNTPort.LargeSieve.e (m * η) =
        if m ∈ K then phase ((m : ℝ) * η) else 0 := by
      intro m
      simp only [b]
      split_ifs <;> simp [phase]
    simp_rw [this]
    rw [← Finset.sum_filter, hfilt]
  have hc : Continuous (fun η : ℝ => ‖∑ h ∈ K, phase ((h : ℝ) * η)‖ ^ 2) := by
    unfold phase LeanLab.PNTPort.LargeSieve.e
    fun_prop
  calc ∫ η in s, ‖∑ h ∈ K, phase ((h : ℝ) * η)‖ ^ 2
      ≤ ∫ η in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ‖∑ h ∈ K, phase ((h : ℝ) * η)‖ ^ 2 :=
        setIntegral_mono_set hc.integrableOn_Icc
          (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hsub)
    _ = ∫ η in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ range M, b m *
          LeanLab.PNTPort.LargeSieve.e (m * η)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
        simp_rw [hsum]
    _ = ∑ m ∈ range M, ‖b m‖ ^ 2 := LeanLab.PNTPort.Gallagher.parseval b M
    _ = (K.card : ℝ) := by
        have : ∀ m, ‖b m‖ ^ 2 = if m ∈ K then (1 : ℝ) else 0 := by
          intro m; simp only [b]; split_ifs <;> simp
        simp_rw [this]
        rw [Finset.sum_boole, hfilt]
    _ ≤ R + 1 := card_kRange_le hR

/-- The number of reduced residues in redRes q is phi of q. -/
theorem card_redRes {q : ℕ} : (redRes q).card = Nat.totient q := by
  rw [← Nat.filter_coprime_Ico_eq_totient q 1]
  unfold redRes
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Nat.coprime_comm]
  omega

/-- LEAF: PP1993 p. 46 displays 9 and 10, Cauchy Schwarz: Sigma_2 at most Y^{1/2} L^B
times the roots of the integrals of the squares of R_i, and Sigma_3 at most L^{2B} times
the geometric mean of those integrals, which is at most their maximum. Class MEDIUM.
PROVED. -/
theorem a9_cauchy_schwarz : A9Stmt := by
  intro ε A hε hA
  have hB : 0 < bigB ε A := by unfold bigB; positivity
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    ((log_rpow_le_eventually (2 * bigB ε A) (show (0 : ℝ) < 7 / 12 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)).and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨N0, ?_⟩
  intro N Y M1 M2 m hN hlow hYN hM1 hM2
  obtain ⟨hw2, hNe⟩ := hN0 N hN
  have hN1 : 1 ≤ N := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hNe
  have hNpos : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNe
  have hP : N ^ ((7 : ℝ) / 12) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hlow
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hN1 (by norm_num)).trans hP
  have hY0 : 0 < Y := by linarith
  set X := Real.log N ^ bigB ε A with hX
  have hX0 : 0 ≤ X := by positivity
  have hXX : X * X = Real.log N ^ (2 * bigB ε A) := by
    rw [hX, ← Real.rpow_add (by linarith)]; ring_nf
  -- the arcs xi'_q lie in a unit interval
  have hxi : ∀ q : ℕ, 1 ≤ q → xiArc N Y ε A q ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro q hq η hη
    have hw : arcWidth N Y ε A q ≤ 1 / 2 := by
      unfold arcWidth
      have hqY : Y ≤ (q : ℝ) * Y := le_mul_of_one_le_left hY0.le (by exact_mod_cast hq)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact ⟨by linarith [hη.1], by linarith [hη.2]⟩
  have hint : ∀ q : ℕ, ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (xiArc N Y ε A q) :=
    fun q f hf => (hf.integrableOn_Icc (a := -arcWidth N Y ε A q)
      (b := arcWidth N Y ε A q)).mono_set Set.Ioo_subset_Icc_self
  have hintC : ∀ q : ℕ, ∀ f : ℝ → ℂ, Continuous f → IntegrableOn f (xiArc N Y ε A q) :=
    fun q f hf => (hf.integrableOn_Icc (a := -arcWidth N Y ε A q)
      (b := arcWidth N Y ε A q)).mono_set Set.Ioo_subset_Icc_self
  have hT1 : Continuous (firstT N Y) := by
    unfold firstT phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hT2 : Continuous (secondT Y) := by
    unfold secondT phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hR1 : ∀ q a, Continuous (firstR N Y q a) := by
    intro q a
    unfold firstR firstT firstPoly phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hR2 : ∀ q a, Continuous (secondR Y q a) := by
    intro q a
    unfold secondR secondT secondPoly phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hP' : Continuous (fun η : ℝ => phase (-(m : ℝ) * η)) := by
    unfold phase LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hnph : ∀ t : ℝ, ‖phase t‖ = 1 := fun t => LeanLab.PNTPort.LargeSieve.norm_e t
  -- Cauchy Schwarz on xi'_q for two continuous complex functions
  have hcs : ∀ q : ℕ, ∀ f g : ℝ → ℂ, Continuous f → Continuous g →
      ∫ η in xiArc N Y ε A q, ‖f η‖ * ‖g η‖ ≤
        Real.sqrt (∫ η in xiArc N Y ε A q, ‖f η‖ ^ 2) *
          Real.sqrt (∫ η in xiArc N Y ε A q, ‖g η‖ ^ 2) := by
    intro q f g hf hg
    exact cs_set (hint q _ (by fun_prop)) (hint q _ (by fun_prop)) (hint q _ (by fun_prop))
  -- the T integrals
  have hTT1 : ∀ q : ℕ, 1 ≤ q → ∫ η in xiArc N Y ε A q, ‖firstT N Y η‖ ^ 2 ≤ Y + 1 :=
    fun q hq => parseval_window (N - Y) Y hY0.le (hxi q hq)
  have hTT2 : ∀ q : ℕ, 1 ≤ q → ∫ η in xiArc N Y ε A q, ‖secondT Y η‖ ^ 2 ≤ Y + 1 :=
    fun q hq => parseval_window 0 Y hY0.le (hxi q hq)
  have hM1' : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
      Real.sqrt (∫ η in xiArc N Y ε A q, ‖firstR N Y q a η‖ ^ 2) ≤ Real.sqrt M1 :=
    fun q hq a ha => Real.sqrt_le_sqrt (hM1 q hq a ha)
  have hM2' : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
      Real.sqrt (∫ η in xiArc N Y ε A q, ‖secondR Y q a η‖ ^ 2) ≤ Real.sqrt M2 :=
    fun q hq a ha => Real.sqrt_le_sqrt (hM2 q hq a ha)
  have hq1 : ∀ q ∈ majorQ N ε A, 1 ≤ q := fun q hq => (Finset.mem_Icc.mp hq).1
  have hcardQ : ((majorQ N ε A).card : ℝ) ≤ X := by
    unfold majorQ
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le hX0
  have hcardR : ∀ q ∈ majorQ N ε A, ((redRes q).card : ℝ) ≤ X := by
    intro q hq
    have h1 : (redRes q).card ≤ q := by
      unfold redRes
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : (q : ℝ) ≤ X := by
      have := (Finset.mem_Icc.mp hq).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hX0)
    exact (Nat.cast_le.mpr h1).trans h2
  have sY : 0 ≤ Real.sqrt (Y + 1) := Real.sqrt_nonneg _
  constructor
  · -- Sigma_2
    set K := Real.sqrt (Y + 1) * (Real.sqrt M1 + Real.sqrt M2) with hK
    have hK0 : 0 ≤ K := by positivity
    have hterm : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
        ‖phase (-(m : ℝ) * a / q) * (((μ q : ℂ)) / (Nat.totient q : ℂ) *
          ∫ η in xiArc N Y ε A q, (firstT N Y η * secondR Y q a η +
            secondT Y η * firstR N Y q a η) * phase (-(m : ℝ) * η))‖ ≤
          (1 / (Nat.totient q : ℝ)) * K := by
      intro q hq a ha
      have hq1' := hq1 q hq
      have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1'
      rw [norm_mul, norm_mul, hnph, one_mul, norm_div, Complex.norm_natCast]
      have hmu : ‖((μ q : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hI : ‖∫ η in xiArc N Y ε A q, (firstT N Y η * secondR Y q a η +
            secondT Y η * firstR N Y q a η) * phase (-(m : ℝ) * η)‖ ≤ K := by
        refine (norm_integral_le_integral_norm _).trans ?_
        have hpt : ∀ η, ‖(firstT N Y η * secondR Y q a η +
            secondT Y η * firstR N Y q a η) * phase (-(m : ℝ) * η)‖ ≤
            ‖firstT N Y η‖ * ‖secondR Y q a η‖ + ‖secondT Y η‖ * ‖firstR N Y q a η‖ := by
          intro η
          rw [norm_mul, hnph, mul_one, ← norm_mul, ← norm_mul]
          exact norm_add_le _ _
        have hmono : ∫ η in xiArc N Y ε A q, ‖(firstT N Y η * secondR Y q a η +
            secondT Y η * firstR N Y q a η) * phase (-(m : ℝ) * η)‖ ≤
            ∫ η in xiArc N Y ε A q, (‖firstT N Y η‖ * ‖secondR Y q a η‖ +
              ‖secondT Y η‖ * ‖firstR N Y q a η‖) :=
          integral_mono (hint q _ (by fun_prop)) ((hint q _ (by fun_prop)).add
            (hint q _ (by fun_prop))) hpt
        refine hmono.trans ?_
        rw [integral_add (hint q _ (by fun_prop)) (hint q _ (by fun_prop))]
        have c1 := hcs q _ _ hT1 (hR2 q a)
        have c2 := hcs q _ _ hT2 (hR1 q a)
        have t1 := Real.sqrt_le_sqrt (hTT1 q hq1')
        have t2 := Real.sqrt_le_sqrt (hTT2 q hq1')
        have m1 := hM1' q hq a ha
        have m2 := hM2' q hq a ha
        have p1 : Real.sqrt (∫ η in xiArc N Y ε A q, ‖firstT N Y η‖ ^ 2) *
            Real.sqrt (∫ η in xiArc N Y ε A q, ‖secondR Y q a η‖ ^ 2) ≤
            Real.sqrt (Y + 1) * Real.sqrt M2 :=
          mul_le_mul t1 m2 (Real.sqrt_nonneg _) sY
        have p2 : Real.sqrt (∫ η in xiArc N Y ε A q, ‖secondT Y η‖ ^ 2) *
            Real.sqrt (∫ η in xiArc N Y ε A q, ‖firstR N Y q a η‖ ^ 2) ≤
            Real.sqrt (Y + 1) * Real.sqrt M1 :=
          mul_le_mul t2 m1 (Real.sqrt_nonneg _) sY
        rw [hK]
        linarith
      exact mul_le_mul (div_le_div_of_nonneg_right hmu hφ.le) hI (norm_nonneg _)
        (by positivity)
    have hq : ∀ q ∈ majorQ N ε A,
        ‖∑ a ∈ redRes q, phase (-(m : ℝ) * a / q) * (((μ q : ℂ)) / (Nat.totient q : ℂ) *
          ∫ η in xiArc N Y ε A q, (firstT N Y η * secondR Y q a η +
            secondT Y η * firstR N Y q a η) * phase (-(m : ℝ) * η))‖ ≤ K := by
      intro q hq
      have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (hq1 q hq)
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hterm q hq)).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul, card_redRes]
      rw [← mul_assoc, mul_one_div_cancel hφ.ne', one_mul]
    unfold sigma2
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hq).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ((majorQ N ε A).card : ℝ) * K ≤ X * K := mul_le_mul_of_nonneg_right hcardQ hK0
      _ = _ := by rw [hK]; ring
  · -- Sigma_3
    set K := Real.sqrt M1 * Real.sqrt M2 with hK
    have hK0 : 0 ≤ K := by positivity
    have hterm : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
        ‖phase (-(m : ℝ) * a / q) * ∫ η in xiArc N Y ε A q,
          firstR N Y q a η * secondR Y q a η * phase (-(m : ℝ) * η)‖ ≤ K := by
      intro q hq a ha
      rw [norm_mul, hnph, one_mul]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt : ∀ η, ‖firstR N Y q a η * secondR Y q a η * phase (-(m : ℝ) * η)‖ =
          ‖firstR N Y q a η‖ * ‖secondR Y q a η‖ := by
        intro η; rw [norm_mul, hnph, mul_one, norm_mul]
      simp_rw [hpt]
      refine (hcs q _ _ (hR1 q a) (hR2 q a)).trans ?_
      exact mul_le_mul (hM1' q hq a ha) (hM2' q hq a ha) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    have hq : ∀ q ∈ majorQ N ε A,
        ‖∑ a ∈ redRes q, phase (-(m : ℝ) * a / q) * ∫ η in xiArc N Y ε A q,
          firstR N Y q a η * secondR Y q a η * phase (-(m : ℝ) * η)‖ ≤ X * K := by
      intro q hq
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hterm q hq)).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hcardR q hq) hK0
    unfold sigma3
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hq).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ← hXX]
    calc ((majorQ N ε A).card : ℝ) * (X * K) ≤ X * (X * K) :=
          mul_le_mul_of_nonneg_right hcardQ (by positivity)
      _ = X * X * K := by ring

set_option maxHeartbeats 1600000 in
/-- LEAF: PP1993 p. 46 display 13 and the display after it, the assembly: with C' at least
4B + A/2 in A7 and A8, displays 12 and 13 bound Sigma_2 and Sigma_3 by Y L^{-A/2}, and with
displays 7, 8 and 11 this gives Sigma_M at most H Y^2 L^{-A}. Class MEDIUM. PROVED. -/
theorem a10_assembly (h2 : A2Stmt) (h4 : A4Stmt) (h5 : A5Stmt) (h7 : A7Stmt)
    (h8 : A8Stmt) (h9 : A9Stmt) :
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
      ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 ≤
        C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A) := by
  intro ε A hε hA
  set B := bigB ε A with hBdef
  have hB : 0 < B := by rw [hBdef]; unfold bigB; positivity
  obtain ⟨N2, h2'⟩ := h2 ε A hε hA
  obtain ⟨C4, N4, h4'⟩ := h4 ε A hε hA
  obtain ⟨C5, N5, h5'⟩ := h5 ε A hε hA
  obtain ⟨C7, N7, h7'⟩ := h7 ε A (4 * B + A / 2) hε hA (by positivity)
  obtain ⟨C8, N8, h8'⟩ := h8 ε A (2 * B + A) hε hA (by positivity)
  obtain ⟨N9, h9'⟩ := h9 ε A hε hA
  set c4 := |C4| with hc4
  set K1 := 6 * c4 ^ 2 with hK1
  set K2 := 3 * (2 * c4 ^ 2 + (8 * C7 ^ 2 + 4 * |C8|) + 2 * C7 ^ 2 * |C8|) with hK2
  refine ⟨K1 * C5 + 3 / 2 * K2,
    max (max (max N2 N4) (max N5 N7)) (max (max N8 N9) (Real.exp 1)), ?_⟩
  intro N Y hN hlow hYN
  have hN2 : N2 ≤ N := le_trans (by simp) hN
  have hN4 : N4 ≤ N := le_trans (by simp) hN
  have hN5 : N5 ≤ N := le_trans (by simp) hN
  have hN7 : N7 ≤ N := le_trans (by simp) hN
  have hN8 : N8 ≤ N := le_trans (by simp) hN
  have hN9 : N9 ≤ N := le_trans (by simp) hN
  have hNe : Real.exp 1 ≤ N := le_trans (by simp) hN
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hN1 : 1 < N := by linarith
  have hNpos : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNe
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hP : N ^ ((7 : ℝ) / 12) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)).trans hlow
  have hY1 : 1 ≤ Y := (Real.one_le_rpow hN1.le (by norm_num)).trans hP
  have hY0 : 0 < Y := by linarith
  have hε5 : ε ≤ 5 / 12 := by
    by_contra hc
    rw [not_le] at hc
    have := Real.rpow_lt_rpow_of_exponent_lt hN1 (show (1 : ℝ) < 7 / 12 + ε by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hBA : A ≤ 2 * B := by
    have h3 : (36 : ℝ) / 5 ≤ 3 / ε := by
      rw [le_div_iff₀ hε]; linarith
    have : B = 3 / ε * (2 * A + 25) := by rw [hBdef]; rfl
    nlinarith
  have r1 : ∀ u : ℝ, (L ^ u) ^ 2 = L ^ (2 * u) := by
    intro u
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    congr 1
    push_cast
    ring
  have r2 : ∀ u v : ℝ, L ^ u * L ^ v = L ^ (u + v) := fun u v => (Real.rpow_add hLpos u v).symm
  have hLA1 : L ^ (-A) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLA0 : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL0 _
  have hLBA : L ^ (2 * -B) ≤ L ^ (-A) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  set X := L ^ B with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hL1 hB.le
  have hX2 : X ^ 2 = L ^ (2 * B) := r1 B
  set H := Y ^ (1 / 3 + ε) with hHdef
  have hH1 : 1 ≤ H := Real.one_le_rpow hY1 (by linarith)
  -- the two mean values M1 and M2
  set M1 := 2 * (L ^ (2 * B) / Y) * (C7 * Y * L ^ (2 * B - (4 * B + A / 2))) ^ 2 with hM1def
  set M2 := C8 * Y * L ^ (-(2 * B + A)) with hM2def
  have hw : ∀ q : ℕ, 1 ≤ q → 0 ≤ arcWidth N Y ε A q ∧ arcWidth N Y ε A q ≤ L ^ (2 * B) / Y := by
    intro q hq
    unfold arcWidth
    rw [← hBdef]
    refine ⟨by positivity, div_le_div_of_nonneg_left (by positivity) hY0 ?_⟩
    exact le_mul_of_one_le_left hY0.le (by exact_mod_cast hq)
  have hint : ∀ q : ℕ, ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (xiArc N Y ε A q) :=
    fun q f hf => (hf.integrableOn_Icc (a := -arcWidth N Y ε A q)
      (b := arcWidth N Y ε A q)).mono_set Set.Ioo_subset_Icc_self
  have hM1 : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
      ∫ η in xiArc N Y ε A q, ‖firstR N Y q a η‖ ^ 2 ≤ M1 := by
    intro q hq a ha
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hR1 : Continuous (firstR N Y q a) := by
      unfold firstR firstT firstPoly phase LeanLab.PNTPort.LargeSieve.e; fun_prop
    have hpt : ∀ η ∈ xiArc N Y ε A q, ‖firstR N Y q a η‖ ^ 2 ≤
        (C7 * Y * L ^ (2 * B - (4 * B + A / 2))) ^ 2 := fun η hη =>
      pow_le_pow_left₀ (norm_nonneg _) (h7' N Y q a η hN7 hlow hYN hq ha hη) 2
    obtain ⟨hw0, hw1⟩ := hw q hq1
    calc ∫ η in xiArc N Y ε A q, ‖firstR N Y q a η‖ ^ 2
        ≤ ∫ η in xiArc N Y ε A q, (C7 * Y * L ^ (2 * B - (4 * B + A / 2))) ^ 2 :=
          setIntegral_mono_on (hint q _ (by fun_prop)) (hint q _ continuous_const)
            measurableSet_Ioo hpt
      _ = 2 * arcWidth N Y ε A q * (C7 * Y * L ^ (2 * B - (4 * B + A / 2))) ^ 2 := by
          rw [setIntegral_const, xiArc, Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul]
          ring
      _ ≤ M1 := by
          rw [hM1def]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          linarith
  have hM2 : ∀ q ∈ majorQ N ε A, ∀ a ∈ redRes q,
      ∫ η in xiArc N Y ε A q, ‖secondR Y q a η‖ ^ 2 ≤ M2 :=
    fun q hq a ha => h8' N Y q a hN8 hlow hYN hq ha
  have h1Q : 1 ∈ majorQ N ε A :=
    Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by rw [Nat.cast_one]; exact hX1)⟩
  have h1R : 1 ∈ redRes 1 := by unfold redRes; decide
  have hM10 : 0 ≤ M1 := (integral_nonneg fun η => sq_nonneg _).trans (hM1 1 h1Q 1 h1R)
  have hM20 : 0 ≤ M2 := (integral_nonneg fun η => sq_nonneg _).trans (hM2 1 h1Q 1 h1R)
  have hXM1 : X ^ 2 * M1 = 2 * C7 ^ 2 * Y * L ^ (-A) := by
    rw [hX2, hM1def, mul_pow, mul_pow, r1]
    have e : L ^ (2 * B) * (2 * (L ^ (2 * B) / Y) * (C7 ^ 2 * Y ^ 2 *
        L ^ (2 * (2 * B - (4 * B + A / 2))))) =
        2 * C7 ^ 2 * Y * (L ^ (2 * B) * L ^ (2 * B) * L ^ (2 * (2 * B - (4 * B + A / 2)))) := by
      field_simp
    rw [e, r2, r2, show 2 * B + 2 * B + 2 * (2 * B - (4 * B + A / 2)) = -A by ring]
  have hXM2 : X ^ 2 * M2 = C8 * Y * L ^ (-A) := by
    rw [hX2, hM2def]
    calc L ^ (2 * B) * (C8 * Y * L ^ (-(2 * B + A))) =
        C8 * Y * (L ^ (2 * B) * L ^ (-(2 * B + A))) := by ring
      _ = _ := by rw [r2, show 2 * B + -(2 * B + A) = -A by ring]
  -- the pointwise bound for each k
  have hk : ∀ k ∈ kRange (N / 2) (H / 2),
      ‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) - ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 ≤
        K1 * Y ^ 2 * ‖ramanujanTail (2 * k) X‖ ^ 2 + K2 * Y ^ 2 * L ^ (-A) := by
    intro k hkR
    set t := ‖ramanujanTail (2 * k) X‖ with ht
    have ht0 : 0 ≤ t := norm_nonneg _
    have hdec := h2' N Y (2 * k) hN2 hlow hYN
    obtain ⟨hb, hc⟩ := h9' N Y M1 M2 (2 * k) hN9 hlow hYN hM1 hM2
    have ha := h4' N Y k hN4 hlow hYN hkR
    try rw [← hLdef] at ha
    try rw [← hXdef] at ha
    try rw [← hLdef] at hb
    try rw [← hXdef] at hb
    try rw [← hLdef] at hc
    set u := sigma1 N Y ε A (2 * k) - ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ) with hu
    have hD : arcCoeff N Y (2 * k) (majorArcs N Y ε A) - ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)
        = u + sigma2 N Y ε A (2 * k) + sigma3 N Y ε A (2 * k) := by
      rw [hdec, hu]; ring
    set a := ‖u‖
    set b := ‖sigma2 N Y ε A (2 * k)‖
    set c := ‖sigma3 N Y ε A (2 * k)‖
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hc0 : 0 ≤ c := norm_nonneg _
    have hnorm : ‖u + sigma2 N Y ε A (2 * k) + sigma3 N Y ε A (2 * k)‖ ≤ a + b + c :=
      (norm_add_le _ _).trans (by linarith [norm_add_le u (sigma2 N Y ε A (2 * k))])
    have hsq : ‖u + sigma2 N Y ε A (2 * k) + sigma3 N Y ε A (2 * k)‖ ^ 2 ≤
        3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have e : 3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2 =
          (a - b) ^ 2 + (b - c) ^ 2 + (a - c) ^ 2 := by ring
      have h2 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        have := add_nonneg (add_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c))) (sq_nonneg (a - c))
        linarith
      exact h1.trans h2
    -- the bound on a
    have hLB0 : 0 ≤ L ^ (-B) := Real.rpow_nonneg hL0 _
    have ha' : a ≤ c4 * (Y * t + Y * L ^ (-B)) :=
      ha.trans (mul_le_mul_of_nonneg_right (le_abs_self C4) (by positivity))
    have ha2 : a ^ 2 ≤ 2 * c4 ^ 2 * Y ^ 2 * t ^ 2 + 2 * c4 ^ 2 * Y ^ 2 * L ^ (-A) := by
      have h1 := pow_le_pow_left₀ ha0 ha' 2
      have h2 : (L ^ (-B)) ^ 2 ≤ L ^ (-A) := by rw [r1]; exact hLBA
      have h3 : (c4 * (Y * t + Y * L ^ (-B))) ^ 2 ≤
          2 * c4 ^ 2 * Y ^ 2 * t ^ 2 + 2 * c4 ^ 2 * Y ^ 2 * (L ^ (-B)) ^ 2 := by
        nlinarith [sq_nonneg (c4 * Y * (t - L ^ (-B)))]
      have h4 : 2 * c4 ^ 2 * Y ^ 2 * (L ^ (-B)) ^ 2 ≤ 2 * c4 ^ 2 * Y ^ 2 * L ^ (-A) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
    -- the bound on b
    have hb2 : b ^ 2 ≤ (8 * C7 ^ 2 + 4 * |C8|) * Y ^ 2 * L ^ (-A) := by
      have h1 := pow_le_pow_left₀ hb0 hb 2
      have s1 := Real.sq_sqrt hM10
      have s2 := Real.sq_sqrt hM20
      have sY := Real.sq_sqrt (show (0 : ℝ) ≤ Y + 1 by linarith)
      have hsum : (Real.sqrt M1 + Real.sqrt M2) ^ 2 ≤ 2 * (M1 + M2) := by
        nlinarith [sq_nonneg (Real.sqrt M1 - Real.sqrt M2)]
      have e : (Real.sqrt (Y + 1) * X * (Real.sqrt M1 + Real.sqrt M2)) ^ 2 =
          (Y + 1) * X ^ 2 * (Real.sqrt M1 + Real.sqrt M2) ^ 2 := by
        rw [mul_pow, mul_pow, sY]
      have h2 : (Y + 1) * X ^ 2 * (Real.sqrt M1 + Real.sqrt M2) ^ 2 ≤
          (Y + 1) * (2 * (X ^ 2 * M1 + X ^ 2 * M2)) := by
        have : 0 ≤ (Y + 1) * X ^ 2 := by positivity
        nlinarith
      rw [hXM1, hXM2] at h2
      have h3 : C8 * Y * L ^ (-A) ≤ |C8| * Y * L ^ (-A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C8) hY0.le) hLA0
      have h4 : 0 ≤ 2 * C7 ^ 2 * Y * L ^ (-A) + |C8| * Y * L ^ (-A) := by positivity
      have h5 : (Y + 1) * (2 * (2 * C7 ^ 2 * Y * L ^ (-A) + |C8| * Y * L ^ (-A))) ≤
          (2 * Y) * (2 * (2 * C7 ^ 2 * Y * L ^ (-A) + |C8| * Y * L ^ (-A))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h6 : (Y + 1) * (2 * (2 * C7 ^ 2 * Y * L ^ (-A) + C8 * Y * L ^ (-A))) ≤
          (Y + 1) * (2 * (2 * C7 ^ 2 * Y * L ^ (-A) + |C8| * Y * L ^ (-A))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rw [e] at h1
      have h7 : (2 * Y) * (2 * (2 * C7 ^ 2 * Y * L ^ (-A) + |C8| * Y * L ^ (-A))) =
          (8 * C7 ^ 2 + 4 * |C8|) * Y ^ 2 * L ^ (-A) := by ring
      linarith
    -- the bound on c
    have hc2 : c ^ 2 ≤ 2 * C7 ^ 2 * |C8| * Y ^ 2 * L ^ (-A) := by
      have h1 := pow_le_pow_left₀ hc0 hc 2
      have e : (L ^ (2 * B) * (Real.sqrt M1 * Real.sqrt M2)) ^ 2 = (X ^ 2 * M1) * (X ^ 2 * M2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hM10, Real.sq_sqrt hM20, ← hX2]; ring
      rw [e, hXM1, hXM2] at h1
      have h2 : C8 * Y * L ^ (-A) ≤ |C8| * Y := by
        calc C8 * Y * L ^ (-A) ≤ |C8| * Y * L ^ (-A) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C8) hY0.le) hLA0
          _ ≤ |C8| * Y * 1 := mul_le_mul_of_nonneg_left hLA1 (by positivity)
          _ = |C8| * Y := mul_one _
      have h3 : (2 * C7 ^ 2 * Y * L ^ (-A)) * (C8 * Y * L ^ (-A)) ≤
          (2 * C7 ^ 2 * Y * L ^ (-A)) * (|C8| * Y) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (2 * C7 ^ 2 * Y * L ^ (-A)) * (|C8| * Y) = 2 * C7 ^ 2 * |C8| * Y ^ 2 * L ^ (-A) := by
        ring
      linarith
    rw [hD]
    have : K1 * Y ^ 2 * t ^ 2 + K2 * Y ^ 2 * L ^ (-A) =
        3 * (2 * c4 ^ 2 * Y ^ 2 * t ^ 2 + 2 * c4 ^ 2 * Y ^ 2 * L ^ (-A) +
          (8 * C7 ^ 2 + 4 * |C8|) * Y ^ 2 * L ^ (-A) + 2 * C7 ^ 2 * |C8| * Y ^ 2 * L ^ (-A)) := by
      rw [hK1, hK2]; ring
    rw [this]
    linarith
  -- sum over k
  have hcard : ((kRange (N / 2) (H / 2)).card : ℝ) ≤ 3 / 2 * H :=
    (card_kRange_le (by linarith)).trans (by linarith)
  have h5k := h5' N Y hN5 hlow hYN
  try rw [← hLdef] at h5k
  try rw [← hXdef] at h5k
  calc ∑ k ∈ kRange (N / 2) (H / 2), ‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2
      ≤ ∑ k ∈ kRange (N / 2) (H / 2),
          (K1 * Y ^ 2 * ‖ramanujanTail (2 * k) X‖ ^ 2 + K2 * Y ^ 2 * L ^ (-A)) :=
        Finset.sum_le_sum hk
    _ = K1 * Y ^ 2 * (∑ k ∈ kRange (N / 2) (H / 2), ‖ramanujanTail (2 * k) X‖ ^ 2) +
          ((kRange (N / 2) (H / 2)).card : ℝ) * (K2 * Y ^ 2 * L ^ (-A)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ K1 * Y ^ 2 * (C5 * H * L ^ (-A)) + 3 / 2 * H * (K2 * Y ^ 2 * L ^ (-A)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h5k (by positivity)
        · exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (K1 * C5 + 3 / 2 * K2) * H * Y ^ 2 * L ^ (-A) := by ring

/-! ## Wiring -/

/-- Exactly the statement of `Decomp398a.major_energy`, PP1993 p. 44 display 4, proved
from the leaves A1 to A10 with no sorry of its own. -/
theorem major_energy_of_leaves :
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ C N0 : ℝ, ∀ N Y : ℝ,
      N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
      ∑ k ∈ kRange (N / 2) (Y ^ (1 / 3 + ε) / 2),
        ‖arcCoeff N Y (2 * k) (majorArcs N Y ε A) -
          ((S (2 * k) * ppM (2 * k) N Y : ℝ) : ℂ)‖ ^ 2 ≤
        C * Y ^ (1 / 3 + ε) * Y ^ 2 * Real.log N ^ (-A) :=
  a10_assembly (a2_split a1_arcs_disjoint) (a4_sigma1 a3_T_integral) a5_tail_mean_square
    (a7_R1_sup a6_short_siegel_walfisz)
    (a8_R2_mean_square (longSW_of_shortSW a6_short_siegel_walfisz)) a9_cauchy_schwarz

end LeanLab.Halupczok2012.Split398aMajor
