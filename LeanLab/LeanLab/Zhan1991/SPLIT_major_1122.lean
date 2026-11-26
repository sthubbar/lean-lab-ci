import LeanLab.Zhan1991.Decomp110
import LeanLab.Zhan1991.SingConv

/-!
P0068 Zhan 1991, the major arc evaluation of page 271, `major_evaluation110` of Decomp110.lean,
split along the standard method the paper cites from Pan and Pan, reference 2, burst-20261122.

Page 271 prints one display only: the integral over `E₁` equals `3 𝔖(N) U² L⁻³ + O(U² L⁻⁴)`,
"by the standard method as in [2]". Reference 2 is not in the lab. The steps below are the
standard circle method steps that display rests on:
1. the major arc approximation `S(a/q + λ) = μ(q)/φ(q) v(λ) + error`, a short interval
   Siegel Walfisz input, cited;
2. the assembly over the arcs, giving the truncated singular series times the singular integral;
3. the singular integral, `3 U² L⁻³ + O(U² L⁻⁴)`;
4. the truncated singular series, `𝔖(N) + O(L⁻¹)`;
5. `𝔖(N)` is bounded.
`majorEval_of_steps` is PROVED from steps 2 to 5.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open Real
open scoped ArithmeticFunction.Moebius

/-- Page 271, the standard major arc main term: `v(λ) = Σ_{N₁ < n ≤ N₂} e(nλ) / log n` over the
integers of the window `[N/3 - U, N/3 + U]`, with the endpoint convention of `Win`. -/
def vSum (N : ℕ) (U lam : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
    ee ((n : ℝ) * lam) / (Real.log n : ℂ)

/-- The Ramanujan sum `c_q(N) = Σ_{a mod q, (a, q) = 1} e(aN/q)`, real since the reduced
residues are closed under negation; page 271, the singular series. -/
def ramanujanC (q N : ℕ) : ℝ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    Real.cos (2 * π * (a : ℝ) * N / q)

/-- Page 271, the truncated singular series `Σ_{q ≤ Q₁} μ(q) c_q(N) / φ(q)³`. -/
def singTrunc (N : ℕ) (Q : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N

/-- Page 271, the singular integral over one arc, `Re ∫_{-w}^{w} v(λ)³ e(-Nλ) dλ`. -/
def singInt (N : ℕ) (U w : ℝ) : ℝ :=
  (∫ lam in (-w)..w, vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)).re

/-- Step 1, the major arc approximation: for `q ≤ L^d`, `(a, q) = 1` and `|λ| ≤ L⁴/U`,
`Σ_{N₁ < p ≤ N₂} e(p(a/q + λ)) = μ(q)/φ(q) v(λ) + O(U L^{-A})` for every `A`. -/
def MajorArcApprox : Prop :=
  ∀ d c A : ℝ, 0 < d → 0 < c → 0 < A → ∃ K N₀ : ℝ, ∀ (N : ℕ) (q : ℕ) (a : ℤ) (lam : ℝ),
    N₀ ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ d → Int.gcd a q = 1 →
    |lam| ≤ Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) →
    ‖primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ((a : ℝ) / q + lam) -
        ((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) *
          vSum N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam‖
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) * Real.log N ^ (-A)

/-- Step 2, the arcs assembled: the major term is the truncated singular series times the
singular integral, up to `O(U² L⁻⁴)`, for every large cutoff exponent `d`. -/
def MajorAssembly : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
    ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
        - singTrunc N (Real.log N ^ d) *
            singInt N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)
              (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))|
        ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)

/-- Step 3, the singular integral: `3 U² L⁻³ + O(U² L⁻⁴)`. -/
def SingIntEval : Prop :=
  ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |singInt N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)
        (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))
      - 3 * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-3 : ℝ)|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)

/-- Step 4, the truncated singular series: `𝔖(N) + O(L⁻¹)` at `Q₁ = L^d` for large `d`. -/
def SingTruncEval : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
    |singTrunc N (Real.log N ^ d) - Sing N| ≤ K / Real.log N

/-- Step 5, `𝔖(N)` is bounded. -/
def SingBounded : Prop := ∃ C : ℝ, ∀ N : ℕ, |Sing N| ≤ C

/-- LEAF: Page 271, step 1 of the standard method of reference 2, the major arc approximation
by a short interval Siegel Walfisz theorem for `U = N^{5/8} L^c`, which is above Huxley's
`N^{7/12 + ε}`. HARD, cited input. The lab's KumchevLiu2007 `thetaChi_short` is the same
citation wall in theta form, also cited. -/
theorem majorArcApprox_cited : MajorArcApprox := by
  sorry

open Real

/-- The sine part of the Ramanujan sum vanishes, by the involution `a ↦ q - a`. PROVED. -/
theorem ramanujan_sin_zero (q N : ℕ) (hq : 1 ≤ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      Real.sin (2 * π * (a : ℝ) * N / q)) = 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hrefl : ∀ a : ℕ, 0 < a → a < q →
      Real.sin (2 * π * ((q - a : ℕ) : ℝ) * N / q) = -Real.sin (2 * π * (a : ℝ) * N / q) := by
    intro a ha haq
    rw [Nat.cast_sub haq.le]
    have e : 2 * π * ((q : ℝ) - a) * N / q = (N : ℕ) * (2 * π) - 2 * π * a * N / q := by
      field_simp
    rw [e, Real.sin_nat_mul_two_pi_sub]
  apply Finset.sum_involution (fun a _ => (q - a) % q)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q), hrefl a hpos ha.1]; ring
  · intro a ha hne heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp at hne
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q)] at heq
      apply hne
      have h2 : 2 * a = q := by omega
      have e : 2 * π * (a : ℝ) * N / q = (N : ℕ) * π := by
        rw [← h2]; push_cast; field_simp
      rw [e, Real.sin_nat_mul_pi]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simpa using ha.2
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q)]
      exact (Nat.coprime_self_sub_left (by omega)).mpr ha.2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; simp
    · rw [Nat.mod_eq_of_lt (by omega : q - a < q), Nat.mod_eq_of_lt (by omega)]; omega

/-- Page 271, `Σ_{a mod q, (a, q) = 1} e(-aN/q) = c_q(N)`. PROVED. -/
theorem ramanujan_sum_complex (q N : ℕ) (hq : 1 ≤ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ee (-((a : ℝ) * N / q))) =
      (ramanujanC q N : ℂ) := by
  have he : ∀ a : ℕ, ee (-((a : ℝ) * N / q)) =
      (Real.cos (2 * π * (a : ℝ) * N / q) : ℂ) - (Real.sin (2 * π * (a : ℝ) * N / q) : ℂ) *
        Complex.I := by
    intro a
    unfold ee
    have : (2 * (π : ℂ) * Complex.I * ((-((a : ℝ) * N / q) : ℝ) : ℂ)) =
        ((-(2 * π * (a : ℝ) * N / q) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    ramanujan_sin_zero q N hq]
  unfold ramanujanC
  simp

open Real Filter Asymptotics

/-- Page 270, the major arcs are separated: two distinct centres `a/q ≠ a'/q'` with
`q, q' ≤ L^d` are more than twice the half width `L⁴/U` apart, for large `N`. PROVED. -/
theorem majorArcs_separated (d c : ℝ) (hd : 0 < d) (hc : 0 ≤ c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (q q' : ℕ) (a a' : ℤ), 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ d → 1 ≤ q' → (q' : ℝ) ≤ Real.log N ^ d →
      (a : ℝ) / q ≠ (a' : ℝ) / q' →
      2 * (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)) <
        |(a : ℝ) / q - (a' : ℝ) / q'| := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 + 2 * d) (by norm_num : (0 : ℝ) < 5 / 8)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (Real.exp 1)))
  refine ⟨X0, fun N hN q q' a a' hq hqL hq' hqL' hne => ?_⟩
  obtain ⟨hb, he⟩ := hX0 N hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 1) he
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hP : 0 < (N : ℝ) ^ (5 / 8 : ℝ) := Real.rpow_pos_of_pos hN0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLpos.le _),
    abs_of_nonneg hP.le] at hb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  -- separation of distinct fractions
  have hsep : 1 / ((q : ℝ) * q') ≤ |(a : ℝ) / q - (a' : ℝ) / q'| := by
    have hz : (a * q' - a' * q : ℤ) ≠ 0 := by
      intro h0
      apply hne
      have : (a : ℝ) * q' = (a' : ℝ) * q := by exact_mod_cast sub_eq_zero.mp h0
      field_simp
      linarith
    have h1 : (1 : ℝ) ≤ |((a * q' - a' * q : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
    have e : (a : ℝ) / q - (a' : ℝ) / q' = ((a * q' - a' * q : ℤ) : ℝ) / (q * q') := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hqq : (q : ℝ) * q' ≤ L ^ (2 * d) := by
    rw [show 2 * d = d + d by ring, Real.rpow_add hLpos]
    exact mul_le_mul hqL hqL' hq0'.le (Real.rpow_nonneg hLpos.le _)
  have hLc : 1 ≤ L ^ c := Real.one_le_rpow hL1 hc
  have hL2d : 0 < L ^ (2 * d) := Real.rpow_pos_of_pos hLpos _
  have hsum : L ^ (4 : ℝ) * L ^ (2 * d) = L ^ (4 + 2 * d) := by rw [← Real.rpow_add hLpos]
  have key : 2 * (L ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * L ^ c)) < 1 / L ^ (2 * d) := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) hL2d]
    have hc1 : (N : ℝ) ^ (5 / 8 : ℝ) ≤ (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c :=
      le_mul_of_one_le_right hP.le hLc
    nlinarith
  calc 2 * (L ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * L ^ c)) < 1 / L ^ (2 * d) := key
    _ ≤ 1 / ((q : ℝ) * q') := one_div_le_one_div_of_le (by positivity) hqq
    _ ≤ _ := hsep

noncomputable section
open Real
open scoped ArithmeticFunction.Moebius
open MeasureTheory

/-- `e(k) = 1` for an integer `k`, page 270. PROVED. -/
theorem ee_intCast_one (k : ℤ) : ee (k : ℝ) = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- Page 270, `S(α)³ e(-Nα)` has period 1. PROVED. -/
theorem majorIntegrand_periodic (N : ℕ) (U α : ℝ) :
    primeSum110 N U (α + 1) ^ 3 * ee (-(N : ℝ) * (α + 1)) =
      primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
  have hS : primeSum110 N U (α + 1) = primeSum110 N U α := by
    unfold primeSum110
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show (p : ℝ) * (α + 1) = (p : ℝ) * α + ((p : ℤ) : ℝ) by push_cast; ring, ee_add110,
      ee_intCast_one, mul_one]
  rw [hS, show -(N : ℝ) * (α + 1) = -(N : ℝ) * α + ((-(N : ℤ) : ℤ) : ℝ) by push_cast; ring,
    ee_add110, ee_intCast_one, mul_one]

/-- Distinct reduced fractions are distinct reals: `a/q = a'/q'` with `(a, q) = (a', q') = 1` forces
`a = a'`, `q = q'`. Page 270. PROVED. -/
theorem reduced_frac_eq (q q' a a' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q') (h : Nat.Coprime a q)
    (h' : Nat.Coprime a' q') (he : (a : ℝ) / q = a' / q') : a = a' ∧ q = q' := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0' : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm : a * q' = a' * q := by
    rw [div_eq_div_iff hq0 hq0'] at he; exact_mod_cast he
  have h1 : q ∣ q' := by
    have : q ∣ q' * a := ⟨a', by rw [mul_comm q' a, hm, mul_comm]⟩
    exact (Nat.Coprime.symm h).dvd_of_dvd_mul_right this
  have h2 : q' ∣ q := by
    have : q' ∣ q * a' := ⟨a, by rw [mul_comm q a', ← hm, mul_comm]⟩
    exact (Nat.Coprime.symm h').dvd_of_dvd_mul_right this
  have hqq := Nat.dvd_antisymm h1 h2
  subst hqq
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hm, rfl⟩

/-- Pages 270 to 271, the major arcs in `[0, 1]` for large `N`: `[0, 1] ∩ E₁` is the half arcs
`[0, w]`, `[1 - w, 1]` of `q = 1` and the full arcs `[a/q - w, a/q + w]` for `2 ≤ q ≤ L^d`,
`1 ≤ a < q`, `(a, q) = 1`, using `majorArcs_separated` to keep reduced fractions with `2 ≤ q` more
than `2w` from `0` and `1`. PROVED. -/
theorem arcs_set_eq_proof (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      Set.Icc (0 : ℝ) 1 ∩ majorArcs110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d =
        Set.Icc 0 (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)) ∪ Set.Icc (1 - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))) 1 ∪
          ⋃ i ∈ (Finset.Icc 2 ⌊(Real.log N ^ d)⌋₊).sigma
              (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)),
            Set.Icc ((i.2 : ℝ) / i.1 - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))) ((i.2 : ℝ) / i.1 + (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))) := by
  obtain ⟨N₂, hsep⟩ := majorArcs_separated d c hd hc.le
  refine ⟨max N₂ (Real.exp 1), fun N hN => ?_⟩
  have hN2 : N₂ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN1' : (1 : ℝ) ≤ N := by have := Real.exp_one_gt_d9; linarith
  have hS := hsep N hN2
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX1 : (1 : ℝ) ≤ X := Real.one_le_rpow hL1 hd.le
  have hX1' : ((1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX1
  have hUpos : 0 < U := mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _)
  have hw0 : 0 ≤ w := by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) (4 : ℝ); positivity
  have hw1 : 2 * w < 1 := by
    have := hS 1 1 0 1 le_rfl hX1' le_rfl hX1' (by norm_num)
    norm_num at this; linarith
  -- a reduced fraction `a/q` with `2 ≤ q` is more than `2w` from `0` and from `1`
  have hfar : ∀ (q : ℕ) (a : ℤ), 2 ≤ q → (q : ℝ) ≤ X → Int.gcd a q = 1 →
      2 * w < |(a : ℝ) / q| ∧ 2 * w < |(a : ℝ) / q - 1| := by
    intro q a hq hqX hg
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [Int.gcd_zero_left] at hg; simp at hg; omega
    have haq : a ≠ q := by
      rintro rfl; rw [Int.gcd_self] at hg; simp at hg; omega
    constructor
    · have := hS q 1 a 0 (by omega) hqX le_rfl hX1' (by
        simp only [Int.cast_zero, zero_div, Nat.cast_one]
        exact div_ne_zero (by exact_mod_cast ha0) hq0)
      simpa using this
    · have := hS q 1 a 1 (by omega) hqX le_rfl hX1' (by
        simp only [Int.cast_one, Nat.cast_one, div_one]
        rw [Ne, div_eq_one_iff_eq hq0]
        exact_mod_cast haq)
      simpa using this
  ext α
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion, Set.mem_Icc, majorArcs110,
    Set.mem_ofPred_eq, exists_prop, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨h0, h1⟩, q, hq1, hqX, a, hg, hdist⟩
    rw [abs_le] at hdist
    rcases Nat.lt_or_ge q 2 with hq | hq
    · have hq1' : q = 1 := by omega
      subst hq1'
      simp only [Nat.cast_one, div_one] at hdist
      have ha1 : a ≤ 1 := by
        have : (a : ℝ) < 2 := by linarith [hdist.1]
        exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
      have ha0 : 0 ≤ a := by
        have : (-1 : ℝ) < a := by linarith [hdist.2]
        have : (-1 : ℤ) < a := by exact_mod_cast this
        omega
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · left; left; push_cast at hdist; constructor <;> linarith [hdist.1, hdist.2]
      · left; right; push_cast at hdist; constructor <;> linarith [hdist.1, hdist.2]
    · right
      obtain ⟨hf0, hf1⟩ := hfar q a hq hqX hg
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hlo : 0 < (a : ℝ) / q := by
        by_contra hneg
        push Not at hneg
        rw [abs_of_nonpos hneg] at hf0
        linarith [hdist.1, hdist.2]
      have hhi : (a : ℝ) / q < 1 := by
        by_contra hneg
        push Not at hneg
        rw [abs_of_nonneg (by linarith)] at hf1
        linarith [hdist.1, hdist.2]
      have ha0 : 0 < a := by
        have : (0 : ℝ) < a := by
          have := mul_pos hlo hq0; rwa [div_mul_cancel₀ _ hq0.ne'] at this
        exact_mod_cast this
      have haq : a < q := by
        have : (a : ℝ) < q := by
          have := (div_lt_one hq0).mp hhi; exact this
        exact_mod_cast this
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha0.le
      refine ⟨⟨q, n⟩, ⟨⟨hq, Nat.le_floor hqX⟩, (show n < q by omega), ?_⟩, ?_⟩
      · rw [Int.gcd_natCast_natCast] at hg; exact hg
      · simp only [Int.cast_natCast] at hdist
        constructor <;> linarith [hdist.1, hdist.2]
  · rintro ((⟨h0, h1⟩ | ⟨h0, h1⟩) | ⟨i, ⟨⟨hi2, hin⟩, hlt, hcop⟩, h0, h1⟩)
    · refine ⟨⟨h0, by linarith⟩, 1, le_rfl, hX1', 0, by norm_num, ?_⟩
      simp only [Int.cast_zero, zero_div, sub_zero]
      rw [abs_le]; constructor <;> linarith
    · refine ⟨⟨by linarith, h1⟩, 1, le_rfl, hX1', 1, by norm_num, ?_⟩
      simp only [Int.cast_one, Nat.cast_one, div_one]
      rw [abs_le]; constructor <;> linarith
    · have hiX : (i.1 : ℝ) ≤ X := (Nat.cast_le.mpr hin).trans (Nat.floor_le (by linarith))
      have hg : Int.gcd (i.2 : ℤ) i.1 = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
      obtain ⟨hf0, hf1⟩ := hfar i.1 (i.2 : ℤ) hi2 hiX hg
      simp only [Int.cast_natCast] at hf0 hf1
      have hq0 : (0 : ℝ) < i.1 := by exact_mod_cast (by omega : 0 < i.1)
      have hlo : 0 ≤ (i.2 : ℝ) / i.1 := by positivity
      have hhi : (i.2 : ℝ) / i.1 ≤ 1 := (div_le_one hq0).mpr (by exact_mod_cast hlt.le)
      rw [abs_of_nonneg hlo] at hf0
      rw [abs_of_nonpos (by linarith)] at hf1
      refine ⟨⟨by linarith, by linarith⟩, i.1, by omega, hiX, (i.2 : ℤ), hg, ?_⟩
      simp only [Int.cast_natCast]
      rw [abs_le]; constructor <;> linarith

/-- Pages 270 to 271, step 2 of the standard method: the major arc integral over `[0, 1]` is the
sum of the integrals over the disjoint arcs, by `arcs_set_eq_proof`, `majorArcs_separated` and
`reduced_frac_eq`. PROVED. -/
theorem arc_sets_proof (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d =
        ((∫ α in (0 : ℝ)..(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)),
            primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α ^ 3 * ee (-(N : ℝ) * α)) +
          (∫ α in (1 - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..1,
            primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α ^ 3 * ee (-(N : ℝ) * α)) +
          ∑ q ∈ Finset.Icc 2 ⌊(Real.log N ^ d)⌋₊,
            ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
              ∫ α in ((a : ℝ) / q - (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..((a : ℝ) / q + (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))),
                primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) α ^ 3 *
                  ee (-(N : ℝ) * α)).re := by
  obtain ⟨N₁, hset⟩ := arcs_set_eq_proof d c hd hc
  obtain ⟨N₂, hsep⟩ := majorArcs_separated d c hd hc.le
  refine ⟨max (max N₁ N₂) (Real.exp 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN1' : (1 : ℝ) ≤ N := by have := Real.exp_one_gt_d9; linarith
  have hS := hsep N hN2
  have hE := hset N hN1
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX1 : (1 : ℝ) ≤ X := Real.one_le_rpow hL1 hd.le
  have hUpos : 0 < U := mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _)
  have hw0 : 0 ≤ w := by have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) (4 : ℝ); positivity
  -- separation in natural number form
  have hSn : ∀ q q' a a' : ℕ, 1 ≤ q → (q : ℝ) ≤ X → 1 ≤ q' → (q' : ℝ) ≤ X →
      (a : ℝ) / q ≠ (a' : ℝ) / q' → 2 * w < |(a : ℝ) / q - (a' : ℝ) / q'| := by
    intro q q' a a' h1 h2 h3 h4 hne
    have := hS q q' (a : ℤ) (a' : ℤ) h1 h2 h3 h4 (by simpa only [Int.cast_natCast] using hne)
    simpa only [Int.cast_natCast] using this
  have hdisjR : ∀ x y : ℝ, 2 * w < |x - y| →
      Disjoint (Set.Icc (x - w) (x + w)) (Set.Icc (y - w) (y + w)) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro z hz hz'
    have : |x - y| ≤ 2 * w := abs_le.mpr ⟨by linarith [hz.1, hz'.2, hz.2, hz'.1], by linarith [hz.2, hz'.1, hz.1, hz'.2]⟩
    linarith
  set I := (Finset.Icc 2 ⌊X⌋₊).sigma
    (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)) with hI
  have hmemI : ∀ i ∈ I, 2 ≤ i.1 ∧ (i.1 : ℝ) ≤ X ∧ 1 ≤ i.2 ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    intro i hi
    rw [hI, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨h2, hn⟩, hlt, hcop⟩ := hi
    refine ⟨h2, (Nat.cast_le.mpr hn).trans (Nat.floor_le (by linarith)), ?_, hlt, hcop⟩
    rcases Nat.eq_zero_or_pos i.2 with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop; omega
    · exact h0
  have hpos : ∀ i ∈ I, 0 < (i.2 : ℝ) / i.1 ∧ (i.2 : ℝ) / i.1 < 1 := by
    intro i hi
    obtain ⟨h2, -, h1, hlt, -⟩ := hmemI i hi
    have hq : (0 : ℝ) < i.1 := by exact_mod_cast (by omega : 0 < i.1)
    refine ⟨div_pos (by exact_mod_cast h1) hq, (div_lt_one hq).mpr (by exact_mod_cast hlt)⟩
  have hA : Set.Icc (0 : ℝ) w ⊆ Set.Icc (((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - w)
      (((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) + w) := by
    intro z hz; simp only [Nat.cast_zero, Nat.cast_one, zero_div, zero_sub, zero_add,
      Set.mem_Icc] at hz ⊢; constructor <;> linarith [hz.1, hz.2]
  have hB : Set.Icc (1 - w) 1 ⊆ Set.Icc (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - w)
      (((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) + w) := by
    intro z hz; simp only [Nat.cast_one, div_one, Set.mem_Icc] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  have hAB : Disjoint (Set.Icc (0 : ℝ) w) (Set.Icc (1 - w) 1) :=
    (hdisjR _ _ (hSn 1 1 0 1 le_rfl (by exact_mod_cast hX1) le_rfl (by exact_mod_cast hX1)
      (by norm_num))).mono hA hB
  have hAC : ∀ i ∈ I, Disjoint (Set.Icc (0 : ℝ) w)
      (Set.Icc ((i.2 : ℝ) / i.1 - w) ((i.2 : ℝ) / i.1 + w)) := by
    intro i hi
    obtain ⟨h2, hX, -, -, -⟩ := hmemI i hi
    have := (hpos i hi).1
    exact (hdisjR _ _ (hSn 1 i.1 0 i.2 le_rfl (by exact_mod_cast hX1) (by omega) hX
      (by simp only [Nat.cast_zero, zero_div]; exact this.ne))).mono hA le_rfl
  have hBC : ∀ i ∈ I, Disjoint (Set.Icc (1 - w) 1)
      (Set.Icc ((i.2 : ℝ) / i.1 - w) ((i.2 : ℝ) / i.1 + w)) := by
    intro i hi
    obtain ⟨h2, hX, -, -, -⟩ := hmemI i hi
    have := (hpos i hi).2
    exact (hdisjR _ _ (hSn 1 i.1 1 i.2 le_rfl (by exact_mod_cast hX1) (by omega) hX
      (by simp only [Nat.cast_one, div_one]; exact this.ne'))).mono hB le_rfl
  have hCC : Set.Pairwise (I : Set (Σ _ : ℕ, ℕ)) (Function.onFun Disjoint
      fun i : (Σ _ : ℕ, ℕ) => Set.Icc ((i.2 : ℝ) / i.1 - w) ((i.2 : ℝ) / i.1 + w)) := by
    intro i hi j hj hij
    obtain ⟨hi2, hiX, -, -, hic⟩ := hmemI i hi
    obtain ⟨hj2, hjX, -, -, hjc⟩ := hmemI j hj
    refine hdisjR _ _ (hSn i.1 j.1 i.2 j.2 (by omega) hiX (by omega) hjX ?_)
    intro heq
    obtain ⟨h1, h2⟩ := reduced_frac_eq i.1 j.1 i.2 j.2 (by omega) (by omega) hic hjc heq
    apply hij
    obtain ⟨q, a⟩ := i
    obtain ⟨q', a'⟩ := j
    simp only at h1 h2
    subst h1 h2
    rfl
  have hgc : Continuous fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    have := primeSum_continuous110 N U
    unfold ee; fun_prop
  have hIcc : ∀ x y : ℝ, x ≤ y → (∫ α in Set.Icc x y, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) =
      ∫ α in x..y, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    intro x y h
    rw [intervalIntegral.integral_of_le h, MeasureTheory.integral_Icc_eq_integral_Ioc]
  show (∫ α in Set.Icc (0 : ℝ) 1 ∩ majorArcs110 N U d,
      primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)).re = _
  rw [hE, MeasureTheory.setIntegral_union
      (Set.disjoint_union_left.mpr ⟨Set.disjoint_iUnion₂_right.mpr hAC,
        Set.disjoint_iUnion₂_right.mpr hBC⟩)
      (Finset.measurableSet_biUnion I (fun i _ => measurableSet_Icc))
      ((hgc.integrableOn_Icc).union (hgc.integrableOn_Icc))
      ((MeasureTheory.integrableOn_finset_iUnion).mpr fun i _ => hgc.integrableOn_Icc),
    MeasureTheory.setIntegral_union hAB measurableSet_Icc hgc.integrableOn_Icc
      hgc.integrableOn_Icc,
    MeasureTheory.integral_biUnion_finset I (fun i _ => measurableSet_Icc) hCC
      (fun i _ => hgc.integrableOn_Icc),
    Finset.sum_sigma, hIcc 0 w hw0, hIcc (1 - w) 1 (by linarith)]
  congr 2
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  exact hIcc _ _ (by linarith)

/-- Page 271, the arc decomposition in the shifted form `α = a/q + λ`, `|λ| ≤ w`, PROVED from
`arc_sets_proof`: the two half arcs at `0` and `1` join into `[-w, w]` by periodicity. -/
theorem arc_decomposition_proof (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d =
        (∑ q ∈ Finset.Icc 1 ⌊Real.log N ^ d⌋₊,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∫ lam in (-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..
              (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)),
              primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ((a : ℝ) / q + lam) ^ 3 *
                ee (-(N : ℝ) * ((a : ℝ) / q + lam))).re := by
  obtain ⟨N₁, h⟩ := arc_sets_proof d c hd hc
  refine ⟨max N₁ (Real.exp 1), fun N hN => ?_⟩
  rw [h N ((le_max_left _ _).trans hN)]
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by
    push_cast; exact Real.one_le_rpow hL1 hd.le)
  have hgc : Continuous fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    have := primeSum_continuous110 N U
    unfold ee; fun_prop
  have hshift : ∀ (q a : ℕ), (∫ lam in (-w)..w,
      primeSum110 N U ((a : ℝ) / q + lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam))) =
      ∫ α in ((a : ℝ) / q - w)..((a : ℝ) / q + w),
        primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    intro q a
    have := intervalIntegral.integral_comp_add_left
      (fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) ((a : ℝ) / q) (a := -w) (b := w)
    beta_reduce at this
    rw [this, ← sub_eq_add_neg]
  rw [Finset.Icc_eq_cons_Ioc hX1, Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
  simp_rw [hshift]
  have hone : (∑ a ∈ (Finset.range 1).filter (fun a => Nat.Coprime a 1),
      ∫ α in ((a : ℝ) / (1 : ℕ) - w)..((a : ℝ) / (1 : ℕ) + w),
        primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) =
      ∫ α in (-w)..w, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    simp
  rw [hone, ← intervalIntegral.integral_add_adjacent_intervals (a := -w) (b := 0) (c := w)
    (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  have hper : (∫ α in (-w)..0, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) =
      ∫ α in (1 - w)..1, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) := by
    have := intervalIntegral.integral_comp_add_right
      (fun α : ℝ => primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) (1 : ℝ) (a := -w) (b := 0)
    beta_reduce at this
    simp_rw [majorIntegrand_periodic] at this
    rw [this]
    congr 1 <;> ring
  rw [hper]
  congr 1
  simp only [Nat.reduceAdd]
  ring

/-- The window `[N/3 - U, N/3 + U]` holds at most `2U + 1` integers, page 271. PROVED. -/
theorem card_Icc_window_le (N : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ((Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊).card : ℝ) ≤ 2 * U + 1 := by
  rw [Nat.card_Icc]
  have hb : 0 ≤ (N : ℝ) / 3 + U := by positivity
  rcases Nat.eq_zero_or_pos (⌊(N : ℝ) / 3 + U⌋₊ + 1 - ⌈(N : ℝ) / 3 - U⌉₊) with h0 | hpos
  · rw [h0]; push_cast; linarith
  · have hle : ⌈(N : ℝ) / 3 - U⌉₊ ≤ ⌊(N : ℝ) / 3 + U⌋₊ + 1 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    have h1 := Nat.floor_le hb
    have h2 := Nat.le_ceil ((N : ℝ) / 3 - U)
    linarith

/-- Page 271, `|S(α)| ≤ 2U + 1`, the trivial bound. PROVED. -/
theorem primeSum_norm_le (N : ℕ) (U α : ℝ) (hU : 0 ≤ U) :
    ‖primeSum110 N U α‖ ≤ 2 * U + 1 := by
  unfold primeSum110
  refine (norm_sum_le _ _).trans ?_
  simp only [ee_norm110, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine le_trans ?_ (card_Icc_window_le N U hU)
  unfold Win
  exact_mod_cast Finset.card_filter_le _ _

/-- Page 271, `|v(λ)| ≤ 2(2U + 1)`, since `1/log n ≤ 2` for `n ≥ 2`, and Lean's `log 0 = log 1 = 0`
makes those terms `0`. PROVED. -/
theorem vSum_norm_le (N : ℕ) (U lam : ℝ) (hU : 0 ≤ U) :
    ‖vSum N U lam‖ ≤ 2 * (2 * U + 1) := by
  unfold vSum
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ‖ee ((n : ℝ) * lam) / (Real.log n : ℂ)‖ ≤ 2 := by
    intro n _
    rw [norm_div, ee_norm110, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have hl : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast h)
      have := Real.log_two_gt_d9
      rw [abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have := card_Icc_window_le N U hU
  linarith

/-- `|x³ - y³| ≤ 3 M² |x - y|` for `|x|, |y| ≤ M`, page 271. PROVED. -/
theorem cube_diff_norm (x y : ℂ) (M : ℝ) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖x ^ 3 - y ^ 3‖ ≤ 3 * M ^ 2 * ‖x - y‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hx
  have he : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [he, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_add₃_le).trans ?_
  rw [norm_pow, norm_mul, norm_pow]
  have h0 := norm_nonneg x
  have h1 := norm_nonneg y
  nlinarith [mul_le_mul hx hy h1 hM]

/-- `|μ(q)/φ(q)| ≤ 1`, page 271. PROVED. -/
theorem moebius_div_norm_le (q : ℕ) (hq : 1 ≤ q) :
    ‖(((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hφ : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [abs_of_pos (a := (Nat.totient q : ℝ)) (by linarith), div_le_one (by linarith)]
  have : |(μ q : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  linarith

/-- Page 271, step 2 of the standard method, the error on one arc, PROVED from `MajorArcApprox`
at `A = 2d + 8`: `|S³ - (μ(q)/φ(q) v)³| ≤ 3 M² |S - μ(q)/φ(q) v|` with `M = 2(2U + 1) ≤ 6U`,
over an interval of length `2 L⁴/U`, giving `216 |K| U² L^{-4} / L^{2d}` per arc. -/
theorem arc_error_proof (h1 : MajorArcApprox) (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    ∃ K N₀ : ℝ, 0 ≤ K ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (q a : ℕ), 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ d → Nat.Coprime a q →
      ‖∫ lam in (-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)))..
            (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)),
          (primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) *
              vSum N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam) ^ 3) *
            ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖
        ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ) /
            (Real.log N ^ d) ^ 2 := by
  obtain ⟨K0, N0, hK0⟩ := h1 d c (2 * d + 8) hd hc (by linarith)
  refine ⟨216 * |K0|, max N0 (Real.exp 1), by positivity, fun N hN q a hq hqX hcop => ?_⟩
  have hN0 : N0 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN1 : (1 : ℝ) ≤ N := by have := Real.exp_one_gt_d9; linarith
  have hLpos : 0 < Real.log N := by linarith
  have hgcd : Int.gcd (a : ℤ) q = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
  have hA := fun lam => hK0 N q (a : ℤ) lam hN0 hq hqX hgcd
  simp only [Int.cast_natCast] at hA
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  set P := L ^ (-(2 * d + 8)) with hP
  have hU1 : 1 ≤ U := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1 (by norm_num))
    (Real.one_le_rpow hL1 hc.le)
  have hUpos : 0 < U := by linarith
  have hw0 : 0 ≤ w := by have := Real.rpow_nonneg hLpos.le (4 : ℝ); positivity
  have hP0 : 0 ≤ P := Real.rpow_nonneg hLpos.le _
  set M := 2 * (2 * U + 1) with hM
  have hpt : ∀ lam ∈ Set.uIoc (-w) w,
      ‖(primeSum110 N U ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) *
          ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖ ≤ 3 * M ^ 2 * (|K0| * U * P) := by
    intro lam hlam
    rw [Set.uIoc_of_le (by linarith)] at hlam
    have hl : |lam| ≤ w := abs_le.mpr ⟨le_of_lt hlam.1, hlam.2⟩
    rw [norm_mul, ee_norm110, mul_one]
    have hS : ‖primeSum110 N U ((a : ℝ) / q + lam)‖ ≤ M := by
      have := primeSum_norm_le N U ((a : ℝ) / q + lam) hUpos.le; linarith
    have hv : ‖(((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam)‖ ≤ M := by
      rw [norm_mul]
      have h1' := moebius_div_norm_le q hq
      have h2' := vSum_norm_le N U lam hUpos.le
      calc _ ≤ 1 * M := mul_le_mul h1' h2' (norm_nonneg _) zero_le_one
        _ = M := one_mul _
    refine (cube_diff_norm _ _ M hS hv).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (hA lam hl).trans ?_
    have := le_abs_self K0
    have : 0 ≤ U * P := by positivity
    nlinarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans ?_
  have hpow : P * L ^ (4 : ℝ) = L ^ (-4 : ℝ) / X ^ 2 := by
    rw [hP, hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_add hLpos,
      div_eq_mul_inv, ← Real.rpow_neg hLpos.le, ← Real.rpow_add hLpos]
    congr 1; push_cast; ring
  have hQ : 0 ≤ L ^ (-4 : ℝ) / X ^ 2 := by
    have := Real.rpow_nonneg hLpos.le (-4 : ℝ); positivity
  have hM2 : M ^ 2 ≤ 36 * U ^ 2 := by nlinarith
  rw [show w - -w = 2 * w by ring, abs_of_nonneg (a := 2 * w) (by linarith)]
  calc 3 * M ^ 2 * (|K0| * U * P) * (2 * w) = 6 * M ^ 2 * |K0| * (P * L ^ (4 : ℝ)) := by
        rw [hw]; field_simp; ring
    _ = 6 * M ^ 2 * |K0| * (L ^ (-4 : ℝ) / X ^ 2) := by rw [hpow]
    _ ≤ 6 * (36 * U ^ 2) * |K0| * (L ^ (-4 : ℝ) / X ^ 2) := by gcongr
    _ = 216 * |K0| * U ^ 2 * L ^ (-4 : ℝ) / X ^ 2 := by ring

/-- `μ(q)³ = μ(q)`, page 271. PROVED. -/
theorem moebius_cube (q : ℕ) : (μ q : ℤ) ^ 3 = μ q := by
  by_cases h : Squarefree q
  · have h2 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    calc (μ q : ℤ) ^ 3 = μ q * μ q ^ 2 := by ring
      _ = μ q := by rw [h2, mul_one]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; norm_num

/-- Page 271, the main term on the arcs of one `q`: summing `e(-aN/q)` over `a` gives `c_q(N)`,
and `(μ(q)/φ(q))³ = μ(q)/φ(q)³`. PROVED. -/
theorem arc_main_sum (N q : ℕ) (hq : 1 ≤ q) (U w : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ lam in (-w)..w, (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 *
        ee (-(N : ℝ) * ((a : ℝ) / q + lam))) =
      (((μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N : ℝ) : ℂ) *
        ∫ lam in (-w)..w, vSum N U lam ^ 3 * ee (-(N : ℝ) * lam) := by
  have hpt : ∀ a : ℕ, ∀ lam : ℝ,
      (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 *
        ee (-(N : ℝ) * ((a : ℝ) / q + lam)) =
      (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ)) ^ 3 * ee (-((a : ℝ) * N / q)) *
        (vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)) := by
    intro a lam
    rw [show -(N : ℝ) * ((a : ℝ) / q + lam) = -((a : ℝ) * N / q) + -(N : ℝ) * lam by ring,
      ee_add110]
    ring
  simp_rw [hpt, intervalIntegral.integral_const_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ramanujan_sum_complex q N hq]
  have hr : ((μ q : ℝ) / (Nat.totient q : ℝ)) ^ 3 * ramanujanC q N =
      (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N := by
    rw [div_pow, ← Int.cast_pow, moebius_cube]
  rw [← hr]
  push_cast
  ring

/-- Page 271, step 2, `MajorAssembly` from `MajorArcApprox` PROVED, conditional only on its hypothesis,
the cited step 1. -/
theorem majorAssembly_of_approx_split (h1 : MajorArcApprox) : MajorAssembly := by
  refine ⟨1, one_pos, fun d hd c hc => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  obtain ⟨N₁, hdec⟩ := arc_decomposition_proof d c hd0 hc
  obtain ⟨K, N₂, hK0, hK⟩ := arc_error_proof h1 d c hd0 hc
  refine ⟨K, max (max N₁ N₂) 3, fun N _ hN => ?_⟩
  have hN1 : N₁ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hK' := hK N hN2
  rw [hdec N hN1]
  set L := Real.log N with hL
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set w := L ^ (4 : ℝ) / U with hw
  set X := L ^ d with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hLpos d
  have hcont : ∀ (q a : ℕ), Continuous fun lam : ℝ =>
      primeSum110 N U ((a : ℝ) / q + lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam)) := by
    intro q a
    have h0 : Continuous fun lam : ℝ => primeSum110 N U ((a : ℝ) / q + lam) :=
      (primeSum_continuous110 N U).comp (by fun_prop)
    unfold ee
    fun_prop
  have hcontv : ∀ (q a : ℕ), Continuous fun lam : ℝ =>
      (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam)) := by
    intro q a
    unfold vSum ee
    fun_prop
  have harc : ∀ q ∈ Finset.Icc 1 ⌊X⌋₊, ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      (∫ lam in (-w)..w, primeSum110 N U ((a : ℝ) / q + lam) ^ 3 *
          ee (-(N : ℝ) * ((a : ℝ) / q + lam))) =
        (∫ lam in (-w)..w, (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3 * ee (-(N : ℝ) * ((a : ℝ) / q + lam))) +
        ∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 - (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) *
          ee (-(N : ℝ) * ((a : ℝ) / q + lam)) := by
    intro q _ a _
    rw [← intervalIntegral.integral_add ((hcontv q a).intervalIntegrable _ _)]
    · congr 1; funext lam; ring
    · have := ((hcont q a).sub (hcontv q a))
      refine (this.congr ?_).intervalIntegrable _ _
      intro lam; simp only [Pi.sub_apply]; ring
  rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (harc q hq))]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun q hq => arc_main_sum N q (Finset.mem_Icc.mp hq).1 U w),
    ← Finset.sum_mul, ← Complex.ofReal_sum, Complex.add_re, Complex.re_ofReal_mul]
  set E := ∑ q ∈ Finset.Icc 1 ⌊X⌋₊, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 - (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) *
        ee (-(N : ℝ) * ((a : ℝ) / q + lam)) with hE
  have hmain : singTrunc N X * singInt N U w =
      (∑ q ∈ Finset.Icc 1 ⌊X⌋₊, (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N) *
        (∫ lam in (-w)..w, vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)).re := rfl
  rw [hmain, add_sub_cancel_left]
  set B := K * U ^ 2 * L ^ (-4 : ℝ) / X ^ 2 with hB
  have hB0 : 0 ≤ B := by
    have := Real.rpow_nonneg hLpos.le (-4 : ℝ); positivity
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX.le
  have hnorm : ‖E‖ ≤ (⌊X⌋₊ : ℝ) * ((⌊X⌋₊ : ℝ) * B) := by
    rw [hE]
    refine (norm_sum_le _ _).trans ?_
    have hq : ∀ q ∈ Finset.Icc 1 ⌊X⌋₊,
        ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) * ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖ ≤
          (⌊X⌋₊ : ℝ) * B := by
      intro q hq
      obtain ⟨hq1, hqX⟩ := Finset.mem_Icc.mp hq
      have hqX' : (q : ℝ) ≤ X := (Nat.cast_le.mpr hqX).trans hfl
      refine (norm_sum_le _ _).trans ?_
      have hle : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∫ lam in (-w)..w, (primeSum110 N U ((a : ℝ) / q + lam) ^ 3 -
            (((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) * vSum N U lam) ^ 3) * ee (-(N : ℝ) * ((a : ℝ) / q + lam))‖ ≤ B := by
        intro a ha
        exact hK' q a hq1 hqX' (Finset.mem_filter.mp ha).2
      refine (Finset.sum_le_sum hle).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ ⌊X⌋₊ := by
        have := (Finset.card_filter_le (Finset.range q) (fun a => Nat.Coprime a q))
        rw [Finset.card_range] at this
        exact_mod_cast this.trans hqX
      exact mul_le_mul_of_nonneg_right hc hB0
    refine (Finset.sum_le_sum hq).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    simp
  have hfinal : (⌊X⌋₊ : ℝ) * ((⌊X⌋₊ : ℝ) * B) ≤ K * U ^ 2 * L ^ (-4 : ℝ) := by
    have h0 : (0 : ℝ) ≤ ⌊X⌋₊ := Nat.cast_nonneg _
    calc (⌊X⌋₊ : ℝ) * ((⌊X⌋₊ : ℝ) * B) ≤ X * (X * B) :=
          mul_le_mul hfl (mul_le_mul_of_nonneg_right hfl hB0) (by positivity) hX.le
      _ = K * U ^ 2 * L ^ (-4 : ℝ) := by rw [hB]; field_simp
  exact (Complex.abs_re_le_norm E).trans (hnorm.trans hfinal)

end

/-- LEAF: Page 271, step 2 of the standard method, from step 1. HARD. The arcs `I(q, a)` are
disjoint for large `N`; the two half arcs at 0 and 1 form one arc by periodicity; on each arc
`|S³ - (μ(q)/φ(q) v)³| ≪ U² · U L^{-A}`, over at most `L^{2d}` arcs of length `2 L⁴/U`, so
`A = 2d + 8` suffices; then sum `e(-aN/q)` over `a` to get `c_q(N)`, and `μ(q)³ = μ(q)`. -/
theorem majorAssembly_of_approx (h1 : MajorArcApprox) : MajorAssembly :=
  majorAssembly_of_approx_split h1

open Finset Filter MeasureTheory

private theorem hex_step (U y : ℝ) :
    |((2 * U * (y + 1) - (y + 1) * |y + 1| / 2) - (2 * U * y - y * |y| / 2)) - (2 * U - |y|)|
      ≤ 1 := by
  rcases abs_cases (y + 1) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases y with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> rw [h1, h2] <;>
  rw [abs_le] <;> constructor <;> nlinarith
private theorem tele (F : ℕ → ℝ) (a : ℕ) : ∀ k : ℕ,
    ∑ n ∈ Finset.Ico a (a + k), (F (n + 1) - F n) = F (a + k) - F a
  | 0 => by simp
  | k + 1 => by
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), tele F a k]
    ring

set_option maxHeartbeats 2000000 in
/-- Step 3 by the elementary route: the full period integral counts window triples, the hexagon
count is `3U² + O(U)`, the weights are `L⁻³(1 + O(L⁻¹))`, and the tail beyond `L⁴/U` is
`O(U² L⁻⁴)` from `v(λ) ≪ 1/(|λ| L)`. -/
theorem singIntEval_leaf : SingIntEval := by
  let si : ℕ → ℝ → ℝ → ℂ := fun N U lam => vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)
  have siD : ∀ (N : ℕ) (U lam : ℝ), si N U lam =
      vSum N U lam ^ 3 * ee (-(N : ℝ) * lam) := fun N U lam => rfl
  let wt : ℕ → ℝ → ℝ := fun N U =>
    ∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          if n₁ + n₂ + n₃ = N then 1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) else 0
  have wtD : ∀ (N : ℕ) (U : ℝ), wt N U =
      (∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          if n₁ + n₂ + n₃ = N then 1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) else 0) := fun N U => rfl
  let win : ℕ → ℝ → ℝ := fun N U =>
    ∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0
  have winD : ∀ (N : ℕ) (U : ℝ), win N U =
      (∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) := fun N U => rfl
  have si_continuous (N : ℕ) (U : ℝ) : Continuous (si N U) := by
    have h : si N U = fun lam => vSum N U lam ^ 3 * ee (-(N : ℝ) * lam) := by
      funext lam; exact siD N U lam
    rw [h]
    unfold vSum ee
    fun_prop
  have singIntEval_of_parts (h1 : ∀ (N : ℕ) (U : ℝ), (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), si N U lam).re = wt N U) (h2 :
      ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |wt N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) - 3 * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-3 : ℝ)|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ))
      (h3 :
      ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |(∫ lam in (-(1 / 2 : ℝ))..(-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))),
        si N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam).re +
      (∫ lam in (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))..(1 / 2), si N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam).re|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)) : SingIntEval := by
    intro c hc
    obtain ⟨K2, N2, hK2⟩ := h2 c hc
    obtain ⟨K3, N3, hK3⟩ := h3 c hc
    refine ⟨K2 + K3, max N2 N3, fun N hN => ?_⟩
    set U := (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c
    set w := Real.log N ^ (4 : ℝ) / U
    have hint : ∀ a b : ℝ, IntervalIntegrable (si N U) MeasureTheory.volume a b :=
      fun a b => (si_continuous N U).intervalIntegrable a b
    have hsplit : (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), si N U lam) =
        (∫ lam in (-(1 / 2 : ℝ))..(-w), si N U lam) +
        (∫ lam in (-w)..w, si N U lam) +
        (∫ lam in w..(1 / 2), si N U lam) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
        intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
    have hfull := h1 N U
    rw [hsplit, Complex.add_re, Complex.add_re] at hfull
    have hsi : singInt N U w = (∫ lam in (-w)..w, si N U lam).re := rfl
    have e2 := hK2 N ((le_max_left _ _).trans hN)
    have e3 := hK3 N ((le_max_right _ _).trans hN)
    rw [hsi]
    have : (∫ lam in (-w)..w, si N U lam).re - 3 * U ^ 2 * Real.log N ^ (-3 : ℝ) =
        (wt N U - 3 * U ^ 2 * Real.log N ^ (-3 : ℝ)) -
        ((∫ lam in (-(1 / 2 : ℝ))..(-w), si N U lam).re +
          (∫ lam in w..(1 / 2), si N U lam).re) := by linarith
    rw [this]
    calc _ ≤ |wt N U - 3 * U ^ 2 * Real.log N ^ (-3 : ℝ)| +
          |(∫ lam in (-(1 / 2 : ℝ))..(-w), si N U lam).re +
            (∫ lam in w..(1 / 2), si N U lam).re| := abs_sub _ _
      _ ≤ K2 * U ^ 2 * Real.log N ^ (-4 : ℝ) + K3 * U ^ 2 * Real.log N ^ (-4 : ℝ) :=
          add_le_add e2 e3
      _ = _ := by ring

  have ee_integral_half (k : ℤ) :
      (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), ee ((k : ℝ) * lam)) = if k = 0 then 1 else 0 := by
    split_ifs with hk
    · subst hk; simp [ee]; norm_num
    · have hz : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
          (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
      have he : ∀ α : ℝ, ee ((k : ℝ) * α) =
          Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * (α : ℂ)) := by
        intro α; simp only [ee, Complex.ofReal_mul, Complex.ofReal_intCast]; congr 1; ring
      simp_rw [he]
      rw [integral_exp_mul_complex hz]
      have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((-(1 / 2 : ℝ)) : ℂ)) := by
        rw [Complex.exp_eq_exp_iff_exists_int]
        exact ⟨k, by push_cast; ring⟩
      rw [h1]; push_cast; simp
  have singIntegrand_expand (N : ℕ) (U lam : ℝ) :
      si N U lam =
        ∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
            ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
              ((1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) : ℝ) : ℂ) *
                ee ((((n₁ + n₂ + n₃ : ℤ) - N : ℤ) : ℝ) * lam) := by
    rw [siD]
    unfold vSum
    simp only [pow_three, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n₁ _
    apply Finset.sum_congr rfl; intro n₂ _
    apply Finset.sum_congr rfl; intro n₃ _
    have hE : ee ((((n₁ + n₂ + n₃ : ℤ) - N : ℤ) : ℝ) * lam) =
        ee ((n₁ : ℝ) * lam) * ee ((n₂ : ℝ) * lam) * ee ((n₃ : ℝ) * lam) * ee (-(N : ℝ) * lam) := by
      rw [← ee_add110, ← ee_add110, ← ee_add110]; congr 1; push_cast; ring
    rw [hE]
    push_cast
    ring
  have fullPeriodIdentity_proof : ∀ (N : ℕ) (U : ℝ), (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), si N U lam).re = wt N U := by
    intro N U
    set W := Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊
    have hc : ∀ (k : ℤ) (c : ℝ), IntervalIntegrable (fun lam : ℝ => (c : ℂ) * ee ((k : ℝ) * lam))
        volume (-(1 / 2 : ℝ)) (1 / 2) := by
      intro k c
      apply Continuous.intervalIntegrable
      unfold ee; fun_prop
    have hterm : ∀ n₁ n₂ n₃ : ℕ,
        (∫ lam in (-(1 / 2 : ℝ))..(1 / 2),
          ((1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) : ℝ) : ℂ) *
            ee ((((n₁ + n₂ + n₃ : ℤ) - N : ℤ) : ℝ) * lam)).re =
        if n₁ + n₂ + n₃ = N then 1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) else 0 := by
      intro n₁ n₂ n₃
      rw [intervalIntegral.integral_const_mul, ee_integral_half]
      by_cases h : n₁ + n₂ + n₃ = N
      · have h0 : ((n₁ + n₂ + n₃ : ℤ) - N : ℤ) = 0 := by omega
        rw [if_pos h0, if_pos h, mul_one, Complex.ofReal_re]
      · have h0 : ((n₁ + n₂ + n₃ : ℤ) - N : ℤ) ≠ 0 := by omega
        rw [if_neg h0, if_neg h, mul_zero, Complex.zero_re]
    simp_rw [singIntegrand_expand]
    rw [intervalIntegral.integral_finsetSum (fun n₁ _ => ?_)]
    · rw [Complex.re_sum]
      rw [wtD]
      apply Finset.sum_congr rfl; intro n₁ _
      rw [intervalIntegral.integral_finsetSum (fun n₂ _ => ?_), Complex.re_sum]
      · apply Finset.sum_congr rfl; intro n₂ _
        rw [intervalIntegral.integral_finsetSum (fun n₃ _ => hc _ _), Complex.re_sum]
        apply Finset.sum_congr rfl; intro n₃ _
        exact hterm n₁ n₂ n₃
      · apply Continuous.intervalIntegrable; unfold ee; fun_prop
    · apply Continuous.intervalIntegrable; unfold ee; fun_prop

  have windowTriples_nonneg (N : ℕ) (U : ℝ) : 0 ≤ win N U := by
    rw [winD]
    refine Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_
    split_ifs <;> norm_num
  have count_inner (N : ℕ) (U : ℝ) (hU : 1 ≤ U) (hU12 : U ≤ (N : ℝ) / 12) (n₁ : ℕ)
      (h₁ : n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊) :
      |(∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) - (2 * U - |(n₁ : ℝ) - N / 3|)| ≤ 3 := by
    set a := ⌈(N : ℝ) / 3 - U⌉₊ with ha
    set b := ⌊(N : ℝ) / 3 + U⌋₊ with hb
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have ha1 : (N : ℝ) / 3 - U ≤ a := Nat.le_ceil _
    have ha2 : (a : ℝ) < (N : ℝ) / 3 - U + 1 := Nat.ceil_lt_add_one (by linarith)
    have hb1 : (b : ℝ) ≤ (N : ℝ) / 3 + U := Nat.floor_le (by linarith)
    have hb2 : (N : ℝ) / 3 + U < b + 1 := Nat.lt_floor_add_one _
    have h2b : 2 * b ≤ N := by
      have : ((2 * b : ℕ) : ℝ) ≤ N := by push_cast; linarith
      exact_mod_cast this
    rw [Finset.mem_Icc] at h₁
    have hn1a : (a : ℝ) ≤ n₁ := by exact_mod_cast h₁.1
    have hn1b : (n₁ : ℝ) ≤ b := by exact_mod_cast h₁.2
    have inner : ∀ n₂ ∈ Finset.Icc a b, (∑ n₃ ∈ Finset.Icc a b,
        if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) =
          if N - (n₁ + n₂) ∈ Finset.Icc a b then 1 else 0 := by
      intro n₂ h₂
      rw [Finset.mem_Icc] at h₂
      rw [← Finset.sum_ite_eq' (Finset.Icc a b) (N - (n₁ + n₂)) (fun _ => (1 : ℝ))]
      apply Finset.sum_congr rfl
      intro n₃ _
      apply if_congr _ rfl rfl
      omega
    rw [Finset.sum_congr rfl inner, Finset.sum_boole]
    have hfilt : (Finset.Icc a b).filter (fun n₂ => N - (n₁ + n₂) ∈ Finset.Icc a b) =
        Finset.Icc (max a (N - b - n₁)) (min b (N - a - n₁)) := by
      ext n₂
      simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]
      omega
    rw [hfilt, Nat.card_Icc]
    have cmin : ((min b (N - a - n₁) : ℕ) : ℝ) = min (b : ℝ) ((N : ℝ) - a - n₁) := by
      rw [Nat.cast_min]
      congr 1
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast; ring
    have cmax : ((max a (N - b - n₁) : ℕ) : ℝ) = max (a : ℝ) ((N : ℝ) - b - n₁) := by
      rw [Nat.cast_max]
      congr 1
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast; ring
    rcases le_or_gt (max a (N - b - n₁)) (min b (N - a - n₁) + 1) with h | h
    · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one, cmin, cmax]
      rcases min_cases (b : ℝ) ((N : ℝ) - a - n₁) with ⟨hm, hm'⟩ | ⟨hm, hm'⟩ <;>
      rcases max_cases (a : ℝ) ((N : ℝ) - b - n₁) with ⟨hM, hM'⟩ | ⟨hM, hM'⟩ <;>
      rw [hm, hM] <;>
      rcases abs_cases ((n₁ : ℝ) - N / 3) with ⟨hA, hA'⟩ | ⟨hA, hA'⟩ <;> rw [hA] <;>
      rw [abs_le] <;> constructor <;> linarith
    · have h' : (min b (N - a - n₁) + 1 : ℝ) < max a (N - b - n₁) := by exact_mod_cast h
      rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      rw [Nat.cast_min, Nat.cast_max] at h'
      have e1 : ((N - a - n₁ : ℕ) : ℝ) = (N : ℝ) - a - n₁ := by
        rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
      have e2 : ((N - b - n₁ : ℕ) : ℝ) = (N : ℝ) - b - n₁ := by
        rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
      rw [e1, e2] at h'
      rcases min_cases (b : ℝ) ((N : ℝ) - a - n₁) with ⟨hm, hm'⟩ | ⟨hm, hm'⟩ <;>
      rcases max_cases (a : ℝ) ((N : ℝ) - b - n₁) with ⟨hM, hM'⟩ | ⟨hM, hM'⟩ <;>
      rw [hm, hM] at h' <;>
      rcases abs_cases ((n₁ : ℝ) - N / 3) with ⟨hA, hA'⟩ | ⟨hA, hA'⟩ <;> rw [hA] <;>
      rw [abs_le] <;> constructor <;> linarith

  have windowTriples_count : ∃ C : ℝ, ∀ (N : ℕ) (U : ℝ), 1 ≤ U → U ≤ (N : ℝ) / 12 →
      |win N U - 3 * U ^ 2| ≤ C * U := by
    refine ⟨14, fun N U hU hU12 => ?_⟩
    set a := ⌈(N : ℝ) / 3 - U⌉₊ with ha
    set b := ⌊(N : ℝ) / 3 + U⌋₊ with hb
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have ha1 : (N : ℝ) / 3 - U ≤ a := Nat.le_ceil _
    have ha2 : (a : ℝ) < (N : ℝ) / 3 - U + 1 := Nat.ceil_lt_add_one (by linarith)
    have hb1 : (b : ℝ) ≤ (N : ℝ) / 3 + U := Nat.floor_le (by linarith)
    have hb2 : (N : ℝ) / 3 + U < b + 1 := Nat.lt_floor_add_one _
    have hW : win N U = ∑ n₁ ∈ Finset.Icc a b, ∑ n₂ ∈ Finset.Icc a b,
        ∑ n₃ ∈ Finset.Icc a b, if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0 := rfl
    set t : ℝ := (N : ℝ) / 3 with ht
    set G : ℝ → ℝ := fun y => 2 * U * y - y * |y| / 2 with hG
    have hab : a ≤ b + 1 := by
      have : (a : ℝ) ≤ b + 1 := by linarith
      exact_mod_cast this
    have hcard : ((Finset.Icc a b).card : ℝ) ≤ 2 * U + 1 := by
      rw [Nat.card_Icc, Nat.cast_sub hab]; push_cast; linarith
    have hIco : Finset.Icc a b = Finset.Ico a (b + 1) := by ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have htel : ∑ n ∈ Finset.Icc a b, (G ((n : ℝ) - t + 1) - G ((n : ℝ) - t)) =
        G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) := by
      have := tele (fun n : ℕ => G ((n : ℝ) - t)) a (b + 1 - a)
      have e : a + (b + 1 - a) = b + 1 := by omega
      rw [e] at this
      rw [hIco, show ((b : ℝ) + 1 - t) = (((b + 1 : ℕ) : ℝ) - t) by push_cast; ring, ← this]
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      push_cast; ring
    have hstep : ∀ n ∈ Finset.Icc a b,
        |(G ((n : ℝ) - t + 1) - G ((n : ℝ) - t)) - (2 * U - |(n : ℝ) - N / 3|)| ≤ 1 := by
      intro n _
      rw [hG]
      exact hex_step U _
    have hA : |(∑ n₁ ∈ Finset.Icc a b, ∑ n₂ ∈ Finset.Icc a b,
        ∑ n₃ ∈ Finset.Icc a b, if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) -
        ∑ n₁ ∈ Finset.Icc a b, (2 * U - |(n₁ : ℝ) - N / 3|)| ≤
        ((Finset.Icc a b).card : ℝ) * 3 := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun n hn => count_inner N U hU hU12 n hn).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hB : |(∑ n ∈ Finset.Icc a b, (G ((n : ℝ) - t + 1) - G ((n : ℝ) - t))) -
        ∑ n₁ ∈ Finset.Icc a b, (2 * U - |(n₁ : ℝ) - N / 3|)| ≤
        ((Finset.Icc a b).card : ℝ) * 1 := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun n hn => hstep n hn).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [htel] at hB
    have hC : |G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) - 3 * U ^ 2| ≤ 2 * U := by
      set e := (b : ℝ) + 1 - t - U with he
      set f := (a : ℝ) - t + U with hf
      have he0 : 0 ≤ e := by linarith
      have he1 : e ≤ 1 := by linarith
      have hf0 : 0 ≤ f := by linarith
      have hf1 : f ≤ 1 := by linarith
      have hyb : (b : ℝ) + 1 - t = U + e := by rw [he]; ring
      have hya : (a : ℝ) - t = -U + f := by rw [hf]; ring
      have key : G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) - 3 * U ^ 2 =
          U * e - U * f - (e * e + f * f) / 2 := by
        rw [hyb, hya, hG]
        simp only
        rw [abs_of_pos (by linarith : 0 < U + e), abs_of_nonpos (by linarith : -U + f ≤ 0)]
        ring
      rw [key]
      have hU0 : 0 ≤ U := by linarith
      have h1 : U * e ≤ U * 1 := mul_le_mul_of_nonneg_left he1 hU0
      have h2 : U * f ≤ U * 1 := mul_le_mul_of_nonneg_left hf1 hU0
      have h3 : 0 ≤ U * e := mul_nonneg hU0 he0
      have h4 : 0 ≤ U * f := mul_nonneg hU0 hf0
      have h5 : e * e ≤ 1 * 1 := mul_le_mul he1 he1 he0 zero_le_one
      have h6 : f * f ≤ 1 * 1 := mul_le_mul hf1 hf1 hf0 zero_le_one
      have h7 : 0 ≤ e * e := mul_nonneg he0 he0
      have h8 : 0 ≤ f * f := mul_nonneg hf0 hf0
      rw [abs_le]; constructor <;> linarith
    rw [hW]
    set S1 := (∑ n₁ ∈ Finset.Icc a b, ∑ n₂ ∈ Finset.Icc a b,
        ∑ n₃ ∈ Finset.Icc a b, if n₁ + n₂ + n₃ = N then (1 : ℝ) else 0) with hS1
    set Sg := ∑ n₁ ∈ Finset.Icc a b, (2 * U - |(n₁ : ℝ) - N / 3|) with hSg
    set Sd := G ((b : ℝ) + 1 - t) - G ((a : ℝ) - t) with hSd
    set K := ((Finset.Icc a b).card : ℝ) with hK
    clear_value S1 Sg Sd K
    have i1 := abs_sub_le S1 Sg (3 * U ^ 2)
    have i2 := abs_sub_le Sg Sd (3 * U ^ 2)
    rw [abs_sub_comm] at hB
    linarith
  have weight_compare : ∃ C N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ n₁ n₂ n₃ : ℕ,
      (N : ℝ) / 4 ≤ n₁ → (n₁ : ℝ) ≤ N → (N : ℝ) / 4 ≤ n₂ → (n₂ : ℝ) ≤ N →
      (N : ℝ) / 4 ≤ n₃ → (n₃ : ℝ) ≤ N →
      |1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) - Real.log N ^ (-3 : ℝ)|
        ≤ C * Real.log N ^ (-4 : ℝ) := by
    refine ⟨24 * Real.log 4, 16, fun N hN n₁ n₂ n₃ h1 h1' h2 h2' h3 h3' => ?_⟩
    set L := Real.log N with hLdef
    set l := Real.log 4 with hldef
    have hN0 : (0 : ℝ) < N := by linarith
    have hl0 : 0 < l := Real.log_pos (by norm_num)
    have hL2 : 2 * l ≤ L := by
      have : Real.log 16 = 2 * l := by
        rw [hldef, ← Real.log_rpow (by norm_num)]; norm_num
      rw [← this]; exact Real.log_le_log (by norm_num) hN
    have hL0 : 0 < L := by linarith
    have key : ∀ n : ℕ, (N : ℝ) / 4 ≤ n → (n : ℝ) ≤ N →
        L - l ≤ Real.log n ∧ Real.log n ≤ L := by
      intro n hn hn'
      have hnpos : (0 : ℝ) < n := by linarith
      refine ⟨?_, Real.log_le_log hnpos hn'⟩
      have := Real.log_le_log (by positivity) hn
      rw [Real.log_div hN0.ne' (by norm_num)] at this
      linarith
    obtain ⟨a1, b1⟩ := key n₁ h1 h1'
    obtain ⟨a2, b2⟩ := key n₂ h2 h2'
    obtain ⟨a3, b3⟩ := key n₃ h3 h3'
    set x1 := Real.log n₁
    set x2 := Real.log n₂
    set x3 := Real.log n₃
    have hx1 : 0 < x1 := by linarith
    have hx2 : 0 < x2 := by linarith
    have hx3 : 0 < x3 := by linarith
    have e3 : L ^ (-3 : ℝ) = 1 / L ^ 3 := by
      rw [Real.rpow_neg hL0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have e4 : L ^ (-4 : ℝ) = 1 / L ^ 4 := by
      rw [Real.rpow_neg hL0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [e3, e4]
    set p := x1 * x2 * x3 with hp
    have hp12 : (L / 2) * (L / 2) ≤ x1 * x2 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) hx1.le
    have hplo : (L / 2) * (L / 2) * (L / 2) ≤ p :=
      mul_le_mul hp12 (by linarith) (by linarith) (by positivity)
    have hq12 : x1 * x2 ≤ L * L := mul_le_mul b1 b2 hx2.le hL0.le
    have hphi : p ≤ L * L * L := mul_le_mul hq12 b3 hx3.le (by positivity)
    -- `L³ - p ≤ L² (d₁ + d₂ + d₃)` with `dᵢ = L - xᵢ ∈ [0, l]`
    have hd12 : L * L - L * ((L - x1) + (L - x2)) ≤ x1 * x2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr b1) (sub_nonneg.mpr b2)]
    have hd123 : (L * L - L * ((L - x1) + (L - x2))) * x3 ≤ p :=
      mul_le_mul_of_nonneg_right hd12 hx3.le
    have hdiff : L * L * L - p ≤ 3 * l * (L * L) := by
      nlinarith [mul_nonneg (mul_nonneg hL0.le (sub_nonneg.mpr b3))
        (by linarith : 0 ≤ (L - x1) + (L - x2)), mul_nonneg (mul_nonneg hL0.le hL0.le)
        (sub_nonneg.mpr b3)]
    have hppos : 0 < p := by positivity
    have hnn : 0 ≤ 1 / p - 1 / L ^ 3 := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hppos (by nlinarith)
    rw [abs_of_nonneg hnn, div_sub_div _ _ hppos.ne' (by positivity), mul_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hL4 : 0 ≤ L ^ 4 := by positivity
    have hL6 : 0 < L * L * L * (L * L * L) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hdiff hL4, mul_le_mul_of_nonneg_left hplo
      (by positivity : 0 ≤ 24 * l * L ^ 3)]
  have weightedTriples_arith (W T U L P Q C1 C2 : ℝ) (hQ : 0 ≤ Q) (hP : P = L * Q)
      (hL : 0 ≤ L) (hLU : L ≤ U) (hC1 : 0 ≤ C1) (hC1U : C1 ≤ U) (hC2 : 0 ≤ C2) (_hT0 : 0 ≤ T)
      (hT : |T - 3 * U ^ 2| ≤ C1 * U) (hup : W ≤ (P + C2 * Q) * T)
      (hlo : (P - C2 * Q) * T ≤ W) :
      |W - 3 * U ^ 2 * P| ≤ (C1 + 4 * C2) * U ^ 2 * Q := by
    obtain ⟨hT1, hT2⟩ := abs_le.mp hT
    have hU : 0 ≤ U := hL.trans hLU
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    have h1 : P * (T - 3 * U ^ 2) ≤ P * (C1 * U) := mul_le_mul_of_nonneg_left (by linarith) hP0
    have h1' : P * (3 * U ^ 2 - T) ≤ P * (C1 * U) := mul_le_mul_of_nonneg_left (by linarith) hP0
    have h2 : P * (C1 * U) ≤ Q * U * (C1 * U) := by
      rw [hP]; nlinarith [mul_le_mul_of_nonneg_right hLU (mul_nonneg hQ (mul_nonneg hC1 hU))]
    have h3 : Q * U * (C1 * U) ≤ Q * U * (U * U) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQ hU)
      exact mul_le_mul_of_nonneg_right hC1U hU
    have hTle : T ≤ 4 * U ^ 2 := by nlinarith
    have h4 : C2 * Q * T ≤ C2 * Q * (4 * U ^ 2) :=
      mul_le_mul_of_nonneg_left hTle (mul_nonneg hC2 hQ)
    rw [abs_le]
    constructor <;> nlinarith
  have weightedTriplesEval_proof :
      ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |wt N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) - 3 * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-3 : ℝ)|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ) := by
    intro c hc
    obtain ⟨C1, hC1⟩ := windowTriples_count
    obtain ⟨C2, N2, hC2⟩ := weight_compare
    have F1 := ((isLittleO_log_rpow_rpow_atTop c (by norm_num : (0 : ℝ) < 3 / 8)).bound
      (by norm_num : (0 : ℝ) < 1 / 12))
    have F2 := Real.tendsto_log_atTop.eventually_ge_atTop 1
    have F3 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 8)).bound one_pos
    have F4 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 8)).eventually_ge_atTop
      (max (max C1 0) 1)
    have F5 := eventually_ge_atTop (max N2 1 : ℝ)
    obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (F1.and (F2.and (F3.and (F4.and F5))))
    refine ⟨max C1 0 + 4 * max C2 0, A, fun N hN => ?_⟩
    obtain ⟨f1, f2, f3, f4, f5⟩ := hA N hN
    set x : ℝ := (N : ℝ) with hx
    set L := Real.log x with hL
    have hx1 : 1 ≤ x := (le_max_right _ _).trans f5
    have hx0 : 0 < x := by linarith
    have hxN2 : N2 ≤ x := (le_max_left _ _).trans f5
    have hL1 : 1 ≤ L := f2
    have hL0 : 0 < L := by linarith
    have hr0 : 0 < x ^ (5 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hs0 : 0 < x ^ (3 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _), Real.norm_of_nonneg hs0.le] at f1
    rw [Real.norm_of_nonneg hL0.le, Real.norm_of_nonneg hr0.le] at f3
    have hLc : 1 ≤ L ^ c := Real.one_le_rpow hL1 hc.le
    set U := x ^ (5 / 8 : ℝ) * L ^ c with hU
    have hUr : x ^ (5 / 8 : ℝ) ≤ U := le_mul_of_one_le_right hr0.le hLc
    have hU1 : 1 ≤ U := ((le_max_right _ _).trans f4).trans hUr
    have hLU : L ≤ U := by linarith
    have hC1U : max C1 0 ≤ U := ((le_max_left _ 1).trans f4).trans hUr
    have hU12 : U ≤ x / 12 := by
      have hrs : x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) = x := by
        rw [← Real.rpow_add hx0]; norm_num
      calc U ≤ x ^ (5 / 8 : ℝ) * (1 / 12 * x ^ (3 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_left f1 hr0.le
        _ = (x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ)) / 12 := by ring
        _ = x / 12 := by rw [hrs]
    have hT := hC1 N U hU1 hU12
    have hT' : |win N U - 3 * U ^ 2| ≤ max C1 0 * U :=
      hT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    -- the window lies in `[N/4, N]`
    have hwin : ∀ n ∈ Finset.Icc ⌈x / 3 - U⌉₊ ⌊x / 3 + U⌋₊, x / 4 ≤ n ∧ (n : ℝ) ≤ x := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      constructor
      · have h := (Nat.le_ceil (x / 3 - U)).trans (Nat.cast_le.mpr hn.1)
        linarith
      · have h := (Nat.cast_le (α := ℝ)).mpr hn.2
        have h' := Nat.floor_le (by linarith : (0 : ℝ) ≤ x / 3 + U)
        linarith
    have hw := hC2 N hxN2
    set P := L ^ (-3 : ℝ)
    set Q := L ^ (-4 : ℝ)
    have hQ0 : 0 ≤ Q := Real.rpow_nonneg hL0.le _
    have hPQ : P = L * Q := by
      show L ^ (-3 : ℝ) = L * L ^ (-4 : ℝ)
      have : L ^ (-3 : ℝ) = L ^ (1 : ℝ) * L ^ (-4 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [this, Real.rpow_one]
    have hC2' : C2 * Q ≤ max C2 0 * Q := mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0
    have hup : wt N U ≤ (P + max C2 0 * Q) * win N U := by
      rw [wtD, winD]
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum; intro n₁ h₁
      apply Finset.sum_le_sum; intro n₂ h₂
      apply Finset.sum_le_sum; intro n₃ h₃
      split_ifs
      · have := hw n₁ n₂ n₃ (hwin n₁ h₁).1 (hwin n₁ h₁).2 (hwin n₂ h₂).1 (hwin n₂ h₂).2
          (hwin n₃ h₃).1 (hwin n₃ h₃).2
        have := (abs_le.mp this).2
        linarith
      · simp
    have hlo : (P - max C2 0 * Q) * win N U ≤ wt N U := by
      rw [wtD, winD]
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum; intro n₁ h₁
      apply Finset.sum_le_sum; intro n₂ h₂
      apply Finset.sum_le_sum; intro n₃ h₃
      split_ifs
      · have := hw n₁ n₂ n₃ (hwin n₁ h₁).1 (hwin n₁ h₁).2 (hwin n₂ h₂).1 (hwin n₂ h₂).2
          (hwin n₃ h₃).1 (hwin n₃ h₃).2
        have := (abs_le.mp this).1
        linarith
      · simp
    have := weightedTriples_arith (wt N U) (win N U) U L P Q (max C1 0)
      (max C2 0) hQ0 hPQ hL0.le hLU (le_max_right _ _) hC1U (le_max_right _ _)
      (windowTriples_nonneg N U) hT' hup hlo
    exact this

  have sitail_ee_nat_mul (n : ℕ) (x : ℝ) : ee ((n : ℝ) * x) = ee x ^ n := by
    unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have sitail_norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
    unfold ee
    rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have sitail_norm_ee_sub_one (x : ℝ) : ‖ee x - 1‖ = |2 * Real.sin (π * x)| := by
    unfold ee
    rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = Complex.I * ((2 * π * x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
    congr 2; ring_nf
  have sitail_sin_lower {x : ℝ} (hx : 0 < |x|) (hx2 : |x| ≤ 1 / 2) :
      2 * |x| ≤ |Real.sin (π * x)| := by
    have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → 2 * y ≤ Real.sin (π * y) := by
      intro y hy hy2
      have h := Real.mul_le_sin (x := π * y) (by positivity) (by nlinarith [Real.pi_pos])
      have : 2 / π * (π * y) = 2 * y := by field_simp
      linarith
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx2 ⊢
      exact (key x h hx2).trans (le_abs_self _)
    · rw [abs_of_neg h] at hx2 ⊢
      have := key (-x) (by linarith) hx2
      rw [show π * x = -(π * -x) by ring, Real.sin_neg, abs_neg]
      exact this.trans (le_abs_self _)
  have sitail_geom (a b : ℕ) {lam : ℝ} (hl : 0 < |lam|) (hl2 : |lam| ≤ 1 / 2) :
      ‖∑ n ∈ Finset.Icc a b, ee ((n : ℝ) * lam)‖ ≤ 1 / (2 * |lam|) := by
    have hpos : 0 < 1 / (2 * |lam|) := by positivity
    by_cases hab : a ≤ b + 1
    · simp_rw [sitail_ee_nat_mul]
      rw [← Finset.Ico_add_one_right_eq_Icc]
      have hg := geom_sum_Ico_mul (ee lam) hab
      have h1 : ‖(∑ i ∈ Finset.Ico a (b + 1), ee lam ^ i)‖ * ‖ee lam - 1‖ ≤ 2 := by
        rw [← norm_mul, hg]
        calc ‖ee lam ^ (b + 1) - ee lam ^ a‖ ≤ ‖ee lam ^ (b + 1)‖ + ‖ee lam ^ a‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, norm_pow, sitail_norm_ee]; norm_num
      rw [sitail_norm_ee_sub_one] at h1
      have hs := sitail_sin_lower hl hl2
      have h2 : 4 * |lam| ≤ |2 * Real.sin (π * lam)| := by rw [abs_mul]; norm_num; linarith
      have hS := norm_nonneg (∑ i ∈ Finset.Ico a (b + 1), ee lam ^ i)
      rw [div_eq_mul_inv, one_mul, ← one_div, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [Finset.Icc_eq_empty (by omega)]; simp only [Finset.sum_empty, norm_zero]; exact hpos.le
  have sitail_window {N : ℕ} {U : ℝ} (hU : 0 ≤ U) {n : ℕ}
      (hn : n ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊) :
      (N : ℝ) / 3 - U ≤ n ∧ (n : ℝ) ≤ (N : ℝ) / 3 + U := by
    rw [Finset.mem_Icc] at hn
    constructor
    · exact (Nat.le_ceil _).trans (by exact_mod_cast hn.1)
    · exact (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by positivity))
  have sitail_card (N : ℕ) {U : ℝ} (hU : 0 ≤ U) :
      ((Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊).card : ℝ) ≤ 2 * U + 1 := by
    rw [Nat.card_Icc]
    set a := ⌈(N : ℝ) / 3 - U⌉₊
    set b := ⌊(N : ℝ) / 3 + U⌋₊
    have ha : (N : ℝ) / 3 - U ≤ a := Nat.le_ceil _
    have hb : (b : ℝ) ≤ (N : ℝ) / 3 + U := Nat.floor_le (by positivity)
    by_cases h : a ≤ b + 1
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [show b + 1 - a = 0 by omega]; simp; linarith
  have sitail_one_le_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
    have := Real.exp_one_lt_d9
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have sitail_log_diff {x y D : ℝ} (hD : 0 < D) (hx : D ≤ x) (hy : D ≤ y) :
      |Real.log y - Real.log x| ≤ |y - x| / D := by
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have h1 : Real.log y - Real.log x ≤ (y - x) / x := by
      rw [← Real.log_div hy0.ne' hx0.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
      rw [sub_div, div_self hx0.ne']; exact this
    have h2 : Real.log x - Real.log y ≤ (x - y) / y := by
      rw [← Real.log_div hx0.ne' hy0.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      rw [sub_div, div_self hy0.ne']; exact this
    have h3 : (y - x) / x ≤ |y - x| / D := by
      rcases le_or_gt 0 (y - x) with h | h
      · rw [abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hD hx
      · exact (div_neg_of_neg_of_pos h hx0).le.trans (by positivity)
    have h4 : (x - y) / y ≤ |y - x| / D := by
      rcases le_or_gt 0 (x - y) with h | h
      · rw [abs_sub_comm, abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hD hy
      · exact (div_neg_of_neg_of_pos h hy0).le.trans (by positivity)
    rw [abs_le]; constructor <;> linarith
  have sitail_vSum_bound {N : ℕ} {U : ℝ} (hN : 12 ≤ (N : ℝ)) (hU : 1 ≤ U)
      (hUN : 12 * U ≤ N) {lam : ℝ} (hl : 0 < |lam|) (hl2 : |lam| ≤ 1 / 2) :
      ‖vSum N U lam‖ ≤ 1 / (|lam| * Real.log N) + 12 * U ^ 2 / N := by
    set L0 := Real.log ((N : ℝ) / 3)
    have hL0 : 1 ≤ L0 := sitail_one_le_log (by linarith)
    have hL : 2 * L0 ≥ Real.log N := by
      rw [← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by positivity)
      norm_num
      nlinarith
    unfold vSum
    set S := Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊
    have hsplit : (∑ n ∈ S, ee ((n : ℝ) * lam) / (Real.log n : ℂ)) =
        (∑ n ∈ S, ee ((n : ℝ) * lam)) / (L0 : ℂ) +
          ∑ n ∈ S, ee ((n : ℝ) * lam) * (((1 / Real.log n - 1 / L0 : ℝ)) : ℂ) := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast; ring
    rw [hsplit]
    have hterm : ∀ n ∈ S, ‖ee ((n : ℝ) * lam) * (((1 / Real.log n - 1 / L0 : ℝ)) : ℂ)‖ ≤
        4 * U / N := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := sitail_window (by linarith) hn
      rw [norm_mul, sitail_norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hn3 : (N : ℝ) / 4 ≤ n := by linarith
      have hln : 1 ≤ Real.log n := sitail_one_le_log (by linarith)
      have hd := sitail_log_diff (D := (N : ℝ) / 4) (by positivity) hn3
        (show (N : ℝ) / 4 ≤ (N : ℝ) / 3 by linarith)
      have hd2 : |(N : ℝ) / 3 - n| ≤ U := by rw [abs_le]; constructor <;> linarith
      have hd3 : |L0 - Real.log n| ≤ 4 * U / N := by
        refine hd.trans ?_
        rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        linarith
      have : |1 / Real.log n - 1 / L0| ≤ |L0 - Real.log n| := by
        rw [div_sub_div _ _ (by linarith) (by linarith), abs_div, one_mul, mul_one,
          abs_of_pos (by positivity : 0 < Real.log n * L0)]
        exact div_le_self (abs_nonneg _) (by nlinarith)
      linarith
    have hsum := norm_sum_le_of_le S hterm
    have hcard := sitail_card N (show (0 : ℝ) ≤ U by linarith)
    have hgeo := sitail_geom ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊ hl hl2
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    calc _ ≤ ‖(∑ n ∈ S, ee ((n : ℝ) * lam)) / (L0 : ℂ)‖ +
          ‖∑ n ∈ S, ee ((n : ℝ) * lam) * (((1 / Real.log n - 1 / L0 : ℝ)) : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / (|lam| * Real.log N) + 12 * U ^ 2 / N := by
        gcongr
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          calc _ ≤ 1 / (2 * |lam|) / L0 := by gcongr
            _ ≤ _ := by
              rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
              nlinarith
        · refine hsum.trans ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          calc (S.card : ℝ) * (4 * U / N) ≤ (2 * U + 1) * (4 * U / N) := by gcongr
            _ ≤ 12 * U ^ 2 / N := by
              rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; nlinarith
  have sitail_integrand_bound {N : ℕ} {U : ℝ} (hN : 12 ≤ (N : ℝ)) (hU : 1 ≤ U)
      (hUN : 12 * U ≤ N) {lam : ℝ} (hl : 0 < |lam|) (hl2 : |lam| ≤ 1 / 2) :
      ‖si N U lam‖ ≤
        4 * (1 / Real.log N) ^ 3 * (1 / |lam| ^ 3) + 4 * (12 * U ^ 2 / N) ^ 3 := by
    have hv := sitail_vSum_bound hN hU hUN hl hl2
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    rw [siD]
    rw [norm_mul, norm_pow, sitail_norm_ee, mul_one]
    set a := 1 / (|lam| * Real.log N)
    set b := 12 * U ^ 2 / N
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have h3 : ‖vSum N U lam‖ ^ 3 ≤ (a + b) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hv 3
    have h4 : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]
    have h5 : a ^ 3 = (1 / Real.log N) ^ 3 * (1 / |lam| ^ 3) := by
      simp only [a]; ring
    rw [h5] at h4
    linarith
  have sitail_tail_bound {N : ℕ} {U : ℝ} (hN : 12 ≤ (N : ℝ)) (hU : 1 ≤ U)
      (hUN : 12 * U ≤ N) {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 2) :
      |(∫ lam in (-(1 / 2 : ℝ))..(-w), si N U lam).re +
        (∫ lam in w..(1 / 2), si N U lam).re| ≤
        4 * (1 / Real.log N) ^ 3 / w ^ 2 + 4 * (12 * U ^ 2 / N) ^ 3 := by
    set A := (1 / Real.log N) ^ 3
    set B := (12 * U ^ 2 / N) ^ 3
    have hA : 0 ≤ A := by
      have : 0 < Real.log N := Real.log_pos (by linarith)
      positivity
    have hB : 0 ≤ B := by positivity
    set f := si N U
    set g : ℝ → ℝ := fun x => 4 * A * x ^ (-3 : ℤ) + 4 * B
    have hpt : ∀ x ∈ Set.Ioc w (1 / 2), ‖f x‖ ≤ g x ∧ ‖f (-x)‖ ≤ g x := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hz : x ^ (-3 : ℤ) = 1 / |x| ^ 3 := by
        rw [abs_of_pos hx0, zpow_neg, one_div]; norm_cast
      have e1 : 0 < |x| := by rw [abs_of_pos hx0]; exact hx0
      have e2 : |x| ≤ 1 / 2 := by rw [abs_of_pos hx0]; exact hx.2
      have e3 : 0 < |-x| := by rw [abs_neg]; exact e1
      have e4 : |-x| ≤ 1 / 2 := by rw [abs_neg]; exact e2
      have b1 := sitail_integrand_bound hN hU hUN e1 e2
      have b2 := sitail_integrand_bound hN hU hUN e3 e4
      rw [abs_neg] at b2
      simp only [g, hz]
      constructor
      · linarith
      · linarith
    have h0 : (0 : ℝ) ∉ Set.uIcc w (1 / 2) := by
      rw [Set.uIcc_of_le hw]; intro h; linarith [h.1]
    have hzi : IntervalIntegrable (fun x : ℝ => x ^ (-3 : ℤ)) MeasureTheory.volume w (1 / 2) :=
      intervalIntegral.intervalIntegrable_zpow (Or.inr h0)
    have hgi : IntervalIntegrable g MeasureTheory.volume w (1 / 2) :=
      (hzi.const_mul (4 * A)).add intervalIntegrable_const
    have h1 : ‖∫ x in w..(1 / 2), f x‖ ≤ ∫ x in w..(1 / 2), g x :=
      intervalIntegral.norm_integral_le_of_norm_le hw
        (Filter.Eventually.of_forall fun x hx => (hpt x hx).1) hgi
    have h2 : ‖∫ x in (-(1 / 2 : ℝ))..(-w), f x‖ ≤ ∫ x in w..(1 / 2), g x := by
      rw [← intervalIntegral.integral_comp_neg (a := w) (b := 1 / 2) (f := f)]
      exact intervalIntegral.norm_integral_le_of_norm_le hw
        (Filter.Eventually.of_forall fun x hx => (hpt x hx).2) hgi
    have hz : ∫ x in w..(1 / 2), x ^ (-3 : ℤ) = (1 / w ^ 2 - 4) / 2 := by
      rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩), show ((-3 : ℤ) + 1) = -2 by norm_num,
        zpow_neg, zpow_neg, zpow_two, zpow_two]
      push_cast
      field_simp
      try ring
    have hgv : ∫ x in w..(1 / 2), g x ≤ 2 * A / w ^ 2 + 2 * B := by
      simp only [g]
      rw [intervalIntegral.integral_add (hzi.const_mul (4 * A)) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, hz, intervalIntegral.integral_const, smul_eq_mul]
      have : 0 < w ^ 2 := by positivity
      have e : 4 * A * ((1 / w ^ 2 - 4) / 2) = 2 * A / w ^ 2 - 8 * A := by
        field_simp; try ring
      rw [e]
      nlinarith
    have hre : ∀ z : ℂ, |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm
    calc _ ≤ |(∫ lam in (-(1 / 2 : ℝ))..(-w), f lam).re| + |(∫ lam in w..(1 / 2), f lam).re| :=
          abs_add_le _ _
      _ ≤ ‖∫ lam in (-(1 / 2 : ℝ))..(-w), f lam‖ + ‖∫ lam in w..(1 / 2), f lam‖ :=
          add_le_add (hre _) (hre _)
      _ ≤ 2 * (2 * A / w ^ 2 + 2 * B) := by linarith
      _ = 4 * A / w ^ 2 + 4 * B := by ring
  have sitail_eventually (r s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 1 ≤ x → Real.log x ^ r ≤ ε * x ^ s := by
    obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ((isLittleO_log_rpow_rpow_atTop r hs).bound hε)
    refine ⟨X, fun x hx h1 => ?_⟩
    have := hX x hx
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg h1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at this
  have singIntTail_proof :
      ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |(∫ lam in (-(1 / 2 : ℝ))..(-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))),
        si N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam).re +
      (∫ lam in (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))..(1 / 2), si N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam).re|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ) := by
    intro c hc
    obtain ⟨X1, hX1⟩ := sitail_eventually (4 * c + 4) (1 / 2) 1 (by norm_num) one_pos
    obtain ⟨X2, hX2⟩ := sitail_eventually c (3 / 8) (1 / 12) (by norm_num) (by norm_num)
    obtain ⟨X3, hX3⟩ := sitail_eventually 4 (5 / 8) (1 / 2) (by norm_num) (by norm_num)
    refine ⟨4 + 4 * 1728, max (max X1 X2) (max X3 12), fun N hN => ?_⟩
    set x : ℝ := (N : ℝ)
    have hx12 : 12 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have h1 := hX1 x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) hx1
    have h2 := hX2 x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) hx1
    have h3 := hX3 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN) hx1
    rw [one_mul] at h1
    set L := Real.log x
    have hL1 : 1 ≤ L := sitail_one_le_log (by linarith)
    have hL0 : 0 < L := by linarith
    have hLc : 1 ≤ L ^ c := Real.one_le_rpow hL1 hc.le
    have hx58 : 1 ≤ x ^ (5 / 8 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    set U := x ^ (5 / 8 : ℝ) * L ^ c
    have hU1 : 1 ≤ U := one_le_mul_of_one_le_of_one_le hx58 hLc
    have hU0 : 0 < U := by linarith
    have hxx : x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    have hUN : 12 * U ≤ x := by
      have : 12 * U = x ^ (5 / 8 : ℝ) * (12 * L ^ c) := by simp only [U]; ring
      rw [this]
      calc x ^ (5 / 8 : ℝ) * (12 * L ^ c) ≤ x ^ (5 / 8 : ℝ) * x ^ (3 / 8 : ℝ) := by
            gcongr; linarith
        _ = x := hxx
    have hL4 : L ^ (4 : ℝ) = L ^ 4 := by exact_mod_cast Real.rpow_natCast L 4
    have hLm4 : L ^ (-4 : ℝ) = (L ^ 4)⁻¹ := by rw [Real.rpow_neg hL0.le, hL4]
    have hw0 : 0 < L ^ (4 : ℝ) / U := by positivity
    have hw : L ^ (4 : ℝ) / U ≤ 1 / 2 := by
      rw [div_le_iff₀ hU0]
      have : x ^ (5 / 8 : ℝ) ≤ U := le_mul_of_one_le_right (by positivity) hLc
      linarith
    refine (sitail_tail_bound hx12 hU1 hUN hw0 hw).trans ?_
    rw [hLm4, hL4]
    -- first term
    have t1 : 4 * (1 / L) ^ 3 / (L ^ 4 / U) ^ 2 ≤ 4 * U ^ 2 * (L ^ 4)⁻¹ := by
      have e : 4 * (1 / L) ^ 3 / (L ^ 4 / U) ^ 2 = 4 * U ^ 2 * (L ^ 4)⁻¹ * (L ^ 7)⁻¹ := by
        field_simp
      rw [e]
      have : (L ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
      have : 0 ≤ 4 * U ^ 2 * (L ^ 4)⁻¹ := by positivity
      nlinarith
    -- second term
    have hU4 : U ^ 4 * L ^ 4 ≤ x ^ 3 := by
      have e1 : (x ^ (5 / 8 : ℝ)) ^ 4 = x ^ (5 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (5 / 8 : ℝ)) 4, ← Real.rpow_mul hx0.le]; norm_num
      have e2 : (L ^ c) ^ 4 * L ^ 4 = L ^ (4 * c + 4) := by
        rw [← Real.rpow_natCast (L ^ c) 4, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 4,
          ← Real.rpow_add hL0]
        congr 1; push_cast; ring
      have e3 : x ^ (5 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ 3 := by
        rw [← Real.rpow_add hx0]; norm_num
      have : U ^ 4 * L ^ 4 = x ^ (5 / 2 : ℝ) * L ^ (4 * c + 4) := by
        simp only [U]; rw [mul_pow, e1, mul_assoc, e2]
      rw [this, ← e3]
      gcongr
    have t2 : 4 * (12 * U ^ 2 / x) ^ 3 ≤ 4 * 1728 * U ^ 2 * (L ^ 4)⁻¹ := by
      have e : 4 * (12 * U ^ 2 / x) ^ 3 = 4 * 1728 * U ^ 2 * (U ^ 4 / x ^ 3) := by
        field_simp; try ring
      rw [e]
      have : U ^ 4 / x ^ 3 ≤ (L ^ 4)⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        calc U ^ 4 = U ^ 4 * L ^ 4 * (L ^ 4)⁻¹ := by field_simp
          _ ≤ x ^ 3 * (L ^ 4)⁻¹ := by gcongr
          _ = _ := by ring
      have : 0 ≤ 4 * 1728 * U ^ 2 := by positivity
      nlinarith
    have : (4 + 4 * 1728 : ℝ) * U ^ 2 * (L ^ 4)⁻¹ =
        4 * U ^ 2 * (L ^ 4)⁻¹ + 4 * 1728 * U ^ 2 * (L ^ 4)⁻¹ := by ring
    rw [this]
    linarith

  exact singIntEval_of_parts fullPeriodIdentity_proof weightedTriplesEval_proof singIntTail_proof

open Finset

set_option maxHeartbeats 1000000 in
/-- Step 4 by the elementary route: the Euler product of `μ(q) c_q(N)/φ(q)³` is the singular
series, and the tail past `Q₁ = L^d` is `O(1/√Q₁)` by `q³ ≤ 16 φ(q)⁴`. -/
theorem singTruncEval_leaf : SingTruncEval := by
  let st : ℕ → ℕ → ℝ :=
    fun N q => if q = 0 then 0 else (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N
  have hst : ∀ N q : ℕ, st N q =
      (if q = 0 then 0 else (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N) :=
    fun N q => rfl
  have singTrunc_eq (N : ℕ) (Q : ℝ) :
      singTrunc N Q = ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), st N q := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
    have h0 : st N 0 = 0 := by simp [hst]
    rw [h0, zero_add]
    unfold singTrunc
    apply Finset.sum_congr
    · ext q; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    intro q hq
    have : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
    simp [hst, this]
  have singTruncEval_of_parts (hI : ∀ N : ℕ, Odd N → HasSum (st N) (Sing N)) (hT :
      ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      Summable (fun q => |st N q|) ∧
      ∑' q : ℕ, (if ⌊Real.log N ^ d⌋₊ < q then |st N q| else 0) ≤ K / Real.log N) :
      SingTruncEval := by
    obtain ⟨d₀, hd₀, hT'⟩ := hT
    refine ⟨d₀, hd₀, fun d hd => ?_⟩
    obtain ⟨K, N₀, h⟩ := hT' d hd
    refine ⟨K, N₀, fun N hN hN0 => ?_⟩
    obtain ⟨hsum, htail⟩ := h N hN hN0
    set Q := ⌊Real.log N ^ d⌋₊
    have hS := hI N hN
    have hsf : Summable (st N) := hS.summable
    -- Sing N = partial + tail
    have hsplit := hsf.sum_add_tsum_nat_add (Q + 1)
    have htrunc : singTrunc N (Real.log N ^ d) = ∑ q ∈ Finset.range (Q + 1), st N q :=
      singTrunc_eq N _
    have heq : singTrunc N (Real.log N ^ d) - Sing N = -∑' q : ℕ, st N (q + (Q + 1)) := by
      rw [htrunc, ← hS.tsum_eq, ← hsplit]; ring
    rw [heq, abs_neg]
    have hsabs : Summable (fun q : ℕ => |st N (q + (Q + 1))|) :=
      (summable_nat_add_iff (Q + 1)).mpr hsum
    calc |∑' q : ℕ, st N (q + (Q + 1))| ≤ ∑' q : ℕ, |st N (q + (Q + 1))| := by
          have hs' : Summable (fun q : ℕ => ‖st N (q + (Q + 1))‖) := by
            simpa [Real.norm_eq_abs] using hsabs
          have := norm_tsum_le_tsum_norm hs'
          simpa [Real.norm_eq_abs] using this
      _ = ∑' q : ℕ, (if Q < q then |st N q| else 0) := by
          have hind : Summable (fun q : ℕ => if Q < q then |st N q| else 0) :=
            hsum.of_nonneg_of_le (fun q => by split_ifs <;> simp [abs_nonneg])
              (fun q => by split_ifs <;> simp [abs_nonneg])
          rw [← hind.sum_add_tsum_nat_add (Q + 1)]
          have : ∑ q ∈ Finset.range (Q + 1), (if Q < q then |st N q| else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro q hq
            have : ¬ Q < q := by have := Finset.mem_range.mp hq; omega
            simp [this]
          rw [this, zero_add]
          apply tsum_congr
          intro q
          have : Q < q + (Q + 1) := by omega
          simp [this]
      _ ≤ K / Real.log N := htail

  have card_coprime_id1122d (q : ℕ) :
      ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
    rw [Nat.totient]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact Nat.coprime_comm
  have abs_ramanujanC_le_id1122d (q N : ℕ) : |ramanujanC q N| ≤ Nat.totient q := by
    unfold ramanujanC
    calc _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          |Real.cos (2 * π * (a : ℝ) * N / q)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) :=
          Finset.sum_le_sum (fun a _ => Real.abs_cos_le_one _)
      _ = Nat.totient q := by rw [Finset.sum_const, card_coprime_id1122d]; simp
  have ramanujanC_one_id1122d (N : ℕ) : ramanujanC 1 N = 1 := by
    unfold ramanujanC
    simp
  have sum_cos_range_id1122d (q N : ℕ) (hq : 1 ≤ q) :
      ∑ a ∈ Finset.range q, Real.cos (2 * π * (a : ℝ) * N / q) = if q ∣ N then (q : ℝ) else 0 := by
    have hq0 : (q : ℝ) ≠ 0 := by
      have : (0 : ℝ) < q := by exact_mod_cast hq
      exact this.ne'
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      have : ∀ a ∈ Finset.range q,
          Real.cos (2 * π * (a : ℝ) * ((q * k : ℕ) : ℝ) / q) = 1 := by
        intro a _
        have e : 2 * π * (a : ℝ) * ((q * k : ℕ) : ℝ) / q = ((a * k : ℕ) : ℝ) * (2 * π) := by
          push_cast; field_simp
        rw [e, Real.cos_nat_mul_two_pi]
      rw [Finset.sum_congr rfl this]; simp
    · set ζ : ℂ := Complex.exp (2 * π * Complex.I * N / q) with hζ
      have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
      have hpow : ∀ a : ℕ,
          ζ ^ a = Complex.exp (((2 * π * (a : ℝ) * N / q : ℝ) : ℂ) * Complex.I) := by
        intro a
        rw [hζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
      have hre : ∑ a ∈ Finset.range q, Real.cos (2 * π * (a : ℝ) * N / q) =
          (∑ a ∈ Finset.range q, ζ ^ a).re := by
        rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro a _
        rw [hpow, Complex.exp_ofReal_mul_I_re]
      have hq1 : ζ ^ q = 1 := by
        rw [hζ, ← Complex.exp_nat_mul]
        have : (q : ℂ) * (2 * π * Complex.I * N / q) = (N : ℂ) * (2 * π * Complex.I) := by
          field_simp
        rw [this, Complex.exp_nat_mul_two_pi_mul_I]
      have hne : ζ ≠ 1 := by
        intro h1
        rw [hζ, Complex.exp_eq_one_iff] at h1
        obtain ⟨k, hk⟩ := h1
        have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have e1 : (N : ℂ) = k * q := by
          have e2 : (N : ℂ) = (2 * π * Complex.I * N / q) * q / (2 * π * Complex.I) := by
            field_simp
          rw [e2, hk]; field_simp
        apply h
        have e3 : (N : ℤ) = k * q := by exact_mod_cast e1
        exact Int.natCast_dvd_natCast.mp ⟨k, by rw [e3]; ring⟩
      rw [hre, geom_sum_eq hne, hq1]; simp
  have ramanujanC_prime_id1122d (p N : ℕ) (hp : p.Prime) :
      ramanujanC p N = if p ∣ N then (p : ℝ) - 1 else -1 := by
    have hp1 := hp.one_le
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range p)
      (fun a => Nat.Coprime a p) (fun a : ℕ => Real.cos (2 * π * (a : ℝ) * N / p))
    have hnot : (Finset.range p).filter (fun a => ¬ Nat.Coprime a p) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hc⟩
        by_contra h0
        apply hc
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro hd
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
        omega
      · rintro rfl
        exact ⟨hp.pos, by simp [hp.ne_one]⟩
    rw [hnot, Finset.sum_singleton, sum_cos_range_id1122d p N hp1] at hsplit
    unfold ramanujanC
    have h0 : Real.cos (2 * π * ((0 : ℕ) : ℝ) * N / p) = 1 := by simp
    rw [h0] at hsplit
    split_ifs at hsplit ⊢ <;> linarith
  have ramanujanC_mul_id1122d (m n N : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : Nat.Coprime m n) :
      ramanujanC (m * n) N = ramanujanC m N * ramanujanC n N := by
    set A := (Finset.range m).filter (fun a => Nat.Coprime a m) with hA
    set B := (Finset.range n).filter (fun b => Nat.Coprime b n) with hB
    set C := (Finset.range (m * n)).filter (fun c => Nat.Coprime c (m * n)) with hC
    have hm0 : (m : ℝ) ≠ 0 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      exact this.ne'
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact this.ne'
    have hcm : ramanujanC m N = ∑ a ∈ A, Real.cos (2 * π * (a : ℝ) * N / m) := rfl
    have hcn : ramanujanC n N = ∑ b ∈ B, Real.cos (2 * π * (b : ℝ) * N / n) := rfl
    have hcmn : ramanujanC (m * n) N =
        ∑ c ∈ C, Real.cos (2 * π * (c : ℝ) * N / ((m * n : ℕ) : ℝ)) := rfl
    have hs : ∑ a ∈ A, Real.sin (2 * π * (a : ℝ) * N / m) = 0 := ramanujan_sin_zero m N hm
    have hR : ramanujanC m N * ramanujanC n N =
        ∑ x ∈ A ×ˢ B, Real.cos (2 * π * (x.1 : ℝ) * N / m + 2 * π * (x.2 : ℝ) * N / n) := by
      rw [hcm, hcn, Finset.sum_product, Finset.sum_mul_sum]
      have : ∀ a ∈ A, ∑ b ∈ B, Real.cos (2 * π * (a : ℝ) * N / m) *
            Real.cos (2 * π * (b : ℝ) * N / n)
          = ∑ b ∈ B, Real.cos (2 * π * (a : ℝ) * N / m + 2 * π * (b : ℝ) * N / n)
            + Real.sin (2 * π * (a : ℝ) * N / m) *
              ∑ b ∈ B, Real.sin (2 * π * (b : ℝ) * N / n) := by
        intro a _
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro b _; rw [Real.cos_add]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, hs, zero_mul,
        add_zero]
    rw [hR, hcmn]
    let i : ℕ × ℕ → ℕ := fun x => (x.1 * n + x.2 * m) % (m * n)
    have hmnpos : 0 < m * n := by positivity
    have hi : ∀ x ∈ A ×ˢ B, i x ∈ C := by
      intro x hx
      rw [Finset.mem_product] at hx
      have ha := (Finset.mem_filter.mp hx.1).2
      have hb := (Finset.mem_filter.mp hx.2).2
      rw [hC, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hmnpos, ?_⟩
      have h1 : Nat.Coprime m (x.1 * n + x.2 * m) := by
        rw [Nat.coprime_add_mul_right_right]
        exact Nat.Coprime.mul_right ha.symm hmn
      have h2 : Nat.Coprime n (x.1 * n + x.2 * m) := by
        rw [add_comm, Nat.coprime_add_mul_right_right]
        exact Nat.Coprime.mul_right hb.symm hmn.symm
      have h3 : Nat.Coprime (m * n) (x.1 * n + x.2 * m) :=
        (Nat.Coprime.mul_right h1.symm h2.symm).symm
      unfold Nat.Coprime
      rw [← Nat.gcd_rec]
      exact h3
    have hinj : Set.InjOn i (A ×ˢ B : Finset (ℕ × ℕ)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hx hy
      have ha1 := Finset.mem_range.mp (Finset.mem_filter.mp hx.1).1
      have hb1 := Finset.mem_range.mp (Finset.mem_filter.mp hx.2).1
      have ha2 := Finset.mem_range.mp (Finset.mem_filter.mp hy.1).1
      have hb2 := Finset.mem_range.mp (Finset.mem_filter.mp hy.2).1
      have hE : x.1 * n + x.2 * m ≡ y.1 * n + y.2 * m [MOD m * n] := hxy
      have hEm := hE.of_mul_right n
      have hEn := hE.of_mul_left m
      have e1 : x.1 * n ≡ y.1 * n [MOD m] := by
        unfold Nat.ModEq at hEm ⊢
        rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at hEm
      have e2 : x.2 * m ≡ y.2 * m [MOD n] := by
        unfold Nat.ModEq at hEn ⊢
        rwa [add_comm, Nat.add_mul_mod_self_right, add_comm,
          Nat.add_mul_mod_self_right] at hEn
      have f1 := Nat.ModEq.cancel_right_of_coprime hmn e1
      have f2 := Nat.ModEq.cancel_right_of_coprime hmn.symm e2
      unfold Nat.ModEq at f1 f2
      rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2] at f1
      rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at f2
      exact Prod.ext f1 f2
    have himg : (A ×ˢ B).image i = C := by
      apply Finset.eq_of_subset_of_card_le
      · intro c hc
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
        exact hi x hx
      · rw [Finset.card_image_of_injOn hinj, Finset.card_product, hA, hB, hC,
          card_coprime_id1122d, card_coprime_id1122d, card_coprime_id1122d, Nat.totient_mul hmn]
    rw [← himg, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro x _
    set c := x.1 * n + x.2 * m with hc
    have hdiv := Nat.mod_add_div c (m * n)
    have hcast : ((c % (m * n) : ℕ) : ℝ) = (c : ℝ) - (m * n : ℝ) * ((c / (m * n) : ℕ) : ℝ) := by
      have : ((c % (m * n) : ℕ) : ℝ) + ((m * n : ℕ) : ℝ) * ((c / (m * n) : ℕ) : ℝ) = (c : ℝ) := by
        exact_mod_cast hdiv
      push_cast at this ⊢
      linarith
    have e : 2 * π * (x.1 : ℝ) * N / m + 2 * π * (x.2 : ℝ) * N / n =
        2 * π * ((c % (m * n) : ℕ) : ℝ) * N / ((m * n : ℕ) : ℝ) +
          ((c / (m * n) * N : ℕ) : ℝ) * (2 * π) := by
      rw [hcast, hc]; push_cast; field_simp; ring
    rw [e, Real.cos_add_nat_mul_two_pi]
  have singTerm_mul_id1122d (N : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
      st N (m * n) = st N m * st N n := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hst]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hst]
    have hmn : m * n ≠ 0 := by positivity
    simp only [hst, hmn, hm.ne', hn.ne', ite_false]
    rw [ramanujanC_mul_id1122d m n N hm hn h, Nat.totient_mul h,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
    push_cast; ring
  have singTerm_one_id1122d (N : ℕ) : st N 1 = 1 := by
    simp [hst, ramanujanC_one_id1122d]
  have singTerm_prime_pow_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 2 ≤ e) :
      st N (p ^ e) = 0 := by
    have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
    simp only [hst, hne, ite_false]
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    have : e ≠ 1 := by omega
    simp [this]
  have singTerm_prime_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) :
      st N p = -ramanujanC p N / ((p : ℝ) - 1) ^ 3 := by
    simp only [hst, hp.ne_zero, ite_false]
    rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le]
    push_cast; ring
  have abs_singTerm_le_id1122d (N q : ℕ) (hq : 1 ≤ q) :
      |st N q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
    have hq0 : q ≠ 0 := by omega
    have ht : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    simp only [hst, hq0, ite_false]
    rw [abs_mul, abs_div, abs_pow, abs_of_pos ht]
    have hmu : |((μ q : ℤ) : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := q)
      exact_mod_cast this
    have hc := abs_ramanujanC_le_id1122d q N
    calc |((μ q : ℤ) : ℝ)| / (Nat.totient q : ℝ) ^ 3 * |ramanujanC q N|
        ≤ 1 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) := by
          apply mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) hc (abs_nonneg _)
            (by positivity)
      _ = 1 / (Nat.totient q : ℝ) ^ 2 := by field_simp
  have abs_singTerm_prime_le_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) :
      |st N p| ≤ 4 / (p : ℝ) ^ 2 := by
    have h := abs_singTerm_le_id1122d N p hp.one_le
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one] at h
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    refine h.trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have tsum_prime_pow_id1122d (g : ℕ → ℝ) (hg1 : g 1 = 1) {p : ℕ}
      (hpe : ∀ e, 2 ≤ e → g (p ^ e) = 0) : ∑' e : ℕ, g (p ^ e) = 1 + g p := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ, hg1]
    · intro e he
      simp only [Finset.mem_range, not_lt] at he
      exact hpe e he
  have summable_four_div_sq_id1122d : Summable (fun m : ℕ => 4 / (m : ℝ) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 4
    exact this.congr (fun m => by ring)
  have sum_range_le_of_mult_id1122d (g : ℕ → ℝ) (hg1 : g 1 = 1)
      (hgmul : ∀ {m n : ℕ}, Nat.Coprime m n → g (m * n) = g m * g n)
      (hg0 : ∀ q, 0 ≤ g q) (hgz : g 0 = 0)
      (hpsum : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖g (p ^ e)‖)) (n : ℕ) :
      ∑ i ∈ Finset.range n, g i ≤ ∏ p ∈ n.primesBelow, ∑' e, g (p ^ e) := by
    obtain ⟨_, hhas⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg1 hgmul hpsum n
    have hind := hasSum_subtype_iff_indicator.mp hhas
    have heq : ∑ i ∈ Finset.range n, g i =
        ∑ i ∈ Finset.range n, (Set.indicator (Nat.smoothNumbers n) g) i := by
      apply Finset.sum_congr rfl; intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hgz]; by_cases h0 : (0 : ℕ) ∈ Nat.smoothNumbers n
        · rw [Set.indicator_of_mem h0, hgz]
        · rw [Set.indicator_of_notMem h0]
      · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hpos (Finset.mem_range.mp hi))]
    rw [heq]
    exact sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => hg0 j) i) hind
  have prod_primesBelow_le_id1122d (g : ℕ → ℝ) (hg0 : ∀ q, 0 ≤ g q)
      (hgp : ∀ {p : ℕ}, p.Prime → g p ≤ 4 / (p : ℝ) ^ 2) (n : ℕ) :
      ∏ p ∈ n.primesBelow, (1 + g p) ≤ Real.exp (∑' m : ℕ, 4 / (m : ℝ) ^ 2) := by
    have h1 : ∏ p ∈ n.primesBelow, (1 + g p) ≤ ∏ p ∈ n.primesBelow, Real.exp (4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod₀ (fun p _ => by linarith [hg0 p])
      intro p hp
      have h1 := hgp (Nat.prime_of_mem_primesBelow hp)
      have h2 := Real.add_one_le_exp (4 / (p : ℝ) ^ 2)
      linarith
    refine h1.trans ?_
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hsub : n.primesBelow ⊆ Finset.range n := fun p hp => (Finset.mem_filter.mp hp).1
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => by positivity)) ?_
    exact summable_four_div_sq_id1122d.sum_le_tsum (Finset.range n) (fun i _ => by positivity)
  have summable_abs_singTerm_id1122d (N : ℕ) : Summable (fun q => |st N q|) := by
    have hg1 : |st N 1| = 1 := by rw [singTerm_one_id1122d, abs_one]
    have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
        |st N (m * n)| = |st N m| * |st N n| := by
      intro m n h; rw [singTerm_mul_id1122d N h, abs_mul]
    have hgz : |st N 0| = 0 := by simp [hst]
    have hpe : ∀ {p : ℕ}, p.Prime → ∀ e, 2 ≤ e → |st N (p ^ e)| = 0 := by
      intro p hp e he; rw [singTerm_prime_pow_id1122d N hp he, abs_zero]
    have hpsum : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖|st N (p ^ e)|‖) := by
      intro p hp
      apply summable_of_ne_finset_zero (s := Finset.range 2)
      intro e he
      simp only [Finset.mem_range, not_lt] at he
      rw [hpe hp e he, norm_zero]
    refine summable_of_sum_range_le (fun q => abs_nonneg _)
      (c := Real.exp (∑' m : ℕ, 4 / (m : ℝ) ^ 2)) ?_
    intro n
    refine (sum_range_le_of_mult_id1122d (fun q => |st N q|) hg1 hgmul
      (fun q => abs_nonneg _) hgz hpsum n).trans ?_
    have hfac : ∏ p ∈ n.primesBelow, ∑' e, |st N (p ^ e)| =
        ∏ p ∈ n.primesBelow, (1 + |st N p|) :=
      Finset.prod_congr rfl (fun p hp =>
        tsum_prime_pow_id1122d (fun q => |st N q|) hg1
          (hpe (Nat.prime_of_mem_primesBelow hp)))
    rw [hfac]
    exact prod_primesBelow_le_id1122d (fun q => |st N q|) (fun q => abs_nonneg _)
      (fun hp => abs_singTerm_prime_le_id1122d N hp) n
  have singTerm_euler_factor_id1122d (N : ℕ) {p : ℕ} (hp : p.Prime) :
      ∑' e : ℕ, st N (p ^ e) =
        if p ∣ N then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
    rw [tsum_prime_pow_id1122d (st N) (singTerm_one_id1122d N)
      (fun e he => singTerm_prime_pow_id1122d N hp he), singTerm_prime_id1122d N hp,
      ramanujanC_prime_id1122d p N hp]
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
    split_ifs <;> field_simp <;> ring
  have singSeriesIdentity_proof : ∀ N : ℕ, Odd N → HasSum (st N) (Sing N) := by
    intro N _
    have hsum : Summable (fun q => ‖st N q‖) := by
      simpa [Real.norm_eq_abs] using summable_abs_singTerm_id1122d N
    have hf0 : st N 0 = 0 := by simp [hst]
    have hE := EulerProduct.eulerProduct_tprod (singTerm_one_id1122d N)
      (fun h => singTerm_mul_id1122d N h) hsum hf0
    have hS : Sing N = ∑' n, st N n := by
      rw [← hE]
      unfold Sing
      exact tprod_congr (fun p => (singTerm_euler_factor_id1122d N p.2).symm)
    rw [hS]
    exact hsum.of_norm.hasSum

  have ramanujanC_abs_le (q N : ℕ) : |ramanujanC q N| ≤ (Nat.totient q : ℝ) := by
    have hc : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
      rw [Nat.totient_eq_card_coprime]
      congr 1
      apply Finset.filter_congr
      intro a _
      exact Nat.coprime_comm
    unfold ramanujanC
    calc |∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            Real.cos (2 * π * (a : ℝ) * N / q)|
        ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            |Real.cos (2 * π * (a : ℝ) * N / q)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) :=
          Finset.sum_le_sum (fun a _ => Real.abs_cos_le_one _)
      _ = (Nat.totient q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  have singTerm_abs_le (N q : ℕ) : |st N q| ≤ 1 / (Nat.totient q : ℝ) ^ 2 := by
    by_cases hq : q = 0
    · subst hq; simp [hst]
    have hφ : (0 : ℝ) < Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
    have hμ : |(μ q : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    simp only [hst, hq, ite_false]
    rw [abs_mul, abs_div, abs_of_pos (pow_pos hφ 3)]
    calc |(μ q : ℝ)| / (Nat.totient q : ℝ) ^ 3 * |ramanujanC q N|
        ≤ 1 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) :=
          mul_le_mul (div_le_div_of_nonneg_right hμ (by positivity)) (ramanujanC_abs_le q N)
            (abs_nonneg _) (by positivity)
      _ = 1 / (Nat.totient q : ℝ) ^ 2 := by field_simp
  have cube_le_totient_pow_four (n : ℕ) : n ^ 3 ≤ 16 * (Nat.totient n) ^ 4 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have h1 := Nat.totient_mul_prod_primeFactors n
    set P := ∏ p ∈ n.primeFactors, p with hPdef
    set R := ∏ p ∈ n.primeFactors, (p - 1) with hRdef
    have hPn : P ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    have hPpos : 0 < P := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    -- the per prime weight
    have hstep : ∀ p ∈ n.primeFactors,
        p ^ 3 ≤ ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1)) * (p - 1) ^ 4 := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      by_cases h2 : p = 2
      · subst h2; norm_num
      by_cases h3 : p = 3
      · subst h3; norm_num
      simp only [h2, h3, ite_false, mul_one, one_mul]
      have h4 : p ≠ 4 := by
        rintro rfl; exact absurd hpr (by decide)
      have h5 : 5 ≤ p := by have := hpr.two_le; omega
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      have hk : 4 ≤ k := by omega
      simp only [Nat.add_sub_cancel]
      nlinarith [Nat.mul_le_mul_left (k ^ 3) hk, pow_pos (show 0 < k by omega) 2]
    have hw : (∏ p ∈ n.primeFactors, ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1))) ≤ 16 := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
      split_ifs <;> norm_num
    have hPR : P ^ 3 ≤ 16 * R ^ 4 := by
      rw [hPdef, hRdef, ← Finset.prod_pow, ← Finset.prod_pow]
      calc ∏ p ∈ n.primeFactors, p ^ 3
          ≤ ∏ p ∈ n.primeFactors,
              (((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1)) * (p - 1) ^ 4) :=
            Finset.prod_le_prod hstep
        _ = (∏ p ∈ n.primeFactors, ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1))) *
              ∏ p ∈ n.primeFactors, (p - 1) ^ 4 := Finset.prod_mul_distrib
        _ ≤ 16 * ∏ p ∈ n.primeFactors, (p - 1) ^ 4 := Nat.mul_le_mul_right _ hw
    have hA : n ^ 4 * P ^ 3 ≤ (16 * Nat.totient n ^ 4 * P) * P ^ 3 := by
      calc n ^ 4 * P ^ 3 ≤ n ^ 4 * (16 * R ^ 4) := Nat.mul_le_mul_left _ hPR
        _ = 16 * (n * R) ^ 4 := by ring
        _ = 16 * (Nat.totient n * P) ^ 4 := by rw [h1]
        _ = (16 * Nat.totient n ^ 4 * P) * P ^ 3 := by ring
    have hB : n ^ 4 ≤ 16 * Nat.totient n ^ 4 * P :=
      Nat.le_of_mul_le_mul_right hA (pow_pos hPpos 3)
    have hC : n ^ 3 * n ≤ 16 * Nat.totient n ^ 4 * n := by
      calc n ^ 3 * n = n ^ 4 := by ring
        _ ≤ 16 * Nat.totient n ^ 4 * P := hB
        _ ≤ 16 * Nat.totient n ^ 4 * n := Nat.mul_le_mul_left _ hPn
    exact Nat.le_of_mul_le_mul_right hC hn
  have inv_totient_sq_le (q : ℕ) (hq : 1 ≤ q) :
      1 / (Nat.totient q : ℝ) ^ 2 ≤ 4 / ((q : ℝ) * Real.sqrt q) := by
    have hφ : (0 : ℝ) < Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by linarith)
    have hspos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
    have hb : ((q : ℝ)) ^ 3 ≤ 16 * (Nat.totient q : ℝ) ^ 4 := by
      exact_mod_cast cube_le_totient_pow_four q
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : ((q : ℝ) * Real.sqrt q) ^ 2 ≤ (4 * (Nat.totient q : ℝ) ^ 2) ^ 2 := by
      have : ((q : ℝ) * Real.sqrt q) ^ 2 = (q : ℝ) ^ 3 := by
        rw [mul_pow, hs]; ring
      rw [this]; nlinarith
    have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    linarith
  have tele_step_ab (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (h : b ^ 2 = a ^ 2 + 1) :
      4 / (b ^ 2 * b) ≤ 8 / a - 8 / b := by
    have hb : 0 < b := by linarith
    have ha0 : 0 < a := by linarith
    have h2 : 1 ≤ 2 * b * (b - a) := by nlinarith
    rw [div_sub_div _ _ (ne_of_gt ha0) (ne_of_gt hb), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg b), mul_le_mul_of_nonneg_right hab hb.le]
  have tele_step (x : ℝ) (hx : 1 ≤ x) :
      4 / ((x + 1) * Real.sqrt (x + 1)) ≤ 8 / Real.sqrt x - 8 / Real.sqrt (x + 1) := by
    have ha : 1 ≤ Real.sqrt x := by
      have := Real.sqrt_le_sqrt hx; rwa [Real.sqrt_one] at this
    have hab : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
    have h : Real.sqrt (x + 1) ^ 2 = Real.sqrt x ^ 2 + 1 := by
      rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have := tele_step_ab _ _ ha hab h
    rwa [Real.sq_sqrt (by linarith)] at this
  have tele_sum (Q : ℕ) (hQ : 1 ≤ Q) : ∀ m : ℕ,
      ∑ i ∈ Finset.range m, 4 / (((Q + 1 + i : ℕ) : ℝ) * Real.sqrt ((Q + 1 + i : ℕ) : ℝ)) ≤
        8 / Real.sqrt Q - 8 / Real.sqrt ((Q + m : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hx : (1 : ℝ) ≤ ((Q + m : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ Q + m by omega)
      have hs := tele_step _ hx
      have e1 : ((Q + 1 + m : ℕ) : ℝ) = ((Q + m : ℕ) : ℝ) + 1 := by push_cast; ring
      have e2 : ((Q + (m + 1) : ℕ) : ℝ) = ((Q + m : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e1, e2]
      linarith
  have cmp_nonneg (q : ℕ) : 0 ≤ 4 / ((q : ℝ) * Real.sqrt q) := by positivity
  have singTerm_abs_le_cmp (N q : ℕ) : |st N q| ≤ 4 / ((q : ℝ) * Real.sqrt q) := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp [hst]
    exact (singTerm_abs_le N q).trans (inv_totient_sq_le q h)
  have cmp_tail_partial (Q : ℕ) (hQ : 1 ≤ Q) (n : ℕ) :
      ∑ i ∈ Finset.range n, (if Q < i then 4 / ((i : ℝ) * Real.sqrt i) else 0) ≤
        8 / Real.sqrt Q := by
    set h : ℕ → ℝ := fun i => if Q < i then 4 / ((i : ℝ) * Real.sqrt i) else 0 with hh
    have hnn : ∀ i, 0 ≤ h i := fun i => by
      simp only [hh]; split_ifs
      · exact cmp_nonneg i
      · exact le_refl _
    calc ∑ i ∈ Finset.range n, h i ≤ ∑ i ∈ Finset.range (Q + 1 + n), h i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : n ≤ Q + 1 + n))
            (fun i _ _ => hnn i)
      _ = ∑ i ∈ Finset.range (Q + 1), h i + ∑ i ∈ Finset.range n, h (Q + 1 + i) :=
          Finset.sum_range_add _ _ _
      _ = ∑ i ∈ Finset.range n,
            4 / (((Q + 1 + i : ℕ) : ℝ) * Real.sqrt ((Q + 1 + i : ℕ) : ℝ)) := by
          have h0 : ∑ i ∈ Finset.range (Q + 1), h i = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have : ¬ Q < i := by have := Finset.mem_range.mp hi; omega
            simp [hh, this]
          rw [h0, zero_add]
          apply Finset.sum_congr rfl
          intro i _
          have : Q < Q + 1 + i := by omega
          simp [hh, this]
      _ ≤ 8 / Real.sqrt Q - 8 / Real.sqrt ((Q + n : ℕ) : ℝ) := tele_sum Q hQ n
      _ ≤ 8 / Real.sqrt Q := by
          have : 0 ≤ 8 / Real.sqrt ((Q + n : ℕ) : ℝ) := by positivity
          linarith
  have cmp_summable : Summable (fun q : ℕ => 4 / ((q : ℝ) * Real.sqrt q)) := by
    apply summable_of_sum_range_le (c := 8 / Real.sqrt 1 + 4) (fun q => cmp_nonneg q)
    intro n
    have h1 := cmp_tail_partial 1 le_rfl n
    have h2 : ∑ i ∈ Finset.range n, 4 / ((i : ℝ) * Real.sqrt i) ≤
        ∑ i ∈ Finset.range n, ((if 1 < i then 4 / ((i : ℝ) * Real.sqrt i) else 0) +
          (if i = 1 then 4 else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      rcases Nat.lt_trichotomy i 1 with hi | hi | hi
      · have : i = 0 := by omega
        subst this; simp
      · subst hi; simp
      · have : i ≠ 1 := by omega
        simp [hi, this]
    rw [Finset.sum_add_distrib] at h2
    have h3 : ∑ i ∈ Finset.range n, (if i = 1 then (4 : ℝ) else 0) ≤ 4 := by
      rw [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    push_cast at h1
    linarith
  have singTerm_abs_summable (N : ℕ) : Summable (fun q => |st N q|) :=
    cmp_summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun q => singTerm_abs_le_cmp N q)
  have singTerm_tail_le (N Q : ℕ) (hQ : 1 ≤ Q) :
      ∑' q : ℕ, (if Q < q then |st N q| else 0) ≤ 8 / Real.sqrt Q := by
    apply Real.tsum_le_of_sum_range_le
    · intro q; split_ifs
      · exact abs_nonneg _
      · exact le_refl _
    intro n
    refine le_trans (Finset.sum_le_sum fun q _ => ?_) (cmp_tail_partial Q hQ n)
    split_ifs
    · exact singTerm_abs_le_cmp N q
    · exact le_refl _
  have singSeriesTail_proof :
      ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      Summable (fun q => |st N q|) ∧
      ∑' q : ℕ, (if ⌊Real.log N ^ d⌋₊ < q then |st N q| else 0) ≤ K / Real.log N := by
    refine ⟨4, by norm_num, fun d hd => ⟨16, 3, fun N _ hN => ?_⟩⟩
    refine ⟨singTerm_abs_summable N, ?_⟩
    set L := Real.log N with hLdef
    have hN3 : (3 : ℝ) ≤ N := hN
    have hL : 1 ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hL4 : L ^ (4 : ℝ) ≤ L ^ d := Real.rpow_le_rpow_of_exponent_le hL hd
    have hL4' : L ^ (4 : ℝ) = L ^ (4 : ℕ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hL4'] at hL4
    have hLd1 : 1 ≤ L ^ d := le_trans (one_le_pow₀ hL) hL4
    set Q := ⌊L ^ d⌋₊ with hQdef
    have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hLd1)
    have hQlt : L ^ d < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hQ1' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
    have hQbig : L ^ 4 / 4 ≤ (Q : ℝ) := by nlinarith
    have hsq : L ^ 2 / 2 ≤ Real.sqrt Q := by
      have := Real.sqrt_le_sqrt (show (L ^ 2 / 2) ^ 2 ≤ (Q : ℝ) by nlinarith)
      rwa [Real.sqrt_sq (by positivity)] at this
    refine le_trans (singTerm_tail_le N Q hQ1) ?_
    have hpos : 0 < L ^ 2 / 2 := by positivity
    calc 8 / Real.sqrt Q ≤ 8 / (L ^ 2 / 2) := div_le_div_of_nonneg_left (by norm_num) hpos hsq
      _ = 16 / L ^ 2 := by field_simp; ring
      _ ≤ 16 / L := by
          apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
          nlinarith

  exact singTruncEval_of_parts singSeriesIdentity_proof singSeriesTail_proof

/-- The Euler factors of `Sing` are `1 + a_p` with `a_p` summable, so every finite partial
product is at most `exp (Σ_p 4/p²)`; `Sing` lies in `[0, exp (Σ_p 4/p²)]`. Private helper. -/
private theorem singBounded_aux : SingBounded := by
  set S := ∑' p : {p : ℕ // p.Prime}, (4 : ℝ) / ((p.1 : ℝ) ^ 2) with hS
  refine ⟨Real.exp S, fun N => ?_⟩
  set f : {p : ℕ // p.Prime} → ℝ := fun p =>
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3 with hf
  have hm : HasProd f (Sing N) := (sing_multipliable N).hasProd
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    have h2 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
      linarith
    simp only [hf]
    split_ifs
    · rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith
    · positivity
  have hf1 : ∀ p, f p ≤ Real.exp (4 / ((p.1 : ℝ) ^ 2)) := by
    intro p
    have hb : f p ≤ 1 + 4 / ((p.1 : ℝ) ^ 2) := by
      have h2 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
        linarith
      have hc := factor_bound p.2 (abs_cube_le p.2)
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at hc
      simp only [hf]
      split_ifs
      · have : 0 ≤ 4 / ((p.1 : ℝ) ^ 2) := by positivity
        have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 2 := by positivity
        linarith
      · linarith
    exact hb.trans (by have := Real.add_one_le_exp (4 / ((p.1 : ℝ) ^ 2)); linarith)
  have hsum := summable_four_div_sq_primes
  have hfin : ∀ s : Finset {p : ℕ // p.Prime}, ∏ p ∈ s, f p ≤ Real.exp S := by
    intro s
    calc ∏ p ∈ s, f p ≤ ∏ p ∈ s, Real.exp (4 / ((p.1 : ℝ) ^ 2)) :=
          Finset.prod_le_prod₀ (fun p _ => hf0 p) (fun p _ => hf1 p)
      _ = Real.exp (∑ p ∈ s, 4 / ((p.1 : ℝ) ^ 2)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp S := Real.exp_le_exp.mpr
          (hsum.sum_le_tsum s (fun p _ => by positivity))
  have hup : Sing N ≤ Real.exp S := le_of_tendsto' hm hfin
  have hlo : 0 ≤ Sing N := ge_of_tendsto' hm (fun s => Finset.prod_nonneg (fun p _ => hf0 p))
  rw [abs_of_nonneg hlo]
  exact hup

/-- LEAF: Page 260, the singular series is bounded: every factor of `Sing` lies in `[0, 2]`
and `∏ (1 + 1/(p-1)³)` over odd primes converges. EASY. -/
theorem singBounded_leaf : SingBounded := singBounded_aux

/-- Page 271, the major arc display after (3.21), PROVED from steps 2 to 5. -/
theorem majorEval_of_steps (h2 : MajorAssembly) (h3 : SingIntEval) (h4 : SingTruncEval)
    (h5 : SingBounded) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  obtain ⟨a₀, ha₀, hA⟩ := h2
  obtain ⟨b₀, hb₀, hB⟩ := h4
  obtain ⟨C, hC⟩ := h5
  refine ⟨max a₀ b₀, lt_of_lt_of_le ha₀ (le_max_left _ _), ?_⟩
  intro d hd c hc
  obtain ⟨K2, N2, hK2⟩ := hA d ((le_max_left _ _).trans hd) c hc
  obtain ⟨K4, N4, hK4⟩ := hB d ((le_max_right _ _).trans hd)
  obtain ⟨K3, N3, hK3⟩ := h3 c hc
  refine ⟨|K2| + |K4| * (3 + |K3|) + |C| * |K3|, max (max N2 N3) (max N4 (Real.exp 1)), ?_⟩
  intro N hN hlarge
  have hN2 : N2 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hlarge)
  have hN3 : N3 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hlarge)
  have hN4 : N4 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hLpos : 0 < Real.log N := by linarith
  set L := Real.log N with hLdef
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set M := majorTerm110 N U d
  set sT := singTrunc N (L ^ d)
  set I := singInt N U (L ^ (4 : ℝ) / U)
  have e2 := hK2 N hN hN2
  have e3 := hK3 N hN3
  have e4 := hK4 N hN hN4
  have hC0 : |Sing N| ≤ |C| := (hC N).trans (le_abs_self _)
  have h4eq : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) / L := by
    rw [show (-4 : ℝ) = -3 - 1 by norm_num, Real.rpow_sub hLpos, Real.rpow_one]
  have hP3 : 0 ≤ U ^ 2 * L ^ (-3 : ℝ) := by
    have := Real.rpow_nonneg hLpos.le (-3 : ℝ); positivity
  have hP4 : 0 ≤ U ^ 2 * L ^ (-4 : ℝ) := by
    have := Real.rpow_nonneg hLpos.le (-4 : ℝ); positivity
  have hP43 : U ^ 2 * L ^ (-4 : ℝ) ≤ U ^ 2 * L ^ (-3 : ℝ) := by
    rw [h4eq, mul_div_assoc']
    exact div_le_self hP3 hL1
  have hI : |I| ≤ (3 + |K3|) * (U ^ 2 * L ^ (-3 : ℝ)) := by
    have hK3' : K3 * U ^ 2 * L ^ (-4 : ℝ) ≤ |K3| * (U ^ 2 * L ^ (-3 : ℝ)) := by
      calc K3 * U ^ 2 * L ^ (-4 : ℝ) = K3 * (U ^ 2 * L ^ (-4 : ℝ)) := by ring
        _ ≤ |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hP4
        _ ≤ |K3| * (U ^ 2 * L ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hP43 (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub I (3 * U ^ 2 * L ^ (-3 : ℝ))
    have h3abs : |3 * U ^ 2 * L ^ (-3 : ℝ)| = 3 * (U ^ 2 * L ^ (-3 : ℝ)) := by
      rw [abs_of_nonneg (by nlinarith)]; ring
    rw [h3abs] at this
    nlinarith
  have hmid : |sT - Sing N| * |I| ≤ |K4| * (3 + |K3|) * (U ^ 2 * L ^ (-4 : ℝ)) := by
    have hs : |sT - Sing N| ≤ |K4| / L :=
      e4.trans (div_le_div_of_nonneg_right (le_abs_self _) hLpos.le)
    calc |sT - Sing N| * |I| ≤ (|K4| / L) * ((3 + |K3|) * (U ^ 2 * L ^ (-3 : ℝ))) :=
          mul_le_mul hs hI (abs_nonneg _) (by positivity)
      _ = |K4| * (3 + |K3|) * (U ^ 2 * (L ^ (-3 : ℝ) / L)) := by ring
      _ = |K4| * (3 + |K3|) * (U ^ 2 * L ^ (-4 : ℝ)) := by rw [h4eq]
  have hlast : |Sing N| * |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| ≤ |C| * |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := by
    have hK3'' : |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| ≤ |K3| * (U ^ 2 * L ^ (-4 : ℝ)) :=
      e3.trans (by
        calc K3 * U ^ 2 * L ^ (-4 : ℝ) = K3 * (U ^ 2 * L ^ (-4 : ℝ)) := by ring
          _ ≤ |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hP4)
    calc |Sing N| * |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| ≤ |C| * (|K3| * (U ^ 2 * L ^ (-4 : ℝ))) :=
          mul_le_mul hC0 hK3'' (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hfirst : |M - sT * I| ≤ |K2| * (U ^ 2 * L ^ (-4 : ℝ)) :=
    e2.trans (by
      calc K2 * U ^ 2 * L ^ (-4 : ℝ) = K2 * (U ^ 2 * L ^ (-4 : ℝ)) := by ring
        _ ≤ |K2| * (U ^ 2 * L ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hP4)
  have hsplit : M - 3 * Sing N * U ^ 2 * L ^ (-3 : ℝ) =
      (M - sT * I) + (sT - Sing N) * I + Sing N * (I - 3 * U ^ 2 * L ^ (-3 : ℝ)) := by ring
  rw [hsplit]
  calc |(M - sT * I) + (sT - Sing N) * I + Sing N * (I - 3 * U ^ 2 * L ^ (-3 : ℝ))|
      ≤ |M - sT * I| + |(sT - Sing N) * I| + |Sing N * (I - 3 * U ^ 2 * L ^ (-3 : ℝ))| :=
        abs_add_three _ _ _
    _ = |M - sT * I| + |sT - Sing N| * |I| + |Sing N| * |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |K2| * (U ^ 2 * L ^ (-4 : ℝ)) + |K4| * (3 + |K3|) * (U ^ 2 * L ^ (-4 : ℝ)) +
        |C| * |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := by linarith
    _ = _ := by ring

/-- `major_evaluation110` through the split: step 1 cited, steps 2 to 5 LEAFs. Shows `sorryAx`
until they close. -/
theorem major_evaluation_split :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) :=
  majorEval_of_steps (majorAssembly_of_approx majorArcApprox_cited) singIntEval_leaf
    singTruncEval_leaf singBounded_leaf

end

end LeanLab.Zhan1991
