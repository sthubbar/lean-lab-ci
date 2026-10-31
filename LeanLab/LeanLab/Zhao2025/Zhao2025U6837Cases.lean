import Mathlib
import LeanLab.Zhao2025.Zhao2025U6825Lemma31

/-!
# Zhao 2025, the R inputs of (4.23) and the unwritten cases `λ₁,₁ ∈ [0.62, H]`

G. Zhao, "The exceptional set of Goldbach problem and Linnik's constant", arXiv 2511.05631v2,
a preprint.  Unit U-6837, CLOUD 20261021T0316Z-cloud57.  AI wrote the Lean code.
Binary Goldbach is open.

Proved unconditionally here:
* exponential enclosures and the value of the `N ≤ N*` branch (3.42) of Zhao's R bound in
  three places: at (4.23) with `N* = 3` it is at most `0.2853`, under the printed `0.300`;
  at (4.18) with `N* = 3` it is at most `0.5513`, under the printed `0.556`; at (4.18) with
  `N* = 4`, the value the text names, it exceeds `0.5902`, above the printed `0.556`.
  So the printed `R₁ ≤ 0.556` of (4.18) is the `N* = 3` bound, not the `N* = 4` bound the text
  names; with `N* = 4` the case `i₀ = 1` of (4.19) would give `(0.5902 + 0.0808)² > 0.45` and
  (4.20) would exceed 1.  A cosmetic QUESTION: any `N*` is admissible, so `N* = 3` is valid.
* `term_bound`, `layout4`: the elementary inequality behind the (4.24) layout, refined per set,
  `Σ (Rᵢ + Tᵢ)² ≤ r ΣR + t (2 ΣR + ΣT) + Σ_{i<4} (ρᵢ (ρᵢ - r) + (τᵢ - t)(2ρᵢ + τᵢ))`.
* `layoutA_064_value`: the literal (4.24) shaped bound at the lab inputs for `[0.64, 0.66]`,
  rounded down, is above `1`; with a finer (3.27) grid it is below `1`, so this is a grid artefact.

Conditional, on the per set inputs computed by the lab from Zhao (3.15), (3.27), (3.38), (3.42),
(3.43) and Lemma 2.4, taken as named hypotheses: each case `[0.60, 0.62]`, `[0.62, 0.64]`,
`[0.64, 0.66]`, `[0.66, 0.68]`, `[0.68, H]` closes below `1` in the refined layout.  Vacuity
instance `cases_vacuity`.
-/

namespace LeanLab.Zhao2025.U6837

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6825

/-! ### Exponential enclosures, width `10⁻¹⁰` -/

theorem x43 : 0.2635971381 ≤ Real.exp (-(4 / 3)) ∧ Real.exp (-(4 / 3)) ≤ 0.2635971382 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem x4615 : 0.0465761502 ≤ Real.exp (-(46 / 15)) ∧ Real.exp (-(46 / 15)) ≤ 0.0465761503 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem x489 : 0.0075214224 ≤ Real.exp (-(489 / 100)) ∧ Real.exp (-(489 / 100)) ≤ 0.0075214225 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem x2 : 0.1353352832 ≤ Real.exp (-(2 : ℝ)) ∧ Real.exp (-(2 : ℝ)) ≤ 0.1353352833 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem x33775 : 0.0111833039 ≤ Real.exp (-(337 / 75)) ∧ Real.exp (-(337 / 75)) ≤ 0.0111833040 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem x9130 : 0.0481548541 ≤ Real.exp (-(91 / 30)) ∧ Real.exp (-(91 / 30)) ≤ 0.0481548542 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

/-! ### The `N ≤ N*` branch (3.42).  `e^{-10λ/3}` at `λ = 0.40, 0.92, 1.467` is `e^{-4/3}`,
`e^{-46/15}`, `e^{-4.89}`; at `λ = 0.60, 0.91, 1.348` it is `e^{-2}`, `e^{-91/30}`, `e^{-337/75}`. -/

/-- (3.42) at (4.23), `λ₁ = λ₂ = 0.60`, `λ* = 0.91`, `Λ = 1.348`, `N* = 3`: at most `0.2853`,
under the printed `max Rᵢ ≤ 0.300`. -/
theorem br342_423_N3 :
    2 * (Real.exp (-(2 : ℝ)) - Real.exp (-(337 / 75))) +
      (3 - 2) * (Real.exp (-(91 / 30)) - Real.exp (-(337 / 75))) ≤ 0.2853 := by
  obtain ⟨_, a2⟩ := x2; obtain ⟨b1, _⟩ := x33775; obtain ⟨_, c2⟩ := x9130
  linarith

/-- (3.42) at (4.18), `λ₁ = λ₂ = 0.40`, `λ* = 0.92`, `Λ = 1.467`, `N* = 3`: at most `0.5513`,
under the printed `R₁ ≤ 0.556`. -/
theorem br342_418_N3 :
    2 * (Real.exp (-(4 / 3)) - Real.exp (-(489 / 100))) +
      (3 - 2) * (Real.exp (-(46 / 15)) - Real.exp (-(489 / 100))) ≤ 0.5513 := by
  obtain ⟨_, a2⟩ := x43; obtain ⟨b1, _⟩ := x489; obtain ⟨_, c2⟩ := x4615
  linarith

/-- (3.42) at (4.18) with `N* = 4`, the value the text of p. 15 names: above `0.5902`, so above
the printed `R₁ ≤ 0.556`.  The bound from (3.42) and (3.43) is the larger of the two branches,
hence also above `0.556`. -/
theorem br342_418_N4 :
    0.5902 < 2 * (Real.exp (-(4 / 3)) - Real.exp (-(489 / 100))) +
      (4 - 2) * (Real.exp (-(46 / 15)) - Real.exp (-(489 / 100))) := by
  obtain ⟨a1, _⟩ := x43; obtain ⟨_, b2⟩ := x489; obtain ⟨c1, _⟩ := x4615
  linarith

/-- With `R₁ ≤ 0.5902` in (4.19) and Zhao's `0.5817` of (4.14), (4.20) would exceed `1`. -/
theorem eq420_with_N4 : (1 : ℝ) < 0.5817 + (0.5902 + 0.0808) ^ 2 := by norm_num

/-! ### The layout -/

/-- One set: `(R + T)² ≤ r R + t (2R + T) + ρ (ρ - r) + (τ - t)(2ρ + τ)`. -/
theorem term_bound {R T ρ τ r t : ℝ} (hR0 : 0 ≤ R) (hT0 : 0 ≤ T) (hR : R ≤ ρ) (hT : T ≤ τ)
    (hr : r ≤ ρ) (ht : t ≤ τ) (hr0 : 0 ≤ r) (ht0 : 0 ≤ t) :
    (R + T) ^ 2 ≤ r * R + t * (2 * R + T) + (ρ * (ρ - r) + (τ - t) * (2 * ρ + τ)) := by
  have h1 : R * R ≤ r * R + ρ * (ρ - r) := by
    rcases le_total R r with h | h
    · nlinarith [mul_nonneg hR0 (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 hr) (hr0.trans hr)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hR) (by linarith : (0 : ℝ) ≤ ρ + R - r)]
  have h2 : T * (2 * R + T) ≤ t * (2 * R + T) + (τ - t) * (2 * ρ + τ) := by
    rcases le_total T t with h | h
    · nlinarith [mul_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ 2 * R + T),
        mul_nonneg (sub_nonneg.2 ht) (by linarith : (0 : ℝ) ≤ 2 * ρ + τ)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hT) (by linarith : (0 : ℝ) ≤ 2 * ρ + τ),
        mul_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ 2 * ρ + τ - 2 * R - T)]
  nlinarith

/-- Head values for the first four sets, `d` for every later set. -/
def hd (a0 a1 a2 a3 d : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3 else d

/-- The extra term of one set. -/
def ex (r t ρ τ : ℝ) : ℝ := ρ * (ρ - r) + (τ - t) * (2 * ρ + τ)

theorem ex_nonneg {r t ρ τ : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ ρ) (ht : t ≤ τ) (ht0 : 0 ≤ t) :
    0 ≤ ex r t ρ τ := by
  unfold ex
  have := mul_nonneg (hr0.trans hr) (sub_nonneg.2 hr)
  have := mul_nonneg (sub_nonneg.2 ht) (by linarith : (0 : ℝ) ≤ 2 * ρ + τ)
  linarith

/-- The refined (4.24) layout for any number `n` of sets, the first four with their own bounds
`ρₖ`, `τₖ`, every later one with `r`, `t`. -/
theorem layout4 (n : ℕ) (R T : ℕ → ℝ) (r t sR sT ρ0 ρ1 ρ2 ρ3 τ0 τ1 τ2 τ3 : ℝ)
    (hr0 : 0 ≤ r) (ht0 : 0 ≤ t) (hρ0 : r ≤ ρ0) (hρ1 : r ≤ ρ1) (hρ2 : r ≤ ρ2) (hρ3 : r ≤ ρ3)
    (hτ0 : t ≤ τ0) (hτ1 : t ≤ τ1) (hτ2 : t ≤ τ2) (hτ3 : t ≤ τ3)
    (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hR : ∀ i, R i ≤ hd ρ0 ρ1 ρ2 ρ3 r i) (hT : ∀ i, T i ≤ hd τ0 τ1 τ2 τ3 t i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ sR) (hsT : ∑ i ∈ Finset.range n, T i ≤ sT) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 ≤
      r * sR + t * (2 * sR + sT) +
        (ex r t ρ0 τ0 + ex r t ρ1 τ1 + ex r t ρ2 τ2 + ex r t ρ3 τ3) := by
  set ρ := hd ρ0 ρ1 ρ2 ρ3 r
  set τ := hd τ0 τ1 τ2 τ3 t
  have hρ : ∀ i, r ≤ ρ i := fun i => by
    simp only [ρ, hd]; split_ifs <;> first | assumption | exact le_refl r
  have hτ : ∀ i, t ≤ τ i := fun i => by
    simp only [τ, hd]; split_ifs <;> first | assumption | exact le_refl t
  have hex0 : ∀ i, 0 ≤ ex r t (ρ i) (τ i) := fun i => ex_nonneg hr0 (hρ i) (hτ i) ht0
  have step : ∑ i ∈ Finset.range n, (R i + T i) ^ 2 ≤
      ∑ i ∈ Finset.range n, (r * R i + t * (2 * R i + T i) + ex r t (ρ i) (τ i)) :=
    Finset.sum_le_sum fun i _ =>
      term_bound (hR0 i) (hT0 i) (hR i) (hT i) (hρ i) (hτ i) hr0 ht0
  have split : ∑ i ∈ Finset.range n, (r * R i + t * (2 * R i + T i) + ex r t (ρ i) (τ i)) =
      r * ∑ i ∈ Finset.range n, R i +
        t * (2 * ∑ i ∈ Finset.range n, R i + ∑ i ∈ Finset.range n, T i) +
        ∑ i ∈ Finset.range n, ex r t (ρ i) (τ i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have hex : ∑ i ∈ Finset.range n, ex r t (ρ i) (τ i) ≤
      ex r t ρ0 τ0 + ex r t ρ1 τ1 + ex r t ρ2 τ2 + ex r t ρ3 τ3 := by
    calc ∑ i ∈ Finset.range n, ex r t (ρ i) (τ i)
        ≤ ∑ i ∈ Finset.range (4 + n), ex r t (ρ i) (τ i) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega) (fun i _ _ => hex0 i)
      _ = ex r t ρ0 τ0 + ex r t ρ1 τ1 + ex r t ρ2 τ2 + ex r t ρ3 τ3 := by
          rw [Finset.sum_range_add]
          have hz : ∀ x ∈ Finset.range n, ex r t (ρ (4 + x)) (τ (4 + x)) = 0 := by
            intro x _
            simp [ρ, τ, hd, ex, show 4 + x ≠ 0 by omega, show 4 + x ≠ 1 by omega,
              show 4 + x ≠ 2 by omega, show 4 + x ≠ 3 by omega]
          rw [Finset.sum_eq_zero hz, add_zero]
          simp [Finset.sum_range_succ, ρ, τ, hd]
  have hsR0 : 0 ≤ ∑ i ∈ Finset.range n, R i := Finset.sum_nonneg fun i _ => hR0 i
  have hsT0 : 0 ≤ ∑ i ∈ Finset.range n, T i := Finset.sum_nonneg fun i _ => hT0 i
  have := mul_le_mul_of_nonneg_left hsR hr0
  have := mul_le_mul_of_nonneg_left
    (by linarith : 2 * ∑ i ∈ Finset.range n, R i + ∑ i ∈ Finset.range n, T i ≤ 2 * sR + sT) ht0
  linarith

/-! ### Layout A, the literal (4.24) shape, at `[0.64, 0.66]` -/

/-- `maxR ΣR + t₅ (2ΣR + ΣT) + 2 (t₁ - t₅)(2 maxR + t₁) + 2 (t₃ - t₅)(2 maxR + t₃)` at the lab
inputs of numerics/zhao_U6837_cases.out for `[0.64, 0.66]`, `Λ = 1.363`, each rounded down:
above `1`.  This is a value of an upper bound, not a proof that the case fails: with a 400
step grid in (3.27) the same layout gives `0.9984`, numerics/zhao_U6837_grid400.out. -/
theorem layoutA_064_value :
    1 < (0.2973 : ℝ) * 0.6642 + 0.0906 * (2 * 0.6642 + 7.446) +
      2 * (0.0957 - 0.0906) * (2 * 0.2973 + 0.0957) +
      2 * (0.0932 - 0.0906) * (2 * 0.2973 + 0.0932) := by norm_num

/-! ### The refined layout C closes each case, CONDITIONAL on the lab inputs

For each case the hypotheses are the per set bounds the lab computed from Zhao's own displays,
numerics/zhao_U6837_layoutC.out by method A and zhao_U6837_indep.out, zhao_U6837_indep2.out by
method B, each rounded up past the larger of the two:
`rA` is (3.42), (3.43) with `λ₁ = λ₂ = λ₁,₁`, `λ*`; `rB` with `λ₁ = λ₁,₁`, `λ₂ = λ*`; `r3` with
`λ₁ = λ₂ = λ*`; `sR` is (3.38) on the union; `sT` is (3.15) general `k`; `t1`, `t3`, `t5` are
(3.27) at `λ₀ = λ₁,₁`, `λ*` and the tail value.  `hcfg` is the dichotomy of Lemma 2.4: both zeros
below `λ*` lie in the first set, or one in each of the first two. -/

theorem closes_of (n : ℕ) (R T : ℕ → ℝ) (rA rB r3 sR sT t1 t3 t5 : ℝ)
    (h0 : 0 ≤ r3) (h1 : 0 ≤ t5) (h2 : r3 ≤ rA) (h3 : r3 ≤ rB) (h4 : t5 ≤ t1) (h5 : t5 ≤ t3)
    (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ sR) (hsT : ∑ i ∈ Finset.range n, T i ≤ sT)
    (hcfg : (∀ i, R i ≤ hd rA r3 r3 r3 r3 i ∧ T i ≤ hd t1 t3 t3 t3 t5 i) ∨
      (∀ i, R i ≤ hd rB rB r3 r3 r3 i ∧ T i ≤ hd t1 t1 t3 t3 t5 i))
    (ha : r3 * sR + t5 * (2 * sR + sT) +
      (ex r3 t5 rA t1 + ex r3 t5 r3 t3 + ex r3 t5 r3 t3 + ex r3 t5 r3 t3) < 1)
    (hb : r3 * sR + t5 * (2 * sR + sT) +
      (ex r3 t5 rB t1 + ex r3 t5 rB t1 + ex r3 t5 r3 t3 + ex r3 t5 r3 t3) < 1) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1 := by
  rcases hcfg with h | h
  · exact lt_of_le_of_lt (layout4 n R T r3 t5 sR sT rA r3 r3 r3 t1 t3 t3 t3 h0 h1 h2 le_rfl le_rfl
      le_rfl h4 h5 h5 h5 hR0 hT0 (fun i => (h i).1) (fun i => (h i).2) hsR hsT) ha
  · exact lt_of_le_of_lt (layout4 n R T r3 t5 sR sT rB rB r3 r3 t1 t1 t3 t3 h0 h1 h3 h3 le_rfl
      le_rfl h4 h4 h5 h5 hR0 hT0 (fun i => (h i).1) (fun i => (h i).2) hsR hsT) hb

/-- Case [0.60, 0.62], `N(0.91) ≤ 2`, `Λ = 1.348`, `λ* = 0.91`, sets `i ≥ 3` at `λ₀ = 0.91`.  CONDITIONAL ON the lab inputs as hypotheses. -/
theorem case060_closes (n : ℕ) (R T : ℕ → ℝ) (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.57982) (hsT : ∑ i ∈ Finset.range n, T i ≤ 7.6236)
    (hcfg : (∀ i, R i ≤ hd 0.29940 0.14790 0.14790 0.14790 0.14790 i ∧ T i ≤ hd 0.10023 0.09272 0.09272 0.09272 0.09272 i) ∨
      (∀ i, R i ≤ hd 0.23508 0.23508 0.14790 0.14790 0.14790 i ∧ T i ≤ hd 0.10023 0.10023 0.09272 0.09272 0.09272 i)) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1 :=
  closes_of n R T 0.29940 0.23508 0.14790 0.57982 7.6236 0.10023 0.09272 0.09272 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])

/-- Case [0.62, 0.64], `N(0.85) ≤ 2`, `Λ = 1.355`, `λ* = 0.85`, sets `i ≥ 5` at `λ₀ = 0.857`.  CONDITIONAL ON the lab inputs as hypotheses. -/
theorem case062_closes (n : ℕ) (R T : ℕ → ℝ) (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.59615) (hsT : ∑ i ∈ Finset.range n, T i ≤ 7.5381)
    (hcfg : (∀ i, R i ≤ hd 0.29306 0.19150 0.19150 0.19150 0.19150 i ∧ T i ≤ hd 0.09797 0.09241 0.09241 0.09241 0.09230 i) ∨
      (∀ i, R i ≤ hd 0.25205 0.25205 0.19150 0.19150 0.19150 i ∧ T i ≤ hd 0.09797 0.09797 0.09241 0.09241 0.09230 i)) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1 :=
  closes_of n R T 0.29306 0.25205 0.19150 0.59615 7.5381 0.09797 0.09241 0.09230 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])

/-- Case [0.64, 0.66], `N(0.74) ≤ 2`, `Λ = 1.363`, `λ* = 0.74`, sets `i ≥ 5` at `λ₀ = 0.857`.  CONDITIONAL ON the lab inputs as hypotheses. -/
theorem case064_closes (n : ℕ) (R T : ℕ → ℝ) (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.66426) (hsT : ∑ i ∈ Finset.range n, T i ≤ 7.4466)
    (hcfg : (∀ i, R i ≤ hd 0.29738 0.24889 0.24889 0.24889 0.24889 i ∧ T i ≤ hd 0.09572 0.09321 0.09321 0.09321 0.09063 i) ∨
      (∀ i, R i ≤ hd 0.27836 0.27836 0.24889 0.24889 0.24889 i ∧ T i ≤ hd 0.09572 0.09572 0.09321 0.09321 0.09063 i)) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1 :=
  closes_of n R T 0.29738 0.27836 0.24889 0.66426 7.4466 0.09572 0.09321 0.09063 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])

/-- Case [0.66, 0.68], `N(0.74) ≤ 2`, `Λ = 1.370`, `λ* = 0.74`, sets `i ≥ 5` at `λ₀ = 0.857`.  CONDITIONAL ON the lab inputs as hypotheses. -/
theorem case066_closes (n : ℕ) (R T : ℕ → ℝ) (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.64932) (hsT : ∑ i ∈ Finset.range n, T i ≤ 7.3632)
    (hcfg : (∀ i, R i ≤ hd 0.28824 0.25104 0.25104 0.25104 0.25104 i ∧ T i ≤ hd 0.09359 0.09166 0.09166 0.09166 0.08900 i) ∨
      (∀ i, R i ≤ hd 0.27380 0.27380 0.25104 0.25104 0.25104 i ∧ T i ≤ hd 0.09359 0.09359 0.09166 0.09166 0.08900 i)) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1 :=
  closes_of n R T 0.28824 0.27380 0.25104 0.64932 7.3632 0.09359 0.09166 0.08900 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])

/-- Case [0.68, H], `N(0.702) ≤ 2`, `Λ = 1.378`, `λ* = 0.702`, sets `i ≥ 5` at `λ₀ = 0.857`.  CONDITIONAL ON the lab inputs as hypotheses. -/
theorem case068_closes (n : ℕ) (R T : ℕ → ℝ) (hR0 : ∀ i, 0 ≤ R i) (hT0 : ∀ i, 0 ≤ T i)
    (hsR : ∑ i ∈ Finset.range n, R i ≤ 0.67914) (hsT : ∑ i ∈ Finset.range n, T i ≤ 7.2739)
    (hcfg : (∀ i, R i ≤ hd 0.28735 0.27703 0.27703 0.27703 0.27703 i ∧ T i ≤ hd 0.09121 0.09112 0.09112 0.09112 0.08733 i) ∨
      (∀ i, R i ≤ hd 0.28342 0.28342 0.27703 0.27703 0.27703 i ∧ T i ≤ hd 0.09121 0.09121 0.09112 0.09112 0.08733 i)) :
    ∑ i ∈ Finset.range n, (R i + T i) ^ 2 < 1 :=
  closes_of n R T 0.28735 0.28342 0.27703 0.67914 7.2739 0.09121 0.09112 0.08733 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hR0 hT0 hsR hsT hcfg (by norm_num [ex]) (by norm_num [ex])

/-- Vacuity: the hypotheses of `case064_closes` are satisfiable, by three sets with `Rᵢ = 0.2`, `Tᵢ = 0.09`. -/
theorem cases_vacuity : ∃ (n : ℕ) (R T : ℕ → ℝ), (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ T i) ∧
    ∑ i ∈ Finset.range n, R i ≤ 0.66426 ∧ ∑ i ∈ Finset.range n, T i ≤ 7.4466 ∧
    ((∀ i, R i ≤ hd 0.29738 0.24889 0.24889 0.24889 0.24889 i ∧
      T i ≤ hd 0.09572 0.09321 0.09321 0.09321 0.09063 i) ∨
     (∀ i, R i ≤ hd 0.27836 0.27836 0.24889 0.24889 0.24889 i ∧
      T i ≤ hd 0.09572 0.09572 0.09321 0.09321 0.09063 i)) := by
  refine ⟨3, fun _ => 0.2, fun _ => 0.09, fun _ => by norm_num, fun _ => by norm_num, ?_, ?_, ?_⟩
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]
  · left; intro i; simp only [hd]; split_ifs <;> norm_num

end LeanLab.Zhao2025.U6837
