/-
P0015 H. L. Montgomery, R. C. Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27 (1975), 353-370. Unit U-1432, PC run 20261021T1403Z-5629, track T1 PROVE.
AI wrote this Lean code; the Lean kernel checked it. Binary Goldbach is OPEN.

The major arc count (8.3) p. 367 in the case of NO exceptional character.

SOURCE CAVEAT: the impan.pl scan could not be fetched in this unit, WebFetch CLIENT_ERROR four
times. The printed shapes below are taken from U-1423's reading of the page images, recorded
in ADD-U1423.md, and from U-6802's docstrings in MontgomeryVaughan1975.lean. Each cited Prop
carries a VERIFY note.

* `ExcZero c₁ P`: some real primitive nonprincipal `χ̃` mod `r̃ ≤ P` has a real zero
  `β̃ > 1 - c₁/log P` of `L(s, χ̃)`, Lemma 4.1's exceptional zero.
* `Gallagher71NoExc`, the shape of Gallagher's bound (7.1) as used in section 7, in the case of
  no exceptional character; a cited Prop.
* `gallagher_exp_at_P`: at `P = X^{6δ}` the saving `exp(-c log X/log P)` is `exp(-c/(6δ))`.
  PROVED.
* `singProd`, the Euler product `∏_{p | n, p > 2} (p-1)/(p-2)` of `𝔖(n) = 2C₂ singProd n`;
  `div_totient_le_singProd`: for even `n`, `n/φ(n) ≤ 2 singProd n`, so `𝔖(n) ≥ C₂ n/φ(n)`.
  PROVED.
* `NoExcR1`, the no exceptional character display of p. 367,
  `R₁(n) = 𝔖(n) n + O(n φ(n)^{-1} X exp(-c₇ δ^{-1}))`, in the lab's discrete normalization; a
  cited Prop.
* `majorCount83_noExc`: from `NoExcR1`, for every small `δ` NO even `n` in the window has small
  major part when there is no exceptional zero, so the count of (8.3) is 0. CONDITIONAL ON
  `NoExcR1`.
* `theorem1_of_noExc`: Theorem 1 CONDITIONAL ON `NoExcR1` and `NoSiegel c₁`, the hypothesis
  that no exceptional zero ever occurs; the exceptional case is left open.
-/
import LeanLab.ExceptionalSet.U1423MVMinor
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace LeanLab.ExceptionalSet.MV75U1432

open Real Finset Filter
open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.MV LeanLab.ExceptionalSet.MV75U1423
open ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-! ### The exceptional zero, Lemma 4.1 -/

/-- Lemma 4.1's exceptional character: a real primitive nonprincipal `χ̃` mod `r̃`, `r̃ ≤ P`,
whose `L`-function has a real zero `β̃` with `1 - c₁/log P < β̃ < 1`. -/
def ExcZero (c₁ P : ℝ) : Prop :=
  ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r), 1 ≤ r ∧ (r : ℝ) ≤ P ∧
    χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    ∃ β : ℝ, 1 - c₁ / Real.log P < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0

/-- The hypothesis that no exceptional zero occurs at any level `P ≥ 1`. Not printed; a
Siegel zero free hypothesis, used only to state the no exceptional case globally. -/
def NoSiegel (c₁ : ℝ) : Prop := ∀ P : ℝ, 1 ≤ P → ¬ ExcZero c₁ P

/-! ### Gallagher's bound (7.1) -/

/-- `ψ(y, χ) = Σ_{m ≤ y} χ(m) Λ(m)`. -/
noncomputable def psiChi {r : ℕ} (χ : DirichletCharacter ℂ r) (y : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊y⌋₊, χ (m : ZMod r) * (Λ m : ℂ)

/-- `E₀ = 1` for the principal character mod 1, else 0. -/
def E0 (ρ : Σ r : ℕ, DirichletCharacter ℂ r) : ℝ := if ρ.1 = 1 then 1 else 0

/-- (7.1), Gallagher's Theorem 7 in the modified form of section 7, no exceptional character:
for `N ≥ N0`, `log N ≤ P ≤ N^b` and no exceptional zero at level `P`, every finite family of
primitive characters `χ` mod `r ≤ P` and every choice `0 ≤ y, h ≤ N` per character satisfy
`Σ (h + N/P)^{-1} |ψ(y + h, χ) - ψ(y, χ) - E₀ h| ≤ B exp(-c log N/log P)`.
The finite family with free `y, h` is the printed double maximum. VERIFY against p. 362 to 363:
reconstructed, the scan was not readable in this unit. -/
def Gallagher71NoExc (c₁ c B b : ℝ) (N0 : ℝ) : Prop :=
  ∀ N P : ℝ, N0 ≤ N → Real.log N ≤ P → P ≤ N ^ b → ¬ ExcZero c₁ P →
    ∀ F : Finset (Σ r : ℕ, DirichletCharacter ℂ r),
      (∀ ρ ∈ F, 1 ≤ ρ.1 ∧ (ρ.1 : ℝ) ≤ P ∧ ρ.2.IsPrimitive) →
      ∀ y h : (Σ r : ℕ, DirichletCharacter ℂ r) → ℝ,
        (∀ ρ ∈ F, 0 ≤ y ρ ∧ y ρ ≤ N ∧ 0 ≤ h ρ ∧ h ρ ≤ N) →
        ∑ ρ ∈ F, (h ρ + N / P)⁻¹ *
            ‖psiChi ρ.2 (y ρ + h ρ) - psiChi ρ.2 (y ρ) - (E0 ρ * h ρ : ℝ)‖ ≤
          B * Real.exp (-(c * Real.log N / Real.log P))

/-- Vacuity of the shape: the empty family satisfies the bound for every `B ≥ 0`. -/
theorem gallagher71_empty (c B N P : ℝ) (hB : 0 ≤ B) :
    ∑ ρ ∈ (∅ : Finset (Σ r : ℕ, DirichletCharacter ℂ r)), ((0 : ℝ) + N / P)⁻¹ * ‖(ρ.1 : ℂ)‖ ≤
      B * Real.exp (-(c * Real.log N / Real.log P)) := by
  rw [sum_empty]; positivity

/-- At `P = N^{6δ}`, `N > 1`, `δ > 0`: `exp(-c log N/log P) = exp(-c/(6δ))`. PROVED. -/
theorem gallagher_exp_at_P {N δ c : ℝ} (hN : 1 < N) (hδ : 0 < δ) :
    Real.exp (-(c * Real.log N / Real.log (N ^ (6 * δ)))) = Real.exp (-(c / (6 * δ))) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  rw [Real.log_rpow hN0]
  congr 2
  field_simp

/-- `P = N^{6δ}` lies in `[log N, N^{1/4}]` for `δ ≤ 1/24` and `N` large: the upper half. -/
theorem P_le_quarter' {N δ : ℝ} (hN : 1 ≤ N) (hδ : δ ≤ 1 / 24) : N ^ (6 * δ) ≤ N ^ (1 / 4 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-! ### The singular series, section 6 -/

/-- `∏_{p | n, p > 2} (p-1)/(p-2)`; `𝔖(n) = 2 C₂ singProd n` for even `n`. -/
noncomputable def singProd (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.erase 2, (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- `n/φ(n) = ∏_{p | n} p/(p-1)`. -/
theorem div_totient_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors n
  have hR : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h' := congrArg (fun t : ℕ => (t : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at h'
    rw [h']
    congr 1
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.pos_of_mem_primeFactors hp)]; simp
  have hφ : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hp1 : ∀ p ∈ n.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hQ : 0 < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := prod_pos hp1
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hQ.ne']
  linarith [hR]

/-- p. 366 to 368, `𝔖(n) ≫ n/φ(n)`: for even `n ≠ 0`, `n/φ(n) ≤ 2 singProd n`, since
`p/(p-1) ≤ (p-1)/(p-2)` for `p ≥ 3` and the factor at 2 is 2. PROVED. -/
theorem div_totient_le_singProd {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    (n : ℝ) / (Nat.totient n : ℝ) ≤ 2 * singProd n := by
  rw [div_totient_eq_prod hn]
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp he, hn⟩
  rw [← mul_prod_erase _ _ h2, singProd]
  rw [show ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp' := (mem_erase.mp hp)
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp'.2).two_le
    apply div_nonneg <;> linarith
  · intro p hp
    have hp' := (mem_erase.mp hp)
    have hpr := Nat.prime_of_mem_primeFactors hp'.2
    have h3 : (3 : ℝ) ≤ p := by
      have : 3 ≤ p := by have := hpr.two_le; omega
      exact_mod_cast this
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- `singProd n ≥ 0`. -/
theorem singProd_nonneg (n : ℕ) : 0 ≤ singProd n := by
  unfold singProd
  apply prod_nonneg
  intro p hp
  have : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2).two_le
  rcases eq_or_lt_of_le this with h | h
  · rw [← h]; norm_num
  · apply div_nonneg <;> linarith

/-! ### The no exceptional character case of (8.3), p. 367 -/

/-- p. 367, no exceptional character, as U-1423 read the scan:
`R₁(n) = 𝔖(n) n + O(n φ(n)^{-1} X exp(-c₇ δ^{-1}))` for even `n ∈ (X/2, X]`, with
`𝔖(n) = 2 C₂ ∏_{p | n, p > 2} (p-1)/(p-2)`. Lab normalization: the discrete major part on
`ZMod (2x+1)` is `M` times `R₁`, so both sides carry `M = Mx x`; `P = x^{6δ}`. The constants
`c₇, C` are absolute; `X0` may depend on `δ`. VERIFY against p. 367. -/
def NoExcR1 (c₁ c₇ C C₂ δ₀ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → ¬ ExcZero c₁ ((x : ℝ) ^ (6 * δ)) →
    ∀ n ∈ Icc (x / 2 + 1) x, Even n →
      ‖majorPart (logPrimes x) (mvMinor x ((x : ℝ) ^ (6 * δ))) (n : ZMod (Mx x)) -
          (((Mx x : ℝ) * n * (2 * C₂ * singProd n) : ℝ) : ℂ)‖ ≤
        C * (Mx x : ℝ) * ((n : ℝ) / (Nat.totient n : ℝ)) * x * Real.exp (-(c₇ / δ))

/-- (8.3) in the no exceptional case: `MajorCount83` restricted to the `x` with no exceptional
zero at level `x^{6δ}`. -/
def MajorCount83NoExc (c₁ δ K : ℝ) (X0 : ℕ) : Prop :=
  ∀ x : ℕ, X0 ≤ x → ¬ ExcZero c₁ ((x : ℝ) ^ (6 * δ)) →
    ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
        ‖majorPart (logPrimes x) (mvMinor x ((x : ℝ) ^ (6 * δ))) (n : ZMod (Mx x))‖
          ≤ (Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ))).card : ℕ) : ℝ) ≤ K * (x : ℝ) ^ (1 - 2 * δ)

/-- A small enough `δ`: `4 C exp(-c₇/δ) ≤ C₂` for some `0 < δ ≤ δ₁`. PROVED. -/
theorem exists_delta_small {c₇ C C₂ δ₁ : ℝ} (hc₇ : 0 < c₇) (hC₂ : 0 < C₂) (hδ₁ : 0 < δ₁) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ 4 * C * Real.exp (-(c₇ / δ)) ≤ C₂ := by
  -- take δ = min δ₁ (c₇ / (1 + |4 C / C₂|)), then exp(-c₇/δ) ≤ 1/(1 + c₇/δ)
  set A := 1 + |4 * C / C₂| with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg (4 * C / C₂)]
  refine ⟨min δ₁ (c₇ / A), lt_min hδ₁ (by positivity), min_le_left _ _, ?_⟩
  set δ := min δ₁ (c₇ / A)
  have hδ : 0 < δ := lt_min hδ₁ (by positivity)
  have hδle : δ ≤ c₇ / A := min_le_right _ _
  have hAle : A ≤ c₇ / δ := by
    rw [le_div_iff₀ hδ]; rw [le_div_iff₀ (by linarith)] at hδle; linarith
  have hexp : Real.exp (-(c₇ / δ)) ≤ 1 / A := by
    have h1 : c₇ / δ + 1 ≤ Real.exp (c₇ / δ) := Real.add_one_le_exp _
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by linarith)
    linarith
  have hpos : 0 < Real.exp (-(c₇ / δ)) := Real.exp_pos _
  have h4 : 4 * C / C₂ ≤ A - 1 := by rw [hA]; simp [le_abs_self]
  have h4' : 4 * C ≤ (A - 1) * C₂ := by rwa [div_le_iff₀ hC₂] at h4
  calc 4 * C * Real.exp (-(c₇ / δ)) ≤ (A - 1) * C₂ * Real.exp (-(c₇ / δ)) := by
        apply mul_le_mul_of_nonneg_right h4' hpos.le
    _ ≤ A * C₂ * Real.exp (-(c₇ / δ)) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le; nlinarith
    _ ≤ A * C₂ * (1 / A) := by
        apply mul_le_mul_of_nonneg_left hexp; positivity
    _ = C₂ := by field_simp

/-- The pointwise step of p. 367: with `4 C e ≤ C₂`, `n ∈ (x/2, x]` even, the asymptotic gives
`|A(n)| ≥ M C₂ x/4`. PROVED. -/
theorem major_lower {A : ℂ} {M x n C C₂ e : ℝ} {φn : ℝ} (hM : 0 < M) (hx : 0 < x)
    (hn2 : x / 2 ≤ n) (hφ : 0 < φn) (hr : 1 ≤ n / φn) (hC₂ : 0 < C₂) (_he : 0 ≤ e)
    {s : ℝ} (hs : C₂ * (n / φn) ≤ 2 * C₂ * s) (hCe : 4 * C * e ≤ C₂)
    (hA : ‖A - ((M * n * (2 * C₂ * s) : ℝ) : ℂ)‖ ≤ C * M * (n / φn) * x * e) :
    M * C₂ * x / 4 ≤ ‖A‖ := by
  have hn0 : 0 < n := by linarith
  set r := n / φn with hrdef
  have hmain : ‖((M * n * (2 * C₂ * s) : ℝ) : ℂ)‖ = M * n * (2 * C₂ * s) := by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    have : 0 ≤ 2 * C₂ * s := le_trans (by positivity) hs
    positivity
  have htri : M * n * (2 * C₂ * s) - C * M * r * x * e ≤ ‖A‖ := by
    have := norm_sub_norm_le ((M * n * (2 * C₂ * s) : ℝ) : ℂ) A
    rw [hmain, norm_sub_rev] at this
    linarith
  have h1 : M * n * (C₂ * r) ≤ M * n * (2 * C₂ * s) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h2 : C * M * r * x * e ≤ M * r * (C₂ * x / 4) := by
    have : C * e * 4 ≤ C₂ := by linarith
    have hMr : 0 ≤ M * r * x := by have : 0 ≤ r := by linarith
                                   positivity
    nlinarith
  have h3 : M * r * (C₂ * x / 4) ≤ M * r * (C₂ * n / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by have : 0 ≤ r := by linarith
                                          positivity)
    nlinarith
  have h4 : M * (C₂ * x / 4) ≤ M * r * (C₂ * x / 4) := by
    have : 0 ≤ M * (C₂ * x / 4) := by positivity
    nlinarith
  nlinarith

/-- **(8.3) in the no exceptional character case, CONDITIONAL ON `NoExcR1`**: for some
`0 < δ ≤ min δ₀ (1/15)` and `X1`, no even `n ∈ (x/2, x]` has major part at most
`M x^{1-2δ}` when there is no exceptional zero at level `x^{6δ}`; the count is 0. -/
theorem majorCount83_noExc {c₁ c₇ C C₂ δ₀ : ℝ} (hc₇ : 0 < c₇) (hC₂ : 0 < C₂) (hδ₀ : 0 < δ₀)
    (h : NoExcR1 c₁ c₇ C C₂ δ₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ 1 / 15 ∧ ∃ X1 : ℕ, MajorCount83NoExc c₁ δ 0 X1 := by
  obtain ⟨δ, hδ, hδle, hsmall⟩ := exists_delta_small (C := C) hc₇ hC₂
    (lt_min hδ₀ (by norm_num : (0 : ℝ) < 1 / 15))
  have hδ0 : δ ≤ δ₀ := hδle.trans (min_le_left _ _)
  have hδ15 : δ ≤ 1 / 15 := hδle.trans (min_le_right _ _)
  obtain ⟨X0, hX0⟩ := h δ hδ hδ0
  -- x^{2δ} → ∞, so eventually 4/C₂ < x^{2δ}
  have hev : ∀ᶠ x : ℕ in atTop, 4 / C₂ < (x : ℝ) ^ (2 * δ) :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 2 * δ)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨X2, hX2⟩ := eventually_atTop.mp hev
  refine ⟨δ, hδ, hδ0, hδ15, max (max X0 X2) 1, fun x hx hexc => ?_⟩
  have hxa : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hMpos : (0 : ℝ) < Mx x := by unfold Mx; push_cast; linarith
  have hbig := hX2 x hxb
  have hT : (Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ) < (Mx x : ℝ) * C₂ * x / 4 := by
    have hxyz : (x : ℝ) ^ (1 - 2 * δ) * (x : ℝ) ^ (2 * δ) = x := by
      rw [← Real.rpow_add hxpos, show 1 - 2 * δ + 2 * δ = (1 : ℝ) by ring, Real.rpow_one]
    have hp : 0 < (x : ℝ) ^ (1 - 2 * δ) := Real.rpow_pos_of_pos hxpos _
    have : (x : ℝ) ^ (1 - 2 * δ) < C₂ * x / 4 := by
      rw [div_lt_iff₀ hC₂] at hbig
      have h4 : (x : ℝ) ^ (1 - 2 * δ) * 4 < (x : ℝ) ^ (1 - 2 * δ) * ((x : ℝ) ^ (2 * δ) * C₂) :=
        mul_lt_mul_of_pos_left hbig hp
      have h5 : C₂ * (x : ℝ) = (x : ℝ) ^ (1 - 2 * δ) * ((x : ℝ) ^ (2 * δ) * C₂) := by
        calc C₂ * (x : ℝ) = C₂ * ((x : ℝ) ^ (1 - 2 * δ) * (x : ℝ) ^ (2 * δ)) := by rw [hxyz]
          _ = _ := by ring
      linarith
    have := mul_lt_mul_of_pos_left this hMpos
    linarith
  have hempty : (Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
      ‖majorPart (logPrimes x) (mvMinor x ((x : ℝ) ^ (6 * δ))) (n : ZMod (Mx x))‖
        ≤ (Mx x : ℝ) * (x : ℝ) ^ (1 - 2 * δ)) = ∅ := by
    apply filter_false_of_mem
    rintro n hn ⟨hev, hle⟩
    have hb := hX0 x hxa hexc n hn hev
    have hn' := mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hn2 : (x : ℝ) / 2 ≤ n := by
      have : x ≤ 2 * n := by omega
      have : (x : ℝ) ≤ 2 * n := by exact_mod_cast this
      linarith
    have hφ : (0 : ℝ) < Nat.totient n := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hr : 1 ≤ (n : ℝ) / (Nat.totient n : ℝ) := by
      rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le n
    have hs : C₂ * ((n : ℝ) / (Nat.totient n : ℝ)) ≤ 2 * C₂ * singProd n := by
      have := div_totient_le_singProd hn0 hev
      nlinarith
    have hlow := major_lower hMpos hxpos hn2 hφ hr hC₂ (Real.exp_pos _).le hs hsmall hb
    linarith
  rw [hempty, card_empty]
  simp

/-- With no exceptional zero at any level, `MajorCount83NoExc` is U-1423's `MajorCount83`. -/
theorem majorCount83_of_noExc {c₁ δ K : ℝ} {X0 : ℕ} (hs : NoSiegel c₁)
    (h : MajorCount83NoExc c₁ δ K X0) (hδ : 0 < δ) :
    MajorCount83 δ K (max X0 1) := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast le_trans (le_max_right _ _) hx
  exact h x (le_trans (le_max_left _ _) hx)
    (hs _ (Real.one_le_rpow hx1 (by linarith)))

/-- **Theorem 1 p. 353, CONDITIONAL ON `NoExcR1` and `NoSiegel c₁`**: the no exceptional
character case of (8.3) and the proved minor arcs of U-1423 give `E(X) ≪ X^{1-δ}`. -/
theorem theorem1_of_noExc {c₁ c₇ C C₂ δ₀ : ℝ} (hc₇ : 0 < c₇) (hC₂ : 0 < C₂) (hδ₀ : 0 < δ₀)
    (h : NoExcR1 c₁ c₇ C C₂ δ₀) (hs : NoSiegel c₁) : MV75.Theorem1 := by
  obtain ⟨δ, hδ, -, hδ15, X1, hX1⟩ := majorCount83_noExc hc₇ hC₂ hδ₀ h
  exact theorem1_of_majorCount83 hδ hδ15 le_rfl (majorCount83_of_noExc hs hX1 hδ)

/-! ### Vacuity and sanity instances -/

/-- `ExcZero` is not trivially true: below level 2 there is no exceptional zero, since the only
character mod 1 is principal. PROVED. -/
theorem not_excZero_lt_two (c₁ : ℝ) {P : ℝ} (hP : P < 2) : ¬ ExcZero c₁ P := by
  rintro ⟨r, _, χ, hr1, hrP, -, -, hχ1, -⟩
  have hr : r = 1 := by
    have : (r : ℝ) < 2 := lt_of_le_of_lt hrP hP
    have : r < 2 := by exact_mod_cast this
    omega
  exact hχ1 (DirichletCharacter.level_one' χ hr)

/-- `singProd 6 = 2` and `6/φ(6) = 3 ≤ 4`: `div_totient_le_singProd` at `n = 6` is not
vacuous. PROVED. -/
theorem singProd_six : singProd 6 = 2 := by
  unfold singProd
  have h6 : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    rfl
  rw [h6]
  rw [show ({2, 3} : Finset ℕ).erase 2 = {3} by decide]
  norm_num

theorem div_totient_six : (6 : ℝ) / (Nat.totient 6 : ℝ) = 3 := by
  rw [show Nat.totient 6 = 2 by decide]; norm_num

/-- The smallness condition of `majorCount83_noExc` is satisfiable: `c₇ = C = C₂ = 1`. -/
theorem exists_delta_small_one : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 15 ∧
    4 * 1 * Real.exp (-(1 / δ)) ≤ 1 :=
  exists_delta_small (C := 1) one_pos one_pos (by norm_num)

/-- `gallagher_exp_at_P` at `N = e`, `δ = 1/6`, `c = 1`: `exp(-1)`. -/
theorem gallagher_exp_e : Real.exp (-(1 * Real.log (Real.exp 1) /
    Real.log (Real.exp 1 ^ (6 * (1 / 6 : ℝ))))) = Real.exp (-(1 / (6 * (1 / 6)))) :=
  gallagher_exp_at_P (by have := Real.add_one_lt_exp (one_ne_zero); linarith) (by norm_num)

end LeanLab.ExceptionalSet.MV75U1432

section AxiomsU1432
open LeanLab.ExceptionalSet.MV75U1432
#print axioms gallagher71_empty
#print axioms gallagher_exp_at_P
#print axioms P_le_quarter'
#print axioms div_totient_eq_prod
#print axioms div_totient_le_singProd
#print axioms singProd_nonneg
#print axioms exists_delta_small
#print axioms major_lower
#print axioms majorCount83_noExc
#print axioms majorCount83_of_noExc
#print axioms theorem1_of_noExc
#print axioms not_excZero_lt_two
#print axioms singProd_six
#print axioms div_totient_six
#print axioms exists_delta_small_one
#print axioms gallagher_exp_e
end AxiomsU1432
