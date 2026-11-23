import LeanLab.ExceptionalSet.SPLIT_leaf_arc_energy

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_arc_energy_offwindow`, P0029 Bhowmik and
Grimmelt 2026 with the arc model of P0083 Pintz 2026: the squared coefficient energy of
`FX X (X ^ 2) ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X)` on the integers that are not an even
frequency `0 ≤ n ≤ X` is eventually at most `C · X^(3/2 + 2Θ + ε)`.

Why a new split.  The existing file `SPLIT_leaf_arc_energy_offwindow.lean` cuts the complement into
the same three pieces, but each of its three pieces is proved FROM the parent
`leaf_arc_energy_offwindow`, and its assembly proves the parent from those pieces.  That file is an
equivalence, not a reduction: it has no open leaf and does not lower the parent.  Here the three
pieces are genuine leaves, and the negative piece is reduced further:

* `leaf_ofw_model_negative`: at a negative frequency the squared generating function has
  coefficient zero, proved here as `fourierCoeff_FX_sq_neg`, so the negative piece is the negative
  frequency energy of the arc model alone, a statement with no primes in it;
* `leaf_ofw_short`: the odd frequencies `0 ≤ n ≤ X`, with the coefficient of the squared
  generating function there rewritten as `R_Λ(n) e^{-n/X}`;
* the frequencies `n > X`, cut once more at the truncation point `X ^ 2` of `F_X`: below it the
  coefficient of the squared generating function is exactly `R_Λ(n) e^{-n/X}`, proved here, which
  gives `leaf_ofw_high_middle`; above it `leaf_ofw_high_tail`.

The assembly `Feed1122.leaf_arc_energy_offwindow_split` is the existing one with these leaves in place of the
circular pieces; its helper lemmas are copied from the existing file, where they are private.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- The squared Fourier coefficient energy of the difference between the squared generating
function and the arc model is summable: both summands are square integrable on the circle, so the
difference is, and Parseval gives a summable family of squared coefficients. -/
private lemma summable_offwindow_coeff_sq (X : ℕ) (hX : 0 < X) :
    Summable (fun n : ℤ =>
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
  classical
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hG : MemLp (fun t => FX X (X ^ 2) t ^ 2) 2 haarAddCircle := memLp_FX_sq (X : ℝ) (X ^ 2)
  have hW : MemLp (Vfun X (Nat.sqrt X) (Nat.sqrt X)) 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hD : MemLp (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) 2
      haarAddCircle := hG.sub hW
  have hh := hasSum_sq_fourierCoeff
    (hD.toLp (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t))
  have hcoef : fourierCoeff
        ((hD.toLp (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) :
          Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) :=
    fourierCoeff_congr_ae (MemLp.coeFn_toLp hD)
  rw [hcoef] at hh
  exact hh.summable

/-- The window set consists of integers between `0` and `X`. -/
private lemma mem_window_bounds (X : ℕ) :
    ∀ m ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)),
      0 ≤ m ∧ m ≤ (X : ℤ) := by
  intro m hm
  obtain ⟨k, hk, hkm⟩ := Finset.mem_image.mp hm
  obtain ⟨hkr, _⟩ := Finset.mem_filter.mp hk
  have hkX : k ≤ X := by have := Finset.mem_range.mp hkr; omega
  constructor
  · rw [← hkm]; exact_mod_cast Nat.zero_le k
  · rw [← hkm]; exact_mod_cast hkX

/-- One summand over the complement of a finite set `S` of integers inside `[0, X]` splits into the
negative frequencies, the frequencies in `[0, X]` outside `S`, and the frequencies above `X`. The
three index sets are disjoint and together they are the complement of `S`. -/
private lemma offwindow_indicator_split (X : ℕ) (S : Finset ℤ)
    (hS : ∀ m ∈ S, 0 ≤ m ∧ m ≤ (X : ℤ)) (n : ℤ) (a : ℝ) :
    (if n ∈ S then 0 else a) =
      (if n < 0 then a else 0) +
        ((if 0 ≤ n ∧ n ≤ (X : ℤ) ∧ n ∉ S then a else 0) +
          (if (X : ℤ) < n then a else 0)) := by
  have h0X : (0 : ℤ) ≤ (X : ℤ) := by exact_mod_cast Nat.zero_le X
  by_cases hneg : n < 0
  · have hnS : n ∉ S := fun hm => by have := (hS n hm).1; omega
    have hlt : ¬ ((X : ℤ) < n) := by omega
    simp [hneg, hnS, hlt]
  · by_cases hhigh : (X : ℤ) < n
    · have hnS : n ∉ S := fun hm => by have := (hS n hm).2; omega
      simp [hneg, hhigh, hnS]
    · have h0 : 0 ≤ n := by omega
      have hle : n ≤ (X : ℤ) := by omega
      by_cases hmS : n ∈ S
      · simp [hneg, hhigh, hmS]
      · simp [hneg, hhigh, hmS, h0, hle]

/-- LEAF: the negative frequencies of the truncated arc model alone.  The squared generating
function has no negative frequency, so at `n < 0` the coefficient of the difference is minus the
coefficient of the model `V_X`, the sum over `q ≤ √X` and coprime `a` of
`μ(q)²/φ(q)²` times the arc profile `(X⁻¹ − 2πiβ)⁻²` cut to `|β| ≤ √X/(qX)`.  The full profile has
no negative coefficients; the cut profile has, and their energy is the truncation loss of the arcs.
The leaf: their squared energy is eventually at most `C · X^(3/2 + 2Θ + ε)`.  MEDIUM: an
`L²` estimate of the cut arcs, independent of the primes and of `Θ`. -/
theorem leaf_ofw_model_negative (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n < 0 then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry


/-- The squared generating function has no negative frequency: `F_{X,M}²` is a trigonometric
polynomial in the frequencies `p₁ + p₂ ≥ 0`. -/
private lemma fourierCoeff_FX_sq_neg (X : ℝ) (M : ℕ) (n : ℤ) (hn : n < 0) :
    fourierCoeff (fun t => FX X M t ^ 2) n = 0 := by
  have hfun : (fun t => FX X M t ^ 2) = (fun t : AddCircle (1 : ℝ) =>
      ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
        (aF X p.1 * aF X p.2) * fourier ((p.1 : ℤ) + (p.2 : ℤ)) t) := by
    ext t; exact trig_sq (aF X) M t
  rw [hfun, fourierCoeff_sum_monomial]
  apply Finset.sum_eq_zero
  intro p _
  have : n ≠ (p.1 : ℤ) + (p.2 : ℤ) := by omega
  simp [this]

/-- At a negative frequency the coefficient of the difference has the modulus of the model
coefficient. -/
private lemma norm_coeff_diff_neg (X : ℕ) (hX : 0 < X) (n : ℤ) (hn : n < 0) :
    ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ =
      ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set W : AddCircle (1 : ℝ) → ℂ := Vfun X (Nat.sqrt X) (Nat.sqrt X) with hWdef
  have hW : MemLp W 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hFX : MemLp (fun t => FX (X : ℝ) (X ^ 2) t ^ 2) 2 haarAddCircle :=
    memLp_FX_sq (X : ℝ) (X ^ 2)
  have hneg : fourierCoeff (-W) = -fourierCoeff W := by
    ext m
    have h := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
    simpa [neg_smul, one_smul] using h
  have hadd := fourierCoeff.add (T := (1 : ℝ))
    (f := fun t => FX X (X ^ 2) t ^ 2) (g := -W)
    (hFX.integrable one_le_two) (hW.integrable one_le_two).neg
  have heq : (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) =
      (fun t => FX X (X ^ 2) t ^ 2) + (-W) := by
    ext t
    simp [hWdef, sub_eq_add_neg]
  rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply, fourierCoeff_FX_sq_neg _ _ n hn, zero_add,
    norm_neg]

/-- The negative frequency piece of the off window energy, from the model leaf. -/
theorem ofw_negative_piece (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n < 0 then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨C, hC, X₀, h⟩ := leaf_ofw_model_negative Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C, hC, max X₀ 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hcongr : (fun n : ℤ => if n < 0 then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) = (fun n : ℤ => if n < 0 then
        ‖fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2 else 0) := by
    funext n
    by_cases hn : n < 0
    · simp only [hn, ↓reduceIte, norm_coeff_diff_neg X hXpos n hn]
    · simp only [hn, ↓reduceIte]
  rw [hcongr]
  exact h X (le_trans (le_max_left _ _) hX)


/-- LEAF: the odd frequencies of the window range, the short frequencies `0 ≤ n ≤ X` outside the
even window: the energy of `R_Λ(n) e^{-n/X} - v_X(n)` there is eventually at most
`C · X^(3/2 + 2Θ + ε)`.  At such `n` the coefficient of `FX X (X ^ 2) ^ 2` is `R_Λ(n) e^{-n/X}`,
proved as `coeff_diff_middle`; the count `R_Λ(n)` at odd `n` only counts
representations with a power of `2`, and the arc model nearly cancels between `q` and `2q`, the
mean square input of the paper's section on `v_X`; only the pairs `q ≤ Q < 2q` survive, of total
size `X^(5/2)` up to logarithms.  MEDIUM: Ramanujan sum bookkeeping at odd `n` plus a count of
`R_Λ(n)` at odd `n`. -/
theorem leaf_ofw_short (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: the damped middle frequencies `X < n ≤ X ^ 2`, where the truncation of `F_X` at `X ^ 2`
plays no role and the coefficient of the squared generating function is exactly
`R_Λ(n) e^{-n/X}`, proved below as `coeff_diff_middle`.  The leaf: the energy of
`R_Λ(n) e^{-n/X} - v_X(n)` over these `n` is eventually at most `C · X^(3/2 + 2Θ + ε)`.  HARD: the
zero free hypothesis enters through the mean square of `error n` weighted by `e^{-2n/X}` over
`n > X`, together with the arc model's reconstruction of `e^{-n/X} n 𝔖(n)` there. -/
theorem leaf_ofw_high_middle (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: the frequencies beyond the truncation, `n > X ^ 2`.  There the coefficient of
`F_{X,X²}²` is a partial convolution damped by `e^{-n/X} ≤ e^{-X}`, and the model coefficient is
`v_X(n)`, whose main part `e^{-n/X} n 𝔖_Q(n)` is equally damped and whose arc truncation part decays
like `q² X / n`.  The leaf: the energy of the difference over these `n` is eventually at most
`C · X^(3/2 + 2Θ + ε)`.  MEDIUM: trivial bounds on a damped tail and an `L²` tail of the cut arcs,
no zero free input. -/
theorem leaf_ofw_high_tail (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if ((X ^ 2 : ℕ) : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- At a frequency `0 ≤ n ≤ X ^ 2` the coefficient of the difference is
`R_Λ(n) e^{-n/X}` minus the model coefficient. -/
private lemma coeff_diff_middle (X : ℕ) (hX : 0 < X) (n : ℤ) (hn0 : 0 ≤ n)
    (hn : n ≤ ((X ^ 2 : ℕ) : ℤ)) :
    fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n =
      ((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
          Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set W : AddCircle (1 : ℝ) → ℂ := Vfun X (Nat.sqrt X) (Nat.sqrt X) with hWdef
  have hW : MemLp W 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hFX : MemLp (fun t => FX (X : ℝ) (X ^ 2) t ^ 2) 2 haarAddCircle :=
    memLp_FX_sq (X : ℝ) (X ^ 2)
  have hneg : fourierCoeff (-W) = -fourierCoeff W := by
    ext m
    have h := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
    simpa [neg_smul, one_smul] using h
  have hadd := fourierCoeff.add (T := (1 : ℝ))
    (f := fun t => FX X (X ^ 2) t ^ 2) (g := -W)
    (hFX.integrable one_le_two) (hW.integrable one_le_two).neg
  have heq : (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) =
      (fun t => FX X (X ^ 2) t ^ 2) + (-W) := by
    ext t
    simp [hWdef, sub_eq_add_neg]
  have hnat : n = ((n.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hn0).symm
  have hle : n.toNat ≤ X ^ 2 := by omega
  rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply, hnat,
    fourierCoeff_FX_sq (X : ℝ) (X ^ 2) n.toNat hle, ← hnat]
  ring

/-- The short odd frequency piece of the off window energy, from `leaf_ofw_short` and the
coefficient identity `coeff_diff_middle`. -/
theorem ofw_short_piece (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C, hC, X₀, h⟩ := leaf_ofw_short Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C, hC, max X₀ 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hXX : (X : ℤ) ≤ ((X ^ 2 : ℕ) : ℤ) := by
    have : X ≤ X ^ 2 := Nat.le_self_pow two_ne_zero X
    exact_mod_cast this
  have hcongr : (fun n : ℤ => if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
        n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) = (fun n : ℤ => if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
        n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
      ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
          Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
        fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
      else 0) := by
    funext n
    by_cases hn : 0 ≤ n ∧ n ≤ (X : ℤ) ∧
        n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ))
    · rw [if_pos hn, if_pos hn, coeff_diff_middle X hXpos n hn.1 (le_trans hn.2.1 hXX)]
    · rw [if_neg hn, if_neg hn]
  rw [hcongr]
  exact h X (le_trans (le_max_left _ _) hX)

/-- The high frequency piece of the off window energy, from the middle and tail leaves. -/
theorem ofw_high_piece (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_ofw_high_middle Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_ofw_high_tail Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C1 + C2, add_nonneg hC1 hC2, X1 + X2 + 1, ?_⟩
  intro X hX
  have hXpos : 0 < X := by omega
  have hbase := summable_offwindow_coeff_sq X hXpos
  set c : ℤ → ℝ := fun n =>
    ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
    with hc
  have hsplit : (fun n : ℤ => if (X : ℤ) < n then c n else 0) =
      fun n => (if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then c n else 0) +
        (if ((X ^ 2 : ℕ) : ℤ) < n then c n else 0) := by
    funext n
    have hXX : (X : ℤ) ≤ ((X ^ 2 : ℕ) : ℤ) := by
      have : X ≤ X ^ 2 := Nat.le_self_pow two_ne_zero X
      exact_mod_cast this
    by_cases h1 : (X : ℤ) < n
    · by_cases h2 : n ≤ ((X ^ 2 : ℕ) : ℤ)
      · have h3 : ¬ ((X ^ 2 : ℕ) : ℤ) < n := by omega
        rw [if_pos h1, if_pos ⟨h1, h2⟩, if_neg h3, add_zero]
      · have h3 : ((X ^ 2 : ℕ) : ℤ) < n := by omega
        rw [if_pos h1, if_neg (fun h => h2 h.2), if_pos h3, zero_add]
    · have h3 : ¬ ((X ^ 2 : ℕ) : ℤ) < n := by omega
      rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg h3, add_zero]
  have hm1 : Summable (fun n : ℤ =>
      if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then c n else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hm2 : Summable (fun n : ℤ => if ((X ^ 2 : ℕ) : ℤ) < n then c n else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hmid : (fun n : ℤ => if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then c n else 0) =
      fun n : ℤ => if (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ) then
        ‖((LeanLab.ExceptionalSet.PintzAlthofer2026.RΛ n.toNat *
            Real.exp (-(n.toNat : ℝ) / X) : ℝ) : ℂ) -
          fourierCoeff (Vfun X (Nat.sqrt X) (Nat.sqrt X)) n‖ ^ 2
        else 0 := by
    funext n
    by_cases h : (X : ℤ) < n ∧ n ≤ ((X ^ 2 : ℕ) : ℤ)
    · simp only [h, and_self, ↓reduceIte, hc]
      rw [coeff_diff_middle X hXpos n (by omega) h.2]
    · simp only [h, ↓reduceIte]
  show (∑' n : ℤ, if (X : ℤ) < n then c n else 0) ≤ _
  rw [hsplit, hm1.tsum_add hm2, hmid]
  have e1 := h1 X (by omega)
  have e2 := h2 X (by omega)
  linarith

namespace Feed1122

/-- Assembly of `leaf_arc_energy_offwindow` from the three genuine pieces.  It sits in the
sub-namespace `Feed1122` because the circular file `SPLIT_leaf_arc_energy_offwindow.lean` already
uses the name `leaf_arc_energy_offwindow_split` in the parent namespace. -/
theorem leaf_arc_energy_offwindow_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := ofw_negative_piece Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := ofw_short_piece Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C3, hC3, X3, h3⟩ := ofw_high_piece Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C1 + C2 + C3, add_nonneg (add_nonneg hC1 hC2) hC3, max (max X1 X2) X3 + 1, ?_⟩
  intro X hX
  have hX1 : X1 ≤ X := by omega
  have hX2 : X2 ≤ X := by omega
  have hX3 : X3 ≤ X := by omega
  have hXpos : 0 < X := by omega
  have hbase := summable_offwindow_coeff_sq X hXpos
  have hm1 : Summable (fun n : ℤ => if n < 0 then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hm2 : Summable (fun n : ℤ => if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
      n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hm3 : Summable (fun n : ℤ => if (X : ℤ) < n then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  calc (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2)
      = ∑' n : ℤ, ((if n < 0 then
            ‖fourierCoeff
              (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
            else 0) +
          ((if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
              n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0) +
            (if (X : ℤ) < n then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0))) :=
        tsum_congr (fun n => offwindow_indicator_split X _ (mem_window_bounds X) n _)
    _ = (∑' n : ℤ, if n < 0 then
            ‖fourierCoeff
              (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
            else 0) +
          (∑' n : ℤ, ((if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
              n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0) +
            (if (X : ℤ) < n then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0))) :=
        hm1.tsum_add (hm2.add hm3)
    _ = (∑' n : ℤ, if n < 0 then
            ‖fourierCoeff
              (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
            else 0) +
          ((∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
              n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0) +
            (∑' n : ℤ, if (X : ℤ) < n then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0)) := by
        rw [hm2.tsum_add hm3]
    _ ≤ C1 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) +
          (C2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + C3 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by
        have h1' := h1 X hX1
        have h2' := h2 X hX2
        have h3' := h3 X hX3
        linarith
    _ = (C1 + C2 + C3) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end Feed1122

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
