import LeanLab.ExceptionalSet.Decomp522a

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_arc_energy`: the mean square distance
between the square of the exponentially weighted prime generating function and the rectangular arc
model, both cut at the natural square root of `X`.

The target is one eventual inequality for

`∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2 ∂haarAddCircle`,

namely that it is at most `C · X^(3/2 + 2Θ + ε)` once `X` is large. The cut made here is on the
frequency support of the difference `FX X (X ^ 2) ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X)`. That
difference is square integrable on the circle, since both summands are, so its circle integral is
the sum of the squares of its Fourier coefficients over all integers. Cutting that sum at the
finite set of even frequencies between `0` and `X` gives two pieces:

* `leaf_arc_energy_spectral`, the cut itself: the integral is at most the squared coefficient
  energy on the even frequencies `0 ≤ n ≤ X` plus the squared coefficient energy on the complement
  of that finite frequency set. This is the reduction of route one, the passage from the circle
  integral to spectral energy; it is an inequality at every `X ≥ 1`, not an eventual one.
* `leaf_arc_energy_window`, the first side: the squared coefficient energy on the even frequencies
  `0 ≤ n ≤ X` is eventually at most `C · X^(3/2 + 2Θ + ε)`.
* `leaf_arc_energy_offwindow`, the second side: the squared coefficient energy on the complement of
  that finite frequency set is eventually at most `C · X^(3/2 + 2Θ + ε)`.

The two frequency sets are disjoint and cover every integer coefficient, so their squared energies
add to the full spectral energy, and each side is one estimate about one part of the spectrum. No
one of the three leaves gives the target: the integral needs the cut and both of its sides, and
each side alone is strictly weaker than the target because the other side's energy is dropped.
The assembly `leaf_arc_energy_split` takes `C` to be the sum of the two constants and `X₀` the sum
of the two thresholds plus one, and adds.

Why the leaves are not degenerate. Each leaf carries the target's own numerical hypotheses
`1/2 ≤ Θ`, `Θ < 3/4`, `0 < ε` and `ε < 3/2 - 2 Θ`, so an instance is `Θ = 1/2`, `ε = 1/4`, and
none of the hypotheses can fail to hold together since `3/2 - 2·(1/2) = 1/2 > 0`. The even
frequency set at `X = 4` is `{0, 2, 4}`, which is nonempty, and its complement at `X = 4` contains
the odd frequency `1`, so neither the window nor the off window leaf is an empty claim; the model
`Vfun 4 2 2` is a genuine arc sum with two coprime numerators at `q = 2` and a nonvanishing
coefficient at `0`. At `X = 0` the cutoff `Nat.sqrt 0` is `0` and both sides of the cut are
degenerate, so `leaf_arc_energy_spectral` is stated for `1 ≤ X` only, and the two threshold leaves
carry their own `X₀`, whose honest value is at least `4`. No division by `X`, by the cutoff or by
`Nat.totient` appears in any statement, so the junk values of Lean division play no role; the only
power is `X ^ (3/2 + 2Θ + ε)` at a nonnegative base, and the empty frequency set is handled by the
`Finset` sum being zero and by the indicator sum of the complement being then the full energy.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- A finite set of integers is split off a summable family: the tail over its complement is the
total minus the finite sum. -/
private lemma tsum_compl_sub {g : ℤ → ℝ} (hg : Summable g) (s : Finset ℤ) :
    ∑' n : ℤ, (if n ∈ s then 0 else g n) = ∑' n : ℤ, g n - ∑ n ∈ s, g n := by
  set w : ℤ → ℝ := fun n => if n ∈ s then g n else 0 with hw
  have hw0 : ∀ n ∉ s, w n = 0 := by
    intro n hn
    simp [hw, hn]
  have hws : Summable w :=
    summable_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (f := w) (s := s) hw0
  have hwval : ∑' n : ℤ, w n = ∑ n ∈ s, g n := by
    rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s) hw0]
    exact Finset.sum_congr rfl (fun n hn => by simp [hw, hn])
  have hd : (fun n : ℤ => if n ∈ s then 0 else g n) = fun n => g n - w n := by
    funext n
    by_cases h : n ∈ s <;> simp [hw, h]
  have hsub : HasSum (fun n : ℤ => g n - w n)
      (∑' n : ℤ, g n - ∑' n : ℤ, w n) := hg.hasSum.sub hws.hasSum
  rw [hd, ← hwval]
  exact hsub.tsum_eq

/-- LEAF. The cut of the circle integral at the even frequencies up to `X`: for `1 ≤ X`, the square
integral of the difference between the squared generating function cut at `X ^ 2` and the arc model
cut at `Nat.sqrt X` is at most the squared Fourier coefficient energy of that difference on the
even frequencies `0 ≤ n ≤ X` plus its squared coefficient energy on the complement of that finite
frequency set. This is the Parseval step only, at one fixed `X`, with no asymptotic content, no
constant to be found and no hypothesis on `Θ` used beyond carrying it. It drops neither side of the
cut in the way the two threshold leaves do, but asserts no bound on either side. Instance:
`Θ = 1/2`, `ε = 1/4`, `X = 4`, where the window is `{0, 2, 4}` and the complement contains `1`. -/
theorem leaf_arc_energy_spectral (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) (X : ℕ) (hX : 1 ≤ X) :
    (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle) ≤
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2) +
      (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
  classical
  set F : AddCircle (1 : ℝ) → ℂ := fun t =>
    FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t with hF
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hmL2 : MemLp F 2 haarAddCircle :=
    (memLp_FX_sq (X : ℝ) (X ^ 2)).sub (memLp_Vfun hX0 _ _)
  have hh := hasSum_sq_fourierCoeff (hmL2.toLp F)
  have hcoef : fourierCoeff ((hmL2.toLp F : Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff F := fourierCoeff_congr_ae (MemLp.coeFn_toLp hmL2)
  have hint : ∫ t, ‖((hmL2.toLp F : Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) t‖ ^ 2
        ∂haarAddCircle = ∫ t, ‖F t‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hmL2] with t ht
    rw [ht]
  rw [hcoef, hint] at hh
  have hsumm : Summable (fun n : ℤ => ‖fourierCoeff F n‖ ^ 2) := hh.summable
  have hsp := tsum_compl_sub hsumm (((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)))
  have himg : (∑ n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)),
        ‖fourierCoeff F n‖ ^ 2) =
      ∑ n ∈ (range (X + 1)).filter Even, ‖fourierCoeff F (n : ℤ)‖ ^ 2 :=
    Finset.sum_image (fun a _ b _ hab => by exact_mod_cast hab)
  have htot : ∑' n : ℤ, ‖fourierCoeff F n‖ ^ 2 =
      (∑ n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)),
          ‖fourierCoeff F n‖ ^ 2) +
        ∑' n : ℤ, (if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
          else ‖fourierCoeff F n‖ ^ 2) := by
    rw [hsp]
    ring
  have hmain : ∫ t, ‖F t‖ ^ 2 ∂haarAddCircle =
      (∑ n ∈ (range (X + 1)).filter Even, ‖fourierCoeff F (n : ℤ)‖ ^ 2) +
        ∑' n : ℤ, (if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
          else ‖fourierCoeff F n‖ ^ 2) := by
    rw [← hh.tsum_eq, ← himg]
    exact htot
  exact le_of_eq hmain

/-- The window leaf reduces to the paper's mean square input for the coefficient error `error n`:
if the squared error on the even frequencies up to `X` is eventually at most
`C · X^(3/2 + 2Θ + ε)`, then the squared coefficient energy of the difference on that window is too.
The two summands of `r2 n e^{−n/X} − v_X(n)` are the exponential smoothing of `error n`, whose square
the exponential damping only shrinks, and the reconstruction error of the arc model against
`e^{−n/X} n Sing n`, which `leaf_singular_energy` bounds by `X^(5/2 + ε)`, below the target power
because `1 ≤ 2Θ`. This is a reduction only: the hypothesis `hE` is the missing input, and this
theorem is not the leaf. -/
private theorem window_of_error_mean_square (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ)
    (hE : ∃ Ce : ℝ, 0 ≤ Ce ∧ ∃ Xe : ℕ, ∀ X : ℕ, Xe ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
        Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨Ce, hCe, Xe, hE'⟩ := hE
  obtain ⟨Cs, hCs, Xs, hs⟩ := leaf_singular_energy ε hε
  refine ⟨2 * Ce + 2 * Cs, by positivity, max (max Xe Xs) 1 + 1, ?_⟩
  intro X hX
  have hXe : Xe ≤ X := by omega
  have hXs : Xs ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  set W : AddCircle (1 : ℝ) → ℂ := Vfun X (Nat.sqrt X) (Nat.sqrt X) with hWdef
  have hW : MemLp W 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hFX : MemLp (fun t => FX (X : ℝ) (X ^ 2) t ^ 2) 2 haarAddCircle :=
    memLp_FX_sq (X : ℝ) (X ^ 2)
  have hneg : fourierCoeff (-W) = -fourierCoeff W := by
    ext m
    have h := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
    simpa [neg_smul, one_smul] using h
  have hcoef (n : ℕ) (hn : n ≤ X) :
      fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ) =
        ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) - fourierCoeff W (n : ℤ) := by
    have hadd := fourierCoeff.add (T := (1 : ℝ))
      (f := fun t => FX X (X ^ 2) t ^ 2) (g := -W)
      (hFX.integrable one_le_two) (hW.integrable one_le_two).neg
    have heq : (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) =
        (fun t => FX X (X ^ 2) t ^ 2) + (-W) := by
      ext t
      simp [hWdef, sub_eq_add_neg]
    rw [heq, hadd, hneg, Pi.add_apply, Pi.neg_apply,
      fourierCoeff_FX_sq (X : ℝ) (X ^ 2) n (hn.trans (Nat.le_self_pow two_ne_zero X))]
    rfl
  have hterm (n : ℕ) (hn : n ∈ (range (X + 1)).filter Even) :
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2 ≤
        2 * (error n) ^ 2 +
          2 * ‖fourierCoeff W (n : ℤ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 := by
    have hnX : n ≤ X := by
      have := mem_range.mp (mem_filter.mp hn).1
      omega
    rw [hcoef n hnX]
    have hexp1 : Real.exp (-(n : ℝ) / X) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have hnn : (0 : ℝ) ≤ (n : ℝ) / X := div_nonneg (Nat.cast_nonneg n) hX0.le
      linarith
    have hexp0 : (0 : ℝ) < Real.exp (-(n : ℝ) / X) := Real.exp_pos _
    have hab : ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 ≤ (error n) ^ 2 := by
      have hid : ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
          ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) =
            ((error n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
        simp only [error]
        push_cast
        ring
      rw [hid, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      have he2 : Real.exp (-(n : ℝ) / X) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (error n)]
    have hsplit : ((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        fourierCoeff W (n : ℤ) =
        (((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
          ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)) +
        (((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
          fourierCoeff W (n : ℤ)) := by
      ring
    have hstep : ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
        fourierCoeff W (n : ℤ)‖ ^ 2 ≤
        2 * ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
          ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 +
        2 * ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
          fourierCoeff W (n : ℤ)‖ ^ 2 := by
      rw [hsplit]
      calc ‖(((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)) +
          (((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
            fourierCoeff W (n : ℤ))‖ ^ 2
          ≤ (‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ +
            ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
              fourierCoeff W (n : ℤ)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ ≤ 2 * (‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 +
            ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
              fourierCoeff W (n : ℤ)‖ ^ 2) := add_sq_le
        _ = 2 * ‖((r2 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2 +
            2 * ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
              fourierCoeff W (n : ℤ)‖ ^ 2 := by ring
    have hsymm : ‖fourierCoeff W (n : ℤ) -
        ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ =
        ‖((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ) -
          fourierCoeff W (n : ℤ)‖ := norm_sub_rev _ _
    rw [hsymm]
    nlinarith [hab, hstep]
  have hsum := sum_le_sum hterm
  have hsplit2 : (∑ n ∈ (range (X + 1)).filter Even,
      (2 * (error n) ^ 2 +
        2 * ‖fourierCoeff W (n : ℤ) -
          ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2)) =
      2 * (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) +
        2 * (∑ n ∈ (range (X + 1)).filter Even,
          ‖fourierCoeff W (n : ℤ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hpow : (X : ℝ) ^ (5 / 2 + ε) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
  have hpow0 : (0 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by positivity
  calc ∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2
      ≤ 2 * (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) +
        2 * (∑ n ∈ (range (X + 1)).filter Even,
          ‖fourierCoeff W (n : ℤ) -
            ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) := by
        rw [← hsplit2]; exact hsum
    _ ≤ 2 * (Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) +
        2 * (Cs * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by
        have h1 : (∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2) ≤
            Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := hE' X hXe
        have h2 : (∑ n ∈ (range (X + 1)).filter Even,
            ‖fourierCoeff W (n : ℤ) -
              ((Real.exp (-(n : ℝ) / X) * (n : ℝ) * Sing n : ℝ) : ℂ)‖ ^ 2) ≤
            Cs * (X : ℝ) ^ (5 / 2 + ε) := hs X hXs
        have h2' : Cs * (X : ℝ) ^ (5 / 2 + ε) ≤ Cs * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
          mul_le_mul_of_nonneg_left hpow hCs
        linarith
    _ = (2 * Ce + 2 * Cs) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

/-- LEAF. The even frequency window `0 ≤ n ≤ X` only: there are `C` and `X₀` with `0 ≤ C` and, for
every `X ≥ X₀`, the squared Fourier coefficient energy of the difference on the even frequencies
`0 ≤ n ≤ X` is at most `C · X^(3/2 + 2Θ + ε)`. This is one side of the spectral cut, stated on
that finite set alone, so it does not imply the target: it says nothing about the coefficients
outside `0 ≤ n ≤ X`. It uses the zero free hypothesis and the numerical hypotheses exactly as the
target does, and it is an eventual inequality, so its constant and threshold are free. Instance:
after the threshold, `Θ = 1/2` and `ε = 1/4`; the summand set at `X = 4` is `{0, 2, 4}`. -/
theorem leaf_arc_energy_window (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (range (X + 1)).filter Even,
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
          (n : ℤ)‖ ^ 2) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF. The complement of the even frequency window only: there are `C` and `X₀` with `0 ≤ C` and,
for every `X ≥ X₀`, the squared Fourier coefficient energy of the difference on the integers that
are not an even frequency `0 ≤ n ≤ X` is at most `C · X^(3/2 + 2Θ + ε)`. This is the other side of
the spectral cut, stated on that complement alone, so it does not imply the target: it says nothing
about the coefficients on `0 ≤ n ≤ X`. The complement is infinite and its indicator is written as
zero on the window, so the sum is the energy of the frequencies dropped by the window leaf.
Instance: `Θ = 1/2`, `ε = 1/4`; at `X = 4` the complement contains the odd frequency `1` and every
frequency above `4`, so the claim is not the claim of an empty index set. -/
theorem leaf_arc_energy_offwindow (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Assembly of `leaf_arc_energy` from the cut and its two sides. The spectral leaf bounds the
circle integral by the window energy plus the off window energy at the same `X`; the two threshold
leaves bound those two energies by `C` times the same power of `X`; the constant is their sum and
the threshold the sum of the two thresholds plus one, which puts `X` at least one and at least both
thresholds. Nothing else is used and `sorry` is not used. -/
theorem leaf_arc_energy_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle) ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨Cw, hCw, Xw, hw⟩ := leaf_arc_energy_window Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨Ct, hCt, Xt, ht⟩ := leaf_arc_energy_offwindow Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨Cw + Ct, add_nonneg hCw hCt, Xw + Xt + 1, ?_⟩
  intro X hX
  have hXw : Xw ≤ X := by omega
  have hXt : Xt ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hsp := leaf_arc_energy_spectral Θ hΘ1 hΘ2 hZF ε hε hsublinear X hX1
  calc (∫ t, ‖FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t‖ ^ 2
        ∂haarAddCircle)
      ≤ (∑ n ∈ (range (X + 1)).filter Even,
          ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t)
            (n : ℤ)‖ ^ 2) +
        (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
          else ‖fourierCoeff
            (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := hsp
    _ ≤ Cw * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Ct * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
        add_le_add (hw X hXw) (ht X hXt)
    _ = (Cw + Ct) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a
