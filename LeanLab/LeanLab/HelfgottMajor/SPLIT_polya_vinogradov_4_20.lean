import LeanLab.HelfgottMajor.PolyaVinogradov123
import LeanLab.HelfgottMajor.EvenPVSums
import LeanLab.HelfgottMajor.EvenPVNumeric
import LeanLab.HelfgottMajor.EvenPVKernel
import LeanLab.HelfgottMajor.SPLIT_leaf_odd_case_pomerance

/-!
Split of the explicit Polya-Vinogradov inequality for a primitive character modulo `q > 1`
(Helfgott, Major arcs, display 4.20), which is stated in the parent module without proof.

The display has two branches, for the two parities of the character, and the two branches come
from two different Fourier expansions of the sawtooth kernel: the even one has kernel coefficients
`2/(pi^2 k^2)`-sized, the odd one `1/(2 pi k)`-sized, which is why the constants differ. Each branch
is therefore stated here as its own leaf, and the assembly is the parity split.

No definition is introduced: the partial sum of `chi` is written out, and the constant
`M(q)` of the display is written as the supremum of its norm over the length.
-/

namespace LeanLab.HelfgottMajor.PolyaVinogradov123
open Real

/-- LEAF: the truncated harmonic-range estimate for the even branch. For an even primitive
character modulo `q > 1`, every partial sum of `chi` up to a length `n` has norm at most
`q / H + 4 / pi ^ 2 * sqrt q * log H + sqrt q / 4`, for every truncation length `H` between `1`
and `q`. This is the step that sums the Fourier coefficients of the even sawtooth kernel over the
range `h <= H` and keeps the remainder; it makes no choice of `H`, so it is one estimate and not
the whole branch. Its instances at `H = 1` (here the bound is `q` up to the remainder, and the
partial sums have norm at most `q`) and at `H = q` are both true, as is the case `n = 0`, where the
sum is empty. -/
private theorem pv_even_truncation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_even : χ (-1) = 1) (n : ℕ) (H : ℝ)
    (hH_one : 1 ≤ H) (hH_q : H ≤ (q : ℝ)) :
    ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖ ≤
      (q : ℝ) / H + 4 / π ^ 2 * sqrt q * log H + 1 / 4 * sqrt q := by
  -- Proof, AI written: Gauss sum completion with a smoothing window of length `L`
  -- (`even_pv_kernel_bound`), the sine sum bounds of `EvenPVSums`, and the numerics of
  -- `EvenPVNumeric`; `L = 1` for `q ≤ 128` and `L = Nat.sqrt q + 1` above.
  have hq2 : 2 ≤ q := by
    have h0 := NeZero.ne q
    omega
  refine le_trans ?_ (even_pv_min_le hq2 H hH_one)
  have hpos : (0 : ℝ) ≤ 1 / (2 * sqrt q) := by positivity
  rcases le_or_gt q 128 with hsm | hlg
  · have hk := even_pv_kernel_bound χ hχ hq h_even n 1 le_rfl
    have hsum : ∑ a ∈ Finset.Ioo 0 q,
        min (1 / sin (π * a / q)) (1 / (((1 : ℕ) : ℝ) * sin (π * a / q) ^ 2)) ≤
        ∑ a ∈ Finset.Ioo 0 q, 1 / sin (π * a / q) :=
      Finset.sum_le_sum fun a _ => min_le_left _ _
    have h1 := mul_le_mul_of_nonneg_left (hsum.trans (sum_inv_sin_le hq2)) hpos
    have h2 := even_pv_small hq2 hsm
    have h3 : (((1 : ℕ) : ℝ) - 1) / 2 = 0 := by simp
    linarith
  · have hsq : Nat.sqrt q * Nat.sqrt q ≤ q := Nat.sqrt_le q
    have hAq : 2 * (Nat.sqrt q + 1) < q := by
      by_contra hcon
      have hs3 : Nat.sqrt q ≤ 3 := by nlinarith
      have : q ≤ 8 := by omega
      omega
    have hk := even_pv_kernel_bound χ hχ hq h_even n (Nat.sqrt q + 1) (by omega)
    have hs := sum_min_inv_sin_le (q := q) (A := Nat.sqrt q + 1) (L := Nat.sqrt q + 1)
      (by omega) (by omega) hAq
    have h1 := mul_le_mul_of_nonneg_left hs hpos
    have h2 := even_pv_large hlg.le
    linarith

/-- LEAF: the choice of the truncation length and the arithmetic of the constants. For `q` at
least `2`, the bound of the first leaf taken at `H = sqrt q`, that is
`q / sqrt q + 4 / pi ^ 2 * sqrt q * log (sqrt q) + sqrt q / 4`, is at most the printed right-hand
side `2 / pi ^ 2 * sqrt q * log q + 4 / pi ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q`. This is
where `q / sqrt q = sqrt q` and `log (sqrt q) = log q / 2` are used, so that the `log q` terms
match with coefficient `2 / pi ^ 2`, and where the remaining `log log q` and constant terms are
checked to cover the leftover `sqrt q / 4` of the remainder. The case `q = 2` is the sharpest one
of the inequality, and it holds there with about a tenth of `sqrt q` to spare. -/
private theorem pv_even_optimization {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ) / sqrt q + 4 / π ^ 2 * sqrt q * log (sqrt q) + 1 / 4 * sqrt q ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set s := sqrt (q : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact sqrt_pos.mpr hq0
  have hlogs : log (sqrt (q : ℝ)) = log (q : ℝ) / 2 := log_sqrt (le_of_lt hq0)
  have hdiv : (q : ℝ) / sqrt (q : ℝ) = s := by
    rw [hs, div_sqrt]
  -- the lower bound `-1/4 <= 4/pi^2 * log (log q)` for `q >= 2`
  have hlogq : 0 < log (q : ℝ) := log_pos (by linarith)
  have hcpos : (0 : ℝ) < 0.6931471803 := by norm_num
  have hlog2gt : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hlog2le : log 2 ≤ log (q : ℝ) := log_le_log (by norm_num) hq2
  have hll : log 0.6931471803 ≤ log (log (q : ℝ)) :=
    log_le_log hcpos (by linarith)
  have hsub : 1 - (0.6931471803 : ℝ)⁻¹ ≤ log 0.6931471803 :=
    one_sub_inv_le_log_of_pos hcpos
  have hlt : 4 / π ^ 2 ≤ 4 / 9 := by
    have h3 : (3 : ℝ) < π := pi_gt_three
    have h9 : (9 : ℝ) < π ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hnonpos : 1 - (0.6931471803 : ℝ)⁻¹ ≤ 0 := by norm_num
  have hnum : -(1 / 4 : ℝ) ≤ 4 / 9 * (1 - (0.6931471803 : ℝ)⁻¹) := by norm_num
  have hstep : 4 / 9 * (1 - (0.6931471803 : ℝ)⁻¹) ≤
      4 / π ^ 2 * (1 - (0.6931471803 : ℝ)⁻¹) :=
    mul_le_mul_of_nonpos_right hlt hnonpos
  have hkey : -(1 / 4 : ℝ) ≤ 4 / π ^ 2 * log (log (q : ℝ)) := by
    have hmono : 4 / π ^ 2 * (1 - (0.6931471803 : ℝ)⁻¹) ≤ 4 / π ^ 2 * log (log (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_trans hsub hll) (by positivity)
    linarith
  have hmul : -(1 / 4 : ℝ) * s ≤ 4 / π ^ 2 * s * log (log (q : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hkey (le_of_lt hs0)
    calc -(1 / 4 : ℝ) * s = -(1 / 4 : ℝ) * s := rfl
      _ ≤ (4 / π ^ 2 * log (log (q : ℝ))) * s := this
      _ = 4 / π ^ 2 * s * log (log (q : ℝ)) := by ring
  have hcoef : 4 / π ^ 2 * s * (log (q : ℝ) / 2) = 2 / π ^ 2 * s * log (q : ℝ) := by
    field_simp
    ring
  rw [hdiv, hlogs, hcoef]
  linarith [hmul]

/-- LEAF: the even branch of the display. If the primitive character satisfies `chi (-1) = 1`, then
the partial sums of `chi` are bounded by the three-term expression with the `2/pi^2` and `4/pi^2`
constants, obtained by summing the `h`-th Fourier coefficient of the even sawtooth kernel over a
harmonic range `h <= H` and then optimizing in `H`. This is one branch, not the whole display: it
says nothing about odd characters. -/
theorem leaf_even_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_even : χ (-1) = 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq2 : 2 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := Nat.pos_of_ne_zero hq0
    exact_mod_cast this
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hH_one : (1 : ℝ) ≤ sqrt (q : ℝ) := by
    rw [Real.one_le_sqrt]
    linarith
  have hH_q : sqrt (q : ℝ) ≤ (q : ℝ) := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr hq1
  refine ciSup_le (fun n => ?_)
  have hmain :=
    pv_even_truncation χ hχ hq h_even n (sqrt (q : ℝ)) hH_one hH_q
  calc ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖
      ≤ (q : ℝ) / sqrt (q : ℝ) + 4 / π ^ 2 * sqrt (q : ℝ) * log (sqrt (q : ℝ)) +
          1 / 4 * sqrt (q : ℝ) := hmain
    _ ≤ 2 / π ^ 2 * sqrt (q : ℝ) * log (q : ℝ) +
          4 / π ^ 2 * sqrt (q : ℝ) * log (log (q : ℝ)) + 3 / 2 * sqrt (q : ℝ) :=
        pv_even_optimization hq2

/-- LEAF: the odd branch of the display. If the primitive character satisfies `chi (-1) ≠ 1`, then
the partial sums of `chi` are bounded by the three-term expression with the `1/(2*pi)` and `1/pi`
constants, obtained by summing the Fourier coefficients of the odd sawtooth kernel over a harmonic
range `h <= H` and then optimizing in `H`. This is one branch, not the whole display: it says
nothing about even characters. -/
theorem leaf_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (h_odd : χ (-1) ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  exact leaf_odd_case_of_leaves χ hχ hq h_odd

/-- The display, assembled from its two parity branches: split on the value of `chi (-1)` and hand
each branch to the corresponding leaf. -/
theorem polya_vinogradov_4_20_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  split_ifs with h
  · exact leaf_even_case χ hχ hq h
  · exact leaf_odd_case χ hχ hq h

end LeanLab.HelfgottMajor.PolyaVinogradov123
