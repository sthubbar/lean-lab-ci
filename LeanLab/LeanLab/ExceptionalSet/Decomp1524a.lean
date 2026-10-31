/-
CODEX task85 status: every original leaf below now has a proof. The additive, arithmetic and multiplicative large sieve conclusions print allowed axioms.
AI wrote the Lean code. Binary Goldbach is open.
-/
/-
P0015 Montgomery and Vaughan 1975, The exceptional set in Goldbach's problem, Acta Arith. 27,
353-370. Unit U-1524, run 20261025T2003Z-426, ARCHITECT DECOMPOSE.

File a of three: the large sieve, analytic and arithmetic, and its consequence for sums over
characters, split into LEAF lemmas. Montgomery and Vaughan use the large sieve through
Gallagher's density estimate (their section 7, Gallagher's Theorem 7) and through the
multiplicative large sieve; the paper itself does not reprove it.

SOURCE: the impan.pl scan could not be fetched in this unit (WebFetch CLIENT_ERROR on the
download link; no copy under Lean Lab/copies). The leaves follow the standard textbook argument:
H. L. Montgomery, Topics in Multiplicative Number Theory, LNM 227 (1971), Lemma 1.1
(Sobolev-Gallagher), Ch. 3; Montgomery-Vaughan, Multiplicative Number Theory I (2007),
Sections 7.4 (duality), 9.2 (Gauss sums); P. X. Gallagher, The large sieve, Mathematika 14
(1967) 14-20; Davenport, Multiplicative Number Theory, Ch. 9 and 27.

Gallagher's form proved here as an assembly: for points `δ`-spaced mod 1, `0 < δ ≤ 1`,
`Σ_r |Σ_{n=M+1}^{M+N} a_n e(n x_r)|² ≤ (πN + δ⁻¹) Σ |a_n|²`.

Leaves (sorry): `sobolev_pointwise`, `hasDerivAt_trig`, `parseval_trig`,
`integral_norm_mul_deriv_le`, `periodic_disjoint_sum`, `shift_trig`, `large_sieve_centered`,
`spaced_count_le`, `farey_spaced`, `duality`, `char_mul_tau`, `norm_tau_sq`,
`char_orthogonality_sum`, `mult_large_sieve`.
Assemblies, zero sorry: `large_sieve` (from `large_sieve_centered`, `shift_trig`),
`arith_large_sieve` (from `large_sieve`, `farey_spaced`).

AI-written Lean code, Claude, unit U-1524. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010GaussBound
import LeanLab.PNTPort.Vinogradov.MinorArcs
import LeanLab.ExceptionalSet.Lu2010Orth
import LeanLab.PNTPort.LargeSieve.Multiplicative

namespace LeanLab.ExceptionalSet.Decomp1524a

open Real MeasureTheory Finset
open ZMod Complex ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- The trigonometric polynomial `S(α) = Σ_{n ∈ s} a_n e(nα)`. -/
noncomputable def trig (s : Finset ℤ) (a : ℤ → ℂ) (α : ℝ) : ℂ := ∑ n ∈ s, a n * e (n * α)

/-- Its derivative `S'(α) = Σ_{n ∈ s} 2πin a_n e(nα)`. -/
noncomputable def trigDeriv (s : Finset ℤ) (a : ℤ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ s, (2 * π * Complex.I * n) * a n * e (n * α)

/-- The points `x_r`, `r ∈ pts`, are `δ`-spaced modulo 1: `‖x_r - x_s‖ ≥ δ` for `r ≠ s`,
where `‖·‖` is the distance to the nearest integer. -/
def Spaced {ι : Type*} (pts : Finset ι) (x : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ r ∈ pts, ∀ s ∈ pts, r ≠ s → ∀ m : ℤ, δ ≤ |x r - x s - m|

/-- `|e(x)| = 1`. PROVED. -/
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-! ### The analytic large sieve, Gallagher's proof -/

/-- LEAF. Sobolev-Gallagher pointwise bound: if `f` is differentiable on `[a,b]` with
continuous derivative `f'`, then `|f((a+b)/2)| ≤ (b-a)⁻¹ ∫_a^b |f| + (1/2) ∫_a^b |f'|`.
Montgomery, Topics in Mult. Number Theory, LNM 227, Lemma 1.1; Gallagher 1967 p. 15.
Unit U-1524. -/
theorem sobolev_pointwise {f f' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Set.Icc a b)) :
    ‖f ((a + b) / 2)‖ ≤ (b - a)⁻¹ * ∫ t in a..b, ‖f t‖ + (1 / 2) * ∫ t in a..b, ‖f' t‖ := by
  let m := (a+b)/2
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hfc : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have parts (u v c : ℝ) (huv : u ≤ v) (hs : Set.Icc u v ⊆ Set.Icc a b) :
      (∫ t in u..v, f t) + (∫ t in u..v, ((t:ℂ)-(c:ℂ))*f' t) =
        ((v:ℂ)-(c:ℂ))*f v-((u:ℂ)-(c:ℂ))*f u := by
    have hs' : Set.uIcc u v ⊆ Set.Icc a b := by simpa [Set.uIcc_of_le huv] using hs
    have hc : ContinuousOn (fun t : ℝ => ((t:ℂ)-(c:ℂ))*f' t) (Set.Icc u v) := by
      apply ContinuousOn.mul (by fun_prop) (hf'.mono hs)
    have hp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
      (u := fun t : ℝ => (t:ℂ)-(c:ℂ)) (u' := fun _ => (1:ℂ)) (v := f) (v' := f')
      (by fun_prop) (hfc.mono hs')
      (fun t ht => (Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (c:ℂ))
      (fun t ht => hf t (hs' ⟨ht.1.le, ht.2.le⟩))
      intervalIntegrable_const (ContinuousOn.intervalIntegrable_of_Icc huv (hf'.mono hs))
    simp only [one_mul] at hp
    rw [intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc huv (hfc.mono hs))
      (ContinuousOn.intervalIntegrable_of_Icc huv hc)] at hp
    exact hp
  have boundWeighted (u v c : ℝ) (huv : u ≤ v) (hs : Set.Icc u v ⊆ Set.Icc a b)
      (hw : ∀ t ∈ Set.Icc u v, ‖(t:ℂ)-(c:ℂ)‖ ≤ L/2) :
      ‖∫ t in u..v, ((t:ℂ)-(c:ℂ))*f' t‖ ≤ L/2 * ∫ t in u..v, ‖f' t‖ := by
    have hc : ContinuousOn (fun t : ℝ => ((t:ℂ)-(c:ℂ))*f' t) (Set.Icc u v) :=
      (by fun_prop : ContinuousOn (fun t : ℝ => (t:ℂ)-(c:ℂ)) (Set.Icc u v)).mul (hf'.mono hs)
    have hcn : ContinuousOn (fun t : ℝ => L/2*‖f' t‖) (Set.Icc u v) := continuousOn_const.mul (hf'.norm.mono hs)
    refine (intervalIntegral.norm_integral_le_integral_norm huv).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on huv
      (ContinuousOn.intervalIntegrable_of_Icc huv hc.norm)
      (ContinuousOn.intervalIntegrable_of_Icc huv hcn)
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hw t ht) (norm_nonneg _)
  have hs1 : Set.Icc a m ⊆ Set.Icc a b := fun t ht => ⟨ht.1, ht.2.trans hmb⟩
  have hs2 : Set.Icc m b ⊆ Set.Icc a b := fun t ht => ⟨ham.trans ht.1, ht.2⟩
  have h1 := parts a m a ham hs1
  have h2 := parts m b b hmb hs2
  simp only [sub_self, zero_mul, sub_zero] at h1
  simp only [sub_self, zero_mul, zero_sub] at h2
  have hfa := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (ContinuousOn.intervalIntegrable_of_Icc ham (hfc.mono hs1))
    (ContinuousOn.intervalIntegrable_of_Icc hmb (hfc.mono hs2))
  have hid : ((b:ℂ)-(a:ℂ))*f m = (∫ t in a..b, f t) +
      (∫ t in a..m, ((t:ℂ)-(a:ℂ))*f' t) + (∫ t in m..b, ((t:ℂ)-(b:ℂ))*f' t) := by
    rw [← hfa]
    linear_combination -h1 - h2
  have hj1 := boundWeighted a m a ham hs1 (by
    intro t ht
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr ht.1)]
    dsimp [L,m] at *
    linarith [ht.2])
  have hj2 := boundWeighted m b b hmb hs2 (by
    intro t ht
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    dsimp [L,m] at *
    linarith [ht.1])
  have htri : L*‖f m‖ ≤ ‖∫ t in a..b, f t‖ +
      ‖∫ t in a..m, ((t:ℂ)-(a:ℂ))*f' t‖ + ‖∫ t in m..b, ((t:ℂ)-(b:ℂ))*f' t‖ := by
    have he : L*‖f m‖ = ‖((b:ℂ)-(a:ℂ))*f m‖ := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hL.le]
    rw [he,hid]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hfp := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (ContinuousOn.intervalIntegrable_of_Icc ham (hf'.norm.mono hs1))
    (ContinuousOn.intervalIntegrable_of_Icc hmb (hf'.norm.mono hs2))
  have htotal : L*‖f m‖ ≤ (∫ t in a..b, ‖f t‖) + L/2*(∫ t in a..b, ‖f' t‖) := by
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hab.le
    rw [← hfp]
    nlinarith
  rw [intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hab.le hfc.norm) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  change ‖f m‖ ≤ L⁻¹*((∫ t in a..b, ‖f t‖)+L*((1/2)*(∫ t in a..b, ‖f' t‖)))
  calc ‖f m‖ ≤ ((∫ t in a..b, ‖f t‖)+L/2*(∫ t in a..b, ‖f' t‖))/L :=
        (le_div_iff₀ hL).2 (by nlinarith)
    _ = _ := by field_simp [hL.ne']

/-- LEAF. The derivative of `S(α) = Σ a_n e(nα)` is `Σ 2πin a_n e(nα)`.
Gallagher 1967 p. 15. Unit U-1524. -/
theorem hasDerivAt_trig (s : Finset ℤ) (a : ℤ → ℂ) (α : ℝ) :
    HasDerivAt (trig s a) (trigDeriv s a α) α := by
  unfold trig trigDeriv
  apply HasDerivAt.fun_sum
  intro n hn
  have hd : HasDerivAt (fun x : ℝ => e (n * x)) ((2 * π * Complex.I * n) * e (n * α)) α := by
    have hc : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 α := Complex.ofRealCLM.hasDerivAt
    have hh := ((hc.const_mul (n : ℂ)).const_mul (2 * π * Complex.I)).cexp
    convert hh using 1 <;> simp [e] <;> ring
  convert hd.const_mul (a n) using 1 <;> ring

/-- LEAF. Parseval for a trigonometric polynomial:
`∫_0^1 |Σ_{n ∈ s} a_n e(nα)|² dα = Σ_{n ∈ s} |a_n|²`. Montgomery-Vaughan, MNT I, Section 7.4;
Gallagher 1967 p. 15. Unit U-1524. -/
theorem parseval_trig (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ α in (0 : ℝ)..1, ‖trig s a α‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have hadd (u v : ℝ) : e (u+v) = e u * e v := LeanLab.ExceptionalSet.Lu2010Orth.ee_add u v
  have hconj (u : ℝ) : conj (e u) = e (-u) := by
    unfold e
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
  have he (j : ℤ) : (∫ t in (0:ℝ)..1, e ((j:ℝ)*t)) = if j=0 then 1 else 0 := by
    simpa [e, LeanLab.ExceptionalSet.Lu2010Orth.ee] using LeanLab.ExceptionalSet.Lu2010Orth.integral_ee j 0
  have hexp (t : ℝ) : ((‖trig s a t‖^2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * conj (a m)) * e (((n-m:ℤ):ℝ)*t) := by
    unfold trig
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [map_mul, hconj]
    have hh : e ((n:ℝ)*t) * e (-((m:ℝ)*t)) = e (((n-m:ℤ):ℝ)*t) := by
      rw [← hadd]
      congr 1
      push_cast
      ring
    rw [← hh]
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hexp]
  rw [intervalIntegral.integral_finset_sum (fun n hn => (by unfold e; fun_prop : Continuous (fun t : ℝ => ∑ m ∈ s, (a n * conj (a m)) * e (((n-m:ℤ):ℝ)*t))).intervalIntegrable _ _)]
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finset_sum (fun m hm => (by unfold e; fun_prop : Continuous (fun t : ℝ => (a n * conj (a m)) * e (((n-m:ℤ):ℝ)*t))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, he]
  have hdiag : ∀ m ∈ s, (a n * conj (a m)) * (if n-m=0 then 1 else 0) =
      if m=n then ((‖a n‖^2 : ℝ):ℂ) else 0 := by
    intro m hm
    by_cases hmn : m=n
    · subst m
      simp [Complex.mul_conj', Complex.ofReal_pow]
    · have hne : n-m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
      simp [hne, hmn]
  rw [sum_congr rfl hdiag]
  simp [hn]

/-- LEAF. For `s ⊆ [-K, K]`: `∫_0^1 |S| |S'| ≤ 2πK Σ |a_n|²`, by Cauchy-Schwarz and Parseval
for `S` and `S'`. Gallagher 1967 p. 15, with the frequencies centred. Unit U-1524. -/
theorem integral_norm_mul_deriv_le (s : Finset ℤ) (a : ℤ → ℂ) (K : ℕ)
    (hs : s ⊆ Finset.Icc (-(K : ℤ)) K) :
    ∫ α in (0 : ℝ)..1, ‖trig s a α‖ * ‖trigDeriv s a α‖ ≤ 2 * π * K * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  by_cases hK : K = 0
  · subst K
    have hz : ∀ n ∈ s, n = 0 := by intro n hn; have hh := Finset.mem_Icc.mp (hs hn); simp at hh; omega
    have hD (t : ℝ) : trigDeriv s a t = 0 := by
      unfold trigDeriv
      apply sum_eq_zero
      intro n hn
      rw [hz n hn]
      simp
    simp_rw [hD]
    simp
  have hK0 : 0 < K := Nat.pos_of_ne_zero hK
  let t : ℝ := 2 * π * K
  have ht : 0 < t := by dsimp [t]; positivity
  let f : ℝ → ℝ := fun u => ‖trig s a u‖
  let g : ℝ → ℝ := fun u => ‖trigDeriv s a u‖
  have hf : Continuous f := by unfold f trig e; fun_prop
  have hg : Continuous g := by unfold g trigDeriv e; fun_prop
  have hF : (∫ u in (0:ℝ)..1, (f u)^2) = ∑ n ∈ s, ‖a n‖^2 := parseval_trig s a
  have hG : (∫ u in (0:ℝ)..1, (g u)^2) ≤ t^2 * ∑ n ∈ s, ‖a n‖^2 := by
    change (∫ u in (0:ℝ)..1, ‖trig s (fun n => (2*π*Complex.I*n)*a n) u‖^2) ≤ _
    rw [parseval_trig, Finset.mul_sum]
    apply sum_le_sum
    intro n hn
    have hnK := Finset.mem_Icc.mp (hs hn)
    have hnabs : |(n:ℝ)| ≤ K := by
      apply abs_le.mpr
      constructor
      · exact_mod_cast hnK.1
      · exact_mod_cast hnK.2
    have hcoef : ‖(2*π*Complex.I*(n:ℂ))‖ ≤ t := by
      norm_num [norm_mul, Complex.norm_intCast, abs_of_pos pi_pos]
      dsimp [t]
      nlinarith [mul_le_mul_of_nonneg_left hnabs (show 0 ≤ 2*π by positivity)]
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) hcoef 2
  have hpoint (u : ℝ) : 2*t*(f u*g u) ≤ t^2*(f u)^2+(g u)^2 := by nlinarith [sq_nonneg (t*f u-g u)]
  have hint : 2*t*(∫ u in (0:ℝ)..1, f u*g u) ≤ t^2*(∫ u in (0:ℝ)..1, (f u)^2)+(∫ u in (0:ℝ)..1, (g u)^2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_mono_on (by norm_num)
        ((by fun_prop : Continuous (fun u => 2*t*(f u*g u))).intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun u => t^2*(f u)^2+(g u)^2)).intervalIntegrable _ _)
      intro u hu
      exact hpoint u
    · exact ((hf.pow 2).const_mul _).intervalIntegrable _ _
    · exact (hg.pow 2).intervalIntegrable _ _
  rw [hF] at hint
  change (∫ u in (0:ℝ)..1, f u*g u) ≤ t * ∑ n ∈ s, ‖a n‖^2
  apply (mul_le_mul_iff_right₀ (show 0 < 2*t by positivity)).mp
  nlinarith

/-- LEAF. Disjoint arcs: if `g ≥ 0` is continuous and 1-periodic and the points `x_r` are
`δ`-spaced modulo 1 with `0 < δ ≤ 1`, then `Σ_r ∫_{x_r-δ/2}^{x_r+δ/2} g ≤ ∫_0^1 g`.
Gallagher 1967 p. 15. Unit U-1524. -/
theorem periodic_disjoint_sum {ι : Type*} (pts : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsp : Spaced pts x δ) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    (hper : ∀ t, g (t + 1) = g t) :
    ∑ r ∈ pts, ∫ t in (x r - δ / 2)..(x r + δ / 2), g t ≤ ∫ t in (0 : ℝ)..1, g t := by
  classical
  have hp : Function.Periodic g 1 := hper
  rcases pts.eq_empty_or_nonempty with rfl | hpts
  · simp only [sum_empty]
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num) hg0
  obtain ⟨r0,hr0⟩ := hpts
  let k : ι → ℤ := fun r => ⌊x r - x r0⌋
  let y : ι → ℝ := fun r => x r - k r
  let a0 := x r0 - δ/2
  have hy (r : ι) : x r0 ≤ y r ∧ y r < x r0+1 := by
    have hl := Int.floor_le (x r-x r0)
    have hu := Int.lt_floor_add_one (x r-x r0)
    dsimp [y,k]
    constructor <;> linarith
  have htop : ∀ r ∈ pts, y r ≤ x r0+1-δ := by
    intro r hr
    by_cases he : r=r0
    · subst r
      simp only [y,k,sub_self,Int.floor_zero,Int.cast_zero,sub_zero]
      linarith
    · have hh := hsp r hr r0 hr0 he (k r+1)
      push_cast at hh
      have hn : x r-x r0-((k r:ℝ)+1) ≤ 0 := by
        have hh := (hy r).2
        dsimp [y] at hh
        linarith
      rw [abs_of_nonpos hn] at hh
      dsimp [y]
      linarith
  have hsep : ∀ r ∈ pts, ∀ s ∈ pts, r ≠ s → δ ≤ |y r-y s| := by
    intro r hr s hs hne
    have hh := hsp r hr s hs hne (k r-k s)
    have he : x r-x s-((k r-k s:ℤ):ℝ) = y r-y s := by dsimp [y]; push_cast; ring
    rwa [he] at hh
  let arcs : ι → Set ℝ := fun r => Set.Ioc (y r-δ/2) (y r+δ/2)
  have hsub : ∀ r ∈ pts, arcs r ⊆ Set.Ioc a0 (a0+1) := by
    intro r hr t ht
    have hylo := (hy r).1
    have hyhi := htop r hr
    dsimp [arcs] at ht
    dsimp [a0]
    constructor <;> linarith [ht.1,ht.2]
  have hdis : (↑pts : Set ι).Pairwise (Function.onFun Disjoint arcs) := by
    intro r hr s hs hne
    apply Set.disjoint_left.mpr
    intro t htr hts
    have hh := hsep r hr s hs hne
    have hlt : |y r-y s| < δ := by
      apply abs_lt.mpr
      dsimp [arcs] at htr hts
      constructor <;> linarith [htr.1,htr.2,hts.1,hts.2]
    linarith
  have hshift : ∀ r ∈ pts, (∫ t in (x r-δ/2)..(x r+δ/2), g t) = ∫ t in (y r-δ/2)..(y r+δ/2), g t := by
    intro r hr
    have hk : Function.Periodic g (k r:ℝ) := by simpa using hp.int_mul (k r)
    have hh := intervalIntegral.integral_comp_add_right (a := y r-δ/2) (b := y r+δ/2) g (k r:ℝ)
    have he1 : y r-δ/2+(k r:ℝ)=x r-δ/2 := by dsimp [y]; ring
    have he2 : y r+δ/2+(k r:ℝ)=x r+δ/2 := by dsimp [y]; ring
    rw [he1,he2] at hh
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hk t
  rw [sum_congr rfl hshift]
  have heach : ∀ r ∈ pts, (∫ t in (y r-δ/2)..(y r+δ/2), g t) = ∫ t in arcs r, g t := by
    intro r hr
    exact intervalIntegral.integral_of_le (by linarith)
  rw [sum_congr rfl heach, ← MeasureTheory.integral_biUnion_finset pts (fun r hr => measurableSet_Ioc) hdis
    (fun r hr => (hg.intervalIntegrable (y r-δ/2) (y r+δ/2)).1)]
  have hUnion : (⋃ r ∈ pts, arcs r) ⊆ Set.Ioc a0 (a0+1) := by
    intro t ht
    obtain ⟨r,ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hr,ht⟩ := Set.mem_iUnion.mp ht
    exact hsub r hr ht
  calc (∫ t in ⋃ r ∈ pts, arcs r, g t) ≤ ∫ t in Set.Ioc a0 (a0+1), g t :=
        MeasureTheory.setIntegral_mono_set (hg.intervalIntegrable a0 (a0+1)).1
          (Filter.Eventually.of_forall (fun t => hg0 t)) (Filter.Eventually.of_forall (fun t ht => hUnion ht))
    _ = ∫ t in a0..(a0+1), g t := (intervalIntegral.integral_of_le (by linarith)).symm
    _ = ∫ t in (0:ℝ)..1, g t := by simpa using hp.intervalIntegral_add_eq a0 0

/-- LEAF. Shifting the frequencies by `c ∈ ℤ`:
`S(α) e(-cα) = Σ_{m ∈ s - c} a_{m+c} e(mα)`. Gallagher 1967 p. 15. Unit U-1524. -/
theorem shift_trig (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (α : ℝ) :
    trig s a α * e (-((c : ℝ) * α)) = trig (s.image (· - c)) (fun n => a (n + c)) α := by
  classical
  unfold trig
  have hinj : ∀ x ∈ s, ∀ y ∈ s, x - c = y - c → x = y := by
    intro x hx y hy hxy
    omega
  rw [Finset.sum_mul, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [sub_add_cancel, Int.cast_sub]
  rw [mul_assoc]
  congr 1
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- LEAF. The analytic large sieve for centred frequencies `s ⊆ [-K, K]`: for points `δ`-spaced
modulo 1, `0 < δ ≤ 1`, `Σ_r |S(x_r)|² ≤ (2πK + δ⁻¹) Σ |a_n|²`. Proof: `sobolev_pointwise` on
`S²` over `[x_r - δ/2, x_r + δ/2]`, `hasDerivAt_trig`, `periodic_disjoint_sum` for `|S|²` and
`|S||S'|`, then `parseval_trig` and `integral_norm_mul_deriv_le`. Gallagher 1967 Theorem 1,
p. 15. Unit U-1524. -/
theorem large_sieve_centered {ι : Type*} (pts : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsp : Spaced pts x δ) (s : Finset ℤ) (a : ℤ → ℂ) (K : ℕ)
    (hs : s ⊆ Finset.Icc (-(K : ℤ)) K) :
    ∑ r ∈ pts, ‖trig s a (x r)‖ ^ 2 ≤ (2 * π * K + δ⁻¹) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  let V : ℝ → ℂ := trig s a
  let D : ℝ → ℂ := trigDeriv s a
  let F : ℝ → ℂ := fun t => V t * star (V t)
  let G : ℝ → ℂ := fun t => D t * star (V t) + V t * star (D t)
  have hV : Continuous V := by unfold V trig e; fun_prop
  have hD : Continuous D := by unfold D trigDeriv e; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hdF (t : ℝ) : HasDerivAt F (G t) t := by
    exact (hasDerivAt_trig s a t).mul (hasDerivAt_trig s a t).star
  have hnF (t : ℝ) : ‖F t‖ = ‖V t‖^2 := by simp [F,norm_mul,pow_two]
  have hnG (t : ℝ) : ‖G t‖ ≤ 2*(‖V t‖*‖D t‖) := by
    calc ‖G t‖ ≤ ‖D t * star (V t)‖ + ‖V t * star (D t)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul,norm_mul,norm_star,norm_star]; ring
  have eint (n : ℤ) : e (n:ℝ) = 1 := by
    unfold e
    convert Complex.exp_int_mul_two_pi_mul_I n using 1
    congr 1
    push_cast
    ring
  have eperiod (n : ℤ) (t : ℝ) : e ((n:ℝ)*(t+1)) = e ((n:ℝ)*t) := by
    have hadd (u v : ℝ) : e (u+v) = e u * e v := LeanLab.ExceptionalSet.Lu2010Orth.ee_add u v
    rw [show (n:ℝ)*(t+1)=(n:ℝ)*t+n by ring,hadd,eint,mul_one]
  have hVp (t : ℝ) : V (t+1) = V t := by dsimp [V,trig]; simp_rw [eperiod]
  have hDp (t : ℝ) : D (t+1) = D t := by dsimp [D,trigDeriv]; simp_rw [eperiod]
  have hV2 : Continuous (fun t : ℝ => ‖V t‖^2) := by fun_prop
  have hVD : Continuous (fun t : ℝ => ‖V t‖*‖D t‖) := by fun_prop
  have hp (r : ι) (hr : r ∈ pts) : ‖V (x r)‖^2 ≤
      δ⁻¹ * (∫ t in (x r-δ/2)..(x r+δ/2), ‖V t‖^2) +
        (∫ t in (x r-δ/2)..(x r+δ/2), ‖V t‖*‖D t‖) := by
    let u := x r-δ/2
    let v := x r+δ/2
    have huv : u < v := by dsimp [u,v]; linarith
    have hmid : (u+v)/2=x r := by dsimp [u,v]; ring
    have hlen : v-u=δ := by dsimp [u,v]; ring
    have hb := sobolev_pointwise (f := F) (f' := G) huv (fun t ht => hdF t) hG.continuousOn
    rw [hmid] at hb
    simp_rw [hnF] at hb
    rw [intervalIntegral.integral_add (hV2.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const,smul_eq_mul,hlen] at hb
    have halg (X Y : ℝ) : δ⁻¹*(X+δ*((1/2)*Y)) = δ⁻¹*X+(1/2)*Y := by field_simp [hδ.ne']
    rw [halg] at hb
    have hGi : (∫ t in u..v, ‖G t‖) ≤ 2*(∫ t in u..v, ‖V t‖*‖D t‖) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on huv.le (hG.norm.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun t : ℝ => 2*(‖V t‖*‖D t‖))).intervalIntegrable _ _)
      intro t ht
      exact hnG t
    nlinarith
  have hsum := sum_le_sum (fun r hr => hp r hr)
  rw [sum_add_distrib,← mul_sum] at hsum
  have h1 := periodic_disjoint_sum pts x hδ hδ1 hsp hV2
    (fun t => sq_nonneg _) (fun t => by rw [hVp])
  have h2 := periodic_disjoint_sum pts x hδ hδ1 hsp hVD
    (fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun t => by rw [hVp,hDp])
  calc ∑ r ∈ pts, ‖trig s a (x r)‖^2 ≤
        δ⁻¹*(∑ r ∈ pts, ∫ t in (x r-δ/2)..(x r+δ/2), ‖V t‖^2) +
        (∑ r ∈ pts, ∫ t in (x r-δ/2)..(x r+δ/2), ‖V t‖*‖D t‖) := hsum
    _ ≤ δ⁻¹*(∫ t in (0:ℝ)..1, ‖V t‖^2)+(∫ t in (0:ℝ)..1, ‖V t‖*‖D t‖) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
    _ ≤ δ⁻¹*(∑ n ∈ s, ‖a n‖^2)+(2*π*K)*(∑ n ∈ s, ‖a n‖^2) := by
      rw [show (∫ t in (0:ℝ)..1, ‖V t‖^2) = ∑ n ∈ s, ‖a n‖^2 from parseval_trig s a]
      exact add_le_add le_rfl (integral_norm_mul_deriv_le s a K hs)
    _ = _ := by ring

/-- **The analytic large sieve, Gallagher's form**, PROVED from `large_sieve_centered` and
`shift_trig`: for points `δ`-spaced modulo 1, `0 < δ ≤ 1`,
`Σ_r |Σ_{n=M+1}^{M+N} a_n e(n x_r)|² ≤ (πN + δ⁻¹) Σ |a_n|²`. Gallagher 1967 Theorem 1.
Unit U-1524. -/
theorem large_sieve {ι : Type*} (pts : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsp : Spaced pts x δ) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∑ r ∈ pts, ‖trig (Finset.Icc (M + 1) (M + N)) a (x r)‖ ^ 2 ≤
      (π * N + δ⁻¹) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  set s := Finset.Icc (M + 1) (M + N) with hsdef
  set c : ℤ := M + ((N + 1) / 2 : ℕ) with hc
  set K : ℕ := N / 2 with hK
  have hinj : Set.InjOn (fun n : ℤ => n - c) s := by
    intro u _ v _ h; simpa using h
  have hsub : s.image (· - c) ⊆ Finset.Icc (-(K : ℤ)) K := by
    intro m hm
    simp only [Finset.mem_image, hsdef, Finset.mem_Icc] at hm
    obtain ⟨n, ⟨h1, h2⟩, rfl⟩ := hm
    simp only [Finset.mem_Icc, hc, hK]
    omega
  have hnorm : ∀ r ∈ pts, ‖trig s a (x r)‖ ^ 2 =
      ‖trig (s.image (· - c)) (fun n => a (n + c)) (x r)‖ ^ 2 := by
    intro r _
    rw [← shift_trig, norm_mul, norm_e, mul_one]
  have hsum : ∑ n ∈ s.image (· - c), ‖a (n + c)‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    rw [Finset.sum_image (fun u hu v hv h => hinj hu hv h)]
    simp
  have hmain := large_sieve_centered pts x hδ hδ1 hsp (s.image (· - c)) (fun n => a (n + c))
    K hsub
  rw [hsum] at hmain
  rw [Finset.sum_congr rfl hnorm]
  refine hmain.trans ?_
  have hK2 : (2 * π * K : ℝ) ≤ π * N := by
    have : (2 * K : ℝ) ≤ N := by
      have : 2 * K ≤ N := by omega
      exact_mod_cast this
    nlinarith [Real.pi_pos]
  have hnn : 0 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith) hnn

/-- LEAF. Well-spaced points: if the reals `x_r` satisfy `|x_r - x_s| ≥ δ > 0` for `r ≠ s`,
then at most `L/δ + 1` of them lie in an interval `[u, u+L]`, `L ≥ 0`.
Montgomery, Topics, Ch. 3; Montgomery-Vaughan, MNT I, Section 7.4. Unit U-1524. -/
theorem spaced_count_le {ι : Type*} (pts : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsp : ∀ r ∈ pts, ∀ s ∈ pts, r ≠ s → δ ≤ |x r - x s|) (u L : ℝ) (hL : 0 ≤ L) :
    ((pts.filter (fun r => x r ∈ Set.Icc u (u + L))).card : ℝ) ≤ L / δ + 1 := by
  classical
  let B := pts.filter (fun r => x r ∈ Set.Icc u (u+L))
  let f : ι → ℕ := fun r => ⌊(x r-u)/δ⌋₊
  have hb : ∀ r ∈ B, 0 ≤ (x r-u)/δ ∧ (x r-u)/δ ≤ L/δ := by
    intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    constructor
    · exact div_nonneg (sub_nonneg.mpr hh.1) hδ.le
    · exact div_le_div_of_nonneg_right (by linarith [hh.2]) hδ.le
  have hinj : Set.InjOn f (↑B : Set ι) := by
    intro r hr s hs hfs
    by_contra hne
    have hg := hsp r (Finset.mem_filter.mp hr).1 s (Finset.mem_filter.mp hs).1 hne
    have hrlo := Nat.floor_le (hb r hr).1
    have hslo := Nat.floor_le (hb s hs).1
    have hrup := Nat.lt_floor_add_one ((x r-u)/δ)
    have hsup := Nat.lt_floor_add_one ((x s-u)/δ)
    change ⌊(x r-u)/δ⌋₊ = ⌊(x s-u)/δ⌋₊ at hfs
    rw [hfs] at hrlo hrup
    have habs : |x r-x s| < δ := by
      apply abs_lt.mpr
      constructor <;> nlinarith [(le_div_iff₀ hδ).mp hrlo, (le_div_iff₀ hδ).mp hslo,
        (div_lt_iff₀ hδ).mp hrup, (div_lt_iff₀ hδ).mp hsup]
    linarith
  have hmap : Set.MapsTo f (↑B : Set ι) (↑(Finset.range (⌊L/δ⌋₊+1)) : Set ℕ) := by
    intro r hr
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_mono (hb r hr).2)
  have hc : B.card ≤ ⌊L/δ⌋₊+1 := by
    have hc := Finset.card_le_card_of_injOn f hmap hinj
    simpa using hc
  have hcf : (B.card : ℝ) ≤ (⌊L/δ⌋₊ : ℝ)+1 := by exact_mod_cast hc
  exact hcf.trans (by linarith [Nat.floor_le (div_nonneg hL hδ.le)])

/-! ### The arithmetic large sieve -/

/-- The Farey points `(q, a)`, `1 ≤ a ≤ q ≤ Q`, `(a, q) = 1`, standing for `a/q`. -/
def fareyPts (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q ×ˢ Finset.Icc 1 Q).filter (fun p => p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1)

/-- LEAF. The Farey fractions `a/q`, `1 ≤ a ≤ q ≤ Q`, `(a,q) = 1`, are `Q⁻²`-spaced modulo 1:
`|a/q - a'/q' - m| = |aq' - a'q - mqq'|/(qq') ≥ 1/(qq') ≥ Q⁻²`. Gallagher 1967 p. 16;
Montgomery-Vaughan 1975 p. 355 for the arcs. Unit U-1524. -/
theorem farey_spaced (Q : ℕ) :
    Spaced (fareyPts Q) (fun p => (p.2 : ℝ) / p.1) ((Q : ℝ) ^ 2)⁻¹ := by
  rintro ⟨q,a⟩ hp ⟨q',a'⟩ hp' hne m
  obtain ⟨hI, haq, hcop⟩ := mem_filter.mp hp
  obtain ⟨hI', haq', hcop'⟩ := mem_filter.mp hp'
  obtain ⟨hq1,hqQ⟩ := mem_Icc.mp (mem_product.mp hI).1
  obtain ⟨hq1',hqQ'⟩ := mem_Icc.mp (mem_product.mp hI').1
  have ha1 := (mem_Icc.mp (mem_product.mp hI).2).1
  have ha1' := (mem_Icc.mp (mem_product.mp hI').2).1
  simp only [Prod.fst, Prod.snd] at *
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqpos' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  set j : ℤ := (a : ℤ) * q' - a' * q - m * q * q' with hj
  have hx : (a : ℝ) / q - a' / q' - m = j / (q * q') := by
    rw [hj]; push_cast; field_simp
  have hj0 : j ≠ 0 := by
    intro hj0
    rw [hj0, Int.cast_zero, zero_div, sub_eq_zero] at hx
    -- `a/q - a'/q'` is an integer of absolute value below one, hence zero
    have hlt1 : |(a : ℝ) / q - a' / q'| < 1 := by
      have h1 : (a : ℝ) / q ≤ 1 := by
        rw [div_le_one hqpos]; exact_mod_cast haq
      have h2 : (a' : ℝ) / q' ≤ 1 := by
        rw [div_le_one hqpos']; exact_mod_cast haq'
      have h3 : 0 < (a : ℝ) / q := div_pos (by exact_mod_cast ha1) hqpos
      have h4 : 0 < (a' : ℝ) / q' := div_pos (by exact_mod_cast ha1') hqpos'
      rw [abs_lt]; constructor <;> linarith
    rw [hx] at hlt1
    have hm0 : m = 0 := by
      have : |(m : ℝ)| < 1 := hlt1
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at this
      have := abs_lt.1 this; omega
    rw [hm0, Int.cast_zero, sub_eq_zero, div_eq_div_iff hqpos.ne' hqpos'.ne'] at hx
    have hnat : a * q' = a' * q := by exact_mod_cast hx
    have hd1 : q ∣ q' := by
      have : q ∣ a * q' := ⟨a', by rw [hnat, mul_comm]⟩
      exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
    have hd2 : q' ∣ q := by
      have : q' ∣ a' * q := ⟨a, by rw [← hnat, mul_comm]⟩
      exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    subst hqq
    have haa : a = a' := Nat.eq_of_mul_eq_mul_right (by omega) hnat
    exact hne (by rw [haa])
  rw [hx, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs hj0
  have hQ : (q : ℝ) * q' ≤ (Q : ℝ) ^ 2 := by
    have : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have : (q' : ℝ) ≤ Q := by exact_mod_cast hqQ'
    nlinarith
  calc ((Q : ℝ) ^ 2)⁻¹ = 1 / (Q : ℝ)^2 := by rw [one_div]
    _ ≤ 1 / (q * q') := one_div_le_one_div_of_le (by positivity) hQ
    _ ≤ |(j : ℝ)| / (q * q') := div_le_div_of_nonneg_right hj1 (by positivity)

/-- **The arithmetic large sieve**, PROVED from `large_sieve` and `farey_spaced`:
`Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|² ≤ (πN + Q²) Σ |a_n|²` for `Q ≥ 1`. Gallagher 1967
Theorem 2. Unit U-1524. -/
theorem arith_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∑ p ∈ fareyPts Q, ‖trig (Finset.Icc (M + 1) (M + N)) a ((p.2 : ℝ) / p.1)‖ ^ 2 ≤
      (π * N + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hpos : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by positivity
  have hle : ((Q : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have h := large_sieve (fareyPts Q) (fun p => (p.2 : ℝ) / p.1) hpos hle (farey_spaced Q) M N a
  simpa [inv_inv] using h

/-! ### Duality -/

/-- LEAF. The duality principle, finite form: if `Σ_r |Σ_n c_{rn} u_n|² ≤ D Σ_n |u_n|²` for all
`u`, with `D ≥ 0`, then `Σ_n |Σ_r c_{rn} v_r|² ≤ D Σ_r |v_r|²` for all `v`.
Montgomery-Vaughan, MNT I, Section 7.4 (duality); Montgomery, Topics, Ch. 2.
Unit U-1524. -/
theorem duality {ι κ : Type*} (R : Finset ι) (Nn : Finset κ) (c : ι → κ → ℂ) {D : ℝ}
    (hD : 0 ≤ D)
    (h : ∀ u : κ → ℂ, ∑ r ∈ R, ‖∑ n ∈ Nn, c r n * u n‖ ^ 2 ≤ D * ∑ n ∈ Nn, ‖u n‖ ^ 2)
    (v : ι → ℂ) :
    ∑ n ∈ Nn, ‖∑ r ∈ R, c r n * v r‖ ^ 2 ≤ D * ∑ r ∈ R, ‖v r‖ ^ 2 := by
  let B : κ → ℂ := fun n => ∑ r ∈ R, c r n * v r
  let u : κ → ℂ := fun n => conj (B n)
  let X : ℝ := ∑ n ∈ Nn, ‖B n‖^2
  let V : ℝ := ∑ r ∈ R, ‖v r‖^2
  have hX0 : 0 ≤ X := sum_nonneg (fun _ _ => sq_nonneg _)
  have hV0 : 0 ≤ V := sum_nonneg (fun _ _ => sq_nonneg _)
  have hX : (X : ℂ) = ∑ r ∈ R, v r * ∑ n ∈ Nn, c r n * u n := by
    calc (X : ℂ) = ∑ n ∈ Nn, B n * u n := by
          dsimp only [X]
          rw [Complex.ofReal_sum]
          apply sum_congr rfl
          intro n hn
          rw [Complex.ofReal_pow, ← Complex.mul_conj']
      _ = _ := by
          dsimp only [B]
          simp_rw [sum_mul, mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro r hr
          apply sum_congr rfl
          intro n hn
          ring
  have h1 : X ≤ ∑ r ∈ R, ‖v r‖ * ‖∑ n ∈ Nn, c r n * u n‖ := by
    have hh : X = ‖(X:ℂ)‖ := by simp [Real.norm_of_nonneg hX0]
    rw [hh, hX]
    simpa only [norm_mul] using (norm_sum_le R (fun r => v r * ∑ n ∈ Nn, c r n * u n))
  have h2 := sum_mul_sq_le_sq_mul_sq R (fun r => ‖v r‖) (fun r => ‖∑ n ∈ Nn, c r n * u n‖)
  have h3 := h u
  have huX : (∑ n ∈ Nn, ‖u n‖^2) = X := by simp only [u, Complex.norm_conj, X]
  rw [huX] at h3
  have hk : X^2 ≤ V * (D*X) := by
    calc X^2 ≤ (∑ r ∈ R, ‖v r‖ * ‖∑ n ∈ Nn, c r n * u n‖)^2 := pow_le_pow_left₀ hX0 h1 2
      _ ≤ V * ∑ r ∈ R, ‖∑ n ∈ Nn, c r n * u n‖^2 := h2
      _ ≤ V * (D*X) := mul_le_mul_of_nonneg_left h3 hV0
  change X ≤ D * V
  rcases eq_or_lt_of_le hX0 with hz | hp
  · rw [← hz]; positivity
  · have hh : X*X ≤ X*(D*V) := by nlinarith
    exact le_of_mul_le_mul_left hh hp

/-! ### Characters: from additive to multiplicative -/

/-- The Gauss sum `τ(χ) = Σ_{b=0}^{q-1} χ(b) e(b/q)`. -/
noncomputable def tau {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ b ∈ Finset.range q, χ (b : ZMod q) * e ((b : ℝ) / q)

/-- The range sum convention agrees with the standard additive character. -/
theorem gaussSum_mulShift_eq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℤ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod q)) =
      ∑ b ∈ Finset.range q, χ (b : ZMod q) * e ((b : ℝ)*n/q) := by
  unfold gaussSum
  refine sum_nbij' (fun j : ZMod q => j.val) (fun b => (b : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact mem_range.2 (ZMod.val_lt j)
  · intro b _; exact mem_univ _
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro b hb; exact ZMod.val_natCast_of_lt (mem_range.1 hb)
  · intro j hj
    rw [AddChar.mulShift_apply]
    congr 1
    · simp
    · have he : (n : ZMod q) * j = ((n * j.val : ℤ) : ZMod q) := by push_cast; simp
      rw [he, stdAddChar_coe]
      unfold e
      congr 1
      push_cast
      ring

/-- LEAF. For a primitive character `χ` mod `q ≥ 1` and every integer `n`,
`χ(n) τ(χ̄) = Σ_{b mod q} χ̄(b) e(bn/q)`; for `(n,q) > 1` both sides vanish by primitivity.
Davenport, Mult. Number Theory, Ch. 9, (2); Montgomery-Vaughan, MNT I, Theorem 9.5.
Unit U-1524. -/
theorem char_mul_tau {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (n : ℤ) :
    χ (n : ZMod q) * tau χ⁻¹ = ∑ b ∈ Finset.range q, χ⁻¹ (b : ZMod q) * e ((b : ℝ) * n / q) := by
  letI : NeZero q := ⟨by omega⟩
  have hi : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv] using hχ
  rw [← gaussSum_mulShift_eq_sum]
  have ht : tau χ⁻¹ = gaussSum χ⁻¹ stdAddChar := by
    have hh := gaussSum_mulShift_eq_sum χ⁻¹ 1
    simpa [tau] using hh.symm
  rw [ht, gaussSum_mulShift_of_isPrimitive _ hi, inv_inv]

/-- LEAF. For a primitive character `χ` mod `q ≥ 1`, `|τ(χ)|² = q`.
Davenport, Mult. Number Theory, Ch. 9, (10); Montgomery-Vaughan, MNT I, Theorem 9.7.
Unit U-1524. -/
theorem norm_tau_sq {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖tau χ‖ ^ 2 = q := by
  letI : NeZero q := ⟨by omega⟩
  have ht : tau χ = gaussSum χ stdAddChar := by
    have hh := gaussSum_mulShift_eq_sum χ 1
    simpa [tau] using hh.symm
  rw [ht]
  exact LeanLab.RieselVaughan1983.GaussImprim.norm_sq_gaussSum_of_isPrimitive hχ

/-- LEAF. Orthogonality over the characters mod `q ≥ 1`:
`Σ_χ |Σ_{b mod q} χ(b) z_b|² = φ(q) Σ_{b mod q, (b,q)=1} |z_b|²`.
Davenport, Mult. Number Theory, Ch. 27, (4); Montgomery-Vaughan, MNT I, Section 4.2.
Unit U-1524. -/
theorem char_orthogonality_sum {q : ℕ} (hq : 1 ≤ q) (z : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b ∈ Finset.range q, χ (b : ZMod q) * z b‖ ^ 2 =
      (Nat.totient q : ℝ) * ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖z b‖ ^ 2 := by
  letI : NeZero q := ⟨by omega⟩
  have hsum (χ : DirichletCharacter ℂ q) : (∑ b ∈ range q, χ (b : ZMod q)*z b) =
      ∑ j : ZMod q, χ j * z j.val := by
    rw [← LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range (fun b => χ (b : ZMod q)*z b)]
    simp only [natCast_zmod_val]
  simp_rw [hsum]
  rw [LeanLab.RieselVaughan1983.GaussImprim.sum_norm_sq_twist]
  congr 1
  rw [sum_filter, sum_filter]
  have hh := LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range_real (M := q)
    (fun b => if Nat.Coprime b q then ‖z b‖^2 else 0)
  refine (sum_congr rfl (fun j hj => ?_)).trans hh
  have hu : IsUnit j ↔ Nat.Coprime j.val q := by
    simpa only [natCast_zmod_val] using (ZMod.isUnit_iff_coprime j.val q)
  simp only [hu]

/-- LEAF. The multiplicative large sieve: for `Q ≥ 1`,
`Σ_{q ≤ Q} (q/φ(q)) Σ*_{χ mod q} |Σ_{n=M+1}^{M+N} a_n χ(n)|² ≤ (πN + Q²) Σ |a_n|²`,
the sum over primitive `χ`. From `char_mul_tau`, `norm_tau_sq`, `char_orthogonality_sum` and
`arith_large_sieve` (the residue `b = 0` only occurs for `q = 1`, where `S(0) = S(1)`).
Davenport, Mult. Number Theory, Ch. 27, Theorem 4; Gallagher 1967 Theorem 3. Unit U-1524. -/
theorem mult_large_sieve {Q : ℕ} (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / Nat.totient q) *
        ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2 ≤
      (π * N + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  classical
  let I := Icc (M+1) (M+N)
  let b : ℤ → ℂ := fun n => (starRingEnd ℂ) (a n)
  have he (t : ℝ) : e t = LeanLab.PNTPort.LargeSieve.e t := by
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have htrig (t : ℝ) : trig I b t = (∑ n ∈ I, b n * LeanLab.PNTPort.LargeSieve.e ((n:ℝ)*t)) := by
    unfold trig
    simp_rw [he]
  have hper (t : ℝ) : trig I b (t+1) = trig I b t := by
    unfold trig
    simp_rw [he]
    apply sum_congr rfl
    intro n hn
    rw [show (n:ℝ)*(t+1)=(n:ℝ)*t+n by ring,
      LeanLab.PNTPort.LargeSieve.e_add,LeanLab.PNTPort.LargeSieve.e_int,mul_one]
  have hrow (q : ℕ) (hq : q ∈ Icc 1 Q) :
      ((q:ℝ)/q.totient) * ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ‖∑ n ∈ I, a n * χ (n:ZMod q)‖^2 ≤
      ∑ c ∈ (Icc 1 q).filter (fun c => Nat.Coprime c q), ‖trig I b ((c:ℝ)/q)‖^2 := by
    have hq0 : 0<q := (mem_Icc.mp hq).1
    letI : NeZero q := ⟨hq0.ne'⟩
    have hh := LeanLab.PNTPort.LargeSieve.prim_chars_le (q := q) I a
    change ((q:ℝ)/q.totient) * ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ‖∑ n ∈ I, a n * χ (n:ZMod q)‖^2 ≤
      ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), ‖∑ n ∈ I, b n * LeanLab.PNTPort.LargeSieve.e ((n:ℝ)*((c:ℝ)/q))‖^2 at hh
    simp_rw [← htrig] at hh
    refine hh.trans (le_of_eq ?_)
    by_cases hq1 : q=1
    · subst q
      simp only [range_one,filter_singleton,Nat.coprime_one_right,ite_true,sum_singleton,
        Icc_self,Nat.cast_zero,zero_div,Nat.cast_one,div_one]
      simpa using congrArg (fun z : ℂ => ‖z‖) (hper 0).symm
    · have hset : (range q).filter (fun c => Nat.Coprime c q) = (Icc 1 q).filter (fun c => Nat.Coprime c q) := by
        ext c
        simp only [mem_filter,mem_range,mem_Icc]
        constructor
        · rintro ⟨hc,hcop⟩
          have hc0 : c≠0 := by intro hz; subst c; exact hq1 (by simpa using hcop)
          exact ⟨⟨by omega,by omega⟩,hcop⟩
        · rintro ⟨⟨hc1,hcq⟩,hcop⟩
          have hcne : c≠q := by intro heq; subst c; exact hq1 (by simpa using hcop)
          exact ⟨by omega,hcop⟩
      rw [hset]
  have hdouble : (∑ q ∈ Icc 1 Q, ∑ c ∈ (Icc 1 q).filter (fun c => Nat.Coprime c q),
      ‖trig I b ((c:ℝ)/q)‖^2) = ∑ p ∈ fareyPts Q, ‖trig I b ((p.2:ℝ)/p.1)‖^2 := by
    unfold fareyPts
    rw [sum_filter,sum_product]
    apply sum_congr rfl
    intro q hq
    rw [← sum_filter]
    have hset : (Icc 1 Q).filter (fun c => c≤q ∧ Nat.Coprime c q) = (Icc 1 q).filter (fun c => Nat.Coprime c q) := by
      ext c
      simp only [mem_filter,mem_Icc]
      have hh := mem_Icc.mp hq
      omega
    rw [hset]
  have hh := (sum_le_sum hrow).trans (le_of_eq hdouble)
  refine hh.trans ?_
  have hb := arith_large_sieve hQ M N b
  simpa [I,b,Complex.norm_conj] using hb

/-! ### Vacuity instances -/

/-- `Spaced` is not vacuous: `0` and `1/2` are `1/2`-spaced modulo 1. -/
example : Spaced ({0, 1} : Finset ℕ) (fun r => (r : ℝ) / 2) (1 / 2) := by
  have key : ∀ y : ℝ, |y| = 1 / 2 → ∀ m : ℤ, (1 / 2 : ℝ) ≤ |y - m| := by
    intro y hy m
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hy with rfl | rfl <;>
    rcases lt_trichotomy m 0 with h | h | h
    all_goals first
      | (have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
         rw [le_abs]; first | (left; linarith) | (right; linarith))
      | (subst h; norm_num [abs_of_pos, abs_of_neg])
      | (have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
         rw [le_abs]; first | (left; linarith) | (right; linarith))
  intro r hr s hs hrs m
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · exact absurd rfl hrs
  · exact key (((0 : ℕ) : ℝ) / 2 - ((1 : ℕ) : ℝ) / 2) (by norm_num [abs_of_neg]) m
  · exact key (((1 : ℕ) : ℝ) / 2 - ((0 : ℕ) : ℝ) / 2) (by norm_num) m
  · exact absurd rfl hrs

/-- `fareyPts 2` holds `1/1` and `1/2`. -/
example : fareyPts 2 = {(1, 1), (2, 1)} := by decide

end LeanLab.ExceptionalSet.Decomp1524a
