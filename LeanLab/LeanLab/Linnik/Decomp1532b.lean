/-
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File b: the major arcs of Section 1, pp. 127-132, and Lemmas 6, 9, 10 of Section 2,
pp. 134-137.
* `majorArcs N P`: the union of the arcs `|α - a/q| ≤ 1/(qQ)`, `Q = N/P`, `1 ≤ q ≤ P`,
  `(a, q) = 1`, inside `[0, 1]`, display (2) p. 127. The arc of `a/q = 0/1` and `1/1` together
  are the arc `M(1, 1)` of the paper taken mod 1.
* `ramanujanSum q n = c_q(n)`, `singSeries n = Σ_q μ(q)²/φ(q)² c_q(n)`, p. 130 and p. 134.
* `Jn N n = Σ_{m₁ - m₂ = n} 1/(log m₁ log m₂)`, Theorem 3, p. 127.
* `zeroCount χ σ T`, the distinct zeros of `L(s, χ)` with `Re ρ ≥ σ`, `|Im ρ| ≤ T`.
* `excSet b T`, primitive characters of conductor at most `T` whose L-function has a zero with
  `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`, p. 127.
Leaves: disjointness and measure of the major arcs, Dirichlet's theorem, the Gauss sum, the
Ramanujan sum, the singular series, `J(n)`, the geometric sum behind `T(β)`, the multiplicative
large sieve, Gallagher's density estimate for zeros near 1, Page's theorem, Siegel's theorem,
Lemmas 6, 9 and 10.
Assembly: `minor_approx`, every point of `[0, 1]` off the major arcs has an approximation
`a/q` with `P < q ≤ N/P`, the starting point of Lemma 11, p. 137.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Linnik.Decomp1532a
import LeanLab.Linnik.U7204Display4
import LeanLab.Zinoviev1997.TotientTail
import LeanLab.PNTPort.DirichletZF.Siegel

namespace LeanLab.Linnik.Decomp1532b

open Finset MeasureTheory ZMod ArithmeticFunction Filter Asymptotics
open LeanLab.PNTPort.DirichletZF (siegel_zero riemannZeta_real_neg L_lift lift_ne_one lift_sq)
open scoped Topology
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov (sum_moebius_divisors)
open LeanLab.PNTPort.LargeSieve (dist0 norm_e e_add norm_geom_le)
open LeanLab.Linnik.Decomp1532a (pairs dif)
open LeanLab.Linnik.U1412Display53 (eC)

/-- The major arcs `𝔐`, display (2) p. 127, with `Q = N/P`, so `1/(qQ) = P/(qN)`. -/
def majorArcs (N : ℕ) (P : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℕ, a ≤ q ∧ Nat.Coprime a q ∧
    |α - a / q| ≤ P / (q * N)}

/-- The Ramanujan sum `c_q(n) = Σ_{a < q, (a, q) = 1} e(an/q)`. -/
noncomputable def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ range q with Nat.Coprime a q, eC ((a : ℝ) * n / q)

/-- The singular series `𝔖(n) = Σ_{q ≥ 1} μ(q)²/φ(q)² c_q(n)`, p. 130; for g = 2 this is the
`𝔖(n)` of p. 134, with `D/φ(D) = 2`. -/
noncomputable def singSeries (n : ℤ) : ℂ :=
  ∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n

/-- `J(n) = Σ_{1 < m₁, m₂ ≤ N, m₁ - m₂ = n} (log m₁ log m₂)⁻¹`, Theorem 3, p. 127. -/
noncomputable def Jn (N : ℕ) (n : ℤ) : ℝ :=
  ∑ m ∈ Ioc 1 N ×ˢ Ioc 1 N with (m.1 : ℤ) - m.2 = n, 1 / (Real.log m.1 * Real.log m.2)

/-- The distinct zeros `ρ` of `L(s, χ)` with `Re ρ ≥ σ` and `|Im ρ| ≤ T`. -/
noncomputable def zeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- Primitive characters of conductor `q + 1 ≤ T` whose L-function vanishes somewhere in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`, p. 127. -/
def excSet (b T : ℝ) : Set (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) :=
  {x | ((x.1 : ℝ) + 1 ≤ T) ∧ x.2.IsPrimitive ∧
    ∃ ρ : ℂ, x.2.LFunction ρ = 0 ∧ 1 - b / Real.log T ≤ ρ.re ∧ |ρ.im| ≤ T}

/-- LEAF. Unit U-1532. The major arcs are disjoint when `2P² < N`, i.e. `2P < Q`: two arcs about
distinct fractions `a/q`, `a'/q'` with `q, q' ≤ P` do not meet, p. 127, after display (2). -/
theorem majorArcs_disjoint {N : ℕ} {P : ℝ} (hP : 0 < P) (hPN : 2 * P ^ 2 < N)
    {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqP : (q : ℝ) ≤ P) (hqP' : (q' : ℝ) ≤ P)
    (hne : (a : ℝ) / q ≠ a' / q') {α : ℝ}
    (h1 : |α - a / q| ≤ P / (q * N)) (h2 : |α - a' / q'| ≤ P / (q' * N)) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hPN
  have hcross : (a : ℤ) * q' - (a' : ℤ) * q ≠ 0 := by
    intro h
    apply hne
    apply (div_eq_div_iff hq0.ne' hq0'.ne').mpr
    exact_mod_cast (sub_eq_zero.mp h)
  have hint : (1 : ℝ) ≤ |(a : ℝ) * q' - (a' : ℝ) * q| := by
    have h := Int.one_le_abs hcross
    exact_mod_cast h
  have hdist : |(a : ℝ) / q - (a' : ℝ) / q'| ≤ P / (q * N) + P / (q' * N) := by
    calc
      _ = |(α - (a' : ℝ) / q') - (α - (a : ℝ) / q)| := by congr 1; ring
      _ ≤ |α - (a' : ℝ) / q'| + |α - (a : ℝ) / q| := abs_sub _ _
      _ ≤ _ := by linarith
  have heq : (a : ℝ) / q - (a' : ℝ) / q' =
      ((a : ℝ) * q' - (a' : ℝ) * q) / (q * q') := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hq0 hq0')] at hdist
  have hdist' := (div_le_iff₀ (mul_pos hq0 hq0')).mp hdist
  have heq' : (P / ((q : ℝ) * N) + P / ((q' : ℝ) * N)) * (q * q') =
      P * (q + q') / N := by field_simp <;> ring
  rw [heq'] at hdist'
  have hbound := (le_div_iff₀ hN).mp (hint.trans hdist')
  nlinarith

/-- LEAF. Unit U-1532. For `P ≥ 1`, `N ≥ 1` the major arcs have measure at most `4P²/N`,
since there are at most `2 + Σ_{2 ≤ q ≤ P} φ(q)` arcs and the arc at `a/q` has length
`2P/(qN)`, p. 127. -/
theorem volume_majorArcs_le {N : ℕ} {P : ℝ} (hP : 1 ≤ P) (hN : 1 ≤ N) :
    MeasureTheory.volume (majorArcs N P) ≤ ENNReal.ofReal (4 * P ^ 2 / N) := by
  classical
  have hP0 : 0 ≤ P := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let A : ℕ → ℕ → Set ℝ := fun q a =>
    Set.Icc ((a : ℝ) / q - P / (q * N)) ((a : ℝ) / q + P / (q * N))
  have hsub : majorArcs N P ⊆ ⋃ q ∈ Icc 1 ⌊P⌋₊, ⋃ a ∈ range (q + 1), A q a := by
    rintro α ⟨_, q, hq, hqP, a, haq, _, ha⟩
    refine Set.mem_iUnion₂.mpr ⟨q, mem_Icc.mpr ⟨hq, Nat.le_floor hqP⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨a, mem_range.mpr (by omega), ?_⟩
    change _ ≤ α ∧ α ≤ _
    rw [abs_le] at ha
    constructor <;> linarith [ha.1, ha.2]
  have hA : ∀ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ range (q + 1), volume (A q a) ≤
      ENNReal.ofReal (4 * P / N) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have heq : ∀ a, volume (A q a) = ENNReal.ofReal (2 * P / (q * N)) := by
      intro a
      change volume (Set.Icc _ _) = _
      rw [Real.volume_Icc]
      congr 1
      ring
    simp_rw [heq]
    simp only [sum_const, card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos hq0 hN0) hN0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (mul_nonneg hP0 hN0.le)]
  calc
    volume (majorArcs N P) ≤ volume (⋃ q ∈ Icc 1 ⌊P⌋₊, ⋃ a ∈ range (q + 1), A q a) := measure_mono hsub
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, volume (⋃ a ∈ range (q + 1), A q a) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ∑ a ∈ range (q + 1), volume (A q a) :=
      sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Icc 1 ⌊P⌋₊, ENNReal.ofReal (4 * P / N) := sum_le_sum hA
    _ ≤ ENNReal.ofReal (4 * P ^ 2 / N) := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hf := Nat.floor_le hP0
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hN0]
      nlinarith

/-- LEAF. Unit U-1532. Dirichlet's theorem in the form of p. 127, display (2): for
`α ∈ [0, 1]` and real `Q ≥ 1` there are `1 ≤ q ≤ Q` and `0 ≤ a ≤ q`, `(a, q) = 1`, with
`|α - a/q| ≤ 1/(qQ)`. -/
theorem exists_approx {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |α - a / q| ≤ 1 / (q * Q) := by
  have ha0 := hα.1
  have ha1 := hα.2
  have hQ0 : 0 < Q := by linarith
  have hn : 0 < ⌊Q⌋₊ := by have := Nat.le_floor (n := 1) (by simpa using hQ); omega
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hdenQ : (r.den : ℝ) ≤ Q :=
    (show (r.den : ℝ) ≤ ⌊Q⌋₊ by exact_mod_cast hden).trans (Nat.floor_le (by linarith))
  have hbd : |α - (r : ℝ)| ≤ 1 / (r.den * Q) := by
    refine hr.trans (one_div_le_one_div_of_le (mul_pos hd0 hQ0) ?_)
    nlinarith [Nat.lt_floor_add_one Q]
  by_cases hr0 : (r : ℝ) < 0
  · refine ⟨1, 0, by norm_num, by simpa using hQ, by norm_num, by norm_num, ?_⟩
    have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hsmall : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    simp only [Nat.cast_one, Nat.cast_zero, zero_div, sub_zero, one_mul]
    rw [abs_of_nonneg hα.1]
    rw [abs_of_nonneg (by linarith : 0 ≤ α - (r : ℝ))] at hbd
    linarith
  by_cases hr1 : 1 < (r : ℝ)
  · refine ⟨1, 1, by norm_num, by simpa using hQ, by norm_num, by norm_num, ?_⟩
    have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hsmall : 1 / ((r.den : ℝ) * Q) ≤ 1 / Q :=
      one_div_le_one_div_of_le hQ0 (by nlinarith)
    simp only [Nat.cast_one, div_one, one_mul]
    rw [abs_of_nonpos (by linarith : α - 1 ≤ 0)]
    rw [abs_of_nonpos (by linarith : α - (r : ℝ) ≤ 0)] at hbd
    linarith
  have hnum0 : 0 ≤ r.num := Rat.num_nonneg.mpr (by exact_mod_cast (le_of_not_gt hr0))
  have hcast : (r.num.toNat : ℝ) / r.den = r := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum0, Rat.cast_def]
  refine ⟨r.den, r.num.toNat, r.den_pos, hdenQ, ?_, ?_, ?_⟩
  · have : (r.num.toNat : ℝ) / r.den ≤ 1 := by rw [hcast]; exact le_of_not_gt hr1
    have := (div_le_one hd0).mp this
    exact_mod_cast this
  · have he : r.num.toNat = r.num.natAbs := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg hnum0, Int.natCast_natAbs, abs_of_nonneg hnum0]
    rw [he]
    exact r.reduced
  · simpa [hcast] using hbd

/-- ASSEMBLY, CONDITIONAL ON the leaf `exists_approx`. A point of `[0, 1]` off the major arcs,
with `0 < P ≤ N`, has an approximation `a/q` in lowest terms with `P < q ≤ N/P` and
`|α - a/q| ≤ P/(qN)`; this is the start of the proof of Lemma 11, p. 137. -/
theorem minor_approx {N : ℕ} {P : ℝ} (hP : 0 < P) (hPN : P ≤ N) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hM : α ∉ majorArcs N P) :
    ∃ q a : ℕ, P < q ∧ (q : ℝ) ≤ N / P ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |α - a / q| ≤ P / (q * N) := by
  have hN : (0 : ℝ) < N := lt_of_lt_of_le hP hPN
  have hQ : 1 ≤ (N : ℝ) / P := by rw [le_div_iff₀ hP]; linarith
  obtain ⟨q, a, hq1, hqQ, haq, hcop, happ⟩ := exists_approx hα hQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have heq : 1 / (q * ((N : ℝ) / P)) = P / (q * N) := by
    field_simp
  rw [heq] at happ
  refine ⟨q, a, ?_, hqQ, haq, hcop, happ⟩
  by_contra hle
  push Not at hle
  exact hM ⟨hα, q, hq1, hle, a, haq, hcop, happ⟩

/-- LEAF. Unit U-1532. A primitive character `χ` modulo `q` has Gauss sum of absolute value
`√q`, display (6) p. 129 in the case `q = r`. -/
theorem gaussSum_norm_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖∑ a : ZMod q, χ a * eC ((a.val : ℝ) / q)‖ ^ 2 = q := by
  have he : (∑ a : ZMod q, χ a * eC ((a.val : ℝ) / q)) = gaussSum χ ZMod.stdAddChar := by
    unfold gaussSum
    apply sum_congr rfl
    intro a _
    congr 1
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    unfold eC
    congr 1
    push_cast
    ring
  rw [he]
  classical
  have hft : ZMod.dft χ = fun k => χ⁻¹ (-k) * gaussSum χ stdAddChar := by
    ext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hχinv : χ⁻¹.IsPrimitive := by simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hprod : gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = (q : ℂ) * χ (-1) := by
    have h := congr_fun (ZMod.dft_dft χ) (1 : ZMod q)
    rw [hft] at h
    rw [ZMod.dft_mul_const, ZMod.dft_comp_neg] at h
    dsimp only at h
    rw [hχinv.fourierTransform_eq_inv_mul_gaussSum] at h
    simpa [mul_comm] using h
  have hstar : star (gaussSum χ stdAddChar) = χ⁻¹ (-1) * gaussSum χ⁻¹ stdAddChar := by
    rw [star_gaussSum_eq]
    simp only [gaussSum, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.neg (ZMod q))
    intro a
    simp only [Equiv.neg_apply, AddChar.inv_apply]
    rw [← mul_assoc, ← map_mul, neg_one_mul, neg_neg]
  have heq : gaussSum χ stdAddChar * star (gaussSum χ stdAddChar) = (q : ℂ) := by
    calc
      _ = (gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar) * χ⁻¹ (-1) := by rw [hstar]; ring
      _ = (q : ℂ) * (χ⁻¹ (-1) * χ (-1)) := by rw [hprod]; ring
      _ = q := by rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply isUnit_neg_one, mul_one]
  have hn := congrArg Complex.re heq
  have hn' : Complex.normSq (gaussSum χ stdAddChar) = (q : ℝ) := by
    simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.natCast_re] using hn
  rwa [Complex.normSq_eq_norm_sq] at hn'

/-- The divisor formula for the Ramanujan sum at an integer argument, p.130.
Adapted from the lab natural argument proof in PNTPort.Vinogradov.SingSeries. -/
theorem ramanujanSum_eq_divisor_sum {q : ℕ} (hq : 1 ≤ q) (n : ℤ) :
    ramanujanSum q n = ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
      (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℤ) := by
  have heq : ramanujanSum q n =
      ∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), LeanLab.PNTPort.LargeSieve.e (n * r / q) := by
    unfold ramanujanSum
    apply sum_congr rfl
    intro a ha
    rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
    congr 1
    ring
  rw [heq, Nat.gcd_comm q n.natAbs]

  rw [sum_filter]
  have step1 : ∀ r ∈ range q, (if Nat.Coprime r q then LeanLab.PNTPort.LargeSieve.e (n * r / q) else 0) =
      ∑ d ∈ (Nat.gcd r q).divisors, (μ d : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * r / q) := by
    intro r _
    rw [← sum_mul, sum_moebius_divisors]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl step1]
  rw [sum_comm' (t' := q.divisors) (s' := fun d => (range q).filter (fun r => d ∣ r))]
  · have step2 : ∀ d ∈ q.divisors, ∑ r ∈ (range q).filter (fun r => d ∣ r), (μ d : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * r / q)
        = (μ d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ n then ((q / d : ℕ) : ℂ) else 0) := by
      intro d hd
      have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdq) hd0
      rw [← mul_sum, ← LeanLab.PNTPort.LargeSieve.sum_e_mul_div n hqd]
      congr 1
      refine sum_nbij' (fun r => r / d) (fun s => d * s) ?_ ?_ ?_ ?_ ?_
      · intro r hr
        rw [mem_filter, mem_range] at hr
        rw [mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [mem_range] at hs
        rw [mem_filter, mem_range]
        refine ⟨?_, dvd_mul_right d s⟩
        have := Nat.mul_lt_mul_of_pos_left hs hd0
        rwa [Nat.mul_div_cancel' hdq] at this
      · intro r hr
        rw [mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _; exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        rw [mem_filter] at hr
        obtain ⟨s, rfl⟩ := hr.2
        rw [Nat.mul_div_cancel_left s hd0, Nat.cast_div hdq (by exact_mod_cast hd0.ne')]
        congr 1
        push_cast
        field_simp
    rw [sum_congr rfl step2]
    -- reindex d ↦ q / d onto the divisors of gcd(n, q)
    rw [← sum_filter_add_sum_filter_not q.divisors (fun d => ((q / d : ℕ) : ℤ) ∣ n)]
    rw [sum_eq_zero (s := q.divisors.filter (fun d => ¬ ((q / d : ℕ) : ℤ) ∣ n))
      (fun d hd => by rw [mem_filter] at hd; rw [if_neg hd.2, mul_zero]), add_zero]
    refine sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [Nat.mem_divisors]
      refine ⟨Nat.dvd_gcd (Int.natCast_dvd.mp hd.2) (Nat.div_dvd_of_dvd hd.1.1), ?_⟩
      exact (Nat.gcd_pos_of_pos_right n.natAbs (by omega)).ne'
    · intro e he
      rw [Nat.mem_divisors] at he
      have heq : e ∣ q := (Nat.dvd_gcd_iff.1 he.1).2
      have hen : e ∣ n.natAbs := (Nat.dvd_gcd_iff.1 he.1).1
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos heq (by omega)
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_of_dvd heq, by omega⟩, ?_⟩
      rw [Nat.div_div_self heq (by omega)]; exact Int.natCast_dvd.mpr hen
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 (by omega)
    · intro e he
      rw [Nat.mem_divisors] at he
      exact Nat.div_div_self (Nat.dvd_gcd_iff.1 he.1).2 (by omega)
    · intro d hd
      rw [mem_filter, Nat.mem_divisors] at hd
      rw [if_pos hd.2, Nat.div_div_self hd.1.1 (by omega)]
      ring
  · intro r d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, ne_eq,
      Nat.gcd_eq_zero_iff]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, by omega⟩


/-- LEAF. Unit U-1532. For squarefree `q`, `c_q(n) = μ(q/(q, n)) φ((q, n))`, the fact used on
p. 130 before display (11). -/
theorem ramanujanSum_squarefree {q : ℕ} (hq : Squarefree q) (n : ℤ) :
    ramanujanSum q n =
      ((ArithmeticFunction.moebius (q / Nat.gcd q n.natAbs) : ℤ) : ℂ) *
        ((Nat.gcd q n.natAbs).totient : ℂ) := by
  classical
  rw [ramanujanSum_eq_divisor_sum (Nat.pos_of_ne_zero hq.ne_zero) n]
  generalize hgdef : Nat.gcd q n.natAbs = g
  have hg : g ∣ q := hgdef ▸ Nat.gcd_dvd_left q n.natAbs
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hq.ne_zero hg
  have hcop : Nat.Coprime (q / g) g := Nat.coprime_of_squarefree_mul (by rwa [Nat.div_mul_cancel hg])
  have hsum : (∑ d ∈ g.divisors, (d : ℂ) * (moebius (g / d) : ℤ)) = (g.totient : ℂ) := by
    have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℂ) (f := fun n => (n.totient : ℂ))
      (g := fun n => (n : ℂ))).mp (by intro n hn; exact_mod_cast Nat.sum_totient n) g (Nat.pos_of_ne_zero hg0)
    rw [Nat.sum_divisorsAntidiagonal' (fun a b => (moebius a : ℂ) * (b : ℂ))] at h
    simpa only [mul_comm] using h
  calc
    _ = ∑ d ∈ g.divisors, (moebius (q / g) : ℂ) * ((d : ℂ) * (moebius (g / d) : ℂ)) := by
      apply sum_congr rfl
      intro d hd
      have hdg := Nat.dvd_of_mem_divisors hd
      have heq : q / d = (q / g) * (g / d) := by rw [← Nat.mul_div_assoc _ hdg, Nat.div_mul_cancel hg]
      rw [heq, isMultiplicative_moebius.map_mul_of_coprime (hcop.of_dvd_right (Nat.div_dvd_of_dvd hdg))]
      push_cast
      ring
    _ = _ := by rw [← mul_sum, hsum]

/-- The literal numerator n printed on p.130 fails at q = 2 and n = 1. -/
theorem printed_ramanujan_formula_two_one_ne : ramanujanSum 2 1 ≠
    ((ArithmeticFunction.moebius (1 / Nat.gcd 2 (1 : ℤ).natAbs) : ℤ) : ℂ) *
      ((Nat.gcd 2 (1 : ℤ).natAbs).totient : ℂ) := by
  rw [ramanujanSum_squarefree Nat.squarefree_two]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- LEAF. Unit U-1532. For `n ≠ 0` the series `Σ_q μ(q)²/φ(q)² c_q(n)` defining `𝔖(n)`
converges absolutely, p. 130. -/
theorem summable_singSeries {n : ℤ} (hn : n ≠ 0) :
    Summable fun q : ℕ =>
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n := by
  classical
  let B : ℝ := ∑ d ∈ n.natAbs.divisors, (d : ℝ)
  have hB : 0 ≤ B := sum_nonneg fun d hd => Nat.cast_nonneg d
  have hnn : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hR (q : ℕ) : ‖ramanujanSum q n‖ ≤ B := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simpa [ramanujanSum] using hB
    rw [ramanujanSum_eq_divisor_sum hq n]
    calc
      _ ≤ ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
          ‖(d : ℂ) * (moebius (q / d) : ℤ)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ (Nat.gcd q n.natAbs).divisors, (d : ℝ) := by
        apply sum_le_sum
        intro d hd
        rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
        have hmu := ArithmeticFunction.abs_moebius_le_one (n := q / d)
        have hmu' : |((moebius (q / d) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hmu
        exact mul_le_of_le_one_right (Nat.cast_nonneg d) hmu'
      _ ≤ B := sum_le_sum_of_subset_of_nonneg
        (Nat.divisors_subset_of_dvd hnn (Nat.gcd_dvd_right q n.natAbs)) (by intros; positivity)
  have hs : Summable (fun q : ℕ => (7 * B) * (q : ℝ) ^ (-(7 : ℝ) / 4)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(7 : ℝ) / 4 < -1)).mul_left _
  apply hs.of_norm_bounded
  intro q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hmu : ‖((moebius q : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
    have h : ‖((moebius q : ℤ) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_intCast] using
        (show |((moebius q : ℤ) : ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q))
    nlinarith [norm_nonneg (((moebius q : ℤ) : ℂ))]
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (1 / (q.totient : ℝ) ^ 2) * B :=
      mul_le_mul (div_le_div_of_nonneg_right hmu (by positivity)) (hR q) (norm_nonneg _) (by positivity)
    _ ≤ (7 * (q : ℝ) ^ (-(7 : ℝ) / 4)) * B :=
      mul_le_mul_of_nonneg_right (LeanLab.Zinoviev1997.inv_totient_sq_seven q hq) hB
    _ = _ := by ring

/-- LEAF. Unit U-1532. For g = 2 the singular series vanishes at odd `n`: the Euler factor at
`p = 2` is `1 + c_2(n) = 0`; p. 134, the remark that only `n` with `D ∣ n` occur. -/
theorem singSeries_odd {n : ℤ} (hn : Odd n) : singSeries n = 0 := by
  classical
  let f : ℕ → ℂ := fun q => (μ q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 * ramanujanSum q n
  have hn0 : n ≠ 0 := by intro h; subst n; norm_num at hn
  have hs : Summable f := summable_singSeries hn0
  have hn2 : Nat.Coprime 2 n.natAbs := Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hn)
  have hzero {q : ℕ} (hq : ¬ Squarefree q) : f q = 0 := by
    simp [f, moebius_eq_zero_of_not_squarefree hq]
  have hfour (q : ℕ) : f (4 * q) = 0 := by
    apply hzero
    intro hsq
    have hdiv : 2 * 2 ∣ 4 * q := by omega
    exact (by norm_num : ¬IsUnit (2 : ℕ)) (hsq 2 hdiv)
  have hpair (r : ℕ) (hr : Odd r) : f (2 * r) = -f r := by
    by_cases hsq : Squarefree r
    · have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
      have hsq2 : Squarefree (2 * r) := (Nat.squarefree_mul hcop).mpr ⟨Nat.squarefree_two, hsq⟩
      have hg : Nat.gcd (2 * r) n.natAbs = Nat.gcd r n.natAbs := hn2.gcd_mul_left_cancel r
      have hcopdiv : Nat.Coprime 2 (r / Nat.gcd r n.natAbs) :=
        hcop.of_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r n.natAbs))
      have hdiv : 2 * r / Nat.gcd r n.natAbs = 2 * (r / Nat.gcd r n.natAbs) :=
        Nat.mul_div_assoc 2 (Nat.gcd_dvd_left r n.natAbs)
      have hm1 : (μ r : ℂ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq
      have hm2 : (μ (2 * r) : ℂ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsq2
      dsimp [f]
      rw [ramanujanSum_squarefree hsq2 n, ramanujanSum_squarefree hsq n, hg,
        Nat.totient_mul hcop, hdiv, isMultiplicative_moebius.map_mul_of_coprime hcopdiv,
        hm2, hm1]
      norm_num [moebius_apply_prime Nat.prime_two]
    · rw [hzero hsq, hzero (fun h => hsq h.of_mul_right), neg_zero]
  have he : Summable (fun k => f (2 * k)) := hs.comp_injective (i := fun k : ℕ => 2 * k) (by
    intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun k => f (2 * k + 1)) := hs.comp_injective (i := fun k : ℕ => 2 * k + 1) (by
    intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hee : Summable (fun k => f (2 * (2 * k))) := hs.comp_injective (i := fun k : ℕ => 2 * (2 * k)) (by
    intro a b h; change 2 * (2 * a) = 2 * (2 * b) at h; omega)
  have heo : Summable (fun k => f (2 * (2 * k + 1))) := hs.comp_injective (i := fun k : ℕ => 2 * (2 * k + 1)) (by
    intro a b h; change 2 * (2 * a + 1) = 2 * (2 * b + 1) at h; omega)
  have hsplit := tsum_even_add_odd (f := f) he ho
  have hsplit2 := tsum_even_add_odd (f := fun k => f (2 * k)) hee heo
  have heq0 : (∑' k, f (2 * (2 * k))) = 0 := by simp [show ∀ k, 2 * (2 * k) = 4 * k by intro k; omega, hfour]
  have heqneg : (∑' k, f (2 * (2 * k + 1))) = -(∑' k, f (2 * k + 1)) := by
    simp_rw [hpair (2 * _ + 1) (by exact ⟨_, rfl⟩)]
    exact tsum_neg
  change (∑' q, f q) = 0
  rw [heq0, heqneg, zero_add] at hsplit2
  rw [hsplit2.symm] at hsplit
  simpa using hsplit.symm

/-- LEAF. Unit U-1532. Lemma 6, display (6) p. 134, for g = 2 where `D/φ(D) = 2`: for
`k ≥ 2` and `N ≥ N_k`, `Σ_{n ≠ 0} r_{k,k}(n) 𝔖(n) = 2 L^{2k} (1 + O(log² k / k))`. -/
theorem lemma6 : ∃ C : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
    ‖∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0, singSeries (dif x) -
        2 * ((Nat.log 2 N : ℕ) : ℂ) ^ (2 * k)‖ ≤
      C * (Real.log k ^ 2 / k) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  sorry

/-- The diagonal identity for J of zero, p.127 and p.130. -/
theorem Jn_zero_eq_sum (N : ℕ) : Jn N 0 = ∑ a ∈ Ioc 1 N, 1 / Real.log a ^ 2 := by
  classical
  unfold Jn
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro a ha
  rw [sum_eq_single_of_mem a ha]
  · simp [pow_two]
  · intro b hb hba
    have hne : (a : ℤ) - b ≠ 0 := by omega
    simp [hne]


/-- LEAF. Unit U-1532. `J(n) ≤ J(0)` for every `n`, by Cauchy-Schwarz; p. 130, the line
`J(n) ≤ J(0) ∼ N/log² N`. -/
theorem Jn_le_J0 (N : ℕ) (n : ℤ) : Jn N n ≤ Jn N 0 := by
  classical
  let T := (Ioc 1 N ×ˢ Ioc 1 N).filter (fun m => (m.1 : ℤ) - m.2 = n)
  let f : ℕ → ℝ := fun a => 1 / Real.log a
  have hJ0 : Jn N 0 = ∑ a ∈ Ioc 1 N, f a ^ 2 := by
    unfold Jn
    rw [sum_filter, sum_product]
    apply sum_congr rfl
    intro a ha
    rw [sum_eq_single_of_mem a ha]
    · simp [f, pow_two]
    · intro b hb hba
      have hne : (a : ℤ) - b ≠ 0 := by omega
      simp [hne]
  have hfst : Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Prod.ext hab
    omega
  have hsnd : Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Prod.ext _ hab
    omega
  have hproj : ∀ (p : ℕ × ℕ → ℕ), Set.InjOn p (T : Set (ℕ × ℕ)) →
      (∀ a ∈ T, p a ∈ Ioc 1 N) → (∑ a ∈ T, f (p a) ^ 2) ≤ ∑ a ∈ Ioc 1 N, f a ^ 2 := by
    intro p hinj hmem
    apply sum_le_sum_of_injOn p hinj
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact hmem b hb
    · intro a ha; exact le_rfl
    · intro a ha _; positivity
  have hleft := hproj Prod.fst hfst (fun a ha => (mem_product.mp (mem_filter.mp ha).1).1)
  have hright := hproj Prod.snd hsnd (fun a ha => (mem_product.mp (mem_filter.mp ha).1).2)
  have hterm : Jn N n ≤ (∑ a ∈ T, (f a.1 ^ 2 + f a.2 ^ 2)) / 2 := by
    unfold Jn
    change (∑ a ∈ T, 1 / (Real.log a.1 * Real.log a.2)) ≤ _
    rw [sum_div]
    apply sum_le_sum
    intro a ha
    have hsq := sq_nonneg (f a.1 - f a.2)
    have heq : 1 / (Real.log a.1 * Real.log a.2) = f a.1 * f a.2 := by simp [f, mul_comm]
    rw [heq]
    nlinarith
  rw [hJ0]
  rw [sum_add_distrib] at hterm
  linarith

/-- The lower estimate underlying J of zero asymptotic, p.130. -/
theorem J0_lower {N : ℕ} (hN : 2 ≤ N) : ((N : ℝ) - 1) / Real.log N ^ 2 ≤ Jn N 0 := by
  rw [Jn_zero_eq_sum]
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have heq : ((N : ℝ) - 1) / Real.log N ^ 2 = ∑ a ∈ Ioc 1 N, 1 / Real.log N ^ 2 := by
    simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    rw [Nat.cast_sub hN1, Nat.cast_one]
    ring
  rw [heq]
  apply sum_le_sum
  intro a ha
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
  have haN : (a : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp ha).2
  have hapos : 0 < Real.log a := Real.log_pos ha1
  have halog : Real.log a ≤ Real.log N := Real.log_le_log (by positivity) haN
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hapos.le halog 2)

/-- LEAF. Unit U-1532. `J(0) = Σ_{1 < m ≤ N} 1/log² m ∼ N/log² N`, p. 130. -/
theorem J0_asymp :
    Filter.Tendsto (fun N : ℕ => Jn N 0 / ((N : ℝ) / Real.log N ^ 2)) Filter.atTop (nhds 1) := by
  let F : ℕ → ℝ := fun n => (n : ℝ) / Real.log n ^ 2
  let g : ℕ → ℝ := fun n => 1 / Real.log (n + 1) ^ 2
  let d : ℕ → ℝ := fun n => F (n + 1) - F n
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (nhds 0) := hlog.inv_tendsto_atTop
  have hdiff := Real.tendsto_log_nat_add_one_sub_log
  let T : ℕ → ℝ := fun n => (n : ℝ) * (Real.log (n + 1) - Real.log n) *
    (Real.log (n + 1) + Real.log n) / Real.log n ^ 2
  have hb : Tendsto (fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log n ^ 2 + 2 / Real.log n)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hdiff.mul (hi.pow 2)).add (hi.const_mul 2)
  have hT : Tendsto T atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log n ^ 2 + 2 / Real.log n)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      dsimp [T]
      exact div_nonneg (mul_nonneg (mul_nonneg hn0.le (sub_nonneg.mpr hmono)) (by linarith)) (sq_nonneg _)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      have hmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
      have hbd : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (n : ℝ) + 1) hn0)
        rw [Real.log_div (by positivity) hn0.ne', show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at h
        have h' := (le_div_iff₀ hn0).mp h
        nlinarith
      dsimp [T]
      calc
        _ ≤ (Real.log ((n : ℝ) + 1) + Real.log n) / Real.log n ^ 2 := by
          exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (by linarith) hbd) (by positivity)
        _ = _ := by field_simp; ring
    · exact hb
  have hd : Tendsto (fun n => d n / g n) atTop (nhds 1) := by
    have hh : Tendsto (fun n => 1 - T n) atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hT
    norm_num only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
    have hl1 : Real.log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    dsimp [d, g, F, T]
    push_cast
    field_simp
    <;> ring
  have herr : (fun n => d n - g n) =o[atTop] g := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · have hh : Tendsto (fun n => d n / g n - 1) atTop (nhds (1 - 1)) := hd.sub tendsto_const_nhds
      norm_num only [sub_self] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hg : g n ≠ 0 := by
        dsimp [g]
        exact one_div_ne_zero (pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne')
      dsimp [d]
      field_simp
      <;> ring
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hg : g n ≠ 0 := by
        dsimp [g]
        exact one_div_ne_zero (pow_ne_zero 2 (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne')
      exact fun h => (hg h).elim
  have hsum (N : ℕ) : (∑ i ∈ range N, g i) = Jn N 0 := by
    rw [Jn_zero_eq_sum]
    have hshift : (∑ i ∈ range N, g i) = ∑ a ∈ Ico 1 (N + 1), 1 / Real.log a ^ 2 := by
      simpa only [g, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm] using
        (sum_Ico_eq_sum_range (fun a : ℕ => 1 / Real.log a ^ 2) 1 (N + 1)).symm
    rw [hshift]
    by_cases hN : N = 0
    · subst N; simp
    have hset : Ico 1 (N + 1) = insert 1 (Ioc 1 N) := by ext a; simp; omega
    rw [hset, sum_insert (by simp)]
    simp
  have hdiv0 : Tendsto (fun n : ℕ => Real.log n ^ 2 / ((n : ℝ) - 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_mul, sub_eq_add_neg] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hdivpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log n ^ 2 / ((n : ℝ) - 1) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hbig : Tendsto (fun n : ℕ => ((n : ℝ) - 1) / Real.log n ^ 2) atTop atTop := by
    have hh := (tendsto_nhdsWithin_iff.mpr ⟨hdiv0, hdivpos⟩).inv_tendsto_nhdsGT_zero
    change Tendsto (fun n : ℕ => (Real.log n ^ 2 / ((n : ℝ) - 1))⁻¹) atTop atTop at hh
    simpa only [inv_div] using hh
  have hsumtop : Tendsto (fun N => ∑ i ∈ range N, g i) atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hbig
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [hsum]
    exact J0_lower hN
  have hsmall := (herr.sum_range (by intro n; dsimp [g]; positivity) hsumtop).tendsto_div_nhds_zero
  have hratio : Tendsto (fun N => F N / Jn N 0) atTop (nhds 1) := by
    have hh : Tendsto (fun N => (∑ i ∈ range N, (d i - g i)) / (∑ i ∈ range N, g i) + 1) atTop (nhds (0 + 1)) := hsmall.add tendsto_const_nhds
    norm_num only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [sum_sub_distrib, show (∑ i ∈ range N, d i) = F N - F 0 from sum_range_sub F N, hsum] 
    have hJ : Jn N 0 ≠ 0 := by
      have h := J0_lower hN
      have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
      have hl : 0 < Real.log (N : ℝ) := Real.log_pos hN1
      exact ne_of_gt (lt_of_lt_of_le (by positivity) h)
    have hf0 : F 0 = 0 := by simp [F]
    rw [hf0, sub_zero]
    field_simp
    <;> ring
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [F] using hinv

/-- LEAF. Unit U-1532. The geometric sum bound `|Σ_{m ≤ x} e(mβ)| ≤ 1/(2‖β‖)` for `β` not an
integer, `‖β‖` the distance to the nearest integer; p. 130, the estimate of `T(β)`. -/
theorem norm_geom_sum_le (x : ℕ) {β : ℝ} (hβ : Int.fract β ≠ 0) :
    ‖∑ m ∈ Icc 1 x, eC (m * β)‖ ≤ 1 / (2 * min (Int.fract β) (1 - Int.fract β)) := by
  simp_rw [← LeanLab.Linnik.U1434Lemma21.e_eq_eC]
  have hd : dist0 β = min (Int.fract β) (1 - Int.fract β) := abs_sub_round_eq_min β
  have hp : 0 < dist0 β := by
    rw [hd, lt_min_iff]
    exact ⟨lt_of_le_of_ne (Int.fract_nonneg β) (Ne.symm hβ), sub_pos.mpr (Int.fract_lt_one β)⟩
  have heq : (∑ m ∈ Icc 1 x, LeanLab.PNTPort.LargeSieve.e (m * β)) = LeanLab.PNTPort.LargeSieve.e β * ∑ m ∈ range x, LeanLab.PNTPort.LargeSieve.e (m * β) := by
    rw [show Icc 1 x = Ico 1 (x + 1) by ext k; simp]
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_sum]
    apply sum_congr rfl
    intro m _
    rw [← e_add]
    congr 1
    push_cast
    ring
  rw [heq, norm_mul, norm_e, one_mul, ← hd]
  exact norm_geom_le x hp

/-- The weaker lab coefficient alone does not imply the sharp coefficient on p.131. -/
theorem weaker_large_sieve_constant_insufficient (N Q : ℕ) (hQ : 0 < Q) :
    ∃ B : ℝ, B ≤ (N : ℝ) + 2 * (Q : ℝ) ^ 2 ∧ (N : ℝ) + (Q : ℝ) ^ 2 < B := by
  refine ⟨(N : ℝ) + 2 * (Q : ℝ) ^ 2, le_rfl, ?_⟩
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := lt_add_of_pos_right ((N : ℝ) + (Q : ℝ) ^ 2) (sq_pos_of_pos hq)
  convert h using 1 <;> ring

/-- The modulus one case of the large sieve input on p.131, by Cauchy Schwarz. -/
theorem large_sieve_level_one (a : ℕ → ℂ) (M N : ℕ) :
    ∑ q ∈ Icc (1 : ℕ) 1, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + 1) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  have hchars : (univ : Finset (DirichletCharacter ℂ 1)) = {1} := by
    ext χ
    simp only [mem_univ, mem_singleton, true_iff]
    exact DirichletCharacter.level_one χ
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  simp only [Icc_self, sum_singleton, Nat.cast_one, Nat.totient_one, div_one, one_mul]
  rw [hchars]
  simp only [filter_singleton, DirichletCharacter.isPrimitive_one_level_one, ite_true, sum_singleton,
    hone, mul_one]
  have hnorm : ‖∑ n ∈ Ioc M (M + N), a n‖ ^ 2 ≤ (∑ n ∈ Ioc M (M + N), ‖a n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have hc := sq_sum_le_card_mul_sum_sq (s := Ioc M (M + N)) (f := fun n => ‖a n‖)
  have hc' : (∑ n ∈ Ioc M (M + N), ‖a n‖) ^ 2 ≤
      (N : ℝ) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by simpa using hc
  exact (hnorm.trans hc').trans (mul_le_mul_of_nonneg_right (by linarith) (sum_nonneg fun _ _ => sq_nonneg _))

/-- LEAF. Unit U-1532. The multiplicative large sieve over primitive characters,
`Σ_{q ≤ Q} q/φ(q) Σ*_χ |Σ_{M < n ≤ M+N} a_n χ(n)|² ≤ (N + Q²) Σ |a_n|²`, the input behind the
bound for `E` in display (14) p. 131 and behind the density estimate below. -/
theorem large_sieve (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  -- LEAF. External source: Montgomery 1971, Topics in multiplicative number theory. The lab constant N plus 2Q squared is too weak.
  sorry

/-- LEAF. Unit U-1532. Gallagher's density estimate for zeros near `σ = 1`: for `T ≥ 2` and
`1/2 ≤ σ ≤ 1`, the zeros with `Re ρ ≥ σ`, `|Im ρ| ≤ T` of all `L(s, χ)`, `χ` primitive of
conductor at most `T`, number at most `C T^{c(1-σ)}`; the input to display (14), p. 131, by the
method of §7 of the 1970 large sieve density paper. -/
theorem gallagher_density : ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  classical
  -- LEAF. External sources: Gallagher 1970, Inventiones 11 pp.329 to 339; Montgomery and Vaughan 1975, Section 7.
  sorry

/-- LEAF. Unit U-1532. Page's theorem, p. 127: there is `b > 0` such that for every `T ≥ 2` at
most one primitive character of conductor at most `T` has an L-function with a zero in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`. -/
theorem page_subsingleton : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → (excSet b T).Subsingleton := by
  -- LEAF. External source: Davenport 1967, Multiplicative number theory, Chapters 13 and 14.
  sorry

/-- LEAF. Unit U-1532. The exceptional zero is real and its character is real, p. 127: for
small `b > 0`, any zero in `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T` of `L(s, χ)`, `χ` primitive of
conductor at most `T`, has `Im ρ = 0`, and `χ² = 1`. -/
theorem page_real : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    x.2 ^ 2 = 1 ∧ ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      ρ.im = 0 := by
  -- LEAF. External source: Davenport 1967, Multiplicative number theory, Chapters 13 and 14.
  sorry

/-- LEAF. Unit U-1532. Siegel's theorem, p. 127: for each `ε > 0` there is `c > 0` such that a
real zero `β` of `L(s, χ)`, `χ` real primitive of conductor `r`, has `1 - β ≥ c r^{-ε}`. -/
theorem siegel : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ (q + 1),
    χ.IsPrimitive → χ ^ 2 = 1 → ∀ β : ℝ, χ.LFunction β = 0 →
      β ≤ 1 - c * ((q : ℝ) + 1) ^ (-ε) := by
  intro ε hε
  obtain ⟨cs, hcs, hs⟩ := siegel_zero ε hε
  let c := min (cs * (8 : ℝ) ^ (-ε)) (1 / 2)
  have hc : 0 < c := lt_min (mul_pos hcs (Real.rpow_pos_of_pos (by norm_num) _)) (by norm_num)
  refine ⟨c, hc, fun q χ hprim h2 β hz => ?_⟩
  by_cases hχ : χ = 1
  · have hlev : q + 1 = 1 := by
      have h := hprim
      rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at h
      exact h.symm
    have hq : q = 0 := by omega
    subst q
    have hzeta : riemannZeta (β : ℂ) = 0 := by rwa [DirichletCharacter.LFunction_modOne_eq] at hz
    have hβ : β ≤ 0 := by
      by_contra hh
      have hb0 : 0 < β := by linarith
      by_cases hb1 : 1 ≤ β
      · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hb1) hzeta
      · have hh := (riemannZeta_real_neg hb0 (by linarith)).2
        rw [hzeta] at hh
        norm_num at hh
    have hc2 : c ≤ 1 / 2 := min_le_right _ _
    norm_num
    linarith
  · have hb1 : β ≤ 1 := by
      by_contra hh
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz
    let M := 8 * (q + 1)
    have hM8 : 8 ≤ M := by dsimp [M]; omega
    haveI : NeZero M := ⟨by omega⟩
    have hd : q + 1 ∣ M := by exact ⟨8, by dsimp [M]; ring⟩
    have hz' : (DirichletCharacter.changeLevel hd χ).LFunction β = 0 := by
      rw [L_lift hd hχ, hz, zero_mul]
    have hbound := hs M hM8 (DirichletCharacter.changeLevel hd χ) (lift_ne_one hd hχ) (lift_sq hd h2) β hb1 hz'
    have hMr : (M : ℝ) = 8 * ((q : ℝ) + 1) := by dsimp [M]; push_cast; ring
    rw [hMr, Real.mul_rpow (by norm_num) (by positivity)] at hbound
    have hc' : c * ((q : ℝ) + 1) ^ (-ε) ≤ cs * ((8 : ℝ) ^ (-ε) * ((q : ℝ) + 1) ^ (-ε)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) _)
    linarith

/-- LEAF. Unit U-1532. Lemma 9, p. 136: the conductor `r` of a real primitive character is
`r₀`, `4r₀` or `8r₀` with `r₀` odd and squarefree. -/
theorem lemma9 {r : ℕ} (hr : 0 < r) (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) :
    ∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀) := by
  -- LEAF. External sources: Page 1935, Proc. London Math. Soc. 39 pp.116 to 141; Suetuna 1926, Tohoku Math. J.27 pp.248 to 257.
  sorry

/-- LEAF. Unit U-1532. Lemma 10, display (8) p. 136: for `1 ≤ k ≤ N` and `r` of the form (7)
with `1 < r ≤ N`, `Σ_{n ≠ 0} r_{k,k}(n) |n|/φ(|n|) · r φ((r, n))/φ(r)² ≤ C L^{2k}/(log r)^{1/3}`
with an absolute `C`. -/
theorem lemma10 : ∃ C : ℝ, ∀ k N r : ℕ, 1 ≤ k → k ≤ N → 1 < r → r ≤ N →
    (∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀)) →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log r ^ (1 / 3 : ℝ) := by
  sorry

end LeanLab.Linnik.Decomp1532b
