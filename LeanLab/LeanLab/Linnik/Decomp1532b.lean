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
Proof additions by Codex task189 on 2026-10-30. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Linnik.Decomp1532a
import LeanLab.Linnik.U7204Display4
import LeanLab.Zinoviev1997.TotientTail
import LeanLab.PNTPort.DirichletZF.Siegel
import LeanLab.Romanov.Decomp134
import LeanLab.PNTPort.DirichletZF.Landau
import LeanLab.PNTPort.StrongPNT.StrongPNT
import LeanLab.Romanov.TotientWeights134
import LeanLab.Linnik.Decomp1537a

namespace LeanLab.Linnik.Decomp1532b

open LeanLab.PNTPort.DirichletZF

open Finset MeasureTheory ZMod ArithmeticFunction Filter Asymptotics
open LeanLab.PNTPort.DirichletZF (siegel_zero riemannZeta_real_neg L_lift lift_ne_one lift_sq)
open scoped Topology
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov (sum_moebius_divisors)
open LeanLab.PNTPort.LargeSieve (dist0 norm_e e_add norm_geom_le)
open LeanLab.Linnik.Decomp1532a (pairs dif ordTwo)
open LeanLab.Linnik.U1434Lemma21 (sv)
open LeanLab.Linnik.U1426ChainWire (Gs)
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
  -- LEAF. Gallagher 1975 pp.134 and 135. The uniform truncated singular series tail and the E and R parameter estimate remain.
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

/-- Gallagher p.131 character orthogonality reduces the multiplicative sieve to additive sums. -/
theorem primitive_sieve_le_additive (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), (starRingEnd ℂ) (a n) * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 := by
  classical
  apply sum_le_sum
  intro q hq
  letI : NeZero q := ⟨by have := (mem_Icc.mp hq).1; omega⟩
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  let I : Finset ℤ := (Ioc M (M + N)).map emb
  let az : ℤ → ℂ := fun z => a z.toNat
  have h := LeanLab.PNTPort.LargeSieve.prim_chars_le I az (q := q)
  simpa only [I, az, sum_map, emb, Function.Embedding.coeFn_mk,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast, Int.cast_ofNat] using h

/-- At real part at least one a primitive character has no zeros. This closes the endpoint
of the p.131 density estimate. -/
theorem zeroCount_eq_zero_of_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) : zeroCount χ σ T = 0 := by
  have hne (ρ : ℂ) (hρ : σ ≤ ρ.re) : χ.LFunction ρ ≠ 0 := by
    by_cases hχ : χ = 1
    · have hq : q = 1 := by
        have hh := hp
        rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at hh
        exact hh.symm
      subst q
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re (hσ.trans hρ)
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (hσ.trans hρ)
  have he : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} = ∅ := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, hβ, ht⟩
    exact hne ρ hβ hz
  simp only [zeroCount, he, Set.ncard_empty]

/-- The primitive family count vanishes at the sigma one endpoint of p.131. -/
theorem density_sum_at_one (T : ℝ) :
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ 1 T : ℝ) = 0 := by
  classical
  apply sum_eq_zero
  intro q hq
  apply sum_eq_zero
  intro χ hχ
  rw [zeroCount_eq_zero_of_one_le χ (mem_filter.mp hχ).2 le_rfl, Nat.cast_zero]

/-- LEAF. Montgomery 1971, Topics in multiplicative number theory, sharp additive large sieve.
Gallagher 1975 p.131, the input behind display 14. Only the sharp Fourier sampling bound
remains here. Primitive character orthogonality is proved separately. -/
theorem additive_large_sieve_sharp (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ n ∈ Ioc M (M + N), a n * LeanLab.PNTPort.LargeSieve.e (n * ((c : ℝ) / q))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  sorry

/-- LEAF. Gallagher 1970, A large sieve density estimate near sigma equals one,
Inventiones 11 pp.329 to 339. Montgomery and Vaughan 1975 Section 7.
Gallagher 1975 p.131 display 14.
The endpoint sigma one is proved separately by nonvanishing. -/
theorem gallagher_density_lt_one : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ < 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  classical
  sorry

/-- LEAF. Unit U-1532. The multiplicative large sieve over primitive characters,
`Σ_{q ≤ Q} q/φ(q) Σ*_χ |Σ_{M < n ≤ M+N} a_n χ(n)|² ≤ (N + Q²) Σ |a_n|²`, the input behind the
bound for `E` in display (14) p. 131 and behind the density estimate below. -/
theorem large_sieve (a : ℕ → ℂ) (M N Q : ℕ) :
    ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ Ioc M (M + N), a n * χ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  calc
    _ ≤ _ := primitive_sieve_le_additive a M N Q
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Ioc M (M + N), ‖(starRingEnd ℂ) (a n)‖ ^ 2 :=
      additive_large_sieve_sharp (fun n => (starRingEnd ℂ) (a n)) M N Q
    _ = _ := by simp only [Complex.norm_conj]

/-- LEAF. Unit U-1532. Gallagher's density estimate for zeros near `σ = 1`: for `T ≥ 2` and
`1/2 ≤ σ ≤ 1`, the zeros with `Re ρ ≥ σ`, `|Im ρ| ≤ T` of all `L(s, χ)`, `χ` primitive of
conductor at most `T`, number at most `C T^{c(1-σ)}`; the input to display (14), p. 131, by the
method of §7 of the 1970 large sieve density paper. -/
theorem gallagher_density : ∃ c C : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  classical
  obtain ⟨c, C, hc, hC, h⟩ := gallagher_density_lt_one
  refine ⟨c, C, hc, ?_⟩
  intro T hT σ hσ hσ1
  by_cases hs : σ = 1
  · subst σ
    rw [density_sum_at_one]
    simpa using hC
  · exact h T hT σ hσ (lt_of_le_of_ne hσ1 hs)

/-- The logarithm in the existing zero free region is bounded uniformly in the paper box. -/
theorem log_Bt_le_log_height : ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} [NeZero q] {T t : ℝ},
    2 ≤ T → (q : ℝ) ≤ T → |t| ≤ T → Real.log (Bt q t) ≤ K * Real.log T := by
  let A := Real.log (6 * Z)
  let K := A / Real.log 2 + 2
  have hZ := one_le_Z
  have hA : 0 ≤ A := Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro q _ T t hT hq ht
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hBt : Bt q t ≤ (6 * Z) * T ^ 2 := by
    unfold Bt
    have h1 := mul_le_mul hq (show |t| + 3 ≤ 3 * T by linarith) (by positivity) hT0.le
    nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ Z by linarith)]
  calc
    Real.log (Bt q t) ≤ Real.log ((6 * Z) * T ^ 2) :=
      Real.log_le_log (by unfold Bt; positivity) hBt
    _ = A + 2 * Real.log T := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num [A]
    _ ≤ K * Real.log T := by
      have hmul : A ≤ A / Real.log 2 * Real.log T := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hlog hA
      dsimp [K]
      nlinarith

/-- The nonprincipal part of the exceptional zero reality assertion on p.127. -/
theorem height_box_real_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ {T : ℝ}, 2 ≤ T → (q : ℝ) ≤ T →
    ∀ ρ : ℂ, χ.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      χ ^ 2 = 1 ∧ ρ.im = 0 := by
  obtain ⟨K, hK, hlog⟩ := log_Bt_le_log_height
  obtain ⟨c, c', hc, hc', hreg⟩ := zero_free_region_real
  refine ⟨c / (2 * K), by positivity, ?_⟩
  intro q _ χ hχ T hT hq ρ hz hβ ht
  rcases (hreg q χ hχ).1 ρ hz with hleft | hright
  · have hlT : 0 < Real.log T := Real.log_pos (by linarith)
    have hlB : 0 < Real.log (Bt q ρ.im) := by linarith [one_le_log_Bt (N := q) ρ.im]
    have hd : c / (K * Real.log T) ≤ c / Real.log (Bt q ρ.im) :=
      div_le_div_of_nonneg_left hc.le hlB (hlog hT hq ht)
    have hpos : 0 < c / (2 * K) / Real.log T := by positivity
    have heq : c / (K * Real.log T) = 2 * (c / (2 * K) / Real.log T) := by field_simp
    rw [heq] at hd
    linarith
  · exact ⟨hright.2.2.1, hright.2.2.2⟩

/-- The principal primitive character has no zero in a uniform p.127 box. -/
theorem zeta_height_box_nonzero : ∃ b : ℝ, 0 < b ∧ ∀ {T : ℝ}, 2 ≤ T →
    ∀ ρ : ℂ, 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T → riemannZeta ρ ≠ 0 := by
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  obtain ⟨σ, hσ, hsmall⟩ := ZetaNoZerosInBox 3
  let b := min A ((1 - σ) * Real.log 2)
  have hb : 0 < b := lt_min hA.1 (mul_pos (by linarith) (Real.log_pos (by norm_num)))
  refine ⟨b, hb, ?_⟩
  intro T hT ρ hβ ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hrep : (ρ.re : ℂ) + ρ.im * Complex.I = ρ := by simp
  by_cases h1 : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  by_cases ht3 : |ρ.im| ≤ 3
  · have hcmp : b / Real.log T ≤ 1 - σ := by
      apply (div_le_iff₀ hlT).mpr
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
      have hmin : b ≤ (1 - σ) * Real.log 2 := min_le_right _ _
      nlinarith
    simpa only [hrep] using hsmall ρ.im ht3 ρ.re (by linarith)
  · have ht3' : 3 < |ρ.im| := lt_of_not_ge ht3
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hcomp : b / Real.log T ≤ A / Real.log |ρ.im| := by
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hlT.le).trans
        (div_le_div_of_nonneg_left hA.1.le hlogt (Real.log_le_log (by positivity) ht))
    have hh := hlarge ρ.re ρ.im ht3' ⟨by simpa only [Real.rpow_one] using (show 1 - A / Real.log |ρ.im| ≤ ρ.re by linarith), lt_of_not_ge h1⟩
    simpa only [hrep] using hh

/-- Equality of primitive characters follows from equality at a common multiple. -/
theorem primitive_sigma_eq_of_lift_eq {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ (q₁ + 1)) (χ₂ : DirichletCharacter ℂ (q₂ + 1))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (he : DirichletCharacter.changeLevel (Nat.dvd_mul_right (q₁ + 1) (q₂ + 1)) χ₁ =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left (q₂ + 1) (q₁ + 1)) χ₂) :
    (⟨q₁, χ₁⟩ : Σ q : ℕ, DirichletCharacter ℂ (q + 1)) = ⟨q₂, χ₂⟩ := by
  have hc := congrArg DirichletCharacter.conductor he
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    h₁, h₂] at hc
  have hq : q₁ = q₂ := by omega
  subst q₂
  have hχ := DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right (q₁ + 1) (q₁ + 1)) he
  subst χ₂
  rfl

/-- Narrowing the zero strip preserves membership in the exceptional family. -/
theorem excSet_mono {b₁ b₂ T : ℝ} (hb : b₁ ≤ b₂) (hT : 2 ≤ T) :
    excSet b₁ T ⊆ excSet b₂ T := by
  rintro x ⟨hq, hp, ρ, hz, hβ, ht⟩
  refine ⟨hq, hp, ρ, hz, ?_, ht⟩
  have hdiv := div_le_div_of_nonneg_right hb (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
  linarith

/-- No primitive principal character occurs in the uniform zero strip on p.127. -/
theorem excSet_nonprincipal : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ x ∈ excSet b T, x.2 ≠ 1 := by
  obtain ⟨b, hb, hz⟩ := zeta_height_box_nonzero
  refine ⟨b, hb, ?_⟩
  intro T hT x hx he
  have hc := hx.2.1
  rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hc
  have hq : x.1 = 0 := by omega
  obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
  have hzeta : riemannZeta ρ = 0 := by
    rcases x with ⟨q, χ⟩
    dsimp at hq
    subst q
    simpa only [he, DirichletCharacter.LFunction_modOne_eq] using hρ
  exact hz hT ρ hβ ht hzeta


/-- LEAF. Unit U-1532. The exceptional zero is real and its character is real, p. 127: for
small `b > 0`, any zero in `Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T` of `L(s, χ)`, `χ` primitive of
conductor at most `T`, has `Im ρ = 0`, and `χ² = 1`. -/
theorem page_real : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    x.2 ^ 2 = 1 ∧ ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      ρ.im = 0 := by
  obtain ⟨bn, hbn, hn⟩ := height_box_real_nonprincipal
  obtain ⟨bz, hbz, hz⟩ := zeta_height_box_nonzero
  let b := min bn bz
  refine ⟨b, lt_min hbn hbz, ?_⟩
  intro T hT x hx
  have hq : ((x.1 + 1 : ℕ) : ℝ) ≤ T := by simpa using hx.1
  have hprim := hx.2.1
  have hχ : x.2 ≠ 1 := by
    intro he
    have hlev : x.1 + 1 = 1 := by
      have hc := hprim
      rw [DirichletCharacter.IsPrimitive, he, DirichletCharacter.conductor_one] at hc
      exact hc.symm
    obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
    have hzeta : riemannZeta ρ = 0 := by
      have hxp : x.1 = 0 := by omega
      rcases x with ⟨q, χ⟩
      dsimp at hxp
      subst q
      simpa only [he, DirichletCharacter.LFunction_modOne_eq] using hρ
    have hβz : 1 - bz / Real.log T ≤ ρ.re := by
      have hcmp := div_le_div_of_nonneg_right (min_le_right bn bz) (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
      linarith
    exact hz hT ρ hβz ht hzeta
  have hmono (ρ : ℂ) (hβ : 1 - b / Real.log T ≤ ρ.re) : 1 - bn / Real.log T ≤ ρ.re := by
    have hcmp := div_le_div_of_nonneg_right (min_le_left bn bz) (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  obtain ⟨ρ, hρ, hβ, ht⟩ := hx.2.2
  refine ⟨(hn x.2 hχ hT hq ρ hρ (hmono ρ hβ) ht).1, ?_⟩
  intro ρ hρ hβ ht
  exact (hn x.2 hχ hT hq ρ hρ (hmono ρ hβ) ht).2

/-- The finite Fourier identity before the order split in Lemma 6 on pp.134 and 135. -/
theorem ramanujan_tuple_sum_eq (q k L : ℕ) :
    ∑ x : pairs k L, ramanujanSum q (dif x) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ((‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) := by
  classical
  unfold ramanujanSum
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hp : Gs L ((a : ℝ) / q) ^ k =
      ∑ ν : Fin k → Fin L, eC (sv ν * ((a : ℝ) / q)) :=
    LeanLab.Linnik.U1434Lemma21.Gs_pow k L _
  have hc (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
    simpa only [LeanLab.Linnik.U1434Lemma21.e_eq_eC] using
      (LeanLab.PNTPort.LargeSieve.e_neg x).symm
  have hn : ((‖Gs L ((a : ℝ) / q)‖ ^ (2 * k) : ℝ) : ℂ) =
      Gs L ((a : ℝ) / q) ^ k * (starRingEnd ℂ) (Gs L ((a : ℝ) / q) ^ k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  rw [hn, hp, map_sum, sum_mul_sum, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro ν hν
  apply sum_congr rfl
  intro mu hmu
  rw [hc, ← LeanLab.Linnik.U1434Lemma21.eC_add]
  congr 1
  simp only [dif, Int.cast_sub, Int.cast_natCast]
  ring

/-- The q one main term in the finite expansion of Lemma 6. -/
theorem ramanujan_tuple_sum_one (k L : ℕ) :
    ∑ x : pairs k L, ramanujanSum 1 (dif x) = (L : ℂ) ^ (2 * k) := by
  have hR (n : ℤ) : ramanujanSum 1 n = 1 := by simp [ramanujanSum, eC]
  simp only [hR, sum_const, nsmul_eq_mul, mul_one]
  simp [pairs, Fintype.card_prod, ← pow_add, two_mul]

/-- The justified finite sum and singular series exchange at the start of Lemma 6. -/
theorem offdiag_singSeries_eq_tsum (k L : ℕ) :
    ∑ x : pairs k L with dif x ≠ 0, singSeries (dif x) =
      ∑' q : ℕ, ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
        ∑ x : pairs k L with dif x ≠ 0, ramanujanSum q (dif x) := by
  classical
  have hs : ∀ x ∈ (univ : Finset (pairs k L)).filter (fun x => dif x ≠ 0),
      Summable (fun q : ℕ => ((ArithmeticFunction.moebius q : ℤ) : ℂ) ^ 2 /
        (q.totient : ℂ) ^ 2 * ramanujanSum q (dif x)) := by
    intro x hx
    exact summable_singSeries (mem_filter.mp hx).2
  simp only [singSeries]
  rw [← Summable.tsum_finsetSum hs]
  apply tsum_congr
  intro q
  exact (mul_sum _ _ _).symm

/-- The zero frequency Ramanujan coefficient removed on p.134. -/
theorem ramanujanSum_zero (q : ℕ) : ramanujanSum q 0 = (q.totient : ℂ) := by
  simp [ramanujanSum, eC, Nat.totient, Nat.coprime_comm]

/-- The square root order series used in Lemma 10 on p.137 is uniformly bounded. -/
theorem half_order_totient_weight_le (S : Finset ℕ) :
    ∑ q ∈ S with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q)) ≤ 16 * Real.log 2 * Real.exp 27 := by
  classical
  have hpoint (q : ℕ) (hq : q ∈ S.filter Odd) :
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q)) ≤ LeanLab.Romanov.halfOrderTerm q := by
    have ho := (mem_filter.mp hq).2
    by_cases hs : Squarefree q
    · rw [LeanLab.Romanov.halfOrderTerm, ite_eq_left (show LeanLab.LPZ2007.OddSqf q from ⟨ho, hs⟩)]
      rw [div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right
        (LeanLab.Romanov.TotientWeights134.totientWeight_le_fd ⟨ho, hs⟩) (Real.sqrt_nonneg _)
    · simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, Int.cast_zero,
        zero_pow (by decide : 2 ≠ 0), zero_div]
      exact LeanLab.Romanov.halfOrderTerm_nonneg q
  exact (sum_le_sum hpoint).trans
    ((LeanLab.Romanov.halfOrder_summable.sum_le_tsum _
      (fun q _ => LeanLab.Romanov.halfOrderTerm_nonneg q)).trans LeanLab.Romanov.halfOrder_tsum_le)

/-- The least common multiple order kernel in Lemma 10 on p.137 gains a square root order. -/
theorem lcm_order_weight_le {f : ℕ} (hf : Odd f) (S : Finset ℕ) :
    ∑ q ∈ S with Odd q,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        (q.totient : ℝ) / ordTwo (Nat.lcm f q) ≤
      (16 * Real.log 2 * Real.exp 27) / Real.sqrt (ordTwo f) := by
  classical
  have hfpos : (0 : ℝ) < ordTwo f := by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hf
  have hsf : 0 < Real.sqrt (ordTwo f) := Real.sqrt_pos.mpr hfpos
  have hpoint (q : ℕ) (hq : q ∈ S.filter Odd) :
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) / ordTwo (Nat.lcm f q) ≤
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := by
    have hqo := (mem_filter.mp hq).2
    have hlo : Odd (Nat.lcm f q) :=
      (hf.mul hqo).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right f q) (dvd_mul_left q f))
    have hlpos : (0 : ℝ) < ordTwo (Nat.lcm f q) :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hlo
    have hqpos : (0 : ℝ) < ordTwo q :=
      by exact_mod_cast LeanLab.Linnik.Decomp1532a.ordTwo_pos hqo
    have hsqp : 0 < Real.sqrt (ordTwo q) := Real.sqrt_pos.mpr hqpos
    have hfle : (ordTwo f : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast LeanLab.Linnik.Decomp1537a.xi_le_of_dvd hlo (Nat.dvd_lcm_left f q)
    have hqle : (ordTwo q : ℝ) ≤ ordTwo (Nat.lcm f q) := by
      exact_mod_cast LeanLab.Linnik.Decomp1537a.xi_le_of_dvd hlo (Nat.dvd_lcm_right f q)
    have hsqrt : Real.sqrt (ordTwo f) * Real.sqrt (ordTwo q) ≤ ordTwo (Nat.lcm f q) := by
      calc
        _ = Real.sqrt ((ordTwo f : ℝ) * ordTwo q) := (Real.sqrt_mul hfpos.le _).symm
        _ ≤ Real.sqrt ((ordTwo (Nat.lcm f q) : ℝ) * ordTwo (Nat.lcm f q)) :=
          Real.sqrt_le_sqrt (mul_le_mul hfle hqle hqpos.le hlpos.le)
        _ = _ := Real.sqrt_mul_self hlpos.le
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) by positivity)
      (mul_pos hsf hsqp) hsqrt
    convert hh using 1 <;> rw [div_mul_eq_div_div] <;> ring
  calc
    _ ≤ ∑ q ∈ S with Odd q,
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := sum_le_sum hpoint
    _ = (∑ q ∈ S with Odd q, ((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 /
        ((q.totient : ℝ) * Real.sqrt (ordTwo q))) / Real.sqrt (ordTwo f) := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (half_order_totient_weight_le S) hsf.le

/-- The first divisor reduction of Lemma 10 on p.137 with an explicit factor eight. -/
theorem exceptional_gcd_totient_le {r s : ℕ} (hs : 0 < s)
    (hr : r = s ∨ r = 4 * s ∨ r = 8 * s) (n : ℕ) :
    (Nat.gcd r n).totient ≤ 8 * ∑ f ∈ (Nat.gcd s n).divisors, f.totient := by
  rw [Nat.sum_totient]
  have hg : 0 < Nat.gcd s n := Nat.gcd_pos_of_pos_left n hs
  have hbound (d : ℕ) (hd : 0 < d) : Nat.gcd (d * s) n ≤ d * Nat.gcd s n := by
    apply Nat.le_of_dvd (Nat.mul_pos hd hg)
    have hdiv : Nat.gcd (d * s) n ∣ Nat.gcd (d * s) (d * n) :=
      Nat.gcd_dvd_gcd_of_dvd_right (d * s) (dvd_mul_left n d)
    rwa [Nat.gcd_mul_left] at hdiv
  have hφ := Nat.totient_le (Nat.gcd r n)
  rcases hr with hr | hr | hr
  · subst r; omega
  · subst r; have hh := hbound 4 (by decide); omega
  · subst r; exact hφ.trans (hbound 8 (by decide))

/-- The direct Lemma 8 bound leaves a conductor factor and no logarithmic decay. -/
theorem twisted_totient_crude : ∃ C : ℝ, ∀ k N r : ℕ,
    1 ≤ k → k ≤ N → 2 ≤ N → 0 < r →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * ((r : ℝ) / r.totient) * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hC⟩ := LeanLab.Linnik.Decomp1532a.lemma8
  refine ⟨C, ?_⟩
  intro k N r hk hkN hN hr
  have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr
  have hfactor (n : ℕ) :
      (r : ℝ) * (Nat.gcd r n).totient / (r.totient : ℝ) ^ 2 ≤ (r : ℝ) / r.totient := by
    have hdiv := Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left r n)
    have hle : ((Nat.gcd r n).totient : ℝ) ≤ r.totient := by
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hr) hdiv
    calc
      _ ≤ (r : ℝ) * r.totient / (r.totient : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg r)) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
        ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) * ((r : ℝ) / r.totient) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hfactor _) (by positivity)
    _ = ((r : ℝ) / r.totient) *
        (∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
          ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ)) := by rw [← sum_mul]; ring
    _ ≤ ((r : ℝ) / r.totient) * (C * (Nat.log 2 N : ℝ) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left (hC k N hk hkN hN) (by positivity)
    _ = _ := by ring

/-- LEAF. Unit U-1532. Page's theorem, p. 127: there is `b > 0` such that for every `T ≥ 2` at
most one primitive character of conductor at most `T` has an L-function with a zero in
`Re ρ ≥ 1 - b/log T`, `|Im ρ| ≤ T`. -/
theorem page_subsingleton : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → (excSet b T).Subsingleton := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨cl, hcl, hl⟩ := landau
  let b := min (min br bn) cl
  have hbr' : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbn' : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hcl' : b ≤ cl := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) hcl, ?_⟩
  intro T hT x hx y hy
  have hxbr := excSet_mono hbr' hT hx
  have hybr := excSet_mono hbr' hT hy
  have hxne := hn T hT x (excSet_mono hbn' hT hx)
  have hyne := hn T hT y (excSet_mono hbn' hT hy)
  obtain ⟨ρ₁, hz₁, hb₁, ht₁⟩ := hx.2.2
  obtain ⟨ρ₂, hz₂, hb₂, ht₂⟩ := hy.2.2
  have hβbr₁ : 1 - br / Real.log T ≤ ρ₁.re := by
    have hd := div_le_div_of_nonneg_right hbr' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have hβbr₂ : 1 - br / Real.log T ≤ ρ₂.re := by
    have hd := div_le_div_of_nonneg_right hbr' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him₁ := (hr T hT x hxbr).2 ρ₁ hz₁ hβbr₁ ht₁
  have him₂ := (hr T hT y hybr).2 ρ₂ hz₂ hβbr₂ ht₂
  have he₁ : (ρ₁.re : ℂ) = ρ₁ := by apply Complex.ext <;> simp [him₁]
  have he₂ : (ρ₂.re : ℂ) = ρ₂ := by apply Complex.ext <;> simp [him₂]
  have hzreal₁ : x.2.LFunction (ρ₁.re : ℂ) = 0 := by rwa [he₁]
  have hzreal₂ : y.2.LFunction (ρ₂.re : ℂ) = 0 := by rwa [he₂]
  have hbtop₁ : ρ₁.re ≤ 1 := by
    by_contra hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re x.2 (Or.inl hxne) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz₁
  have hbtop₂ : ρ₂.re ≤ 1 := by
    by_contra hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re y.2 (Or.inl hyne) (by simpa using (le_of_lt (lt_of_not_ge hh)))) hz₂
  have hQ : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT)
  have hxQ : x.1 + 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hx.1)
  have hyQ : y.1 + 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hy.1)
  have hlogQ : 0 < Real.log (⌊T⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  have hlogT : Real.log (⌊T⌋₊ : ℝ) ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast (show 0 < ⌊T⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hcmp : b / Real.log T ≤ cl / Real.log (⌊T⌋₊ : ℝ) :=
    (div_le_div_of_nonneg_right hcl' (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)).trans
      (div_le_div_of_nonneg_left hcl.le hlogQ hlogT)
  have hlift := hl ⌊T⌋₊ hQ (x.1 + 1) (y.1 + 1) hxQ hyQ x.2 y.2 hxne hyne
    ρ₁.re ρ₂.re hbtop₁ hbtop₂ hzreal₁ hzreal₂ (by linarith) (by linarith)
  exact primitive_sigma_eq_of_lift_eq x.2 y.2 hx.2.1 hy.2.1 hlift


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
  exact LeanLab.Romanov.Decomp134.lemma9 hr χ hχ h2

/-- LEAF. Unit U-1532. Lemma 10, display (8) p. 136: for `1 ≤ k ≤ N` and `r` of the form (7)
with `1 < r ≤ N`, `Σ_{n ≠ 0} r_{k,k}(n) |n|/φ(|n|) · r φ((r, n))/φ(r)² ≤ C L^{2k}/(log r)^{1/3}`
with an absolute `C`. -/
theorem lemma10 : ∃ C : ℝ, ∀ k N r : ℕ, 1 ≤ k → k ≤ N → 1 < r → r ≤ N →
    (∃ r₀ : ℕ, Odd r₀ ∧ Squarefree r₀ ∧ (r = r₀ ∨ r = 4 * r₀ ∨ r = 8 * r₀)) →
    ∑ x : pairs k (Nat.log 2 N) with dif x ≠ 0,
      ((dif x).natAbs : ℝ) / ((dif x).natAbs.totient : ℝ) *
        ((r : ℝ) * (Nat.gcd r (dif x).natAbs).totient / (r.totient : ℝ) ^ 2) ≤
      C * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log r ^ (1 / 3 : ℝ) := by
  -- LEAF. Gallagher 1975 p.137. The uniform weighted one coordinate estimate and the final divisor and logarithm split remain.
  sorry

/-- Gallagher 1975 p.127. The exceptional character has at most one zero in the height box. -/
theorem page_zero_unique : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    ∀ ρ₁ ρ₂ : ℂ, x.2.LFunction ρ₁ = 0 → x.2.LFunction ρ₂ = 0 →
      1 - b / Real.log T ≤ ρ₁.re → |ρ₁.im| ≤ T →
      1 - b / Real.log T ≤ ρ₂.re → |ρ₂.im| ≤ T → ρ₁ = ρ₂ := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨K, hK, hKlog⟩ := log_Bt_le_log_height
  obtain ⟨c, hc, hpage⟩ := page_two_zeros
  let b := min (min br bn) (c / K)
  have hbbr : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbbn : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hbc : b ≤ c / K := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) (by positivity), ?_⟩
  intro T hT x hx ρ₁ ρ₂ hz₁ hz₂ hb₁ ht₁ hb₂ ht₂
  have hχ := hn T hT x (excSet_mono hbbn hT hx)
  have hxbr := excSet_mono hbbr hT hx
  have hmono (ρ : ℂ) (hh : 1 - b / Real.log T ≤ ρ.re) :
      1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hbbr (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him₁ := (hr T hT x hxbr).2 ρ₁ hz₁ (hmono ρ₁ hb₁) ht₁
  have him₂ := (hr T hT x hxbr).2 ρ₂ hz₂ (hmono ρ₂ hb₂) ht₂
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlB : 0 < Real.log (Bt (x.1 + 1) 0) := by
    linarith [one_le_log_Bt (N := x.1 + 1) 0]
  have hcmp : b / Real.log T ≤ c / Real.log (Bt (x.1 + 1) 0) := by
    calc
      b / Real.log T ≤ (c / K) / Real.log T := div_le_div_of_nonneg_right hbc hlT.le
      _ = c / (K * Real.log T) := by rw [div_div]
      _ ≤ c / Real.log (Bt (x.1 + 1) 0) :=
        div_le_div_of_nonneg_left hc.le hlB
          (hKlog hT (by simpa using hx.1) (by simp; linarith : |(0 : ℝ)| ≤ T))
  exact hpage (x.1 + 1) x.2 hχ ρ₁ ρ₂ hz₁ hz₂ (by linarith)
    (by rw [him₁, abs_zero]; positivity) (by linarith)
    (by rw [him₂, abs_zero]; positivity)

/-- Gallagher 1975 p.127. Every exceptional zero in a sufficiently narrow height box is simple. -/
theorem page_zero_simple : ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 2 ≤ T → ∀ x ∈ excSet b T,
    ∀ ρ : ℂ, x.2.LFunction ρ = 0 → 1 - b / Real.log T ≤ ρ.re → |ρ.im| ≤ T →
      analyticOrderNatAt x.2.LFunction ρ = 1 := by
  obtain ⟨br, hbr, hr⟩ := page_real
  obtain ⟨bn, hbn, hn⟩ := excSet_nonprincipal
  obtain ⟨K, hK, hKlog⟩ := log_Bt_le_log_height
  obtain ⟨c, hc, hc31, hcount⟩ := page_count
  let b := min (min br bn) (c / K)
  have hbbr : b ≤ br := (min_le_left _ _).trans (min_le_left _ _)
  have hbbn : b ≤ bn := (min_le_left _ _).trans (min_le_right _ _)
  have hbc : b ≤ c / K := min_le_right _ _
  refine ⟨b, lt_min (lt_min hbr hbn) (by positivity), ?_⟩
  intro T hT x hx ρ hz hb ht
  have hχ := hn T hT x (excSet_mono hbbn hT hx)
  have hxbr := excSet_mono hbbr hT hx
  have hβbr : 1 - br / Real.log T ≤ ρ.re := by
    have hd := div_le_div_of_nonneg_right hbbr (show 0 ≤ Real.log T by apply Real.log_nonneg; linarith)
    linarith
  have him := (hr T hT x hxbr).2 ρ hz hβbr ht
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlB : 0 < Real.log (Bt (x.1 + 1) 0) := by
    linarith [one_le_log_Bt (N := x.1 + 1) 0]
  have hcmp : b / Real.log T ≤ c / Real.log (Bt (x.1 + 1) 0) := by
    calc
      b / Real.log T ≤ (c / K) / Real.log T := div_le_div_of_nonneg_right hbc hlT.le
      _ = c / (K * Real.log T) := by rw [div_div]
      _ ≤ c / Real.log (Bt (x.1 + 1) 0) :=
        div_le_div_of_nonneg_left hc.le hlB
          (hKlog hT (by simpa using hx.1) (by simp; linarith : |(0 : ℝ)| ≤ T))
  have hβ : 1 - c / Real.log (Bt (x.1 + 1) 0) ≤ ρ.re := by linarith
  have hγ : |ρ.im| ≤ c / Real.log (Bt (x.1 + 1) 0) := by rw [him, abs_zero]; positivity
  have hη31 : c / Real.log (Bt (x.1 + 1) 0) ≤ 1 / 31 := by
    rw [div_le_iff₀ hlB]
    have hh := one_le_log_Bt (N := x.1 + 1) 0
    nlinarith
  have hm := mem_Tset_of_box hχ hη31 hz hβ hγ
  classical
  have hmem : ρ - 3 / 2 ∈ (Tset hχ 0).filter (fun w =>
      1 - c / Real.log (Bt (x.1 + 1) 0) ≤ w.re + 3 / 2 ∧
      |w.im| ≤ c / Real.log (Bt (x.1 + 1) 0)) := by
    refine Finset.mem_filter.mpr ⟨hm, ?_, ?_⟩
    · have he : (ρ - 3 / 2).re + 3 / 2 = ρ.re := by simp
      rw [he]
      exact hβ
    · have he : (ρ - 3 / 2).im = ρ.im := by simp
      rw [he]
      exact hγ
  have hu : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) ≤ 1 :=
    (Finset.single_le_sum (fun w _ => Nat.zero_le _) hmem).trans (hcount (x.1 + 1) x.2 hχ)
  have hzshift : fShift x.2 0 (ρ - 3 / 2) = 0 := by simpa [fShift] using hz
  have ho : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) = 1 :=
    Nat.le_antisymm hu (one_le_order hχ 0 hzshift)
  have hg : AnalyticAt ℂ (fun z : ℂ => z + 3 / 2) (ρ - 3 / 2) := by fun_prop
  have hd : deriv (fun z : ℂ => z + 3 / 2) (ρ - 3 / 2) ≠ 0 := by simp
  have hshift := analyticOrderAt_comp_of_deriv_ne_zero (f := x.2.LFunction) hg hd
  have hnat := congrArg ENat.toNat hshift
  have he : analyticOrderNatAt (fShift x.2 0) (ρ - 3 / 2) =
      analyticOrderNatAt x.2.LFunction ρ := by
    unfold analyticOrderNatAt
    have hf : fShift x.2 0 = fun z : ℂ => x.2.LFunction (z + 3 / 2) := by
      funext z
      simp [fShift]
    rw [hf]
    simpa only [Function.comp_def, sub_add_cancel] using hnat
  exact he.symm.trans ho

/-- Gallagher 1975 p.127. The exceptional conductor exceeds every fixed power of log T
up to a positive constant depending on that power. No effective constant is asserted. -/
theorem exceptional_conductor_log_growth : ∃ b : ℝ, 0 < b ∧
    ∀ B : ℝ, 0 < B → ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T →
    ∀ x ∈ excSet b T, c * Real.log T ^ B ≤ (x.1 : ℝ) + 1 := by
  obtain ⟨b, hb, hreal⟩ := page_real
  refine ⟨b, hb, ?_⟩
  intro B hB
  obtain ⟨cs, hcs, hs⟩ := siegel (1 / B) (by positivity)
  refine ⟨(cs / b) ^ B, Real.rpow_pos_of_pos (div_pos hcs hb) _, ?_⟩
  intro T hT x hx
  obtain ⟨ρ, hz, hβ, ht⟩ := hx.2.2
  have hchi := (hreal T hT x hx).1
  have him := (hreal T hT x hx).2 ρ hz hβ ht
  have he : (ρ.re : ℂ) = ρ := by apply Complex.ext <;> simp [him]
  have hzreal : x.2.LFunction (ρ.re : ℂ) = 0 := by rwa [he]
  have hS := hs x.1 x.2 hx.2.1 hchi ρ.re hzreal
  let r : ℝ := (x.1 : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hbound : cs * r ^ (-(1 / B)) ≤ b / Real.log T := by
    dsimp [r]
    linarith
  rw [Real.rpow_neg hr.le, ← div_eq_mul_inv] at hbound
  have hp : 0 < r ^ (1 / B) := Real.rpow_pos_of_pos hr _
  have hprod := (div_le_div_iff₀ hp hlT).mp hbound
  have hbase : cs / b * Real.log T ≤ r ^ (1 / B) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb]
    nlinarith
  have hraise := Real.rpow_le_rpow (by positivity : 0 ≤ cs / b * Real.log T) hbase hB.le
  rw [← Real.rpow_mul hr.le, one_div_mul_cancel hB.ne', Real.rpow_one] at hraise
  rw [Real.mul_rpow (div_nonneg hcs.le hb.le) hlT.le] at hraise
  exact hraise

end LeanLab.Linnik.Decomp1532b
