/-
Split of `theorem82`, the Theorem 8.2 step of this folder's Section 8, into four leaves and one
assembly.

The assembly is the counting argument of the proof.  The sparse two-sided Hardy-Littlewood
input is a statement about the multiples of the conductor `r` in the dyadic interval at
`X = r^A`; the analytic formula of Section 8 fails on at most `X^(3/5+ε)` even integers of
that interval, and the sparse input fails on at most `X^(3/5)` of them.  Since the interval
holds about `X/r` multiples of `r`, and `A > 5/2` makes `X^(3/5)` smaller than `X/r`, one
multiple of `r` lies outside both exceptional sets.  There the two-sided range and the
analytic formula contradict each other, because at a real zero `β = 1 - e` with `e` small the
formula's main term is `𝔖(N)·N·(1 + χ(-1))` up to `O(δ)`.

Leaves: a lower bound for the singular series on even arguments, the two-sided estimate for
the beta factor at a zero close to one, the domination of the three error terms by the main
term, and the absence of zeros at or beyond one.  Everything else is proved here.

AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.Counting107
import LeanLab.BhowmikGrimmelt2026.Section8Steps107

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-! ## Leaves -/

/-- LEAF. Step 1: on even arguments the singular series is at least `1/2`, so the main term
`𝔖(N)·N` of the analytic formula of Section 8 dominates its three error terms. -/
theorem leaf_singular_lower (N : ℕ) (hEven : Even N) (h2 : 2 ≤ N) : (1 / 2 : ℝ) ≤ singular N := by
  sorry

/-- LEAF. Step 2: at a real zero `β` with `3/4 ≤ β ≤ 1` the beta factor is real and the
combination `βC(β,β)·N^(2β-2)` differs from one by at most `8·(1-β)·log N` on either side.
This is the factor that turns the formula's main term into `𝔖(N)·N·(1 + χ(-1))`. -/
theorem leaf_kappa_between (N : ℕ) (hN : 2 ≤ N) {β : ℝ} (hβ : 3 / 4 ≤ β) (hβ' : β ≤ 1) :
    (betaC (β : ℂ) (β : ℂ)).im = 0 ∧
      1 - 8 * (1 - β) * Real.log N ≤ (betaC (β : ℂ) (β : ℂ)).re * (N : ℝ) ^ (2 * β - 2) ∧
      (betaC (β : ℂ) (β : ℂ)).re * (N : ℝ) ^ (2 * β - 2) ≤ 1 + 8 * (1 - β) * Real.log N := by
  sorry

/-- LEAF. Step 3: the three error terms of the analytic formula — the `X`-term carrying
`(e·log X)^c'`, the conductor term `𝔖(N)·N·r/φ(r)^2` and the minor term `X^(1-ε₀)` — are in
total at most `(δ/4)·𝔖(N)·N` on the dyadic interval, once the conductor is large enough.
This is where the constant `c = c(δ)` and the threshold `r₀ = r₀(A,δ)` come from. -/
theorem leaf_error_domination (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (C c' ε₀ h : ℝ)
    (hc' : 0 < c') (hε₀ : 0 < ε₀) (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ c < h ∧ c ≤ δ / 32 ∧ ∀ A : ℝ, 5 / 2 < A → ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ (N : ℕ) (e : ℝ), 0 ≤ e → e * Real.log ((r : ℝ) ^ A) ≤ c →
        N ∈ Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊ → Even N →
          C * (singular N * (r : ℝ) ^ A * ((e * Real.log ((r : ℝ) ^ A)) ^ c') +
                singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
                ((r : ℝ) ^ A) ^ (1 - ε₀)) ≤ (δ / 4) * (singular N * N) := by
  sorry

/-- LEAF. Step 4: a primitive character of conductor at least two has no zero of its
L-function at or beyond one, so only the range `1 - c/log X < β < 1` needs the counting step. -/
theorem leaf_LFunction_ne_zero_ge_one {r : ℕ} [NeZero r] (hr : 2 ≤ r) (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) {β : ℝ} (hβ : 1 ≤ β) : DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  sorry

/-! ## Private steps of the assembly -/

/-- A real number, read inside the complex numbers, has its absolute value as norm. -/
private theorem norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  first
    | rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_sq_eq_abs]
    | simpa using RCLike.norm_ofReal (K := ℂ) x
    | simp

/-- A two-sided `δ/4` estimate for the beta factor plus a `δ/4` analytic remainder contradict
the two-sided range of the sparse input, for either sign of the character at `-1`. -/
private theorem split_norm_step {a s k δ : ℝ} {z : ℂ} (hz : z = 1 ∨ z = -1) (hs : 0 < s)
    (hδ : 0 < δ) (hmain : ‖(a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)‖ ≤ (δ / 4) * s)
    (hk : |k - 1| ≤ δ / 4) : ‖(a : ℂ) - (1 + z) * (s : ℂ)‖ < δ * s := by
  have hz1 : ‖z‖ = 1 := by rcases hz with h | h <;> simp [h]
  have hcast : (k : ℂ) - 1 = ((k - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have hshift : ‖z * (s : ℂ) * ((k : ℂ) - 1)‖ = s * |k - 1| := by
    have h1 : ‖z * (s : ℂ) * ((k : ℂ) - 1)‖ = ‖z‖ * ‖(s : ℂ)‖ * ‖((k : ℂ) - 1)‖ := by
      rw [norm_mul, norm_mul]
    rw [h1, hz1, hcast, one_mul, norm_ofReal_eq_abs s, norm_ofReal_eq_abs (k - 1),
      abs_of_pos hs]
  have hsplit : (a : ℂ) - (1 + z) * (s : ℂ)
      = ((a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)) + z * (s : ℂ) * ((k : ℂ) - 1) := by
    ring
  have h1 : s * |k - 1| ≤ s * (δ / 4) := mul_le_mul_of_nonneg_left hk hs.le
  rw [hsplit]
  calc ‖((a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)) + z * (s : ℂ) * ((k : ℂ) - 1)‖
      ≤ ‖(a : ℂ) - (s : ℂ) - z * (s : ℂ) * (k : ℂ)‖ + ‖z * (s : ℂ) * ((k : ℂ) - 1)‖ :=
        norm_add_le _ _
    _ ≤ (δ / 4) * s + s * |k - 1| := by rw [hshift]; linarith
    _ ≤ (δ / 4) * s + s * (δ / 4) := by linarith
    _ < δ * s := by nlinarith

/-- The beta factor at a real argument is the real number given by its real part. -/
private theorem betaC_of_real {β : ℝ} (him : (betaC (β : ℂ) (β : ℂ)).im = 0) :
    betaC (β : ℂ) (β : ℂ) = (((betaC (β : ℂ) (β : ℂ)).re : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simpa using him

/-! ## Assembly -/

/-- Theorem 8.2, proved from the four leaves: the sparse two-sided Hardy-Littlewood input on
the multiples of the conductor rules out real zeros of a primitive real character beyond
`1 - c/log X`. -/
theorem theorem82_split : Theorem82 := by
  intro δ hδ0 hδ1
  obtain ⟨h, c', ε₀, C, hh, hc', hε₀, hrest⟩ := prop81 (2 / 5) (by norm_num) (by norm_num)
  obtain ⟨c, hc0, hch, hcδ, hdom⟩ := leaf_error_domination δ hδ0 hδ1 C c' ε₀ h hc' hε₀ hh
  refine ⟨c, hc0, ?_⟩
  intro A hA
  obtain ⟨hA1, hεpos, hεlt⟩ := thm82_arith hA
  obtain ⟨Cε, hCε⟩ := hrest ((1 - 1 / A - 3 / 5) / 2) hεpos
  obtain ⟨r₀, hr₀⟩ := hdom A hA
  obtain ⟨r₁, hr₁⟩ := even_multiples_growth107 A hA (max Cε 0) (le_max_right _ _)
  refine ⟨max (max r₀ r₁) 2, ?_⟩
  intro r _ hr
  intro hcount
  intro χ hχprim hχreal β hβzero
  by_contra hcon
  simp only [not_le] at hcon
  -- scalar facts about the conductor and the scale
  have hr2 : 2 ≤ r := (le_max_right (max r₀ r₁) 2).trans hr
  have hr0r : r₀ ≤ r := (le_max_left r₀ r₁).trans ((le_max_left (max r₀ r₁) 2).trans hr)
  have hr1r : r₁ ≤ r := (le_max_right r₀ r₁).trans ((le_max_left (max r₀ r₁) 2).trans hr)
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hX2 : 2 ≤ (r : ℝ) ^ A := by
    have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have h2A : (2 : ℝ) ≤ (2 : ℝ) ^ A := by
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    exact h2A.trans (Real.rpow_le_rpow (by norm_num) h2r hA0.le)
  have hlogX : 0 < Real.log ((r : ℝ) ^ A) := Real.log_pos (by linarith)
  have hlogX1 : 1 ≤ Real.log ((r : ℝ) ^ A) := by
    have hX4 : (4 : ℝ) ≤ (r : ℝ) ^ A := by
      have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      have h24 : (4 : ℝ) ≤ (2 : ℝ) ^ A := by
        calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num [Real.rpow_two]
          _ ≤ (2 : ℝ) ^ A := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      exact h24.trans (Real.rpow_le_rpow (by norm_num) h2r hA0.le)
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      have hsplit : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [hsplit]
      nlinarith [Real.log_two_gt_d9]
    exact hlog4.trans (Real.log_le_log (by norm_num) hX4)
  have hcond : (r : ℝ) ≤ ((r : ℝ) ^ A) ^ (2 / 5 : ℝ) := (thm82_cond_lt_R hA hr1).le
  rcases lt_or_ge β 1 with hβlt | hβge
  · -- the zero sits in the interval (1 - c/log X, 1)
    have he0 : 0 < 1 - β := by linarith
    have helog : (1 - β) * Real.log ((r : ℝ) ^ A) ≤ c := by
      have h1 : 1 - β < c / Real.log ((r : ℝ) ^ A) := by linarith
      exact ((lt_div_iff₀ hlogX).mp h1).le
    have hβ34 : 3 / 4 ≤ β := by
      have h1 : 1 - β ≤ c / Real.log ((r : ℝ) ^ A) := (le_div_iff₀ hlogX).mpr helog
      have h2 : c / Real.log ((r : ℝ) ^ A) ≤ c := by
        rw [div_le_iff₀ hlogX]
        nlinarith [hc0]
      have h3 : c ≤ 1 / 32 := by linarith
      linarith
    -- the two exceptional sets
    set S : Finset ℕ := evenMultiples107 r ((r : ℝ) ^ A) with hS
    set B : Finset ℕ :=
      S.filter (fun N => ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N)) with hB
    set Ef : Finset ℕ := (Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter
      (fun N => Even N ∧
        ¬ ‖(r2 N : ℂ) - singular N * N - genSing χ χ N * betaC (β : ℂ) (β : ℂ) *
            (N : ℂ) ^ (2 * (β : ℂ) - 1)‖ ≤
          C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
            singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
            ((r : ℝ) ^ A) ^ (1 - ε₀))) with hEf
    -- the sparse input counts `B`
    have hBeq : B = (Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter
        (fun N => Even N ∧ r ∣ N ∧
          ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N)) := by
      ext N
      simp only [hB, hS, evenMultiples107, Finset.mem_filter, and_assoc]
    have hBcard : (B.card : ℝ) ≤ ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) := by
      rw [hBeq]
      exact hcount
    -- the analytic formula counts `Ef`
    have hstep := hCε ((r : ℝ) ^ A) hX2 r χ (1 - β) hχprim hχreal hcond he0
      ((lt_div_iff₀ hlogX).mpr (by linarith))
      (by simpa only [show (1 : ℝ) - (1 - β) = β from by ring] using hβzero)
    have hEcard : (Ef.card : ℝ) ≤ Cε * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) := by
      rw [hEf]
      simpa only [show (1 : ℝ) - (1 - β) = β from by ring] using hstep
    -- more multiples than both exceptional sets together
    have hSg : (max Cε 0) * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) +
        ((r : ℝ) ^ A) ^ (3 / 5 : ℝ) < (S.card : ℝ) := by
      rw [hS]
      exact hr₁ r hr1r
    have hE2 : (Ef.card : ℝ) ≤
        (max Cε 0) * ((r : ℝ) ^ A) ^ (3 / 5 + (1 - 1 / A - 3 / 5) / 2) :=
      hEcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hcard : (B.card : ℝ) + (Ef.card : ℝ) < (S.card : ℝ) := by linarith
    obtain ⟨N, hNS, hNB, hNE⟩ := exists_outside_two107 S B Ef hcard
    have hNS' : N ∈ evenMultiples107 r ((r : ℝ) ^ A) := hS ▸ hNS
    have hNB' : N ∉ S.filter
        (fun N => ¬ (δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N)) := hB ▸ hNB
    have hNE' : N ∉ (Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊).filter
        (fun N => Even N ∧
          ¬ ‖(r2 N : ℂ) - singular N * N - genSing χ χ N * betaC (β : ℂ) (β : ℂ) *
              (N : ℂ) ^ (2 * (β : ℂ) - 1)‖ ≤
            C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
              singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
              ((r : ℝ) ^ A) ^ (1 - ε₀))) := hEf ▸ hNE
    obtain ⟨hNIcc, hNEv, hNdiv⟩ : N ∈ Finset.Icc ⌈(r : ℝ) ^ A / 2⌉₊ ⌊(r : ℝ) ^ A⌋₊ ∧
        Even N ∧ r ∣ N := by
      simpa only [evenMultiples107, Finset.mem_filter] using hNS'
    -- the range of the sparse input at this multiple
    have hgood : δ * singular N * N ≤ r2 N ∧ r2 N ≤ (2 - δ) * singular N * N := by
      by_contra hbad
      exact hNB' (Finset.mem_filter.mpr ⟨hNS, hbad⟩)
    have hrange : δ * (singular N * N) ≤ r2 N ∧ r2 N ≤ (2 - δ) * (singular N * N) :=
      ⟨by simpa only [mul_assoc] using hgood.1, by simpa only [mul_assoc] using hgood.2⟩
    -- the analytic formula at this multiple
    have hnorm : ‖(r2 N : ℂ) - singular N * N - genSing χ χ N * betaC (β : ℂ) (β : ℂ) *
        (N : ℂ) ^ (2 * (β : ℂ) - 1)‖ ≤
        C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
          singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
          ((r : ℝ) ^ A) ^ (1 - ε₀)) := by
      by_contra hbad
      exact hNE' (Finset.mem_filter.mpr ⟨hNIcc, hNEv, hbad⟩)
    -- sizes
    have hNge : 1 ≤ N := by
      have h1 : 0 < ⌈(r : ℝ) ^ A / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
      have h2 := (Finset.mem_Icc.mp hNIcc).1
      omega
    have hN2 : 2 ≤ N := by
      obtain ⟨k, hk⟩ := hNEv
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hNX : (N : ℝ) ≤ (r : ℝ) ^ A :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hNIcc).2).trans (Nat.floor_le (by positivity))
    have hlogN : Real.log (N : ℝ) ≤ Real.log ((r : ℝ) ^ A) :=
      Real.log_le_log hNpos hNX
    have h8 : 8 * (1 - β) * Real.log (N : ℝ) ≤ δ / 4 := by
      have hstep1 : 8 * ((1 - β) * Real.log (N : ℝ)) ≤
          8 * ((1 - β) * Real.log ((r : ℝ) ^ A)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogN he0.le) (by norm_num)
      have hstep2 : 8 * ((1 - β) * Real.log ((r : ℝ) ^ A)) ≤ 8 * c :=
        mul_le_mul_of_nonneg_left helog (by norm_num)
      have hstep3 : 8 * c ≤ δ / 4 := by linarith
      calc 8 * (1 - β) * Real.log (N : ℝ) = 8 * ((1 - β) * Real.log (N : ℝ)) := by ring
        _ ≤ δ / 4 := by linarith
    -- the beta factor is one up to `δ/4`
    obtain ⟨hkim, hklo, hkhi⟩ := leaf_kappa_between N hN2 hβ34 hβlt.le
    set k : ℝ := (betaC (β : ℂ) (β : ℂ)).re * (N : ℝ) ^ (2 * β - 2) with hkdef
    have hk1 : |k - 1| ≤ δ / 4 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    -- the formula's third term is `χ(-1)·(𝔖(N)·N)·k`
    have hthird : genSing χ χ N * betaC (β : ℂ) (β : ℂ) * (N : ℂ) ^ (2 * (β : ℂ) - 1)
        = χ (-1) * ((singular N * N : ℝ) : ℂ) * (k : ℂ) := by
      have hgen : genSing χ χ N = χ (-1) * ((singular N : ℂ)) :=
        facts81.2 r χ hχprim hχreal N hNEv hN2 hNdiv
      have hpow : (N : ℂ) ^ (2 * (β : ℂ) - 1) = (((N : ℝ) ^ (2 * β - 1) : ℝ) : ℂ) := by
        rw [show (2 : ℂ) * (β : ℂ) - 1 = ((2 * β - 1 : ℝ) : ℂ) from by push_cast; ring]
        exact (Complex.ofReal_cpow hNpos.le (2 * β - 1)).symm
      have hbc := betaC_of_real hkim
      have hNpow : (N : ℝ) ^ (2 * β - 1) = (N : ℝ) * (N : ℝ) ^ (2 * β - 2) := by
        rw [show 2 * β - 1 = (2 * β - 2) + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
        ring
      rw [hgen, hbc, hpow, hNpow, hkdef]
      push_cast
      ring_nf
    have hnorm' : ‖(r2 N : ℂ) - ((singular N * N : ℝ) : ℂ) - χ (-1) *
        ((singular N * N : ℝ) : ℂ) * (k : ℂ)‖ ≤
        C * (singular N * (r : ℝ) ^ A * (((1 - β) * Real.log ((r : ℝ) ^ A)) ^ c') +
          singular N * N * (r : ℝ) / (Nat.totient r : ℝ) ^ 2 +
          ((r : ℝ) ^ A) ^ (1 - ε₀)) := by
      rw [hthird] at hnorm
      simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using hnorm
    -- the error terms are dominated by the main term
    have herr := hr₀ r hr0r N (1 - β) he0.le helog hNIcc hNEv
    -- contradiction
    have hs : 0 < singular N * N := by
      have h1 := leaf_singular_lower N hNEv hN2
      have h2 : (0 : ℝ) < (N : ℝ) := hNpos
      nlinarith
    refine sign_contradiction107 hδ0 hrange (character_neg_one107 χ) ?_
    refine split_norm_step (character_neg_one107 χ) hs hδ0 ?_ hk1
    exact hnorm'.trans herr
  · exact absurd hβzero (leaf_LFunction_ne_zero_ge_one hr2 χ hχprim hβge)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.theorem82_split
