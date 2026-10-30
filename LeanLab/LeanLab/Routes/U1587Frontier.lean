/-
AI wrote this Lean code. Claude, for the Lean Lab, PC run 20261030T0803Z-29399, unit U-1587,
T2 FRONTIER, the Goldbach exceptional set exponent, idea I-0140, a follow-up of I-0139.

Question: does any KNOWN character sum bound give a Burgess parameter `ϕ < 1/3` on the
non-cube-free class moduli `q = X^θ`, `θ ∈ (0.3003, 0.3343]`, that keep Zhao's exponent at 7/10?

Inputs surveyed.
* Heath-Brown 1992, Lemma 2.3 p. 8, copies/HB1992.txt: with `v` the cube-full part of `q`,
  `Σ χ(n) ≪ v^{(3k-1)/(4k²)} q^{(k+1)/(4k²)+ε} H^{1-1/k}` for every `k`.  Partial summation as on
  p. 9 gives `ϕ_L23(ν, k) = (1/4)(1 + ν(3k-1)/(k+1))` for `v = q^ν`, and Pintz P0016 (5.10) p. 20
  takes `k = ⌈4/ε⌉ → ∞`, so the usable value is `(1 + 3ν)/4`: below `1/3` iff `ν < 1/9`.
* Postnikov, Gallagher 1972, Iwaniec 1974, Banks-Shparlinski arXiv 1605.07553: need a small core
  `∏_{p ∣ q} p`.  Chang arXiv 1201.0299 Theorem 5: needs `q > N > P(q)^{1000}`.
* Irving arXiv 1503.07156, which I-0139 labelled Banks-Shparlinski: squarefree smooth moduli only.
* Heath-Brown arXiv 1203.5219: Burgess with `r ≥ 4` only for cube-free `q`.

Answer, NEGATIVE, BLOCKED.  The class modulus is fixed by hypothetical zeros, so the method needs
the worst admissible `q`.  `q = p³`, `p` prime, is non-cube-free, its cube-full part is all of `q`,
`cubeFullPart_primeCube`, so Lemma 2.3 gives `ϕ_L23 = k/(k+1) ≥ 3/4`, `phiL23_one_ge`, and its
core is `p = q^{1/3}`, `rad_primeCube`, so every small-core bound and Chang's Theorem 5 are vacuous.
Only Burgess `r = 3`, `ϕ = 1/3`, applies, and primes `p` with `p³` in the binding window exist for
every large `X`.  Any route below 7/10 through U-1585's split needs `BurgessPhiOn PrimeCube ϕ` at
some `ϕ < 1/3`, `primeCube_needed`, which is OPEN.
Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib
import LeanLab.Routes.U1585Frontier

open Real

noncomputable section
namespace LeanLab.Routes.U1587

open LeanLab.Routes.U1563 LeanLab.Routes.U1585

/-! ## 1. Cube-full part, core and the prime-cube moduli -/

/-- The cube-full part `v` of Heath-Brown 1992, Lemma 2.3 p. 8: the product of the `p^e ∥ q`
with `e ≥ 3`. -/
def cubeFullPart (q : ℕ) : ℕ := q.factorization.prod fun p e => if 3 ≤ e then p ^ e else 1

/-- The core `q' = ∏_{p ∣ q} p` of Chang 1201.0299 and Banks-Shparlinski 1605.07553. -/
def rad (q : ℕ) : ℕ := q.primeFactors.prod id

/-- The gap class: cubes of primes. -/
def PrimeCube (q : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ q = p ^ 3

/-- Vacuity: the class is inhabited, `8 = 2³`. -/
theorem primeCube_eight : PrimeCube 8 := ⟨2, Nat.prime_two, by norm_num⟩

/-- PROVED: a prime cube is not cube-free, so it lies in U-1585's open class. -/
theorem primeCube_nonCubeFree {q : ℕ} (h : PrimeCube q) : NonCubeFree q := by
  obtain ⟨p, hp, rfl⟩ := h
  exact fun hc => hc p hp dvd_rfl

/-- PROVED: the cube-full part of `p³` is `p³`, so `ν = 1` in Lemma 2.3. -/
theorem cubeFullPart_primeCube {p : ℕ} (hp : p.Prime) : cubeFullPart (p ^ 3) = p ^ 3 := by
  unfold cubeFullPart
  rw [hp.factorization_pow, Finsupp.prod_single_index (by simp)]
  simp

/-- PROVED: the core of `p³` is `p = q^{1/3}`, not small. -/
theorem rad_primeCube {p : ℕ} (hp : p.Prime) : rad (p ^ 3) = p := by
  unfold rad
  rw [Nat.primeFactors_prime_pow (by norm_num) hp]
  simp

/-- PROVED: `rad (p³)³ = p³`, the core is exactly the cube root. -/
theorem rad_primeCube_cube {p : ℕ} (hp : p.Prime) : rad (p ^ 3) ^ 3 = p ^ 3 := by
  rw [rad_primeCube hp]

/-- Moduli whose cube-full part is at most `q^ν`, Lemma 2.3's good class. -/
def SmallCubeFull (ν : ℝ) (q : ℕ) : Prop := (cubeFullPart q : ℝ) ≤ (q : ℝ) ^ ν

/-- PROVED: a prime cube is outside `SmallCubeFull ν` for every `ν < 1`. -/
theorem primeCube_not_small {q : ℕ} (h : PrimeCube q) {ν : ℝ} (hν : ν < 1) :
    ¬ SmallCubeFull ν q := by
  obtain ⟨p, hp, rfl⟩ := h
  unfold SmallCubeFull
  rw [cubeFullPart_primeCube hp, not_le]
  have h1 : (1 : ℝ) < ((p ^ 3 : ℕ) : ℝ) := by
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    exact_mod_cast this
  calc ((p ^ 3 : ℕ) : ℝ) ^ ν < ((p ^ 3 : ℕ) : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt h1 hν
    _ = _ := by rw [Real.rpow_one]

/-! ## 2. The effective parameter from Lemma 2.3 -/

/-- `ϕ_L23(ν, k)`: Heath-Brown Lemma 2.3 with `v = q^ν`, written as `ϕ (1 + 1/k)`. -/
def phiL23 (ν k : ℝ) : ℝ := 1 / 4 * (1 + ν * (3 * k - 1) / (k + 1))

/-- PROVED: at `ν = 1`, the prime-cube case, `ϕ_L23 = k/(k+1)`. -/
theorem phiL23_one {k : ℝ} (hk : 0 < k) : phiL23 1 k = k / (k + 1) := by
  unfold phiL23; field_simp; ring

/-- PROVED: at `ν = 1`, `ϕ_L23 ≥ 3/4 > 1/3` for every `k ≥ 3`: Lemma 2.3 is useless on `p³`. -/
theorem phiL23_one_ge {k : ℝ} (hk : 3 ≤ k) : 3 / 4 ≤ phiL23 1 k := by
  rw [phiL23_one (by linarith), le_div_iff₀ (by linarith)]
  linarith

/-- The `k → ∞` value used by Pintz, capped by the general `ϕ = 1/3`. -/
def phiLim (ν : ℝ) : ℝ := min (1 / 3) ((1 + 3 * ν) / 4)

/-- PROVED: Lemma 2.3 beats `1/3` exactly when the cube-full part is below `q^{1/9}`. -/
theorem phiLim_lt_third_iff (ν : ℝ) : phiLim ν < 1 / 3 ↔ ν < 1 / 9 := by
  unfold phiLim
  constructor
  · intro h
    rcases min_lt_iff.mp h with h | h
    · exact absurd h (lt_irrefl _)
    · linarith
  · intro h
    exact min_lt_iff.mpr (Or.inr (by linarith))

/-- PROVED: `ϕ_L23(ν, k) ≤ (1 + 3ν)/4` for `ν ≥ 0`, `k ≥ 1`, so the Prop below is implied by
Lemma 2.3 for every `k`. -/
theorem phiL23_le_lim {ν k : ℝ} (hν : 0 ≤ ν) (hk : 1 ≤ k) : phiL23 ν k ≤ (1 + 3 * ν) / 4 := by
  unfold phiL23
  have hk1 : 0 < k + 1 := by linarith
  have : (3 * k - 1) / (k + 1) ≤ 3 := by rw [div_le_iff₀ hk1]; linarith
  have := mul_le_mul_of_nonneg_left this hν
  rw [mul_div_assoc]; linarith

/-- CITED, a LAB DERIVATION from Heath-Brown 1992 Lemma 2.3 p. 8 by the partial summation of
p. 9: on `SmallCubeFull ν`, Lemma 2.5 holds at `ϕ = (1 + 3ν)/4`. -/
def L23Bound (ν : ℝ) : Prop := BurgessPhiOn (SmallCubeFull ν) ((1 + 3 * ν) / 4)

/-- PROVED: a Burgess input on a class restricts to every subclass. -/
theorem burgessPhiOn_sub {S T : ℕ → Prop} {φ : ℝ} (hTS : ∀ q, T q → S q)
    (h : BurgessPhiOn S φ) : BurgessPhiOn T φ := by
  intro k hk ε hε
  obtain ⟨C, hC⟩ := h k hk ε hε
  exact ⟨C, fun q _ χ hq => hC q χ (hTS q hq)⟩

/-- PROVED: `ϕ` monotone on a class, as `U1563.burgessPhi_mono`. -/
theorem burgessPhiOn_mono {S : ℕ → Prop} {φ φ' : ℝ} (hφ : φ ≤ φ') (h : BurgessPhiOn S φ) :
    BurgessPhiOn S φ' := by
  intro k hk ε hε
  obtain ⟨C, hC⟩ := h k hk ε hε
  refine ⟨max C 0, fun q _ χ hq hχ h1 s hs1 hs2 => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ 1 + 1 / (k : ℝ) := by positivity
  have hexp : φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε ≤ φ' * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hφ (by linarith : 0 ≤ 1 - s.re)) hk0
    linarith
  calc _ ≤ C * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) :=
        hC q χ hq hχ h1 s hs1 hs2
    _ ≤ max C 0 * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) := by
        gcongr; exact le_max_left _ _
    _ ≤ _ := by
        have := Real.rpow_le_rpow_of_exponent_le hq1 hexp
        gcongr

/-- Vacuity for `L23Bound`: for `ν ≥ 1/9` it follows from the CITED all-moduli `ϕ = 1/3`. -/
theorem l23Bound_of_third {ν : ℝ} (hν : 1 / 9 ≤ ν) (hB : BurgessPhi (1 / 3)) : L23Bound ν :=
  burgessPhiOn_mono (by linarith) (burgessPhiOn_of_all hB)

/-! ## 3. The block and the conditional statement -/

/-- PROVED: every non-cube-free input at `ϕ` contains the prime-cube input at `ϕ`.  So a route
below 7/10 through U-1585's `SplitMethod` needs `BurgessPhiOn PrimeCube ϕ` with `ϕ < 1/3`, OPEN:
no surveyed bound reaches `p³`, see `primeCube_not_small`, `phiL23_one_ge`, `rad_primeCube`. -/
theorem primeCube_needed {φ : ℝ} (h : BurgessPhiOn NonCubeFree φ) : BurgessPhiOn PrimeCube φ :=
  burgessPhiOn_sub (fun _ hq => primeCube_nonCubeFree hq) h

/-- PROVED: the Lemma 2.3 input never reaches a prime cube, whatever `ν < 1`. -/
theorem l23_misses_primeCube {ν : ℝ} (hν : ν < 1) :
    ¬ ∀ q, PrimeCube q → SmallCubeFull ν q :=
  fun h => primeCube_not_small primeCube_eight hν (h 8 primeCube_eight)

/-- CONDITIONAL ON `SplitMethod I` CITED, `BurgessPhiOn CubeFree (1/4)` CITED KNOWN,
`BurgessPhiOn NonCubeFree 0.30` OPEN, and Section 4 closing at `(1/4, W)` and `(0.30, 3.183)`,
OPEN and MODEL: the exponent `1 - 1/3.183 < 0.6859 < 7/10`. -/
theorem exponent_030_of_split {I : List (List ℝ) → Prop} (hM : SplitMethod I) {W : ℝ}
    (hW3 : 3 ≤ W) (hW : W ≤ 3.183)
    (hc : BurgessPhiOn CubeFree (1 / 4)) (hn : BurgessPhiOn NonCubeFree 0.30)
    (hSc : Section4Closes (1 / 4) W I) (hSn : Section4Closes 0.30 3.183 I) :
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (1 - 1 / 3.183 + ε) := by
  intro ε hε
  have h := hM (1 / 4) 0.30 W 3.183 le_rfl (by norm_num) (by norm_num) (by norm_num) hW3 hW hc hn
    hSc hSn ε hε
  rwa [split_exponent_eq (by linarith) hW] at h

/-- Exponent arithmetic for `exponent_030_of_split`. -/
theorem exponent_030_lt : (1 : ℝ) - 1 / 3.183 < 0.6859 ∧ (0.6859 : ℝ) < 7 / 10 := by norm_num

end LeanLab.Routes.U1587

end
