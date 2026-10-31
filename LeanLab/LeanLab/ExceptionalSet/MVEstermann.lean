/-
Estermann 1938 on the concrete circle method data, CONDITIONAL, unit U-1031, run
20261019T0503Z-10740, T2, P0091 Estermann 1938 and P0015 skeleton. AI wrote this Lean code.

`MVLogInputs` and `MVSupInputs` ask for some `Φ`, `m`, `T`. Here they are fixed:
`M = 2x + 1`, `Φ(j) = log p` when `j` is a prime `p ≤ x`, so `𝓕 Φ k = S(-k/M)` with
`S(α) = Σ_{p ≤ x} log p e(pα)`; the major arcs are
`|k/M - a/q| ≤ Q/M`, `q ≤ Q`, at `Q = (log x)^B`, the minor arcs their complement; and
`T = M x / 4`. Two standard inputs are stated as named Props, NOT proved here:
* `VinogradovMinor`: Vinogradov's bound `|S(α)| ≤ C x/(log x)^A` on the minor arcs;
* `MajorArcCount`: all but `O(x/(log x)^A)` even `n ∈ (x/2, x]` have major arc part above
  `M x / 4`; the major part is `M (𝔖_Q(n) n + O(x/(log x)^A))` by Siegel-Walfisz, and the
  truncated singular series is at least `2 C₂ > 1.32`, up to a factor `1 + o(1)`, for all
  but few `n`, see Routes/R0005RandomModel.lean for its local factors.
`estermann_of_cited` derives `LogPowerSaving` from them. KNOWN mathematics: Estermann 1938,
Vaughan 1977 Chapter 3. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.MVLogInputs

open ZMod Finset Real

namespace LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-- the modulus `M = 2x + 1 > 2x` -/
def Mx (x : ℕ) : ℕ := 2 * x + 1

instance instNeZeroMx (x : ℕ) : NeZero (Mx x) := ⟨by unfold Mx; omega⟩

/-- `Φ(j) = log p` on the primes `p ≤ x`, zero elsewhere -/
noncomputable def logPrimes (x : ℕ) : ZMod (Mx x) → ℂ :=
  fun j => if (ZMod.val j).Prime ∧ ZMod.val j ≤ x then (Real.log (ZMod.val j) : ℂ) else 0

/-- the major arcs at level `Q`: `|k/M - a/q| ≤ Q/M` for some `1 ≤ q ≤ Q`, `a ∈ ℤ`, width
`Q/M` for every `q`, as in Vaughan's book, Chapter 3. Width `Q/(qM)` would leave tails of the
singular integral of the size of the main term for `q` near `Q`, run 20261019T0503Z-10740. -/
noncomputable def majorArcs (x : ℕ) (Q : ℝ) : Finset (ZMod (Mx x)) :=
  univ.filter (fun k => ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ ∃ a : ℤ,
    |(ZMod.val k : ℝ) / (Mx x) - (a : ℝ) / q| ≤ Q / (Mx x))

/-- the minor arcs, the complement -/
noncomputable def minorArcs (x : ℕ) (Q : ℝ) : Finset (ZMod (Mx x)) := (majorArcs x Q)ᶜ

/-- CITED. Vinogradov 1937 as used by Estermann: for every `A`, for `B` large, the exponential
sum over primes is at most `C x/(log x)^A` on the minor arcs at `Q = (log x)^B`. -/
def VinogradovMinor : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, ∀ B : ℝ, B0 ≤ B → ∃ (C : ℝ) (X0 : ℕ), ∀ x : ℕ, X0 ≤ x →
    ∀ k ∈ minorArcs x (Real.log x ^ B), ‖𝓕 (logPrimes x) k‖ ≤ C * x / Real.log x ^ A

/-- CITED. The major arc count: for every `A`, for `B` large, at most `C x/(log x)^A` even
`n ∈ (x/2, x]` have major arc part of modulus at most `M x / 4`. -/
def MajorArcCount : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, ∀ B : ℝ, B0 ≤ B → ∃ (C : ℝ) (X0 : ℕ), ∀ x : ℕ, X0 ≤ x →
    ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
        ‖majorPart (logPrimes x) (minorArcs x (Real.log x ^ B)) (n : ZMod (Mx x))‖
          ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ) ≤ C * x / Real.log x ^ A

/-- `|Φ(j)| ≤ log x` -/
theorem norm_logPrimes_le (x : ℕ) (j : ZMod (Mx x)) : ‖logPrimes x j‖ ≤ Real.log x := by
  unfold logPrimes
  split_ifs with h
  · have hp := h.1.two_le
    have h0 : 0 ≤ Real.log (ZMod.val j) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ ZMod.val j))
    rw [Complex.norm_real, Real.norm_of_nonneg h0]
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < ZMod.val j)) (by exact_mod_cast h.2)
  · simp only [norm_zero]
    exact Real.log_natCast_nonneg x

/-- `Σ_j |Φ(j)|² ≤ M (log x)²` -/
theorem sum_sq_logPrimes_le (x : ℕ) :
    ∑ j, ‖logPrimes x j‖ ^ 2 ≤ (Mx x : ℝ) * Real.log x ^ 2 := by
  calc ∑ j, ‖logPrimes x j‖ ^ 2 ≤ ∑ _j : ZMod (Mx x), Real.log x ^ 2 := by
        apply sum_le_sum; intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_logPrimes_le x j) 2
    _ = (Mx x : ℝ) * Real.log x ^ 2 := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- the support hypothesis for `logPrimes` -/
theorem primeSupported_logPrimes' (x : ℕ) : PrimeSupported (logPrimes x) x := by
  intro j hj
  by_contra h
  exact hj (by simp [logPrimes, h])

/-- the minor arc term at `T = M x / 4` with a sup bound `U = C x/(log x)^A'` is at most
`48 C² x / (log x)^(2A' - 2)` -/
theorem minorTerm_bound (x : ℕ) (hx : 3 ≤ x) (C A' : ℝ) :
    (Mx x : ℝ) * ((C * x / Real.log x ^ A') ^ 2 * ((Mx x : ℝ) * ∑ j, ‖logPrimes x j‖ ^ 2)) /
        ((Mx x : ℝ) * x / 4) ^ 2
      ≤ 48 * C ^ 2 * x / Real.log x ^ (2 * A' - 2) := by
  have hx0 : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hM : (Mx x : ℝ) = 2 * x + 1 := by unfold Mx; push_cast; ring
  have hL : 1 < Real.log x := by
    have : Real.exp 1 < x := by have := Real.exp_one_lt_d9; linarith
    rw [Real.lt_log_iff_exp_lt (by linarith)]; exact this
  have hS := sum_sq_logPrimes_le x
  set L := Real.log x with hLdef
  have hLpos : 0 < L := by linarith
  have hLA : 0 < L ^ A' := Real.rpow_pos_of_pos hLpos _
  have hLB : 0 < L ^ (2 * A' - 2) := Real.rpow_pos_of_pos hLpos _
  have hpow : (L ^ A') ^ 2 = L ^ (2 * A' - 2) * L ^ 2 := by
    rw [← Real.rpow_two L, ← Real.rpow_add hLpos, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
    rw [mul_comm]
  have hMpos : (0 : ℝ) < Mx x := by rw [hM]; linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hM3 : (Mx x : ℝ) ≤ 3 * x := by rw [hM]; linarith
  set S := ∑ j, ‖logPrimes x j‖ ^ 2 with hSdef
  have e : (Mx x : ℝ) * ((C * x / L ^ A') ^ 2 * ((Mx x : ℝ) * S)) / ((Mx x : ℝ) * x / 4) ^ 2
      = 16 * C ^ 2 * S / (L ^ A') ^ 2 := by
    field_simp; ring
  rw [e]
  calc 16 * C ^ 2 * S / (L ^ A') ^ 2 ≤ 16 * C ^ 2 * ((Mx x : ℝ) * L ^ 2) / (L ^ A') ^ 2 := by
        gcongr
    _ ≤ 16 * C ^ 2 * (3 * x * L ^ 2) / (L ^ A') ^ 2 := by gcongr
    _ = 48 * C ^ 2 * x / L ^ (2 * A' - 2) := by
        rw [hpow]; field_simp; ring

/-- the concrete data satisfy `MVSupInputs` at every log power, from the two cited inputs -/
theorem mvSupInputs_of_cited (hV : VinogradovMinor) (hMa : MajorArcCount) :
    ∀ A : ℝ, 0 < A → ∃ (C₁ C₂ : ℝ) (X0 : ℕ), MVSupInputs A C₁ C₂ X0 := by
  intro A hA
  set A' : ℝ := (A + 2) / 2 with hA'
  have hA'pos : 0 < A' := by rw [hA']; linarith
  have h2A : 2 * A' - 2 = A := by rw [hA']; ring
  obtain ⟨Bv, hBv⟩ := hV A' hA'pos
  obtain ⟨Bm, hBm⟩ := hMa A hA
  set B := max Bv Bm with hB
  obtain ⟨Cv, Xv, hv⟩ := hBv B (le_max_left _ _)
  obtain ⟨Cm, Xm, hm⟩ := hBm B (le_max_right _ _)
  refine ⟨Cm, 48 * Cv ^ 2, max (max Xv Xm) 3, ?_⟩
  intro x hx
  have hxv : Xv ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxm : Xm ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  refine ⟨Mx x, by unfold Mx; omega, by unfold Mx; omega, logPrimes x,
    minorArcs x (Real.log x ^ B), (Mx x : ℝ) * x / 4, Cv * x / Real.log x ^ A',
    primeSupported_logPrimes' x, ?_, hv x hxv, hm x hxm, ?_⟩
  · have : (0 : ℝ) < Mx x := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne _))
    positivity
  · have := minorTerm_bound x hx3 Cv A'
    rw [h2A] at this
    exact this

/-- **Estermann 1938, CONDITIONAL ON `VinogradovMinor` and `MajorArcCount`**: almost all even
numbers are Goldbach numbers, `E(X) ≪_A X/(log X)^A` for every `A`. -/
theorem estermann_of_cited (hV : VinogradovMinor) (hMa : MajorArcCount) : LogPowerSaving :=
  logPowerSaving_of_supInputs (mvSupInputs_of_cited hV hMa)

/-- vacuity: the major arcs are not empty, `k = 0` lies on them at `q = 1`, `a = 0`,
whenever `Q ≥ 1` -/
theorem zero_mem_majorArcs (x : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) : (0 : ZMod (Mx x)) ∈ majorArcs x Q := by
  simp only [majorArcs, mem_filter, mem_univ, true_and]
  refine ⟨1, le_rfl, by simpa using hQ, 0, ?_⟩
  simp only [ZMod.val_zero, Nat.cast_zero, zero_div, Int.cast_zero, sub_zero, abs_zero]
  have : (0 : ℝ) < Mx x := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne _))
  positivity

#print axioms norm_logPrimes_le
#print axioms sum_sq_logPrimes_le
#print axioms minorTerm_bound
#print axioms mvSupInputs_of_cited
#print axioms estermann_of_cited
#print axioms zero_mem_majorArcs

end LeanLab.ExceptionalSet.MV
