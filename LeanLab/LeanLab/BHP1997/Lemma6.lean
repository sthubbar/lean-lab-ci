/-
P0069 Baker, Harman, Pintz 1997, Lemma 6, page 21, read from the page images
papers/P0069-original.pdf. Unit U-5066, CLOUD 20261019T0213Z-cloud14.

PROVED: `iteratedDeriv_tlog`, for `f(ν) = t log(qν + r)` and `qν + r > 0`,
`f^{(j)}(ν) = t (-1)^{j-1} (j-1)! q^j / (qν + r)^j` for `j ≥ 1`, so with `qν + r ≍ N`,
`|f^{(j)}(ν)| ≍ |t| q^j N^{-j}`; and the exponent step of (3.35): for `K = 2^{j-1}` with
`j ≥ 3`, both van der Corput terms are at most `N^{1-2η}` with an explicit `η > 0`.
FINDING, cosmetic: the page prints `|f^{(j)}(ν)| ≍ |t| q^{2j} N^{-j}`; the true size has `q^j`.
Since `q ≤ ℒ^A` and `j = O(1)` the two differ by at most a power of ℒ, so the choice of `j` and
(3.35) survive. `printed_ratio`: the printed and true sizes differ by exactly `q^j`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma6

open Real

/-- The closed form of the `j`-th derivative, `j ≥ 1`. -/
noncomputable def g (t q r : ℝ) (j : ℕ) (ν : ℝ) : ℝ :=
  t * (-1) ^ j * (j.factorial : ℝ) * q ^ (j + 1) / (q * ν + r) ^ (j + 1)

lemma hasDerivAt_g (t q r : ℝ) (j : ℕ) {ν : ℝ} (hν : 0 < q * ν + r) :
    HasDerivAt (g t q r j) (g t q r (j + 1) ν) ν := by
  unfold g
  have hlin : HasDerivAt (fun ν => q * ν + r) q ν := by
    simpa using ((hasDerivAt_id ν).const_mul q).add_const r
  have hpow := hlin.pow (j + 1)
  have hne : (q * ν + r) ^ (j + 1) ≠ 0 := pow_ne_zero _ hν.ne'
  have hd := (hasDerivAt_const ν (t * (-1) ^ j * (j.factorial : ℝ) * q ^ (j + 1))).div hpow hne
  convert hd using 1
  simp only [Pi.pow_apply]
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- `f^{(j+1)}(ν) = t (-1)^j j! q^{j+1}/(qν + r)^{j+1}` on `qν + r > 0`. -/
theorem iteratedDeriv_tlog (t q r : ℝ) (j : ℕ) {ν : ℝ} (hν : 0 < q * ν + r) :
    iteratedDeriv (j + 1) (fun ν => t * Real.log (q * ν + r)) ν = g t q r j ν := by
  have hopen : IsOpen {ν : ℝ | 0 < q * ν + r} :=
    isOpen_lt continuous_const (by fun_prop)
  -- the statement on the open set, by induction
  have key : ∀ j : ℕ, ∀ ν, 0 < q * ν + r →
      iteratedDeriv (j + 1) (fun ν => t * Real.log (q * ν + r)) ν = g t q r j ν := by
    intro j
    induction j with
    | zero =>
      intro ν hν
      rw [iteratedDeriv_one]
      have hlin : HasDerivAt (fun ν => q * ν + r) q ν := by
        simpa using ((hasDerivAt_id ν).const_mul q).add_const r
      have := (hlin.log hν.ne').const_mul t
      rw [this.deriv]
      unfold g; simp; ring
    | succ n ih =>
      intro ν hν
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv (n + 1) (fun ν => t * Real.log (q * ν + r)) =ᶠ[nhds ν]
          g t q r n := by
        filter_upwards [hopen.mem_nhds hν] with y hy using ih y hy
      rw [hev.deriv_eq]
      exact (hasDerivAt_g t q r n hν).deriv
  exact key j ν hν

/-- The printed size `|t| q^{2j} N^{-j}` is the true size `|t| q^j N^{-j}` times `q^j`. -/
theorem printed_ratio (t q N : ℝ) (j : ℕ) :
    |t| * q ^ (2 * j) * N ^ (-(j : ℤ)) = (|t| * q ^ j * N ^ (-(j : ℤ))) * q ^ j := by
  rw [two_mul, pow_add]; ring

/-- (3.35), the exponents: for `K ≥ 4`, the terms `N (N^{-1/2})^{1/(2K-2)}` and
`N^{1 - 2/K + 3/(4K-4)}` are at most `N^{1-2η}` with `η = (2/K - 3/(4K-4))/2 > 0`, which is
below `1/(8K - 8)` as well, so one `η` serves both. -/
theorem eq335_exponents {K : ℝ} (hK : 4 ≤ K) :
    let η := min (1 / (8 * K - 8)) ((2 / K - 3 / (4 * K - 4)) / 2)
    0 < η ∧ 1 - 1 / 2 * (1 / (2 * K - 2)) ≤ 1 - 2 * η ∧
      1 - 2 / K + 3 / (4 * K - 4) ≤ 1 - 2 * η := by
  intro η
  have h1 : 0 < 8 * K - 8 := by linarith
  have h2 : 0 < 4 * K - 4 := by linarith
  have hK0 : 0 < K := by linarith
  have hpos : 0 < 2 / K - 3 / (4 * K - 4) := by
    rw [sub_pos, div_lt_div_iff₀ h2 hK0]; linarith
  refine ⟨lt_min (by positivity) (by linarith), ?_, ?_⟩
  · have := min_le_left (1 / (8 * K - 8)) ((2 / K - 3 / (4 * K - 4)) / 2)
    have e : 1 / 2 * (1 / (2 * K - 2)) = 2 * (1 / (8 * K - 8)) := by
      field_simp; ring
    linarith
  · have := min_le_right (1 / (8 * K - 8)) ((2 / K - 3 / (4 * K - 4)) / 2)
    linarith

/-- `j ≥ 3` gives `K = 2^{j-1} ≥ 4`. -/
theorem K_ge (j : ℕ) (hj : 3 ≤ j) : (4 : ℝ) ≤ 2 ^ (j - 1) := by
  have : (2 : ℝ) ^ 2 ≤ 2 ^ (j - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at this ⊢; exact this

/-- U-5160, the choice of `j`: in units of `log N`, `|t|q^jN^{-j}` is `u - js` with `s = 1 - log q/log N`
in `(0, 1]`; for `u ≥ -1/2` some `j` gives `N^{-3/2} ≤ |t|q^jN^{-j} < N^{-1/2}`, and
`j ≤ (u + 1/2)/s + 1`, which is `O(1)` for `q ≤ ℒ^A`, `|t| ≤ x`, `N ≥ x^ε`. The claim `j ≥ 3` is not
formalized here. -/
theorem choose_j {u s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hu : -1 / 2 ≤ u) :
    ∃ j : ℕ, -3 / 2 ≤ u - j * s ∧ u - j * s < -1 / 2 ∧ (j : ℝ) ≤ (u + 1 / 2) / s + 1 := by
  set y := (u + 1 / 2) / s
  have hy : 0 ≤ y := div_nonneg (by linarith) hs.le
  refine ⟨⌊y⌋₊ + 1, ?_, ?_, ?_⟩
  · have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    have h2 : y * s = u + 1 / 2 := by simp only [y]; field_simp
    push_cast
    nlinarith
  · have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
    have h2 : y * s = u + 1 / 2 := by simp only [y]; field_simp
    push_cast
    nlinarith
  · push_cast
    linarith [Nat.floor_le hy]

/-- U-5163, the cases `j ≤ 2` the page's 'Then j ≥ 3' omits, in units of `log N`, `|t| = N^τ`,
`0 ≤ τ ≤ 3/2`, `0 < η ≤ 1/8`: if `τ ≥ 4η` the second derivative test exponents `τ/2` and `1 - τ/2` are
at most `1 - 2η`, the bound (3.35). For `τ < 4η` the first derivative test gives `N/|t|`, exponent
`1 - τ`, which is the lemma's second term; that case needs no comparison. -/
theorem small_j_second_deriv {τ η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 8) (hτ : τ ≤ 3 / 2)
    (h4 : 4 * η ≤ τ) : τ / 2 ≤ 1 - 2 * η ∧ 1 - τ / 2 ≤ 1 - 2 * η := by
  constructor <;> linarith

end LeanLab.BHP1997.Lemma6
