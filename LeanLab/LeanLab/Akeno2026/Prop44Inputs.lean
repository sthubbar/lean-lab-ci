/-
P0087 M. Akeno, arXiv 2606.29559 v1. Unit U-1321, run 20261021T0203Z-29730.
The distribution inputs of the sieve argument of Section 4.1, at θ = 0.1635.

STATUS. Proposition 4.4 and the functional `M_k` could NOT be read: the arXiv HTML text
available to the lab ends inside the statement of Lemma 4.2, and ar5iv ends in Section 2.
So Proposition 4.4 is NOT stated here. What is formalized is the part that could be read:
the two residue bridges that turn the sieve remainders of Section 4.1 into the sums of
Theorem 1.1 and of the second sum of Theorem 3.1, the coprimality bookkeeping, the
specialisation of the cited theorems to θ = 0.1635 and to the weight `w` supported on
`[1/10, 2/10]`, and the numerical window of Lemma 4.2.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026
open Real
open scoped ContDiff

/-! ### Bridge 1: the original problem, sieving `r = m - n + 1`, goes to Theorem 1.1 -/

/-- For `m + n = N`: `d ∣ m - n + 1` iff `2m ≡ N - 1 (mod d)`. For odd `d` this is one
residue class `m ≡ l (mod d)`, the shape of Theorem 1.1. -/
theorem dvd_sieve_iff {d m n N : ℤ} (h : m + n = N) :
    d ∣ m - n + 1 ↔ 2 * m ≡ N - 1 [ZMOD d] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  have : 2 * m - (N - 1) = m - n + 1 := by omega
  rw [this]

/-- For odd `d` the class `2l ≡ N - 1` exists. -/
theorem exists_half_class {d : ℤ} (hd : Odd d) (N : ℤ) : ∃ l : ℤ, 2 * l ≡ N - 1 [ZMOD d] := by
  obtain ⟨k, rfl⟩ := hd
  refine ⟨-k * (N - 1), ?_⟩
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  exact ⟨-(N - 1), by ring⟩

theorem isCoprime_two_of_odd {d : ℤ} (hd : Odd d) : IsCoprime d 2 := by
  obtain ⟨k, rfl⟩ := hd
  exact ⟨1, -k, by ring⟩

/-- Transfer of coprimality along a congruence. -/
theorem isCoprime_congr {d a b : ℤ} (h : a ≡ b [ZMOD d]) : IsCoprime d a ↔ IsCoprime d b := by
  obtain ⟨t, ht⟩ := (Int.ModEq.dvd h)
  have hb : b = a + d * t := by linarith
  rw [hb, IsCoprime.add_mul_left_right_iff]

/-- For odd `d` and `2l ≡ N - 1 (mod d)`, the admissibility condition `(d, l(N - l)) = 1` of
Theorem 1.1 is exactly `(d, N² - 1) = 1`, which is why `𝔗(N)` of Section 4.1 distinguishes
`p ∣ N(N² - 1)`. Key identity: `4 l (N - l) ≡ (N - 1)(N + 1)`. -/
theorem admissible_iff_coprime_sq_sub_one {d l N : ℤ} (hd : Odd d)
    (hl : 2 * l ≡ N - 1 [ZMOD d]) :
    Int.gcd d (l * (N - l)) = 1 ↔ Int.gcd d (N ^ 2 - 1) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one, ← Int.isCoprime_iff_gcd_eq_one]
  have h2 := isCoprime_two_of_odd hd
  have h4 : IsCoprime d 4 := by
    have := h2.mul_right h2; norm_num at this; exact this
  have hcong : 4 * (l * (N - l)) ≡ N ^ 2 - 1 [ZMOD d] := by
    have e1 : 4 * (l * (N - l)) = (2 * l) * (2 * N - 2 * l) := by ring
    have e2 : N ^ 2 - 1 = (N - 1) * (2 * N - (N - 1)) := by ring
    rw [e1, e2]
    exact hl.mul (Int.ModEq.sub_left _ hl)
  rw [← isCoprime_congr hcong, IsCoprime.mul_right_iff (y := 4)]
  exact ⟨fun h => ⟨h4, h⟩, fun h => h.2⟩

/-! ### Bridge 2: the switched problem goes to the second sum of Theorem 3.1 at `N + 1` -/

/-- Switching: `m + n = N` with `r = m - n + 1` is the same as `2n + r = N + 1` with
`m = N - n`. The paper's introduction names the equation `2m + n = N + 1`. -/
theorem switch_iff {m n r N : ℤ} :
    (m + n = N ∧ r = m - n + 1) ↔ (2 * n + r = N + 1 ∧ m = N - n) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/-- In the switched problem the sieved variable is `m = N - n`, and `d ∣ N - n` is the single
class `n ≡ N (mod d)` on the `Λ` variable, the shape of the second sum of Theorem 3.1. -/
theorem switched_dvd_iff {d n N : ℤ} : d ∣ N - n ↔ n ≡ N [ZMOD d] :=
  (Int.modEq_iff_dvd).symm

/-- The admissibility condition `(d, l(N' - 2l)) = 1` of the second sum of Theorem 3.1, at
`N' = N + 1` and `l = N`, is `(d, N(N - 1)) = 1`. -/
theorem switched_admissible_iff (d N : ℤ) :
    Int.gcd d (N * ((N + 1) - 2 * N)) = 1 ↔ Int.gcd d (N * (N - 1)) = 1 := by
  have : N * ((N + 1) - 2 * N) = -(N * (N - 1)) := by ring
  rw [this, Int.gcd_neg]

/-- The natural-number form used by `betaSum'`: for `N ≥ 1` the switched `N' = N + 1` is odd
exactly when `N` is even, so `S'(N + 1)` is the nonzero branch of `singSeries'`. -/
theorem switched_odd {N : ℕ} (hN : Even N) : ¬ 2 ∣ N + 1 := by
  obtain ⟨k, rfl⟩ := hN; omega

/-! ### Specialisation of the cited statements -/

/-- Smaller `η` is weaker: a weight supported on `[η, 1]` is supported on `[η', 1]`. -/
theorem smoothWeight_mono {η' η : ℝ} (h : η' ≤ η) {w : ℝ → ℝ} (hw : SmoothWeight η w) :
    SmoothWeight η' w :=
  ⟨hw.1, hw.2.trans (Set.Icc_subset_Icc_left h)⟩

/-- The weight of Section 4.1, smooth with support in `[1/10, 2/10]`, is admissible for every
`η ≤ 1/10`. -/
theorem smoothWeight_tenth {η : ℝ} (hη : η ≤ 1 / 10) {w : ℝ → ℝ} (hs : ContDiff ℝ ∞ w)
    (hw : Function.support w ⊆ Set.Icc (1 / 10) (2 / 10)) : SmoothWeight η w :=
  ⟨hs, hw.trans (Set.Icc_subset_Icc hη (by norm_num))⟩

/-- CONDITIONAL ON `akeno_thm1_1` and `akeno_thm3_1`, passed as hypotheses `h11`, `h31`.
At `θ = 0.1635` the Goldbach primes have level `0.1635` in the sense of Theorem 1.1, and there
is `η ∈ (0, 1/10]` for which both sums of Theorem 3.1 have level `0.1635` and the Section 4.1
weight on `[1/10, 2/10]` is admissible. -/
theorem inputs_0_1635
    (h11 : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 → LevelGP θ)
    (h31 : ∀ θ : ℝ, 0 < θ → θ < 1 / 6 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → BetaLevel θ η) :
    LevelGP 0.1635 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 10 ∧ BetaLevel 0.1635 η ∧
      ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → Function.support w ⊆ Set.Icc (1 / 10) (2 / 10) →
        SmoothWeight η w := by
  refine ⟨h11 _ (by norm_num) (by norm_num), ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := h31 0.1635 (by norm_num) (by norm_num)
  refine ⟨min η₀ (1 / 10), lt_min hη₀ (by norm_num), min_le_right _ _,
    h _ (lt_min hη₀ (by norm_num)) (min_le_left _ _), ?_⟩
  intro w hs hw
  exact smoothWeight_tenth (min_le_right _ _) hs hw

/-- The same, directly from the cited Lean statements. CONDITIONAL ON `akeno_thm1_1`,
`akeno_thm3_1`, which carry `sorry`. -/
theorem inputs_0_1635_cited :
    LevelGP 0.1635 ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 10 ∧ BetaLevel 0.1635 η ∧
      ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w → Function.support w ⊆ Set.Icc (1 / 10) (2 / 10) →
        SmoothWeight η w :=
  inputs_0_1635 akeno_thm1_1 akeno_thm3_1

/-! ### Numerical window of Lemma 4.2 at `θ = 0.1635`, `s = 33.5` -/

/-- Lemma 4.2 needs `1/s < θ < 1/6`; Section 4.1 needs `s > 2`. Also `sθ > 2`, so `ω⁻(sθ)`
is past the range `sθ ≤ 2` where Lemma 4.1 sets it to `0`. -/
theorem lemma4_2_window :
    (2 : ℝ) < 33.5 ∧ 1 / (33.5 : ℝ) < 0.1635 ∧ (0.1635 : ℝ) < 1 / 6 ∧
      (2 : ℝ) < 33.5 * 0.1635 := by
  norm_num

/-! ### Vacuity tests, concrete instances where the hypotheses hold -/

/-- `N = 10, m = 7, n = 3, r = 5`, `d = 5`: `2·3 + 5 = 11 = N + 1`, `5 ∣ 7 - 3 + 1`,
`2·7 ≡ 9 (mod 5)`. -/
example : (7 : ℤ) + 3 = 10 ∧ (5 : ℤ) = 7 - 3 + 1 := by norm_num
example : (2 : ℤ) * 3 + 5 = 10 + 1 ∧ (7 : ℤ) = 10 - 3 :=
  (switch_iff (m := 7) (n := 3) (r := 5) (N := 10)).1 (by norm_num)
example : (5 : ℤ) ∣ 7 - 3 + 1 := (dvd_sieve_iff (d := 5) (m := 7) (n := 3) (N := 10) rfl).2
  (by decide)
/-- `d = 7, N = 10, l = 1`: `2·1 ≡ 9 (mod 7)`, `(7, 1·9) = 1` and `(7, 99) = 1`. -/
example : Int.gcd 7 (1 * (10 - 1)) = 1 :=
  (admissible_iff_coprime_sq_sub_one (d := 7) (l := 1) (N := 10) ⟨3, by norm_num⟩
    (by decide)).2 (by decide)

end LeanLab.Akeno2026
