import LeanLab.ExceptionalSet.Decomp385a

/-!
Split of the sealed statement `leaf_mean_square` of `LeanLab.ExceptionalSet.Decomp385a` into
three strictly smaller steps, plus an assembly `leaf_mean_square_split` whose statement is the
sealed statement and whose proof uses only the three leaves.

`leaf_mean_square` bounds the second moment of the even weighted error: for `1/2 ≤ Θ < 3/4`, a
zero-free region past `Θ` and `0 < ε < 3/2 - 2Θ`, the sum of `error n ^ 2` over the even
`n ≤ X` is at most `C X ^ (3/2 + 2 Θ + ε)`.  The split keeps the analytic content at a single
scale, which is where the uniform arc estimate is needed, and reduces the passage from one scale
to the whole prefix to an elementary induction that halves the range.

The steps are:
* `leaf_window_energy_four_dvd` and `leaf_window_energy_four_not_dvd`: the second moment over one
  window `(Y/2, Y]`, separated into the even indices divisible by `4` and the even indices not
  divisible by `4`.  These are the two classes of the singular series: only the indices divisible
  by `4` carry the prime `2` in the Euler product of `Sing`, and the two classes are of different
  shape there.  Each leaf sums over a subset of a single window, so each is strictly weaker than
  the prefix statement, which sums over every scale at once.
* `leaf_coarse_even_energy`: an unconditional second moment bound with the much larger exponent
  `5`, which uses no zero-free region at all and needs only a pointwise polynomial size for
  `error`.  It controls the ranges below the window threshold and it is what makes the induction
  start.

The assembly does the bookkeeping: split the prefix at the half `⌊X/2⌋`, bound the window at the
larger scale by the two window leaves and the prefix at half the scale by the induction
hypothesis, and sum the geometric constant `2^p / (2^p - 1)`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- LEAF 1 of 3, the coarse step: the unconditional second moment bound with exponent `5` for the
whole even prefix.  This is the whole-prefix statement with an exponent far above the analytic one,
so no zero-free region is involved: a pointwise polynomial size for `error` and the number of
terms suffice.  It is the start of the induction in the assembly. -/
theorem leaf_coarse_even_energy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ∑ n ∈ (Finset.range (X + 1)).filter Even, (error n) ^ 2 ≤ C * (X : ℝ) ^ 5 := by
  sorry

/-- LEAF 2 of 3, one scale of the analytic step, on the even indices divisible by `4`: some
nonnegative `C` bounds the second moment over the window `(Y/2, Y]` restricted to the even `n`
with `4 ∣ n`, by `C Y ^ (3/2 + 2 Θ + ε)`, for every `Y` past a fixed threshold.  This is a sum
over a subset of one window, not over the prefix.  It is where the uniform arc estimate from the
zero-free region enters. -/
theorem leaf_window_energy_four_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF 3 of 3, the other class of the same scale: the second moment over the window `(Y/2, Y]`
restricted to the even `n` with `4 ∤ n`, that is `n ≡ 2 (mod 4)`, with the same exponent.  At these
indices the prime `2` contributes to the singular series only through the constant `2 C₀`, which is
why the class is estimated separately.  Strictly easier than the prefix statement: one window, one
class. -/
theorem leaf_window_energy_four_not_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The geometric constant step: if `K` dominates `Cw * 2^p / (2^p - 1)` then `Cw` plus the half
of `K` in the scale `2^p` still fits inside `K`.  This is the inequality that makes the halving
induction of the assembly close. -/
private lemma const_step {Cw K p : ℝ} (hp : 0 < p)
    (hK : Cw * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤ K) :
    K / (2 : ℝ) ^ p + Cw ≤ K := by
  have ht1 : (1 : ℝ) < (2 : ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ p - 1 := by linarith
  have htpos : (0 : ℝ) < (2 : ℝ) ^ p := by linarith
  have hA : Cw * (2 : ℝ) ^ p ≤ K * ((2 : ℝ) ^ p - 1) := by
    rw [div_le_iff₀ ht0] at hK
    linarith
  have hkey : K / (2 : ℝ) ^ p + Cw = (K + Cw * (2 : ℝ) ^ p) / (2 : ℝ) ^ p := by
    field_simp
  rw [hkey, div_le_iff₀ htpos]
  linarith

/-- Splitting the even prefix at `m ≤ X`: the terms with `n < m` and the terms `m ≤ n ≤ X`. -/
private lemma sum_window_split {f : ℕ → ℝ} {m X : ℕ} (hm : m ≤ X) :
    ∑ n ∈ (Finset.range (X + 1)).filter Even, f n =
      ∑ n ∈ (Finset.range m).filter Even, f n + ∑ n ∈ (Finset.Icc m X).filter Even, f n := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_range_add_sum_Ico (fun n => if Even n then f n else 0)
    (by omega : m ≤ X + 1)]
  rw [Finset.Ico_add_one_right_eq_Icc]

/-- Splitting the even terms of an interval into the class divisible by `4` and its complement. -/
private lemma window_four_split {f : ℕ → ℝ} {a b : ℕ} :
    ∑ n ∈ (Finset.Icc a b).filter Even, f n =
      ∑ n ∈ (Finset.Icc a b).filter (fun n => Even n ∧ 4 ∣ n), f n
        + ∑ n ∈ (Finset.Icc a b).filter (fun n => Even n ∧ ¬ 4 ∣ n), f n := by
  have hpoint : ∀ n : ℕ, (if Even n then f n else 0) =
      (if Even n ∧ 4 ∣ n then f n else 0) + (if Even n ∧ ¬ 4 ∣ n then f n else 0) := by
    intro n
    by_cases h1 : Even n
    · by_cases h2 : (4 : ℕ) ∣ n
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun n _ => hpoint n)

/-- `leaf_mean_square` of `LeanLab.ExceptionalSet.Decomp385a`, assembled from the three leaves:
the coarse prefix bound starts the induction, the two window leaves bound one scale, and the
prefix at half the scale comes from the induction hypothesis. -/
theorem leaf_mean_square_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨Cc, hCc0, hcoarse⟩ := leaf_coarse_even_energy
  obtain ⟨C4, hC40, Y4, hY4, hwin4⟩ :=
    leaf_window_energy_four_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC20, Y2, hY2, hwin2⟩ :=
    leaf_window_energy_four_not_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  set p : ℝ := 3 / 2 + 2 * Θ + ε with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  set Cw : ℝ := C4 + C2 with hCwdef
  have hCw0 : 0 ≤ Cw := by rw [hCwdef]; linarith
  set N₁ : ℕ := max (max Y4 Y2) 2 with hN1def
  have hN1ge : 1 ≤ N₁ := by rw [hN1def]; omega
  have hY4N : Y4 ≤ N₁ := by rw [hN1def]; omega
  have hY2N : Y2 ≤ N₁ := by rw [hN1def]; omega
  set K : ℝ := max (Cw * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) (Cc * (N₁ : ℝ) ^ 5) with hKdef
  have hKN : Cc * (N₁ : ℝ) ^ 5 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hKc : Cw * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤ K := by
    rw [hKdef]; exact le_max_left _ _
  have hK0 : 0 ≤ K := le_trans (by positivity) hKN
  have hwin4' : ∀ Y : ℕ, N₁ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2 ≤
        C4 * (Y : ℝ) ^ p := by
    intro Y hY
    exact hwin4 Y (le_trans hY4N hY)
  have hwin2' : ∀ Y : ℕ, N₁ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C2 * (Y : ℝ) ^ p := by
    intro Y hY
    exact hwin2 Y (le_trans hY2N hY)
  refine ⟨K, N₁, ?_⟩
  have key : ∀ X : ℕ, N₁ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤ K * (X : ℝ) ^ p := by
    intro X
    refine Nat.strong_induction_on X ?_
    intro X ih hX
    by_cases hsmall : X ≤ N₁
    · -- below the threshold: the coarse bound at the threshold
      have hX1 : 1 ≤ X := le_trans hN1ge hX
      have hmono : ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2
          ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          exact ⟨by omega, hn.2⟩
        · intro n _ _
          positivity
      have hXp1 : (1 : ℝ) ≤ (X : ℝ) ^ p := by
        have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
        calc (1 : ℝ) = (1 : ℝ) ^ p := by simp
          _ ≤ (X : ℝ) ^ p := Real.rpow_le_rpow (by norm_num) hXR hp0.le
      calc ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2
          ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := hmono
        _ ≤ Cc * (N₁ : ℝ) ^ 5 := hcoarse N₁ hN1ge
        _ ≤ K := hKN
        _ = K * 1 := by ring
        _ ≤ K * (X : ℝ) ^ p := mul_le_mul_of_nonneg_left hXp1 hK0
    · -- above the threshold: one window plus the prefix at half the scale
      have hXgt : N₁ < X := lt_of_not_ge hsmall
      have hX1 : 1 ≤ X := by omega
      have hX2 : 2 ≤ X := by omega
      have hhalf_lt : X / 2 < X := Nat.div_lt_self (by omega : 0 < X) (by norm_num)
      have hw : ∑ n ∈ (Icc (X / 2 + 1) X).filter Even, (error n) ^ 2 ≤ Cw * (X : ℝ) ^ p := by
        have hfour := window_four_split (f := fun n => (error n) ^ 2) (a := X / 2 + 1) (b := X)
        rw [hfour]
        have h4 := hwin4' X (le_of_lt hXgt)
        have h2 := hwin2' X (le_of_lt hXgt)
        calc ∑ n ∈ (Icc (X / 2 + 1) X).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2
            + ∑ n ∈ (Icc (X / 2 + 1) X).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2
            ≤ C4 * (X : ℝ) ^ p + C2 * (X : ℝ) ^ p := add_le_add h4 h2
          _ = (C4 + C2) * (X : ℝ) ^ p := by ring
          _ = Cw * (X : ℝ) ^ p := by rw [hCwdef]
      have hpre : ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
          ≤ K * ((X : ℝ) / 2) ^ p := by
        have hhalf : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
          have h := Nat.div_mul_le_self X 2
          have h' : ((X / 2 : ℕ) : ℝ) * 2 ≤ (X : ℝ) := by exact_mod_cast h
          linarith
        by_cases hmid : N₁ ≤ X / 2
        · have h := ih (X / 2) hhalf_lt hmid
          have hmono := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg (X / 2)) hhalf hp0.le) hK0
          exact le_trans h hmono
        · have hmid' : X / 2 ≤ N₁ := le_of_lt (lt_of_not_ge hmid)
          have hmono : ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
              ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
              exact ⟨by omega, hn.2⟩
            · intro n _ _
              positivity
          have hco := hcoarse N₁ hN1ge
          have hbase : ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2 ≤ K := by
            calc ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
                ≤ ∑ n ∈ (range (N₁ + 1)).filter Even, (error n) ^ 2 := hmono
              _ ≤ Cc * (N₁ : ℝ) ^ 5 := hco
              _ ≤ K := hKN
          have hhalf1 : (1 : ℝ) ≤ ((X : ℝ) / 2) ^ p := by
            have hXR : (1 : ℝ) ≤ (X : ℝ) / 2 := by
              have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
              linarith
            calc (1 : ℝ) = (1 : ℝ) ^ p := by simp
              _ ≤ ((X : ℝ) / 2) ^ p := Real.rpow_le_rpow (by norm_num) hXR hp0.le
          calc ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2 ≤ K := hbase
            _ = K * 1 := by ring
            _ ≤ K * ((X : ℝ) / 2) ^ p := mul_le_mul_of_nonneg_left hhalf1 hK0
      have hsplit := sum_window_split (f := fun n => (error n) ^ 2) (m := X / 2 + 1) (X := X)
        (by omega)
      rw [hsplit]
      have hXp : 0 ≤ (X : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg X) p
      have hstep : K * ((2 : ℝ) ^ p)⁻¹ + Cw ≤ K := by
        have := const_step hp0 hKc
        simpa [div_eq_mul_inv] using this
      calc ∑ n ∈ (range (X / 2 + 1)).filter Even, (error n) ^ 2
          + ∑ n ∈ (Icc (X / 2 + 1) X).filter Even, (error n) ^ 2
          ≤ K * ((X : ℝ) / 2) ^ p + Cw * (X : ℝ) ^ p := add_le_add hpre hw
        _ = (K * ((2 : ℝ) ^ p)⁻¹) * (X : ℝ) ^ p + Cw * (X : ℝ) ^ p := by
            rw [Real.div_rpow (Nat.cast_nonneg X) (by norm_num) p]
            ring
        _ = ((K * ((2 : ℝ) ^ p)⁻¹) + Cw) * (X : ℝ) ^ p := by ring
        _ ≤ K * (X : ℝ) ^ p := mul_le_mul_of_nonneg_right hstep hXp
  exact key

-- Axiom audit driver for the assembly.
#print axioms leaf_mean_square_split

end LeanLab.ExceptionalSet.BG2026.Supply385
