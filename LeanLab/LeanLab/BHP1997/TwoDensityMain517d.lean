/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: the two applications of the prime number theorem to the
outer primes `p1`, `p2` at one point `m` of J.

`two_pair_first_prime` and `two_pair_second_prime` replace the first and then the second outer
prime by the integers with density `1 / log`, with every log power saved. Both are proved here
from the prime number theorem with partial summation of `TwoDensityMain517c.lean` and the
bounded variation of the E2 weight along each outer variable, `two_pair_first_variation` of
`TwoDensityMain517e.lean` and `two_pair_second_variation` of `TwoDensityMain517f.lean`.
Nothing is left open in this file.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.TwoDensityMain517a
import LeanLab.BHP1997.TwoDensityMain517c
import LeanLab.BHP1997.TwoDensityMain517e
import LeanLab.BHP1997.TwoDensityMain517f

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

/-- P0069 page 51 display 5.17 with page 50 display 5.15. An integer `b ≥ 1` whose exponent is
the second coordinate of a point of E2 is at least `(2 Y) ^ (1 / 10)`, whatever the first
coordinate: E2 lies above `β2 = 1 / 10`. -/
theorem two_pair_level_ge {ε x : ℝ} (hε8 : ε ≤ 1/10^8)
    (hY : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε)) {α : ℝ} {b : ℕ} (hb1 : 1 ≤ b)
    (h : lowerTwoDiscarded ε α (expo ε x b)) :
    (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (b : ℝ) := by
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY
  have hZ : scaleZ ε x = 4 * x ^ (11 / 20 + ε) := rfl
  have hZpos : 0 < scaleZ ε x := by rw [hZ]; linarith
  have hlZ : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
    rw [hZ, Real.log_mul (by norm_num) hYpos.ne']
  have hlY : 9 * Real.log 4 ≤ Real.log (x ^ (11 / 20 + ε)) := by
    have h9 := Real.log_le_log (by norm_num) hY
    rw [Real.log_pow] at h9
    exact_mod_cast h9
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlZpos : 0 < Real.log (scaleZ ε x) := by linarith
  obtain ⟨hb, -⟩ := h
  unfold expo at hb
  have hp2' : (0 : ℝ) < b := by exact_mod_cast hb1
  have hc : (1 / 10 : ℝ) ≤ (1+7*(2*(1/16-1/10^5)))/15-ε := by
    have : (1/10 : ℝ) + 1/10^8 ≤ (1+7*(2*(1/16-1/10^5)))/15 := by norm_num
    linarith
  have h2 : 1 / 10 * Real.log (scaleZ ε x) ≤ Real.log b := by
    have h3 := (le_div_iff₀ hlZpos).mp hb
    have h4 := mul_le_mul_of_nonneg_right hc hlZpos.le
    linarith
  have hX : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ scaleZ ε x ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by rw [hZ]; linarith) (by norm_num)
  refine hX.trans ?_
  rw [Real.rpow_def_of_pos hZpos, ← Real.exp_log hp2']
  apply Real.exp_le_exp.mpr
  linarith

/-- P0069 page 51 display 5.17, summation over one outer variable of display 5.15: terms
bounded by `B / j` against weights bounded by 2 sum to at most `2 B (1 + log N)`. -/
theorem two_pair_outer_sum (N : ℕ) (v T : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ j ∈ Finset.Icc 1 N, |v j| ≤ 2)
    (hT : ∀ j ∈ Finset.Icc 1 N, |T j| ≤ B * (1 / (j : ℝ))) :
    |∑ j ∈ Finset.Icc 1 N, v j * T j| ≤ 2 * B * (1 + Real.log N) := by
  have hh : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log N := by
    have h1 := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    simpa [one_div] using h1
  calc |∑ j ∈ Finset.Icc 1 N, v j * T j|
      ≤ ∑ j ∈ Finset.Icc 1 N, |v j * T j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 N, 2 * (B * (1 / (j : ℝ))) := Finset.sum_le_sum fun j hj => by
        rw [abs_mul]
        exact mul_le_mul (hv j hj) (hT j hj) (abs_nonneg _) (by norm_num)
    _ = 2 * B * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 2 * B * (1 + Real.log N) := mul_le_mul_of_nonneg_left hh (by linarith)

/-- P0069 page 51 display 5.17 with page 3 display 1.8. Scale facts for `x` large: `Y` is at
least `4 ^ 9` and the threshold `CH`, the levels `(2 Y) ^ (1 / 20)` and `(2 Y) ^ (1 / 10)` are
separated, and `log (2 Y)` is comparable with `log x`. -/
theorem two_pair_scale_facts {ε A CH x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hA : 0 < A)
    (h40 : (2 : ℝ) ^ 40 ≤ x) (hexp : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x) (hCH : CH ^ 2 ≤ x) :
    (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) ∧ CH ≤ 2 * x ^ (11 / 20 + ε) ∧
      (2 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) ∧
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) + 1 ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ∧
      (2 : ℝ) ^ (A + 1) ≤ Real.log x ∧
      Real.log x / 2 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ∧
      Real.log (2 * x ^ (11 / 20 + ε)) ≤ 2 * Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) h40
  have hxpos : 0 < x := by linarith
  have hY20 : (2 : ℝ) ^ 20 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h : ((2 : ℝ) ^ 20) ^ 2 = (2 : ℝ) ^ 40 := by norm_num
    rw [h]
    exact h40
  have hYC : CH ≤ x ^ (11 / 20 + ε) := shortY_ge_of_sq_le hε hx1 hCH
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY20
  have hl : (2 : ℝ) ^ (A + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hexp
  have hl1 : 1 ≤ Real.log x :=
    (Real.one_le_rpow (by norm_num) (by linarith)).trans hl
  obtain ⟨hlX1, hlX2⟩ := log_scale_bounds hε hε8 hxpos hl1
  have ht2 : (2 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) := by
    have h20 : (2 : ℝ) ^ (20 : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    have h2 : (2 : ℝ) = ((2 : ℝ) ^ (20 : ℝ)) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    calc (2 : ℝ) = ((2 : ℝ) ^ (20 : ℝ)) ^ (1 / 20 : ℝ) := h2
      _ ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by rw [h20]; linarith) (by norm_num)
  have hsq : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) =
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) * (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  refine ⟨le_trans (by norm_num) hY20, by linarith, ht2, ?_, hl, hlX1, hlX2⟩
  rw [hsq]
  nlinarith

/-- P0069 page 51 display 5.17 with page 3 display 1.8. Log power bookkeeping for one outer
variable: the loss `(2 (1 + ℓ) + K) (1 + log N)` at the scale `ℓ = log (2 Y)` is absorbed by
the saving `ℓ ^ (-(A + 2))`, leaving `log x ^ (-A)`. -/
theorem two_pair_log_arith {A l lX CH K lN : ℝ} (hA : 0 < A) (hl : (2 : ℝ) ^ (A + 1) ≤ l)
    (h1 : l / 2 ≤ lX) (h2 : lX ≤ 2 * l) (hCH : 0 ≤ CH) (hlN : lN ≤ lX) :
    2 * (CH * (2 * (1 + lX) + |K|) * lX ^ (-(A + 2))) * (1 + lN) ≤
      CH * (4 + |K|) * 4 * (2 : ℝ) ^ A * l ^ (-A) := by
  obtain ⟨-, htr, hX1⟩ := log_power_transfer hA hl h1 h2
  have hP : 0 ≤ lX ^ (-(A + 2)) := Real.rpow_nonneg (by linarith) _
  have hK := abs_nonneg K
  have step1 : 2 * (1 + lX) + |K| ≤ (4 + |K|) * lX := by
    nlinarith [mul_nonneg hK (sub_nonneg.2 hX1)]
  have s1 : CH * (2 * (1 + lX) + |K|) * lX ^ (-(A + 2)) ≤
      CH * ((4 + |K|) * lX) * lX ^ (-(A + 2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left step1 hCH) hP
  have s0 : 0 ≤ CH * ((4 + |K|) * lX) * lX ^ (-(A + 2)) :=
    mul_nonneg (mul_nonneg hCH (mul_nonneg (by linarith) (by linarith))) hP
  have s00 : 0 ≤ CH * (2 * (1 + lX) + |K|) * lX ^ (-(A + 2)) :=
    mul_nonneg (mul_nonneg hCH (by linarith)) hP
  have s2 : 2 * (CH * (2 * (1 + lX) + |K|) * lX ^ (-(A + 2))) * (1 + lN) ≤
      2 * (CH * ((4 + |K|) * lX) * lX ^ (-(A + 2))) * (2 * lX) := by
    by_cases hneg : 1 + lN ≤ 0
    · have : 2 * (CH * (2 * (1 + lX) + |K|) * lX ^ (-(A + 2))) * (1 + lN) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
      have h3 : 0 ≤ 2 * (CH * ((4 + |K|) * lX) * lX ^ (-(A + 2))) * (2 * lX) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have s3 : 2 * (CH * ((4 + |K|) * lX) * lX ^ (-(A + 2))) * (2 * lX) =
      CH * (4 + |K|) * (lX ^ (-(A + 2)) * (2 * lX) ^ 2) := by ring
  have s4 := mul_le_mul_of_nonneg_left htr (mul_nonneg hCH (by linarith : (0 : ℝ) ≤ 4 + |K|))
  have s5 : CH * (4 + |K|) * 4 * (2 : ℝ) ^ A * l ^ (-A) =
      CH * (4 + |K|) * (4 * (2 : ℝ) ^ A * l ^ (-A)) := by ring
  linarith

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", the first outer prime `p1` of the E2 sum of display 5.15 at one point `m` of J. For
each fixed prime `p2 = b` the sum over the primes `p1 = a > b` of the E2 weight
`ω(log (m / (a b)) / log b) / (a b log b)` is replaced by the sum over all integers `a > b`
with density `1 / log a`, with every log power saved after summing over `b`. -/
theorem two_pair_first_prime (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, primeWeight b *
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨CH, hCH0, hH⟩ := two_pair_pnt_harmonic (A + 2) (by linarith) (1 / 20) (by norm_num)
  obtain ⟨K, CV, hV⟩ := two_pair_first_variation ω hω hz hε hε8
  refine ⟨max (max (CH * (4 + |K|) * 4 * (2 : ℝ) ^ A) CV)
    (max ((2 : ℝ) ^ 40) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (CH ^ 2))),
    fun x hx m hm1 hm2 => ?_⟩
  have hCle : CH * (4 + |K|) * 4 * (2 : ℝ) ^ A ≤ max (max (CH * (4 + |K|) * 4 * (2 : ℝ) ^ A) CV)
      (max ((2 : ℝ) ^ 40) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (CH ^ 2))) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxCV : CV ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have h40 : (2 : ℝ) ^ 40 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hexp : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hCH2 : CH ^ 2 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  obtain ⟨hY49, hCHX, ht2, htW, hl, hlX1, hlX2⟩ :=
    two_pair_scale_facts hε hε8 hA h40 hexp hCH2
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hX1 : (1 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlog0 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_nonneg hX1
  have hP : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) := Real.rpow_nonneg hlog0 _
  have hlpos : 0 ≤ Real.log x := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (A + 1)
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlpos _
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℝ, Bb = CH * (2 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + |K|) *
      Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) := ⟨_, rfl⟩
  have hBb0 : 0 ≤ Bb := by
    rw [hBb]
    exact mul_nonneg (mul_nonneg hCH0 (by linarith [abs_nonneg K])) hP
  have hpw : ∀ j ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, |primeWeight j| ≤ 2 := fun j _ => by
    unfold primeWeight
    split_ifs <;> norm_num
  refine (two_pair_outer_sum _ _ _ hBb0 hpw (fun b hb => ?_)).trans ?_
  · have hb' := Finset.mem_Icc.mp hb
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb'.1
    by_cases hWb : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (b : ℝ)
    · have hb2 : 2 ≤ b := by
        have : (2 : ℝ) ≤ (b : ℝ) := by linarith
        exact_mod_cast this
      obtain ⟨hM, -, -⟩ := two_cofactor_density_props ω hω hz hb2
      have hcongr : ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) =
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              ((if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / (b : ℝ)
              else 0) / (a : ℝ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b) <;>
          simp only [hE, ↓reduceIte] <;> ring
      rw [hcongr]
      have h := hH (2 * x ^ (11 / 20 + ε)) hCHX b ⌊2 * x ^ (11 / 20 + ε)⌋₊ hb'.2
        (by linarith) hNle
        (fun a : ℕ => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / (b : ℝ) else 0)
        (2 / (b : ℝ)) (K / (b : ℝ)) (by positivity)
        (fun a _ => by
          by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
          · simp only [hE, ↓reduceIte]
            rw [abs_div, abs_of_pos hb0]
            exact div_le_div_of_nonneg_right (hM _) hb0.le
          · simp only [hE, ↓reduceIte, abs_zero]
            positivity)
        (hV x hxCV m hm1 hm2 b hWb hb'.2)
      refine h.trans ?_
      have e : CH * (2 / (b : ℝ) * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + K / (b : ℝ)) *
          Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) =
          CH * (2 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + K) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) * (1 / (b : ℝ)) := by ring
      rw [e, hBb]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [le_abs_self K]) hCH0) hP) (by positivity)
    · rw [Finset.sum_eq_zero, abs_zero]
      · positivity
      · intro a _
        by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
        · exact absurd (two_pair_level_ge hε8 hY49 hb'.1 hE) hWb
        · simp [hE]
  · rw [hBb]
    exact (two_pair_log_arith hA hl hlX1 hlX2 hCH0 hlogN).trans
      (mul_le_mul_of_nonneg_right hCle hL)

/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", the second outer prime `p2` of the E2 sum of display 5.15 at one point `m` of J.
After the first prime is replaced by the integers `a` with density `1 / log a`, for each fixed
integer `a` the sum over the primes `p2 = b < a` of the E2 weight
`ω(log (m / (a b)) / log b) / (a b log b)` is replaced by the sum over all integers `b < a`
with density `1 / log b`, with every log power saved after summing over `a`. -/
theorem two_pair_second_prime (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ a ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / Real.log (a : ℝ) *
          ∑ b ∈ Finset.Ico 1 a,
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨CH, hCH0, hH⟩ := two_pair_pnt_harmonic (A + 2) (by linarith) (1 / 20) (by norm_num)
  obtain ⟨K, CV, hV⟩ := two_pair_second_variation ω hω hz hε hε8
  refine ⟨max (max (CH * (4 + |K|) * 4 * (2 : ℝ) ^ A) CV)
    (max ((2 : ℝ) ^ 40) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (CH ^ 2))),
    fun x hx m hm1 hm2 => ?_⟩
  have hCle : CH * (4 + |K|) * 4 * (2 : ℝ) ^ A ≤ max (max (CH * (4 + |K|) * 4 * (2 : ℝ) ^ A) CV)
      (max ((2 : ℝ) ^ 40) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (CH ^ 2))) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hxCV : CV ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have h40 : (2 : ℝ) ^ 40 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hexp : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hCH2 : CH ^ 2 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  obtain ⟨hY49, hCHX, ht2, htW, hl, hlX1, hlX2⟩ :=
    two_pair_scale_facts hε hε8 hA h40 hexp hCH2
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hX1 : (1 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlog0 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_nonneg hX1
  have hP : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) := Real.rpow_nonneg hlog0 _
  have hlpos : 0 ≤ Real.log x := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (A + 1)
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlpos _
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℝ, Bb = CH * (2 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + |K|) *
      Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) := ⟨_, rfl⟩
  have hBb0 : 0 ≤ Bb := by
    rw [hBb]
    exact mul_nonneg (mul_nonneg hCH0 (by linarith [abs_nonneg K])) hP
  have hlw : ∀ j ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, |1 / Real.log (j : ℝ)| ≤ 2 := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    rcases hj1.eq_or_lt with h1 | h2
    · rw [← h1]; simp
    · have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
      have hlj : (1 / 2 : ℝ) < Real.log (j : ℝ) := by
        have h3 := Real.log_two_gt_d9
        have h4 := Real.log_le_log (by norm_num) hj2
        linarith
      rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
      linarith
  -- the level below which E2 is empty
  have hWpos : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by linarith
  have hceil1 : 1 ≤ ⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ := Nat.ceil_pos.mpr hWpos
  have hLcast : (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) ≤
      ((⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hceil1, Nat.cast_one]
    have := Nat.le_ceil ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ))
    linarith
  have hzero : ∀ a b : ℕ, 1 ≤ b → b ≤ ⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1 →
      (primeWeight b - 1 / Real.log (b : ℝ)) *
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
        else 0) = 0 := by
    intro a b hb1 hbL
    have hlt : (b : ℝ) < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
      Nat.lt_ceil.mp (by omega)
    by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
    · exact absurd (two_pair_level_ge hε8 hY49 hb1 hE) (not_le.mpr hlt)
    · simp [hE]
  refine (two_pair_outer_sum _ _ _ hBb0 hlw (fun a ha => ?_)).trans ?_
  · have ha' := Finset.mem_Icc.mp ha
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha'.1
    have hIco : Finset.Ico 1 a = Finset.Ioc 0 (a - 1) := by
      ext b
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hIco]
    by_cases hc : ⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1 ≤ a - 1
    · rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hc,
        Finset.sum_eq_zero (fun b hb => hzero a b (Finset.mem_Ioc.mp hb).1
          (Finset.mem_Ioc.mp hb).2), zero_add]
      have hcongr : ∑ b ∈ Finset.Ioc (⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1) (a - 1),
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) =
          ∑ b ∈ Finset.Ioc (⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1) (a - 1),
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              ((if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / (a : ℝ)
              else 0) / (b : ℝ)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b) <;>
          simp only [hE, ↓reduceIte] <;> ring
      rw [hcongr]
      have haX : ((a - 1 : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
        have h1 : ((a - 1 : ℕ) : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr (Nat.sub_le a 1)
        have h2 : (a : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Nat.cast_le.mpr ha'.2
        linarith
      have h := hH (2 * x ^ (11 / 20 + ε)) hCHX
        (⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1) (a - 1) hc hLcast haX
        (fun b : ℕ => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / (a : ℝ) else 0)
        (2 / (a : ℝ)) (K / (a : ℝ)) (by positivity)
        (fun b hb => by
          have hb' := Finset.mem_Ioc.mp hb
          have hbW : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (b : ℝ) :=
            Nat.ceil_le.mp (by omega)
          have hb2 : 2 ≤ b := by
            have : (2 : ℝ) ≤ (b : ℝ) := by linarith
            exact_mod_cast this
          obtain ⟨hM, -, -⟩ := two_cofactor_density_props ω hω hz hb2
          by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
          · simp only [hE, ↓reduceIte]
            rw [abs_div, abs_of_pos ha0]
            exact div_le_div_of_nonneg_right (hM _) ha0.le
          · simp only [hE, ↓reduceIte, abs_zero]
            positivity)
        (hV x hxCV m hm1 hm2 a ha'.1 ha'.2 _ hLcast)
      refine h.trans ?_
      have e : CH * (2 / (a : ℝ) * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + K / (a : ℝ)) *
          Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) =
          CH * (2 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + K) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) * (1 / (a : ℝ)) := by ring
      rw [e, hBb]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [le_abs_self K]) hCH0) hP) (by positivity)
    · rw [Finset.sum_eq_zero, abs_zero]
      · positivity
      · intro b hb
        have hb' := Finset.mem_Ioc.mp hb
        exact hzero a b hb'.1 (by omega)
  · rw [hBb]
    exact (two_pair_log_arith hA hl hlX1 hlX2 hCH0 hlogN).trans
      (mul_le_mul_of_nonneg_right hCle hL)

end LeanLab.BHP1997.LowerShortC165
