import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Split of `real_exceptional_conductor481` of `Decomp481b`.

The target bounds the conductor of every zero of the box `zeroBox481 X H T P` that belongs to a
real primitive character from below by `c * Lg X ^ 2`, at bounded height `T`, in the strip
`1 - H / log X ≤ re ≤ 1`, uniformly in the major arc parameter `P`.

Two cases are needed, and they are not the same argument.

Real zeros. `RealZeroStatement481`, the hypothesis `hzero` of the target, gives `a > 0` with
`a * r ^ (-1/2) ≤ δ` for a zero of a real character at the real point `1 - δ`. A zero of the box
has `1 - re ≤ H / log X`, so `a / √r ≤ H / log X`, that is `r ≥ (a log X / H) ^ 2`, which is
`c * Lg X ^ 2` with a constant that works for every `X`. `leaf_real_zero_conductor481` is that
estimate from `hzero` alone and `leaf_real_zero_box481` puts it into the shape of the box.

Nonreal zeros of real characters. `hzero` says nothing about those, and the box does not exclude
them: membership only requires the character to take real values, not the zero to be real. Off the
real axis one needs the classical zero free region for real characters, which is
`leaf_real_nonreal_threshold481`: the radius `b / log (r (|t| + 2))` is at most `H / log X` for
any zero of the box with nonzero imaginary part, since otherwise the zero would sit inside the
region where the L function does not vanish. `leaf_real_nonreal_conductor481` turns that inequality
into the quadratic conductor bound, which is an exponential lower bound in `X` cut down by
`|im| ≤ T`, hence beats `Lg X ^ 2` for all large `X`.

`real_exceptional_conductor481_split` below is proved from the four leaves with no `sorry`,
does not use `real_exceptional_conductor481`, and keeps the statement of the target.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- LEAF. The real zero case, from the real zero lower bound alone: for a modulus `r ≥ 1`, a
character with real values, and a genuine zero of the L function at the real point `1 - δ` with
`0 < δ ≤ H / log X`, the modulus is at least `c * Lg X ^ 2`, with one constant `c` for all `X`.
This is the lower bound `a * r ^ (-1/2) ≤ δ` rearranged, with `Lg X = log X / log 2`. -/
theorem leaf_real_zero_conductor481 (hzero : RealZeroStatement481)
    (H : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      (∀ a, (χ a).im = 0) → ∀ δ : ℝ, 0 < δ → δ ≤ H / Real.log X →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → c * Lg X ^ 2 ≤ (r : ℝ) := by
  obtain ⟨a, ha, hbound⟩ := hzero
  have hH0 : 0 < H := by linarith
  refine ⟨(a / H) ^ 2 * (Real.log 2) ^ 2, by positivity, ?_⟩
  intro X r hr χ hreal δ hδ hδle hpt
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hR : (0 : ℝ) < (r : ℝ) := by linarith
  rcases eq_or_lt_of_le (Real.log_natCast_nonneg X) with h0 | hpos
  · have hLg : Lg X = 0 := by rw [Lg, Real.logb, ← h0]; simp
    rw [hLg]
    simp
  · have hstep : a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ H / Real.log X :=
      le_trans (hbound r hr χ hreal δ hδ hpt) hδle
    rw [Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at hstep
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hR) hpos] at hstep
    have hsq : (a * Real.log X) ^ 2 ≤ H ^ 2 * (r : ℝ) := by
      have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ a * Real.log X) hstep 2
      simp only [mul_pow, Real.sq_sqrt hR.le] at hp
      simpa [mul_pow] using hp
    have hgoal : (a / H) ^ 2 * (Real.log 2) ^ 2 * Lg X ^ 2 = (a * Real.log X) ^ 2 / H ^ 2 := by
      rw [Lg, Real.logb]
      field_simp
    rw [hgoal, div_le_iff₀ (by positivity : (0:ℝ) < H ^ 2)]
    linarith

/-- LEAF. The zero free region for real characters off the real axis, in the form the box uses:
some `b > 0` has `b / log (r (|t| + 2)) ≤ H / log X` for every zero of the box with real character
and nonzero imaginary part. Such a zero cannot sit inside `re ≥ 1 - b / log (r (|t| + 2))`, where
the L function does not vanish, and the box puts it at `re ≥ 1 - H / log X`, so the two radii are
ordered. -/
theorem leaf_real_nonreal_threshold481 :
    ∃ b : ℝ, 0 < b ∧ ∀ X : ℕ, 1 < X → ∀ H T P : ℝ,
      ∀ z ∈ zeroBox481 X H T P, (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
        b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X := by
  sorry

/-- LEAF. From that radius to the conductor bound: for a fixed `H ≥ 1` and `T ≥ 1`, if every
nonreal zero of the box satisfies the radius inequality at every height, then the modulus of such
a zero is at least `c * Lg X ^ 2` for all large `X`, uniformly in the major arc parameter `P`.
The box gives `|im| ≤ T`, so `r ≥ X ^ (b / H) / (T + 2)`, and an exponential in `X` beats
`Lg X ^ 2` for large `X`. -/
theorem leaf_real_nonreal_conductor481 (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∀ b : ℝ, 0 < b →
      (∀ X : ℕ, 1 < X → ∀ P : ℝ, ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
          b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X) →
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
        AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
          (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  intro b hb hhyp
  have hH0 : 0 < H := by linarith
  have hT0 : (0 : ℝ) < T + 2 := by linarith
  set q := b / H with hqval
  have hq : 0 < q := by rw [hqval]; exact div_pos hb hH0
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have key : ∀ X : ℕ, 2 ≤ X → (Real.log X) ^ 2 ≤ 4 / q ^ 2 * (X : ℝ) ^ q := by
    intro X hX2
    have hX1' : (1 : ℝ) < (X : ℝ) := by
      have h : 1 < X := by omega
      exact_mod_cast h
    have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
    have hlogX : 0 ≤ Real.log X := le_of_lt (Real.log_pos hX1')
    have hypos : 0 < (X : ℝ) ^ (q / 2) := Real.rpow_pos_of_pos hXpos _
    have hlogXeq : Real.log X = (2 / q) * Real.log ((X : ℝ) ^ (q / 2)) := by
      rw [Real.log_rpow hXpos]
      field_simp
    have hb1 : Real.log ((X : ℝ) ^ (q / 2)) ≤ (X : ℝ) ^ (q / 2) := by
      have h := Real.log_le_sub_one_of_pos hypos
      linarith
    have hbound : Real.log X ≤ (2 / q) * (X : ℝ) ^ (q / 2) := by
      rw [hlogXeq]
      exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    have hsq := pow_le_pow_left₀ hlogX hbound 2
    have hpow : ((X : ℝ) ^ (q / 2)) ^ 2 = (X : ℝ) ^ q := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ (q / 2)) 2, ← Real.rpow_mul hXpos.le]
      congr 1
      ring
    calc (Real.log X) ^ 2 ≤ ((2 / q) * (X : ℝ) ^ (q / 2)) ^ 2 := hsq
      _ = 4 / q ^ 2 * (X : ℝ) ^ q := by
            rw [mul_pow, hpow]
            field_simp
            ring
  refine ⟨(Real.log 2) ^ 2 * q ^ 2 / (4 * (T + 2)), by positivity, 2, ?_⟩
  intro X hX P hP z hz hreal him
  have hz' : z ∈ zeroBox481 X H T P := hz
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz'
  have hX2 : 2 ≤ X := hX
  have hX1' : (1 : ℝ) < (X : ℝ) := by
    have h : 1 < X := by omega
    exact_mod_cast h
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1'
  have hr1 : (1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast h1
  have hrpos : (0 : ℝ) < (z.1 : ℝ) := by linarith
  have hCpos : (0 : ℝ) < (z.1 : ℝ) * (|z.2.2.im| + 2) :=
    mul_pos hrpos (by positivity)
  have hC1 : (1 : ℝ) < (z.1 : ℝ) * (|z.2.2.im| + 2) := by
    have h2' : (2 : ℝ) ≤ |z.2.2.im| + 2 := by
      have hnn := abs_nonneg z.2.2.im
      linarith
    have hm := mul_le_mul hr1 h2' (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hrpos)
    linarith
  have hlogC : 0 < Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) := Real.log_pos hC1
  have hDpos : (0 : ℝ) < (z.1 : ℝ) * (T + 2) := mul_pos hrpos hT0
  have hle : (z.1 : ℝ) * (|z.2.2.im| + 2) ≤ (z.1 : ℝ) * (T + 2) :=
    mul_le_mul_of_nonneg_left (by have := h7; linarith) (le_of_lt hrpos)
  have hlogle : Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤
      Real.log ((z.1 : ℝ) * (T + 2)) := Real.log_le_log hCpos hle
  have hstep : b * Real.log X ≤ H * Real.log ((z.1 : ℝ) * (T + 2)) := by
    have hd := hhyp X (by omega) P z hz hreal him
    rw [div_le_div_iff₀ hlogC hlogX] at hd
    have hm := mul_le_mul_of_nonneg_left hlogle (le_of_lt hH0)
    linarith
  have hqle : q * Real.log X ≤ Real.log ((z.1 : ℝ) * (T + 2)) := by
    rw [hqval, div_mul_eq_mul_div, div_le_iff₀ hH0]
    linarith
  have hexp : (X : ℝ) ^ q ≤ (z.1 : ℝ) * (T + 2) := by
    have e1 : (X : ℝ) ^ q = Real.exp (Real.log X * q) := by
      rw [mul_comm, ← Real.log_rpow hXpos, Real.exp_log (Real.rpow_pos_of_pos hXpos q)]
    rw [e1]
    have h1 : Real.exp (Real.log X * q) ≤ Real.exp (Real.log ((z.1 : ℝ) * (T + 2))) :=
      Real.exp_le_exp.2 (by rw [mul_comm]; exact hqle)
    rwa [Real.exp_log hDpos] at h1
  have hk := key X hX2
  have hm : q ^ 2 / 4 * (Real.log X) ^ 2 ≤ q ^ 2 / 4 * (4 / q ^ 2 * (X : ℝ) ^ q) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  have hsimp : q ^ 2 / 4 * (4 / q ^ 2 * (X : ℝ) ^ q) = (X : ℝ) ^ q := by
    field_simp
  rw [hsimp] at hm
  have hm4 := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)
  have heq : 4 * (q ^ 2 / 4 * (Real.log X) ^ 2) = q ^ 2 * (Real.log X) ^ 2 := by ring
  rw [heq] at hm4
  have hcval : (Real.log 2) ^ 2 * q ^ 2 / (4 * (T + 2)) * Lg X ^ 2 =
      q ^ 2 * (Real.log X) ^ 2 / (4 * (T + 2)) := by
    rw [Lg, Real.logb]
    field_simp
  rw [hcval, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (T + 2))]
  have hfin : q ^ 2 * (Real.log X) ^ 2 ≤ 4 * (X : ℝ) ^ q := by linarith
  nlinarith [hfin, hexp, hDpos]

/-- LEAF. The real zero case inside the box: a zero of the box whose imaginary part vanishes is the
real point `1 - δ` with `δ = 1 - re`, `0 < δ` and `δ ≤ H / log X`, so the real zero case applies to
it with one constant and with a threshold that does not depend on the character, the height, the
major arc parameter or the modulus. -/
theorem leaf_real_zero_box481 (hzero : RealZeroStatement481) (H T : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im = 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c, hc, h⟩ := leaf_real_zero_conductor481 hzero H hH
  refine ⟨c, hc, 0, ?_⟩
  intro X _ P _ z hz hreal him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  set d : ℝ := 1 - z.2.2.re with hdval
  have hdpos : 0 < d := by rw [hdval]; linarith
  have hdle : d ≤ H / Real.log X := by rw [hdval]; linarith
  have hzz : z.2.2 = ((z.2.2.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hcast : (1 : ℂ) - (d : ℂ) = ((z.2.2.re : ℝ) : ℂ) := by
    rw [hdval]; push_cast; ring
  have hzpt : Lfun481 z.2.1 (1 - (d : ℂ)) = 0 := by
    rw [hcast, ← hzz]
    exact h4
  exact h X z.1 h1 z.2.1 hreal d hdpos hdle hzpt

/-- The split target: the statement of `real_exceptional_conductor481`, proved from the four leaves
by the case distinction `im = 0` or `im ≠ 0`, with the smaller constant and the larger threshold. -/
theorem real_exceptional_conductor481_split (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c₁, hc₁, X₁, hreal⟩ := leaf_real_zero_box481 hzero H T hH
  obtain ⟨b, hb, hthr⟩ := leaf_real_nonreal_threshold481
  obtain ⟨c₂, hc₂, X₂, hnonreal⟩ := leaf_real_nonreal_conductor481 H T hH hT b hb
    (fun X hX P z hz him hIm => hthr X hX H T P z hz him hIm)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max X₁ X₂, ?_⟩
  intro X hX P hAdm z hz him
  have hle₁ : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hle₂ : X₂ ≤ X := le_trans (le_max_right _ _) hX
  have hsq : (0 : ℝ) ≤ Lg X ^ 2 := sq_nonneg (Lg X)
  by_cases hIm : z.2.2.im = 0
  · have h := hreal X hle₁ P hAdm z hz him hIm
    have hmin : min c₁ c₂ * Lg X ^ 2 ≤ c₁ * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hsq
    linarith
  · have h := hnonreal X hle₂ P hAdm z hz him hIm
    have hmin : min c₁ c₂ * Lg X ^ 2 ≤ c₂ * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hsq
    linarith

end

end LeanLab.LPZ2007
