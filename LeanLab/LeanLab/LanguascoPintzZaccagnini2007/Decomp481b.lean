import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a
import LeanLab.PNTPort.DirichletZF.RealZero

/-!
The real and nonreal character cases of P0045 preprint page 6.
External results stay cited. Their consequences proved in P0045 stay open.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- P0045 page 6: Davenport Chapter 5, the real primitive conductor classification. -/
def RealPrimitiveStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∀ a, (χ a).im = 0) →
      r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r

/-- P0045 page 5: Pintz and Goldfeld and Schinzel, the real zero lower bound. -/
def RealZeroStatement481 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ →
      Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ

/-- P0045 page 6: the denominator in the quoted Iwaniec region. -/
def iwaniecDenom481 (r : ℕ) (t : ℝ) : ℝ :=
  let ℓ := Real.log ((r : ℝ) * (|t| + 2))
  4 * 10 ^ 4 * (Real.log (2 * (oddRad131 r : ℝ)) +
    (ℓ * Real.log (2 * ℓ)) ^ (3 / 4 : ℝ))

/-- P0045 page 6: Iwaniec's zero free region for nonreal primitive characters. -/
def IwaniecStatement481 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∃ a, (χ a).im ≠ 0) → ∀ s : ℂ,
      1 - 1 / iwaniecDenom481 r s.im < s.re → Lfun481 χ s ≠ 0

/-- LEAF. CITED. P0045 page 6, first proof paragraph following display 10.
Davenport Chapter 5 supplies the classification of real primitive conductors. -/
theorem davenport_classification481 : RealPrimitiveStatement481 := by
  sorry

/-- LEAF. CITED. P0045 page 5, the paragraph before Lemma 4.1.
Pintz 1976 and Goldfeld and Schinzel 1975 supply the real zero bound. -/
theorem real_zero_bound481 : RealZeroStatement481 := by
  sorry

/-- LEAF. CITED. P0045 page 6, second proof paragraph following display 10.
Iwaniec 1974 supplies the nonreal character zero free region. -/
theorem iwaniec_zero_free481 : IwaniecStatement481 := by
  sorry

/-! Inlined proof of `real_exceptional_conductor481`. These private lemmas are copies of the
proved lemmas of `Decomp484a` and `SPLIT_real_exceptional_conductor481`, which import this file and
so cannot be called from here. No statement is changed and nothing is assumed. -/

section RealInline481b

open Complex LeanLab.PNTPort.DirichletZF

/-- P0045 page 5, display 8, change of logarithmic scale in the classical region.
The auxiliary factor in Bt is absorbed in one absolute positive constant. -/
private theorem log_Bt_comparison484_inl481b :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, 1 ≤ r → ∀ t : ℝ,
      Real.log (Bt r t) ≤ K * Real.log ((r : ℝ) * (|t| + 2)) := by
  have hZ : 0 < Z := Z_pos
  let B : ℝ := 3 * Z
  have hB : 1 ≤ B := by dsimp [B]; linarith [one_le_Z]
  have hB0 : 0 < B := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + Real.log B / Real.log 2, by positivity, ?_⟩
  intro r hr t
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  let A : ℝ := (r : ℝ) * (|t| + 2)
  have hA2 : 2 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg hr0.le (abs_nonneg t)]
  have hA0 : 0 < A := by linarith
  have hlogA : Real.log 2 ≤ Real.log A := Real.log_le_log (by norm_num) hA2
  have hBt : Bt r t ≤ B * A := by
    dsimp [Bt, B, A]
    nlinarith [show 0 ≤ (r : ℝ) * |t| * Z by positivity]
  have hBt0 : 0 < Bt r t := by dsimp [Bt]; positivity
  have hscale : Real.log B ≤ Real.log B / Real.log 2 * Real.log A := by
    have hm := mul_le_mul_of_nonneg_left hlogA (div_nonneg hlB hl2.le)
    simpa [div_mul_cancel₀ _ hl2.ne'] using hm
  calc Real.log (Bt r t) ≤ Real.log (B * A) := Real.log_le_log hBt0 hBt
    _ = Real.log B + Real.log A := Real.log_mul hB0.ne' hA0.ne'
    _ ≤ (1 + Real.log B / Real.log 2) * Real.log A := by nlinarith

/-- P0045 page 5 before Lemma 4.1, nonreal zeros of nonprincipal characters.
The only exceptional zero in the proved classical region is real. -/
private theorem nonprincipal_nonreal_gap484_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ ≠ 1 → ∀ ρ : ℂ, Lfun481 χ ρ = 0 → ρ.im ≠ 0 →
        b / Real.log ((r : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by
  obtain ⟨c, c', hc, _, hreg⟩ := zero_free_region_real
  obtain ⟨K, hK, hcomp⟩ := log_Bt_comparison484_inl481b
  refine ⟨c / K, div_pos hc hK, ?_⟩
  intro r hr χ hχ ρ hρ him
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hzero : DirichletCharacter.LFunction χ ρ = 0 := by simpa [Lfun481, hr0] using hρ
  have hgap : c / Real.log (Bt r ρ.im) ≤ 1 - ρ.re := by
    rcases (hreg r χ hχ).1 ρ hzero with h | h
    · linarith
    · exact (him h.2.2.2).elim
  have hlogBt : 0 < Real.log (Bt r ρ.im) := by linarith [one_le_log_Bt (N := r) ρ.im]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 1 < (r : ℝ) * (|ρ.im| + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (abs_nonneg ρ.im)]
  have hlogA : 0 < Real.log ((r : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA
  apply le_trans _ hgap
  rw [div_div, div_le_div_iff₀ (mul_pos hK hlogA) hlogBt]
  exact mul_le_mul_of_nonneg_left (hcomp r hr ρ.im) hc.le

/-- P0045 page 5, the primitive principal case of the nonreal zero region.
The compact low height strip and the classical zeta region cover all heights. -/
private theorem zeta_gap484_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      b / Real.log (|ρ.im| + 2) ≤ 1 - ρ.re := by
  obtain ⟨σ, hσ, hbox⟩ := ZetaNoZerosInBox 3
  obtain ⟨A, hA, hlarge⟩ := ZetaZeroFree1
  have hσgap : 0 < 1 - σ := sub_pos.mpr hσ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min ((1 - σ) * Real.log 2) A, lt_min (by positivity) hA.1, ?_⟩
  intro ρ hρ
  have hre : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hρ
  have hrepr : (ρ.re : ℂ) + (ρ.im : ℂ) * I = ρ := by
    simpa [mul_comm] using ρ.re_add_im
  have hlog : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
  by_cases ht : |ρ.im| ≤ 3
  · have hs : ρ.re < σ := by
      by_contra h
      exact hbox ρ.im ht ρ.re (le_of_not_gt h) (by rwa [hrepr])
    have hlogs : Real.log 2 ≤ Real.log (|ρ.im| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg ρ.im])
    rw [div_le_iff₀ hlog]
    calc min ((1 - σ) * Real.log 2) A ≤ (1 - σ) * Real.log 2 := min_le_left _ _
      _ ≤ (1 - σ) * Real.log (|ρ.im| + 2) := mul_le_mul_of_nonneg_left hlogs (by linarith)
      _ ≤ (1 - ρ.re) * Real.log (|ρ.im| + 2) := by nlinarith
  · have ht3 : 3 < |ρ.im| := lt_of_not_ge ht
    have hzero : riemannZeta ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = 0 := by rwa [hrepr]
    have hleft : ρ.re < 1 - A / Real.log |ρ.im| := by
      by_contra hn
      have he := hlarge ρ.re ρ.im ht3 ⟨by simpa using le_of_not_gt hn, hre⟩
      exact he hzero
    have hlogt : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
    have hlogs : Real.log |ρ.im| ≤ Real.log (|ρ.im| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    calc min ((1 - σ) * Real.log 2) A / Real.log (|ρ.im| + 2)
        ≤ A / Real.log (|ρ.im| + 2) := div_le_div_of_nonneg_right (min_le_right _ _) hlog.le
      _ ≤ A / Real.log |ρ.im| := div_le_div_of_nonneg_left hA.1.le hlogt hlogs
      _ ≤ 1 - ρ.re := by linarith

/-- P0045 pages 5 and 6, the classical gap for primitive characters at nonreal zeros.
Primitivity reduces the principal case to zeta at modulus one. -/
private theorem primitive_nonreal_gap484_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → ∀ ρ : ℂ, Lfun481 χ ρ = 0 → ρ.im ≠ 0 →
        b / Real.log ((r : ℝ) * (|ρ.im| + 2)) ≤ 1 - ρ.re := by
  obtain ⟨b₁, hb₁, hnon⟩ := nonprincipal_nonreal_gap484_inl481b
  obtain ⟨b₂, hb₂, hzeta⟩ := zeta_gap484_inl481b
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, ?_⟩
  intro r hr χ hprim ρ hρ him
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 0 ≤ Real.log ((r : ℝ) * (|ρ.im| + 2)) :=
    Real.log_nonneg (by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r) (abs_nonneg ρ.im)])
  by_cases hχ : χ = 1
  · have hrone : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hζ : riemannZeta ρ = 0 := by
      simpa [Lfun481, hχ, DirichletCharacter.LFunction_modOne_eq] using hρ
    have he := hzeta ρ hζ
    simp only [Nat.cast_one, one_mul] at hlog ⊢
    exact (div_le_div_of_nonneg_right (min_le_right _ _) hlog).trans he
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hlog).trans (hnon r hr χ hχ ρ hρ him)

end RealInline481b

/-- The real zero case, from the real zero lower bound alone: for a modulus `r ≥ 1`, a
character with real values, and a genuine zero of the L function at the real point `1 - δ` with
`0 < δ ≤ H / log X`, the modulus is at least `c * Lg X ^ 2`, with one constant `c` for all `X`.
This is the lower bound `a * r ^ (-1/2) ≤ δ` rearranged, with `Lg X = log X / log 2`. -/
private theorem leaf_real_zero_conductor481_inl481b (hzero : RealZeroStatement481)
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

/-- The zero free region for real characters off the real axis, in the form the box uses:
some `b > 0` has `b / log (r (|t| + 2)) ≤ H / log X` for every zero of the box with real character
and nonzero imaginary part. Such a zero cannot sit inside `re ≥ 1 - b / log (r (|t| + 2))`, where
the L function does not vanish, and the box puts it at `re ≥ 1 - H / log X`, so the two radii are
ordered. -/
private theorem leaf_real_nonreal_threshold481_inl481b :
    ∃ b : ℝ, 0 < b ∧ ∀ X : ℕ, 1 < X → ∀ H T P : ℝ,
      ∀ z ∈ zeroBox481 X H T P, (∀ a, (z.2.1 a).im = 0) → z.2.2.im ≠ 0 →
        b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ H / Real.log X := by
  obtain ⟨b, hb, hregion⟩ := primitive_nonreal_gap484_inl481b
  refine ⟨b, hb, ?_⟩
  intro X hX H T P z hz hreal him
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  -- The region places the nonreal zero at least `b / log (r (|t| + 2))` to the left of one.
  have hzreg : b / Real.log ((z.1 : ℝ) * (|z.2.2.im| + 2)) ≤ 1 - z.2.2.re :=
    hregion z.1 h1 z.2.1 h3 z.2.2 h4 him
  -- The box puts the zero at real part at least `1 - H / log X`, so the gap to one is at most
  -- `H / log X`. The two radii are therefore ordered.
  have hgap : 1 - z.2.2.re ≤ H / Real.log X := by
    linarith [h5]
  exact le_trans hzreg hgap

/-- From that radius to the conductor bound: for a fixed `H ≥ 1` and `T ≥ 1`, if every
nonreal zero of the box satisfies the radius inequality at every height, then the modulus of such
a zero is at least `c * Lg X ^ 2` for all large `X`, uniformly in the major arc parameter `P`.
The box gives `|im| ≤ T`, so `r ≥ X ^ (b / H) / (T + 2)`, and an exponential in `X` beats
`Lg X ^ 2` for large `X`. -/
private theorem leaf_real_nonreal_conductor481_inl481b (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
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

/-- The real zero case inside the box: a zero of the box whose imaginary part vanishes is the
real point `1 - δ` with `δ = 1 - re`, `0 < δ` and `δ ≤ H / log X`, so the real zero case applies to
it with one constant and with a threshold that does not depend on the character, the height, the
major arc parameter or the modulus. -/
private theorem leaf_real_zero_box481_inl481b (hzero : RealZeroStatement481) (H T : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → z.2.2.im = 0 → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c, hc, h⟩ := leaf_real_zero_conductor481_inl481b hzero H hH
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
private theorem real_exceptional_conductor481_split_inl481b (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨c₁, hc₁, X₁, hreal⟩ := leaf_real_zero_box481_inl481b hzero H T hH
  obtain ⟨b, hb, hthr⟩ := leaf_real_nonreal_threshold481_inl481b
  obtain ⟨c₂, hc₂, X₂, hnonreal⟩ := leaf_real_nonreal_conductor481_inl481b H T hH hT b hb
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

/-- PROVED. P0045 page 5 before Lemma 4.1 and page 6, first proof paragraph.
The real zero bound gives the quadratic conductor bound.
Nonreal zeros of real characters also require the classical zero free region.
The primitive principal character is excluded for large X at bounded height. -/
theorem real_exceptional_conductor481 (hzero : RealZeroStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) :=
  real_exceptional_conductor481_split_inl481b hzero H T hH hT

/-- LEAF. OPEN. P0045 page 6, last proof paragraph and display 10.
The Iwaniec region gives odd radical growth for nonreal exceptional characters.
This states the weaker quadratic conclusion actually used by the corollary. -/
theorem nonreal_exceptional_radical481 (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∃ a, (z.2.1 a).im ≠ 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  sorry

/-- LEAF. P0045 page 6, first proof paragraph following display 10.
Transfer the conductor lower bound through the three classified possibilities. -/
theorem real_radical_transfer481 {r : ℕ} {Y : ℝ}
    (hclass : r = oddRad131 r ∨ r = 4 * oddRad131 r ∨ r = 8 * oddRad131 r)
    (hY : Y ≤ (r : ℝ)) : Y / 8 ≤ (oddRad131 r : ℝ) := by
  have hr : r ≤ 8 * oddRad131 r := by rcases hclass with h | h | h <;> omega
  have hc : (r : ℝ) ≤ 8 * (oddRad131 r : ℝ) := by exact_mod_cast hr
  linarith

end
end LeanLab.LPZ2007
