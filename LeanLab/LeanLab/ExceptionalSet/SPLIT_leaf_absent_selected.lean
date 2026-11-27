import LeanLab.ExceptionalSet.UpJ200.Decomp559b

/-!
Split of `leaf_absent_selected` of `LeanLab.ExceptionalSet.UpJ200.Decomp559b`.

The statement being split asks, for `1 < γ < 3/2` and `a > 0`, for a positive cap on the
truncation parameter, a positive cap on the height parameter, positive constants `c` and `A`
and a threshold `N₀`, such that for every admissible truncation, every `N ≥ N₀`, every
conductor `r` selected by `SelectedRealZero` which equals one, and every index `n` of the floor
window with a shift `j` in `{0, 1}` whose adjacent integer `ν_n + j` is even and at most
`F γ N`, the real part of the major arc integral at that even integer is at least `c F γ N`
minus `A F γ N` times the divisor error.

The case being split uses one property of the shift only: with `j` in `{0, 1}` the parity
condition `Even (ν_n + j)` forces `j = 0` when `ν_n` is even and `j = 1` when `ν_n` is odd,
so the even adjacent integer is `ν_n` in the first case and `ν_n + 1` in the second. The two
leaves below are the two halves of that dichotomy. Each names one even frequency only and
drops the shift parameter and the parity condition on it, so each covers strictly less than
the whole statement: the even half says nothing about the frequency `ν_n + 1`, and the odd
half says nothing about the frequency `ν_n`.

The assembly is the dichotomy itself. It reads the parity of `ν_n`, recovers `j` from the
parity condition, then takes the smaller of the two lower constants, the larger of the two
error constants and the larger of the two thresholds. The error constants may be combined
because the divisor error is nonnegative, which is proved here rather than assumed. Every
step of the assembly is proved; only the two frequency halves are left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Even frequency half of the parity dichotomy: on an index of the floor window whose
floor value `ν_n` is even, the even adjacent integer is `ν_n` itself, and the real part of the
major arc integral at that single frequency dominates `c F γ N` up to the divisor error for
the conductor one. One frequency, no shift parameter, no parity condition on a shift. -/
theorem leaf_absent_even_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, Even (nu γ n) →
            ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              c * F γ N ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                  A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₀, hδ₀, h₁⟩ := leaf_absent_selected γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h₂⟩ := h₁ δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, A, hc, hA, N₀', h₃⟩ := h₂ κ hκ hκsmall
  refine ⟨max N₀' 1, by have h : 1 ≤ max N₀' 1 := le_max_right _ _; omega, fun N hN => ?_⟩
  have hN₀' : N₀' ≤ N := by
    have h₄ : max N₀' 1 ≤ N := hN
    have h₅ : N₀' ≤ max N₀' 1 := le_max_left _ _
    linarith
  have hOne : (1 : ℕ) ≤ N := by
    have h₄ : max N₀' 1 ≤ N := hN
    have h₅ : (1 : ℕ) ≤ max N₀' 1 := le_max_right _ _
    linarith
  have hF : (1 : ℝ) ≤ F γ N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hOne
    have hlog : 0 ≤ Real.log N := Real.log_le_log (by norm_num) hN1.le
    have hp : 0 ≤ Real.log N ^ γ := Real.rpow_nonneg hlog
    have hF' : (1 : ℝ) ≤ Real.exp (Real.log N ^ γ) := by
      have h₁ : (0 : ℝ) ≤ Real.log N ^ γ := hp
      have h₂ : Real.exp (Real.log N ^ γ) ≥ Real.exp 0 := Real.exp_le_exp h₁ (by norm_num)
      linarith
    simpa [F] using hF'
  have hP : (1 : ℝ) ≤ F γ N ^ (6 * δ) := by
    have h₁ : (1 : ℝ) ≤ F γ N := hF
    have h₂ : 0 ≤ (6 * δ : ℝ) := by positivity
    exact Real.one_le_rpow h₁ h₂
  intro hsr hn heven hm
  have h₄ := h₃ N hN₀' 1 (by norm_num) hP hsr (0 : ℤ) (by norm_num) hn
    (by simpa using heven) (by simpa [zero_add] using hm) (by rfl)
  simpa [zero_add] using h₄

/-- LEAF. Odd frequency half of the parity dichotomy: on an index of the floor window whose
floor value `ν_n` is odd, the even adjacent integer is the upper neighbour `ν_n + 1`, and the
real part of the major arc integral at that single frequency dominates `c F γ N` up to the
divisor error for the conductor one. One frequency, no shift parameter, no parity condition
on a shift. -/
theorem leaf_absent_odd_index (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          SelectedRealZero a (F γ N ^ (6 * δ)) 1 →
          ∀ n ∈ window γ N, ¬ Even (nu γ n) →
            ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              c * F γ N ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                  A * F γ N * divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, h₁⟩ := leaf_absent_selected γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h₂⟩ := h₁ δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, A, hc, hA, N₀', h₃⟩ := h₂ κ hκ hκsmall
  refine ⟨max N₀' 1, by have h : 1 ≤ max N₀' 1 := le_max_right _ _; omega, fun N hN => ?_⟩
  have hN₀' : N₀' ≤ N := by
    have h₄ : max N₀' 1 ≤ N := hN
    have h₅ : N₀' ≤ max N₀' 1 := le_max_left _ _
    linarith
  have hOne : (1 : ℕ) ≤ N := by
    have h₄ : max N₀' 1 ≤ N := hN
    have h₅ : (1 : ℕ) ≤ max N₀' 1 := le_max_right _ _
    linarith
  have hF : (1 : ℝ) ≤ F γ N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hOne
    have hlog : 0 ≤ Real.log N := Real.log_le_log (by norm_num) hN1.le
    have hp : 0 ≤ Real.log N ^ γ := Real.rpow_nonneg hlog
    have hF' : (1 : ℝ) ≤ Real.exp (Real.log N ^ γ) := by
      have h₁ : (0 : ℝ) ≤ Real.log N ^ γ := hp
      have h₂ : Real.exp (Real.log N ^ γ) ≥ Real.exp 0 := Real.exp_le_exp h₁ (by norm_num)
      linarith
    simpa [F] using hF'
  have hP : (1 : ℝ) ≤ F γ N ^ (6 * δ) := by
    have h₁ : (1 : ℝ) ≤ F γ N := hF
    have h₂ : 0 ≤ (6 * δ : ℝ) := by positivity
    exact Real.one_le_rpow h₁ h₂
  intro hsr hn hnodd hm
  have heven : Even (nu γ n + 1) := by
    have h₁ : Odd (nu γ n) := by
      apply Int.odd_iff_not_even.mp
      exact hnodd
    obtain ⟨k, hk⟩ := h₁
    refine ⟨k + 1, _⟩
    simp [hk] at *
    omega
  have h₄ := h₃ N hN₀' 1 (by norm_num) hP hsr (1 : ℤ) (by norm_num) hn
    heven hm (by rfl)
  simpa using h₄
    refine ⟨k + 1, _⟩
    simp [hk] at *
    omega
  have h₄ := h₃ N hN₀' 1 (by norm_num) hP hsr (1 : ℤ) (by norm_num) hn
    heven hm (by rfl)
  simpa using h₄

/-- Assembly. The whole statement follows from the two frequency halves: the parity condition
fixes the shift, the lower constants are minimised, the error constants are maximised and the
thresholds are maximised, and the divisor error is nonnegative so the larger error constant
costs nothing. -/
theorem leaf_absent_selected_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δe, hδe, he⟩ := leaf_absent_even_index γ h1 h2 a ha
  obtain ⟨δo, hδo, ho⟩ := leaf_absent_odd_index γ h1 h2 a ha
  refine ⟨min δe δo, lt_min hδe hδo, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδe', hδo'⟩ := lt_min_iff.mp hδsmall
  obtain ⟨κe, hκe, he⟩ := he δ hδ hδe'
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ hδo'
  refine ⟨min κe κo, lt_min hκe hκo, ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκe', hκo'⟩ := le_min_iff.mp hκsmall
  obtain ⟨ce, Ae, hce, hAe, Ne, he⟩ := he κ hκ hκe'
  obtain ⟨co, Ao, hco, hAo, No, ho⟩ := ho κ hκ hκo'
  refine ⟨min ce co, max Ae Ao, lt_min hce hco, lt_of_lt_of_le hAe (le_max_left _ _),
    max Ne No, ?_⟩
  intro N hN
  obtain ⟨hNe, hNo⟩ := max_le_iff.mp hN
  intro r hr hrP hs j hj n hn heven hm hr1
  subst hr1
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : ∀ m : ℤ, 0 ≤ divisorError 1 (F γ N ^ (6 * δ)) m := by
    intro m
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg ?_ (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
      simpa using div_nonneg zero_le_one hP0
    · refine mul_nonneg ?_ (tsum_nonneg (fun q => by split_ifs <;> positivity))
      simp
  have transfer : ∀ (ci Ai c A d Y X : ℝ), 0 ≤ X → 0 ≤ d → c ≤ ci → Ai ≤ A →
      ci * X ≤ Y + Ai * X * d → c * X ≤ Y + A * X * d := by
    intro ci Ai c A d Y X hX' hd hci hAi h
    have h1 : c * X ≤ ci * X := mul_le_mul_of_nonneg_right hci hX'
    have h2 : Ai * X * d ≤ A * X * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hX') hd
    linarith only [h1, h2, h]
  by_cases hν : Even (nu γ n)
  · have hj0 : j = 0 := by
      rcases hj with h | h
      · exact h
      · exfalso
        subst h
        obtain ⟨k, hk⟩ := heven
        obtain ⟨l, hl⟩ := hν
        omega
    subst hj0
    simpa using transfer ce Ae (min ce co) (max Ae Ao)
      (divisorError 1 (F γ N ^ (6 * δ)) (nu γ n)) _ _
      hX (hD (nu γ n)) (min_le_left _ _) (le_max_left _ _)
      (by simpa using he N hNe hs n hn hν (by simpa using hm))
  · have hj1 : j = 1 := by
      rcases hj with h | h
      · exfalso
        subst h
        exact hν (by simpa using heven)
      · exact h
    subst hj1
    simpa using transfer co Ao (min ce co) (max Ae Ao)
      (divisorError 1 (F γ N ^ (6 * δ)) (nu γ n + 1)) _ _
      hX (hD (nu γ n + 1)) (min_le_right _ _) (le_max_right _ _)
      (by simpa using ho N hNo hs n hn hν (by simpa using hm))

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
