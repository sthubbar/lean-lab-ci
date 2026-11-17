import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_selected

/-!
Split of `leaf_near_zero_even_index` of `LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_selected`.

The target fixes the even member of the shifted pair to be `nu γ n` itself and then asks for
one lower bound at that single frequency, with the error carried by the divisor error.  Its
hypotheses already pin the conductor down: the modulus shares a nontrivial common divisor
with the frequency, and every prime above three that divides the modulus divides the
frequency.

The three leaves below cut that conductor range rather than the frequency.  A modulus either
has no prime divisor above three, or it has one; in the second case it either stays below the
fourteenth power of the truncation scale or it does not.  Each leaf therefore quantifies over
a strictly smaller set of moduli than the target and keeps every remaining hypothesis
verbatim, so none of them restates the target or assumes it.  All three ranges are inhabited:
a modulus built from two and three exercises the first leaf, and a modulus with a single
prime divisor above three, dividing the frequency, exercises the second and third.

The assembly is that case distinction with the constants of the three leaves combined: the
smallest lower constant, the largest error constant and the largest threshold.  The step from
a leaf's error coefficient to the assembled one is proved from the nonnegativity of the
divisor error and of the truncation scale.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Smooth-conductor case of the single even frequency: when the modulus has no prime
divisor above three, the real part of the major arc integral at the even frequency `nu γ n`
dominates `c F γ N` times the negative tenth power of the truncation scale, up to the divisor
error.  Only moduli built from two and three are quantified over. -/
theorem leaf_near_zero_even_smooth_modulus (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (∀ p : ℕ, p.Prime → p ∣ r → p ≤ 3) →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  sorry

/-- LEAF. Large-prime conductor, short modulus: when some prime above three divides the
modulus and the modulus is at most the fourteenth power of the truncation scale, the real part
of the major arc integral at the even frequency `nu γ n` dominates `c F γ N` times the
negative tenth power of the truncation scale, up to the divisor error.  Only moduli with a
large prime divisor, and only those below the fourteenth power of the truncation scale, are
quantified over. -/
theorem leaf_near_zero_even_large_prime_short (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p) →
            (r : ℝ) ≤ calE γ κ N ^ (1 / 14 : ℝ) →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  sorry

/-- LEAF. Large-prime conductor, long modulus: when some prime above three divides the
modulus and the modulus exceeds the fourteenth power of the truncation scale, the real part of
the major arc integral at the even frequency `nu γ n` dominates `c F γ N` times the negative
tenth power of the truncation scale, up to the divisor error.  Only moduli with a large prime
divisor, and only those above the fourteenth power of the truncation scale, are quantified
over. -/
theorem leaf_near_zero_even_large_prime_long (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p) →
            calE γ κ N ^ (1 / 14 : ℝ) < (r : ℝ) →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  sorry

/-- Assembly.  The target follows from the three conductor ranges: the modulus either has no
prime divisor above three, or it has one and then sits on one side of the fourteenth power of
the truncation scale.  Constants are combined by taking the smallest lower constant, the
largest error constant and the largest threshold. -/
theorem leaf_near_zero_even_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨δ₁, hδ₁, H₁⟩ := leaf_near_zero_even_smooth_modulus γ h1 h2 a ha
  obtain ⟨δ₂, hδ₂, H₂⟩ := leaf_near_zero_even_large_prime_short γ h1 h2 a ha
  obtain ⟨δ₃, hδ₃, H₃⟩ := leaf_near_zero_even_large_prime_long γ h1 h2 a ha
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδ₁', hδsmall'⟩ := lt_min_iff.mp hδsmall
  obtain ⟨hδ₂', hδ₃'⟩ := lt_min_iff.mp hδsmall'
  obtain ⟨κ₁, hκ₁, K₁⟩ := H₁ δ hδ hδ₁'
  obtain ⟨κ₂, hκ₂, K₂⟩ := H₂ δ hδ hδ₂'
  obtain ⟨κ₃, hκ₃, K₃⟩ := H₃ δ hδ hδ₃'
  refine ⟨min κ₁ (min κ₂ κ₃), lt_min hκ₁ (lt_min hκ₂ hκ₃), ?_⟩
  intro κ hκ hκsmall
  obtain ⟨hκ₁', hκsmall'⟩ := le_min_iff.mp hκsmall
  obtain ⟨hκ₂', hκ₃'⟩ := le_min_iff.mp hκsmall'
  obtain ⟨c₁, A₁, hc₁, hA₁, N₁, L₁⟩ := K₁ κ hκ hκ₁'
  obtain ⟨c₂, A₂, hc₂, hA₂, N₂, L₂⟩ := K₂ κ hκ hκ₂'
  obtain ⟨c₃, A₃, hc₃, hA₃, N₃, L₃⟩ := K₃ κ hκ hκ₃'
  refine ⟨min c₁ (min c₂ c₃), max A₁ (max A₂ A₃), lt_min hc₁ (lt_min hc₂ hc₃),
    lt_of_lt_of_le hA₁ (le_max_left _ _), max N₁ (max N₂ N₃), ?_⟩
  intro N hN
  obtain ⟨hN₁, hN'⟩ := max_le_iff.mp hN
  obtain ⟨hN₂, hN₃⟩ := max_le_iff.mp hN'
  intro r hr hrP hsel n hn heven hm hgcd hnop hrE
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hEpos : 0 < calE γ κ N := by
    unfold calE
    exact Real.exp_pos _
  have hℓ : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hEpos.le _
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg (div_nonneg (by positivity) hP0)
        (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
    · refine mul_nonneg (by positivity)
        (tsum_nonneg (fun q => by split_ifs <;> positivity))
  have transfer : ∀ (ci Ai c A d Y : ℝ), 0 ≤ d → c ≤ ci → Ai ≤ A →
      ci * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ Y + Ai * F γ N * d →
      c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ Y + A * F γ N * d := by
    intro ci Ai c A d Y hd hci hAi h
    have h1 : c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        ci * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
      have h0 := mul_le_mul_of_nonneg_right hci (mul_nonneg hX hℓ)
      calc c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
          = c * (F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) := by ring
        _ ≤ ci * (F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) := h0
        _ = ci * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by ring
    have h2 : Ai * F γ N * d ≤ A * F γ N * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hX) hd
    linarith only [h1, h2, h]
  have hc₂ : min c₁ (min c₂ c₃) ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₃ : min c₁ (min c₂ c₃) ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hA₂ : A₂ ≤ max A₁ (max A₂ A₃) := (le_max_left _ _).trans (le_max_right _ _)
  have hA₃ : A₃ ≤ max A₁ (max A₂ A₃) := (le_max_right _ _).trans (le_max_right _ _)
  by_cases hbig : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p
  · by_cases hcut : (r : ℝ) ≤ calE γ κ N ^ (1 / 14 : ℝ)
    · exact transfer c₂ A₂ _ _ _ _ hD hc₂ hA₂
        (L₂ N hN₂ r hr hrP hsel hbig hcut n hn heven hm hgcd hnop hrE)
    · exact transfer c₃ A₃ _ _ _ _ hD hc₃ hA₃
        (L₃ N hN₃ r hr hrP hsel hbig (not_le.mp hcut) n hn heven hm hgcd hnop hrE)
  · have hsmooth : ∀ p : ℕ, p.Prime → p ∣ r → p ≤ 3 := by
      intro p hp hpd
      by_contra hgt
      exact hbig ⟨p, hp, hpd, not_le.mp hgt⟩
    exact transfer c₁ A₁ _ _ _ _ hD (min_le_left _ _) (le_max_left _ _)
      (L₁ N hN₁ r hr hrP hsel hsmooth n hn heven hm hgcd hnop hrE)

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
