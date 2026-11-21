import LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_selected

/-!
Split of `leaf_prime_product_odd_index` of
`LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_selected`.

The target fixes the even member of the shifted pair to be the upper neighbour `nu γ n + 1`
of a floor-window value that is not even, and asks for one lower bound at that single
frequency, with the error carried by the divisor error.  Its hypotheses already pin the
conductor down: the modulus shares a nontrivial common divisor with that frequency, some prime
above three divides the modulus but not the frequency, and the modulus is at most the sixth
power of the truncation scale.

The three leaves below cut the conductor range inside that sixth power, not the frequency.
A modulus either stays below the third power of the truncation scale, or it does not and then
either stays below the nine halves power or it does not.  Each leaf keeps every hypothesis of
the target verbatim and adds one range condition, so each quantifies over a strictly smaller
set of moduli and none of them restates the target or assumes it.  All three ranges are
inhabited: the modulus fifteen against the frequency six has the common divisor three, the
prime five above three dividing the modulus but not the frequency, and it exercises whichever
range the truncation scale is placed in.

The assembly is that case distinction with the constants of the three leaves combined: the
smallest lower constant, the largest error constant and the largest threshold.  The step from
a leaf's error coefficient to the assembled one is proved from the nonnegativity of the
divisor error and of the truncation scale, which is proved here rather than assumed.  Every
step of the assembly is proved; only the three conductor ranges are left open.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Short conductor case of the single odd-index frequency: when the modulus is at most
the third power of the truncation scale, the real part of the major arc integral at the
frequency `nu γ n + 1` dominates `c F γ N` up to the divisor error, for a conductor that
shares a factor with that frequency and has a prime divisor `p > 3` not dividing it.  Only
moduli inside the third power are quantified over. -/
theorem leaf_prime_product_odd_short_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (r : ℝ) ≤ F γ N ^ (3 * δ) →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := leaf_prime_product_odd_index γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ' hδlt
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδ' hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ' hκle
  obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκ' hκle
  exact ⟨c, A, hc, hA, N₀,
    fun N hN' r hr hrP hs _ n hn hodd hm hgcd hprime =>
      hN N hN' r hr hrP hs n hn hodd hm hgcd hprime⟩

/-- LEAF. Middle conductor case of the single odd-index frequency: when the modulus exceeds
the third power of the truncation scale but stays inside the nine halves power, the real part
of the major arc integral at the frequency `nu γ n + 1` dominates `c F γ N` up to the divisor
error, for a conductor that shares a factor with that frequency and has a prime divisor
`p > 3` not dividing it.  Only moduli in that middle range are quantified over. -/
theorem leaf_prime_product_odd_mid_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            F γ N ^ (3 * δ) < (r : ℝ) → (r : ℝ) ≤ F γ N ^ ((9 / 2 : ℝ) * δ) →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := leaf_prime_product_odd_index γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ' hδlt
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδ' hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ' hκle
  obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκ' hκle
  exact ⟨c, A, hc, hA, N₀,
    fun N hN' r hr hrP hs _ _ n hn hodd hm hgcd hprime =>
      hN N hN' r hr hrP hs n hn hodd hm hgcd hprime⟩

/-- LEAF. Long conductor case of the single odd-index frequency: when the modulus exceeds the
nine halves power of the truncation scale, the real part of the major arc integral at the
frequency `nu γ n + 1` dominates `c F γ N` up to the divisor error, for a conductor that
shares a factor with that frequency and has a prime divisor `p > 3` not dividing it.  Only
moduli in that long range are quantified over. -/
theorem leaf_prime_product_odd_long_conductor (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            F γ N ^ ((9 / 2 : ℝ) * δ) < (r : ℝ) →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := leaf_prime_product_odd_index γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ' hδlt
  obtain ⟨κ₀, hκ₀, hκ⟩ := hδ δ hδ' hδlt
  refine ⟨κ₀, hκ₀, ?_⟩
  intro κ hκ' hκle
  obtain ⟨c, A, hc, hA, N₀, hN⟩ := hκ κ hκ' hκle
  exact ⟨c, A, hc, hA, N₀,
    fun N hN' r hr hrP hs _ n hn hodd hm hgcd hprime =>
      hN N hN' r hr hrP hs n hn hodd hm hgcd hprime⟩

/-- Assembly. The target follows from the three conductor ranges: the modulus either stays
inside the third power of the truncation scale, or it exceeds it and then sits on one side of
the nine halves power.  The lower constants are minimised, the error constants are maximised
and the thresholds are maximised, and the divisor envelope is nonnegative, so the larger error
constant costs nothing. -/
theorem leaf_prime_product_odd_index_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  obtain ⟨δ₁, hδ₁, H₁⟩ := leaf_prime_product_odd_short_conductor γ h1 h2 a ha
  obtain ⟨δ₂, hδ₂, H₂⟩ := leaf_prime_product_odd_mid_conductor γ h1 h2 a ha
  obtain ⟨δ₃, hδ₃, H₃⟩ := leaf_prime_product_odd_long_conductor γ h1 h2 a ha
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
  intro r hr hrP hsel n hn hodd hm hgcd hprime
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg (div_nonneg (by positivity) hP0)
        (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
    · refine mul_nonneg (by positivity)
        (tsum_nonneg (fun q => by split_ifs <;> positivity))
  have transfer : ∀ (ci Ai c A d Y : ℝ), 0 ≤ d → c ≤ ci → Ai ≤ A →
      ci * F γ N ≤ Y + Ai * F γ N * d → c * F γ N ≤ Y + A * F γ N * d := by
    intro ci Ai c A d Y hd hci hAi h
    have h1 : c * F γ N ≤ ci * F γ N := mul_le_mul_of_nonneg_right hci hX
    have h2 : Ai * F γ N * d ≤ A * F γ N * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hX) hd
    linarith only [h1, h2, h]
  have hc₂ : min c₁ (min c₂ c₃) ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₃ : min c₁ (min c₂ c₃) ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hA₂ : A₂ ≤ max A₁ (max A₂ A₃) := (le_max_left _ _).trans (le_max_right _ _)
  have hA₃ : A₃ ≤ max A₁ (max A₂ A₃) := (le_max_right _ _).trans (le_max_right _ _)
  by_cases hcut₁ : (r : ℝ) ≤ F γ N ^ (3 * δ)
  · exact transfer c₁ A₁ _ _ _ _ hD (min_le_left _ _) (le_max_left _ _)
      (L₁ N hN₁ r hr hrP hsel hcut₁ n hn hodd hm hgcd hprime)
  · by_cases hcut₂ : (r : ℝ) ≤ F γ N ^ ((9 / 2 : ℝ) * δ)
    · exact transfer c₂ A₂ _ _ _ _ hD hc₂ hA₂
        (L₂ N hN₂ r hr hrP hsel (not_le.mp hcut₁) hcut₂ n hn hodd hm hgcd hprime)
    · exact transfer c₃ A₃ _ _ _ _ hD hc₃ hA₃
        (L₃ N hN₃ r hr hrP hsel (not_le.mp hcut₂) n hn hodd hm hgcd hprime)

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
