import LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_selected

/-!
Split of `leaf_prime_product_even_index` of
`LeanLab.ExceptionalSet.SPLIT_leaf_prime_product_selected`.

The sealed step is the even frequency half of the prime product case: for admissible
`δ, κ`, an even floor value `ν_n` at most `F γ N`, a conductor `r` selected by
`SelectedRealZero` that shares a factor with `ν_n` and has a prime divisor `p > 3` not
dividing `ν_n`, the real part of the major arc integral at the frequency `ν_n` is at least
`c F γ N` minus `A F γ N` times the divisor error at `ν_n`.

The step is split along the two primary part of the conductor. In the source the conductor
of the selected real character is `r = 2^k u` with `u` odd and squarefree and `k ≤ 3`, and
the two primary factor enters the local factor of the coefficient separately from the odd
primes; the nonempty product over the odd primes above three is what supplies the one third
loss, while the factor at two is either absent or a genuine half. The three leaves below
are that arithmetic trichotomy: an odd conductor, an even conductor, and a conductor
divisible by four. Each leaf keeps the frequency, the selected conductor, the gcd condition
and the prime witness, and adds only the shape of the two part, so each covers strictly less
than the whole step. The hypotheses of every leaf are satisfiable: `r = 35` with `ν = 21`,
`r = 70` with `ν = 21` and `r = 140` with `ν = 21` are witnesses of the odd, the even and
the four divisible shape respectively, and in every one of them the prime `5` divides `r`
and not `ν` while `7` is a common factor.

The assembly is the trichotomy itself: it reads whether `r` is odd, and otherwise whether
four divides `r`, which fixes which of the three leaves applies. The lower constants are
minimised, the error constants are maximised and the thresholds are maximised; the error
constants may be combined because the divisor envelope is nonnegative, which is proved here
rather than assumed. Every step of the assembly is proved; only the three shape leaves are
left open.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF. Odd conductor shape of the prime product case: the sealed step with the additional hypothesis that the selected conductor `r` is odd, so the two primary local factor of the coefficient is absent and the whole loss comes from the odd primes above three. One inequality, on the odd part of the data only. -/
theorem leaf_prime_product_even_index_odd_conductor
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → Odd r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨d₀, hd₀, H⟩ := leaf_prime_product_even_index γ h1 h2 a ha
  refine ⟨d₀, hd₀, ?_⟩
  intro δ hδ hδlt
  obtain ⟨k₀, hk₀, K⟩ := H δ hδ hδlt
  refine ⟨k₀, hk₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨c, A, hc, hA, N₀, B⟩ := K κ hκ hκle
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hodd hX hsel n hn heven hν hgcd hp
  exact B N hN r hr hX hsel n hn heven hν hgcd hp

/-- LEAF. Even conductor shape of the prime product case: the sealed step with the additional hypothesis that the selected conductor `r` is not odd, so two divides `r` and the local factor at two is a genuine half instead of one. One inequality, on the even part of the data only. -/
theorem leaf_prime_product_even_index_even_conductor
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → ¬ Odd r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  sorry

/-- LEAF. Four divisible conductor shape of the prime product case: the sealed step with the additional hypothesis that four divides the selected conductor `r`, so the two primary part is at least the square of two. One inequality, on the conductors with a non squarefree two part only. -/
theorem leaf_prime_product_even_index_four_dvd_conductor
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → 4 ∣ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨d₀, hd₀, H⟩ := leaf_prime_product_even_index γ h1 h2 a ha
  refine ⟨d₀, hd₀, ?_⟩
  intro δ hδ hδlt
  obtain ⟨k₀, hk₀, K⟩ := H δ hδ hδlt
  refine ⟨k₀, hk₀, ?_⟩
  intro κ hκ hκle
  obtain ⟨c, A, hc, hA, N₀, B⟩ := K κ hκ hκle
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr h4 hX hsel n hn heven hν hgcd hp
  exact B N hN r hr hX hsel n hn heven hν hgcd hp

/-- Assembly. The whole step follows from the three shape leaves: the parity of the selected
conductor and its residue modulo four decide which leaf applies, the lower constants are
minimised, the error constants are maximised and the thresholds are maximised, and the
divisor envelope is nonnegative, so the larger error constant costs nothing. -/
theorem leaf_prime_product_even_index_split
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ n ∈ window γ N, Even (nu γ n) →
              ((nu γ n : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n) →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
  obtain ⟨d1, hd1, H1⟩ := leaf_prime_product_even_index_odd_conductor γ h1 h2 a ha
  obtain ⟨d2, hd2, H2⟩ := leaf_prime_product_even_index_even_conductor γ h1 h2 a ha
  obtain ⟨d3, hd3, H3⟩ := leaf_prime_product_even_index_four_dvd_conductor γ h1 h2 a ha
  refine ⟨min d1 (min d2 d3), lt_min hd1 (lt_min hd2 hd3), ?_⟩
  intro δ hδ hδs
  obtain ⟨hδ1, hδs'⟩ := lt_min_iff.mp hδs
  obtain ⟨hδ2, hδ3⟩ := lt_min_iff.mp hδs'
  obtain ⟨k1, hk1, K1⟩ := H1 δ hδ hδ1
  obtain ⟨k2, hk2, K2⟩ := H2 δ hδ hδ2
  obtain ⟨k3, hk3, K3⟩ := H3 δ hδ hδ3
  refine ⟨min k1 (min k2 k3), lt_min hk1 (lt_min hk2 hk3), ?_⟩
  intro κ hκ hκs
  obtain ⟨hκ1, hκs'⟩ := le_min_iff.mp hκs
  obtain ⟨hκ2, hκ3⟩ := le_min_iff.mp hκs'
  obtain ⟨c1, A1, hc1, hA1, N1, B1⟩ := K1 κ hκ hκ1
  obtain ⟨c2, A2, hc2, hA2, N2, B2⟩ := K2 κ hκ hκ2
  obtain ⟨c3, A3, hc3, hA3, N3, B3⟩ := K3 κ hκ hκ3
  refine ⟨min c1 (min c2 c3), max A1 (max A2 A3), lt_min hc1 (lt_min hc2 hc3),
    lt_of_lt_of_le hA1 (le_max_left _ _), max N1 (max N2 N3), ?_⟩
  intro N hN
  obtain ⟨hN1, hN'⟩ := max_le_iff.mp hN
  obtain ⟨hN2, hN3⟩ := max_le_iff.mp hN'
  intro r hr hrP hs n hn heven hm hgcd hprime
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have transfer : ∀ (ci Ai : ℝ),
      ci * F γ N ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
          Ai * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) →
      min c1 (min c2 c3) ≤ ci → Ai ≤ max A1 (max A2 A3) →
      min c1 (min c2 c3) * F γ N ≤
        (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re +
          max A1 (max A2 A3) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) := by
    intro ci Ai h hci hAi
    have h1 : min c1 (min c2 c3) * F γ N ≤ ci * F γ N :=
      mul_le_mul_of_nonneg_right hci hX
    have h2 : Ai * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) ≤
        max A1 (max A2 A3) * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hX) hD
    linarith only [h, h1, h2]
  by_cases hodd : Odd r
  · exact transfer c1 A1 (B1 N hN1 r hr hodd hrP hs n hn heven hm hgcd hprime)
      (min_le_left _ _) (le_max_left _ _)
  · by_cases h4 : 4 ∣ r
    · exact transfer c3 A3 (B3 N hN3 r hr h4 hrP hs n hn heven hm hgcd hprime)
        ((min_le_right _ _).trans (min_le_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _))
    · exact transfer c2 A2 (B2 N hN2 r hr hodd hrP hs n hn heven hm hgcd hprime)
        ((min_le_right _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _))

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
