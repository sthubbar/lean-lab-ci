import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_even_index

/-!
Feed for `leaf_near_zero_even_large_prime_long` of
`LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_even_index`.

Paper: Brüdern and Perelli 1998, P0082, Lemma 3 page 358 and the proof of Lemma 7, cases
ii b to ii d, pages 363 and 364, together with display 10 on page 358.

Two leaves carry the analytic content.

* `leaf_exceptional_main_term_lower`, HARD: Lemma 3 combined with display 21 and case ii d.
  When the exceptional character exists, the frequency `m` is even with `X/2 < m ≤ X`, it
  shares a factor with the exceptional modulus and every prime above three dividing the
  modulus divides `m`, then `R₁(m)` plus the divisor error envelope of displays 14 and 15 is
  at least a constant times `(1 - β) (log P) X`.
* `leaf_exceptional_zero_page_bound`, MEDIUM: display 10, the lower bound
  `1 - β ≫ r^(-1/2) (log r)^(-2)`, used in the weaker form `1 - β ≫ r^(-3/5)`.

The proved helper `feed1122_large_prime_core` then runs the last lines of the proof of
Lemma 7: for `r ≤ ℰ^(1/7)` one has `r^(-3/5) ≥ ℰ^(-3/35) ≥ ℰ^(-1/10)` and `log P ≥ 6 δ`.
It is generic in the frequency and is reused by the two odd index feeds.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- LEAF: P0082 page 358 Lemma 3 with page 363 display 20, display 21 and case ii b, and page
364 case ii d. HARD. When the exceptional character `χ` of modulus `r` with zero `β` exists,
and the even frequency `m` with `X/2 < m ≤ X` satisfies `(m, r) > 1` with every prime above
three dividing `r` also dividing `m`, the product in display 21 is empty, `χ(m) = 0`, and
`m 𝔖(m) + J(m) 𝔖'(m) ≥ 𝔖(m) (m - m^β) ≫ (1 - β) (log P) X`; the terms `X Γ₁ + X Γ₂` of
Lemma 3 are carried by the divisor error envelope of displays 14 and 15, and the last error
term of Lemma 3 is absorbed for small `δ`. -/
theorem leaf_exceptional_main_term_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
        ∀ m : ℤ, Even m → F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N →
          1 < Int.gcd m r →
          (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) →
          ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
            χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β →
            1 - a / Real.log (F γ N ^ (6 * δ)) ≤ β → β < 1 → χ.LFunction β = 0 →
            (∀ (q : ℕ) (_ : NeZero q) (ψ : DirichletCharacter ℂ q),
              1 ≤ q → (q : ℝ) ≤ F γ N ^ (6 * δ) → ψ.IsPrimitive →
                ∀ σ : ℝ, 1 - a / Real.log (F γ N ^ (6 * δ)) ≤ σ → σ < 1 →
                  ψ.LFunction σ = 0 → q = r ∧ HEq ψ χ ∧ σ = β) →
            c * (1 - β) * Real.log (F γ N ^ (6 * δ)) * F γ N ≤
              (R1 (F γ N ^ (6 * δ)) (F γ N) m).re +
                A * F γ N * divisorError r (F γ N ^ (6 * δ)) m := by
  sorry

/-- LEAF: P0082 page 358 display 10, the lower bound `1 - β ≫ r^(-1/2) (log r)^(-2)` for a
real zero of the L function of a real nontrivial primitive character of modulus `r`, see
Davenport chapter 14; used in the weaker form `1 - β ≫ r^(-3/5)`. MEDIUM. -/
theorem leaf_exceptional_zero_page_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 0 < β → β < 1 → χ.LFunction β = 0 →
        c₀ * (r : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 - β := by
  sorry

/-- Proved helper: `log P = 6 δ (log N)^γ` for `P = F γ N ^ (6 δ)`. -/
theorem feed1122_log_P (γ δ : ℝ) (N : ℕ) :
    Real.log (F γ N ^ (6 * δ)) = 6 * δ * Real.log (N : ℝ) ^ γ := by
  have hF : 0 < F γ N := Real.exp_pos _
  rw [Real.log_rpow hF]
  unfold LeanLab.ExceptionalSet.BrudernPerelli1998.F
  rw [Real.log_exp]

/-- Proved helper, the end of the proof of Lemma 7 on page 364, generic in the frequency. -/
theorem feed1122_large_prime_core (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ κ : ℝ, 0 < κ →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
        SelectedRealZero a (F γ N ^ (6 * δ)) r → r ≠ 1 →
        ∀ m : ℤ, Even m → F γ N / 2 < (m : ℝ) → (m : ℝ) ≤ F γ N →
          1 < Int.gcd m r →
          (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ m) →
          (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
          c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
            (R1 (F γ N ^ (6 * δ)) (F γ N) m).re +
              A * F γ N * divisorError r (F γ N ^ (6 * δ)) m := by
  obtain ⟨c₀, hc₀, HB⟩ := leaf_exceptional_zero_page_bound
  obtain ⟨δ₀, hδ₀, HA⟩ := leaf_exceptional_main_term_lower γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδs
  obtain ⟨c, A, hc, hA, N₀, H⟩ := HA δ hδ hδs
  refine ⟨c * c₀ * (6 * δ), A, by positivity, hA, max N₀ 3, ?_⟩
  intro N hN κ hκ r hr hrP hsel hr1 m hm hm1 hm2 hg hnop hrE
  rcases hsel with ⟨h, _⟩ | ⟨hNZ, χ, β, hprim, hsq, hne, hβ0, hβa, hβ1, hL, huniq⟩
  · exact absurd h hr1
  have key := H N (le_of_max_le_left hN) r hr hrP m hm hm1 hm2 hg hnop hNZ χ β hprim hsq hne
    hβ0 hβa hβ1 hL huniq
  have hpage := HB r hNZ χ β hprim hsq hne hβ0 hβ1 hL
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_of_max_le_right hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hL1 : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hlogN (by linarith)
  have hE1 : 1 ≤ calE γ κ N := by
    unfold calE
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (by linarith) _)
  have hEpos : 0 < calE γ κ N := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hw : (calE γ κ N ^ (1 / 7 : ℝ)) ^ (-(3 / 5 : ℝ)) ≤ (r : ℝ) ^ (-(3 / 5 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hrpos hrE (by norm_num)
  rw [← Real.rpow_mul hEpos.le] at hw
  have hu : calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ calE γ κ N ^ ((1 / 7 : ℝ) * (-(3 / 5 : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have huw := le_trans hu hw
  have hh1 : c₀ * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ 1 - β :=
    le_trans (mul_le_mul_of_nonneg_left huw hc₀.le) hpage
  have hh2 : (1 - β) * 1 ≤ (1 - β) * Real.log (N : ℝ) ^ γ :=
    mul_le_mul_of_nonneg_left hL1 (by linarith)
  have hF : 0 ≤ F γ N := (Real.exp_pos _).le
  have hh3 : 0 ≤ c * F γ N * (6 * δ) := by positivity
  calc c * c₀ * (6 * δ) * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
      = (c * F γ N * (6 * δ)) * (c₀ * calE γ κ N ^ (-(1 / 10 : ℝ))) := by ring
    _ ≤ (c * F γ N * (6 * δ)) * ((1 - β) * Real.log (N : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_left (by linarith) hh3
    _ = c * (1 - β) * (6 * δ * Real.log (N : ℝ) ^ γ) * F γ N := by ring
    _ = c * (1 - β) * Real.log (F γ N ^ (6 * δ)) * F γ N := by rw [feed1122_log_P]
    _ ≤ _ := key

/-- Proved helper: a modulus with a prime divisor above three is not one. -/
theorem feed1122_ne_one_of_big_prime (r : ℕ) (h : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p) :
    r ≠ 1 := by
  rintro rfl
  obtain ⟨p, hp, hpd, h3⟩ := h
  have := Nat.le_of_dvd one_pos hpd
  omega

/-- Assembly, statement copied verbatim from `leaf_near_zero_even_large_prime_long`. -/
theorem leaf_near_zero_even_large_prime_long_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
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
  obtain ⟨δ₀, hδ₀, H⟩ := feed1122_large_prime_core γ h1 h2 a ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδs
  obtain ⟨c, A, hc, hA, N₀, K⟩ := H δ hδ hδs
  refine ⟨1, one_pos, ?_⟩
  intro κ hκ _
  refine ⟨c, A, hc, hA, N₀, ?_⟩
  intro N hN r hr hrP hsel hbig _ n hn heven hm hgcd hnop hrE
  have hwin := (Finset.mem_filter.mp hn).2.1
  exact K N hN κ hκ r hr hrP hsel (feed1122_ne_one_of_big_prime r hbig) (nu γ n) heven hwin
    hm hgcd hnop hrE

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
