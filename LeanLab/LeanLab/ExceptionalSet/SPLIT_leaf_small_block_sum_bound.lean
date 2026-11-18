/-
Split of the sealed statement `leaf_small_block_sum_bound` of
`LeanLab.ExceptionalSet.SPLIT_leaf_small_case`. That statement is the p. 248 short block
estimate of the small `n` case of Karacuba's Theorem 1, chapter I section 2: for constants
`0 < c0, c1, c2, c3, c4` with `c0 < 1`, `c1 < 1` and `c2 + c4 < c1` there are `A0, rho > 0`,
`rho < 1`, such that every block `[a, a+m)` inside `[N, N+P]`, of length
`m <= [P^(c1 - c4/2)]`, obeys `|sum_{x in [a,a+m)} e(f x)| <= A0 m^(1-rho)`.

Two facts make such a block tame, and the split below separates them from the arithmetic that
pays for the thresholds between them.

* `leaf_block_threshold`, the arithmetic of the threshold. With `0 < rho <= 3 c4 / (4 c1)`
  there is one `P0 >= 1` above which `8 pi (n+1) <= P^((c4/2)(n+1+rho) - c1 rho)` for every
  `2 <= n < n0`. The exponent is `(c4/2)(n+1) + rho (c4/2 - c1) >= 3 c4/2 - c1 rho >= 3 c4/4`,
  which is positive, and `n < n0` needs no more than `n0 >= 12` to keep `n` at most `11`: the
  range of `n` is finite and explicit, which is what makes one `P0` serve every `n`.
* `leaf_polynomial_block_sum`, the Weyl sum input at the block level: one saving `rho` and one
  constant `K`, uniform in `n < n0` and in `P` above the threshold, for the `n`-th Taylor
  polynomial of `f` at the left end of the block. This is Karacuba's Lemma 2 read at the `s`-th
  Taylor coefficient of `KarHyp`, whose denominator `[P^(c2 s)]` is below `m^s` because
  `c2 + c4 < c1` and `m >= P^(c1 - c4/2)/2`.
* `leaf_taylor_block_reduction`, the p. 248 Taylor step: the block sum over `f` is the block
  sum over that polynomial plus half a saving `(1/2) m^(1-rho)`, the Taylor remainder
  `m 4 pi (n+1) P^(-c1(n+1)) m^(n+1)` being swallowed by the threshold exponent.

`sorry` sits on those three leaves only. The assembly `leaf_small_block_sum_bound_split` is the
case split on whether the block length `P^(c1 - c4/2)` is below the constant
`A0 = max 2 (max K (P0^(c1 - c4/2)))`: if it is, every term of the block sum has norm one and
`m <= A0 <= A0 m^(1-rho)`; if it is not, then `1 < P` and `P0 <= P` both follow, so the Taylor
step and the Weyl sum bound at the same `rho` add up to `A0 m^(1-rho)`.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_small_case

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Leaves -/

/-- LEAF: The threshold of the saving. For `0 < c1`, `0 < c4` and `0 < rho <= 3 c4 / (4 c1)`
there is a single real `P0 >= 1` such that, for every `2 <= n < n0`, every real `P >= P0`
satisfies `8 pi (n+1) <= P^((c4/2)(n+1+rho) - c1 rho)`. The exponent is bounded below by
`(c4/2)(n+1) - c1 rho >= 3 c4/2 - 3 c4/4 = 3 c4/4 > 0` on `2 <= n`, and `n < n0` with
`n0 >= 12` leaves only the ten values `2, ..., 11`, so the supremum of `(8 pi (n+1))^(1/gamma)`
over them is attained and `P0` may be taken to be its maximum with `1`. -/
theorem leaf_block_threshold (c1 c2 c4 ρ : ℝ) (hc1 : 0 < c1) (hc4 : 0 < c4) (hρ : 0 < ρ)
    (hρc : ρ ≤ 3 * c4 / (4 * c1)) :
    ∃ P0 : ℝ, 1 ≤ P0 ∧ ∀ n : ℕ, 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 → ∀ P : ℝ, P0 ≤ P →
      8 * Real.pi * ((n : ℝ) + 1) ≤ P ^ ((c4 / 2) * ((n : ℝ) + 1 + ρ) - c1 * ρ) := by
  sorry

/- Where the saving comes from: Karacuba's Lemma 2 at the `s`-th coefficient, `2 <= s <= n`.
The approximation `A/q` with `q <= [P^(c2 s)] < m^s` gives `tau >= c3 s - log 2 / log P`, and
`rho = tau/(3 n^2 log (12 n (n+1)/tau))` stays away from zero because `n < n0` bounds `n` by
`11` and `s` by `n`; the price `(8n)^(n l / 2)` of the lemma is one constant, since
`l = log (12 n (n+1)/tau)` is bounded on that finite range too. -/

/-- LEAF: The Weyl sum input at the block level, in the small case `2 <= n < n0`. There are
`rho` and `K`, with `0 < rho < 1`, `rho <= 3 c4 / (4 c1)` and `1 <= K`, both depending on
`c0, ..., c4` only, such that for every admissible block of length `m >= 1` at most
`P^(c1 - c4/2)`, with `P` above the threshold of `leaf_block_threshold`, the `n`-th Taylor
polynomial of `f` at the left end of the block has block sum at most `(1/2) K m^(1-rho)`. -/
theorem leaf_polynomial_block_sum (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ ρ K : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ≤ 3 * c4 / (4 * c1) ∧ 1 ≤ K ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 → 1 < P →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              (m : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) →
              8 * Real.pi * ((n : ℝ) + 1) ≤
                (P : ℝ) ^ ((c4 / 2) * ((n : ℝ) + 1 + ρ) - c1 * ρ) →
              ‖∑ y ∈ Finset.range m,
                eC (taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ)
                  ((a : ℝ) + (y : ℝ)))‖ ≤ 1 / 2 * (K * (m : ℝ) ^ (1 - ρ)) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  exact h2

/-- LEAF: The p. 248 Taylor step, with the remainder removed. On a block `[a, a+m)` inside
`[N, N+P]` of length `1 <= m <= P^(c1 - c4/2)`, with `0 < rho` and `P` above the threshold
`8 pi (n+1) <= P^((c4/2)(n+1+rho) - c1 rho)`, the block sum over `f` is at most the block sum
over the `n`-th Taylor polynomial of `f` at the left end plus half a saving
`(1/2) m^(1-rho)`. Taylor's formula bounds the remainder by `(n+1) P^(-c1(n+1)) m^(n+1)` term
by term, `m` terms of it cost `m 4 pi (n+1) P^(-c1(n+1)) m^(n+1)`, and the threshold exponent
`(c4/2)(n+1+rho) - c1 rho` is exactly what makes that at most `(1/2) m^(1-rho)`, using
`m^(n+1) <= P^((c1 - c4/2)(n+1))`. -/
theorem leaf_taylor_block_reduction
    {c0 c1 c2 c3 c4 ρ : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hH : KarHyp c0 c1 c2 c3 N P n f T) (hP : 1 < P) (hρ : 0 < ρ)
    {a m : ℕ} (ha : N ≤ a) (ham : a + m ≤ N + P) (hm : 1 ≤ m)
    (hAm : (m : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2))
    (hthr : 8 * Real.pi * ((n : ℝ) + 1) ≤
      (P : ℝ) ^ ((c4 / 2) * ((n : ℝ) + 1 + ρ) - c1 * ρ)) :
    ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤
      ‖∑ y ∈ Finset.range m,
        eC (taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ)
          ((a : ℝ) + (y : ℝ)))‖ + 1 / 2 * (m : ℝ) ^ (1 - ρ) := by
  sorry

/-! ### Assembly -/

/-- The sealed statement itself, from the three leaves: the case split on whether the block
length `P^(c1 - c4/2)` is below `A0 = max 2 (max K (P0^(c1 - c4/2)))` separates the blocks so
short that each of their terms can be counted on its own from the blocks past the threshold,
where the Taylor step and the Weyl sum bound at the same saving add up. -/
theorem leaf_small_block_sum_bound_split (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ A0 ρ : ℝ, 0 < A0 ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ N P n : ℕ, 0 < P → 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a m : ℕ, N ≤ a → a + m ≤ N + P → 1 ≤ m →
              m ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ →
              ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ A0 * (m : ℝ) ^ (1 - ρ) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨ρ, K, hρ0, hρ1, hρc, hK1, hkar⟩ :=
    leaf_polynomial_block_sum h2 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨P0, hP01, hthr⟩ := leaf_block_threshold c1 c2 c4 ρ hc1 hc4 hρ0 hρc
  refine ⟨max 2 (max K (P0 ^ (c1 - c4 / 2))), ρ, ?_, hρ0, hρ1, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro N P n hP hn hnN0 f T hH a m ha ham hm hmL
    have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have hδ0 : (0 : ℝ) ≤ c1 - c4 / 2 := by linarith
    have hmle : (m : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) := by
      have h1 : (m : ℝ) ≤ ((⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmL
      have h2 : ((⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℕ) : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) :=
        Nat.floor_le (Real.rpow_nonneg hPpos.le _)
      linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hPownn : (0 : ℝ) ≤ (m : ℝ) ^ (1 - ρ) := Real.rpow_nonneg hm0 _
    by_cases hcase : (P : ℝ) ^ (c1 - c4 / 2) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2)))
    · have hsum : ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤ (m : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        have hEq : ∑ x ∈ Finset.Ico a (a + m), ‖eC (f x)‖ = (m : ℝ) := by
          calc ∑ x ∈ Finset.Ico a (a + m), ‖eC (f x)‖
              = ∑ _x ∈ Finset.Ico a (a + m), (1 : ℝ) :=
                Finset.sum_congr rfl (fun x _ => norm_eC (f x))
            _ = (m : ℝ) := by
                rw [Finset.sum_Ico_eq_sum_range, show a + m - a = m by omega]
                simp
        rw [hEq]
      have hmA : (m : ℝ) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) := le_trans hmle hcase
      have hone : (1 : ℝ) ≤ (m : ℝ) ^ (1 - ρ) := Real.one_le_rpow hm1 (by linarith)
      have hA0 : (0 : ℝ) < max 2 (max K (P0 ^ (c1 - c4 / 2))) :=
        lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hfin : (m : ℝ) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) * (m : ℝ) ^ (1 - ρ) := by
        calc (m : ℝ) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) := hmA
          _ = max 2 (max K (P0 ^ (c1 - c4 / 2))) * 1 := by ring
          _ ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) * (m : ℝ) ^ (1 - ρ) :=
              mul_le_mul_of_nonneg_left hone hA0.le
      linarith
    · push_neg at hcase
      have hgt1 : (1 : ℝ) < (P : ℝ) := by
        rcases le_or_gt (P : ℝ) 1 with hle | hlt
        · exfalso
          have h1 : (P : ℝ) ^ (c1 - c4 / 2) ≤ (1 : ℝ) ^ (c1 - c4 / 2) :=
            Real.rpow_le_rpow hPpos.le hle hδ0
          have h2 : (1 : ℝ) ^ (c1 - c4 / 2) = 1 := Real.one_rpow _
          have h3 : (2 : ℝ) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) := le_max_left _ _
          rw [h2] at h1
          linarith
        · exact hlt
      have hge : P0 ≤ (P : ℝ) := by
        rcases lt_or_ge (P : ℝ) P0 with hlt | hge
        · exfalso
          have h1 : (P : ℝ) ^ (c1 - c4 / 2) ≤ P0 ^ (c1 - c4 / 2) :=
            Real.rpow_le_rpow hPpos.le hlt.le hδ0
          have h2 : P0 ^ (c1 - c4 / 2) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) :=
            le_trans (le_max_right K _) (le_max_right 2 _)
          linarith
        · exact hge
      have hthr' := hthr n hn hnN0 (P : ℝ) hge
      have hP1 : (1 : ℕ) < P := by exact_mod_cast hgt1
      have hred := leaf_taylor_block_reduction hH hP1 hρ0 ha ham hm hmle hthr'
      have hpoly := hkar N P n hP hn hnN0 hP1 f T hH a m ha ham hm hmle hthr'
      have hKA : K ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) :=
        le_trans (le_max_left K _) (le_max_right 2 _)
      have hA0ge1 : (1 : ℝ) ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) :=
        le_trans (by norm_num) (le_max_left _ _)
      have hkey : (1 / 2) * (K * (m : ℝ) ^ (1 - ρ)) + 1 / 2 * (m : ℝ) ^ (1 - ρ)
          ≤ max 2 (max K (P0 ^ (c1 - c4 / 2))) * (m : ℝ) ^ (1 - ρ) := by
        have hrw : (1 / 2) * (K * (m : ℝ) ^ (1 - ρ)) + 1 / 2 * (m : ℝ) ^ (1 - ρ)
            = (K / 2 + 1 / 2) * (m : ℝ) ^ (1 - ρ) := by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_right (by linarith) hPownn
      linarith
