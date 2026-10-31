/-
P0015 H. L. Montgomery, R. C. Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27 (1975), 353-370. Read from the journal scan, papers/P0015.pdf, page images.
Unit U-6802, CLOUD 20261021T0117Z-cloud55, track T1. AI wrote this Lean code; the Lean kernel
checked it. Binary Goldbach is OPEN; Theorem 1 only says exceptions are rare.

Contents, page numbers of the journal:
* `Theorem1`, the literal form p. 353, and `theorem1_iff_powerSaving`, its equivalence with the
  lab's `PowerSaving`. PROVED.
* `Theorem2`, p. 354, the unconditional short interval statement, a `Prop`, not asserted.
* `majorArcs_separated`, the non-overlap display p. 355. PROVED.
* exponent bookkeeping of (2.4), (3.2)-(3.3), (8.2) and the case `(n, r̃) > 1` p. 367. PROVED.
* `card_gt_mul_sq_le`, the Chebyshev step behind (8.2) p. 367. PROVED.
* `gallagher_max_le`, the first modification of Gallagher's Theorem 7, p. 357. PROVED.
* `I_tilde_le`, the bound `Ĩ(n) ≤ n^β̃`, p. 365. PROVED.
* `euler_ratio`, the per-prime identity behind (8.5), p. 368. PROVED.
* `conductor_le_gcd`, `(n, r̃) ≥ r̃/24` when the product in (8.5) is empty, p. 368. PROVED.
* `final_lower`, the last display of section 8, p. 368. PROVED.
* `theorem2_exponent`, `7/72 = (1 - 1/c)(1 - 2/c)` at Huxley's `c = 12/5`, p. 369. PROVED.
* `Section8Inputs` and `powerSaving_of_section8`, Theorem 1 CONDITIONAL ON the mean square
  (3.2) and the major arc count (8.3), with the paper's `P = X^{6δ}`.
-/
import LeanLab.ExceptionalSet.MVConditional

namespace LeanLab.ExceptionalSet.MV75

open Real Finset Filter
open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-! ### Theorem 1, the literal form -/

/-- Theorem 1, p. 353: there is a positive constant `δ` with `E(X) < X^{1-δ}` for all large `X`.
Effectivity is not recorded. -/
def Theorem1 : Prop := ∃ δ : ℝ, 0 < δ ∧ EventuallyBelow (1 - δ)

/-- The literal form and the lab's `PowerSaving` are equivalent. -/
theorem theorem1_iff_powerSaving : Theorem1 ↔ PowerSaving := by
  constructor
  · rintro ⟨δ, hδ, X0, hX0⟩
    set δ' := min δ (1 / 2) with hδ'
    have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
    have hδ'le : δ' ≤ δ := min_le_left _ _
    have hδ'h : δ' ≤ 1 / 2 := min_le_right _ _
    refine ⟨δ', hδ'pos, powerBound_of_eventuallyBelow (by linarith) ⟨max X0 1, fun X hX => ?_⟩⟩
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_of_max_le_right hX
    calc (E X : ℝ) < (X : ℝ) ^ (1 - δ) := hX0 X (le_of_max_le_left hX)
      _ ≤ (X : ℝ) ^ (1 - δ') := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ / 2, by linarith, eventuallyBelow_of_powerBound (by linarith) h⟩

/-- Theorem 2, first part, p. 354: for all large `X` the interval `(X, X + X^{7/72+ε})` contains
a sum of two primes. Stated, not asserted. -/
def Theorem2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    ∃ n : ℕ, IsGoldbachSum n ∧ X < n ∧ (n : ℝ) < X + X ^ (7 / 72 + ε)

/-- p. 369: the constant `7/72` is `(1 - 1/c)(1 - 2/c)` at Huxley's `c = 12/5`, with
`7/12 = 1 - 1/c` and `1/6 = 1 - 2/c`. -/
theorem theorem2_exponent :
    (1 - 1 / (12 / 5 : ℝ)) = 7 / 12 ∧ (1 - 2 / (12 / 5 : ℝ)) = 1 / 6 ∧
      (1 - 1 / (12 / 5 : ℝ)) * (1 - 2 / (12 / 5 : ℝ)) = 7 / 72 := by
  norm_num

/-! ### Section 2, the major arcs do not overlap -/

/-- p. 355: for `1 ≤ q, q' ≤ P`, `2P < Q` and distinct fractions `a/q ≠ a'/q'`, the arcs of
radius `1/(qQ)` and `1/(q'Q)` around them are disjoint, indeed separated. -/
theorem majorArcs_separated {a a' : ℤ} {q q' : ℕ} {P Q : ℝ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqP : (q : ℝ) ≤ P) (hq'P : (q' : ℝ) ≤ P) (hPQ : 2 * P < Q) (hne : a * q' ≠ a' * q) :
    1 / (q * Q) + 1 / (q' * Q) < |(a : ℝ) / q - a' / q'| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQ : 0 < Q := by linarith
  have hd : (a * q' - a' * q : ℤ) ≠ 0 := sub_ne_zero.mpr hne
  have h1z : (1 : ℤ) ≤ |a * q' - a' * q| := Int.one_le_abs hd
  have h1 : (1 : ℝ) ≤ |(a : ℝ) * q' - a' * q| := by exact_mod_cast h1z
  have heq : (a : ℝ) / q - a' / q' = (a * q' - a' * q) / (q * q') := by
    field_simp
  have hqq : (0 : ℝ) < q * q' := mul_pos hq0 hq0'
  rw [heq, abs_div, abs_of_pos hqq]
  have hsum : 1 / (q * Q) + 1 / (q' * Q) = ((q : ℝ) + q') / (q * q' * Q) := by
    field_simp; ring
  rw [hsum, div_lt_div_iff₀ (by positivity) hqq]
  have hlt : (q : ℝ) + q' < Q := by linarith
  have hA : ((q : ℝ) + q') * (q * q') < Q * (q * q') := mul_lt_mul_of_pos_right hlt hqq
  have hB : Q * (q * q') ≤ |(a : ℝ) * q' - a' * q| * (q * q' * Q) := by
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt (mul_pos hqq hQ))
    nlinarith
  linarith

/-! ### Exponent bookkeeping with `P = X^{6δ}`, `Q = X^{1-6δ}` -/

/-- (2.4) p. 355: `PQ = X`. -/
theorem PQ_eq {X δ : ℝ} (hX : 0 < X) : X ^ (6 * δ) * X ^ (1 - 6 * δ) = X := by
  rw [← rpow_add hX]; simp

/-- (8.2) p. 367: `X P^{-1/3} = X^{1-2δ}`. -/
theorem XP_third {X δ : ℝ} (hX : 0 < X) :
    X * (X ^ (6 * δ)) ^ (-(1 / 3) : ℝ) = X ^ (1 - 2 * δ) := by
  have : X ^ (1 - 2 * δ) = X ^ (1 : ℝ) * X ^ (6 * δ * (-(1 / 3) : ℝ)) := by
    rw [← rpow_add hX]; congr 1; ring
  rw [this, rpow_one, ← rpow_mul hX.le]

/-- p. 367, the case `(n, r̃) > 1`: `X^{1+δ} P^{-1/2} = X^{1-2δ} = X P^{-1/3}`. -/
theorem XP_half {X δ : ℝ} (hX : 0 < X) :
    X ^ (1 + δ) * (X ^ (6 * δ)) ^ (-(1 / 2) : ℝ) = X ^ (1 - 2 * δ) := by
  rw [← rpow_mul hX.le, ← rpow_add hX]; congr 1; ring

/-- (3.2) from (3.3) p. 356: `(X P^{-1/2} L^{17})² · X L = X³ P^{-1} L^{35}`. -/
theorem meanSquare_exponent {X P L : ℝ} (hP : 0 < P) :
    (X * P ^ (-(1 / 2) : ℝ) * L ^ 17) ^ 2 * (X * L) = X ^ 3 * P⁻¹ * L ^ 35 := by
  have : (P ^ (-(1 / 2) : ℝ)) ^ 2 = P⁻¹ := by
    rw [← rpow_natCast, ← rpow_mul hP.le]; norm_num [rpow_neg_one]
  calc (X * P ^ (-(1 / 2) : ℝ) * L ^ 17) ^ 2 * (X * L)
      = X ^ 3 * (P ^ (-(1 / 2) : ℝ)) ^ 2 * L ^ 35 := by ring
    _ = X ^ 3 * P⁻¹ * L ^ 35 := by rw [this]

/-- Lemma 3.1 applies with `Y = P` p. 356 when `P ≤ X^{1/4}`, that is `δ ≤ 1/24`. -/
theorem P_le_quarter {X δ : ℝ} (hX : 1 ≤ X) (hδ : δ ≤ 1 / 24) : X ^ (6 * δ) ≤ X ^ (1 / 4 : ℝ) :=
  rpow_le_rpow_of_exponent_le hX (by linarith)

/-! ### The Chebyshev step -/

/-- p. 367: the number of `n` with `|f n| > T`, times `T²`, is at most the mean square. -/
theorem card_gt_mul_sq_le {ι : Type*} (S : Finset ι) (f : ι → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ((S.filter (fun n => T < |f n|)).card : ℝ) * T ^ 2 ≤ ∑ n ∈ S, f n ^ 2 := by
  calc ((S.filter (fun n => T < |f n|)).card : ℝ) * T ^ 2
      = ∑ n ∈ S.filter (fun n => T < |f n|), T ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ S.filter (fun n => T < |f n|), f n ^ 2 := by
        apply sum_le_sum
        intro n hn
        have h2 : T < |f n| := (mem_filter.mp hn).2
        rw [← sq_abs (f n)]
        exact pow_le_pow_left₀ hT h2.le 2
    _ ≤ ∑ n ∈ S, f n ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-! ### Section 4 and 6, elementary inequalities -/

/-- p. 357, the first modification of Gallagher's Theorem 7: for `0 ≤ β ≤ 1`, `x > 0`, `h ≥ 0`,
`y = N/P > 0`, `(h + y)^{-1} x^{β-1} min(x, h) ≤ y^{β-1}`, with constant 1. -/
theorem gallagher_max_le {β x h y : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 < x) (hh : 0 ≤ h)
    (hy : 0 < y) : (h + y)⁻¹ * (x ^ (β - 1) * min x h) ≤ y ^ (β - 1) := by
  have hhy : 0 < h + y := by linarith
  have hxb : 0 < x ^ (β - 1) := rpow_pos_of_pos hx _
  rcases le_or_gt x y with hxy | hxy
  · have h1 : x ^ (β - 1) * min x h ≤ x ^ β := by
      calc x ^ (β - 1) * min x h ≤ x ^ (β - 1) * x :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hxb.le
        _ = x ^ β := by rw [rpow_sub_one hx.ne']; field_simp
    have h2 : x ^ β ≤ y ^ β := rpow_le_rpow hx.le hxy hβ0
    have h3 : (h + y)⁻¹ ≤ y⁻¹ := inv_anti₀ hy (by linarith)
    calc (h + y)⁻¹ * (x ^ (β - 1) * min x h) ≤ y⁻¹ * y ^ β := by
          apply mul_le_mul h3 (h1.trans h2) (by positivity) (by positivity)
      _ = y ^ (β - 1) := by rw [rpow_sub_one hy.ne']; field_simp
  · have h1 : x ^ (β - 1) ≤ y ^ (β - 1) := rpow_le_rpow_of_nonpos hy hxy.le (by linarith)
    have h2 : (h + y)⁻¹ * min x h ≤ 1 := by
      rw [inv_mul_le_iff₀ hhy]
      have := min_le_right x h
      linarith
    calc (h + y)⁻¹ * (x ^ (β - 1) * min x h) = x ^ (β - 1) * ((h + y)⁻¹ * min x h) := by ring
      _ ≤ x ^ (β - 1) * 1 := mul_le_mul_of_nonneg_left h2 hxb.le
      _ ≤ y ^ (β - 1) := by rw [mul_one]; exact h1

/-- p. 365: `Ĩ(n) = Σ_{P<k<n-P} (k(n-k))^{β̃-1} ≤ n · n^{β̃-1} = n^{β̃}` for `β̃ ≤ 1`, `P ≥ 1`. -/
theorem I_tilde_le {β : ℝ} (hβ : β ≤ 1) (n P : ℕ) (hP : 1 ≤ P) :
    ∑ k ∈ Finset.Ioo P (n - P), ((k : ℝ) * ((n : ℝ) - k)) ^ (β - 1) ≤ (n : ℝ) ^ β := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : Finset.Ioo P (0 - P) = ∅ := by
      ext k; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    rw [this, sum_empty]; exact rpow_nonneg (by simp) _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ k ∈ Finset.Ioo P (n - P), ((k : ℝ) * ((n : ℝ) - k)) ^ (β - 1) ≤
      (n : ℝ) ^ (β - 1) := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hnk : (2 : ℝ) ≤ (n : ℝ) - k := by
      have : k + 2 ≤ n := by omega
      have : ((k + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at this; linarith
    have hge : (n : ℝ) ≤ k * ((n : ℝ) - k) := by nlinarith
    exact rpow_le_rpow_of_nonpos hn0 hge (by linarith)
  calc ∑ k ∈ Finset.Ioo P (n - P), ((k : ℝ) * ((n : ℝ) - k)) ^ (β - 1)
      ≤ ∑ k ∈ Finset.Ioo P (n - P), (n : ℝ) ^ (β - 1) := sum_le_sum hterm
    _ = ((Finset.Ioo P (n - P)).card : ℝ) * (n : ℝ) ^ (β - 1) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (n : ℝ) ^ (β - 1) := by
        apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hn0.le _)
        have : (Finset.Ioo P (n - P)).card ≤ n := by rw [Nat.card_Ioo]; omega
        exact_mod_cast this
    _ = (n : ℝ) ^ β := by rw [rpow_sub_one hn0.ne']; field_simp

/-! ### Section 8 -/

/-- (8.5) p. 368, per prime `p ≥ 3` dividing `r̃` but not `n`: the factor of `S̃(n)/S(n)`,
`(p/(p-1)) (1/(p-1)) / (1 - 1/(p-1)²)`, is exactly `1/(p-2)`. -/
theorem euler_ratio {p : ℝ} (hp : 3 ≤ p) :
    (p / (p - 1)) * (1 / (p - 1)) / (1 - 1 / (p - 1) ^ 2) = 1 / (p - 2) := by
  have h1 : p - 1 ≠ 0 := by intro h; linarith
  have h2 : p - 2 ≠ 0 := by intro h; linarith
  have hp0 : p ≠ 0 := by intro h; linarith
  have hd : 1 - 1 / (p - 1) ^ 2 = p * (p - 2) / (p - 1) ^ 2 := by
    field_simp; ring
  rw [hd]
  field_simp

/-- p. 368: if `r / (4, r)` is squarefree, as Lemma 5.1 gives for a quadratic conductor, and every
prime `p > 3` dividing `r` divides `n`, then `r ≤ 24 (n, r)`. -/
theorem conductor_le_gcd {r n : ℕ} (hr : 0 < r) (hsq : Squarefree (r / Nat.gcd 4 r))
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ r → 3 < p → p ∣ n) : r ≤ 24 * Nat.gcd n r := by
  set g := Nat.gcd 4 r with hg
  set s := r / g with hs
  have hgr : g * s = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right 4 r)
  have hsr : s ∣ r := ⟨g, by rw [mul_comm]; exact hgr.symm⟩
  have hs6 : s ∣ 6 * n := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_primes_dvd
    · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
      by_cases h3 : 3 < p
      · exact Dvd.dvd.mul_left (hdiv p hpp (hps.trans hsr) h3) 6
      · have h2 := hpp.two_le
        interval_cases p
        · exact Dvd.dvd.mul_right (by norm_num) n
        · exact Dvd.dvd.mul_right (by norm_num) n
  have h24 : r ∣ 24 * n := by
    rw [← hgr, show 24 * n = 4 * (6 * n) by ring]
    exact mul_dvd_mul (Nat.gcd_dvd_left 4 r) hs6
  have hdvd : r ∣ 24 * Nat.gcd n r := by
    rw [← Nat.gcd_mul_left]
    exact Nat.dvd_gcd h24 (Dvd.intro_left 24 rfl)
  exact Nat.le_of_dvd (by have := Nat.gcd_pos_of_pos_right n hr; omega) hdvd

/-- p. 368, last display: `X P^{-1/4} / log P > X P^{-1/3}` once `log P < P^{1/12}`. -/
theorem final_lower {X P : ℝ} (hX : 0 < X) (hP : 1 < P) (hlog : Real.log P < P ^ (1 / 12 : ℝ)) :
    X * P ^ (-(1 / 3) : ℝ) < X * P ^ (-(1 / 4) : ℝ) / Real.log P := by
  have hP0 : 0 < P := by linarith
  have hL : 0 < Real.log P := Real.log_pos hP
  have hsplit : P ^ (-(1 / 4) : ℝ) = P ^ (1 / 12 : ℝ) * P ^ (-(1 / 3) : ℝ) := by
    rw [← rpow_add hP0]; norm_num
  rw [lt_div_iff₀ hL, hsplit]
  have h3 : 0 < P ^ (-(1 / 3) : ℝ) := rpow_pos_of_pos hP0 _
  have := mul_lt_mul_of_pos_left hlog (mul_pos hX h3)
  nlinarith

/-- p. 368: `r̃ ≤ P^{1/2}` turns `1 - β̃ ≫ r̃^{-1/2} log^{-2} r̃` into `≫ P^{-1/4} log^{-2} P`. -/
theorem siegel_shape_mono {r P : ℝ} (hr : 1 < r) (hrP : r ≤ P ^ (1 / 2 : ℝ)) (hP : 1 < P) :
    P ^ (-(1 / 4) : ℝ) / Real.log P ^ 2 ≤ r ^ (-(1 / 2) : ℝ) / Real.log r ^ 2 := by
  have hP0 : 0 < P := by linarith
  have hr0 : 0 < r := by linarith
  have hLr : 0 < Real.log r := Real.log_pos hr
  have hrP' : r ≤ P := by
    calc r ≤ P ^ (1 / 2 : ℝ) := hrP
      _ ≤ P ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hP.le (by norm_num)
      _ = P := rpow_one P
  have hlog : Real.log r ≤ Real.log P := Real.log_le_log hr0 hrP'
  have hpow : P ^ (-(1 / 4) : ℝ) ≤ r ^ (-(1 / 2) : ℝ) := by
    have : P ^ (-(1 / 4) : ℝ) = (P ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) := by
      rw [← rpow_mul hP0.le]; norm_num
    rw [this]
    exact rpow_le_rpow_of_nonpos hr0 hrP (by norm_num)
  apply div_le_div₀ (rpow_nonneg hr0.le _) hpow (by positivity)
  exact pow_le_pow_left₀ hLr.le hlog 2

/-- The inputs of section 8 for each window `(x/2, x]`, `x ≥ X0`, with `P = x^{6δ}`:
functions `R₁`, `R₂` such that `R₁(n) + R₂(n) > 0` makes `n` a sum of two primes, as `R(n) > 0` does;
the mean square (3.2) over the window, `Σ R₂(n)² ≤ K₁ x³ P^{-1} log³⁵ x`; and the count (8.3), at most
`K₂ x P^{-1/3}` even `n` in the window with `R₁(n) ≤ x P^{-1/3} = x^{1-2δ}`. -/
def Section8Inputs (δ K₁ K₂ : ℝ) (X0 : ℕ) : Prop :=
  ∀ x : ℕ, X0 ≤ x → ∃ R₁ R₂ : ℕ → ℝ,
    (∀ n, 0 < R₁ n + R₂ n → IsGoldbachSum n) ∧
    ∑ n ∈ Finset.Icc (x / 2 + 1) x, R₂ n ^ 2 ≤
      K₁ * (x : ℝ) ^ 3 * ((x : ℝ) ^ (6 * δ))⁻¹ * Real.log x ^ 35 ∧
    (((Finset.Icc (x / 2 + 1) x).filter
        (fun n => Even n ∧ R₁ n ≤ (x : ℝ) ^ (1 - 2 * δ))).card : ℝ) ≤ K₂ * (x : ℝ) ^ (1 - 2 * δ)

/-- (8.2) p. 367 from the inputs: the bad even numbers in the window number at most
`K₂ x^{1-2δ} + K₁ x^{1-2δ} log³⁵ x`. -/
theorem badWindow_le_of_section8 {δ K₁ K₂ : ℝ} {X0 : ℕ} (h : Section8Inputs δ K₁ K₂ X0)
    {x : ℕ} (hx : X0 ≤ x) (hx1 : 1 ≤ x) :
    (badWindow x : ℝ) ≤ K₂ * (x : ℝ) ^ (1 - 2 * δ) + K₁ * (x : ℝ) ^ (1 - 2 * δ) * Real.log x ^ 35 := by
  obtain ⟨R₁, R₂, hR, hms, hcnt⟩ := h x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  set T : ℝ := (x : ℝ) ^ (1 - 2 * δ) with hT
  have hT0 : 0 < T := rpow_pos_of_pos hx0 _
  set W := Finset.Icc (x / 2 + 1) x
  set A := W.filter (fun n => Even n ∧ R₁ n ≤ T)
  set B := W.filter (fun n => T < |R₂ n|)
  have hsub : W.filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n) ⊆ A ∪ B := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hnW, he, hng⟩ := hn
    have hle : R₁ n + R₂ n ≤ 0 := by
      by_contra hc; exact hng (hR n (lt_of_not_ge hc))
    rcases le_or_gt (R₁ n) T with h1 | h1
    · exact mem_union_left _ (mem_filter.mpr ⟨hnW, he, h1⟩)
    · refine mem_union_right _ (mem_filter.mpr ⟨hnW, ?_⟩)
      have : T < -R₂ n := by linarith
      exact lt_of_lt_of_le this (neg_le_abs _)
  have hcard : (badWindow x : ℝ) ≤ (A.card : ℝ) + B.card := by
    have h1 : badWindow x ≤ A.card + B.card :=
      (card_le_card hsub).trans (card_union_le _ _)
    exact_mod_cast h1
  have hB : (B.card : ℝ) * T ^ 2 ≤ K₁ * (x : ℝ) ^ 3 * ((x : ℝ) ^ (6 * δ))⁻¹ * Real.log x ^ 35 :=
    (card_gt_mul_sq_le W R₂ hT0.le).trans hms
  have hT2 : T ^ 2 * T = (x : ℝ) ^ 3 * ((x : ℝ) ^ (6 * δ))⁻¹ := by
    rw [hT, ← rpow_natCast, ← rpow_mul hx0.le, ← rpow_add hx0, ← rpow_neg hx0.le,
      ← rpow_natCast, ← rpow_add hx0]
    congr 1; push_cast; ring
  have hB' : (B.card : ℝ) ≤ K₁ * T * Real.log x ^ 35 := by
    have hT2pos : 0 < T ^ 2 := by positivity
    have heq : K₁ * (x : ℝ) ^ 3 * ((x : ℝ) ^ (6 * δ))⁻¹ * Real.log x ^ 35 =
        (K₁ * T * Real.log x ^ 35) * T ^ 2 := by
      calc K₁ * (x : ℝ) ^ 3 * ((x : ℝ) ^ (6 * δ))⁻¹ * Real.log x ^ 35
          = K₁ * ((x : ℝ) ^ 3 * ((x : ℝ) ^ (6 * δ))⁻¹) * Real.log x ^ 35 := by ring
        _ = (K₁ * T * Real.log x ^ 35) * T ^ 2 := by rw [← hT2]; ring
    rw [heq] at hB
    exact le_of_mul_le_mul_right hB hT2pos
  have hA : (A.card : ℝ) ≤ K₂ * T := hcnt
  linarith

/-- `log³⁵ x ≤ (35/δ)³⁵ x^δ` for `x ≥ 1`. -/
theorem log_pow35_le {δ x : ℝ} (hδ : 0 < δ) (hx : 1 ≤ x) :
    Real.log x ^ 35 ≤ (35 / δ) ^ 35 * x ^ δ := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ (δ / 35) / (δ / 35) := Real.log_le_rpow_div hx0.le (by positivity)
  have h2 : Real.log x ^ 35 ≤ (x ^ (δ / 35) / (δ / 35)) ^ 35 := pow_le_pow_left₀ hL0 h1 35
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, ← rpow_natCast (x ^ (δ / 35)), ← rpow_mul hx0.le]
  have : δ / 35 * ((35 : ℕ) : ℝ) = δ := by push_cast; ring
  rw [this]
  field_simp

/-- **Theorem 1, CONDITIONAL ON `Section8Inputs`**, the mean square (3.2) and the major arc
count (8.3) with `P = X^{6δ}`, `0 < δ < 1`: the power saving `E(X) ≪ X^{1-δ}`, p. 367. -/
theorem powerSaving_of_section8 {δ K₁ K₂ : ℝ} {X0 : ℕ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (h : Section8Inputs δ K₁ K₂ X0) : PowerSaving := by
  refine ⟨δ, hδ0, powerBound_of_window (C := K₂ + K₁ * (35 / δ) ^ 35) (X0 := max X0 1)
    (by linarith) ?_⟩
  intro x hx
  have hxX0 : X0 ≤ x := le_of_max_le_left hx
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hbad := badWindow_le_of_section8 h hxX0 hx1
  have hlog := log_pow35_le hδ0 hxr
  have hsplit : (x : ℝ) ^ (1 - 2 * δ) * (x : ℝ) ^ δ = (x : ℝ) ^ (1 - δ) := by
    rw [← rpow_add hx0]; congr 1; ring
  have hle : (x : ℝ) ^ (1 - 2 * δ) ≤ (x : ℝ) ^ (1 - δ) :=
    rpow_le_rpow_of_exponent_le hxr (by linarith)
  have hp : 0 ≤ (x : ℝ) ^ (1 - 2 * δ) := rpow_nonneg hx0.le _
  have h2 : K₁ * (x : ℝ) ^ (1 - 2 * δ) * Real.log x ^ 35 ≤
      K₁ * (35 / δ) ^ 35 * (x : ℝ) ^ (1 - δ) := by
    rw [← hsplit]
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hK₁ hp)
    linarith
  have h1 : K₂ * (x : ℝ) ^ (1 - 2 * δ) ≤ K₂ * (x : ℝ) ^ (1 - δ) :=
    mul_le_mul_of_nonneg_left hle hK₂
  linarith

end LeanLab.ExceptionalSet.MV75
