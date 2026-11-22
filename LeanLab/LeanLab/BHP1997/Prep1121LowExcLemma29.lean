/-
Prep 2026-11-21, BHP1997, route step `LowerShortC165.lower_exceptional_mean_square`.
This file splits `DQLeaf518Split.leaf_lemma29`, the open LEAF of the route that carries
Lemma 29 on page 43 of P0069, Baker Harman Pintz 1997, along the paper's own proof on
pages 43 and 44.

The paper's proof: by [30] Lemma 3.19 the window sum is a Perron integral at height `Y` plus
`O(Y^ε)`. So it is enough to show 5.3 for `χ ∈ F = E_q^c \ {χ0}` and 5.4 for `χ0`. Both follow
from a variant of [8] Lemma 2 and the kernel bound `|((1+z)^s - 1)/s|^2 ≪ 1/(T2^2 + t^2)`,
then from 5.1 and 5.2.

Here the per character steps and the error inequality are LEAFs, and the summation over characters is PROVED:
* `leaf_char_nonprincipal`, page 43 to 44, Perron and 5.3 for one `χ ≠ χ0`;
* `leaf_char_principal`, page 44, Perron and 5.4 for `χ0`;
* `leaf_card_le`, PROVED, the number of characters modulo `q` is at most `q`;
* `leaf_error_arith`, the Perron error `O(Y^ε)`, squared and summed over the characters, is
  below `(qQ)^2 Y L^(-A)` since `Q` is a power of `Y`.
`leaf_lemma29_split` has exactly the statement of `DQLeaf518Split.leaf_lemma29` and is
PROVED from the three leaves.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.

NOTE U-1745, 2026-11-22: P0069 pages 20 and 43 print `[29], Lemma 3.19`, but [29] is Saffari and
Vaughan 1977, which has no Lemma 3.19. The result used is Titchmarsh [30], second edition 1986,
Lemma 3.19, book p. 70, the finite Perron formula with error, which follows from Lemma 3.12,
book p. 60, display 3.12.1. Page 22 of P0069 calls it Theorem 3.19 of [30]. Read from
copies/Titchmarsh1986-chIII.pdf, page images. Below, [30] Lemma 3.19 replaces the printed label.
NOTE U-1744, 2026-11-22: [8] is Harman, Primes in short intervals, Math. Z. 180, 1982, 335-348,
Lemma 2 on p. 339: for continuous g and 0 < T0 < T < X, the mean of the square of the integral of
g(s) x^s over c+iT0 to c+iT, c = 1 + 1/log X, over X to 2X is at most X^2 log X times the integral
of |g|^2. The variant on P0069 p. 44 has y^(it), a factor Y L, and prints [T, T'] in [Y/2, 3Y].
The leaves here use t in [-Y, Y] and no factor L: a stronger, still true form, by Plancherel
after y = e^v. MISMATCH with the printed statements, no statement change; see PROGRESS.md.
-/
import LeanLab.BHP1997.DQLeaf518Split

namespace LeanLab.BHP1997.Prep1121LowExc
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43 to 44, proof of Lemma 29, the case `χ ∈ F = E_q^c \ {χ0}`. P0069 Baker
Harman Pintz 1997: by [30] Lemma 3.19 the window sum `Σ_{m ∈ J_y} b(m) χ(m)` equals
`(1/2πi) ∫_{1/2-iY}^{1/2+iY} G(s, χ) ((y+yz)^s - y^s)/s ds + O(Y^ε)`; by the variant of [8]
Lemma 2 on page 44 and the bound `|((1+z)^(1/2+it) - 1)/(1/2+it)|^2 ≪ 1/(T2^2 + t^2)`, the
mean square over `y` in `[Y/2, 3Y]` of that Perron integral is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, the first step of the display after
5.4. The Perron error `O(Y^ε)` is taken with `ε = 1/100`, so its mean square is at most
`Y^(1+1/50)` times a constant. Here `δχ = 0`. The constants depend only on the
coefficients `b` and on `ε`. -/
theorem leaf_char_nonprincipal (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  sorry

/-- LEAF: page 44, proof of Lemma 29, the principal character and display 5.4. P0069 Baker
Harman Pintz 1997: by [30] Lemma 3.19 as in the case of `F`, the window sum of `b χ0` minus
`W(y, z)` is the Perron integral over `[1/2+iT0, 1/2+iY]` and `[1/2-iY, 1/2-iT0]` plus
`O(Y^ε)`; "Similarly (5.2) yields (5.4)", by the variant of [8] Lemma 2 on page 44 and the
kernel bound, the mean square of those two integrals is
`≪ Y^2 ∫_{[-Y,Y] \ [-T0,T0]} |G(1/2+it, χ0)|^2 / (T2^2 + t^2) dt`. Here `δχ0 = 1`. The
Perron error is taken with `ε = 1/100`. The constants depend only on `b` and `ε`. -/
theorem leaf_char_principal (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
              Thm2.delta (1 : DirichletCharacter ℂ q) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              ((∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                    ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
                (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
                  ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                    ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2))) +
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  sorry

/-- Page 3 and page 44, the count of characters in the sum over `χ ∉ E_q`. There are
`φ(q) ≤ q` Dirichlet characters modulo `q`. PROVED by a Mathlib lookup. -/
theorem leaf_card_le (q : ℕ) (hq : 1 ≤ q) :
    (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ q := by
  have : NeZero q := ⟨by omega⟩
  have : NeZero (Monoid.exponent (ZMod q)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have h := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at h
  rw [h]
  exact_mod_cast Nat.totient_le q

/-- For `p > 0` and any constant `R`, `R * log x ^ A ≤ x ^ p` for all large `x`. -/
private lemma eventually_const_mul_log_rpow_le {A p R : ℝ} (hp : 0 < p) :
    ∀ᶠ x : ℝ in Filter.atTop, R * Real.log x ^ A ≤ x ^ p := by
  have hx1 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  rcases le_or_gt R 0 with hR | hR
  · filter_upwards [hx1] with x hx
    have h0 : 0 ≤ Real.log x ^ A := Real.rpow_nonneg (Real.log_nonneg hx) A
    have h1 : 0 ≤ x ^ p := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) p
    nlinarith
  · have hRpos : 0 < R := hR
    have ho := Asymptotics.isLittleO_iff.1
      (isLittleO_log_rpow_rpow_atTop A hp) (inv_pos.2 hRpos)
    filter_upwards [ho, hx1] with x hx hx1'
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) p)] at hx
    have h0 : 0 ≤ Real.log x ^ A := Real.rpow_nonneg (Real.log_nonneg hx1') A
    rw [abs_of_nonneg h0] at hx
    have h2 : R * (R⁻¹ * x ^ p) = x ^ p := by field_simp
    linarith [mul_le_mul_of_nonneg_left hx hRpos.le, h2]

/-- LEAF: page 43, proof of Lemma 29, the error `O(Y^ε)` of [30] Lemma 3.19. Its square,
integrated over `[Y/2, 3Y]` and summed over at most `q + 1` characters, is
`≪ q Y^(1+1/50)`, below `(qQ)^2 Y L^(-A)` for large `x`, because `Q` is the integer part of
`Y^(1/16-1/10^5) / 2` on page 3 and `q ≥ 1`. A pure asymptotic inequality. -/
theorem leaf_error_arith {ε : ℝ} (hε : 0 < ε) :
    ∀ A : ℝ, 0 < A → ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q →
      q ≤ sieveQ ε x →
      ((q : ℝ) + 1) * (K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ)) ≤
        ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA K hK
  set c : ℝ := 1 / 16 - 1 / 10 ^ 5 with hcdef
  clear_value c
  have hc0 : 0 < c := by rw [hcdef]; norm_num
  have hhalf : 0 < 2 * c - 1 / 50 := by rw [hcdef]; norm_num
  have hp : 0 < (11 / 20 + ε) * (2 * c - 1 / 50) := by
    have h : 0 < 11 / 20 + ε := by linarith
    positivity
  -- the Perron error times `log^A` is eventually below `x^((11/20+ε)(2c-1/50))`
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, 32 * K * Real.log x ^ A ≤
      x ^ ((11 / 20 + ε) * (2 * c - 1 / 50)) := eventually_const_mul_log_rpow_le hp
  -- `Q ≈ Y^c` is eventually at least `8`
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, (8 : ℝ) ≤ x ^ ((11 / 20 + ε) * c) :=
    (tendsto_rpow_atTop (show 0 < (11 / 20 + ε) * c by positivity)).eventually
      (Filter.eventually_ge_atTop 8)
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨max C 2, ?_⟩
  intro x hx q hq1 hqQ
  obtain ⟨hxC, hx8, hx1⟩ := hC x (le_trans (le_max_left _ _) hx)
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
  set L : ℝ := Real.log x ^ (-A) with hLdef
  clear_value Y L
  have hY0 : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hx0 _
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLpos : 0 < L := by rw [hLdef]; exact Real.rpow_pos_of_pos hlogpos _
  have hLaL : Real.log x ^ A * L = 1 := by
    rw [hLdef, ← Real.rpow_add hlogpos]
    simp
  have hq2 : ((q : ℝ) + 1) ≤ 2 * q := by
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith
  -- `sieveQ` is the floor of `Y^c / 2`
  have hQeq : (sieveQ ε x : ℝ) = ⌊Y ^ c / 2⌋₊ := by
    unfold sieveQ
    rw [← hYdef]
    have hpow : (Y ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) = Y ^ c := by
      rw [← Real.rpow_mul hY0.le,
        show (2 : ℝ) * (1 / 16 - 1 / 10 ^ 5) * (1 / 2) = c by rw [hcdef]; ring]
    rw [hpow]
  have h8 : 8 ≤ Y ^ c := by
    have h := hx8
    rw [Real.rpow_mul hx0.le, ← hYdef] at h
    exact h
  -- the lower bound for the sieve modulus
  have hQlow : Y ^ c / 4 ≤ (sieveQ ε x : ℝ) := by
    rw [hQeq]
    have hfloor := Nat.sub_one_lt_floor (Y ^ c / 2)
    linarith
  have hQpos : 0 < (sieveQ ε x : ℝ) := lt_of_lt_of_le (by positivity) hQlow
  have hYcsq : Y ^ c * Y ^ c = Y ^ (2 * c) := by
    rw [← Real.rpow_add hY0, show c + c = 2 * c by ring]
  have hQsq : Y ^ (2 * c) ≤ 16 * (sieveQ ε x : ℝ) ^ 2 := by
    have h4 : Y ^ c ≤ 4 * (sieveQ ε x : ℝ) := by linarith
    have h5 : Y ^ c * Y ^ c ≤ (4 * (sieveQ ε x : ℝ)) * (4 * (sieveQ ε x : ℝ)) :=
      mul_self_le_mul_self (by positivity) h4
    rw [← hYcsq]
    nlinarith [h5]
  -- the `log^A` chunk is below `Y^(2c) / Y^(1/50)`
  have hlogc : 32 * K * Real.log x ^ A ≤ Y ^ (2 * c - 1 / 50) := by
    have h := hxC
    rw [Real.rpow_mul hx0.le, ← hYdef] at h
    exact h
  have hYb : 0 < Y ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hY0 _
  rw [Real.rpow_sub hY0] at hlogc
  have hstep1 : 32 * K * Real.log x ^ A * Y ^ (1 / 50 : ℝ) ≤ Y ^ (2 * c) := by
    have h := mul_le_mul_of_nonneg_right hlogc hYb.le
    rwa [div_mul_cancel₀ _ hYb.ne'] at h
  have hstep2 : 2 * K * Real.log x ^ A * Y ^ (1 / 50 : ℝ) ≤ (sieveQ ε x : ℝ) ^ 2 := by
    nlinarith [hstep1, hQsq]
  -- multiply by `log^(-A)`, which cancels the `log^A`
  have hstep3 : 2 * K * Y ^ (1 / 50 : ℝ) ≤ (q : ℝ) * (sieveQ ε x : ℝ) ^ 2 * L := by
    have hmul := mul_le_mul_of_nonneg_right hstep2 hLpos.le
    have he : 2 * K * Real.log x ^ A * Y ^ (1 / 50 : ℝ) * L = 2 * K * Y ^ (1 / 50 : ℝ) := by
      calc 2 * K * Real.log x ^ A * Y ^ (1 / 50 : ℝ) * L
          = 2 * K * Y ^ (1 / 50 : ℝ) * (Real.log x ^ A * L) := by ring
        _ = 2 * K * Y ^ (1 / 50 : ℝ) := by rw [hLaL, mul_one]
    rw [he] at hmul
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hQ2L : 0 ≤ (sieveQ ε x : ℝ) ^ 2 * L := by positivity
    nlinarith [hmul, hQ2L, hq1']
  calc ((q : ℝ) + 1) * (K * Y * Y ^ (1 / 50 : ℝ))
      ≤ (2 * q) * (K * Y * Y ^ (1 / 50 : ℝ)) := by
        have hKY : 0 ≤ K * Y * Y ^ (1 / 50 : ℝ) := by positivity
        nlinarith [hq2, hKY]
    _ = 2 * (q : ℝ) * K * Y * Y ^ (1 / 50 : ℝ) := by ring
    _ ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * Y * L := by
        rw [show 2 * (q : ℝ) * K * Y * Y ^ (1 / 50 : ℝ)
              = 2 * K * Y ^ (1 / 50 : ℝ) * ((q : ℝ) * Y) by ring]
        have hqY : 0 ≤ (q : ℝ) * Y := by positivity
        calc 2 * K * Y ^ (1 / 50 : ℝ) * ((q : ℝ) * Y)
            ≤ ((q : ℝ) * (sieveQ ε x : ℝ) ^ 2 * L) * ((q : ℝ) * Y) :=
              mul_le_mul_of_nonneg_right hstep3 hqY
          _ = ((q : ℝ) * sieveQ ε x) ^ 2 * Y * L := by ring

/-- P0069 page 43, Lemma 29, `Y^2 (Y / T2^2) = (qQ)^2 Y` with `T2 = Y / qQ`. PROVED. -/
theorem y_sq_mul_div_T2_sq {Y P : ℝ} (hY : 0 < Y) (hP : 0 < P) :
    Y ^ 2 * (Y / (Y / P) ^ 2) = P ^ 2 * Y := by
  field_simp

/-- P0069 page 43, Lemma 29, PROVED from the three LEAFs above: the exact statement of
`DQLeaf518Split.leaf_lemma29`. The sum over `χ ∉ E` splits into `χ ≠ χ0`, bounded by 5.1,
and `χ0`, bounded by 5.2, plus the Perron errors. No sorry in this proof. -/
theorem leaf_lemma29_split (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (h51 : ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → q ≤ sieveQ ε x →
      ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
        ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A'))
    (h52 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨K1, hK1, C1, hC1⟩ := leaf_char_nonprincipal b hε hb
  obtain ⟨K2, hK2, C2, hC2⟩ := leaf_char_principal b hε hb
  obtain ⟨C3, hC3⟩ := h51 A hA A hA
  obtain ⟨C4, hC4⟩ := h52 A hA
  obtain ⟨C5, hC5⟩ := leaf_error_arith hε A hA (K1 + K2) (add_nonneg hK1 hK2)
  refine ⟨max (max (max C1 C2) (max C3 C4)) (max C5 (max (K1 * C3 + K2 * C4 + 1) 1)),
    fun x hx q hq1 hqQ z hz1 hz2 => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hx
  have hx4 : C4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hx
  have hx5 : C5 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hDM : K1 * C3 + K2 * C4 + 1 ≤
      max (max (max C1 C2) (max C3 C4)) (max C5 (max (K1 * C3 + K2 * C4 + 1) 1)) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxone : (1 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hQ1 : (1 : ℝ) ≤ sieveQ ε x := by
    have : 1 ≤ sieveQ ε x := le_trans hq1 hqQ
    exact_mod_cast this
  have hP : 0 < (q : ℝ) * sieveQ ε x := by positivity
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
  have hE : 0 ≤ x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) :=
    mul_nonneg hY.le (Real.rpow_nonneg hY.le _)
  have hid := y_sq_mul_div_T2_sq hY hP
  -- the integrand is nonnegative
  have hnn : ∀ χ : DirichletCharacter ℂ q, 0 ≤
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖(∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          (b x m : ℂ) * χ (m : ZMod q)) -
          Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
              (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                  (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                  (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                  (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 :=
    fun χ => intervalIntegral.integral_nonneg (by linarith) (fun y _ => by positivity)
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q) (· ≠ 1)]
  -- the characters `χ ≠ χ0`, display 5.3 and 5.1
  have a1 := Finset.sum_le_sum
    (s := ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1))
    (fun χ hχ => hC1 x hx1 q hq1 hqQ z hz1 hz2 χ (Finset.mem_filter.mp hχ).2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at a1
  have a2 := mul_le_mul_of_nonneg_left (hC3 x hx3 q hq1 hqQ)
    (mul_nonneg hK1 (sq_nonneg (x ^ (11 / 20 + ε))))
  have hcard : ((((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter
      (· ≠ 1)).card : ℝ) ≤ q :=
    le_trans (by exact_mod_cast Finset.card_le_univ _) (leaf_card_le q hq1)
  have a5 := mul_le_mul_of_nonneg_right hcard (mul_nonneg hK1 hE)
  -- the principal character, display 5.4 and 5.2
  have hsub : ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter
      (fun χ => ¬ χ ≠ 1) ⊆ {1} := by
    intro χ hχ
    have := (Finset.mem_filter.mp hχ).2
    push_neg at this
    simp [this]
  have a3 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun χ _ _ => hnn χ)
  rw [Finset.sum_singleton] at a3
  have a3' := hC2 x hx2 q hq1 hqQ z hz1 hz2
  have a4 := mul_le_mul_of_nonneg_left (hC4 x hx4 q hq1 hqQ)
    (mul_nonneg hK2 (sq_nonneg (x ^ (11 / 20 + ε))))
  have a6 := hC5 x hx5 q hq1 hqQ
  have a7 := mul_le_mul_of_nonneg_right hDM
    (mul_nonneg (mul_nonneg (sq_nonneg ((q : ℝ) * sieveQ ε x)) hY.le) hL)
  have e1 : (x ^ (11 / 20 + ε)) ^ 2 * (x ^ (11 / 20 + ε) /
      (x ^ (11 / 20 + ε) / ((q : ℝ) * sieveQ ε x)) ^ 2) =
      ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) := hid
  have e2 : ∀ K C : ℝ, K * (x ^ (11 / 20 + ε)) ^ 2 * (C * (x ^ (11 / 20 + ε) /
      (x ^ (11 / 20 + ε) / ((q : ℝ) * sieveQ ε x)) ^ 2) * Real.log x ^ (-A)) =
      K * C * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
    intro K C
    rw [← e1]; ring
  rw [e2] at a2 a4
  have t1 := add_le_add a1 (a3.trans a3')
  refine t1.trans ?_
  have a8 : 0 ≤ (q : ℝ) * (K2 * (x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ))) :=
    mul_nonneg (by linarith) (mul_nonneg hK2 hE)
  have a9 : 0 ≤ K1 * (x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ)) :=
    mul_nonneg hK1 hE
  linarith [a2, a4, a5, a6, a7, a8, a9]

end LeanLab.BHP1997.Prep1121LowExc
