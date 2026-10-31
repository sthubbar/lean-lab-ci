/-
P0030 D. A. Goldston, Linnik's theorem on Goldbach numbers in short intervals,
Glasgow Math. J. 32 (1990) 285-297, papers/P0030.pdf, pages 285 and 286 read as page images.
Unit U-1520, run 20261025T1603Z-10248, track T1, DECOMPOSE. AI-written Lean code, Claude.
Checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

Goldston's introduction, p. 285 to 286, gives the Kátai, Montgomery-Vaughan argument: under RH
there is an absolute `C` with a Goldbach number in `[N, N + C log² N]` for all large `N`.
* Pairing, p. 285: if `[N, N + h]` holds no Goldbach number then one of `[y, y + h/2]` and
  `[N - y, N - y + h/2]` holds no prime.
* Covering, p. 285: the blocks `[N/2 + k h/2, N/2 + (k + 1) h/2]` pair off as `k, -k`, so about
  `N/(2h)` of them are prime free.
* Mean square, display 3: on a prime free block the integrand of `J` is `(window)²`, so
  `J ≫ h² N`.
* Selberg, display 4, the explicit formula consequence of RH: `J(N, h) ≪ h N log² N`. Taken
  here as the named hypothesis `SelbergJ`, NOT proved in this file; the lab's
  `Goldston1990Cor1Full.jg_pointwise` proves a natural number form of it under RH for `K² ≤ N`.
* Bookkeeping: the two bounds clash once `h ≥ C log² N`.
Constants: the lab uses blocks of length `h/2 = 2w` and the window `w = h/4` inside each block;
the paper's display 3 uses `J(N, h/8)`, more slack, same argument.

Definitions are restated locally, Mathlib plus `LeanLab.Common.Goldbach` only, to keep the
build small: `JgL` is word for word `Goldston1990.Jg` of Goldston1990Main.lean, and the
conclusion of `goldbach_interval_of_selbergJ` is the body of `Goldston1990.KataiMV` with `GNum`
unfolded.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.GoldbachGaps.Decomp1520
open Real Chebyshev Finset MeasureTheory Filter

/-- Display 2 of P0030, p. 285: `J(N, h) = ∫_1^N (θ(x + h) - θ(x) - h)² dx`. Same as
`Goldston1990.Jg`. -/
noncomputable def JgL (N h : ℝ) : ℝ := ∫ x in (1 : ℝ)..N, (θ (x + h) - θ x - h) ^ 2

/-- The closed real interval `[a, b]` contains no prime. -/
def PrimeFree (a b : ℝ) : Prop := ∀ p : ℕ, p.Prime → ¬ ((a : ℝ) ≤ p ∧ (p : ℝ) ≤ b)

/-- The closed real interval `[N, N + h]` contains no Goldbach number, an even sum of two
primes, Goldston's definition p. 285. -/
def NoGoldbachIn (N h : ℝ) : Prop :=
  ∀ n : ℕ, Even n → IsGoldbachSum n → ¬ (N ≤ n ∧ (n : ℝ) ≤ N + h)

/-- Selberg's bound, display 4 of P0030, p. 285, the consequence of RH through the explicit
formula: `J(N, w) ≤ A w N log² N` for `N ≥ N₁`, `1 ≤ w`, `w² ≤ N`. A NAMED HYPOTHESIS, the
range `w² ≤ N` is narrower than the paper needs to quote. Unit U-1520. -/
def SelbergJ (A N₁ : ℝ) : Prop :=
  ∀ N w : ℝ, N₁ ≤ N → 1 ≤ w → w ^ 2 ≤ N → JgL N w ≤ A * w * N * Real.log N ^ 2

/-! ### OPEN leaves -/

/-- Pairing, P0030 p. 285: if `[N, N + h]` contains no Goldbach number, `3 ≤ y` and
`3 ≤ N - y`, then `[y, y + h/2]` or `[N - y, N - y + h/2]` contains no prime; two odd primes,
one in each, would sum to an even number in `[N, N + h]`. Unit U-1520. -/
theorem pairing {N h y : ℝ} (hy : 3 ≤ y) (hy' : 3 ≤ N - y) (hG : NoGoldbachIn N h) :
    PrimeFree y (y + h / 2) ∨ PrimeFree (N - y) (N - y + h / 2) := by
  classical
  unfold PrimeFree
  by_contra! hn
  obtain ⟨⟨p, hp, hp1, hp2⟩, q, hq, hq1, hq2⟩ := hn
  have hp3 : 3 ≤ p := by exact_mod_cast (show (3 : ℝ) ≤ p by linarith)
  have hq3 : 3 ≤ q := by exact_mod_cast (show (3 : ℝ) ≤ q by linarith)
  have he : Even (p + q) := (hp.odd_of_ne_two (by omega)).add_odd (hq.odd_of_ne_two (by omega))
  apply hG (p + q) he ⟨p, q, hp, hq, rfl⟩
  push_cast
  constructor <;> linarith

/-- Covering count, P0030 p. 285: if for each `1 ≤ k ≤ M` one of `P k`, `P (-k)` holds, then
at least `M` integers `j` with `|j| ≤ M` satisfy `P j`. Unit U-1520. -/
theorem card_pairs (M : ℕ) (P : ℤ → Prop) [DecidablePred P]
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ M → P k ∨ P (-(k : ℤ))) :
    M ≤ ((Icc (-(M : ℤ)) M).filter P).card := by
  let f : ℕ → ℤ := fun k => if P k then k else -(k : ℤ)
  have hm : (Icc 1 M).card = M := by simp
  calc
    M = (Icc 1 M).card := hm.symm
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn f
      · intro k hk
        have hk' := Finset.mem_Icc.mp hk
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        dsimp [f]
        split_ifs with hp
        · exact ⟨⟨by omega, by exact_mod_cast hk'.2⟩, hp⟩
        · exact ⟨⟨by omega, by omega⟩, (h k hk'.1 hk'.2).resolve_left hp⟩
      · intro i hi j hj he
        have hi' := Finset.mem_Icc.mp hi
        have hj' := Finset.mem_Icc.mp hj
        dsimp [f] at he
        split_ifs at he <;> omega

/-- No prime in `(x, y]` gives `θ(y) = θ(x)`, used for display 3 of P0030, p. 285.
Unit U-1520. -/
theorem theta_eq_of_primeFree {x y : ℝ} (hxy : x ≤ y)
    (h : ∀ p : ℕ, p.Prime → ¬ (x < p ∧ (p : ℝ) ≤ y)) : θ y = θ x := by
  rw [theta_eq_sum_primesLE, theta_eq_sum_primesLE]
  congr 1
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hpY, hp⟩
    have hpy : (p : ℝ) ≤ y := (Nat.le_floor_iff' hp.ne_zero).mp hpY
    have hpx : (p : ℝ) ≤ x := le_of_not_gt fun hx => h p hp ⟨hx, hpy⟩
    exact ⟨(Nat.le_floor_iff' hp.ne_zero).mpr hpx, hp⟩
  · rintro ⟨hpX, hp⟩
    exact ⟨hpX.trans (Nat.floor_mono hxy), hp⟩

/-- The integrand of `J`, display 2 of P0030, is interval integrable on every interval.
Unit U-1520. -/
theorem jg_integrand_integrable (w a b : ℝ) :
    IntervalIntegrable (fun x => (θ (x + w) - θ x - w) ^ 2) MeasureTheory.volume a b := by
  apply IntegrableOn.intervalIntegrable
  have hm : Measurable (fun x : ℝ => (θ (x + w) - θ x - w) ^ 2) :=
    ((theta_mono.measurable.comp (measurable_id.add_const w)).sub
      theta_mono.measurable |>.sub measurable_const).pow_const 2
  apply IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top) hm.aestronglyMeasurable
    ((θ (max a b + w) + θ (max a b) + |w|) ^ 2)
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  have hxmax : x ≤ max a b := hx.2
  have ht : |θ (x + w)| ≤ θ (max a b + w) := by
    rw [abs_of_nonneg (theta_nonneg _)]
    exact theta_mono (by linarith)
  have ht' : |θ x| ≤ θ (max a b) := by
    rw [abs_of_nonneg (theta_nonneg _)]
    exact theta_mono hxmax
  have hb : |θ (x + w) - θ x - w| ≤ θ (max a b + w) + θ (max a b) + |w| := by
    calc
      _ ≤ |θ (x + w) - θ x| + |w| := abs_sub _ _
      _ ≤ |θ (x + w)| + |θ x| + |w| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (θ (x + w) - θ x - w), abs_nonneg (θ (x + w) - θ x - w)]

/-- The integral of a nonnegative integrable `f` over `[1, N]` is at least the sum of its
integrals over windows `[a j, a j + w] ⊂ [1, N]` that do not overlap, the step from the set `E`
to display 3 of P0030, p. 285. Unit U-1520. -/
theorem integral_ge_sum_windows {f : ℝ → ℝ} {N w : ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ a b, IntervalIntegrable f MeasureTheory.volume a b) (hN : 1 ≤ N)
    (S : Finset ℤ) (a : ℤ → ℝ) (hw : 0 < w) (hin : ∀ j ∈ S, 1 ≤ a j ∧ a j + w ≤ N)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i < j → a i + w ≤ a j) :
    ∑ j ∈ S, ∫ x in a j..(a j + w), f x ≤ ∫ x in (1 : ℝ)..N, f x := by
  classical
  induction S using Finset.induction_on_max generalizing N with
  | empty =>
    simpa using intervalIntegral.integral_nonneg_of_forall hN hf0
  | insert j S hmax ih =>
    have hj : j ∉ S := by intro hj; exact (lt_irrefl j) (hmax j hj)
    have hjin := hin j (mem_insert_self j S)
    have hSin : ∀ i ∈ S, 1 ≤ a i ∧ a i + w ≤ a j := by
      intro i hi
      exact ⟨(hin i (mem_insert_of_mem hi)).1,
        hsep i (mem_insert_of_mem hi) j (mem_insert_self j S) (hmax i hi)⟩
    have hSsep : ∀ i ∈ S, ∀ k ∈ S, i < k → a i + w ≤ a k := by
      intro i hi k hk hik
      exact hsep i (mem_insert_of_mem hi) k (mem_insert_of_mem hk) hik
    have hs := ih hjin.1 hSin hSsep
    rw [sum_insert hj]
    calc
      _ ≤ (∫ x in a j..(a j + w), f x) + ∫ x in (1 : ℝ)..a j, f x := add_le_add le_rfl hs
      _ = ∫ x in (1 : ℝ)..(a j + w), f x := by
        rw [add_comm, intervalIntegral.integral_add_adjacent_intervals (hfi _ _) (hfi _ _)]
      _ ≤ ∫ x in (1 : ℝ)..N, f x :=
        intervalIntegral.integral_mono_interval le_rfl (by linarith) hjin.2
          (Filter.Eventually.of_forall hf0) (hfi _ _)

/-- A function equal to the constant `c` on `[a, a + w]` has integral `c w` there, the last
equality of display 3 of P0030, p. 285. Unit U-1520. -/
theorem integral_window_const {f : ℝ → ℝ} {a w c : ℝ} (hw : 0 ≤ w)
    (h : ∀ x ∈ Set.Icc a (a + w), f x = c) : ∫ x in a..(a + w), f x = c * w := by
  calc
    _ = ∫ x in a..(a + w), c := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply h x
      simpa only [Set.uIcc_of_le (by linarith : a ≤ a + w)] using hx
    _ = c * w := by simp [mul_comm]

/-- Bookkeeping, P0030 p. 286: for every constant `c`, `c log⁴ N < N` for all large real `N`.
Unit U-1520. -/
theorem eventually_log_four (c : ℝ) :
    ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N → c * Real.log N ^ 4 < N := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).const_mul_left c
  have he := h.eventuallyLT_norm_of_eventually_pos (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hx] using hx)
  have : ∀ᶠ N : ℝ in atTop, c * Real.log N ^ 4 < N := by
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with N hN hpos
    exact lt_of_le_of_lt (le_abs_self _) (by simpa [Real.norm_eq_abs, abs_of_pos hpos] using hN)
  exact eventually_atTop.mp this

/-- Bookkeeping for display 3 of P0030, p. 285: `M ≥ (N/2 - 3 - w)/(2w) - 1` prime free
blocks, each giving `w³`, give `M w³ ≥ w² N/4 - (3/2) w² - (3/2) w³`. Unit U-1520. -/
theorem J_lower_algebra {N w M : ℝ} (hw : 0 < w) (hM : (N / 2 - 3 - w) / (2 * w) - 1 ≤ M) :
    w ^ 2 * N / 4 - 3 / 2 * w ^ 2 - 3 / 2 * w ^ 3 ≤ M * w ^ 3 := by
  have hw2 : 0 < 2 * w := by linarith
  have hw3 : 0 < w ^ 2 := by positivity
  have h1 : (N / 2 - 3 - w) / (2 * w) ≤ M + 1 := by linarith
  have h2 : N / 2 - 3 - w ≤ (M + 1) * (2 * w) := (div_le_iff₀ hw2).mp h1
  have h3 : (N / 2 - 3 - w) * (w ^ 2 / 2) ≤ (M + 1) * (2 * w) * (w ^ 2 / 2) := by
    nlinarith
  have h4 : (M + 1) * (2 * w) * (w ^ 2 / 2) = M * w ^ 3 + w ^ 3 := by ring
  have h5 : (N / 2 - 3 - w) * (w ^ 2 / 2) = w ^ 2 * N / 4 - 3 / 2 * w ^ 2 - w ^ 3 / 2 := by ring
  nlinarith

/-- The clash of display 3 with display 4, P0030 p. 286, at `w = 8 A L²`, `L = log N`: if
`1 ≤ A`, `1 ≤ L` and `200 A² L⁴ < N` then `A w N L² < w² N/4 - (3/2) w² - (3/2) w³`.
Unit U-1520. -/
theorem final_ineq {A L N : ℝ} (hA : 1 ≤ A) (hL : 1 ≤ L) (hN : 200 * A ^ 2 * L ^ 4 < N) :
    A * (8 * A * L ^ 2) * N * L ^ 2 <
      (8 * A * L ^ 2) ^ 2 * N / 4 - 3 / 2 * (8 * A * L ^ 2) ^ 2
        - 3 / 2 * (8 * A * L ^ 2) ^ 3 := by
  have h1 : A * (8 * A * L ^ 2) * N * L ^ 2 = 8 * A ^ 2 * L ^ 4 * N := by ring
  have h2 : (8 * A * L ^ 2) ^ 2 * N / 4 = 16 * A ^ 2 * L ^ 4 * N := by ring
  have h3 : 3 / 2 * (8 * A * L ^ 2) ^ 2 = 96 * A ^ 2 * L ^ 4 := by ring
  have h4 : 3 / 2 * (8 * A * L ^ 2) ^ 3 = 768 * A ^ 3 * L ^ 6 := by ring
  rw [h1, h2, h3, h4]
  have hpos : 0 < 8 * A ^ 2 * L ^ 4 := by positivity
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have h_AL : A ^ 2 * L ^ 4 ≤ A ^ 3 * L ^ 6 := by
    have h_a : A ^ 2 ≤ A ^ 3 := by
      calc
        A ^ 2 = A ^ 2 * 1 := by ring
        _ ≤ A ^ 2 * A := mul_le_mul_of_nonneg_left hA (by positivity)
        _ = A ^ 3 := by ring
    have h_l : L ^ 4 ≤ L ^ 6 := by
      calc
        L ^ 4 = L ^ 4 * 1 := by ring
        _ ≤ L ^ 4 * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
        _ = L ^ 6 := by ring
    nlinarith
  have h5a : 96 * A ^ 2 * L ^ 4 ≤ 96 * A ^ 3 * L ^ 6 := by linarith
  have h5 : 96 * A ^ 2 * L ^ 4 + 768 * A ^ 3 * L ^ 6 ≤ 864 * A ^ 3 * L ^ 6 := by linarith
  have h6 : 864 * A ^ 3 * L ^ 6 = 8 * A ^ 2 * L ^ 4 * (108 * A * L ^ 2) := by ring
  have hA2 : A ≤ A ^ 2 := by
    calc
      A = A * 1 := by ring
      _ ≤ A * A := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = A ^ 2 := by ring
  have hL4 : L ^ 2 ≤ L ^ 4 := by
    calc
      L ^ 2 = L ^ 2 * 1 := by ring
      _ ≤ L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = L ^ 4 := by ring
  have h7 : 108 * A * L ^ 2 ≤ 200 * A ^ 2 * L ^ 4 := by nlinarith
  have h8 : 8 * A ^ 2 * L ^ 4 * (108 * A * L ^ 2) ≤ 8 * A ^ 2 * L ^ 4 * (200 * A ^ 2 * L ^ 4) := by
    exact mul_le_mul_of_nonneg_left h7 hpos.le
  have h9 : 8 * A ^ 2 * L ^ 4 * (200 * A ^ 2 * L ^ 4) < 8 * A ^ 2 * L ^ 4 * N := by
    nlinarith
  linarith

/-- Size conditions at `w = 8 A L²`: if `1 ≤ A`, `1 ≤ L` and `200 A² L⁴ < N` then `1 ≤ w`,
`w² ≤ N` and `w + 3 ≤ N/2`, the ranges needed for displays 3 and 4 of P0030. Unit U-1520. -/
theorem size_conditions {A L N : ℝ} (hA : 1 ≤ A) (hL : 1 ≤ L) (hN : 200 * A ^ 2 * L ^ 4 < N) :
    1 ≤ 8 * A * L ^ 2 ∧ (8 * A * L ^ 2) ^ 2 ≤ N ∧ 8 * A * L ^ 2 + 3 ≤ N / 2 := by
  have h1 : 1 ≤ 8 * A * L ^ 2 := by nlinarith
  have h2 : (8 * A * L ^ 2) ^ 2 ≤ 200 * A ^ 2 * L ^ 4 := by
    calc
      (8 * A * L ^ 2) ^ 2 = 64 * A ^ 2 * L ^ 4 := by ring
      _ ≤ 200 * A ^ 2 * L ^ 4 := by nlinarith
  have h3 : (8 * A * L ^ 2) ^ 2 ≤ N := by linarith
  have h4 : 8 * A * L ^ 2 + 3 ≤ N / 2 := by
    have h5 : 8 * A * L ^ 2 + 3 ≤ 64 * A ^ 2 * L ^ 4 + 3 := by nlinarith
    have h6 : 64 * A ^ 2 * L ^ 4 + 3 ≤ 100 * A ^ 2 * L ^ 4 := by nlinarith
    have h7 : 100 * A ^ 2 * L ^ 4 = (200 * A ^ 2 * L ^ 4) / 2 := by ring
    linarith
  exact ⟨h1, h3, h4⟩

/-! ### Assembly, real proofs from the leaves -/

/-- A prime free block `[a, a + 2w]` gives `θ(x + w) = θ(x)` for `x ∈ [a, a + w]`.
Unit U-1520. -/
theorem window_theta {a w x : ℝ} (hw : 0 < w) (hP : PrimeFree a (a + 2 * w))
    (hx : x ∈ Set.Icc a (a + w)) : θ (x + w) = θ x := by
  apply theta_eq_of_primeFree (by linarith)
  intro p hp hxp
  exact hP p hp ⟨by linarith [hx.1, hxp.1], by linarith [hx.2, hxp.2]⟩

/-- Display 3 of P0030, p. 285, explicit: if `[N, N + 4w]` contains no Goldbach number,
`1 ≤ w` and `w + 3 ≤ N/2`, then `J(N, w) ≥ w² N/4 - (3/2) w² - (3/2) w³`. PROVED from the
leaves. Unit U-1520. -/
theorem J_lower_of_noGoldbach {N w : ℝ} (hw : 1 ≤ w) (hNw : w + 3 ≤ N / 2)
    (hG : NoGoldbachIn N (4 * w)) :
    w ^ 2 * N / 4 - 3 / 2 * w ^ 2 - 3 / 2 * w ^ 3 ≤ JgL N w := by
  classical
  have hw0 : 0 < w := by linarith
  set X := (N / 2 - 3 - w) / (2 * w) with hX
  have hX0 : 0 ≤ X := div_nonneg (by linarith) (by linarith)
  set M := ⌊X⌋₊ with hMdef
  have hMX : (M : ℝ) ≤ X := Nat.floor_le hX0
  have hMX' : X - 1 ≤ (M : ℝ) := (Nat.sub_one_lt_floor X).le
  have h2wX : 2 * w * X = N / 2 - 3 - w := by
    rw [hX]; field_simp
  have h2wM : 2 * w * (M : ℝ) ≤ N / 2 - 3 - w := by
    rw [← h2wX]; exact mul_le_mul_of_nonneg_left hMX (by linarith)
  set a : ℤ → ℝ := fun j => N / 2 + (j : ℝ) * (2 * w) with ha
  set P : ℤ → Prop := fun j => PrimeFree (a j) (a j + 2 * w) with hP
  have hpair : ∀ k : ℕ, 1 ≤ k → k ≤ M → P k ∨ P (-(k : ℤ)) := by
    intro k _ hkM
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h2wk : 2 * w * (k : ℝ) ≤ N / 2 - 3 - w :=
      le_trans (mul_le_mul_of_nonneg_left hkM' (by linarith)) h2wM
    have hy : (3 : ℝ) ≤ a k := by
      simp only [ha, Int.cast_natCast]; nlinarith
    have hy' : (3 : ℝ) ≤ N - a k := by
      simp only [ha, Int.cast_natCast]; nlinarith
    rcases pairing hy hy' hG with h | h
    · left
      show PrimeFree (a k) (a k + 2 * w)
      rwa [show a k + 2 * w = a k + 4 * w / 2 by ring]
    · right
      have e1 : a (-(k : ℤ)) = N - a k := by
        simp only [ha, Int.cast_neg, Int.cast_natCast]; ring
      show PrimeFree (a (-(k : ℤ))) (a (-(k : ℤ)) + 2 * w)
      rw [e1, show N - a k + 2 * w = N - a k + 4 * w / 2 by ring]
      exact h
  set S := (Icc (-(M : ℤ)) M).filter P with hS
  have hcard : M ≤ S.card := card_pairs M P hpair
  have hjM : ∀ j ∈ S, -(M : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ M := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).1
    rw [Finset.mem_Icc] at hj'
    exact ⟨by exact_mod_cast hj'.1, by exact_mod_cast hj'.2⟩
  have hin : ∀ j ∈ S, 1 ≤ a j ∧ a j + w ≤ N := by
    intro j hj
    obtain ⟨h1, h2⟩ := hjM j hj
    have hlo : -(2 * w * (M : ℝ)) ≤ (j : ℝ) * (2 * w) := by nlinarith
    have hhi : (j : ℝ) * (2 * w) ≤ 2 * w * (M : ℝ) := by nlinarith
    simp only [ha]
    constructor <;> linarith
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i < j → a i + w ≤ a j := by
    intro i _ j _ hij
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    simp only [ha]
    nlinarith
  set f : ℝ → ℝ := fun x => (θ (x + w) - θ x - w) ^ 2 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have hfi : ∀ a b, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => jg_integrand_integrable w a b
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsum := integral_ge_sum_windows hf0 hfi hN1 S a hw0 hin hsep
  have hwin : ∀ j ∈ S, ∫ x in a j..(a j + w), f x = w ^ 2 * w := by
    intro j hj
    have hPj : P j := (Finset.mem_filter.mp hj).2
    apply integral_window_const hw0.le
    intro x hx
    simp only [hf]
    rw [window_theta hw0 hPj hx]
    ring
  rw [Finset.sum_congr rfl hwin, Finset.sum_const, nsmul_eq_mul] at hsum
  have hJ : JgL N w = ∫ x in (1 : ℝ)..N, f x := rfl
  have hcard' : (M : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
  have halg := J_lower_algebra hw0 hMX'
  have hw3 : 0 ≤ w ^ 3 := by positivity
  have : (M : ℝ) * w ^ 3 ≤ (S.card : ℝ) * (w ^ 2 * w) := by
    rw [show w ^ 2 * w = w ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right hcard' hw3
  rw [hJ]
  linarith

/-- Kátai, Montgomery-Vaughan as presented by Goldston, P0030 pp. 285 and 286: Selberg's bound,
display 4, gives an absolute `C` with a Goldbach number in `[N, N + C log² N]` for all large
real `N`. PROVED CONDITIONAL ON the named hypothesis `SelbergJ` only, from the leaves.
Unit U-1520. -/
theorem goldbach_interval_of_selbergJ {A N₁ : ℝ} (hS : SelbergJ A N₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
      ∃ n : ℕ, Even n ∧ IsGoldbachSum n ∧ N ≤ n ∧ (n : ℝ) ≤ N + C * Real.log N ^ 2 := by
  set A' := max A 1 with hA'def
  have hA' : 1 ≤ A' := le_max_right _ _
  obtain ⟨N2, hN2⟩ := eventually_log_four (200 * A' ^ 2)
  refine ⟨32 * A', by positivity, max (max N₁ N2) (Real.exp 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNe : Real.exp 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNe
  have hL : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  have hbig := hN2 N hN2'
  obtain ⟨h1w, hw2, hw3⟩ := size_conditions hA' hL hbig
  by_contra hcon
  have hG : NoGoldbachIn N (4 * (8 * A' * Real.log N ^ 2)) := by
    intro n he hg hin
    apply hcon
    refine ⟨n, he, hg, hin.1, ?_⟩
    have := hin.2
    linarith
  have hlow := J_lower_of_noGoldbach h1w hw3 hG
  have hup := hS N (8 * A' * Real.log N ^ 2) hN1 h1w hw2
  have hfin := final_ineq hA' hL hbig
  have hAA : A * (8 * A' * Real.log N ^ 2) * N * Real.log N ^ 2 ≤
      A' * (8 * A' * Real.log N ^ 2) * N * Real.log N ^ 2 := by
    have h0 : 0 ≤ (8 * A' * Real.log N ^ 2) * N * Real.log N ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left A 1) h0
    linarith
  linarith

/-- Under RH, through Selberg's bound taken as a named input: the Kátai, Montgomery-Vaughan
statement quoted in P0030 p. 285. PROVED CONDITIONAL ON `hSel` only. Unit U-1520. -/
theorem kataiMV_of_selbergRH (hSel : RiemannHypothesis → ∃ A N₁ : ℝ, SelbergJ A N₁) :
    RiemannHypothesis → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
      ∃ n : ℕ, Even n ∧ IsGoldbachSum n ∧ N ≤ n ∧ (n : ℝ) ≤ N + C * Real.log N ^ 2 := by
  intro hRH
  obtain ⟨A, N₁, h⟩ := hSel hRH
  exact goldbach_interval_of_selbergJ h

/-! ### Vacuity -/

/-- Vacuity for `pairing`: `[7.1, 7.6]` holds no natural number, so no Goldbach number, and
`y = 3`, `N - y = 4.1` meet the side conditions. Unit U-1520. -/
theorem noGoldbachIn_vacuity : NoGoldbachIn (71 / 10) (1 / 2) := by
  intro n _ _ hn
  obtain ⟨h1, h2⟩ := hn
  have h8 : (8 : ℝ) ≤ n := by
    have : 7 < n := by exact_mod_cast (show (7 : ℝ) < n by linarith)
    exact_mod_cast this
  linarith

/-- Vacuity for `PrimeFree` and the block lemmas: `[24, 28]` holds no prime. Unit U-1520. -/
theorem primeFree_vacuity : PrimeFree 24 28 := by
  intro p hp hpin
  obtain ⟨h1, h2⟩ := hpin
  have h1' : 24 ≤ p := by exact_mod_cast h1
  have h2' : p ≤ 28 := by exact_mod_cast h2
  interval_cases p <;> norm_num at hp

end LeanLab.GoldbachGaps.Decomp1520
