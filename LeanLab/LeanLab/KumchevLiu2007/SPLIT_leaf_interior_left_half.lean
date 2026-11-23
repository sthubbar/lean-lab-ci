/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 and its use
on page 15 after display 52. Split of the open leaf `leaf_interior_left_half`
of `SPLIT_lemma34_second_sum_dyadic`, burst 20261122, unit P1122-0152.

The leaf is the mean square over the left half [Y/4, Y/2] of the t window of
the second sum of display 52 for one dyadic block of primes M <= p < 2M,
Y = windowY X eps. The paper gets it from Lemma 3.4 with x = Y, y = H,
(m, k) = (p, m / p) and z = z1 = Y^(1/6 + eps/2). The split:

* `lemma34`, LEAF HARD: Lemma 3.4 of page 11 in the paper's own generality.
  Its proof on pages 11 and 12 rests on Lemmas 3.1 and 3.2, cited to Liu and
  Zhan 1997, and Lemma 3.3, cited to Kumchev 2006. Citation wall.
* `block_sum_reindex`, PROVED 20261122: the rewriting of page 15, the lab form of
  the second sum for one block equals the double sum of Lemma 3.4 with
  (m, k) = (p, m / p) and a_m the indicator of the primes of the block.
* `left_half_params`, PROVED 20261122: the parameter checks of page 15, that the
  instance x = Y/4, y = H, z = z1, M below z0 meets the hypotheses of
  Lemma 3.4 for X large, including the remark that z1 <= H Y^(-1/2) L^(-2B).
* `left_half_small_H`: PROVED from the three results above, the leaf for
  eps below 1/6 and H at most Y/4, the range where Lemma 3.4 applies as
  printed, with x = Y/4.
* `left_half_band_low` and `left_half_band_high`, PROVED from `lemma34`, and
  `left_half_band` PROVED from them, the old band leaf: the leaf for eps below 1/6 and
  Y/4 < H < Y (log X)^(A/2). This band is outside the hypothesis y <= x of
  Lemma 3.4, the QUESTION recorded in the parent files. The routes, revised
  after the independent audit of 20261122, are in the doc comments.
* `leaf_interior_left_half_split`: PROVED from the leaves, the exact
  statement of `leaf_interior_left_half`, through
  `leaf_interior_left_half_of_core`.

Paper notation, page 3: m ~ M means M <= m < 2M, and Phi(n, z) of display 10
is 1 when every prime factor of n is at least z, which is `roughWeight z n`.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.InteriorHalvesAux
import LeanLab.KumchevLiu2007.SPLIT_lemma34_second_sum_dyadic

namespace LeanLab.KumchevLiu2007.Eq33RouteD.LeftHalf1122

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4, HARD, cited. For x large,
x^(1/2) <= y <= x, display 41 with L = log x, |a_m| <= tau(m)^c,
1 <= M <= x^(1/4) L^(-2B) and 2 <= z <= y x^(-1/2) L^(-2B), the mean square
over x to 2x of the sum over m ~ M, page 3 M <= m < 2M, and k of
a_m Phi(k, z) e(alpha m^2 k^2) with t < m^2 k^2 <= t + y is << y^2 L^(-A).
The cap k <= (3x)^(1/2) is harmless. Proof pages 11 and 12 uses Lemmas 3.1,
3.2, cited to Liu and Zhan 1997, and 3.3, cited to Kumchev 2006. -/
theorem lemma34 (c : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ ∀ x y : ℝ, x0 ≤ x → x ^ (1 / 2 : ℝ) ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y * Real.log x ^ (-B) →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ am : ℕ → ℂ, (∀ m : ℕ, ‖am m‖ ≤ ((Nat.divisors m).card : ℝ) ^ c) →
        ∀ M z : ℝ, 1 ≤ M → M ≤ x ^ (1 / 4 : ℝ) * Real.log x ^ (-2 * B) →
        2 ≤ z → z ≤ y * x ^ (-1 / 2 : ℝ) * Real.log x ^ (-2 * B) →
        (∫ t in x..(2 * x),
          ‖∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
              (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
            ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + y),
              am m * roughWeight z k *
                fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 * Real.log x ^ (-A) := by
  sorry

/-- PROVED. P0088 page 15, the sentence after display 52: Lemma 3.4 is
applied to the second sum with (m, k) = (p, m / p). For one dyadic block of
primes M <= p < 2M between z1 and z0, the lab form of the short sum, over m in
the square root window with t < m^2 <= t + H of the sum over the primes p of
the block dividing m of Phi(m / p, w) e(alpha m^2), equals the double sum of
Lemma 3.4 over p ~ M and k with a_p the indicator of the primes of the block.
The two side conditions say that every m with t < m^2 <= t + H lies in the
window and is at most (3x)^(1/2); both hold for t in [Y/4, Y/2] and
H <= Y/4 with x = Y/4. -/
theorem block_sum_reindex (Y x t H z1 z0 M w α : ℝ) (ht : 0 ≤ t)
    (hwin : ∀ n : ℕ, t < (n : ℝ) ^ 2 → (n : ℝ) ^ 2 ≤ t + H → n ∈ squareWindow Y)
    (hk : ∀ n : ℕ, (n : ℝ) ^ 2 ≤ t + H → n ≤ ⌊Real.sqrt (3 * x)⌋₊) :
    (∑ m ∈ (squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
      (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        roughWeight w (m / p)) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
    ∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
        (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + H),
        (if m.Prime ∧ z1 ≤ (m : ℝ) ∧ (m : ℝ) < z0 then (1 : ℂ) else 0) *
          roughWeight w k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  have hR : (∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
        (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + H),
        (if m.Prime ∧ z1 ≤ (m : ℝ) ∧ (m : ℝ) < z0 then (1 : ℂ) else 0) *
          roughWeight w k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) =
      ∑ m ∈ ((Finset.range (⌊2 * M⌋₊ + 1)).filter
        (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M)).filter
          (fun m : ℕ => m.Prime ∧ z1 ≤ (m : ℝ) ∧ (m : ℝ) < z0),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + H),
          roughWeight w k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
    rw [Finset.sum_filter (fun m : ℕ => m.Prime ∧ z1 ≤ (m : ℝ) ∧ (m : ℝ) < z0)]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [hR]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => (⟨x.2, x.1 / x.2⟩ : Σ _ : ℕ, ℕ))
    (fun y _ => (⟨y.1 * y.2, y.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, p⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hx ⊢
    obtain ⟨⟨_, htn, hnH⟩, ⟨⟨_, hpr, hz1, hz0, hd⟩, hM, hM2⟩⟩ := hx
    have hpk : p * (n / p) = n := Nat.mul_div_cancel' hd
    refine ⟨⟨⟨?_, hM, hM2⟩, hpr, hz1, hz0⟩, ?_, ?_⟩
    · have : p ≤ ⌊2 * M⌋₊ := Nat.le_floor hM2.le
      omega
    · have h1 := hk n hnH
      have h2 : n / p ≤ n := Nat.div_le_self n p
      omega
    · rw [hpk]; exact ⟨htn, hnH⟩
  · rintro ⟨p, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hy ⊢
    obtain ⟨⟨⟨_, hM, hM2⟩, hpr, hz1, hz0⟩, _, htn, hnH⟩ := hy
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at htn
      linarith
    refine ⟨⟨hwin _ htn hnH, htn, hnH⟩, ⟨?_, hpr, hz1, hz0, dvd_mul_right p k⟩, hM, hM2⟩
    have : p ≤ p * k := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hk0)
    omega
  · rintro ⟨n, p⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hx
    have hpk : p * (n / p) = n := Nat.mul_div_cancel' hx.2.1.2.2.2.2
    simp [hpk]
  · rintro ⟨p, k⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hy
    have hp : 0 < p := hy.1.2.1.pos
    simp [Nat.mul_div_cancel_left k hp]
  · rintro ⟨n, p⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hx
    have hpk : p * (n / p) = n := Nat.mul_div_cancel' hx.2.1.2.2.2.2
    simp only [hpk]

/-- PROVED. P0088 page 15, the paragraph after display 52: the
parameter checks for Lemma 3.4 with x = Y/4, y = H, z = z1 = Y^(1/6 + eps/2)
and M below z0 = Y^(1/4) (log X)^(-2B), Y = windowY X eps. For B >= 1,
0 < eps < 1/6 and X large: x is large; z1 >= 2; the remark of page 15 that
z1 <= H x^(-1/2) L^(-2B) once H >= X^(7/18 + eps), which is the lab form of
theta2 >= 2/3 + eps; x^(1/2) <= H; the remark that z0 is fixed by the bound
on M of Lemma 3.4, here z0 <= x^(1/4) L^(-2B); and L = log x lies between
(7/24) log X and log X, so the log powers of the leaf and of the lemma agree
up to constants. -/
theorem left_half_params (B ε x0 : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) (hε' : ε < 1 / 6) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      x0 ≤ windowY X ε / 4 ∧
      2 ≤ windowY X ε ^ (1 / 6 + ε / 2) ∧
      (∀ H : ℝ, X ^ (7 / 18 + ε) ≤ H →
        windowY X ε ^ (1 / 6 + ε / 2) ≤
          H * (windowY X ε / 4) ^ (-1 / 2 : ℝ) *
            Real.log (windowY X ε / 4) ^ (-2 * B)) ∧
      (windowY X ε / 4) ^ (1 / 2 : ℝ) ≤ X ^ (7 / 18 + ε) ∧
      windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
        (windowY X ε / 4) ^ (1 / 4 : ℝ) * Real.log (windowY X ε / 4) ^ (-2 * B) ∧
      1 ≤ Real.log (windowY X ε / 4) ∧
      7 / 24 * Real.log X ≤ Real.log (windowY X ε / 4) ∧
      Real.log (windowY X ε / 4) ≤ Real.log X := by
  set K : ℝ := 12 + 4 * |x0| + (12 * B / ε) ^ 2 with hK
  have hK12 : 12 ≤ K := by nlinarith [abs_nonneg x0, sq_nonneg (12 * B / ε)]
  refine ⟨Real.exp K, ?_, ?_⟩
  · have := Real.add_one_le_exp K; linarith
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos K) hX
  have hLx : K ≤ Real.log X := by
    rw [← Real.log_exp K]; exact Real.log_le_log (Real.exp_pos K) hX
  set Lx := Real.log X with hLxdef
  have hLx0 : 0 ≤ Lx := by linarith
  set a : ℝ := 7 / 12 + ε / 2 with ha
  have hYe : windowY X ε = Real.exp (a * Lx) := by
    unfold windowY; rw [Real.rpow_def_of_pos hXpos, ha, hLxdef]; ring_nf
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log (windowY X ε / 4) = a * Lx - Real.log 4 := by
    rw [hYe, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  set l := Real.log (windowY X ε / 4) with hldef
  have hY4 : windowY X ε / 4 = Real.exp l :=
    (Real.exp_log (by rw [hYe]; positivity)).symm
  have hsq : (12 * B / ε) ^ 2 ≤ Lx := by nlinarith [abs_nonneg x0]
  have hl1 : 7 / 24 * Lx ≤ l := by rw [hl]; nlinarith [mul_nonneg hε.le hLx0]
  have hl0 : 0 < l := by nlinarith
  have hlLx : l ≤ Lx := by rw [hl]; nlinarith [mul_nonneg hε.le hLx0]
  have hl23 : l ≤ 2 / 3 * Lx := by rw [hl]; nlinarith [mul_nonneg hε.le hLx0]
  have hLxpos : 0 < Lx := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hl1, hlLx⟩
  · rw [hY4]
    nlinarith [Real.add_one_le_exp l, le_abs_self x0, abs_nonneg x0]
  · rw [hYe, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    nlinarith [Real.add_one_le_exp (a * Lx * (1 / 6 + ε / 2)), mul_nonneg hε.le hLx0,
      mul_nonneg (mul_nonneg hε.le hε.le) hLx0]
  · intro H hH
    rw [Real.rpow_def_of_pos hXpos] at hH
    rw [hY4, hYe, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hl0]
    have hs0 : 0 ≤ Real.sqrt Lx := Real.sqrt_nonneg _
    have hspos : 0 < Real.sqrt Lx := Real.sqrt_pos.mpr hLxpos
    have hss : Real.sqrt Lx ^ 2 = Lx := Real.sq_sqrt hLx0
    have hlogl : Real.log l ≤ 2 * Real.sqrt Lx := by
      have h1 : Real.log l ≤ Real.log Lx := Real.log_le_log hl0 hlLx
      have h2 : Real.log (Real.sqrt Lx) = Real.log Lx / 2 := Real.log_sqrt hLx0
      have h3 := Real.log_le_sub_one_of_pos hspos
      linarith
    have h12 : 12 * B / ε ≤ Real.sqrt Lx := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity)] at this
    have h12' : 12 * B ≤ Real.sqrt Lx * ε := (div_le_iff₀ hε).mp h12
    have hs2 : 12 * B * Real.sqrt Lx ≤ ε * Lx := by
      have := mul_le_mul_of_nonneg_left h12' hs0
      nlinarith
    have hBl : B * Real.log l ≤ B * (2 * Real.sqrt Lx) :=
      mul_le_mul_of_nonneg_left hlogl (by linarith)
    have hcoef : ε * ε * Lx ≤ ε / 6 * Lx :=
      mul_le_mul_of_nonneg_right (by nlinarith) hLx0
    calc Real.exp (a * Lx * (1 / 6 + ε / 2))
        ≤ Real.exp (Lx * (7 / 18 + ε)) * Real.exp (l * (-1 / 2)) *
            Real.exp (Real.log l * (-2 * B)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hexp : a * Lx * (1 / 6 + ε / 2) + a * Lx / 2 =
              7 / 18 * Lx + 5 / 8 * (ε * Lx) + 1 / 4 * (ε * ε * Lx) := by rw [ha]; ring
          have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
          linarith
      _ ≤ H * Real.exp (l * (-1 / 2)) * Real.exp (Real.log l * (-2 * B)) := by gcongr
  · rw [hY4, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos hXpos]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hε.le hLx0]
  · rw [hY4, hYe, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hl0,
      Real.rpow_def_of_pos hLxpos, zpow_neg, zpow_two, ← Real.exp_add, ← Real.exp_neg,
      ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log l ≤ Real.log (2 / 3 * Lx) := Real.log_le_log hl0 hl23
    rw [Real.log_mul (by norm_num) hLxpos.ne'] at h1
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2 / 3)
    have hBl : B * Real.log l ≤ B * (Real.log Lx - 1 / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · linarith

/-- PROVED from the leaves `lemma34`, `block_sum_reindex` and
`left_half_params`: P0088 page 15, Lemma 3.4 with x = Y/4, y = H,
(m, k) = (p, m / p) and z = z1 gives the leaf `leaf_interior_left_half` for
eps below 1/6 and H at most Y/4, the range where y <= x. The coefficient a_p
is the indicator of the primes of the block, so c = 0. -/
theorem left_half_small_H (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H ≤ windowY X ε / 4 →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h34⟩ := lemma34 0 A hA
  refine ⟨max B1 1, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε hε' => ?_⟩
  obtain ⟨C, x0, hC, k34⟩ := h34 B ((le_max_left _ _).trans hB)
  obtain ⟨X0, hX0, hP⟩ := left_half_params B ε x0 ((le_max_right _ _).trans hB) hε hε'
  have hK : (0 : ℝ) < (24 / 7) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  refine ⟨C * (24 / 7) ^ A, X0, mul_pos hC hK, hX0, ?_⟩
  intro X H hX hHl hHu hHs α q a hcop hqP hqQ hclose M hM htop hlow
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hP X hX
  have hX1 : 1 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hL0 : 0 ≤ Real.log (windowY X ε / 4) := by linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one ((le_max_right _ _).trans hB)
  have hPq : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hlogX B
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := hPq.trans hqP
    exact_mod_cast this
  have hLB : Real.log (windowY X ε / 4) ^ B ≤ Real.log X ^ B :=
    Real.rpow_le_rpow hL0 p8 hB0
  have hLBpos : 0 < Real.log (windowY X ε / 4) ^ B := Real.rpow_pos_of_pos (by linarith) B
  have hH0 : 0 ≤ H := le_trans (Real.rpow_nonneg (by linarith) _) hHl
  have h41a : Real.log (windowY X ε / 4) ^ B ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt hLB hqP)
  have h41b : (q : ℝ) ≤ H * Real.log (windowY X ε / 4) ^ (-B) := by
    rw [Real.rpow_neg hL0, ← div_eq_mul_inv]
    exact hqQ.trans (div_le_div_of_nonneg_left hH0 hLBpos hLB)
  have h41c : |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 :=
    display41_of_minor hq0 hqQ hclose
  have ham : ∀ m : ℕ, ‖(fun m : ℕ => if m.Prime ∧ windowY X ε ^ (1 / 6 + ε / 2) ≤ (m : ℝ) ∧
      (m : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) then (1 : ℂ) else 0) m‖ ≤
      ((Nat.divisors m).card : ℝ) ^ (0 : ℕ) := by
    intro m
    simp only [pow_zero]
    split_ifs <;> simp
  have key := k34 (windowY X ε / 4) H p1 (p4.trans hHl) hHs α q a hcop h41a h41b h41c _ ham
    M (windowY X ε ^ (1 / 6 + ε / 2)) hM (le_of_lt (lt_of_lt_of_le htop p5)) p2 (p3 H hHl)
  rw [show 2 * (windowY X ε / 4) = windowY X ε / 2 by ring] at key
  have hcongr : (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
              (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
            ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 4))⌋₊ + 1)).filter
              (fun k : ℕ => t < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ t + H),
              (fun m : ℕ => if m.Prime ∧ windowY X ε ^ (1 / 6 + ε / 2) ≤ (m : ℝ) ∧
                (m : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)
                then (1 : ℂ) else 0) m * roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) k *
                fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hwin : ∀ n : ℕ, t < (n : ℝ) ^ 2 → (n : ℝ) ^ 2 ≤ t + H →
        n ∈ squareWindow (windowY X ε) := by
      intro n hn1 hn2
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hs := Real.sq_sqrt hY.le
      have hs0 := Real.sqrt_nonneg (windowY X ε)
      have hlt : (n : ℝ) < Real.sqrt (windowY X ε) := by nlinarith
      simp only [squareWindow, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor hlt.le), ?_, hlt⟩
      nlinarith
    have hk : ∀ n : ℕ, (n : ℝ) ^ 2 ≤ t + H → n ≤ ⌊Real.sqrt (3 * (windowY X ε / 4))⌋₊ := by
      intro n hn
      apply Nat.le_floor
      apply Real.le_sqrt_of_sq_le
      linarith
    have e := block_sum_reindex (windowY X ε) (windowY X ε / 4) t H
      (windowY X ε ^ (1 / 6 + ε / 2))
      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M
      (windowY X ε ^ (1 / 6 + ε / 2)) α (by linarith) hwin hk
    simp only at e ⊢
    rw [e]
  have hLA : Real.log (windowY X ε / 4) ^ (-A) ≤ (24 / 7) ^ A / Real.log X ^ A := by
    have hc : 0 < 7 / 24 * Real.log X := by positivity
    have h1 : (7 / 24 * Real.log X) ^ A ≤ Real.log (windowY X ε / 4) ^ A :=
      Real.rpow_le_rpow hc.le p7 hA.le
    have h2 : (7 / 24 * Real.log X) ^ A = (7 / 24) ^ A * Real.log X ^ A :=
      Real.mul_rpow (by norm_num) hlogX.le
    have hpos : 0 < (7 / 24 * Real.log X) ^ A := Real.rpow_pos_of_pos hc A
    have hlx : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
    rw [Real.rpow_neg hL0]
    calc (Real.log (windowY X ε / 4) ^ A)⁻¹ ≤ ((7 / 24 * Real.log X) ^ A)⁻¹ :=
          inv_anti₀ hpos h1
      _ = (24 / 7) ^ A / Real.log X ^ A := by
          rw [h2, mul_inv, ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 7 / 24)]
          norm_num [div_eq_mul_inv]
  have hH2 : 0 ≤ C * H ^ 2 := by positivity
  calc _ = _ := hcongr
    _ ≤ C * H ^ 2 * Real.log (windowY X ε / 4) ^ (-A) := key
    _ ≤ C * H ^ 2 * ((24 / 7) ^ A / Real.log X ^ A) := mul_le_mul_of_nonneg_left hLA hH2
    _ = C * (24 / 7) ^ A * H ^ 2 / Real.log X ^ A := by ring

/-- Helper definition for the band proof, for review: P0088 page 11 Lemma 3.4,
the inner double sum over m ~ M, page 3 M <= m < 2M, and k <= K with
s < m^2 k^2 <= s + y of a_m Phi(k, z) e(alpha m^2 k^2), the summand of the
display of `lemma34` with a general cap K on k. -/
noncomputable def Gs (am : ℕ → ℂ) (z α M : ℝ) (K : ℕ) (y s : ℝ) : ℂ :=
  ∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
      (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
    ∑ k ∈ (Finset.range (K + 1)).filter
      (fun k : ℕ => s < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ s + y),
      am m * roughWeight z k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))

theorem ite3 (v t h : ℝ) (c : ℂ) (hh : 0 ≤ h) :
    (if t < v ∧ v ≤ t + 3 * h then c else 0) =
      (if t < v ∧ v ≤ t + h then c else 0) + (if t + h < v ∧ v ≤ t + h + h then c else 0) +
        (if t + 2 * h < v ∧ v ≤ t + 2 * h + h then c else 0) := by
  rcases le_or_gt v t with a | a
  · rw [if_neg (show ¬ (t < v ∧ v ≤ t + 3 * h) by intro hc; linarith [hc.1]),
      if_neg (show ¬ (t < v ∧ v ≤ t + h) by intro hc; linarith [hc.1]),
      if_neg (show ¬ (t + h < v ∧ v ≤ t + h + h) by intro hc; linarith [hc.1]),
      if_neg (show ¬ (t + 2 * h < v ∧ v ≤ t + 2 * h + h) by intro hc; linarith [hc.1])]
    simp
  rcases le_or_gt v (t + h) with b | b
  · rw [if_pos (show (t < v ∧ v ≤ t + 3 * h) from ⟨a, by linarith⟩),
      if_pos (show (t < v ∧ v ≤ t + h) from ⟨a, b⟩),
      if_neg (show ¬ (t + h < v ∧ v ≤ t + h + h) by intro hc; linarith [hc.1]),
      if_neg (show ¬ (t + 2 * h < v ∧ v ≤ t + 2 * h + h) by intro hc; linarith [hc.1])]
    simp
  rcases le_or_gt v (t + 2 * h) with c' | c'
  · rw [if_pos (show (t < v ∧ v ≤ t + 3 * h) from ⟨a, by linarith⟩),
      if_neg (show ¬ (t < v ∧ v ≤ t + h) by intro hc; linarith [hc.2]),
      if_pos (show (t + h < v ∧ v ≤ t + h + h) from ⟨b, by linarith⟩),
      if_neg (show ¬ (t + 2 * h < v ∧ v ≤ t + 2 * h + h) by intro hc; linarith [hc.1])]
    simp
  rcases le_or_gt v (t + 3 * h) with d | d
  · rw [if_pos (show (t < v ∧ v ≤ t + 3 * h) from ⟨a, d⟩),
      if_neg (show ¬ (t < v ∧ v ≤ t + h) by intro hc; linarith [hc.2]),
      if_neg (show ¬ (t + h < v ∧ v ≤ t + h + h) by intro hc; linarith [hc.2]),
      if_pos (show (t + 2 * h < v ∧ v ≤ t + 2 * h + h) from ⟨c', by linarith⟩)]
    simp
  · rw [if_neg (show ¬ (t < v ∧ v ≤ t + 3 * h) by intro hc; linarith [hc.2]),
      if_neg (show ¬ (t < v ∧ v ≤ t + h) by intro hc; linarith [hc.2]),
      if_neg (show ¬ (t + h < v ∧ v ≤ t + h + h) by intro hc; linarith [hc.2]),
      if_neg (show ¬ (t + 2 * h < v ∧ v ≤ t + 2 * h + h) by intro hc; linarith [hc.2])]
    simp

theorem three_split (am : ℕ → ℂ) (z α M : ℝ) (K : ℕ) (t h : ℝ) (hh : 0 ≤ h) :
    Gs am z α M K (3 * h) t =
      Gs am z α M K h t + Gs am z α M K h (t + h) + Gs am z α M K h (t + 2 * h) := by
  unfold Gs
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => ite3 _ _ _ _ hh

theorem Gs_sq_intervalIntegrable (am : ℕ → ℂ) (z α M : ℝ) (K : ℕ) (y a b : ℝ) :
    IntervalIntegrable (fun s => ‖Gs am z α M K y s‖ ^ 2) volume a b := by
  set S := (Finset.range (⌊2 * M⌋₊ + 1)).filter
      (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M) with hS
  set F : ℕ → ℕ → ℂ := fun m k =>
    am m * roughWeight z k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) with hF
  have hrw : ∀ s, Gs am z α M K y s = ∑ m ∈ S, ∑ k ∈ Finset.range (K + 1),
      if (s < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ s + y) then F m k else 0 := by
    intro s
    unfold Gs
    exact Finset.sum_congr rfl fun m _ => Finset.sum_filter _ _
  have hmeas : Measurable (fun s => ‖Gs am z α M K y s‖ ^ 2) := by
    simp_rw [hrw]
    refine (Measurable.norm ?_).pow_const 2
    refine Finset.measurable_sum _ fun m _ => Finset.measurable_sum _ fun k _ => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_id.add_const y))
  have hbound : ∀ s : ℝ, ‖‖Gs am z α M K y s‖ ^ 2‖ ≤
      (∑ m ∈ S, ∑ k ∈ Finset.range (K + 1), ‖F m k‖) ^ 2 := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrw]
    have h1 : ‖∑ m ∈ S, ∑ k ∈ Finset.range (K + 1),
        (if (s < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ s + y) then F m k else 0)‖ ≤
        ∑ m ∈ S, ∑ k ∈ Finset.range (K + 1), ‖F m k‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      split_ifs <;> simp
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact (intervalIntegrable_const (c := (∑ m ∈ S, ∑ k ∈ Finset.range (K + 1), ‖F m k‖) ^ 2)).mono_fun'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem Gs_cap_congr (am : ℕ → ℂ) (z α M : ℝ) (K1 K2 : ℕ) (y s : ℝ) (hM : 1 ≤ M)
    (h1 : ∀ k : ℕ, (k : ℝ) ^ 2 ≤ s + y → k ≤ K1)
    (h2 : ∀ k : ℕ, (k : ℝ) ^ 2 ≤ s + y → k ≤ K2) :
    Gs am z α M K1 y s = Gs am z α M K2 y s := by
  unfold Gs
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := hM.trans (Finset.mem_filter.mp hm).2.1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  have hk2 : (k : ℝ) ^ 2 ≤ ((m * k : ℕ) : ℝ) ^ 2 := by
    push_cast
    have h1m : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right h1m (sq_nonneg (k : ℝ))]
  constructor
  · rintro ⟨-, hc⟩
    have := h2 k (hk2.trans hc.2)
    exact ⟨by omega, hc⟩
  · rintro ⟨-, hc⟩
    have := h1 k (hk2.trans hc.2)
    exact ⟨by omega, hc⟩

theorem norm_add3_sq_le (u v w : ℂ) :
    ‖u + v + w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add₃_le (a := u) (b := v) (c := w)) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖), sq_nonneg (‖u‖ - ‖w‖)]

theorem band_analytic (am : ℕ → ℂ) (z α M : ℝ) (K : ℕ) (Y h D : ℝ) (hY : 0 < Y)
    (hh : 0 ≤ h) (hh6 : h ≤ Y / 6)
    (hJ1 : ∫ s in (Y / 4)..(Y / 2), ‖Gs am z α M K h s‖ ^ 2 ≤ D)
    (hJ2 : ∫ s in (Y / 2)..Y, ‖Gs am z α M K h s‖ ^ 2 ≤ D) :
    ∫ t in (Y / 4)..(Y / 2), ‖Gs am z α M K (3 * h) t‖ ^ 2 ≤ 18 * D := by
  set f : ℝ → ℝ := fun s => ‖Gs am z α M K h s‖ ^ 2 with hf
  have hint : ∀ a b, IntervalIntegrable f volume a b := fun a b =>
    Gs_sq_intervalIntegrable am z α M K h a b
  have hfnn : ∀ s, 0 ≤ f s := fun s => by positivity
  have hJ : ∫ s in (Y / 4)..Y, f s ≤ 2 * D := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint (Y / 4) (Y / 2))
      (hint (Y / 2) Y)]
    linarith
  have hshift : ∀ c, 0 ≤ c → c ≤ Y / 2 → ∫ t in (Y / 4)..(Y / 2), f (t + c) ≤ 2 * D := by
    intro c hc0 hc1
    rw [intervalIntegral.integral_comp_add_right f c]
    refine le_trans ?_ hJ
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall (fun s => hfnn s)
    · exact hint _ _
  have hpt : ∀ t, ‖Gs am z α M K (3 * h) t‖ ^ 2 ≤ 3 * (f t + f (t + h) + f (t + 2 * h)) := by
    intro t
    rw [three_split am z α M K t h hh]
    exact norm_add3_sq_le _ _ _
  have hi1 : IntervalIntegrable (fun t => f (t + h)) volume (Y / 4) (Y / 2) := by
    have := (hint (Y / 4 + h) (Y / 2 + h)).comp_add_right h
    simpa using this
  have hi2 : IntervalIntegrable (fun t => f (t + 2 * h)) volume (Y / 4) (Y / 2) := by
    have := (hint (Y / 4 + 2 * h) (Y / 2 + 2 * h)).comp_add_right (2 * h)
    simpa using this
  have h0 := hshift 0 le_rfl (by linarith)
  simp only [add_zero] at h0
  have h1 := hshift h hh (by linarith)
  have h2 := hshift (2 * h) (by linarith) (by linarith)
  calc ∫ t in (Y / 4)..(Y / 2), ‖Gs am z α M K (3 * h) t‖ ^ 2
      ≤ ∫ t in (Y / 4)..(Y / 2), 3 * (f t + f (t + h) + f (t + 2 * h)) :=
        intervalIntegral.integral_mono_on (by linarith)
          (Gs_sq_intervalIntegrable am z α M K (3 * h) _ _)
          ((((hint _ _).add hi1).add hi2).const_mul 3) (fun t _ => hpt t)
    _ = 3 * ((∫ t in (Y / 4)..(Y / 2), f t) + (∫ t in (Y / 4)..(Y / 2), f (t + h)) +
          ∫ t in (Y / 4)..(Y / 2), f (t + 2 * h)) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          ((hint _ _).add hi1) hi2, intervalIntegral.integral_add (hint _ _) hi1]
    _ ≤ 18 * D := by linarith

theorem logpow_le (A L l : ℝ) (hA : 0 < A) (hL : 0 < L) (hl : 7 / 24 * L ≤ l) :
    l ^ (-A) ≤ (24 / 7) ^ A / L ^ A := by
  have hc : 0 < 7 / 24 * L := by positivity
  have hl0 : 0 ≤ l := by linarith
  have h1 : (7 / 24 * L) ^ A ≤ l ^ A := Real.rpow_le_rpow hc.le hl hA.le
  have h2 : (7 / 24 * L) ^ A = (7 / 24) ^ A * L ^ A := Real.mul_rpow (by norm_num) hL.le
  have hpos : 0 < (7 / 24 * L) ^ A := Real.rpow_pos_of_pos hc A
  rw [Real.rpow_neg hl0]
  calc (l ^ A)⁻¹ ≤ ((7 / 24 * L) ^ A)⁻¹ := inv_anti₀ hpos h1
    _ = (24 / 7) ^ A / L ^ A := by
        rw [h2, mul_inv, ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 7 / 24)]
        norm_num [div_eq_mul_inv]


theorem band_params (B ε x0 : ℝ) (hB : 2 ≤ B) (hε : 0 < ε) (hε' : ε < 1 / 6) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      3 ≤ Real.log X ∧ 2 ≤ windowY X ε ^ (1 / 6 + ε / 2) ∧
      ∀ x : ℝ, windowY X ε / 4 ≤ x → x ≤ windowY X ε / 2 →
        x0 ≤ x ∧
        x ^ (1 / 2 : ℝ) ≤ windowY X ε / 12 ∧
        windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
          x ^ (1 / 4 : ℝ) * Real.log x ^ (-2 * (B - 1)) ∧
        (∀ H : ℝ, X ^ (7 / 18 + ε) ≤ H →
          windowY X ε ^ (1 / 6 + ε / 2) ≤
            H / 3 * x ^ (-1 / 2 : ℝ) * Real.log x ^ (-2 * (B - 1))) ∧
        1 ≤ Real.log x ∧ 7 / 24 * Real.log X ≤ Real.log x ∧ Real.log x ≤ Real.log X := by
  obtain ⟨X1, hX1, hP⟩ := left_half_params B ε x0 (by linarith) hε hε'
  set K : ℝ := 48 + (24 * B / ε) ^ 2 with hK
  have hK48 : 48 ≤ K := by nlinarith [sq_nonneg (24 * B / ε)]
  refine ⟨max X1 (Real.exp K), hX1.trans (le_max_left _ _), ?_⟩
  intro X hX
  obtain ⟨p1, p2, -, -, -, p6, p7, p8⟩ := hP X ((le_max_left _ _).trans hX)
  have hXK : Real.exp K ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos K) hXK
  have hLx : K ≤ Real.log X := by
    rw [← Real.log_exp K]; exact Real.log_le_log (Real.exp_pos K) hXK
  set Lx := Real.log X with hLxdef
  have hLx0 : 0 ≤ Lx := by linarith
  have hLxpos : 0 < Lx := by linarith
  set a : ℝ := 7 / 12 + ε / 2 with ha
  have hYe : windowY X ε = Real.exp (a * Lx) := by
    unfold windowY; rw [Real.rpow_def_of_pos hXpos, ha, hLxdef]; ring_nf
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hY0 : 0 < windowY X ε := by rw [hYe]; exact Real.exp_pos _
  have hlY4 : Real.log (windowY X ε / 4) = a * Lx - Real.log 4 := by
    rw [hYe, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have hlY2 : Real.log (windowY X ε / 2) = a * Lx - Real.log 2 := by
    rw [hYe, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have haL : a * Lx = 7 / 12 * Lx + ε * Lx / 2 := by rw [ha]; ring
  have hεL0 : 0 ≤ ε * Lx := mul_nonneg hε.le hLx0
  have hεεL : ε * ε * Lx ≤ ε / 6 * Lx := mul_le_mul_of_nonneg_right (by nlinarith) hLx0
  refine ⟨by linarith, p2, ?_⟩
  intro x hx1 hx2
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx1
  have hl_lo : a * Lx - Real.log 4 ≤ Real.log x := by
    rw [← hlY4]; exact Real.log_le_log (by positivity) hx1
  have hl_hi : Real.log x ≤ a * Lx - Real.log 2 := by
    rw [← hlY2]; exact Real.log_le_log hxpos hx2
  set l := Real.log x with hldef
  have hxe : x = Real.exp l := (Real.exp_log hxpos).symm
  have hl1 : 1 ≤ l := by linarith
  have hl0 : 0 < l := by linarith
  have hl7 : 7 / 24 * Lx ≤ l := by linarith
  have hεL6 : ε * Lx ≤ 1 / 6 * Lx := mul_le_mul_of_nonneg_right hε'.le hLx0
  have hlL : l ≤ Lx := by linarith
  have hloglL : Real.log l ≤ Real.log Lx := Real.log_le_log hl0 hlL
  have hlogL2 : Real.log 2 ≤ Real.log Lx := Real.log_le_log (by norm_num) (by linarith)
  refine ⟨by linarith, ?_, ?_, ?_, hl1, hl7, hlL⟩
  · -- x^(1/2) ≤ Y/12
    rw [hxe, hYe, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have e1 : Real.exp (a * Lx) = Real.exp (l * (1 / 2)) * Real.exp (a * Lx - l * (1 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : 12 ≤ Real.exp (a * Lx - l * (1 / 2)) := by
      linarith [Real.add_one_le_exp (a * Lx - l * (1 / 2))]
    rw [e1, le_div_iff₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_left e2 (Real.exp_pos _).le
  · -- M bound
    rw [hxe, hYe, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hl0,
      Real.rpow_def_of_pos hLxpos, zpow_neg, zpow_two, ← Real.exp_add, ← Real.exp_neg,
      ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hBl : (B - 1) * Real.log l ≤ (B - 1) * Real.log Lx :=
      mul_le_mul_of_nonneg_left hloglL (by linarith)
    linarith
  · intro H hH
    rw [Real.rpow_def_of_pos hXpos] at hH
    rw [hxe, hYe, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hl0]
    have hs0 : 0 ≤ Real.sqrt Lx := Real.sqrt_nonneg _
    have hss : Real.sqrt Lx ^ 2 = Lx := Real.sq_sqrt hLx0
    have hspos : 0 < Real.sqrt Lx := Real.sqrt_pos.mpr hLxpos
    have hlogl : Real.log l ≤ 2 * Real.sqrt Lx := by
      have h2 : Real.log (Real.sqrt Lx) = Real.log Lx / 2 := Real.log_sqrt hLx0
      have h3 := Real.log_le_sub_one_of_pos hspos
      linarith
    have hsq : (24 * B / ε) ^ 2 ≤ Lx := by linarith [hK]
    have h12 : 24 * B / ε ≤ Real.sqrt Lx := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity)] at this
    have h12' : 24 * B ≤ Real.sqrt Lx * ε := (div_le_iff₀ hε).mp h12
    have hs2 : 24 * B * Real.sqrt Lx ≤ ε * Lx := by
      have := mul_le_mul_of_nonneg_left h12' hs0
      calc 24 * B * Real.sqrt Lx = Real.sqrt Lx * (24 * B) := by ring
        _ ≤ Real.sqrt Lx * (Real.sqrt Lx * ε) := this
        _ = Real.sqrt Lx ^ 2 * ε := by ring
        _ = ε * Lx := by rw [hss]; ring
    have hs1 : 1 ≤ Real.sqrt Lx := by
      have : (1 : ℝ) ≤ 24 * B / ε := by rw [le_div_iff₀ hε]; linarith
      linarith
    have hB1 : 2 * 1 ≤ B * Real.sqrt Lx := mul_le_mul hB hs1 (by norm_num) (by linarith)
    have hεL : 12 ≤ ε * Lx := by linarith
    have hBl : (B - 1) * Real.log l ≤ (B - 1) * (2 * Real.sqrt Lx) :=
      mul_le_mul_of_nonneg_left hlogl (by linarith)
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
    have hexp3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
    calc Real.exp (a * Lx * (1 / 6 + ε / 2))
        ≤ Real.exp (Lx * (7 / 18 + ε)) * Real.exp (-Real.log 3) * Real.exp (l * (-1 / 2)) *
            Real.exp (Real.log l * (-2 * (B - 1))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hexp : a * Lx * (1 / 6 + ε / 2) + a * Lx / 2 =
              7 / 18 * Lx + 5 / 8 * (ε * Lx) + 1 / 4 * (ε * ε * Lx) := by rw [ha]; ring
          linarith
      _ = Real.exp (Lx * (7 / 18 + ε)) / 3 * Real.exp (l * (-1 / 2)) *
            Real.exp (Real.log l * (-2 * (B - 1))) := by
          rw [Real.exp_neg, hexp3]; ring
      _ ≤ H / 3 * Real.exp (l * (-1 / 2)) * Real.exp (Real.log l * (-2 * (B - 1))) := by
          gcongr



/-- PROVED. P0088 page 11 Lemma 3.4, the band Y/4 < H <= Y/2 just past its
hypothesis y <= x, MEDIUM. Here t + H <= Y on the left half, so the window
cut removes at most m^2 = Y. Route: cut (t, t + H] into three intervals of length
H/3 <= Y/6, use |u + v + w|^2 <= 3 (|u|^2 + |v|^2 + |w|^2), shift t, cover
the shifted ranges by [Y/4, Y/2] and [Y/2, Y], and apply `lemma34` at
x = Y/4 and x = Y/2 with y = H/3, with B lowered by one. -/
theorem left_half_band_low (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        windowY X ε / 4 < H → H ≤ windowY X ε / 2 →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h34⟩ := lemma34 0 A hA
  refine ⟨max (B1 + 1) 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    fun B hB ε hε hε' => ?_⟩
  have hB2 : 2 ≤ B := (le_max_right _ _).trans hB
  have hB1' : B1 ≤ B - 1 := by linarith [(le_max_left (B1 + 1) 2).trans hB]
  obtain ⟨C, x0, hC, k34⟩ := h34 (B - 1) hB1'
  obtain ⟨X0, hX0, hP⟩ := band_params B ε x0 hB2 hε hε'
  have hK : (0 : ℝ) < (24 / 7) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  refine ⟨2 * C * (24 / 7) ^ A, X0, by positivity, hX0, ?_⟩
  intro X H hX hHl hHu hHa hHb α q a hcop hqP hqQ hclose M hM htop hlow
  obtain ⟨hL3, hz2, hx⟩ := hP X hX
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  set Y := windowY X ε with hYdef
  set L := Real.log X with hLdef
  set z := Y ^ (1 / 6 + ε / 2) with hzdef
  set z0 := Y ^ (1 / 4 : ℝ) * (L ^ B) ^ (-2 : ℤ) with hz0def
  set am : ℕ → ℂ := fun m => if m.Prime ∧ z ≤ (m : ℝ) ∧ (m : ℝ) < z0 then 1 else 0
    with ham_def
  set Kc : ℕ := ⌊Real.sqrt (3 * (Y / 2))⌋₊ with hKc
  have hLpos : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  set h := H / 3 with hh_def
  have hh0 : 0 ≤ h := by positivity
  have ham : ∀ m : ℕ, ‖am m‖ ≤ ((Nat.divisors m).card : ℝ) ^ (0 : ℕ) := by
    intro m
    simp only [pow_zero, ham_def]
    split_ifs <;> simp
  have hPq : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := hPq.trans hqP
    exact_mod_cast this
  have h41c : |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 :=
    display41_of_minor hq0 hqQ hclose
  have hLB2 : 3 * L ^ (B - 1) ≤ L ^ B := by
    rw [Real.rpow_sub_one hLpos.ne', mul_div_assoc', div_le_iff₀ hLpos]
    nlinarith
  have piece : ∀ x, Y / 4 ≤ x → x ≤ Y / 2 →
      ∫ t in x..(2 * x), ‖Gs am z α M ⌊Real.sqrt (3 * x)⌋₊ h t‖ ^ 2 ≤
        C * h ^ 2 * ((24 / 7) ^ A / L ^ A) := by
    intro x hx1 hx2
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hx x hx1 hx2
    have hlx0 : 0 < Real.log x := by linarith
    have hLB1 : Real.log x ^ (B - 1) ≤ L ^ (B - 1) :=
      Real.rpow_le_rpow hlx0.le p7 (by linarith)
    have hLBm : 0 ≤ L ^ (B - 1) := (Real.rpow_pos_of_pos hLpos _).le
    have hlxB : 0 < Real.log x ^ (B - 1) := Real.rpow_pos_of_pos hlx0 _
    have h41a : Real.log x ^ (B - 1) ≤ (q : ℝ) := by linarith
    have h41b : (q : ℝ) ≤ h * Real.log x ^ (-(B - 1)) := by
      rw [Real.rpow_neg hlx0.le, ← div_eq_mul_inv]
      refine hqQ.trans ?_
      rw [div_le_div_iff₀ hPq hlxB, hh_def]
      nlinarith
    have hM2 : M ≤ x ^ (1 / 4 : ℝ) * Real.log x ^ (-2 * (B - 1)) := (le_of_lt htop).trans p3
    have hz : z ≤ h * x ^ (-1 / 2 : ℝ) * Real.log x ^ (-2 * (B - 1)) := p4 H hHl
    have key := k34 x h p1 (p2.trans (by rw [hh_def]; linarith)) (by rw [hh_def]; linarith)
      α q a hcop h41a h41b h41c am ham M z hM hM2 hz2 hz
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_left (logpow_le A L (Real.log x) hA hLpos p6) (by positivity)
  set D := C * h ^ 2 * ((24 / 7) ^ A / L ^ A) with hD
  have hJ1 : ∫ s in (Y / 4)..(Y / 2), ‖Gs am z α M Kc h s‖ ^ 2 ≤ D := by
    have e := piece (Y / 4) le_rfl (by linarith)
    rw [show 2 * (Y / 4) = Y / 2 by ring] at e
    refine le_trans (le_of_eq ?_) e
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only
    rw [Gs_cap_congr am z α M Kc ⌊Real.sqrt (3 * (Y / 4))⌋₊ h s hM]
    · intro k hk
      apply Nat.le_floor
      apply Real.le_sqrt_of_sq_le
      rw [hh_def] at hk
      linarith
    · intro k hk
      apply Nat.le_floor
      apply Real.le_sqrt_of_sq_le
      rw [hh_def] at hk
      linarith
  have hJ2 : ∫ s in (Y / 2)..Y, ‖Gs am z α M Kc h s‖ ^ 2 ≤ D := by
    have e := piece (Y / 2) (by linarith) le_rfl
    rw [show 2 * (Y / 2) = Y by ring] at e
    exact e
  have hA3 := band_analytic am z α M Kc Y h D hY hh0 (by rw [hh_def]; linarith) hJ1 hJ2
  rw [show 3 * h = H by rw [hh_def]; ring] at hA3
  have hcongr : (∫ t in (Y / 4)..(Y / 2),
          ‖∑ m ∈ (squareWindow Y).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                z ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight z (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in (Y / 4)..(Y / 2), ‖Gs am z α M Kc H t‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (Y / 2)] with t ht hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    obtain ⟨ht1, ht2⟩ := hmem
    have ht3 : t < Y / 2 := lt_of_le_of_ne ht2 ht
    have hwin : ∀ n : ℕ, t < (n : ℝ) ^ 2 → (n : ℝ) ^ 2 ≤ t + H → n ∈ squareWindow Y := by
      intro n hn1 hn2
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hs := Real.sq_sqrt hY.le
      have hs0 := Real.sqrt_nonneg Y
      have hlt : (n : ℝ) < Real.sqrt Y := (Real.lt_sqrt hn0).mpr (by linarith)
      simp only [squareWindow, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor hlt.le), ?_, hlt⟩
      refine (pow_le_pow_iff_left₀ (by positivity) hn0 two_ne_zero).mp ?_
      rw [div_pow, hs]
      linarith
    have hk : ∀ n : ℕ, (n : ℝ) ^ 2 ≤ t + H → n ≤ ⌊Real.sqrt (3 * (Y / 2))⌋₊ := by
      intro n hn
      apply Nat.le_floor
      apply Real.le_sqrt_of_sq_le
      linarith
    have e := block_sum_reindex Y (Y / 2) t H z z0 M z α (by linarith) hwin hk
    rw [e]
    rfl
  calc _ = _ := hcongr
    _ ≤ 18 * D := hA3
    _ = 2 * C * (24 / 7) ^ A * H ^ 2 / L ^ A := by
        rw [hD, hh_def]; field_simp; ring

theorem ite2_hi (a b c v : ℝ) (x : ℂ) (hab : a ≤ b) (hbc : b ≤ c) :
    (if a < v ∧ v ≤ c then x else 0) =
      (if a < v ∧ v ≤ b then x else 0) + (if b < v ∧ v ≤ c then x else 0) := by
  by_cases h1 : a < v ∧ v ≤ b
  · rw [if_pos ⟨h1.1, h1.2.trans hbc⟩, if_pos h1, if_neg (fun h => by linarith [h.1, h1.2])]
    simp
  · by_cases h2 : b < v ∧ v ≤ c
    · rw [if_neg h1, if_pos h2, if_pos ⟨lt_of_le_of_lt hab h2.1, h2.2⟩]; simp
    · rw [if_neg h1, if_neg h2, if_neg]
      · simp
      · rintro ⟨h3, h4⟩
        rcases le_or_gt v b with h5 | h5
        · exact h1 ⟨h3, h5⟩
        · exact h2 ⟨h5, h4⟩

theorem sum_split_hi (S : Finset ℕ) (f : ℕ → ℂ) (t g : ℝ) (hg : 0 ≤ g) (J : ℕ) :
    ∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + (J : ℝ) * g), f m =
      ∑ j ∈ Finset.range J, ∑ m ∈ S.filter (fun m : ℕ =>
        t + (j : ℝ) * g < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + (j : ℝ) * g + g), f m := by
  induction J with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm
    simp only [Nat.cast_zero, zero_mul, add_zero] at h2
    exfalso
    linarith
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e : t + ((J + 1 : ℕ) : ℝ) * g = t + (J : ℝ) * g + g := by push_cast; ring
    rw [e]
    have hJ : 0 ≤ (J : ℝ) * g := mul_nonneg (Nat.cast_nonneg J) hg
    exact ite2_hi _ _ _ _ _ (by linarith) (by linarith)

theorem cs_hi (J : ℕ) (P : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range J, P j‖ ^ 2 ≤ (J : ℝ) * ∑ j ∈ Finset.range J, ‖P j‖ ^ 2 := by
  calc ‖∑ j ∈ Finset.range J, P j‖ ^ 2 ≤ (∑ j ∈ Finset.range J, ‖P j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.range J).card : ℝ) * ∑ j ∈ Finset.range J, ‖P j‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = (J : ℝ) * ∑ j ∈ Finset.range J, ‖P j‖ ^ 2 := by rw [Finset.card_range]

theorem shift_hi (S : Finset ℕ) (f : ℕ → ℂ) (a b g H : ℝ) (J : ℕ) (hab : a ≤ b)
    (hg : 0 ≤ g) (hH : H = (J : ℝ) * g) :
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), f m‖ ^ 2) ≤
      (J : ℝ) ^ 2 * ∫ s in a..(b + H),
        ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2 := by
  set F : ℝ → ℝ := fun s =>
    ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2 with hF
  have hint : ∀ c d, IntervalIntegrable F volume c d := fun c d =>
    short_sum_sq_intervalIntegrable S f g c d
  have hFnn : ∀ s, 0 ≤ F s := fun s => by positivity
  have hpt : ∀ t, ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
      f m‖ ^ 2 ≤ (J : ℝ) * ∑ j ∈ Finset.range J, F (t + (j : ℝ) * g) := by
    intro t
    rw [hH, sum_split_hi S f t g hg J]
    exact cs_hi J _
  have hsh : ∀ j ∈ Finset.range J,
      IntervalIntegrable (fun t => F (t + (j : ℝ) * g)) volume a b := by
    intro j _
    have := (hint (a + j * g) (b + j * g)).comp_add_right ((j : ℝ) * g)
    simpa using this
  have hsum : IntervalIntegrable (fun t => ∑ j ∈ Finset.range J, F (t + (j : ℝ) * g))
      volume a b := by
    have := IntervalIntegrable.sum (Finset.range J) hsh
    convert this using 1
    ext t
    simp [Finset.sum_apply]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hone : ∀ j ∈ Finset.range J,
      ∫ t in a..b, F (t + (j : ℝ) * g) ≤ ∫ s in a..(b + H), F s := by
    intro j hj
    have hjJ : (j : ℝ) + 1 ≤ J := by
      have := Finset.mem_range.mp hj
      exact_mod_cast this
    have hjg : (j : ℝ) * g + g ≤ H := by rw [hH]; nlinarith
    have hj0 : 0 ≤ (j : ℝ) * g := by positivity
    rw [intervalIntegral.integral_comp_add_right F]
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall (fun s => hFnn s)
    · exact hint _ _
  calc _ ≤ ∫ t in a..b, (J : ℝ) * ∑ j ∈ Finset.range J, F (t + (j : ℝ) * g) :=
        intervalIntegral.integral_mono_on hab (short_sum_sq_intervalIntegrable S f H a b)
          (hsum.const_mul _) (fun t _ => hpt t)
    _ = (J : ℝ) * ∑ j ∈ Finset.range J, ∫ t in a..b, F (t + (j : ℝ) * g) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hsh]
    _ ≤ (J : ℝ) * ∑ j ∈ Finset.range J, ∫ s in a..(b + H), F s :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hone) hJ0
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem count_hi (S : Finset ℕ) (Y s g : ℝ) (hY : 0 < Y) (hs : Y / 4 ≤ s) (hg : 0 ≤ g) :
    ((S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g)).card : ℝ) ≤
      g / Real.sqrt Y + 1 := by
  have hs0 : 0 ≤ s := by linarith
  set u := Real.sqrt s with hu
  set v := Real.sqrt (s + g) with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have huv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hu2 : u ^ 2 = s := Real.sq_sqrt hs0
  have hv2 : v ^ 2 = s + g := Real.sq_sqrt (by linarith)
  have hsub : S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g) ⊆
      Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ := by
    intro m hm
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hum : u < m := by nlinarith
    have hmv : (m : ℝ) ≤ v := by nlinarith
    rw [Finset.mem_Ioc]
    exact ⟨(Nat.floor_lt hu0).mpr hum, Nat.le_floor hmv⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hc : ((⌊v⌋₊ - ⌊u⌋₊ : ℕ) : ℝ) ≤ v - u + 1 := by
    rcases le_total ⌊u⌋₊ ⌊v⌋₊ with h | h
    · rw [Nat.cast_sub h]
      have := Nat.floor_le (hu0.trans huv)
      have := Nat.lt_floor_add_one u
      linarith
    · rw [Nat.sub_eq_zero_of_le h]; simp; linarith
  have hsY : Real.sqrt Y ≤ u + v := by
    have h1 : Real.sqrt Y ≤ 2 * u := by
      have hy : Y ≤ (2 * u) ^ 2 := by nlinarith
      calc Real.sqrt Y ≤ Real.sqrt ((2 * u) ^ 2) := Real.sqrt_le_sqrt hy
        _ = 2 * u := Real.sqrt_sq (by positivity)
    linarith
  have hvu : v - u ≤ g / Real.sqrt Y := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hY)]
    nlinarith [mul_le_mul_of_nonneg_left hsY (show 0 ≤ v - u by linarith)]
  have : ((S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g)).card : ℝ) ≤
      ((⌊v⌋₊ - ⌊u⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

theorem pt_hi (S : Finset ℕ) (f : ℕ → ℂ) (Y s g : ℝ) (hY : 0 < Y) (hs : Y / 4 ≤ s)
    (hg : 0 ≤ g) (hf : ∀ m ∈ S, ‖f m‖ ≤ 2) :
    ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2 ≤
      (2 * (g / Real.sqrt Y + 1)) ^ 2 := by
  have h1 : ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ≤
      2 * (g / Real.sqrt Y + 1) := by
    calc _ ≤ ∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), ‖f m‖ :=
          norm_sum_le _ _
      _ ≤ ∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), (2 : ℝ) :=
          Finset.sum_le_sum (fun m hm => hf m (Finset.mem_filter.mp hm).1)
      _ = 2 * ((S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := by have := count_hi S Y s g hY hs hg; linarith
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem region_hi (S : Finset ℕ) (f : ℕ → ℂ) (Y g R : ℝ) (hY : 0 < Y) (hg : 0 ≤ g)
    (hgY : g ≤ Y / 2) (hR : Y ≤ R) (hS : ∀ m ∈ S, (m : ℝ) ^ 2 < Y)
    (hf : ∀ m ∈ S, ‖f m‖ ≤ 2) :
    (∫ s in (Y / 4)..R,
      ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2) ≤
      (∫ s in (Y / 4)..(Y / 2),
        ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2) +
      (∫ s in ((Y - g) / 2)..(Y - g),
        ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2) +
      g * (2 * (g / Real.sqrt Y + 1)) ^ 2 := by
  set F : ℝ → ℝ := fun s =>
    ‖∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2 with hF
  have hint : ∀ c d, IntervalIntegrable F volume c d := fun c d =>
    short_sum_sq_intervalIntegrable S f g c d
  have hFnn : ∀ s, 0 ≤ F s := fun s => by positivity
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hint (Y / 4) (Y - g)) (hint (Y - g) R)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hint (Y - g) Y) (hint Y R)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hint (Y / 4) (Y / 2))
    (hint (Y / 2) (Y - g))
  have i1 : ∫ s in (Y / 2)..(Y - g), F s ≤ ∫ s in ((Y - g) / 2)..(Y - g), F s := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
    · exact Filter.Eventually.of_forall (fun s => hFnn s)
    · exact hint _ _
  have i2 : ∫ s in (Y - g)..Y, F s ≤ g * (2 * (g / Real.sqrt Y + 1)) ^ 2 := by
    calc ∫ s in (Y - g)..Y, F s ≤ ∫ s in (Y - g)..Y, (2 * (g / Real.sqrt Y + 1)) ^ 2 :=
          intervalIntegral.integral_mono_on (by linarith) (hint _ _) intervalIntegrable_const
            (fun s hs => pt_hi S f Y s g hY (by linarith [hs.1]) hg hf)
      _ = g * (2 * (g / Real.sqrt Y + 1)) ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have i3 : ∫ s in Y..R, F s = 0 := by
    have : ∀ s ∈ Set.uIcc Y R, F s = 0 := by
      intro s hs
      rw [Set.uIcc_of_le hR] at hs
      have hsum : ∑ m ∈ S.filter (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g),
          f m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        obtain ⟨hmS, h1, -⟩ := Finset.mem_filter.mp hm
        have := hS m hmS
        exfalso
        linarith [hs.1]
      simp only [F, hsum, norm_zero]
      norm_num
    rw [intervalIntegral.integral_congr this]
    simp
  linarith

theorem piece_congr_hi (Y x g z1 z0 M w α : ℝ) (hY : 0 < Y) (hx : Y / 4 ≤ x)
    (hxg : 2 * x ≤ Y - g) (hg0 : 0 ≤ g) (hgx : g ≤ x) :
    (∫ s in x..(2 * x), ‖∑ m ∈ (squareWindow Y).filter
        (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g),
      (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        roughWeight w (m / p)) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
    ∫ s in x..(2 * x), ‖∑ m ∈ (Finset.range (⌊2 * M⌋₊ + 1)).filter
        (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
      ∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun k : ℕ => s < ((m * k : ℕ) : ℝ) ^ 2 ∧ ((m * k : ℕ) : ℝ) ^ 2 ≤ s + g),
        (if m.Prime ∧ z1 ≤ (m : ℝ) ∧ (m : ℝ) < z0 then (1 : ℂ) else 0) *
          roughWeight w k * fourier (((m * k) ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (2 * x)] with s hs hmem
  rw [Set.uIoc_of_le (by linarith)] at hmem
  obtain ⟨hs1, hs2⟩ := hmem
  have hs3 : s < 2 * x := lt_of_le_of_ne hs2 hs
  have hwin : ∀ n : ℕ, s < (n : ℝ) ^ 2 → (n : ℝ) ^ 2 ≤ s + g → n ∈ squareWindow Y := by
    intro n hn1 hn2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq := Real.sq_sqrt hY.le
    have hs0 := Real.sqrt_nonneg Y
    have hlt : (n : ℝ) < Real.sqrt Y := (Real.lt_sqrt hn0).mpr (by linarith)
    simp only [squareWindow, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor hlt.le), ?_, hlt⟩
    refine (pow_le_pow_iff_left₀ (by positivity) hn0 two_ne_zero).mp ?_
    rw [div_pow, hsq]
    linarith
  have hk : ∀ n : ℕ, (n : ℝ) ^ 2 ≤ s + g → n ≤ ⌊Real.sqrt (3 * x)⌋₊ := by
    intro n hn
    apply Nat.le_floor
    apply Real.le_sqrt_of_sq_le
    linarith
  rw [block_sum_reindex Y x s g z1 z0 M w α (by linarith) hwin hk]

theorem asym_hi (A : ℝ) (hA : 0 < A) :
    ∃ X1 : ℝ, ∀ X : ℝ, X1 ≤ X → 4 ≤ Real.log X ^ A ∧ 4 * Real.log X ^ A ≤ X ^ (1 / 9 : ℝ) := by
  have h1 := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0:ℝ) < 1 / 9)).bound
    (by norm_num : (0:ℝ) < 1 / 4)
  have h2 : Filter.Tendsto (fun X : ℝ => Real.log X ^ A) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop
  have h3 := h2.eventually_ge_atTop 4
  have h4 := Filter.eventually_ge_atTop (1 : ℝ)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (h1.and (h3.and h4))
  refine ⟨X1, fun X hX => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hX1 X hX
  refine ⟨e2, ?_⟩
  have hl : 0 ≤ Real.log X := Real.log_nonneg e3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at e1
  linarith

set_option maxHeartbeats 400000 in
/-- PROVED. P0088 page 11 Lemma 3.4, the band Y/2 < H < Y (log X)^(A/2),
the parent QUESTION. The window caps m^2 below Y, a fixed right end. Route,
from the 20261122 audit: cut (t, Y) into about L^(A1) moving pieces of
length y = H L^(-A1), apply `lemma34` to each with B lowered by A1 + A/2 and
a constant, and bound the last short piece and the case m^2 = Y trivially.
Proved with J = ceil(H L^A / Y) pieces of length g = H / J. -/
theorem left_half_band_high (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        windowY X ε / 2 < H → H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h34⟩ := lemma34 0 A hA
  obtain ⟨X2, hX2⟩ := asym_hi A hA
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 3 * A / 2 + 1 := ⟨_, rfl⟩
  refine ⟨max (B1 + D + 1) (D + 2), lt_of_lt_of_le (by linarith) (le_max_right _ _),
    fun B hB ε hε hε' => ?_⟩
  have hBD : D + 2 ≤ B := (le_max_right _ _).trans hB
  have hB1' : B1 ≤ B - D - 1 := by
    have := (le_max_left (B1 + D + 1) (D + 2)).trans hB; linarith
  obtain ⟨C, x0, hC, k34⟩ := h34 (B - D - 1) hB1'
  obtain ⟨X0, hX0, hP⟩ := band_params (B - D) ε x0 (by linarith) hε hε'
  obtain ⟨X3, hX3, hP3⟩ := left_half_params 1 ε 0 le_rfl hε hε'
  have hK : (0 : ℝ) < (24 / 7) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  refine ⟨2 * C * (24 / 7) ^ A + 16, max X0 (max X2 X3), by positivity,
    hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hHl hHu hHa hHb α q a hcop hqP hqQ hclose M hM htop hlow
  have hXX0 : X0 ≤ X := (le_max_left _ _).trans hX
  have hXX2 : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXX3 : X3 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  obtain ⟨hL3, hz2, hx⟩ := hP X hXX0
  obtain ⟨-, -, -, hY4h, -⟩ := hP3 X hXX3
  obtain ⟨hLA4, hLA9⟩ := hX2 X hXX2
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hY1 : 1 ≤ windowY X ε := by unfold windowY; exact Real.one_le_rpow hX1 (by linarith)
  have hrel : 4 * Real.log X ^ A * X ^ (7 / 18 + ε) ≤ windowY X ε := by
    have e : windowY X ε = X ^ (7 / 18 + ε) * X ^ (7 / 36 - ε / 2) := by
      unfold windowY; rw [← Real.rpow_add hXpos]; ring_nf
    have h9 : X ^ (1 / 9 : ℝ) ≤ X ^ (7 / 36 - ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    rw [e]
    have hp : 0 ≤ X ^ (7 / 18 + ε) := Real.rpow_nonneg hXpos.le _
    nlinarith
  set Y := windowY X ε with hYdef
  set L := Real.log X with hLdef
  set z := Y ^ (1 / 6 + ε / 2) with hzdef
  set z0 := Y ^ (1 / 4 : ℝ) * (L ^ B) ^ (-2 : ℤ) with hz0def
  set T := X ^ (7 / 18 + ε) with hTdef
  set am : ℕ → ℂ := fun m => if m.Prime ∧ z ≤ (m : ℝ) ∧ (m : ℝ) < z0 then 1 else 0
    with ham_def
  set f : ℕ → ℂ := fun m => (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          z ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M), roughWeight z (m / p)) *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) with hf_def
  have hY : 0 < Y := by linarith
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLA : 0 < L ^ A := by linarith
  have hT0 : 0 ≤ T := Real.rpow_nonneg hXpos.le _
  have hsqY : Real.sqrt Y ≤ 2 * T := by
    rw [← Real.sqrt_eq_rpow] at hY4h
    have h1 := Real.sq_sqrt (show 0 ≤ Y / 4 by positivity)
    have h3 := Real.sqrt_nonneg (Y / 4)
    have hy : Y ≤ (2 * T) ^ 2 := by nlinarith [mul_self_le_mul_self h3 hY4h]
    calc Real.sqrt Y ≤ Real.sqrt ((2 * T) ^ 2) := Real.sqrt_le_sqrt hy
      _ = 2 * T := Real.sqrt_sq (by positivity)
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = ⌈H * L ^ A / Y⌉₊ := ⟨_, rfl⟩
  have hR0 : 2 ≤ H * L ^ A / Y := by rw [le_div_iff₀ hY]; nlinarith
  have hJ1 : H * L ^ A / Y ≤ J := by rw [hJdef]; exact Nat.le_ceil _
  have hJ2 : (J : ℝ) < H * L ^ A / Y + 1 := by rw [hJdef]; exact Nat.ceil_lt_add_one (by linarith)
  have hJpos : (0 : ℝ) < J := by linarith
  have hH0 : 0 < H := by linarith
  have eY : H * L ^ A / Y * Y = H * L ^ A := div_mul_cancel₀ _ hY.ne'
  have hJY : (J : ℝ) * Y ≤ 2 * (H * L ^ A) := by
    have h := mul_le_mul_of_nonneg_right (show (J : ℝ) ≤ 2 * (H * L ^ A / Y) by linarith) hY.le
    linarith
  have hJY' : H * L ^ A ≤ (J : ℝ) * Y := by
    have h := mul_le_mul_of_nonneg_right hJ1 hY.le
    linarith
  set g := H / J with hg
  have hg0 : 0 < g := div_pos hH0 hJpos
  have hHJ : H = (J : ℝ) * g := by rw [hg]; field_simp
  have hgU : g * L ^ A ≤ Y := by
    have : (J : ℝ) * (g * L ^ A) ≤ J * Y := by rw [← mul_assoc, ← hHJ]; linarith
    exact le_of_mul_le_mul_left this hJpos
  have hgL : Y ≤ 2 * (g * L ^ A) := by
    have : (J : ℝ) * Y ≤ J * (2 * (g * L ^ A)) := by
      have : (J : ℝ) * (2 * (g * L ^ A)) = 2 * (H * L ^ A) := by rw [hHJ]; ring
      linarith
    exact le_of_mul_le_mul_left this hJpos
  have hg2T : 2 * T ≤ g := by
    have : (2 * L ^ A) * (2 * T) ≤ (2 * L ^ A) * g := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hgY4 : g ≤ Y / 4 := by
    have := mul_le_mul_of_nonneg_left hLA4 hg0.le
    linarith
  have hsg : Real.sqrt Y ≤ g := hsqY.trans hg2T
  have hJb : (J : ℝ) ≤ 2 * (L ^ (A / 2) * L ^ A) := by
    have h1 : 2 * (H * L ^ A) ≤ 2 * (L ^ (A / 2) * L ^ A) * Y := by
      have := mul_le_mul_of_nonneg_right hHb.le (by positivity : (0 : ℝ) ≤ 2 * L ^ A)
      linarith
    exact le_of_mul_le_mul_right (hJY.trans h1) hY
  have hLsplit : L ^ B = L ^ (A / 2) * L ^ A * L ^ (B - D - 1) * L ^ (2 : ℝ) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    congr 1; rw [hD]; ring
  have hL2 : (9 : ℝ) ≤ L ^ (2 : ℝ) := by
    rw [Real.rpow_two, sq]
    have := mul_le_mul hL3 hL3 (by norm_num) (by linarith)
    linarith
  have hPq : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
  have hq0 : 0 < q := by
    have : (0 : ℝ) < (q : ℝ) := hPq.trans hqP
    exact_mod_cast this
  have h41c : |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 :=
    display41_of_minor hq0 hqQ hclose
  have hq1 : (q : ℝ) * L ^ B ≤ H := (le_div_iff₀ hPq).mp hqQ
  have ham : ∀ m : ℕ, ‖am m‖ ≤ ((Nat.divisors m).card : ℝ) ^ (0 : ℕ) := by
    intro m
    simp only [pow_zero, ham_def]
    split_ifs <;> simp
  have htop' : M < Y ^ (1 / 4 : ℝ) * (L ^ B) ^ (-2 : ℤ) := htop
  have piece : ∀ x, Y / 4 ≤ x → x ≤ Y / 2 → 2 * x ≤ Y - g →
      (∫ s in x..(2 * x), ‖∑ m ∈ (squareWindow Y).filter
        (fun m : ℕ => s < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ s + g), f m‖ ^ 2) ≤
        C * g ^ 2 * ((24 / 7) ^ A / L ^ A) := by
    intro x hx1 hx2 hx3
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hx x hx1 hx2
    have hlx0 : 0 < Real.log x := by linarith
    set B' := B - D - 1 with hB'
    have hB'0 : 0 ≤ B' := by linarith
    have hlB : Real.log x ^ B' ≤ L ^ B' := Real.rpow_le_rpow hlx0.le p7 hB'0
    have hLB' : L ^ B' ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hlxB : 0 < Real.log x ^ B' := Real.rpow_pos_of_pos hlx0 _
    have h41a : Real.log x ^ B' ≤ (q : ℝ) := by linarith
    have hJLB : (J : ℝ) * L ^ B' ≤ L ^ B := by
      rw [hLsplit]
      have hp : 0 ≤ L ^ (A / 2) * L ^ A * L ^ B' := by positivity
      have h1 := mul_le_mul_of_nonneg_right hJb (Real.rpow_nonneg hLpos.le B')
      have h2 := mul_le_mul_of_nonneg_left hL2 hp
      linarith
    have h41b : (q : ℝ) ≤ g * Real.log x ^ (-B') := by
      rw [Real.rpow_neg hlx0.le, ← div_eq_mul_inv, le_div_iff₀ hlxB]
      have hqpos : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      have e1 : (q : ℝ) * Real.log x ^ B' ≤ q * L ^ B' := mul_le_mul_of_nonneg_left hlB hqpos
      have e2 : (J : ℝ) * ((q : ℝ) * L ^ B') ≤ J * g := by
        calc (J : ℝ) * ((q : ℝ) * L ^ B') = q * (J * L ^ B') := by ring
          _ ≤ q * L ^ B := mul_le_mul_of_nonneg_left hJLB hqpos
          _ ≤ H := hq1
          _ = J * g := hHJ
      have e3 := le_of_mul_le_mul_left e2 hJpos
      linarith
    have hzz : (L ^ B) ^ (-2 : ℤ) ≤ (L ^ (B - D)) ^ (-2 : ℤ) := by
      have h1 : L ^ (B - D) ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have h0 : 0 < L ^ (B - D) := Real.rpow_pos_of_pos hLpos _
      rw [zpow_neg, zpow_neg, zpow_two, zpow_two]
      exact inv_anti₀ (by positivity) (mul_self_le_mul_self h0.le h1)
    have hM2 : M ≤ x ^ (1 / 4 : ℝ) * Real.log x ^ (-2 * B') :=
      htop'.le.trans ((mul_le_mul_of_nonneg_left hzz (by positivity)).trans p3)
    have hz : z ≤ g * x ^ (-1 / 2 : ℝ) * Real.log x ^ (-2 * B') := by
      have := p4 (3 * g) (by linarith)
      rwa [show 3 * g / 3 = g by ring] at this
    have hx12 : x ^ (1 / 2 : ℝ) ≤ g := by
      rw [← Real.sqrt_eq_rpow]; exact (Real.sqrt_le_sqrt (by linarith)).trans hsg
    have hgx : g ≤ x := by linarith
    have key := k34 x g p1 hx12 hgx α q a hcop h41a h41b h41c am ham M z hM hM2 hz2 hz
    calc _ = _ := piece_congr_hi Y x g z z0 M z α hY hx1 hx3 hg0.le hgx
      _ ≤ C * g ^ 2 * Real.log x ^ (-A) := key
      _ ≤ _ := mul_le_mul_of_nonneg_left (logpow_le A L (Real.log x) hA hLpos p6)
          (by positivity)
  have hS : ∀ m ∈ squareWindow Y, (m : ℝ) ^ 2 < Y := fun m hm => squareWindow_sq_lt hY.le hm
  have hf : ∀ m ∈ squareWindow Y, ‖f m‖ ≤ 2 := by
    intro m hm
    simp only [hf_def]
    rw [norm_mul]
    have h1 : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := by
      simp only [fourier_apply, Circle.norm_coe]
    rw [h1, mul_one]
    exact interior_coeff_norm_le_two Y ε z0 M z hY1 hε.le m hm
  have hP1 := piece (Y / 4) le_rfl (by linarith) (by linarith)
  rw [show 2 * (Y / 4) = Y / 2 by ring] at hP1
  have hP2 := piece ((Y - g) / 2) (by linarith) (by linarith) (by linarith)
  rw [show 2 * ((Y - g) / 2) = Y - g by ring] at hP2
  have hreg := region_hi (squareWindow Y) f Y g (Y / 2 + H) hY hg0.le (by linarith)
    (by linarith) hS hf
  have hsh := shift_hi (squareWindow Y) f (Y / 4) (Y / 2) g H J (by linarith) hg0.le hHJ
  have hE : g * (2 * (g / Real.sqrt Y + 1)) ^ 2 ≤ 16 * g ^ 2 / L ^ A := by
    have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
    have hsq := Real.sq_sqrt hY.le
    have h1 : g / Real.sqrt Y + 1 ≤ 2 * g / Real.sqrt Y := by
      rw [div_add_one hsY.ne', div_le_div_iff_of_pos_right hsY]; linarith
    have h2 : (2 * (g / Real.sqrt Y + 1)) ^ 2 ≤ 16 * g ^ 2 / Y := by
      have h0 : 0 ≤ g / Real.sqrt Y + 1 := by positivity
      calc (2 * (g / Real.sqrt Y + 1)) ^ 2 ≤ (2 * (2 * g / Real.sqrt Y)) ^ 2 := by gcongr
        _ = 16 * g ^ 2 / Y := by rw [mul_pow, div_pow, mul_pow, hsq]; ring
    calc g * (2 * (g / Real.sqrt Y + 1)) ^ 2 ≤ g * (16 * g ^ 2 / Y) :=
          mul_le_mul_of_nonneg_left h2 hg0.le
      _ ≤ 16 * g ^ 2 / L ^ A := by
          rw [mul_div_assoc', div_le_div_iff₀ hY hLA]
          have := mul_le_mul_of_nonneg_left hgU (by positivity : (0 : ℝ) ≤ 16 * g ^ 2)
          linarith
  have hJ2' : (0 : ℝ) ≤ (J : ℝ) ^ 2 := by positivity
  calc _ ≤ _ := hsh
    _ ≤ (J : ℝ) ^ 2 * (C * g ^ 2 * ((24 / 7) ^ A / L ^ A) +
          C * g ^ 2 * ((24 / 7) ^ A / L ^ A) + 16 * g ^ 2 / L ^ A) := by
        apply mul_le_mul_of_nonneg_left _ hJ2'
        linarith
    _ = (2 * C * (24 / 7) ^ A + 16) * ((J : ℝ) * g) ^ 2 / L ^ A := by ring
    _ = _ := by rw [← hHJ]

/-- PROVED from `left_half_band_low` and `left_half_band_high`: the leaf for
eps below 1/6 and Y/4 < H < Y (log X)^(A/2), cut at H = Y/2. -/
theorem left_half_band (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        windowY X ε / 4 < H → H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := left_half_band_low A hA
  obtain ⟨B2, hB2, h2⟩ := left_half_band_high A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨max C1 C2, max X1 X2, lt_of_lt_of_le hC1 (le_max_left _ _),
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hHl hHu hHa hHb α q a hcop hqP hqQ hclose M hM htop hlow
  have hX1' : 1 < X := by linarith [le_max_left X1 X2]
  have hL : 0 < Real.log X := Real.log_pos hX1'
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  by_cases hs : H ≤ windowY X ε / 2
  · have e := k1 X H ((le_max_left _ _).trans hX) hHl hHu hHa hs α q a hcop hqP hqQ hclose
      M hM htop hlow
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · push Not at hs
    have e := k2 X H ((le_max_right _ _).trans hX) hHl hHu hs hHb α q a hcop hqP hqQ hclose
      M hM htop hlow
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

/-- PROVED from `left_half_small_H` and `left_half_band`: the hypothesis
`hcore` of `leaf_interior_left_half_of_core`, the leaf for eps below 1/6 and
H below Y (log X)^(A/2), cut at H = Y/4. -/
theorem left_half_core (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := left_half_small_H A hA
  obtain ⟨B2, hB2, h2⟩ := left_half_band A hA
  refine ⟨max B1 B2, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε hε' => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε'
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε'
  refine ⟨max C1 C2, max X1 X2, lt_of_lt_of_le hC1 (le_max_left _ _),
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hHl hHu hHb α q a hcop hqP hqQ hclose M hM htop hlow
  have hX1' : 1 < X := by linarith [le_max_left X1 X2]
  have hL : 0 < Real.log X := Real.log_pos hX1'
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  by_cases hs : H ≤ windowY X ε / 4
  · have e := k1 X H ((le_max_left _ _).trans hX) hHl hHu hs α q a hcop hqP hqQ hclose
      M hM htop hlow
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · push Not at hs
    have e := k2 X H ((le_max_right _ _).trans hX) hHl hHu hs hHb α q a hcop hqP hqQ hclose
      M hM htop hlow
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)

/-- PROVED from the leaves of this file: the exact statement of
`leaf_interior_left_half` of `SPLIT_lemma34_second_sum_dyadic`, through the
proved reduction `leaf_interior_left_half_of_core` of `InteriorHalvesAux`. -/
theorem leaf_interior_left_half_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A :=
  leaf_interior_left_half_of_core A (left_half_core A hA)

example : type_of% @leaf_interior_left_half := @leaf_interior_left_half_split

end LeanLab.KumchevLiu2007.Eq33RouteD.LeftHalf1122
