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
  set g : ℝ := 3 * c4 / 4 with hg
  have hgpos : 0 < g := by rw [hg]; positivity
  set B : ℝ := 8 * Real.pi * (karN0 c1 c2 c4 + 1) with hB
  have hk : (12 : ℝ) ≤ karN0 c1 c2 c4 := le_max_left _ _
  have hBpos : 0 < B := by
    rw [hB]
    exact mul_pos (by positivity) (by linarith)
  refine ⟨max 1 (B ^ (1 / g)), le_max_left _ _, ?_⟩
  intro n hn hnk P hP
  have hP1 : 1 ≤ P := le_trans (le_max_left _ _) hP
  have hPB : B ^ (1 / g) ≤ P := le_trans (le_max_right _ _) hP
  have hc1ρ : c1 * ρ ≤ 3 * c4 / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hρc hc1.le
    have e : c1 * (3 * c4 / (4 * c1)) = 3 * c4 / 4 := by field_simp
    linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : g ≤ (c4 / 2) * ((n : ℝ) + 1 + ρ) - c1 * ρ := by
    have h1 : (c4 / 2) * 3 ≤ (c4 / 2) * ((n : ℝ) + 1 + ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hg]
    linarith
  calc 8 * Real.pi * ((n : ℝ) + 1) ≤ B := by
        rw [hB]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (B ^ (1 / g)) ^ g := by
        rw [← Real.rpow_mul hBpos.le, one_div, inv_mul_cancel₀ hgpos.ne', Real.rpow_one]
    _ ≤ P ^ g := Real.rpow_le_rpow (Real.rpow_nonneg hBpos.le _) hPB hgpos.le
    _ ≤ P ^ ((c4 / 2) * ((n : ℝ) + 1 + ρ) - c1 * ρ) :=
        Real.rpow_le_rpow_of_exponent_le hP1 hexp

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
  sorry

/-- `e(t) = exp(2πit)`: its real and imaginary parts and its Lipschitz constant `4π`. -/
private theorem eC_re (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  rw [eC, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

private theorem eC_im (t : ℝ) : (eC t).im = Real.sin (2 * Real.pi * t) := by
  rw [eC, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

/-- `e(t) = exp(2πit)` is Lipschitz with constant `4π`. -/
private theorem norm_eC_sub_le (u v : ℝ) : ‖eC u - eC v‖ ≤ 4 * Real.pi * |u - v| := by
  have h1 : ‖eC u - eC v‖ ≤ |(eC u - eC v).re| + |(eC u - eC v).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have h2 : |(eC u - eC v).re| = |Real.cos (2 * Real.pi * u) - Real.cos (2 * Real.pi * v)| := by
    rw [Complex.sub_re, eC_re, eC_re]
  have h3 : |(eC u - eC v).im| = |Real.sin (2 * Real.pi * u) - Real.sin (2 * Real.pi * v)| := by
    rw [Complex.sub_im, eC_im, eC_im]
  have h4 : |Real.cos (2 * Real.pi * u) - Real.cos (2 * Real.pi * v)| ≤ 2 * Real.pi * |u - v| := by
    have := Real.abs_cos_sub_cos_le (2 * Real.pi * u) (2 * Real.pi * v)
    rw [show 2 * Real.pi * u - 2 * Real.pi * v = 2 * Real.pi * (u - v) by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at this
    exact this
  have h5 : |Real.sin (2 * Real.pi * u) - Real.sin (2 * Real.pi * v)| ≤ 2 * Real.pi * |u - v| := by
    have := Real.abs_sin_sub_sin_le (2 * Real.pi * u) (2 * Real.pi * v)
    rw [show 2 * Real.pi * u - 2 * Real.pi * v = 2 * Real.pi * (u - v) by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at this
    exact this
  rw [h2, h3] at h1
  linarith

/-- The block Taylor remainder: on a block `[a, a+m)` inside `[N, N+P]`, the `n`-th Taylor
polynomial at the left end misses `f` by at most `(n+1) P^{-c1(n+1)} m^{n+1}`. -/
private theorem taylor_remainder_block
    {c0 c1 c2 c3 : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hH : KarHyp c0 c1 c2 c3 N P n f T) (hP : 0 < P)
    {a m : ℕ} (ha : N ≤ a) (ham : a + m ≤ N + P) :
    ∀ y : ℕ, y ≤ m →
      |f ((a : ℝ) + (y : ℝ)) -
        taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ)
          ((a : ℝ) + (y : ℝ))|
        ≤ ((n : ℝ) + 1) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (m : ℝ) ^ (n + 1) := by
  obtain ⟨U, hUopen, hUI, hCf⟩ := hH.1
  have hCn := hH.2.1
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have haR : (N : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hamR : (a : ℝ) + (m : ℝ) ≤ (N : ℝ) + (P : ℝ) := by
    have h : ((a + m : ℕ) : ℝ) ≤ ((N + P : ℕ) : ℝ) := by exact_mod_cast ham
    push_cast at h
    linarith
  have hsub : Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ)) ⊆ U := by
    intro z hz
    exact hUI ⟨by linarith [hz.1], by linarith [hz.2]⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    intro y hy
    have hy0 : y = 0 := by omega
    subst hy0
    rw [Nat.cast_zero, add_zero, taylorWithinEval_self, sub_self, abs_zero]
    positivity
  · have hab : (a : ℝ) < (a : ℝ) + (m : ℝ) := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      linarith
    have hu : UniqueDiffOn ℝ (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) := uniqueDiffOn_Icc hab
    have hCdiff : ContDiffOn ℝ (n + 1) f (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) :=
      hCf.mono (fun z hz => hsub hz)
    have hCbd : ∀ z ∈ Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ)),
        ‖iteratedDerivWithin (n + 1) f (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) z‖
          ≤ ((n + 1).factorial : ℝ) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := by
      intro z hz
      have hzU : z ∈ U := hsub hz
      have hcont : ContDiffAt ℝ (n + 1) f z := hCf.contDiffAt (hUopen.mem_nhds hzU)
      have heq : iteratedDerivWithin (n + 1) f (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) z
          = iteratedDeriv (n + 1) f z := iteratedDerivWithin_eq_iteratedDeriv hu hcont hz
      have hzI : z ∈ Set.Icc (N : ℝ) ((N : ℝ) + (P : ℝ)) :=
        ⟨by linarith [hz.1], by linarith [hz.2]⟩
      have hb := hCn z hzI
      have hb' : ‖iteratedDeriv (n + 1) f z‖ / ((n + 1).factorial : ℝ)
          ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := by
        rw [← Real.norm_eq_abs, norm_div, Real.norm_natCast] at hb
        exact hb
      have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
      rw [div_le_iff₀ hfac] at hb'
      rw [heq, Real.norm_eq_abs]
      calc |iteratedDeriv (n + 1) f z| = ‖iteratedDeriv (n + 1) f z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ((n + 1).factorial : ℝ) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := by
            rw [mul_comm]; exact hb'
    intro y hy
    have hym : (y : ℝ) ≤ (m : ℝ) := by exact_mod_cast hy
    have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
    have hx : (a : ℝ) + (y : ℝ) ∈ Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ)) := by
      refine ⟨by linarith, by linarith⟩
    have hmain := taylor_mean_remainder_bound (f := f) (a := (a : ℝ)) (b := (a : ℝ) + (m : ℝ))
      (C := ((n + 1).factorial : ℝ) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))))
      (x := (a : ℝ) + (y : ℝ)) (n := n) hab.le hCdiff hx hCbd
    rw [Real.norm_eq_abs] at hmain
    refine hmain.trans ?_
    have hxa : (a : ℝ) + (y : ℝ) - (a : ℝ) = (y : ℝ) := by ring
    rw [hxa]
    have hpow : (y : ℝ) ^ (n + 1) ≤ (m : ℝ) ^ (n + 1) := pow_le_pow_left₀ hy0 hym _
    have hPnn : (0 : ℝ) ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) := Real.rpow_nonneg hPr.le _
    have hfs : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hfac : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by positivity
    rw [hfs]
    rw [show ((n : ℝ) + 1) * (n.factorial : ℝ) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) *
        (y : ℝ) ^ (n + 1) / (n.factorial : ℝ)
        = ((n : ℝ) + 1) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (y : ℝ) ^ (n + 1) by
      field_simp]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)


/-- Changing each term of a block sum by a remainder bounded by `ε` costs `m * 4π ε`. -/
private theorem sum_eC_le_add {g h : ℕ → ℝ} {m : ℕ} {ε : ℝ}
    (_hε : 0 ≤ ε) (hgh : ∀ y, y < m → |g y - h y| ≤ ε) :
    ‖∑ y ∈ Finset.range m, eC (g y)‖ ≤
      ‖∑ y ∈ Finset.range m, eC (h y)‖ + (m : ℝ) * (4 * Real.pi * ε) := by
  have hdecomp : ∑ y ∈ Finset.range m, eC (g y) =
      (∑ y ∈ Finset.range m, eC (h y)) + ∑ y ∈ Finset.range m, (eC (g y) - eC (h y)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hb : ‖∑ y ∈ Finset.range m, (eC (g y) - eC (h y))‖ ≤ (m : ℝ) * (4 * Real.pi * ε) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ Finset.range m, ‖eC (g y) - eC (h y)‖
        ≤ ∑ y ∈ Finset.range m, (4 * Real.pi * ε) := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          refine (norm_eC_sub_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (hgh y (Finset.mem_range.1 hy))
            (by positivity)
      _ = (m : ℝ) * (4 * Real.pi * ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hdecomp]
  linarith [norm_add_le (∑ y ∈ Finset.range m, eC (h y))
    (∑ y ∈ Finset.range m, (eC (g y) - eC (h y)))]

/-- The p. 248 Taylor reduction: on a block `[a, a+m)` inside `[N, N+P]` the exponential sum
over `f` is that over the `n`-th Taylor polynomial at `a`, up to `m` times the remainder
`4π (n+1) P^{-c1(n+1)} m^{n+1}`. -/
private theorem block_sum_taylor_reduction
    {c0 c1 c2 c3 : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hH : KarHyp c0 c1 c2 c3 N P n f T) (hP : 0 < P)
    {a m : ℕ} (ha : N ≤ a) (ham : a + m ≤ N + P) :
    ‖∑ x ∈ Finset.Ico a (a + m), eC (f x)‖ ≤
      ‖∑ y ∈ Finset.range m,
        eC (taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ)
          ((a : ℝ) + (y : ℝ)))‖ +
      (m : ℝ) * (4 * Real.pi * (((n : ℝ) + 1) *
        (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (m : ℝ) ^ (n + 1))) := by
  have hrem := taylor_remainder_block hH hP ha ham
  have hε : (0 : ℝ) ≤ ((n : ℝ) + 1) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (m : ℝ) ^ (n + 1) := by
    have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have := Real.rpow_nonneg hPr.le (-(c1 * ((n + 1 : ℕ) : ℝ)))
    positivity
  have hfun : ∀ y : ℕ, y < m →
      |f ((a : ℝ) + (y : ℝ)) - taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ)))
        (a : ℝ) ((a : ℝ) + (y : ℝ))| ≤
        ((n : ℝ) + 1) * (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (m : ℝ) ^ (n + 1) :=
    fun y hy => hrem y (le_of_lt hy)
  have h := sum_eC_le_add (g := fun y => f ((a : ℝ) + (y : ℝ)))
    (h := fun y => taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ)
      ((a : ℝ) + (y : ℝ))) (m := m) (ε := ((n : ℝ) + 1) *
        (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ))) * (m : ℝ) ^ (n + 1)) hε hfun
  rw [Finset.sum_Ico_eq_sum_range, show a + m - a = m by omega]
  simpa using h

/-- The saving swallows the Taylor remainder: if the block length `m` is at least one and at
most `P^(c1 - c4/2)`, `rho > 0`, and `P` is past the threshold `8 pi D <= P^((c4/2)(D + rho)
- c1 rho)` with `D = n + 1`, then the whole remainder contribution
`m * 4 pi (D P^(-c1 D) m^D)` of a block is at most `(1/2) m^(1 - rho)`, half of the saving
that the block estimate spends. -/
private lemma saving_absorbs_remainder
    {c1 c4 ρ D P m : ℝ} (hP : 1 < P) (hm : 1 ≤ m) (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hAm : m ≤ P ^ (c1 - c4 / 2))
    (hthr : 8 * Real.pi * D ≤ P ^ ((c4 / 2) * (D + ρ) - c1 * ρ)) :
    m * (4 * Real.pi * (D * P ^ (-(c1 * D)) * m ^ D)) ≤ 1 / 2 * m ^ (1 - ρ) := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hDρ : 0 ≤ D + ρ := by linarith
  -- the block length against the block power
  have hpow : m ^ (D + ρ) ≤ P ^ ((c1 - c4 / 2) * (D + ρ)) := by
    calc m ^ (D + ρ) ≤ (P ^ (c1 - c4 / 2)) ^ (D + ρ) :=
          Real.rpow_le_rpow hm0.le hAm hDρ
      _ = P ^ ((c1 - c4 / 2) * (D + ρ)) := (Real.rpow_mul hP0.le _ _).symm
  -- the three exponents cancel
  have hcancel : (c4 / 2) * (D + ρ) - c1 * ρ + ((c1 - c4 / 2) * (D + ρ)) + -(c1 * D) = 0 := by
    ring
  have hprod : P ^ ((c4 / 2) * (D + ρ) - c1 * ρ) * P ^ ((c1 - c4 / 2) * (D + ρ)) *
      P ^ (-(c1 * D)) = 1 := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0, hcancel, Real.rpow_zero]
  -- so the whole bracket is at most one
  have hkey : 8 * Real.pi * D * P ^ (-(c1 * D)) * m ^ (D + ρ) ≤ 1 := by
    have hnn1 : (0 : ℝ) ≤ P ^ ((c4 / 2) * (D + ρ) - c1 * ρ) := Real.rpow_nonneg hP0.le _
    have hnn2 : (0 : ℝ) ≤ P ^ ((c1 - c4 / 2) * (D + ρ)) := Real.rpow_nonneg hP0.le _
    have hnn3 : (0 : ℝ) ≤ P ^ (-(c1 * D)) := Real.rpow_nonneg hP0.le _
    have hstep : 8 * Real.pi * D * m ^ (D + ρ) ≤
        P ^ ((c4 / 2) * (D + ρ) - c1 * ρ) * P ^ ((c1 - c4 / 2) * (D + ρ)) :=
      mul_le_mul hthr hpow (Real.rpow_nonneg hm0.le _) hnn1
    calc 8 * Real.pi * D * P ^ (-(c1 * D)) * m ^ (D + ρ)
        = (8 * Real.pi * D * m ^ (D + ρ)) * P ^ (-(c1 * D)) := by ring
      _ ≤ (P ^ ((c4 / 2) * (D + ρ) - c1 * ρ) * P ^ ((c1 - c4 / 2) * (D + ρ))) *
            P ^ (-(c1 * D)) := mul_le_mul_of_nonneg_right hstep hnn3
      _ = 1 := hprod
  -- the remainder is `(1/2) m^(1-rho)` times that bracket
  have hfac : m * (4 * Real.pi * (D * P ^ (-(c1 * D)) * m ^ D)) =
      1 / 2 * m ^ (1 - ρ) * (8 * Real.pi * D * P ^ (-(c1 * D)) * m ^ (D + ρ)) := by
    have hmD : m ^ (1 - ρ) * m ^ (D + ρ) = m ^ (D + 1) := by
      rw [← Real.rpow_add hm0]
      congr 1
      ring
    have hmD1 : m * m ^ D = m ^ (D + 1) := by
      have h := Real.rpow_add hm0 (1 : ℝ) D
      rw [Real.rpow_one] at h
      rw [← h]
      congr 1
      ring
    calc m * (4 * Real.pi * (D * P ^ (-(c1 * D)) * m ^ D))
        = 4 * Real.pi * D * P ^ (-(c1 * D)) * (m * m ^ D) := by ring
      _ = 4 * Real.pi * D * P ^ (-(c1 * D)) * m ^ (D + 1) := by rw [hmD1]
      _ = 4 * Real.pi * D * P ^ (-(c1 * D)) * (m ^ (1 - ρ) * m ^ (D + ρ)) := by rw [hmD]
      _ = 1 / 2 * m ^ (1 - ρ) * (8 * Real.pi * D * P ^ (-(c1 * D)) * m ^ (D + ρ)) := by ring
  rw [hfac]
  have hsave : (0 : ℝ) ≤ 1 / 2 * m ^ (1 - ρ) := by positivity
  calc 1 / 2 * m ^ (1 - ρ) * (8 * Real.pi * D * P ^ (-(c1 * D)) * m ^ (D + ρ))
      ≤ 1 / 2 * m ^ (1 - ρ) * 1 := mul_le_mul_of_nonneg_left hkey hsave
    _ = 1 / 2 * m ^ (1 - ρ) := by ring


/-- The p. 248 reduction with the remainder removed: on a block of length `m` inside `[N, N+P]`
the exponential sum over `f` is at most the exponential sum over the `n`-th Taylor polynomial at
the left end plus half of the saving `m^(1-rho)`. This is `block_sum_taylor_reduction` with its
remainder term absorbed by `saving_absorbs_remainder`, and it leaves nothing but the polynomial
sum. -/
private theorem block_sum_reduced_to_polynomial
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
  have hP0 : 0 < P := Nat.zero_lt_of_lt hP
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_one hm))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hD : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hred := block_sum_taylor_reduction hH hP0 ha ham
  have habs := saving_absorbs_remainder (c1 := c1) (c4 := c4) (ρ := ρ) (D := (n : ℝ) + 1)
    (P := (P : ℝ)) (m := (m : ℝ)) (by exact_mod_cast hP) hm1 hρ hD hAm hthr
  -- the two power mismatches between the two statements
  have hDcast : (n : ℝ) + 1 = (((n + 1 : ℕ)) : ℝ) := by push_cast; ring
  have hmpow : (m : ℝ) ^ (n + 1) = (m : ℝ) ^ ((n : ℝ) + 1) := by
    rw [hDcast, Real.rpow_natCast]
  have hPpow : (P : ℝ) ^ (-(c1 * (((n + 1 : ℕ)) : ℝ))) =
      (P : ℝ) ^ (-(c1 * ((n : ℝ) + 1))) := by
    rw [hDcast]
  rw [hmpow, hPpow] at hred
  linarith [hred, habs]


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
  exact block_sum_reduced_to_polynomial hH hP hρ ha ham hm hAm hthr

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

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_block_threshold
