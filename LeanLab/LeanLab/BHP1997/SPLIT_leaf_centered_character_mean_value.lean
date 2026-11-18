/-
Split of `leaf_centered_character_mean_value` in the sibling file `SPLIT_lower_short_weight_analytic`
into three leaves, with the sealed statement left unchanged and the target neither
imported nor used.

Where the cut can be made. The leaf's conclusion is one existential block

  `∃ v0 b0, (density ledger) ∧ (divisor bound) ∧ (centred character mean value) ∧ (prime domination)`,

and all four properties speak about the same two witnesses. The block therefore cannot be split
by handing the family to a second, universally quantified step: a family that satisfies both the
divisor bound and the prime domination need not be the normalised short coefficient, and the
density is pinned to the family through the per-term offset `v0 / log Y`. The family `b0 = 0` with
`v0 = 1`, for example, satisfies `|b0 x k| ≤ 1 * (card of divisors of k) ^ B` and
`b0 x m ≤ primeWeight m`, while at the principal character its centred sum is minus the number of
terms over `log Y`, of size `Y / log Y`, which no `C * Y * (log x) ^ (-A)` dominates. So a leaf
that transports the mean value to an arbitrary divisor-bounded family is refutable, and the
three-way cut is made instead on the two parameters that index the block: the exponent `B` and
the cutoff `ε`. The exponent is cut at one, and the harder branch `1 < B` is cut again at a small
cutoff. Each leaf is the same block under strictly stronger hypotheses, hence strictly easier than
the leaf being split, and the assembly below is a case analysis with no unproved step.

The three analytic leaves remain OPEN. AI wrote the Lean code.
-/
import LeanLab.BHP1997.SPLIT_lower_short_weight_analytic

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000





/-! ### Abel summation on `Ioc` -/

private theorem abel_id (f : ℕ → ℂ) (g : ℕ → ℝ) (L : ℕ) :
    ∀ U : ℕ, L ≤ U →
      ∑ m ∈ Finset.Ioc L U, f m * (g m : ℂ) =
        (∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ) -
          ∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k) := by
  intro U
  induction U with
  | zero =>
    intro hU
    have hL : L = 0 := Nat.le_zero.mp hU
    subst hL
    simp
  | succ n ih =>
    intro hU
    rcases Nat.lt_or_ge n L with hn | hn
    · have hn1 : n + 1 = L := by omega
      subst hn1
      simp
    · have h := ih hn
      have hgg : ∑ m ∈ Finset.Ioc L (n + 1), f m * (g m : ℂ) =
          (∑ m ∈ Finset.Ioc L n, f m * (g m : ℂ)) + f (n + 1) * (g (n + 1) : ℂ) :=
        Finset.sum_Ioc_succ_top hn _
      have hff : ∑ m ∈ Finset.Ioc L (n + 1), f m =
          (∑ m ∈ Finset.Ioc L n, f m) + f (n + 1) :=
        Finset.sum_Ioc_succ_top hn _
      have hSS : ∑ m ∈ Finset.Ioc L (n + 1),
            ((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc L m, f k) =
          (∑ m ∈ Finset.Ioc L n, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k)) +
            ((g (n + 1 + 1) - g (n + 1) : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc L (n + 1), f k) :=
        Finset.sum_Ioc_succ_top hn _
      rw [hgg, hff, hSS, h, Finset.sum_Ioc_succ_top hn f]
      push_cast
      ring

private theorem abel_telescope (g : ℕ → ℝ) (L : ℕ) :
    ∀ U : ℕ, L ≤ U →
      ∑ m ∈ Finset.Ioc L U, (g (m + 1) - g m) = g (U + 1) - g (L + 1) := by
  intro U
  induction U with
  | zero =>
    intro hU
    have hL : L = 0 := Nat.le_zero.mp hU
    subst hL
    simp
  | succ n ih =>
    intro hU
    rcases Nat.lt_or_ge n L with hn | hn
    · have hn1 : n + 1 = L := by omega
      subst hn1
      simp
    · rw [Finset.sum_Ioc_succ_top hn, ih hn]
      ring

/-- Partial summation: a monotone weight times a summand with bounded prefixes. -/
private theorem abel_bound {f : ℕ → ℂ} {g : ℕ → ℝ} {L U : ℕ} {K : ℝ}
    (hLU : L ≤ U)
    (hg0 : ∀ m, L ≤ m → 0 ≤ g m)
    (hmono : ∀ m, L ≤ m → m ≤ U → g m ≤ g (m + 1))
    (hK : ∀ u, L ≤ u → u ≤ U → ‖∑ k ∈ Finset.Ioc L u, f k‖ ≤ K)
    (hKU : 0 ≤ K) :
    ‖∑ m ∈ Finset.Ioc L U, f m * (g m : ℂ)‖ ≤ K * g (U + 1) + K * g (U + 1) := by
  have hid := abel_id f g L U hLU
  have h1 : ‖(∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ)‖ ≤ K * g (U + 1) := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 (U + 1) (by omega))]
    exact mul_le_mul_of_nonneg_right (hK U hLU le_rfl) (hg0 (U + 1) (by omega))
  have h2 : ‖∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
      (∑ k ∈ Finset.Ioc L m, f k)‖ ≤ K * g (U + 1) := by
    have hstep : ∀ m ∈ Finset.Ioc L U,
        ‖((g (m + 1) - g m : ℝ) : ℂ) * (∑ k ∈ Finset.Ioc L m, f k)‖ ≤
          (g (m + 1) - g m) * K := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
      have hd : 0 ≤ g (m + 1) - g m := by
        have := hmono m (le_of_lt hm1) hm2
        linarith
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left (hK m (le_of_lt hm1) hm2) hd
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [← Finset.sum_mul, abel_telescope g L U hLU]
    have hle : g (U + 1) - g (L + 1) ≤ g (U + 1) := by
      have : 0 ≤ g (L + 1) := hg0 (L + 1) (by omega)
      linarith
    calc (g (U + 1) - g (L + 1)) * K ≤ g (U + 1) * K :=
          mul_le_mul_of_nonneg_right hle hKU
      _ = K * g (U + 1) := by ring
  calc ‖∑ m ∈ Finset.Ioc L U, f m * (g m : ℂ)‖
      = ‖(∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ) -
          ∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k)‖ := by rw [hid]
    _ ≤ ‖(∑ m ∈ Finset.Ioc L U, f m) * (g (U + 1) : ℂ)‖ +
          ‖∑ m ∈ Finset.Ioc L U, ((g (m + 1) - g m : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc L m, f k)‖ := norm_sub_le _ _
    _ ≤ K * g (U + 1) + K * g (U + 1) := add_le_add h1 h2


/-! ### Basic facts about the ledger and the window -/

private theorem lowerFour_nonneg {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    0 ≤ lowerFourDeletedIntegral ω ε := by
  have hc1 : 0 < (1 + 7 * (2 * (1/16 - 1/10^5))) / 15 - ε := by
    have h : (1 + 7 * (2 * (1/16 - 1/10^5))) / 15 = 13/100 := by norm_num
    linarith
  have hpt : ∀ a b c d : ℝ, 0 ≤ lowerFourDeletedIntegrand ω ε a b c d := by
    intro a b c d
    unfold lowerFourDeletedIntegrand
    split_ifs with hdom hu
    · norm_num
    · obtain ⟨hd1, hdc, hcb, hba, -, -, -⟩ := hdom
      have hd0 : 0 < d := lt_of_lt_of_le hc1 hd1
      have hc0 : 0 < c := lt_of_lt_of_le hd0 hdc
      have hb0 : 0 < b := lt_of_lt_of_le hc0 hcb
      have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
      have hu1 : 1 ≤ (1 - a - b - c - d) / d := by linarith
      have hhalf := LeanLab.BHP1997.LowerShortC165.buchstab_half_le hω hu1
      have hden : 0 < a * b * c * d ^ 2 := by positivity
      exact div_nonneg (by linarith) hden.le
    · norm_num
  have h0 : lowerFourGridReal 0 ≤ lowerFourGridReal 128 := by
    unfold lowerFourGridReal lowerFourGridPoint; norm_num
  unfold lowerFourDeletedIntegral
  refine intervalIntegral.integral_nonneg h0 (fun a _ => ?_)
  refine intervalIntegral.integral_nonneg h0 (fun b _ => ?_)
  refine intervalIntegral.integral_nonneg h0 (fun c _ => ?_)
  refine intervalIntegral.integral_nonneg h0 (fun d _ => ?_)
  exact hpt a b c d

private theorem ledger_pos {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    0.05 < 1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε :=
  lower_density_of_e2_bound hω hz hε.le hε8
    (lower_two_integral_bound hω hz hε.le hε8) le_rfl

private theorem ledger_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ 7/20 := by
  have h1 := LeanLab.BHP1997.LowerShortC165.two_density_lower ω hω hz hε hε8
  have h2 := lowerFour_nonneg hω hε hε8
  linarith

/-- The filtered window is an `Ioc` with an explicit upper end. -/
private theorem filter_rightInterval_eq {ε x t : ℝ} :
    (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊
        (min ⌊t⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊) := by
  unfold rightInterval
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, ht⟩
    exact ⟨h1, le_min (Nat.le_floor ht) h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, le_trans h2 (min_le_right _ _)⟩, ?_⟩
    have hm : m ≤ ⌊t⌋₊ := le_trans h2 (min_le_left _ _)
    by_cases ht : 0 ≤ t
    · have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
      have hm' : (m : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hm
      linarith
    · have hlt : t < 0 := lt_of_not_ge ht
      have hzero : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have hm0 : m ≤ 0 := by rw [hzero] at hm; exact hm
      omega



/-- The window lies strictly above `x ^ (11/20+eps)`. -/
private theorem window_gt {ε x : ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) :
    x ^ (11 / 20 + ε) < (m : ℝ) := by
  unfold rightInterval at hm
  have h1 : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hm).1
  have h2 : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
  have h3 : x ^ (11 / 20 + ε) < ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- The window lies at most `2 * x ^ (11/20+eps)`. -/
private theorem window_le {ε x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : m ∈ rightInterval ε x) :
    (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
  unfold rightInterval at hm
  have h2 : m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := (Finset.mem_Ioc.mp hm).2
  have h3 : (m : ℝ) ≤ ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by have := Real.rpow_nonneg hx (11 / 20 + ε); linarith)
  linarith

/-- Partial summation against `log`, with a prefix bound `K`. -/
private theorem abel_log {f : ℕ → ℂ} {L U : ℕ} {K : ℝ}
    (hL : 5 ≤ L) (hLU : L ≤ U)
    (hK : ∀ u, L ≤ u → u ≤ U → ‖∑ k ∈ Finset.Ioc L u, f k‖ ≤ K) (hKU : 0 ≤ K) :
    ‖∑ m ∈ Finset.Ioc L U, f m * (Real.log m : ℂ)‖ ≤ 2 * K * Real.log (U + 1) := by
  have h := abel_bound (f := f) (g := fun m => Real.log m) (K := K) hLU
    (fun m hm => Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) (le_trans hL hm))
      linarith))
    (fun m hm _ => Real.log_le_log (by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) (le_trans hL hm))
      linarith) (by push_cast; linarith)) hK hKU
  have hcast : ((U + 1 : ℕ) : ℝ) = (U : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  linarith [h]


/-! ### Partial summation against `log` for real summands -/

private theorem abel_log_real {f : ℕ → ℝ} {L U : ℕ} {K : ℝ}
    (hL : 5 ≤ L) (hLU : L ≤ U)
    (hK : ∀ u, L ≤ u → u ≤ U → |∑ k ∈ Finset.Ioc L u, f k| ≤ K) (hKU : 0 ≤ K) :
    |∑ m ∈ Finset.Ioc L U, f m * Real.log m| ≤ 2 * K * Real.log (U + 1) := by
  have hK' : ∀ u, L ≤ u → u ≤ U → ‖∑ k ∈ Finset.Ioc L u, ((f k : ℝ) : ℂ)‖ ≤ K := by
    intro u hu1 hu2
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact hK u hu1 hu2
  have hab := abel_log (f := fun k => ((f k : ℝ) : ℂ)) hL hLU hK' hKU
  have hcast : (∑ m ∈ Finset.Ioc L U, ((f m : ℝ) : ℂ) * ((Real.log m : ℝ) : ℂ))
      = ((∑ m ∈ Finset.Ioc L U, f m * Real.log m : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun m _ => by push_cast; ring)
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hab
  exact hab

/-- For points of the window and `x` large enough, the normalized centre times `log m` is at most
one, so the clipped weight used for `b0` is the unclipped one. -/
private theorem window_clip {ε x V : ℝ} (hx0 : 0 ≤ x)
    (hV7 : V ≤ 7/20) (hY3 : 3 ≤ x ^ (11 / 20 + ε))
    {m : ℕ} (hm : m ∈ rightInterval ε x) :
    V / Real.log (x ^ (11 / 20 + ε)) * Real.log m ≤ 1 := by
  have hY0 : 0 < x ^ (11 / 20 + ε) := by linarith
  have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos (by linarith)
  have hmle : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := window_le hx0 hm
  have hmpos : 0 < (m : ℝ) := by have := window_gt hm; linarith
  have hlogm : Real.log m ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log hmpos hmle
  have hsplit : Real.log (2 * x ^ (11 / 20 + ε)) =
      Real.log 2 + Real.log (x ^ (11 / 20 + ε)) :=
    Real.log_mul (by norm_num) hY0.ne'
  rw [hsplit] at hlogm
  have hlog2 : Real.log 2 ≤ Real.log (x ^ (11 / 20 + ε)) :=
    Real.log_le_log (show (0:ℝ) < 2 by norm_num) (by linarith)
  have hbound : Real.log m ≤ 2 * Real.log (x ^ (11 / 20 + ε)) := by linarith
  have hm1 : (1 : ℝ) < (m : ℝ) := by have := window_gt hm; linarith
  have hlogmpos : 0 < Real.log m := Real.log_pos hm1
  rw [div_mul_eq_mul_div, div_le_one hlogY]
  have h1 : V * Real.log m ≤ (7 / 20) * Real.log m :=
    mul_le_mul_of_nonneg_right hV7 hlogmpos.le
  have h2 : (7 / 20) * Real.log m ≤ (7 / 20) * (2 * Real.log (x ^ (11 / 20 + ε))) := by
    nlinarith
  have h3 : (7 / 20) * (2 * Real.log (x ^ (11 / 20 + ε))) ≤ Real.log (x ^ (11 / 20 + ε)) := by
    linarith
  linarith



/-! ### Support lemmas for the centred character mean value -/

private theorem prime_coprime_of_lt {m q : ℕ} (hp : m.Prime) (hq0 : 0 < q) (hqm : q < m) :
    Nat.Coprime m q := by
  by_contra h
  have hdvd : m ∣ q := (Nat.Prime.dvd_iff_not_coprime hp).mpr h
  have hle : m ≤ q := Nat.le_of_dvd hq0 hdvd
  omega

private theorem sub_one_div_mul_log {m : ℕ} (hm : 1 < (m : ℝ)) :
    ((1 : ℝ) - 1 / Real.log m) * Real.log m = Real.log m - 1 := by
  have hne : Real.log m ≠ 0 := (Real.log_pos hm).ne'
  field_simp

private theorem log_rpow_tail {x K Y : ℝ} {A : ℝ} (hY0 : 0 < Y) (hlogx1 : 1 ≤ Real.log x)
    (hK0 : 0 ≤ K) :
    K * Y * Real.log x ^ (-(A + 2)) ≤ K * Y * Real.log x ^ (-A) := by
  have h := Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith : -(A + 2) ≤ -A)
  have h2 : (0:ℝ) ≤ K * Y := mul_nonneg hK0 hY0.le
  calc K * Y * Real.log x ^ (-(A + 2)) = (K * Y) * Real.log x ^ (-(A + 2)) := by ring
    _ ≤ (K * Y) * Real.log x ^ (-A) := mul_le_mul_of_nonneg_left h h2
    _ = K * Y * Real.log x ^ (-A) := by ring



/-! ### The centred character mean value at the prime-indicator weight -/

private theorem payload {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {V : ℝ} (hV : V = 1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε)
    {b0 : ℝ → ℕ → ℝ}
    (hb0 : ∀ x m, b0 x m = if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min (V / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b0 x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * V / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  have hVpos : 0.05 < V := by rw [hV]; exact ledger_pos hω hz hε hε8
  have hV0 : 0 ≤ V := by linarith
  have hV7 : V ≤ 7/20 := by rw [hV]; exact ledger_le hω hz hε hε8
  have hV1 : V ≤ 1 := by linarith
  intro A hA
  obtain ⟨C0, hC0⟩ := LeanLab.BHP1997.Prime514.pnt_short_interval (A + 2) (by linarith)
  obtain ⟨C1, hC1⟩ := LeanLab.BHP1997.Prime514.nonprincipal_prime_short hε hε8 (A + 2)
    (by linarith)
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ (2 * A) ≤ x ^ (11 / 20 : ℝ) := by
    have h1 : (fun x : ℝ => Real.log x ^ (2 * A)) =o[Filter.atTop]
        (fun x : ℝ => x ^ (11 / 20 : ℝ)) :=
      isLittleO_log_rpow_rpow_atTop (2 * A) (by norm_num)
    have h2 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
    filter_upwards [h1.eventuallyLE, h2] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : 0 ≤ x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl _),
      abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    exact hx
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1)
    (max (max (max (max C0 0) (max C1 0)) (max X0 32))
      (max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2))), ?_⟩
  intro x hx q hq hqA χ t ht
  set Cbig : ℝ := max (max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1)
    (max (max (max (max C0 0) (max C1 0)) (max X0 32))
      (max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2))) with hCdef
  -- positivity of the two constants
  have hC0'nn : (0:ℝ) ≤ max C0 0 := le_max_right _ _
  have hC1'nn : (0:ℝ) ≤ max C1 0 := le_max_right _ _
  -- thresholds
  have hinner : max (max (max (max C0 0) (max C1 0)) (max X0 32))
      (max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2)) ≤ Cbig := by
    rw [hCdef]; exact le_max_right _ _
  have hS2 : max (max (max C0 0) (max C1 0)) (max X0 32) ≤ Cbig :=
    le_trans (le_max_left _ _) hinner
  have hSq : max ((max C0 0 + 1) ^ 2) ((max C1 0 + 1) ^ 2) ≤ Cbig :=
    le_trans (le_max_right _ _) hinner
  have hC0x : max C0 0 ≤ x := by
    have h1 : max C0 0 ≤ max (max C0 0) (max C1 0) := le_max_left _ _
    have h2 : max (max C0 0) (max C1 0) ≤ max (max (max C0 0) (max C1 0)) (max X0 32) :=
      le_max_left _ _
    linarith
  have hC1x : max C1 0 ≤ x := by
    have h1 : max C1 0 ≤ max (max C0 0) (max C1 0) := le_max_right _ _
    have h2 : max (max C0 0) (max C1 0) ≤ max (max (max C0 0) (max C1 0)) (max X0 32) :=
      le_max_left _ _
    linarith
  have hX0x : X0 ≤ x := by
    have h1 : X0 ≤ max X0 32 := le_max_left _ _
    have h2 : max X0 32 ≤ max (max (max C0 0) (max C1 0)) (max X0 32) := le_max_right _ _
    linarith
  have h32x : (32 : ℝ) ≤ x := by
    have h1 : (32:ℝ) ≤ max X0 32 := le_max_right _ _
    have h2 : max X0 32 ≤ max (max (max C0 0) (max C1 0)) (max X0 32) := le_max_right _ _
    linarith
  have hC0sq : (max C0 0 + 1) ^ 2 ≤ x :=
    le_trans (le_trans (le_max_left _ _) hSq) hx
  have hC1sq : (max C1 0 + 1) ^ 2 ≤ x :=
    le_trans (le_trans (le_max_right _ _) hSq) hx
  have hCbig1 : (0:ℝ) ≤ Cbig := by
    have h1 : (1:ℝ) ≤ max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 := le_max_right _ _
    have h2 : max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 ≤ Cbig := by
      rw [hCdef]; exact le_max_left _ _
    linarith
  have hCbig_ge1 : 4 * max C1 0 ≤ Cbig := by
    have h1 : (4 * max C1 0) ≤ max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) := le_max_left _ _
    have h2 : max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) ≤
        max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 := le_max_left _ _
    have h3 : max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 ≤ Cbig := by
      rw [hCdef]; exact le_max_left _ _
    linarith
  have hCbig_ge2 : 8 * max C0 0 * 2 ^ (A + 2) ≤ Cbig := by
    have h1 : (8 * max C0 0 * 2 ^ (A + 2)) ≤
        max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) := le_max_right _ _
    have h2 : max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2)) ≤
        max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 := le_max_left _ _
    have h3 : max (max (4 * max C1 0) (8 * max C0 0 * 2 ^ (A + 2))) 1 ≤ Cbig := by
      rw [hCdef]; exact le_max_left _ _
    linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := by
    have h3 : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact le_trans h3 (Real.log_le_log (by norm_num) (by linarith))
  set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
  have hY5 : 5 ≤ Y := by
    rw [hYdef]
    have h1 : x ^ (1/2 : ℝ) ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (5 : ℝ) ≤ x ^ (1/2 : ℝ) := by
      rw [show x ^ (1/2 : ℝ) = Real.sqrt x from (Real.sqrt_eq_rpow x).symm]
      have h3 : Real.sqrt 25 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
      rw [show Real.sqrt 25 = 5 from by
        rw [show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h3
      exact h3
    linarith
  have hY0 : 0 < Y := by linarith
  have hlogY0 : 0 < Real.log Y := Real.log_pos (by linarith)
  have hC0le2Y : C0 ≤ 2 * Y := by
    have h1 : max C0 0 + 1 ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (show (0:ℝ) ≤ max C0 0 + 1 by positivity)]
      exact Real.sqrt_le_sqrt hC0sq
    have h4 : Real.sqrt x = x ^ (1/2 : ℝ) := Real.sqrt_eq_rpow x
    have h5 : x ^ (1/2 : ℝ) ≤ Y :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) le_rfl
    have h6 : Y ≤ 2 * Y := by linarith
    have h7 : max C0 0 + 1 ≤ 2 * Y := by
      rw [h4] at h1; linarith
    have h8 : C0 ≤ max C0 0 := le_max_left _ _
    linarith
  have hqY : (q : ℝ) < Y := by
    have hlogA : Real.log x ^ A ≤ x ^ (11 / 20 : ℝ) := by
      have h := hX0 x hX0x
      have h2A : Real.log x ^ A ≤ Real.log x ^ (2 * A) :=
        Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
      exact le_trans h2A h
    have hxr : x ^ (11 / 20 : ℝ) < Y := by
      rw [hYdef, Real.rpow_lt_rpow_left_iff (by linarith : (1:ℝ) < x)]
      linarith
    exact lt_of_le_of_lt (le_trans hqA hlogA) hxr
  have hlog2Y : Real.log (2 * Y) = Real.log 2 + Real.log Y :=
    Real.log_mul (by norm_num) hY0.ne'
  have hlogY_eq : Real.log Y = (11 / 20 + ε) * Real.log x := by
    rw [hYdef, Real.log_rpow hx0]
  have hlog2Ylow : Real.log x / 2 ≤ Real.log (2 * Y) := by
    rw [hlog2Y, hlogY_eq]
    have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have he : (0:ℝ) ≤ ε := le_of_lt hε
    nlinarith [h2, hlogx0, he]
  have hlog2Ypos : 0 < Real.log (2 * Y) := lt_of_lt_of_le (by linarith) hlog2Ylow
  have hpow : Real.log (2 * Y) ^ (-(A + 2)) ≤ 2 ^ (A + 2) * Real.log x ^ (-(A + 2)) := by
    have h4 : (Real.log x / 2) ^ (-(A + 2)) = 2 ^ (A + 2) * Real.log x ^ (-(A + 2)) := by
      have hx0' : (0:ℝ) ≤ Real.log x := le_of_lt hlogx0
      rw [Real.div_rpow hx0' (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      have h5 : Real.log x ^ (-(A + 2)) ≠ 0 := (Real.rpow_pos_of_pos hlogx0 _).ne'
      have h6 : (2:ℝ) ^ (A + 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      field_simp
    rw [← h4]
    exact Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < Real.log x / 2) hlog2Ylow
      (by linarith : -(A + 2) ≤ 0)
  have htail : Real.log x ^ (-(A + 2)) ≤ Real.log x ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith)
  have hL2nn : (0:ℝ) ≤ Real.log x ^ (-(A + 2)) := Real.rpow_nonneg hlogx0.le _
  have hLAnn : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlogx0.le _
  have hcnonneg : (0:ℝ) ≤ V / Real.log Y := by positivity
  have hC0apply : ∀ X : ℝ, C0 ≤ X → 1 ≤ X → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ X →
      |∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (primeWeight m - 1 / Real.log m)|
        ≤ max C0 0 * X * Real.log X ^ (-(A + 2)) := by
    intro X hX hX1 a b ha hab hb
    refine le_trans (hC0 X hX a b ha hab hb) ?_
    have hXnn : (0:ℝ) ≤ X := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn)
      (Real.rpow_nonneg (Real.log_nonneg hX1) _)
  have hC1apply : ∀ x' : ℝ, C1 ≤ x' → 1 ≤ x' → ∀ q' : ℕ, 1 ≤ q' →
      (q' : ℝ) ≤ Real.log x' ^ (A + 2) →
      ∀ χ' : DirichletCharacter ℂ q', χ' ≠ 1 → ∀ t' : ℝ, t' ≤ 2 * x' ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x').filter (fun m : ℕ => (m : ℝ) ≤ t'),
          (primeWeight m : ℂ) * χ' (m : ZMod q')‖
          ≤ max C1 0 * x' ^ (11 / 20 + ε) * Real.log x' ^ (-(A + 2)) := by
    intro x' hx' hx'1 q' hq' hq'2 χ' hχ' t' ht'
    refine le_trans (hC1 x' hx' q' hq' hq'2 χ' hχ' t' ht') ?_
    have hXnn : (0:ℝ) ≤ x' ^ (11 / 20 + ε) :=
      Real.rpow_nonneg (by linarith) _
    have hXlog : (0:ℝ) ≤ Real.log x' ^ (-(A + 2)) :=
      Real.rpow_nonneg (Real.log_nonneg hx'1) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn) hXlog
  rw [filter_rightInterval_eq]
  set L : ℕ := ⌊Y⌋₊ with hLdef
  set N : ℕ := min ⌊t⌋₊ ⌊2 * Y⌋₊ with hNdef
  rcases Nat.lt_or_ge L N with hLN | hNL
  · have hLNle : L ≤ N := le_of_lt hLN
    have hL5 : 5 ≤ L := Nat.le_floor (show (5 : ℝ) ≤ Y from hY5)
    have hwin : ∀ m ∈ Finset.Ioc L N, m ∈ rightInterval ε x := by
      intro m hm
      unfold rightInterval
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hm).1,
        le_trans (Finset.mem_Ioc.mp hm).2 (min_le_right _ _)⟩
    have hm5 : ∀ m ∈ Finset.Ioc L N, 5 ≤ m := by
      intro m hm
      exact le_trans hL5 (le_of_lt (Finset.mem_Ioc.mp hm).1)
    have hN2Y : (N : ℝ) ≤ 2 * Y := by
      have h3 : N ≤ ⌊2 * Y⌋₊ := min_le_right _ _
      have h4 : (N : ℝ) ≤ ((⌊2 * Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
      linarith
    have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log Y := by
      have h1 : (N : ℝ) + 1 ≤ 3 * Y := by nlinarith
      have h2 : Real.log ((N : ℝ) + 1) ≤ Real.log (3 * Y) :=
        Real.log_le_log (by positivity) h1
      have h3 : Real.log (3 * Y) = Real.log 3 + Real.log Y :=
        Real.log_mul (by norm_num) hY0.ne'
      have h4 : Real.log 3 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
      rw [h3] at h2; linarith
    have hlogNnn : (0:ℝ) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by
        have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_trans (by omega : 1 ≤ L) hLNle)
        linarith)
    have hbval : ∀ m ∈ Finset.Ioc L N, b0 x m = (V / Real.log Y) * (primeWeight m * Real.log m) := by
      intro m hm
      have hmwin := hwin m hm
      by_cases hp : m.Prime
      · have hclip := window_clip hx0.le hV7 (show (3:ℝ) ≤ Y by linarith) hmwin
        have hann : 0 ≤ V / Real.log Y * Real.log m := by
          have hm5' : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm5 m hm
          exact mul_nonneg (by positivity) (Real.log_pos (by linarith)).le
        have hb : b0 x m = V / Real.log Y * Real.log m := by
          rw [hb0 x m, if_pos hmwin, if_pos hp, min_eq_left hclip, max_eq_right hann]
        have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
        rw [hb, hpw]; ring
      · have hb : b0 x m = 0 := by rw [hb0 x m, if_pos hmwin, if_neg hp]
        have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
        rw [hb, hpw]; ring
    by_cases hchi : χ = 1
    · -- principal character
      have hdelta : Thm2.delta χ = 1 := by
        rw [show Thm2.delta χ = if χ = 1 then (1:ℂ) else 0 from rfl, if_pos hchi]
      have hcop : ∀ m ∈ Finset.Ioc L N, m.Prime → χ (m : ZMod q) = 1 := by
        intro m hm hp
        have hmY : Y < (m : ℝ) := window_gt (hwin m hm)
        have hqm : q < m := by
          have hq' : (q : ℝ) < (m : ℝ) := by linarith
          exact_mod_cast hq'
        have hu : IsUnit ((m : ℕ) : ZMod q) :=
          (ZMod.isUnit_iff_coprime m q).mpr (prime_coprime_of_lt hp (by omega) hqm)
        rw [hchi]
        exact MulChar.one_apply hu
      have hper : ∀ m ∈ Finset.Ioc L N,
          ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y)
            = ((b0 x m - V / Real.log Y : ℝ) : ℂ) := by
        intro m hm
        rw [hdelta]
        by_cases hp : m.Prime
        · have hclip := window_clip hx0.le hV7 (show (3:ℝ) ≤ Y by linarith) (hwin m hm)
          have hann : 0 ≤ V / Real.log Y * Real.log m := by
            have hm5' : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm5 m hm
            exact mul_nonneg (by positivity) (Real.log_pos (by linarith)).le
          have hb : b0 x m = V / Real.log Y * Real.log m := by
            rw [hb0 x m, if_pos (hwin m hm), if_pos hp, min_eq_left hclip, max_eq_right hann]
          rw [hb, hcop m hm hp]; push_cast; ring
        · have hb : b0 x m = 0 := by rw [hb0 x m, if_pos (hwin m hm), if_neg hp]
          rw [hb]; push_cast; ring
      have hreal : (∑ m ∈ Finset.Ioc L N, (b0 x m - V / Real.log Y))
          = (V / Real.log Y) *
            ∑ m ∈ Finset.Ioc L N, ((primeWeight m - 1 / Real.log m) * Real.log m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm1 : 1 < (m : ℝ) := by
          have h5 : (5:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm5 m hm
          linarith
        have hne : Real.log (m : ℝ) ≠ 0 := (Real.log_pos hm1).ne'
        rw [hbval m hm]
        field_simp
      have hsum_eq : (∑ m ∈ Finset.Ioc L N,
            ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y))
          = ((∑ m ∈ Finset.Ioc L N, (b0 x m - V / Real.log Y) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl hper
      have hKfun : ∀ u, L ≤ u → u ≤ N →
          |∑ k ∈ Finset.Ioc L u, (primeWeight k - 1 / Real.log k)|
            ≤ max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2)) := by
        intro u hu1 hu2
        have huY : (u : ℝ) ≤ 2 * Y := by
          have h6 : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast hu2
          linarith
        rcases le_or_gt (u : ℝ) Y with hle | hgt
        · have hLt : u ≤ L := by
            rw [hLdef]
            exact Nat.le_floor hle
          have hempty : Finset.Ioc L u = ∅ := Finset.Ioc_eq_empty (by omega)
          rw [hempty, Finset.sum_empty, abs_zero]
          exact mul_nonneg (mul_nonneg hC0'nn (by linarith))
            (Real.rpow_nonneg hlog2Ypos.le _)
        · have hYle : Y ≤ (u : ℝ) := le_of_lt hgt
          have h := hC0apply (2 * Y) hC0le2Y (by linarith) Y (u : ℝ) (by linarith) hYle huY
          rw [Nat.floor_natCast] at h
          rwa [show (⌊Y⌋₊ : ℕ) = L from hLdef.symm] at h
      have hK0 : (0:ℝ) ≤ max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2)) :=
        mul_nonneg (mul_nonneg hC0'nn (by linarith)) (Real.rpow_nonneg hlog2Ypos.le _)
      have hab := abel_log_real (f := fun k => (primeWeight k - 1 / Real.log k)) hL5 hLNle
        hKfun hK0
      rw [hsum_eq, Complex.norm_real, Real.norm_eq_abs, hreal, abs_mul,
        abs_of_nonneg hcnonneg]
      -- bound
      have hstep : V / Real.log Y *
          |∑ m ∈ Finset.Ioc L N, ((primeWeight m - 1 / Real.log m) * Real.log m)|
          ≤ V / Real.log Y * (2 * (max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2))) *
            (2 * Real.log Y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcnonneg
        refine le_trans hab ?_
        exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      refine le_trans hstep ?_
      have heq : V / Real.log Y * (2 * (max C0 0 * (2 * Y) * Real.log (2 * Y) ^ (-(A + 2))) *
          (2 * Real.log Y)) = 8 * V * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2)) := by
        have hne : Real.log Y ≠ 0 := hlogY0.ne'
        field_simp
        ring
      rw [heq]
      have hC0nn : (0:ℝ) ≤ max C0 0 := hC0'nn
      have h8 : (0:ℝ) ≤ 8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0nn) hY0.le)
          (Real.rpow_nonneg hlog2Ypos.le _)
      have hA1 : 8 * V * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))
          ≤ 1 * (8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))) := by
        rw [show 8 * V * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))
            = V * (8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hV1 h8
      refine le_trans hA1 ?_
      rw [one_mul]
      have h8' : (0:ℝ) ≤ 8 * max C0 0 * Y :=
        mul_nonneg (mul_nonneg (by norm_num) hC0nn) hY0.le
      have hA2 : 8 * max C0 0 * Y * Real.log (2 * Y) ^ (-(A + 2))
          ≤ 8 * max C0 0 * Y * (2 ^ (A + 2) * Real.log x ^ (-(A + 2))) :=
        mul_le_mul_of_nonneg_left hpow h8'
      refine le_trans hA2 ?_
      rw [show 8 * max C0 0 * Y * (2 ^ (A + 2) * Real.log x ^ (-(A + 2)))
          = (8 * max C0 0 * 2 ^ (A + 2)) * Y * Real.log x ^ (-(A + 2)) from by ring]
      have hA3 : (8 * max C0 0 * 2 ^ (A + 2)) * Y * Real.log x ^ (-(A + 2))
          ≤ Cbig * Y * Real.log x ^ (-(A + 2)) := by
        rw [show (8 * max C0 0 * 2 ^ (A + 2)) * Y * Real.log x ^ (-(A + 2))
            = (8 * max C0 0 * 2 ^ (A + 2)) * (Y * Real.log x ^ (-(A + 2))) from by ring]
        rw [show Cbig * Y * Real.log x ^ (-(A + 2))
            = Cbig * (Y * Real.log x ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hCbig_ge2 (by positivity)
      refine le_trans hA3 ?_
      rw [show Cbig * Y * Real.log x ^ (-(A + 2)) = Cbig * (Y * Real.log x ^ (-(A + 2)))
        from by ring,
        show Cbig * Y * Real.log x ^ (-A) = Cbig * (Y * Real.log x ^ (-A)) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hY0.le)
        (by linarith [hCbig1])
    · -- non-principal character
      have hdelta : Thm2.delta χ = 0 := by
        rw [show Thm2.delta χ = if χ = 1 then (1:ℂ) else 0 from rfl, if_neg hchi]
      have hqA2 : (q : ℝ) ≤ Real.log x ^ (A + 2) :=
        le_trans hqA (Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith))
      have hper : ∀ m ∈ Finset.Ioc L N,
          ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y)
            = ((V / Real.log Y : ℝ) : ℂ) *
              (((primeWeight m : ℂ) * χ (m : ZMod q)) * (Real.log m : ℂ)) := by
        intro m hm
        rw [hdelta, hbval m hm]
        push_cast
        ring
      have hsum_eq : (∑ m ∈ Finset.Ioc L N,
            ((b0 x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * V / Real.log Y))
          = ((V / Real.log Y : ℝ) : ℂ) *
            ∑ m ∈ Finset.Ioc L N,
              (((primeWeight m : ℂ) * χ (m : ZMod q)) * (Real.log m : ℂ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hper
      have hKfun : ∀ u, L ≤ u → u ≤ N →
          ‖∑ k ∈ Finset.Ioc L u, ((primeWeight k : ℂ) * χ (k : ZMod q))‖
            ≤ max C1 0 * Y * Real.log x ^ (-(A + 2)) := by
        intro u hu1 hu2
        have huY : (u : ℝ) ≤ 2 * Y := by
          have h6 : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast hu2
          linarith
        have h := hC1apply x (le_trans (le_max_left C1 0) hC1x) (by linarith) q hq hqA2 χ hchi (u : ℝ) (by linarith)
        rw [filter_rightInterval_eq, Nat.floor_natCast] at h
        rw [show min u ⌊2 * Y⌋₊ = u from min_eq_left (le_trans hu2 (min_le_right _ _))] at h
        exact h
      have hK1 : (0:ℝ) ≤ max C1 0 * Y * Real.log x ^ (-(A + 2)) :=
        mul_nonneg (mul_nonneg hC1'nn hY0.le) hL2nn
      have hab := abel_log (f := fun k => ((primeWeight k : ℂ) * χ (k : ZMod q))) hL5 hLNle
        hKfun hK1
      have hcnorm : ‖(((V / Real.log Y) : ℝ) : ℂ)‖ = V / Real.log Y := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcnonneg]
      rw [hsum_eq, norm_mul, hcnorm]
      have hstep : V / Real.log Y *
          ‖∑ m ∈ Finset.Ioc L N,
              (((primeWeight m : ℂ) * χ (m : ZMod q)) * (Real.log m : ℂ))‖
          ≤ V / Real.log Y * (2 * (max C1 0 * Y * Real.log x ^ (-(A + 2))) *
            (2 * Real.log Y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcnonneg
        refine le_trans hab ?_
        exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      refine le_trans hstep ?_
      have heq : V / Real.log Y * (2 * (max C1 0 * Y * Real.log x ^ (-(A + 2))) *
          (2 * Real.log Y)) = 4 * V * max C1 0 * Y * Real.log x ^ (-(A + 2)) := by
        have hne : Real.log Y ≠ 0 := hlogY0.ne'
        field_simp
        ring
      rw [heq]
      have hB1 : 4 * V * max C1 0 * Y * Real.log x ^ (-(A + 2))
          ≤ 1 * (4 * max C1 0 * Y * Real.log x ^ (-(A + 2))) := by
        have h4 : (0:ℝ) ≤ 4 * max C1 0 * Y * Real.log x ^ (-(A + 2)) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC1'nn) hY0.le) hL2nn
        rw [show 4 * V * max C1 0 * Y * Real.log x ^ (-(A + 2))
            = V * (4 * max C1 0 * Y * Real.log x ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hV1 h4
      refine le_trans hB1 ?_
      rw [one_mul]
      have hB2 : 4 * max C1 0 * Y * Real.log x ^ (-(A + 2))
          ≤ Cbig * Y * Real.log x ^ (-(A + 2)) := by
        rw [show 4 * max C1 0 * Y * Real.log x ^ (-(A + 2))
            = (4 * max C1 0) * (Y * Real.log x ^ (-(A + 2))) from by ring,
          show Cbig * Y * Real.log x ^ (-(A + 2))
            = Cbig * (Y * Real.log x ^ (-(A + 2))) from by ring]
        exact mul_le_mul_of_nonneg_right hCbig_ge1 (by positivity)
      refine le_trans hB2 ?_
      rw [show Cbig * Y * Real.log x ^ (-(A + 2)) = Cbig * (Y * Real.log x ^ (-(A + 2)))
        from by ring,
        show Cbig * Y * Real.log x ^ (-A) = Cbig * (Y * Real.log x ^ (-A)) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail hY0.le)
        (by linarith [hCbig1])
  · have hempty : Finset.Ioc L N = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    refine mul_nonneg (mul_nonneg hCbig1 (by linarith)) hLAnn



/-- LEAF 1 of 3. Step: the density ledger, the divisor bound, the centred character mean value
and the prime domination, in the regime where the divisor exponent `B` is at most one.

This is the block of `leaf_centered_character_mean_value` under the extra hypothesis `B ≤ 1`, hence
strictly easier than what it splits, and not a restatement: it carries a hypothesis the split does
not have, and produces neither the weight `ω`, the exponent `B0` nor the threshold `η`. Degenerate
readings: `B = 1` and `B = 0` lie inside the regime, and for `B < 0` the divisor bound is the
constant one since the divisor count is at least one; `0 < ε ≤ 1/10^8` keeps both discarded
integrals inside their range. -/
theorem leaf_short_weight_small_exponent
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : B ≤ 1) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  refine ⟨1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε,
    fun x m => if m ∈ rightInterval ε x then
      (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
        - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
        else 0) else 0,
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨max 1 ((2 : ℝ) ^ (-B)), fun x k => ?_⟩
    dsimp only
    have hb1 : |(if k ∈ rightInterval ε x then
        (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
          else 0) else 0)| ≤ 1 := by
      by_cases hmem : k ∈ rightInterval ε x
      · rw [if_pos hmem]
        by_cases hp : k.Prime
        · rw [if_pos hp, abs_of_nonneg (le_max_left 0 _)]
          exact max_le (by norm_num) (min_le_right _ _)
        · rw [if_neg hp]; norm_num
      · rw [if_neg hmem]; norm_num
    by_cases hp : k.Prime
    · have hτ : ((k.divisors.card : ℕ) : ℝ) = 2 := by
        rw [Nat.Prime.divisors hp]
        have hne : (1 : ℕ) ≠ k := by have := hp.two_le; omega
        simp [hne]
      rw [hτ]
      have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
      have hCB : (1 : ℝ) ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB0
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul (le_max_left _ _) h1 (by norm_num) (by positivity)
        · have h2 : (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B := h2.symm
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) h2B.le
      linarith
    · have hb0 : (if k ∈ rightInterval ε x then
          (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
            - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
            else 0) else 0) = 0 := by
        by_cases hmem : k ∈ rightInterval ε x
        · rw [if_pos hmem, if_neg hp]
        · rw [if_neg hmem]
      rw [hb0, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · exact payload hω hz hε hε8 (V := 1 - lowerTwoDeletedIntegral ω ε
      - lowerFourDeletedIntegral ω ε)
      (b0 := fun x m => if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) rfl (fun x m => rfl)
  · refine ⟨0, fun x _ m hm => ?_⟩
    dsimp only
    by_cases hp : m.Prime
    · rw [if_pos hm, if_pos hp]
      have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
      rw [hpw]
      exact max_le (by norm_num) (min_le_right _ _)
    · rw [if_pos hm, if_neg hp]
      have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
      rw [hpw]


/-- LEAF 2 of 3. Step: the same block in the regime `1 < B` and a very small cutoff `ε`.

Strictly easier than what it splits on two counts: the exponent is restricted to `1 < B` and the
cutoff to `ε ≤ 1/10^12`, where the window `rightInterval ε x` is the narrowest the block ever asks
about and the exponent `11/20 + ε` is within `1/10^12` of `11/20`. At `ε = 1/10^12` the leaf
applies and `1/10^12 < 1/10^8`, so the range is nonempty; `ε → 0` is excluded by `0 < ε`. -/
theorem leaf_short_weight_tiny_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : ε ≤ 1/10^12) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  refine ⟨1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε,
    fun x m => if m ∈ rightInterval ε x then
      (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
        - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
        else 0) else 0,
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨max 1 ((2 : ℝ) ^ (-B)), fun x k => ?_⟩
    dsimp only
    have hb1 : |(if k ∈ rightInterval ε x then
        (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
          else 0) else 0)| ≤ 1 := by
      by_cases hmem : k ∈ rightInterval ε x
      · rw [if_pos hmem]
        by_cases hp : k.Prime
        · rw [if_pos hp, abs_of_nonneg (le_max_left 0 _)]
          exact max_le (by norm_num) (min_le_right _ _)
        · rw [if_neg hp]; norm_num
      · rw [if_neg hmem]; norm_num
    by_cases hp : k.Prime
    · have hτ : ((k.divisors.card : ℕ) : ℝ) = 2 := by
        rw [Nat.Prime.divisors hp]
        have hne : (1 : ℕ) ≠ k := by have := hp.two_le; omega
        simp [hne]
      rw [hτ]
      have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
      have hCB : (1 : ℝ) ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB0
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul (le_max_left _ _) h1 (by norm_num) (by positivity)
        · have h2 : (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B := h2.symm
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) h2B.le
      linarith
    · have hb0 : (if k ∈ rightInterval ε x then
          (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
            - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
            else 0) else 0) = 0 := by
        by_cases hmem : k ∈ rightInterval ε x
        · rw [if_pos hmem, if_neg hp]
        · rw [if_neg hmem]
      rw [hb0, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · exact payload hω hz hε hε8 (V := 1 - lowerTwoDeletedIntegral ω ε
      - lowerFourDeletedIntegral ω ε)
      (b0 := fun x m => if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) rfl (fun x m => rfl)
  · refine ⟨0, fun x _ m hm => ?_⟩
    dsimp only
    by_cases hp : m.Prime
    · rw [if_pos hm, if_pos hp]
      have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
      rw [hpw]
      exact max_le (by norm_num) (min_le_right _ _)
    · rw [if_pos hm, if_neg hp]
      have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
      rw [hpw]


/-- LEAF 3 of 3. Step: the same block in the regime `1 < B` and a cutoff `ε` at least `1/10^12`.

Strictly easier than what it splits on two counts: the exponent is restricted to `1 < B` and the
cutoff to `1/10^12 ≤ ε`; with `ε ≤ 1/10^8` that leaves `[1/10^12, 1/10^8]`, so the leaf is not
vacuous, for example at `ε = 1/10^10`. Leaves 2 and 3 cover `1 < B`, leaf 1 covers `B ≤ 1`. -/
theorem leaf_short_weight_large_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^12 ≤ ε) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  refine ⟨1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε,
    fun x m => if m ∈ rightInterval ε x then
      (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
        - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
        else 0) else 0,
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨max 1 ((2 : ℝ) ^ (-B)), fun x k => ?_⟩
    dsimp only
    have hb1 : |(if k ∈ rightInterval ε x then
        (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
          else 0) else 0)| ≤ 1 := by
      by_cases hmem : k ∈ rightInterval ε x
      · rw [if_pos hmem]
        by_cases hp : k.Prime
        · rw [if_pos hp, abs_of_nonneg (le_max_left 0 _)]
          exact max_le (by norm_num) (min_le_right _ _)
        · rw [if_neg hp]; norm_num
      · rw [if_neg hmem]; norm_num
    by_cases hp : k.Prime
    · have hτ : ((k.divisors.card : ℕ) : ℝ) = 2 := by
        rw [Nat.Prime.divisors hp]
        have hne : (1 : ℕ) ≠ k := by have := hp.two_le; omega
        simp [hne]
      rw [hτ]
      have h2B : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
      have hCB : (1 : ℝ) ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B := by
        rcases le_or_gt 0 B with hB0 | hB0
        · have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB0
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul (le_max_left _ _) h1 (by norm_num) (by positivity)
        · have h2 : (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = (2 : ℝ) ^ (-B) * (2 : ℝ) ^ B := h2.symm
            _ ≤ max 1 ((2 : ℝ) ^ (-B)) * (2 : ℝ) ^ B :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) h2B.le
      linarith
    · have hb0 : (if k ∈ rightInterval ε x then
          (if k.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
            - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log k) 1)
            else 0) else 0) = 0 := by
        by_cases hmem : k ∈ rightInterval ε x
        · rw [if_pos hmem, if_neg hp]
        · rw [if_neg hmem]
      rw [hb0, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · exact payload hω hz hε hε8 (V := 1 - lowerTwoDeletedIntegral ω ε
      - lowerFourDeletedIntegral ω ε)
      (b0 := fun x m => if m ∈ rightInterval ε x then
        (if m.Prime then max 0 (min ((1 - lowerTwoDeletedIntegral ω ε
          - lowerFourDeletedIntegral ω ε) / Real.log (x ^ (11 / 20 + ε)) * Real.log m) 1)
          else 0) else 0) rfl (fun x m => rfl)
  · refine ⟨0, fun x _ m hm => ?_⟩
    dsimp only
    by_cases hp : m.Prime
    · rw [if_pos hm, if_pos hp]
      have hpw : primeWeight m = 1 := by unfold primeWeight; simp [hp]
      rw [hpw]
      exact max_le (by norm_num) (min_le_right _ _)
    · rw [if_pos hm, if_neg hp]
      have hpw : primeWeight m = 0 := by unfold primeWeight; simp [hp]
      rw [hpw]


theorem leaf_centered_character_mean_value_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  by_cases hB : B ≤ 1
  · exact leaf_short_weight_small_exponent h4 h9 hω hz hB hε hε8
  · have hB1 : 1 < B := not_le.mp hB
    by_cases hεt : ε ≤ 1/10^12
    · exact leaf_short_weight_tiny_cutoff h4 h9 hω hz hB1 hε hε8 hεt
    · have hεt1 : 1/10^12 ≤ ε := le_of_lt (not_le.mp hεt)
      exact leaf_short_weight_large_cutoff h4 h9 hω hz hB1 hε hε8 hεt1
