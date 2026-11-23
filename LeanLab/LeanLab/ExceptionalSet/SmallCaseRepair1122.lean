/-
A sound split of the sealed statement `leaf_small_case` of
`LeanLab.ExceptionalSet.KaracubaSplit`, the case `2 ≤ n < n0` of Karacuba's Theorem 1,
A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971) 241-255, proved on p. 248.

Why a repair. The earlier split `SPLIT_leaf_small_case` reduces to the block leaf
`leaf_small_block_sum_bound`, and `SPLIT_leaf_small_block_sum_bound` to
`leaf_polynomial_block_sum`. Both are FALSE as stated, refuted by a kernel checked file this
burst: they allow every block length `1 ≤ m ≤ P^(c1 - c4/2)`, and a block much shorter than
`P^(c2)` sees an almost constant phase and saves nothing. Karacuba p. 248 uses ONE block
length `P2 = [P^(c1 - γ2/n³)]` and needs `Q_s ≤ P^(c2 s) < P2^s`, a LOWER bound on the block.

The repair. Every block leaf below carries the one fixed block length
`L = ⌊P^(c1 - c4/2)⌋₊`, Karacuba's `P2` with `γ2/n³` taken to be `c4/2`, admissible since
`c2 + c4/2 < c1`, and `L ≥ P^(c1 - c4/2)/2` once `P` is large. Karacuba averages the shifted
sums `T(x) = Σ_{y=0}^{P2} e(f(x+y))` over all `x`; here `[N, N + P₁)` is cut into consecutive
blocks of the one length `L`, the same estimate with the same cost, and the last partial block
is bounded trivially by `L ≤ P^(1-γ/n²)`. Every block lies inside `[N, N + P₁) ⊆ [N, N + P]`,
so the points never pass `N + P`, the gap of the write up noted at `leaf_small_case`.

Status. The assembly `leaf_small_case_repaired` has exactly the type of `leaf_small_case`,
`h2 : KarLemma2` included, and this file has NO sorry: every piece is proved, from the cited
hypothesis `KarLemma2` and from the PROVED theorems `leaf_taylor_block_reduction`,
`leaf_block_threshold`, `leaf_small_bookkeeping` and `leaf_block_length_ge` of the two earlier
split files, none of which depends on the refuted leaves. So the case `2 ≤ n < n0` of
Karacuba's Theorem 1 is CONDITIONAL ON Karacuba's Lemma 2 only, Vinogradov's estimate, which
`KaracubaSplit` carries as the CITED leaf `leaf_karLemma2`.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_small_block_sum_bound

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-! ### Elementary tools -/

/-- `e(u + v) = e(u) e(v)`. -/
theorem eC_add_r1122 (u v : ℝ) : eC (u + v) = eC u * eC v := by
  unfold eC
  rw [show 2 * ↑Real.pi * Complex.I * ↑(u + v)
      = 2 * ↑Real.pi * Complex.I * ↑u + 2 * ↑Real.pi * Complex.I * ↑v by
    push_cast
    ring]
  rw [Complex.exp_add]

/-- `e(0) = 1`. -/
theorem eC_zero_r1122 : eC 0 = 1 := by
  unfold eC
  simp

/-- A sum over `range (n+1)` is its `0` term plus the sum over `Icc 1 n`. -/
theorem sum_range_succ_eq_zero_add_Icc_r1122 {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), g j = g 0 + ∑ j ∈ Finset.Icc 1 n, g j
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_range_succ_eq_zero_add_Icc_r1122 g n,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), add_assoc]

/-- PROVED. The partition of p. 248 with one fixed block length: if every block
`[a, a + L)` inside `[S, E]` has sum at most `C`, and every term has norm at most one, then
`[N, N + P₁)` inside `[S, E]` has sum at most `(P₁/L) C + L`; the last partial block, shorter
than `L`, is counted trivially. -/
theorem fixed_block_partition_r1122 (g : ℕ → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (hL : 0 < L) (S E : ℕ)
    (hblk : ∀ a : ℕ, S ≤ a → a + L ≤ E → ‖∑ x ∈ Finset.Ico a (a + L), g x‖ ≤ C) :
    ∀ P₁ N : ℕ, S ≤ N → N + P₁ ≤ E →
      ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖ ≤ (P₁ : ℝ) / (L : ℝ) * C + L := by
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  intro P₁
  induction P₁ using Nat.strong_induction_on with
  | _ P₁ ih =>
    intro N hSN hNE
    rcases Nat.lt_or_ge P₁ L with hPL | hLP
    · have h1 : ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖ ≤ P₁ := by
        calc ‖∑ x ∈ Finset.Ico N (N + P₁), g x‖ ≤ ∑ x ∈ Finset.Ico N (N + P₁), ‖g x‖ :=
              norm_sum_le _ _
          _ ≤ ∑ x ∈ Finset.Ico N (N + P₁), (1 : ℝ) := Finset.sum_le_sum (fun x _ => hg x)
          _ = P₁ := by simp
      have h2 : (P₁ : ℝ) ≤ L := by exact_mod_cast hPL.le
      have h3 : 0 ≤ (P₁ : ℝ) / (L : ℝ) * C := by positivity
      linarith
    · have hsplit : ∑ x ∈ Finset.Ico N (N + P₁), g x
          = ∑ x ∈ Finset.Ico N (N + L), g x + ∑ x ∈ Finset.Ico (N + L) (N + P₁), g x :=
        (Finset.sum_Ico_consecutive g (by omega : N ≤ N + L) (by omega : N + L ≤ N + P₁)).symm
      rw [hsplit]
      have hfirst := hblk N hSN (by omega)
      have htail := ih (P₁ - L) (by omega) (N + L) (by omega) (by omega)
      rw [show N + L + (P₁ - L) = N + P₁ by omega] at htail
      have hcast : ((P₁ - L : ℕ) : ℝ) = (P₁ : ℝ) - (L : ℝ) := by
        push_cast [Nat.cast_sub hLP]
        ring
      rw [hcast] at htail
      have harith : ((P₁ : ℝ) - L) / L * C + C = (P₁ : ℝ) / L * C := by
        field_simp
        ring
      calc ‖∑ x ∈ Finset.Ico N (N + L), g x + ∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖
          ≤ ‖∑ x ∈ Finset.Ico N (N + L), g x‖ + ‖∑ x ∈ Finset.Ico (N + L) (N + P₁), g x‖ :=
            norm_add_le _ _
        _ ≤ C + (((P₁ : ℝ) - L) / L * C + L) := add_le_add hfirst htail
        _ = (P₁ : ℝ) / (L : ℝ) * C + L := by rw [← harith]; ring

/-! ### Taylor's formula at the left end of a block, p. 248 -/

/-- PROVED. Karacuba p. 248, `f(x + y) = B_0 + B_1 y + ... + B_n y^n + R` with
`B_s = f^(s)(x)/s!`: the `n`-th Taylor polynomial of `f` at the left end `a` of a block
`[a, a + m]` inside `[N, N + P]`, written out with the ordinary derivatives of `f` at `a`. -/
theorem taylor_expand_r1122 {c0 c1 c2 c3 : ℝ} {N P n : ℕ} {f : ℝ → ℝ} {T : Finset ℕ}
    (hH : KarHyp c0 c1 c2 c3 N P n f T) {a m : ℕ} (ha : N ≤ a) (ham : a + m ≤ N + P)
    (hm : 1 ≤ m) (y : ℝ) :
    taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) (a : ℝ) ((a : ℝ) + y) =
      ∑ j ∈ Finset.range (n + 1), iteratedDeriv j f a / (j.factorial : ℝ) * y ^ j := by
  obtain ⟨U, hUopen, hUI, hCf⟩ := hH.1
  have haR : (N : ℝ) ≤ a := by exact_mod_cast ha
  have hamR : (a : ℝ) + m ≤ N + P := by exact_mod_cast ham
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : UniqueDiffOn ℝ (Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ))) :=
    uniqueDiffOn_Icc (by linarith)
  have haI : (a : ℝ) ∈ Set.Icc (a : ℝ) ((a : ℝ) + (m : ℝ)) := ⟨le_rfl, by linarith⟩
  have haU : (a : ℝ) ∈ U := hUI ⟨haR, by linarith⟩
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjn : j ≤ n + 1 := by have := Finset.mem_range.1 hj; omega
  have hcont : ContDiffAt ℝ j f a :=
    (hCf.contDiffAt (hUopen.mem_nhds haU)).of_le (by exact_mod_cast hjn)
  rw [iteratedDerivWithin_eq_iteratedDeriv hu hcont haI, smul_eq_mul, add_sub_cancel_left,
    div_eq_mul_inv]
  ring

/-! ### The Weyl sum input, Lemma 2 at one coefficient -/

/-- Dirichlet approximation with a denominator bound, from Mathlib: for `Q > 0` and real `α`
there are `A` and `q` with `gcd A q = 1`, `1 ≤ q ≤ Q` and `|α - A/q| ≤ 1/(Q q)`. The same
statement as a private lemma of `SPLIT_leaf_small_case`, restated here since that one cannot
be imported. -/
theorem exists_rat_approx_r1122 (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (A : ℤ) (q : ℕ), Int.gcd A q = 1 ∧ 1 ≤ q ∧ q ≤ Q ∧
      |α - (A : ℝ) / (q : ℝ)| ≤ 1 / ((Q : ℝ) * (q : ℝ)) := by
  obtain ⟨r, h1, h2⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hdpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hle : (Q : ℝ) * (r.den : ℝ) ≤ ((Q : ℝ) + 1) * (r.den : ℝ) := by nlinarith
  have hmono : 1 / (((Q : ℝ) + 1) * (r.den : ℝ)) ≤ 1 / ((Q : ℝ) * (r.den : ℝ)) :=
    one_div_le_one_div_of_le (mul_pos hQpos hdpos) hle
  refine ⟨r.num, r.den, r.reduced, r.den_pos, h2, ?_⟩
  have hr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def]
  rw [← hr]
  exact h1.trans hmono

/-- PROVED. Karacuba p. 248, display `B_s = a/Q_s + θ_s/Q_s², |Q_s| ≤ P^(c2 s)`, by
Dirichlet's theorem. The paper prints the numerator as `1`; it is an integer `a` coprime to
`Q_s`, as Lemma 2 asks. For `P` past a threshold depending on `c2, c3` only, every real `β`
with `P^(-c2 s) ≤ |β| ≤ P^(-c3 s)`, `s ≥ 1`, has `β = a/q + θ/q²` with `gcd(a, q) = 1`,
`|θ| ≤ 1`, `1 < q ≤ 2 P^(c2 s)`, and also `q ≥ P^(c3 s)/2`, the lower bound that makes `τ` of
Lemma 2 positive. Dirichlet at level `Q = ⌊P^(c2 s)⌋ + 1 > P^(c2 s)`; `q = 1` is excluded since
then `a = 0` by `|β| < 1/2` and `|β| ≤ 1/Q < P^(-c2 s)`; the lower bound follows from
`1/q ≤ |a/q| ≤ |β| + 1/(2q)`. -/
theorem dirichlet_coefficient_r1122 :
    ∀ c2 c3 : ℝ, 0 < c2 → 0 < c3 →
      ∃ P0 : ℝ, 1 ≤ P0 ∧ ∀ P : ℕ, P0 ≤ (P : ℝ) → ∀ s : ℕ, 1 ≤ s → ∀ β : ℝ,
        (P : ℝ) ^ (-(c2 * (s : ℝ))) ≤ |β| → |β| ≤ (P : ℝ) ^ (-(c3 * (s : ℝ))) →
        ∃ (a : ℤ) (q : ℕ) (θ : ℝ), Int.gcd a q = 1 ∧ 1 < q ∧
          (q : ℝ) ≤ 2 * (P : ℝ) ^ (c2 * (s : ℝ)) ∧ (P : ℝ) ^ (c3 * (s : ℝ)) / 2 ≤ (q : ℝ) ∧
          |θ| ≤ 1 ∧ β = (a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2 := by
  intro c2 c3 hc2 hc3
  refine ⟨max ((4 : ℝ) ^ (1 / c3)) 1, le_max_right _ _, ?_⟩
  intro P hP s hs β hlow hupp
  have hP1 : (1 : ℝ) ≤ P := le_trans (le_max_right _ _) hP
  have hP4 : (4 : ℝ) ^ (1 / c3) ≤ P := le_trans (le_max_left _ _) hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hPc3 : (4 : ℝ) ≤ (P : ℝ) ^ (c3 * (s : ℝ)) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / c3)) ^ c3 := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc3.ne', Real.rpow_one]
      _ ≤ (P : ℝ) ^ c3 := Real.rpow_le_rpow (by positivity) hP4 hc3.le
      _ ≤ (P : ℝ) ^ (c3 * (s : ℝ)) := Real.rpow_le_rpow_of_exponent_le hP1 (by nlinarith)
  set Y := (P : ℝ) ^ (c3 * (s : ℝ)) with hYdef
  have hYpos : 0 < Y := by linarith
  rw [Real.rpow_neg hPpos.le, ← hYdef] at hupp
  have hβ4 : |β| ≤ 1 / 4 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hPc3
    rw [one_div]; linarith
  set X := (P : ℝ) ^ (c2 * (s : ℝ)) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hP1 (by positivity)
  rw [Real.rpow_neg hPpos.le, ← hXdef] at hlow
  set Q := ⌊X⌋₊ + 1 with hQdef
  have hQX : X < (Q : ℝ) := by
    rw [hQdef]; push_cast; exact Nat.lt_floor_add_one X
  have hQle : (Q : ℝ) ≤ X + 1 := by
    rw [hQdef]; push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ X)]
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by
    have : (1 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by exact_mod_cast hX1)
    rw [hQdef]; push_cast; linarith
  have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
  have h1Q : 1 / (Q : ℝ) < X⁻¹ := by
    rw [one_div]; exact inv_strictAnti₀ (by linarith) hQX
  obtain ⟨a, q, hgcd, hq1, hqQ, herr⟩ := exists_rat_approx_r1122 β Q (Nat.succ_pos _)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqQr : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  -- `a ≠ 0`
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, zero_div, sub_zero] at herr
    have : 1 / ((Q : ℝ) * (q : ℝ)) ≤ 1 / (Q : ℝ) := by
      apply one_div_le_one_div_of_le hQpos
      nlinarith [(by exact_mod_cast hq1 : (1 : ℝ) ≤ (q : ℝ))]
    linarith
  have haabs : (1 : ℝ) ≤ |(a : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs ha0
  -- `q ≥ 2`
  have hq2 : 1 < q := by
    by_contra hcon
    have hq : q = 1 := by omega
    rw [hq, Nat.cast_one, div_one, mul_one] at herr
    have h12 : 1 / (Q : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hQ2
    have : |(a : ℝ)| ≤ |β| + |β - (a : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (a : ℝ) β
      rw [abs_sub_comm] at this
      linarith
    linarith
  refine ⟨a, q, (q : ℝ) ^ 2 * (β - (a : ℝ) / (q : ℝ)), hgcd, hq2, ?_, ?_, ?_, ?_⟩
  · linarith
  · -- the lower bound `q ≥ Y/2`
    have hfar : 1 / (q : ℝ) ≤ |(a : ℝ) / (q : ℝ)| := by
      rw [abs_div, abs_of_pos hqpos]
      exact div_le_div_of_nonneg_right haabs hqpos.le
    have hnear : |(a : ℝ) / (q : ℝ)| ≤ |β| + 1 / ((Q : ℝ) * (q : ℝ)) := by
      have := abs_sub_abs_le_abs_sub ((a : ℝ) / (q : ℝ)) β
      rw [abs_sub_comm] at this
      linarith
    have hQq : 1 / ((Q : ℝ) * (q : ℝ)) ≤ 1 / (2 * (q : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hhalf : 1 / (2 * (q : ℝ)) ≤ Y⁻¹ := by
      have e : 1 / (q : ℝ) = 1 / (2 * (q : ℝ)) + 1 / (2 * (q : ℝ)) := by field_simp; ring
      linarith
    rw [one_div] at hhalf
    have := (inv_le_inv₀ (by positivity) hYpos).1 hhalf
    linarith
  · -- `|θ| ≤ 1`
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (q : ℝ) ^ 2 * |β - (a : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ 2 * (1 / ((Q : ℝ) * (q : ℝ))) :=
          mul_le_mul_of_nonneg_left herr (by positivity)
      _ = (q : ℝ) / (Q : ℝ) := by field_simp
      _ ≤ 1 := (div_le_one hQpos).2 hqQr
  · field_simp
    ring

/-- A threshold `P ≥ 2^(k/e)` in logarithmic form: `k log 2 ≤ e log P`. -/
theorem log_ge_of_two_rpow_le_r1122 {k e P : ℝ} (he : 0 < e) (h : (2 : ℝ) ^ (k / e) ≤ P) :
    k * Real.log 2 ≤ e * Real.log P := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k / e) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 := Real.log_le_log hpos h
  rw [Real.log_rpow (by norm_num)] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 he.le
  have e1 : e * (k / e * Real.log 2) = k * Real.log 2 := by field_simp
  linarith

/-- PROVED. Karacuba p. 248, `|Q_s| ≤ P^(c2 s) < P2^s` and "it is easy to see that `τ`
of this lemma is some positive constant". With the fixed block length `M`,
`P^(c1 - c4/2)/4 ≤ M ≤ P^(c1 - c4/2)`, and a denominator `P^(c3 s)/2 ≤ q ≤ 2 P^(c2 s)`,
`2 ≤ s ≤ n < n0`, for `P` past a threshold: `q < M^s`, because `c2 < c1 - c4/2`, and the
parameter `τ` of Lemma 2, p. 243, taken at `P := M`, `r := s`, lies in `[τ0, 1]` with `τ0 > 0`
depending on `c1, ..., c4` only. In the range `q ≤ M`, `τ = log q/log M ≥ c3 s/(2 (c1 - c4/2))`
roughly; in `M < q ≤ M^(s-1)`, `τ = 1`; in `M^(s-1) < q < M^s`,
`τ = s - log q/log M ≥ s (1 - c2/(c1 - c4/2))` roughly. -/
theorem tau_range_r1122 :
    ∀ c1 c2 c3 c4 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → c1 < 1 → c2 + c4 < c1 →
      ∃ τ0 P0 : ℝ, 0 < τ0 ∧ τ0 ≤ 1 ∧ 1 ≤ P0 ∧
        ∀ (P n s M q : ℕ), 2 ≤ s → s ≤ n → (n : ℝ) < karN0 c1 c2 c4 → P0 ≤ (P : ℝ) →
          (P : ℝ) ^ (c1 - c4 / 2) / 4 ≤ (M : ℝ) → (M : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) →
          (P : ℝ) ^ (c3 * (s : ℝ)) / 2 ≤ (q : ℝ) → (q : ℝ) ≤ 2 * (P : ℝ) ^ (c2 * (s : ℝ)) →
          (q : ℝ) < (M : ℝ) ^ s ∧ τ0 ≤ karTau (M : ℝ) (q : ℝ) s ∧ karTau (M : ℝ) (q : ℝ) s ≤ 1 := by
  intro c1 c2 c3 c4 hc1 hc2 hc3 hc4 hc11 h241
  set A := c1 - c4 / 2 with hAdef
  have hA : 0 < A := by linarith
  set d := A - c2 with hddef
  have hd : 0 < d := by linarith
  set τ0 := min (min (c3 / A) (d / A)) 1 with hτ0def
  have hτ0pos : 0 < τ0 := lt_min (lt_min (div_pos hc3 hA) (div_pos hd hA)) one_pos
  have hτ0c3 : τ0 * A ≤ c3 := by
    have : τ0 ≤ c3 / A := le_trans (min_le_left _ _) (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right this hA.le
    rwa [div_mul_cancel₀ _ hA.ne'] at this
  have hτ0d : τ0 * A ≤ d := by
    have : τ0 ≤ d / A := le_trans (min_le_left _ _) (min_le_right _ _)
    have := mul_le_mul_of_nonneg_right this hA.le
    rwa [div_mul_cancel₀ _ hA.ne'] at this
  set P0 := max (max ((2 : ℝ) ^ (4 / A)) ((2 : ℝ) ^ (6 / d))) (max ((2 : ℝ) ^ (1 / c3)) 1)
    with hP0def
  refine ⟨τ0, P0, hτ0pos, min_le_right _ _, le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro P n s M q hs2 hsn hn0 hP hM4 hMA hqlow hqup
  have hP1 : (1 : ℝ) ≤ P := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set lam := Real.log (P : ℝ) with hlamdef
  have hlam : 0 ≤ lam := Real.log_nonneg hP1
  have hAl : 4 * Real.log 2 ≤ A * lam := log_ge_of_two_rpow_le_r1122 hA
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP)
  have hdl : 6 * Real.log 2 ≤ d * lam := log_ge_of_two_rpow_le_r1122 hd
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP)
  have hcl : 1 * Real.log 2 ≤ c3 * lam := log_ge_of_two_rpow_le_r1122 hc3
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hP)
  have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
  -- logarithms of `M` and `q`
  have hPA : 0 < (P : ℝ) ^ A := Real.rpow_pos_of_pos hPpos _
  have hlogPA : Real.log ((P : ℝ) ^ A) = A * lam := Real.log_rpow hPpos _
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le (by positivity) hM4
  have hlogMlo : A * lam - 2 * Real.log 2 ≤ Real.log (M : ℝ) := by
    have := Real.log_le_log (by positivity) hM4
    rw [Real.log_div hPA.ne' (by norm_num), hlogPA, hlog4] at this
    exact this
  have hlogMhi : Real.log (M : ℝ) ≤ A * lam := by
    have := Real.log_le_log hMpos hMA
    rwa [hlogPA] at this
  have hlogM : 0 < Real.log (M : ℝ) := by linarith
  have hY : 0 < (P : ℝ) ^ (c3 * (s : ℝ)) := Real.rpow_pos_of_pos hPpos _
  have hX : 0 < (P : ℝ) ^ (c2 * (s : ℝ)) := Real.rpow_pos_of_pos hPpos _
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (by positivity) hqlow
  have hlogqlo : c3 * (s : ℝ) * lam - Real.log 2 ≤ Real.log (q : ℝ) := by
    have := Real.log_le_log (by positivity) hqlow
    rwa [Real.log_div hY.ne' (by norm_num), Real.log_rpow hPpos] at this
  have hlogqhi : Real.log (q : ℝ) ≤ c2 * (s : ℝ) * lam + Real.log 2 := by
    have := Real.log_le_log hqpos hqup
    rwa [Real.log_mul (by norm_num) hX.ne', Real.log_rpow hPpos, add_comm] at this
  -- `q < M^s`
  have hlogMs : Real.log ((M : ℝ) ^ s) = (s : ℝ) * Real.log (M : ℝ) := Real.log_pow _ _
  have hqlt : Real.log (q : ℝ) < Real.log ((M : ℝ) ^ s) := by
    rw [hlogMs]
    have h1 : (s : ℝ) * (A * lam - 2 * Real.log 2) ≤ (s : ℝ) * Real.log (M : ℝ) :=
      mul_le_mul_of_nonneg_left hlogMlo (by linarith)
    have h2 : (s : ℝ) * (6 * Real.log 2) ≤ (s : ℝ) * (d * lam) :=
      mul_le_mul_of_nonneg_left hdl (by linarith)
    have e1 : (s : ℝ) * (A * lam - 2 * Real.log 2) =
        c2 * (s : ℝ) * lam + (s : ℝ) * (d * lam) - 2 * (s : ℝ) * Real.log 2 := by
      rw [hddef]; ring
    nlinarith
  have hqM : (q : ℝ) < (M : ℝ) ^ s := (Real.log_lt_log_iff hqpos (by positivity)).1 hqlt
  refine ⟨hqM, ?_⟩
  unfold karTau
  split_ifs with h1 h2
  · -- `q ≤ M`: `τ = log q / log M`
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hlogM]
      have k1 : τ0 * Real.log (M : ℝ) ≤ τ0 * (A * lam) :=
        mul_le_mul_of_nonneg_left hlogMhi hτ0pos.le
      have k2 : τ0 * (A * lam) ≤ c3 * lam := by
        have := mul_le_mul_of_nonneg_right hτ0c3 hlam
        linarith [this]
      have k3 : 2 * (c3 * lam) ≤ c3 * (s : ℝ) * lam := by
        have := mul_le_mul_of_nonneg_right hsR (by positivity : (0 : ℝ) ≤ c3 * lam)
        linarith
      linarith
    · rw [div_le_one hlogM]
      exact Real.log_le_log hqpos h1
  · exact ⟨min_le_right _ _, le_rfl⟩
  · -- `M^(s-1) < q < M^s`: `τ = s - log q / log M`
    push Not at h1 h2
    have hlogMs1 : Real.log ((M : ℝ) ^ (s - 1)) = ((s : ℝ) - 1) * Real.log (M : ℝ) := by
      rw [Real.log_pow]; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; ring
    have hgt : ((s : ℝ) - 1) * Real.log (M : ℝ) < Real.log (q : ℝ) := by
      rw [← hlogMs1]
      exact Real.log_lt_log (by positivity) h2
    refine ⟨?_, ?_⟩
    · have key : Real.log (q : ℝ) ≤ ((s : ℝ) - τ0) * Real.log (M : ℝ) := by
        have hsτ : 0 ≤ (s : ℝ) - τ0 := by linarith [min_le_right (min (c3 / A) (d / A)) 1]
        have k1 : ((s : ℝ) - τ0) * (A * lam - 2 * Real.log 2) ≤
            ((s : ℝ) - τ0) * Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hlogMlo hsτ
        have k2 : τ0 * A * lam ≤ d * lam := mul_le_mul_of_nonneg_right hτ0d hlam
        have k3 : ((s : ℝ) - 1) * (6 * Real.log 2) ≤ ((s : ℝ) - 1) * (d * lam) :=
          mul_le_mul_of_nonneg_left hdl (by linarith)
        have e1 : ((s : ℝ) - τ0) * (A * lam - 2 * Real.log 2) =
            (s : ℝ) * (c2 * lam) + (s : ℝ) * (d * lam) - 2 * (s : ℝ) * Real.log 2
              - τ0 * A * lam + 2 * τ0 * Real.log 2 := by
          rw [hddef]; ring
        have k4 : 0 ≤ τ0 * Real.log 2 := by positivity
        have k5 : 2 * Real.log 2 ≤ (s : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hsR hL2.le
        linarith
      have : Real.log (q : ℝ) / Real.log (M : ℝ) ≤ (s : ℝ) - τ0 := by
        rw [div_le_iff₀ hlogM]; exact key
      linarith
    · have : (s : ℝ) - 1 < Real.log (q : ℝ) / Real.log (M : ℝ) := by
        rw [lt_div_iff₀ hlogM]; exact hgt
      linarith

/-- PROVED. Karacuba p. 248, "recalling that `n < n0`": the bound of Lemma 2, p. 243-244,
`(8n)^(0.5 n l) m^(2ρ/τ) P^(1-ρ)` with `m = 1`, `l = log (12 n (n+1)/τ)` and
`ρ = τ/(3 n² l)`, is at most `K M^(1 - ρ0)` with `K` and `ρ0 ∈ (0, 1)` depending on `τ0` and
`n0` only, uniformly over `2 ≤ n < n0` and `τ0 ≤ τ ≤ 1`, for every `M ≥ 1`: `l` is at most
`log (12 n0 (n0+1)/τ0)` and `ρ` at least `τ0/(3 n0² log (12 n0 (n0+1)/τ0))`. -/
theorem lemma2_constants_r1122 :
    ∀ τ0 n0 : ℝ, 0 < τ0 → τ0 ≤ 1 →
      ∃ K ρ : ℝ, 0 < K ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ (n : ℕ) (τ M : ℝ), 2 ≤ n → (n : ℝ) < n0 → τ0 ≤ τ → τ ≤ 1 → 1 ≤ M →
          (8 * (n : ℝ)) ^ (0.5 * (n : ℝ) * Real.log (12 * (n : ℝ) * ((n : ℝ) + 1) / τ)) *
              M ^ (1 - τ / (3 * (n : ℝ) ^ 2 * Real.log (12 * (n : ℝ) * ((n : ℝ) + 1) / τ)))
            ≤ K * M ^ (1 - ρ) := by
  intro τ0 n0 hτ0 hτ01
  set N0 : ℝ := max n0 2 with hN0def
  have hN02 : (2 : ℝ) ≤ N0 := le_max_right _ _
  set l0 := Real.log (12 * N0 * (N0 + 1) / τ0) with hl0def
  have hbig0 : (1 : ℝ) < 12 * N0 * (N0 + 1) / τ0 := by
    rw [lt_div_iff₀ hτ0]
    nlinarith
  have hl0 : 0 < l0 := Real.log_pos hbig0
  set ρ0 := min (τ0 / (3 * N0 ^ 2 * l0)) (1 / 2) with hρ0def
  have hρ0pos : 0 < ρ0 := lt_min (by positivity) (by norm_num)
  have hρ0le : ρ0 ≤ τ0 / (3 * N0 ^ 2 * l0) := min_le_left _ _
  have hρ0half : ρ0 ≤ 1 / 2 := min_le_right _ _
  refine ⟨(8 * N0) ^ (0.5 * N0 * l0), ρ0, by positivity, hρ0pos, by linarith, ?_⟩
  intro n τ M hn hnn0 hτ0τ hτ1 hM
  have hτ : 0 < τ := lt_of_lt_of_le hτ0 hτ0τ
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnN0 : (n : ℝ) ≤ N0 := le_trans hnn0.le (le_max_left _ _)
  have hx : (1 : ℝ) < 12 * (n : ℝ) * ((n : ℝ) + 1) / τ := by
    rw [lt_div_iff₀ hτ]
    nlinarith
  have hl : 0 < Real.log (12 * (n : ℝ) * ((n : ℝ) + 1) / τ) := Real.log_pos hx
  have hxle : 12 * (n : ℝ) * ((n : ℝ) + 1) / τ ≤ 12 * N0 * (N0 + 1) / τ0 := by
    have h1 : 12 * (n : ℝ) * ((n : ℝ) + 1) ≤ 12 * N0 * (N0 + 1) := by nlinarith
    calc 12 * (n : ℝ) * ((n : ℝ) + 1) / τ ≤ 12 * (n : ℝ) * ((n : ℝ) + 1) / τ0 :=
          div_le_div_of_nonneg_left (by positivity) hτ0 hτ0τ
      _ ≤ 12 * N0 * (N0 + 1) / τ0 := div_le_div_of_nonneg_right h1 hτ0.le
  have hll0 : Real.log (12 * (n : ℝ) * ((n : ℝ) + 1) / τ) ≤ l0 :=
    Real.log_le_log (by linarith) hxle
  set l := Real.log (12 * (n : ℝ) * ((n : ℝ) + 1) / τ) with hldef
  -- the constant
  have hexp : 0.5 * (n : ℝ) * l ≤ 0.5 * N0 * l0 := by
    have := mul_le_mul hnN0 hll0 hl.le (by linarith)
    nlinarith
  have hK1 : (8 * (n : ℝ)) ^ (0.5 * (n : ℝ) * l) ≤ (8 * N0) ^ (0.5 * N0 * l0) :=
    calc (8 * (n : ℝ)) ^ (0.5 * (n : ℝ) * l) ≤ (8 * (n : ℝ)) ^ (0.5 * N0 * l0) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
      _ ≤ (8 * N0) ^ (0.5 * N0 * l0) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  -- the saving
  have hden : 3 * (n : ℝ) ^ 2 * l ≤ 3 * N0 ^ 2 * l0 := by
    have h1 : (n : ℝ) ^ 2 ≤ N0 ^ 2 := by nlinarith
    have := mul_le_mul h1 hll0 hl.le (by positivity)
    nlinarith
  have hρle : ρ0 ≤ τ / (3 * (n : ℝ) ^ 2 * l) :=
    le_trans hρ0le (div_le_div₀ hτ.le hτ0τ (by positivity) hden)
  have hM2 : M ^ (1 - τ / (3 * (n : ℝ) ^ 2 * l)) ≤ M ^ (1 - ρ0) :=
    Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  exact mul_le_mul hK1 hM2 (by positivity) (by positivity)

/-- PROVED from `KarLemma2` and the three pieces above. Karacuba p. 248, the application of
Lemma 2 to the last trigonometric sum `Σ_y e(B_1 y + ... + B_n y^n)` at one `s ∈ T`. The block
length is `M` with `P^(c1 - c4/2)/4 ≤ M ≤ P^(c1 - c4/2)`: the LOWER bound is what makes
`Q_s ≤ P^(c2 s) < M^s` hold. Stated for an arbitrary coefficient sequence `B` with one index
`2 ≤ s ≤ n` satisfying hypothesis b) of p. 244 at that index; `ρ`, `K` and `P0` depend on
`c0, ..., c4` only, uniformly over `2 ≤ n < n0`. Lemma 2 is used with its `n` equal to ours,
its top coefficient `α_{n+1} = 0`, `m = 1`, `P := M` and `r := s`. -/
theorem lemma2_block_core_r1122 (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ ρ K P0 : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < K ∧ 1 ≤ P0 ∧
        ∀ P n : ℕ, 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 → P0 ≤ (P : ℝ) →
          ∀ (B : ℕ → ℝ) (s : ℕ), 2 ≤ s → s ≤ n →
            (P : ℝ) ^ (-(c2 * s)) ≤ |B s| → |B s| ≤ (P : ℝ) ^ (-(c3 * s)) →
            ∀ M : ℕ, (P : ℝ) ^ (c1 - c4 / 2) / 4 ≤ (M : ℝ) →
              (M : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) →
              ‖∑ y ∈ Finset.Icc 1 M, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j)‖ ≤
                K * (M : ℝ) ^ (1 - ρ) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨P0d, hP0d, hdir⟩ := dirichlet_coefficient_r1122 c2 c3 hc2 hc3
  obtain ⟨τ0, P0t, hτ0, hτ01, hP0t, htau⟩ :=
    tau_range_r1122 c1 c2 c3 c4 hc1 hc2 hc3 hc4 hc11 h241
  obtain ⟨K, ρ, hK, hρ, hρ1, hconst⟩ := lemma2_constants_r1122 τ0 (karN0 c1 c2 c4) hτ0 hτ01
  refine ⟨ρ, K, max P0d P0t, hρ, hρ1, hK, le_trans hP0d (le_max_left _ _), ?_⟩
  intro P n hn hn0 hP B s hs2 hsn hlow hupp M hM4 hMA
  obtain ⟨a, q, θ, hgcd, hq1, hqup, hqlow, hθ, hα⟩ :=
    hdir P (le_trans (le_max_left _ _) hP) s (by omega) (B s) hlow hupp
  obtain ⟨hqM, hτlo, hτhi⟩ :=
    htau P n s M q hs2 hsn hn0 (le_trans (le_max_right _ _) hP) hM4 hMA hqlow hqup
  have hq1r : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exfalso
      rw [h, Nat.cast_zero, zero_pow (by omega)] at hqM
      linarith
    · exact h
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
  set α : ℕ → ℝ := fun j => if j ≤ n then B j else 0 with hαdef
  have hαs : α s = (a : ℝ) / (q : ℝ) + θ / (q : ℝ) ^ 2 := by
    simp only [hαdef, if_pos hsn]
    exact hα
  have hL2 : ‖∑ x ∈ Finset.Icc 1 M,
        eC (((1 : ℕ) : ℝ) * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j)‖ <
      (8 * n : ℝ) ^ (0.5 * n * Real.log (12 * n * (n + 1) / karTau (M : ℝ) (q : ℝ) s)) *
        ((1 : ℕ) : ℝ) ^ (2 * (karTau (M : ℝ) (q : ℝ) s /
          (3 * (n : ℝ) ^ 2 * Real.log (12 * n * (n + 1) / karTau (M : ℝ) (q : ℝ) s))) /
          karTau (M : ℝ) (q : ℝ) s) *
        (M : ℝ) ^ (1 - karTau (M : ℝ) (q : ℝ) s /
          (3 * (n : ℝ) ^ 2 * Real.log (12 * n * (n + 1) / karTau (M : ℝ) (q : ℝ) s))) :=
    h2 n 1 M (by omega) one_pos hMpos α s hs2 (by omega) a q θ hgcd hq1 hqM hθ hαs
  have hsum : ∑ x ∈ Finset.Icc 1 M,
        eC (((1 : ℕ) : ℝ) * ∑ j ∈ Finset.Icc 1 (n + 1), α j * (x : ℝ) ^ j) =
      ∑ y ∈ Finset.Icc 1 M, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    rw [Nat.cast_one, one_mul, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have htop : α (n + 1) = 0 := by
      simp only [hαdef]
      rw [if_neg (by omega)]
    rw [htop, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn : j ≤ n := (Finset.mem_Icc.1 hj).2
    simp only [hαdef, if_pos hjn]
  rw [hsum, Nat.cast_one, Real.one_rpow, mul_one] at hL2
  have hc := hconst n (karTau (M : ℝ) (q : ℝ) s) (M : ℝ) hn hn0 hτlo hτhi hM1
  exact le_trans hL2.le hc

/-! ### The block estimate at the one fixed length -/

/-- PROVED from `lemma2_block_core_r1122` and `taylor_expand_r1122`. The corrected form
of `leaf_polynomial_block_sum`: the same polynomial block sum, but only for the one fixed block
length `L = ⌊P^(c1 - c4/2)⌋₊` of p. 248 and `P` past a threshold. The `y = 0` term and the
unimodular factor `e(B_0)` are split off, and Lemma 2 runs over `y ∈ [1, L - 1]`. -/
theorem fixed_polynomial_block_sum_r1122 (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ ρ K P0 : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ≤ 3 * c4 / (4 * c1) ∧ 0 < K ∧ 1 ≤ P0 ∧
        ∀ N P n : ℕ, 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 → P0 ≤ (P : ℝ) →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a : ℕ, N ≤ a → a + ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ ≤ N + P →
              ‖∑ y ∈ Finset.range ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊,
                eC (taylorWithinEval f n
                  (Set.Icc (a : ℝ) ((a : ℝ) + (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ))) (a : ℝ)
                  ((a : ℝ) + (y : ℝ)))‖ ≤
                K * (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ) ^ (1 - ρ) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨ρ, K, P0, hρ, hρ1, hK, hP0, hcore⟩ :=
    lemma2_block_core_r1122 h2 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  set A := c1 - c4 / 2 with hAdef
  have hA : 0 < A := by linarith
  set ρ' := min ρ (3 * c4 / (4 * c1)) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min hρ (by positivity)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  refine ⟨ρ', K + 1, max P0 ((4 : ℝ) ^ (1 / A)), hρ'pos, lt_of_le_of_lt hρ'ρ hρ1,
    min_le_right _ _, by linarith, le_trans hP0 (le_max_left _ _), ?_⟩
  intro N P n hn hn0 hPbig f T hH a ha haL
  have hP0P : P0 ≤ (P : ℝ) := le_trans (le_max_left _ _) hPbig
  have hP4 : (4 : ℝ) ^ (1 / A) ≤ (P : ℝ) := le_trans (le_max_right _ _) hPbig
  have hPpos : (0 : ℝ) < P := by linarith
  -- `P^A ≥ 4`
  have hPA4 : (4 : ℝ) ≤ (P : ℝ) ^ A := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / A)) ^ A := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hA.ne', Real.rpow_one]
      _ ≤ (P : ℝ) ^ A := Real.rpow_le_rpow (by positivity) hP4 hA.le
  set L := ⌊(P : ℝ) ^ A⌋₊ with hLdef
  have hLA : (L : ℝ) ≤ (P : ℝ) ^ A := Nat.floor_le (by positivity)
  have hLgt : (P : ℝ) ^ A - 1 < (L : ℝ) := Nat.sub_one_lt_floor _
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  -- the coefficient index
  have hsub := hH.2.2.1
  have hcard := hH.2.2.2.1
  have hbds := hH.2.2.2.2
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hTne : T.Nonempty := by
    have h1 : (0 : ℝ) < (T.card : ℝ) := lt_of_lt_of_le (mul_pos hc0 hn0') hcard
    exact Finset.card_pos.mp (by exact_mod_cast h1)
  obtain ⟨s, hsT⟩ := hTne
  have hs2n := Finset.mem_Icc.mp (hsub hsT)
  have haR : (N : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have haP : (a : ℝ) ≤ (N : ℝ) + (P : ℝ) := by
    have : a ≤ N + P := by omega
    exact_mod_cast this
  obtain ⟨hlow, hupp⟩ := hbds s hsT (a : ℝ) ⟨haR, haP⟩
  set B : ℕ → ℝ := fun j => iteratedDeriv j f a / (j.factorial : ℝ) with hBdef
  -- Lemma 2 on `[1, L - 1]`
  set M := L - 1 with hMdef
  have hML : (M : ℝ) = (L : ℝ) - 1 := by
    rw [hMdef]; push_cast [Nat.cast_sub hL1]; ring
  have hM4 : (P : ℝ) ^ A / 4 ≤ (M : ℝ) := by rw [hML]; linarith
  have hMA : (M : ℝ) ≤ (P : ℝ) ^ A := by rw [hML]; linarith
  have hcoreB := hcore P n hn hn0 hP0P B s hs2n.1 hs2n.2 hlow hupp M hM4 hMA
  -- rewrite the Taylor polynomial
  have hexp : ∀ y : ℕ, taylorWithinEval f n (Set.Icc (a : ℝ) ((a : ℝ) + (L : ℝ))) (a : ℝ)
      ((a : ℝ) + (y : ℝ)) = B 0 + ∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j := by
    intro y
    rw [taylor_expand_r1122 hH ha haL hL1 (y : ℝ), sum_range_succ_eq_zero_add_Icc_r1122]
    simp only [hBdef, pow_zero, mul_one]
  have hsum : ∑ y ∈ Finset.range L, eC (taylorWithinEval f n
      (Set.Icc (a : ℝ) ((a : ℝ) + (L : ℝ))) (a : ℝ) ((a : ℝ) + (y : ℝ))) =
      eC (B 0) * ∑ y ∈ Finset.range L, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hexp y, eC_add_r1122]
  have hL' : L = M + 1 := by omega
  have hsplit : ∑ y ∈ Finset.range L, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j) =
      1 + ∑ y ∈ Finset.Icc 1 M, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j) := by
    rw [hL', sum_range_succ_eq_zero_add_Icc_r1122]
    congr 1
    rw [show ∑ j ∈ Finset.Icc 1 n, B j * (((0 : ℕ) : ℝ)) ^ j = 0 from
      Finset.sum_eq_zero (fun j hj => by
        have : j ≠ 0 := by have := (Finset.mem_Icc.1 hj).1; omega
        simp [this])]
    exact eC_zero_r1122
  rw [hsum, norm_mul, norm_eC, one_mul, hsplit]
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hρ'1 : 0 ≤ 1 - ρ' := by linarith [lt_of_le_of_lt hρ'ρ hρ1]
  have hMpow : (M : ℝ) ^ (1 - ρ) ≤ (L : ℝ) ^ (1 - ρ') :=
    calc (M : ℝ) ^ (1 - ρ) ≤ (M : ℝ) ^ (1 - ρ') :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ ≤ (L : ℝ) ^ (1 - ρ') :=
          Real.rpow_le_rpow (by linarith) (by rw [hML]; linarith) hρ'1
  have hone : (1 : ℝ) ≤ (L : ℝ) ^ (1 - ρ') := Real.one_le_rpow hL1r hρ'1
  calc ‖1 + ∑ y ∈ Finset.Icc 1 M, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j)‖
      ≤ ‖(1 : ℂ)‖ + ‖∑ y ∈ Finset.Icc 1 M, eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j)‖ :=
        norm_add_le _ _
    _ ≤ 1 + K * (M : ℝ) ^ (1 - ρ) := by rw [norm_one]; linarith
    _ ≤ (K + 1) * (L : ℝ) ^ (1 - ρ') := by
        have := mul_le_mul_of_nonneg_left hMpow hK.le
        nlinarith

/-- PROVED from `fixed_polynomial_block_sum_r1122` and the PROVED theorems
`leaf_taylor_block_reduction` and `leaf_block_threshold`. Karacuba p. 248,
`T(x) = Σ_y e(B_0 + B_1 y + ... + B_n y^n) + 4πθ_1 (P2 + 1) P^(-γ2/n²)` and its estimate by
Lemma 2: one block `[a, a + L)` of the one fixed length `L = ⌊P^(c1 - c4/2)⌋₊` inside
`[N, N + P]` has sum at most `K L^(1-ρ)`, for `P` past a threshold. This is the corrected form
of the refuted `leaf_small_block_sum_bound`: it does not claim anything for shorter blocks. -/
theorem fixed_block_bound_r1122 (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ K ρ P0 : ℝ, 0 < K ∧ 0 < ρ ∧ ρ < 1 ∧ 1 ≤ P0 ∧
        ∀ N P n : ℕ, 2 ≤ n → (n : ℝ) < karN0 c1 c2 c4 → P0 ≤ (P : ℝ) →
          ∀ (f : ℝ → ℝ) (T : Finset ℕ), KarHyp c0 c1 c2 c3 N P n f T →
            ∀ a : ℕ, N ≤ a → a + ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ ≤ N + P →
              ‖∑ x ∈ Finset.Ico a (a + ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊), eC (f x)‖ ≤
                K * (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ) ^ (1 - ρ) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨ρ, K, P0, hρ, hρ1, hρc, hK, hP0, hpoly⟩ :=
    fixed_polynomial_block_sum_r1122 h2 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨Pt, hPt, hthr⟩ := leaf_block_threshold c1 c2 c4 ρ hc1 hc4 hρ hρc
  refine ⟨K + 1 / 2, ρ, max (max P0 Pt) 2, by linarith, hρ, hρ1,
    le_trans hP0 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro N P n hn hn0 hPbig f T hH a ha haL
  have hP0P : P0 ≤ (P : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hPbig
  have hPtP : Pt ≤ (P : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hPbig
  have hP2 : (2 : ℝ) ≤ P := le_trans (le_max_right _ _) hPbig
  have hP1 : 1 < P := by exact_mod_cast (by linarith : (1 : ℝ) < P)
  have hPA1 : (1 : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hL1 : 1 ≤ ⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ := Nat.le_floor (by exact_mod_cast hPA1)
  have hLA : (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ) ≤ (P : ℝ) ^ (c1 - c4 / 2) :=
    Nat.floor_le (by positivity)
  have hred := leaf_taylor_block_reduction hH hP1 hρ ha haL hL1 hLA (hthr n hn hn0 P hPtP)
  have hp := hpoly N P n hn hn0 hP0P f T hH a ha haL
  have e : (K + 1 / 2) * (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ) ^ (1 - ρ) =
      K * (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ) ^ (1 - ρ) +
        1 / 2 * (⌊(P : ℝ) ^ (c1 - c4 / 2)⌋₊ : ℝ) ^ (1 - ρ) := by ring
  rw [e]
  linarith

/-! ### Assembly -/

/-- PROVED from `fixed_block_bound_r1122` and the PROVED theorems `leaf_small_bookkeeping`
and `leaf_block_length_ge`. The sealed statement `leaf_small_case` of `KaracubaSplit`, the case
`2 ≤ n < n0` of Theorem 1, Karacuba p. 248, with exactly its type. The sum over
`[N, N + P₁)` is cut into blocks of the one length `L = ⌊P^(c1 - c4/2)⌋₊`, each bounded by
`K L^(1-ρ)`, and the last partial block costs at most `L ≤ P^(1-γ/n²)`; the count
`(P/L + 1) L^(1-ρ) ≤ P^(1-γ/n²)` is `leaf_small_bookkeeping`. -/
theorem leaf_small_case_repaired (h2 : KarLemma2) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      KarCase c0 c1 c2 c3 (fun n => (n : ℝ) < karN0 c1 c2 c4) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  obtain ⟨K, ρ, P0, hK, hρ, hρ1, hP0, hblk⟩ :=
    fixed_block_bound_r1122 h2 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 h241
  set A := c1 - c4 / 2 with hAdef
  have hA : 0 < A := by linarith
  have hA1 : A < 1 := by linarith
  set M := min (A * ρ) (1 - A) with hMdef
  have hM : 0 < M := lt_min (mul_pos hA hρ) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlP0 : 0 ≤ Real.log P0 := Real.log_nonneg hP0
  have hla : 0 < Real.log 2 / A := div_pos hl2 hA
  have hlb : 0 < 8 * (Real.log 2 / A) / M := by positivity
  set cc := 8 * (Real.log 2 / A) / M + Real.log 2 / A + Real.log P0 with hccdef
  have hcc : 0 < cc := by linarith
  refine ⟨K + 1, M / 2, cc, by linarith, by linarith, hcc, ?_⟩
  intro N P n hP hn hpred hbig f T hH P₁ hP₁ hP₁P
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1r : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hexp_le : ∀ t : ℝ, t ≤ cc → Real.exp t ≤ (P : ℝ) := by
    intro t htc
    refine le_trans (Real.exp_le_exp.2 ?_) hbig
    nlinarith [mul_nonneg hcc.le (sub_nonneg.2 hn1)]
  have hb1 : Real.exp (8 * (Real.log 2 / A) / M * (n : ℝ) ^ 2) ≤ (P : ℝ) := by
    refine le_trans (Real.exp_le_exp.2 ?_) hbig
    have : 8 * (Real.log 2 / A) / M ≤ cc := by linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hb2 : Real.exp (Real.log 2 / A) ≤ (P : ℝ) := hexp_le _ (by linarith)
  have hb3 : P0 ≤ (P : ℝ) := by
    have := hexp_le (Real.log P0) (by linarith)
    rwa [Real.exp_log (by linarith)] at this
  have hlogP : Real.log 2 / A ≤ Real.log P := by
    have h := Real.log_le_log (Real.exp_pos _) hb2
    rwa [Real.log_exp] at h
  have hPA2 : (2 : ℝ) ≤ (P : ℝ) ^ A := by
    rw [Real.rpow_def_of_pos hPr]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log P * A) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hlogP hA.le
          rwa [div_mul_cancel₀ _ hA.ne'] at this
  set L := ⌊(P : ℝ) ^ A⌋₊ with hLdef
  have hLA : (L : ℝ) ≤ (P : ℝ) ^ A := Nat.floor_le (by positivity)
  have hLA2 : (P : ℝ) ^ A / 2 ≤ (L : ℝ) := leaf_block_length_ge A hA hA1.le P hb2
  have hL1r : (1 : ℝ) ≤ (L : ℝ) := by linarith
  have hL1 : 1 ≤ L := by exact_mod_cast hL1r
  have hLpos : 0 < L := hL1
  have hblk' : ∀ a : ℕ, N ≤ a → a + L ≤ N + P →
      ‖∑ x ∈ Finset.Ico a (a + L), eC (f x)‖ ≤ K * (L : ℝ) ^ (1 - ρ) :=
    fun a ha haL => hblk N P n hn hpred hb3 f T hH a ha haL
  have hLpow0 : 0 ≤ (L : ℝ) ^ (1 - ρ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpart := fixed_block_partition_r1122 (fun x => eC (f x)) (fun x => (norm_eC _).le)
    (K * (L : ℝ) ^ (1 - ρ)) (mul_nonneg hK.le hLpow0) L hLpos N (N + P) hblk' P₁ N le_rfl
    (by omega)
  have hbook := leaf_small_bookkeeping A ρ (M / 2) hA hA1 hρ hρ1.le (by linarith) le_rfl
    n P L hn hP hb1 hLA hLA2 hL1
  have hγn : (M / 2) / (n : ℝ) ^ 2 ≤ M / 2 := div_le_self (by linarith) hn1
  have hMA : M ≤ 1 - A := min_le_right _ _
  have hLP : (L : ℝ) ≤ (P : ℝ) ^ (1 - (M / 2) / (n : ℝ) ^ 2) :=
    hLA.trans (Real.rpow_le_rpow_of_exponent_le hP1r (by linarith))
  have hq : (P₁ : ℝ) / L ≤ (P : ℝ) / L + 1 := by
    have : (P₁ : ℝ) / L ≤ (P : ℝ) / L :=
      div_le_div_of_nonneg_right (by exact_mod_cast hP₁P) (Nat.cast_nonneg _)
    linarith
  have h1 := mul_le_mul_of_nonneg_right hq (mul_nonneg hK.le hLpow0)
  have h2' := mul_le_mul_of_nonneg_left hbook hK.le
  have e1 : ((P : ℝ) / L + 1) * (K * (L : ℝ) ^ (1 - ρ)) =
      K * (((P : ℝ) / L + 1) * (L : ℝ) ^ (1 - ρ)) := by ring
  have e2 : (K + 1) * (P : ℝ) ^ (1 - (M / 2) / (n : ℝ) ^ 2) =
      K * (P : ℝ) ^ (1 - (M / 2) / (n : ℝ) ^ 2) + (P : ℝ) ^ (1 - (M / 2) / (n : ℝ) ^ 2) := by
    ring
  rw [e2]
  linarith

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
