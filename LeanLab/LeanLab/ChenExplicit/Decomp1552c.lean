/-
AI-written Lean code, Claude, 2026-10-26, run 20261026T1219Z-15327, unit U-1552, track T1, DECOMPOSE.
T. Yamada 2015, Explicit Chen's theorem, arXiv 1511.03409v2, Section 7, proof of Theorem 7.1.

Part c: the assemblies. With real proofs, CONDITIONAL ON the leaves of Decomp1552a.lean,
Decomp1552b.lean and this file, and on the Cited Theorem 3.1 application `thm31_upper_applied`:
* `lemma73_corr`: Lemma 7.3, (108), with `2.207` replaced by `2.207 + 5ε`, the form the
  corrected (109) to (116) give, see Decomp1552a;
* `remainder_le`: (124) to (126) summed, `≤ e^{-138} N/(ε log³ N)`;
* `thm71W_of_leaves`: Theorem 7.1 in the form `Thm71W` of Thm71Fix.lean, F-0028;
* `yamada_of_leaves`: Yamada's Theorem 1.1, CONDITIONAL ON these leaves and the remaining
  cited inputs `Thm48`, `Thm51`, `Thm61C C6corr`.
Chen's theorem is known; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.Decomp1552b
import LeanLab.ChenExplicit.Thm71Fix
import LeanLab.ChenExplicit.BJSCbar

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.D1552

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Yamada

/-- `c₂ = I₇₃ + 10⁻⁸`, by definition. -/
lemma c2_eq : c2 = I73 + 1 / 10 ^ 8 := rfl

/-- LEAF. Unit U-1552. Yamada 2015, Lemma 7.3, numerical lower bound: `0.3 ≤ c₂`; the value is
`c₂ ≈ 0.3630837`. -/
theorem c2_ge : (3 / 10 : ℝ) ≤ c2 := by
  have h : (3630 / 10000 : ℝ) < I73 := BJS.cbar_gt
  rw [c2_eq]
  linarith

/-- LEAF. Unit U-1552. Yamada 2015, (47), Section 4: for `N > exp exp 36` and `q₁` as in (46),
`U_N^(1) ≤ U_N (q₁-1)/(q₁-2) ≤ U_N (1 + ε₀(N))`. -/
theorem eq47 (N q₁ : ℕ) (hN : exp (exp 36) < N) (hq : Adm N q₁) :
    U1 N q₁ ≤ U N * (1 + eps0' N) := by
  have he0 : 0 ≤ eps0' N := by
    unfold eps0'
    exact div_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _))
  unfold U1
  apply mul_le_mul_of_nonneg_left _ (U_pos N).le
  split_ifs with h
  · rcases hq with hz | ⟨_, hq⟩
    · subst q₁; norm_num at h
    have hm : 0 < max 57 (log (log N)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hq2 : max 57 (log (log N)) ≤ (q₁ : ℝ) - 2 := by
      apply max_le
      · linarith [le_trans (le_max_left _ _) hq]
      · linarith [le_trans (le_max_right _ _) hq]
    have hqp : 0 < (q₁ : ℝ) - 2 := hm.trans_le hq2
    have hi := one_div_le_one_div_of_le hm hq2
    have he : ((q₁ : ℝ) - 1) / ((q₁ : ℝ) - 2) = 1 + 1 / ((q₁ : ℝ) - 2) := by
      field_simp
      ring
    rw [he]
    simpa only [eps0', add_comm] using add_le_add_left hi 1
  · linarith

/-- LEAF. Unit U-1552. Numerical step from (127) and Lemma 7.3 to (128), Section 7: for
`N > exp exp 36`, `D = N^{1/2}/log^{10} N`, `y = N^{1/3}`, `L = log N` and `0.3 ≤ c ≤ 1`,
`(c/L + 2.257/L²)(2e^γ/log D + 298.87013/log^{3/2} D + 1/(5 log² y))
≤ (c/L)(4e^γ/L + 845.33255/L^{3/2})`; at `c = 0.3` the margin is about `2.7·10⁻⁵ L^{-5/2}`.
The `2.257` is `2.207 + 5/100`, see `lemma73_corr`. -/
theorem eq128_num (N : ℕ) (hN : exp (exp 36) < N) (c : ℝ) (hc : 3 / 10 ≤ c) (hc1 : c ≤ 1) :
    (c / log N + 2257 / 1000 / log N ^ 2) *
        (2 * exp eulerMascheroniConstant / log (Dsv N) +
          29887013 / 100000 / (log (Dsv N) * √(log (Dsv N))) + 1 / (5 * log (y3 N) ^ 2)) ≤
      c / log N * (4 * exp eulerMascheroniConstant / log N +
        84533255 / 100000 / (log N * √(log N))) := by
  have hNp : (0 : ℝ) < N := (exp_pos _).trans hN
  have hL : exp 36 < log N := by simpa using log_lt_log (exp_pos _) hN
  set L := log (N : ℝ) with hLeq
  have hLp : 0 < L := (exp_pos _).trans hL
  have hlogD : log (Dsv N) = L / 2 - 10 * log L := by
    unfold Dsv
    rw [log_div (sqrt_pos_of_pos hNp).ne' (pow_pos hLp _).ne', log_sqrt hNp.le, log_pow]
    ring
  have hlogy : log (y3 N) = L / 3 := by rw [log_rpow hNp]; ring
  have hest : 1 / (L / 2 - 10 * log L) ≤ 2 / L + 3 / 100000 / (L * √L) ∧
      29887013 / 100000 / ((L / 2 - 10 * log L) * √(L / 2 - 10 * log L)) ≤
        8453324 / 10000 / (L * √L) := by
    clear * - L hL
    have hLp : 0 < L := (exp_pos _).trans hL
    have hsp : 0 < √L := sqrt_pos.mpr hLp
    have hsq : √L ^ 2 = L := sq_sqrt hLp.le
    have hs : 50000000 ≤ √L := by
      have he : √(exp (36 : ℝ)) = exp 18 := by
        apply (sq_eq_sq₀ (sqrt_nonneg _) (exp_pos _).le).mp
        rw [sq_sqrt (exp_pos _).le, ← exp_nat_mul]
        norm_num
      have h := sqrt_le_sqrt hL.le
      rw [he] at h
      have hexp := exp_18_gt
      norm_num at hexp
      linarith
    have hratio := Real.log_div_sqrt_antitoneOn
      (show exp (36 : ℝ) ∈ Set.Ici (exp 2) by simp only [Set.mem_Ici]; exact exp_le_exp.mpr (by norm_num))
      (show L ∈ Set.Ici (exp 2) by simp only [Set.mem_Ici]; exact (exp_le_exp.mpr (by norm_num : (2 : ℝ) ≤ 36)).trans hL.le) hL.le
    have he : √(exp (36 : ℝ)) = exp 18 := by
        apply (sq_eq_sq₀ (sqrt_nonneg _) (exp_pos _).le).mp
        rw [sq_sqrt (exp_pos _).le, ← exp_nat_mul]
        norm_num
    dsimp only at hratio
    rw [log_exp, he] at hratio
    have he18 : 36 / exp 18 ≤ 36 / 50000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by have h := exp_18_gt; norm_num at h; linarith)
    have hl : log L ≤ 36 / 50000000 * √L := (div_le_iff₀ hsp).mp (hratio.trans he18)
    have hls := mul_le_mul_of_nonneg_right hl hsp.le
    have hls' : log L * √L ≤ 36 / 50000000 * L := by nlinarith [hls]
    set d := L / 2 - 10 * log L with hd
    have hdlo : (4999999999 / 10000000000 : ℝ) * L ≤ d := by
      have hs' : 50000000 * √L ≤ L := by nlinarith
      nlinarith
    have hdp : 0 < d := by nlinarith
    constructor
    · apply (div_le_iff₀ hdp).mpr
      apply (mul_le_mul_iff_left₀ (show 0 < L * √L by positivity)).mp
      field_simp
      rw [hd]
      nlinarith [mul_nonneg (show 0 ≤ √L - 50000000 by linarith) hsp.le]
    · have hroot : (707106781 / 1000000000 : ℝ) * √L ≤ √d := by
        apply (le_sqrt (by positivity) hdp.le).mpr
        nlinarith
      have hprod : (3535533904 / 10000000000 : ℝ) * (L * √L) ≤ d * √d := by
        have hp := mul_le_mul hdlo hroot (by positivity : (0 : ℝ) ≤ 707106781 / 1000000000 * √L) hdp.le
        nlinarith
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
  have hg : exp eulerMascheroniConstant ≤ (2 : ℝ) := by
    apply (le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mp
    linarith [eulerMascheroniConstant_lt_two_thirds, log_two_gt_d9]
  have hnumeric (L s d g c : ℝ) (hs : 50000000 ≤ s) (hsq : s ^ 2 = L)
      (hg0 : 0 ≤ g) (hg : g ≤ 2) (hc : 3 / 10 ≤ c)
      (hdi : 1 / d ≤ 2 / L + 3 / 100000 / (L * s))
      (hdt : 29887013 / 100000 / (d * √d) ≤ 8453324 / 10000 / (L * s)) :
      (c / L + 2257 / 1000 / L ^ 2) *
        (2 * g / d + 29887013 / 100000 / (d * √d) + 9 / (5 * L ^ 2)) ≤
      c / L * (4 * g / L + 84533255 / 100000 / (L * s)) := by
    clear * - L s d g c hs hsq hg0 hg hc hdi hdt
    have hsp : 0 < s := by linarith
    have hLp : 0 < L := by nlinarith
    have hiy : 9 / (5 * L ^ 2) ≤ 1 / 1000000 / (L * s) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (show 0 ≤ s - 50000000 by linarith) (sq_nonneg s)]
    have hK : 2 * g / d + 29887013 / 100000 / (d * √d) + 9 / (5 * L ^ 2) ≤
        4 * g / L + 845332521 / 1000000 / (L * s) := by
      have hi := mul_le_mul_of_nonneg_left hdi (show 0 ≤ 2 * g by positivity)
      have hg' : 2 * g * (3 / 100000 / (L * s)) ≤ 12 / 100000 / (L * s) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have he : 2 * g * (1 / d) = 2 * g / d := by ring
      rw [he] at hi
      have he' : 2 * g * (2 / L + 3 / 100000 / (L * s)) =
          4 * g / L + 2 * g * (3 / 100000 / (L * s)) := by ring
      rw [he'] at hi
      have sumid : 8453324 / 10000 / (L * s) + 12 / 100000 / (L * s) +
          1 / 1000000 / (L * s) = 845332521 / 1000000 / (L * s) := by ring
      linarith
    have hfirst : 0 ≤ c / L + 2257 / 1000 / L ^ 2 := by positivity
    refine (mul_le_mul_of_nonneg_left hK hfirst).trans ?_
    set t := 1 / s with ht
    have htp : 0 < t := by rw [ht]; positivity
    have htmax : t ≤ 1 / 50000000 := by rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
    have hL : 1 / L = t ^ 2 := by rw [ht, ← hsq]; ring
    have hb : 4 * g + 845332521 / 1000000 * t ≤ 9 := by nlinarith
    have hex : 2257 / 1000 * t * (4 * g + 845332521 / 1000000 * t) ≤ c * (29 / 1000000) := by
      have hmul := mul_le_mul hb htmax htp.le (by norm_num : (0 : ℝ) ≤ 9)
      nlinarith
    have hex' := mul_le_mul_of_nonneg_right hex htp.le
    have hcore : (c + 2257 / 1000 * t ^ 2) * (4 * g + 845332521 / 1000000 * t) ≤
        c * (4 * g + 84533255 / 100000 * t) := by nlinarith [hex']
    have hfinal := mul_le_mul_of_nonneg_right hcore (show 0 ≤ (1 / L) ^ 2 by positivity)
    rw [ht] at hfinal
    subst L
    convert hfinal using 1 <;> field_simp <;> ring
  have hs : 50000000 ≤ √L := by
    have he : √(exp (36 : ℝ)) = exp 18 := by
      apply (sq_eq_sq₀ (sqrt_nonneg _) (exp_pos _).le).mp
      rw [sq_sqrt (exp_pos _).le, ← exp_nat_mul]
      norm_num
    have h := sqrt_le_sqrt hL.le
    rw [he] at h
    have hexp := exp_18_gt
    norm_num at hexp
    linarith
  rw [hlogD, hlogy]
  have hy : 1 / (5 * (L / 3) ^ 2) = 9 / (5 * L ^ 2) := by ring
  rw [hy]
  exact hnumeric L (√L) (L / 2 - 10 * log L) (exp eulerMascheroniConstant) c
    hs (sq_sqrt hLp.le) (exp_pos _).le hg hc hest.1 hest.2

/-- Real arithmetic for `lemma73_corr`. PROVED. -/
lemma key73 (I ε a E : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1 / 100) (hI : I ≤ 1)
    (hE0 : 0 ≤ E * a) (hEa : E * a ≤ 1 / 10 ^ 5) :
    (1 + ε + 1 / 10 ^ 8) * (I * a + (22069 / 10000 + 5 * ε) * a ^ 2 + E * a ^ 3) ≤
      (1 + ε) * ((I + 1 / 10 ^ 8) * a + (2207 / 1000 + 5 * ε) * a ^ 2) := by
  have h1 : 0 ≤ a * (1 + ε - I) := mul_nonneg ha.le (by linarith)
  have h3 : 0 ≤ ε * (1 / 10 ^ 4 - E * a) := mul_nonneg hε.le (by linarith)
  have h4 : 0 ≤ (1 + ε) * (1 / 10 ^ 4 - E * a) - 1 / 10 ^ 8 * (22069 / 10000 + 5 * ε + E * a) := by
    nlinarith
  have h2 : 0 ≤ a ^ 2 * ((1 + ε) * (1 / 10 ^ 4 - E * a) -
      1 / 10 ^ 8 * (22069 / 10000 + 5 * ε + E * a)) := mul_nonneg (sq_nonneg a) h4
  nlinarith [h1, h2]

/-- Lemma 7.3, (108), corrected: for even `N > exp exp 36` and `0 < ε < 1/100`,
`Σ_j |B^(j)| ≤ (1+ε) N (c₂/log N + (2.207 + 5ε)/log² N)`. PROVED, CONDITIONAL ON the leaves
`eq109_count`, `eq109_pi`, `eq112_main`, `eq112_tail`, `eq113`, `eq115`, `eq116_sum`,
`eq116_integral`, `Hz_eq`, and on `c2Bound`, which is PROVED in C2Bound.lean. -/
theorem lemma73_corr (N : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1 / 100) :
    (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) ≤
      (1 + ε) * N * (c2 / log N + (2207 / 1000 + 5 * ε) / log N ^ 2) := by
  have hN0 : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL36 : exp 36 < log N := by rw [lt_log_iff_exp_lt hN0]; exact hN
  have hLbig : (6 * 10 ^ 6 : ℝ) < log N := by
    have h9 : exp (9 : ℝ) * exp 9 * exp 9 * exp 9 = exp 36 := by
      rw [← exp_add, ← exp_add, ← exp_add]; norm_num
    have e9 : (1 + 9 + 81 / 2 : ℝ) ≤ exp 9 := by
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 by norm_num)
      norm_num at this; linarith
    have e36 : (50 * 50 * 50 * 50 : ℝ) ≤ exp 36 := by
      rw [← h9]
      have b1 := mul_le_mul e9 e9 (by norm_num) (exp_pos _).le
      have b2 := mul_le_mul b1 e9 (by norm_num) (by positivity)
      have b3 := mul_le_mul b2 e9 (by norm_num) (by positivity)
      nlinarith [b3]
    nlinarith [e36]
  have hLpos : 0 < log N := by linarith
  have hk0 : 0 ≤ 1 + ε + 1 / 10 ^ 8 := by linarith
  -- leaves of Lemma 7.3
  have hS1 := eq115 N hN
  have hsum := eq116_sum N hN
  have hz : log (z8 N) = log N / 8 := by rw [log_rpow hN0]; ring
  rw [eq116_integral N hN, Hz_eq N hN, hz] at hsum
  have hc2 := c2Bound
  unfold C2Bound at hc2
  rw [c2_eq] at hc2 ⊢
  have inner : ∀ p₁ ∈ primesIco (z8 N) (y3 N),
      ∑ p₂ ∈ primesIco (y3 N) (wP N ε p₁), 1 / ((p₂ : ℝ) * log (N / (p₁ * p₂))) ≤
        H N p₁ + 9 * (1 + exp (-50)) / (4 * log N ^ 2) + (5 * ε + 7 / log N) / log N ^ 2 := by
    intro p₁ hp₁
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : ℕ => (p : ℝ) < √(N / p₁))]
    have a := eq112_main N hN ε hε hε1 p₁ hp₁
    have b := eq113 N hN p₁ hp₁
    have c := eq112_tail N hN ε hε hε1 p₁ hp₁
    linarith
  have step : (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) ≤
      ∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 + ε + 1 / 10 ^ 8) * N * (1 / (p₁ : ℝ)) *
        (H N p₁ + 9 * (1 + exp (-50)) / (4 * log N ^ 2) + (5 * ε + 7 / log N) / log N ^ 2) := by
    refine (eq109_count N ε hε hε1).trans ?_
    refine Finset.sum_le_sum fun p₁ hp₁ => ?_
    calc ∑ p₂ ∈ primesIco (y3 N) (wP N ε p₁),
          (Nat.primeCounting ⌊(1 + ε) * N / (p₁ * p₂)⌋₊ : ℝ)
        ≤ ∑ p₂ ∈ primesIco (y3 N) (wP N ε p₁),
          (1 + ε + 1 / 10 ^ 8) * N * (1 / (p₁ : ℝ)) * (1 / ((p₂ : ℝ) * log (N / (p₁ * p₂)))) :=
          Finset.sum_le_sum fun p₂ hp₂ => eq109_pi N hN ε hε hε1 p₁ hp₁ p₂ hp₂
      _ = (1 + ε + 1 / 10 ^ 8) * N * (1 / (p₁ : ℝ)) *
          ∑ p₂ ∈ primesIco (y3 N) (wP N ε p₁), 1 / ((p₂ : ℝ) * log (N / (p₁ * p₂))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (inner p₁ hp₁)
          exact mul_nonneg (mul_nonneg hk0 hN0.le) (by positivity)
  have hsplit : ∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 + ε + 1 / 10 ^ 8) * N * (1 / (p₁ : ℝ)) *
        (H N p₁ + 9 * (1 + exp (-50)) / (4 * log N ^ 2) + (5 * ε + 7 / log N) / log N ^ 2) =
      (1 + ε + 1 / 10 ^ 8) * N * ((∑ p₁ ∈ primesIco (z8 N) (y3 N), H N p₁ / p₁) +
        (9 * (1 + exp (-50)) / (4 * log N ^ 2) + (5 * ε + 7 / log N) / log N ^ 2) *
          ∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 / (p₁ : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p₁ _ => ?_
    ring
  rw [hsplit] at step
  have hS1nn : 0 ≤ ∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 / (p₁ : ℝ)) :=
    Finset.sum_nonneg fun p _ => by positivity
  generalize (∑ p₁ ∈ primesIco (z8 N) (y3 N), H N p₁ / p₁) = SH at hsum step
  generalize (∑ p₁ ∈ primesIco (z8 N) (y3 N), (1 / (p₁ : ℝ))) = S1 at hS1 hS1nn step
  generalize (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) = A at step ⊢
  generalize I73 = I at hsum hc2 ⊢
  generalize log N = L at hsum step hLbig hLpos ⊢
  -- arithmetic with a = 1/L
  obtain ⟨a, hA⟩ : ∃ a : ℝ, a = 1 / L := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hA]; positivity
  have ha1 : a ≤ 1 / (6 * 10 ^ 6) := by
    rw [hA]; exact one_div_le_one_div_of_le (by norm_num) hLbig.le
  have hlg : log (13 / 8 : ℝ) ≤ 1 := by
    have := log_le_sub_one_of_pos (show (0 : ℝ) < 13 / 8 by norm_num); linarith
  have hlg0 : 0 ≤ log (13 / 8 : ℝ) := log_nonneg (by norm_num)
  have hS1le : S1 ≤ 1 := by
    have he : 0 ≤ exp (-50 : ℝ) := (exp_pos _).le
    nlinarith [hS1]
  have hSH : SH ≤ I * a + 128 / 7 * log (13 / 8) * a ^ 3 := by
    have e1 : I / L = I * a := by rw [hA]; ring
    have e2 : 8 / 7 * log (13 / 8) / L / (4 * (L / 8) ^ 2) = 128 / 7 * log (13 / 8) * a ^ 3 := by
      rw [hA]; field_simp <;> ring
    rw [e1, e2] at hsum; exact hsum
  have hT : 9 * (1 + exp (-50)) / (4 * L ^ 2) * S1 ≤ 22069 / 10000 * a ^ 2 := by
    have e : 9 * (1 + exp (-50)) / (4 * L ^ 2) * S1 = (9 * (1 + exp (-50)) / 4 * S1) * a ^ 2 := by
      rw [hA]; field_simp <;> ring
    rw [e]; exact mul_le_mul_of_nonneg_right hS1 (sq_nonneg a)
  have hX : (5 * ε + 7 / L) / L ^ 2 * S1 ≤ 5 * ε * a ^ 2 + 7 * a ^ 3 := by
    have e : (5 * ε + 7 / L) / L ^ 2 = 5 * ε * a ^ 2 + 7 * a ^ 3 := by rw [hA]; field_simp <;> ring
    rw [e]
    have : 0 ≤ 5 * ε * a ^ 2 + 7 * a ^ 3 := by positivity
    nlinarith
  have hP : SH + (9 * (1 + exp (-50)) / (4 * L ^ 2) + (5 * ε + 7 / L) / L ^ 2) * S1 ≤
      I * a + (22069 / 10000 + 5 * ε) * a ^ 2 + (7 + 128 / 7 * log (13 / 8)) * a ^ 3 := by
    have : (9 * (1 + exp (-50)) / (4 * L ^ 2) + (5 * ε + 7 / L) / L ^ 2) * S1 =
        9 * (1 + exp (-50)) / (4 * L ^ 2) * S1 + (5 * ε + 7 / L) / L ^ 2 * S1 := by ring
    rw [this]; nlinarith [hSH, hT, hX]
  have hIle : I ≤ 1 := by linarith
  set E' := 7 + 128 / 7 * log (13 / 8 : ℝ) with hE'
  have hE'a : E' * a ≤ 1 / 10 ^ 5 := by
    have : E' ≤ 26 := by rw [hE']; nlinarith
    have hE'0 : 0 ≤ E' := by rw [hE']; positivity
    calc E' * a ≤ 26 * (1 / (6 * 10 ^ 6)) := mul_le_mul this ha1 ha.le (by norm_num)
      _ ≤ 1 / 10 ^ 5 := by norm_num
  have hE'0 : 0 ≤ E' * a := by
    have : 0 ≤ E' := by rw [hE']; positivity
    positivity
  have key : (1 + ε + 1 / 10 ^ 8) *
      (I * a + (22069 / 10000 + 5 * ε) * a ^ 2 + E' * a ^ 3) ≤
      (1 + ε) * ((I + 1 / 10 ^ 8) * a + (2207 / 1000 + 5 * ε) * a ^ 2) := by
    exact key73 I ε a E' ha hε hε1 hIle hE'0 hE'a
  calc A ≤ _ := step
    _ ≤ (1 + ε + 1 / 10 ^ 8) * N *
        (I * a + (22069 / 10000 + 5 * ε) * a ^ 2 + E' * a ^ 3) :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hk0 hN0.le)
    _ = N * ((1 + ε + 1 / 10 ^ 8) *
        (I * a + (22069 / 10000 + 5 * ε) * a ^ 2 + E' * a ^ 3)) := by ring
    _ ≤ N * ((1 + ε) * ((I + 1 / 10 ^ 8) * a + (2207 / 1000 + 5 * ε) * a ^ 2)) :=
        mul_le_mul_of_nonneg_left key hN0.le
    _ = (1 + ε) * N * ((I + 1 / 10 ^ 8) / L + (2207 / 1000 + 5 * ε) / L ^ 2) := by
        rw [hA]; ring

/-- (124) to (126) together: for even `N > exp exp 36`, `0 < ε < 1/100`, `q₁` from `lemma72`,
`Σ_j Σ_{d<D, d ∣ P^(1)(y)} |r_d^(j)| ≤ e^{-138} N/(ε log³ N)`. PROVED, CONDITIONAL ON the
leaves `eq123`, `eq124`, `eq126`, `eq125_phi`, `eq125_num`. -/
theorem remainder_le (N q₁ : ℕ) (hE : Even N) (hN : exp (exp 36) < N) (hq : Adm N q₁)
    (h72 : ∀ (c : ℕ → ℝ) (res : ℕ → ℕ) (X Y Z : ℝ), (∀ n, |c n| ≤ 1) →
      (∀ d, 0 < d → Nat.Coprime (res d) d) → log Y ^ 10 < X → X ≤ N / z8 N →
      X * Y < 2 * N → z8 N < Y → z8 N ≤ Z → Lemma72At q₁ c res X Y Z)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∑ j ∈ range (Jblk N ε), ∑ d ∈ Dset N q₁, |rj N ε j d| ≤
      exp (-138) * N / (ε * log N ^ 3) := by
  have hN0 : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : 1 < log N := by
    rw [lt_log_iff_exp_lt hN0]
    exact lt_trans (exp_lt_exp.mpr (by linarith [add_one_le_exp (36 : ℝ)])) hN
  have hL3 : 0 < log N ^ 3 := by positivity
  have h1 : ∑ j ∈ range (Jblk N ε), ∑ d ∈ Dset N q₁, |rj N ε j d| ≤
      ∑ j ∈ range (Jblk N ε), ∑ d ∈ Dset N q₁, |r1 N ε j d| +
        ∑ d ∈ Dset N q₁, ∑ j ∈ range (Jblk N ε), |r2 N ε j d| := by
    rw [Finset.sum_comm (s := Dset N q₁), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun d _ => abs_r_le N ε j d
  have h2 : ∑ j ∈ range (Jblk N ε), ∑ d ∈ Dset N q₁, |r1 N ε j d| ≤
      6 / 5 * exp (-139) * N / (ε * log N ^ 3) :=
    (Finset.sum_le_sum fun j hj =>
      eq123 N q₁ hE hN hq h72 ε hε hε1 j (Finset.mem_range.mp hj)).trans (eq124 N hN ε hε hε1)
  have h3 : ∑ d ∈ Dset N q₁, ∑ j ∈ range (Jblk N ε), |r2 N ε j d| ≤
      8 * (N : ℝ) ^ ((7 : ℝ) / 8) * log N := by
    calc ∑ d ∈ Dset N q₁, ∑ j ∈ range (Jblk N ε), |r2 N ε j d|
        ≤ ∑ d ∈ Dset N q₁, 8 * (N : ℝ) ^ ((7 : ℝ) / 8) * (1 / (d.totient : ℝ)) :=
          Finset.sum_le_sum fun d hd => by
            have := eq126 N q₁ hE hN hq ε hε hε1 d hd
            rw [mul_one_div]; exact this
      _ = 8 * (N : ℝ) ^ ((7 : ℝ) / 8) * ∑ d ∈ Dset N q₁, 1 / (d.totient : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 8 * (N : ℝ) ^ ((7 : ℝ) / 8) * log N :=
          mul_le_mul_of_nonneg_left (eq125_phi N q₁ hN).le (by positivity)
  have h4 := eq125_num N hN
  have h5 : exp (-139) * N / log N ^ 3 ≤ exp (-139) * N / (ε * log N ^ 3) := by
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hε hL3)
    nlinarith
  have h6 : exp (-138 : ℝ) = exp 1 * exp (-139) := by rw [← exp_add]; norm_num
  have he : (27 / 10 : ℝ) < exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have h7 : 6 / 5 * exp (-139) * N / (ε * log N ^ 3) + exp (-139) * N / (ε * log N ^ 3) ≤
      exp (-138) * N / (ε * log N ^ 3) := by
    rw [← add_div, h6]
    apply div_le_div_of_nonneg_right _ (mul_pos hε hL3).le
    have : 0 ≤ exp (-139 : ℝ) * N := by positivity
    nlinarith
  linarith

/-- Yamada 2015, Theorem 7.1, in the form `Thm71W` that its proof gives, F-0028.
PROVED, CONDITIONAL ON the leaves of Decomp1552a, Decomp1552b and this file and on the Cited
`thm31_upper_applied`; `c2Bound` is PROVED in C2Bound.lean. -/
theorem thm71W_of_leaves : Thm71W := by
  intro N hE hN ε hε hε1
  obtain ⟨q₁, hq, h72⟩ := lemma72 N hE hN
  have hN0 : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  obtain ⟨hy, hD, hU1⟩ := logs_pos N q₁ hN
  have hL : 1 < log N := by
    rw [lt_log_iff_exp_lt hN0]
    exact lt_trans (exp_lt_exp.mpr (by linarith [add_one_le_exp (36 : ℝ)])) hN
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * exp eulerMascheroniConstant / log (Dsv N) +
      29887013 / 100000 / (log (Dsv N) * √(log (Dsv N))) + 1 / (5 * log (y3 N) ^ 2) :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ 2 * exp eulerMascheroniConstant / log (Dsv N) :=
      div_nonneg (by positivity) hD.le
    have h2 : 0 ≤ 29887013 / 100000 / (log (Dsv N) * √(log (Dsv N))) :=
      div_nonneg (by norm_num) (mul_nonneg hD.le (sqrt_nonneg _))
    have h3 : 0 ≤ 1 / (5 * log (y3 N) ^ 2) := by positivity
    linarith
  -- (107), (117), (118), summed: (127)
  have s1 : (SB N (zN N) (yN N) : ℝ) ≤ ∑ j ∈ range (Jblk N ε), (SBj N q₁ ε j : ℝ) := by
    have := (eq107_sub N q₁ ε hε hε1).trans (sum_sifted_le N q₁ ε)
    exact_mod_cast this
  have s2 : ∑ j ∈ range (Jblk N ε), (SBj N q₁ ε j : ℝ) ≤
      ∑ j ∈ range (Jblk N ε), (((Bj N ε j).card : ℝ) * (U1 N q₁ * K) +
        ∑ d ∈ Dset N q₁, |rj N ε j d|) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have t := thm31_upper_applied N q₁ hE hN hq ε hε hε1 j (Finset.mem_range.mp hj)
    have m := eq118 N q₁ hE hN hq
    rw [← hK] at m
    have : ((Bj N ε j).card : ℝ) * (V1 N q₁ (y3 N) + U1 N q₁ *
        (F1lin (log (Dsv N) / log (y3 N)) / log (Dsv N) +
          29887013 / 100000 / (log (Dsv N) * √(log (Dsv N))))) ≤
        ((Bj N ε j).card : ℝ) * (U1 N q₁ * K) :=
      mul_le_mul_of_nonneg_left m (by positivity)
    linarith
  have s3 : ∑ j ∈ range (Jblk N ε), (((Bj N ε j).card : ℝ) * (U1 N q₁ * K) +
        ∑ d ∈ Dset N q₁, |rj N ε j d|) =
      (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) * (U1 N q₁ * K) +
        ∑ j ∈ range (Jblk N ε), ∑ d ∈ Dset N q₁, |rj N ε j d| := by
    rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hR := remainder_le N q₁ hE hN hq h72 ε hε hε1
  have h73 := lemma73_corr N hE hN ε hε hε1
  have hc2lo := c2_ge
  have hc2hi := c2Bound
  unfold C2Bound at hc2hi
  have h128 := eq128_num N hN c2 hc2lo (by linarith)
  rw [← hK] at h128
  have h47 := eq47 N q₁ hN hq
  have he0 : eps0' N ≤ 1 / 57 := by
    unfold eps0'
    exact one_div_le_one_div_of_le (by norm_num) (le_max_left _ _)
  have he0' : 0 ≤ eps0' N := by
    unfold eps0'
    exact div_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _))
  have hU : 0 < U N := U_pos N
  have hg : 0 < exp eulerMascheroniConstant := exp_pos _
  have heq : eps0 N = eps0' N := rfl
  rw [heq]
  have hsq : 0 < √(log N) := sqrt_pos.mpr (by linarith)
  -- clean atoms
  generalize (SB N (zN N) (yN N) : ℝ) = S at s1 ⊢
  generalize (∑ j ∈ range (Jblk N ε), ((Bj N ε j).card : ℝ)) = A at s3 h73
  generalize (∑ j ∈ range (Jblk N ε), ∑ d ∈ Dset N q₁, |rj N ε j d|) = R at s3 hR
  generalize U1 N q₁ = u at s2 s3 hU1 h47
  generalize U N = V at h47 hU ⊢
  generalize eps0' N = e0 at h47 he0 he0' ⊢
  generalize exp eulerMascheroniConstant = g at h128 hg ⊢
  generalize log N = L at h73 h128 hR hL hsq ⊢
  have hS : S ≤ A * (u * K) + R := by linarith
  have hc0 : 0 < c2 := by linarith
  have hLp : 0 < L := by linarith
  have hε0 : 0 ≤ 1 + ε := by linarith
  have hB : A ≤ (1 + ε) * N * (c2 / L + 2257 / 1000 / L ^ 2) := by
    refine h73.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hε0 hN0.le))
    have : (2207 / 1000 + 5 * ε) / L ^ 2 ≤ 2257 / 1000 / L ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hM0 : 0 ≤ c2 / L * (4 * g / L + 84533255 / 100000 / (L * √L)) := by
    have : 0 ≤ 4 * g / L + 84533255 / 100000 / (L * √L) :=
      add_nonneg (div_nonneg (by linarith) hLp.le)
        (div_nonneg (by norm_num) (mul_nonneg hLp.le hsq.le))
    exact mul_nonneg (div_nonneg hc0.le hLp.le) this
  have hmain : A * (u * K) ≤
      (1 + ε) * N * (V * (1 + e0)) * (c2 / L * (4 * g / L + 84533255 / 100000 / (L * √L))) := by
    calc A * (u * K) ≤ ((1 + ε) * N * (c2 / L + 2257 / 1000 / L ^ 2)) * (u * K) :=
          mul_le_mul_of_nonneg_right hB (mul_nonneg hU1 hK0)
      _ = (1 + ε) * N * u * ((c2 / L + 2257 / 1000 / L ^ 2) * K) := by ring
      _ ≤ (1 + ε) * N * u * (c2 / L * (4 * g / L + 84533255 / 100000 / (L * √L))) :=
          mul_le_mul_of_nonneg_left h128 (mul_nonneg (mul_nonneg hε0 hN0.le) hU1)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hM0
          exact mul_le_mul_of_nonneg_left h47 (mul_nonneg hε0 hN0.le)
  have hM : c2 / L * (4 * g / L + 84533255 / 100000 / (L * √L)) =
      c2 / L ^ 2 * (4 * g + 84533255 / 100000 / √L) := by
    have hL0 : L ≠ 0 := hLp.ne'
    have hsq0 : √L ≠ 0 := hsq.ne'
    field_simp <;> ring
  have hc : 84533255 / 100000 * (1 + e0) / √L ≤ 86016295 / 100000 / √L :=
    div_le_div_of_nonneg_right (by linarith) hsq.le
  have hpos : 0 ≤ c2 * (1 + ε) * N * V / L ^ 2 := by
    have := mul_nonneg (mul_nonneg (mul_nonneg hc0.le hε0) hN0.le) hU.le
    exact div_nonneg this (by positivity)
  have hfin : (1 + ε) * N * (V * (1 + e0)) * (c2 / L ^ 2 * (4 * g + 84533255 / 100000 / √L)) ≤
      c2 * (1 + ε) * N * V / L ^ 2 * (4 * g * (1 + e0) + 86016295 / 100000 / √L) := by
    calc (1 + ε) * N * (V * (1 + e0)) * (c2 / L ^ 2 * (4 * g + 84533255 / 100000 / √L))
        = c2 * (1 + ε) * N * V / L ^ 2 *
            (4 * g * (1 + e0) + 84533255 / 100000 * (1 + e0) / √L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hpos
  rw [hM] at hmain
  linarith

/-- Yamada 2015, Theorem 1.1: every even `N > exp exp 36` has `π₂(N) > 0.007 U_N N/log² N`.
PROVED, CONDITIONAL ON the U-1552 leaves through `thm71W_of_leaves`, the Cited Theorem 3.1
application, and the lab's cited `Thm48`, `Thm51`, `Thm61C C6corr`. -/
theorem yamada_of_leaves (h48 : Thm48) (h51 : Thm51) (h61 : Thm61C C6corr) : Yamada :=
  yamada_of_section8_corrW h48 h51 h61 thm71W_of_leaves c2Bound

end LeanLab.ChenExplicit.D1552
