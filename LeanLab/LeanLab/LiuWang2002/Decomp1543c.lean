/-
Unit U-1543, run 20261026T0808Z-17522, track T1. Decomposition of Lemmas 6.2, 6.5, 6.6 of
Liu-Wang 2002, Acta Arith. 105, pp. 169-170, the sums `S1`, `S2`, `S3` of the Vaughan split,
and the assembly `prop61_large`: Proposition 6.1 p. 168 for `log N ≥ 3100` and `q` in the
range (6.3), with the printed constants `0.28`, `4`, `0.09`, proved CONDITIONAL ON the leaves
of Decomp1543a, Decomp1543b and this file. The reduction to (6.3) on p. 168 and the case
`log N < 3100` are not formalized here.
Source: papers/P0023.pdf, pages 168-170 rendered with pdftoppm.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PNTPort.LargeSieve.Basic
import LeanLab.LiuWang2002.Decomp1543b
import LeanLab.LiuWang2002.Constants
import LeanLab.LiuWang2002.Vaughan109
import LeanLab.LiuWang2002.ArcBounds109
import LeanLab.LiuWang2002.Decomp109b
import LeanLab.LiuWang2002.BoundLimits109

namespace LeanLab.LiuWang2002.U1543

open Real Finset ArithmeticFunction

/-! ### Input from another paper -/

/-- Lemma 6.4 p. 169, the statement of Wang-Chen 1994, Lemma 3: for `X ≥ 1`, `q ≥ 15`,
`∑_{n≤X} min(Y/n, 1/(2‖αn‖)) ≤ 5q + 1.5 q log q + X log q + 5Y q^(-1) log X`. -/
def WCLemma3 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → 15 ≤ q → ∀ X Y : ℝ, 1 ≤ X → 0 < Y →
    ∑ n ∈ Icc 1 ⌊X⌋₊, minK (Y / n) (α * n) ≤
      5 * q + 1.5 * q * Real.log q + X * Real.log q + 5 * Y / q * Real.log X

/-- CITED, not proved in the lab: Lemma 6.4 p. 169 is [WC, Lemma 3], Wang-Chen, Acta Math.
Sinica 37 (1994), read with `‖x‖` the distance to the nearest integer. -/
theorem wc_lemma3 : WCLemma3 := by sorry

/-- The range (6.3) with `log N ≥ 3100` gives `15 ≤ q ≤ N`. PROVED. -/
theorem q_range (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) : 15 ≤ q ∧ q ≤ N := by
  have h4 : (3100 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have h5 : (3100 : ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have hL5 : (0 : ℝ) < Real.log N ^ 5 := by positivity
  constructor
  · have : (15 : ℝ) < q := by nlinarith
    exact_mod_cast this.le
  · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log N ^ 5 ≤ N := by
      rw [div_le_iff₀ hL5]; nlinarith
    exact_mod_cast (hq2.trans_le this).le


/-- The coefficient estimate in the proof of Lemma 6.6 on page 170. -/
theorem task147_S3_coefficient (k : ℕ) (U V : ℝ) :
    |∑ r ∈ k.divisors,
      if (r : ℝ) ≤ U ∧ ((k / r : ℕ) : ℝ) ≤ V then
        (vonMangoldt r : ℝ) * (moebius (k / r) : ℝ) else 0| ≤ Real.log k := by
  calc
    _ ≤ ∑ r ∈ k.divisors, |if (r : ℝ) ≤ U ∧ ((k / r : ℕ) : ℝ) ≤ V then
        (vonMangoldt r : ℝ) * (moebius (k / r) : ℝ) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ k.divisors, (vonMangoldt r : ℝ) := by
      apply sum_le_sum
      intro r hr
      split_ifs
      · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        apply mul_le_of_le_one_right vonMangoldt_nonneg
        exact_mod_cast (abs_moebius_le_one (n := k / r))
      · simp only [abs_zero]
        exact vonMangoldt_nonneg
    _ = _ := vonMangoldt_sum

/-- The elementary triangle estimate in Lemma 6.2 on page 169. -/
theorem task147_S1_triangle (c : ℝ) (N : ℕ) (U α : ℝ) :
    ‖Ssum (lam1 U) c N α‖ ≤ ∑ n ∈ Icc 1 ⌊U⌋₊, (vonMangoldt n : ℝ) := by
  classical
  unfold Ssum
  calc
    _ ≤ ∑ n ∈ rangeN c N, ‖(lam1 U n : ℂ) * e (α * n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ rangeN c N, if (n : ℝ) ≤ U then (vonMangoldt n : ℝ) else 0 := by
      apply sum_congr rfl
      intro n hn
      have he : ‖e (α * n)‖ = 1 := by rw [e, Complex.norm_exp]; simp
      rw [norm_mul, he, mul_one]
      unfold lam1
      split_ifs <;> simp [Complex.norm_real, abs_of_nonneg vonMangoldt_nonneg]
    _ = ∑ n ∈ (rangeN c N).filter (fun n : ℕ => (n : ℝ) ≤ U), (vonMangoldt n : ℝ) := by
      rw [sum_filter]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn, hnU⟩ := mem_filter.mp hn
        have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
        exact mem_Icc.mpr ⟨hn1, Nat.le_floor hnU⟩
      · intro n hn hnot
        exact vonMangoldt_nonneg

/-- The divisor to product reindexing used in partial summation on page 170. -/
theorem task147_divisor_reindex (c : ℝ) (N : ℕ) (V : ℝ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ rangeN c N, ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V), F n t) =
      ∑ t ∈ Icc 1 ⌊V⌋₊, ∑ m ∈ (Icc 1 (N / t)).filter
        (fun m : ℕ => c * N < ((m * t : ℕ) : ℝ)), F (m * t) t := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
  · intro p hp
    obtain ⟨hn, ht⟩ := mem_sigma.mp hp
    obtain ⟨hnN, hc⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnN
    obtain ⟨htd, htV⟩ := mem_filter.mp ht
    have hdiv := (Nat.mem_divisors.mp htd).1
    have ht0 := Nat.pos_of_mem_divisors htd
    have hn0 : 0 < p.1 := by omega
    have hm0 : 1 ≤ p.1 / p.2 := Nat.div_pos (Nat.le_of_dvd hn0 hdiv) ht0
    apply mem_sigma.mpr
    refine ⟨mem_Icc.mpr ⟨ht0, Nat.le_floor htV⟩, mem_filter.mpr ⟨mem_Icc.mpr ⟨hm0, ?_⟩, ?_⟩⟩
    · exact Nat.div_le_div_right hnN
    · simpa only [Nat.div_mul_cancel hdiv] using hc
  · intro p hp p' hp' he
    have ht : p.2 = p'.2 := congrArg Sigma.fst he
    have hm : p.1 / p.2 = p'.1 / p'.2 := congrArg (fun x : (_root_.Sigma fun _ : ℕ => ℕ) => x.2) he
    have hd := (Nat.mem_divisors.mp (mem_filter.mp (mem_sigma.mp hp).2).1).1
    have hd' := (Nat.mem_divisors.mp (mem_filter.mp (mem_sigma.mp hp').2).1).1
    have hn : p.1 = p'.1 := by
      calc p.1 = p.1 / p.2 * p.2 := (Nat.div_mul_cancel hd).symm
           _ = p'.1 / p'.2 * p'.2 := by rw [hm, ht]
           _ = p'.1 := Nat.div_mul_cancel hd'
    cases p
    cases p'
    simp_all
  · intro p hp
    obtain ⟨ht, hm⟩ := mem_sigma.mp hp
    obtain ⟨ht1, htV⟩ := mem_Icc.mp ht
    obtain ⟨hm, hc⟩ := mem_filter.mp hm
    obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
    have ht0 : 0 < p.1 := by omega
    have hprod : p.2 * p.1 ≤ N := (Nat.le_div_iff_mul_le ht0).mp hmN
    have hn0 : 0 < p.2 * p.1 := Nat.mul_pos hm1 ht1
    refine ⟨⟨p.2 * p.1, p.1⟩, ?_, ?_⟩
    · apply mem_sigma.mpr
      refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0, hprod⟩, hc⟩, mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, Nat.ne_of_gt hn0⟩
      · exact (Nat.le_floor_iff' (by omega : p.1 ≠ 0)).mp htV
    · simp only [Nat.mul_div_cancel _ ht0]
  · intro p hp
    have hd := (Nat.mem_divisors.mp (mem_filter.mp (mem_sigma.mp hp).2).1).1
    simp only [Nat.div_mul_cancel hd]

/-- The product form of S2 before partial summation on page 170. -/
theorem task147_S2_reindex (c : ℝ) (N : ℕ) (V α : ℝ) :
    Ssum (lam2 V) c N α =
      ∑ t ∈ Icc 1 ⌊V⌋₊, (moebius t : ℂ) *
        ∑ m ∈ (Icc 1 (N / t)).filter (fun m : ℕ => c * N < ((m * t : ℕ) : ℝ)),
          (Real.log m : ℂ) * e ((α * t) * m) := by
  classical
  unfold Ssum lam2
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [task147_divisor_reindex]
  apply sum_congr rfl
  intro t ht
  have ht0 : 0 < t := (mem_Icc.mp ht).1
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [Nat.mul_div_cancel m ht0]
  have he : α * ((m * t : ℕ) : ℝ) = (α * t) * m := by push_cast; ring
  rw [he]
  push_cast
  ring

/-- The monotone partial summation bound used for Lemma 6.5 on page 170. -/
theorem task147_weighted_suffix (w : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) (M : ℝ)
    (hw : Monotone w) (hw0 : 0 ≤ w 0)
    (hM : ∀ a ≤ n, ‖∑ i ∈ Ico a (n + 1), z i‖ ≤ M) :
    ‖∑ i ∈ range (n + 1), (w i : ℂ) * z i‖ ≤ w n * M := by
  induction n generalizing w z with
  | zero =>
    have hh := hM 0 (by omega)
    simpa [norm_mul, Complex.norm_real, abs_of_nonneg hw0] using
      mul_le_mul_of_nonneg_left hh hw0
  | succ n ih =>
    have hw' : Monotone (fun i => w (i + 1) - w 0) := by
      intro a b hab
      exact sub_le_sub_right (hw (by omega)) _
    have hw'0 : 0 ≤ w (0 + 1) - w 0 := sub_nonneg.mpr (hw (by omega))
    have hM' : ∀ a ≤ n, ‖∑ i ∈ Ico a (n + 1), z (i + 1)‖ ≤ M := by
      intro a ha
      rw [sum_Ico_add' z a (n + 1) 1]
      exact hM (a + 1) (by omega)
    have ht := ih (fun i => w (i + 1) - w 0) (fun i => z (i + 1)) hw' hw'0 hM'
    have he : (∑ i ∈ range (n + 2), (w i : ℂ) * z i) =
        (w 0 : ℂ) * (∑ i ∈ range (n + 2), z i) +
          ∑ i ∈ range (n + 1), ((w (i + 1) - w 0 : ℝ) : ℂ) * z (i + 1) := by
      rw [sum_range_succ' (fun i => (w i : ℂ) * z i), sum_range_succ' z]
      simp only [Complex.ofReal_sub, sub_mul, sum_sub_distrib, mul_add, mul_sum]
      ring
    have htotal : ‖∑ i ∈ range (n + 2), z i‖ ≤ M := by
      simpa only [range_eq_Ico] using hM 0 (by omega)
    change ‖∑ i ∈ range (n + 2), (w i : ℂ) * z i‖ ≤ w (n + 1) * M
    rw [he]
    calc
      _ ≤ ‖(w 0 : ℂ) * (∑ i ∈ range (n + 2), z i)‖ +
          ‖∑ i ∈ range (n + 1), ((w (i + 1) - w 0 : ℝ) : ℂ) * z (i + 1)‖ := norm_add_le _ _
      _ ≤ w 0 * M + (w (n + 1) - w 0) * M := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
        exact add_le_add (mul_le_mul_of_nonneg_left htotal hw0) ht
      _ = _ := by ring

/-- The geometric interval estimate used on page 170. -/
theorem task147_geom_interval (A B : ℕ) (X θ : ℝ) (hX : ((B + 1 - A : ℕ) : ℝ) ≤ X) :
    ‖∑ n ∈ Icc A B, e (θ * n)‖ ≤ minK X θ := by
  have heq : ∀ x : ℝ, e x = LeanLab.PNTPort.LargeSieve.e x := by
    intro x
    unfold e LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  simp_rw [heq]
  have htriv : ‖∑ n ∈ Icc A B, LeanLab.PNTPort.LargeSieve.e (θ * n)‖ ≤ X := by
    calc
      _ ≤ ∑ n ∈ Icc A B, ‖LeanLab.PNTPort.LargeSieve.e (θ * n)‖ := norm_sum_le _ _
      _ = ((B + 1 - A : ℕ) : ℝ) := by simp [LeanLab.PNTPort.LargeSieve.norm_e, Nat.card_Icc]
      _ ≤ _ := hX
  unfold minK
  split_ifs with hθ
  · exact htriv
  · apply le_min htriv
    have hdist : 0 < LeanLab.PNTPort.LargeSieve.dist0 θ :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hθ)
    have hk : (∑ n ∈ Icc A B, LeanLab.PNTPort.LargeSieve.e (θ * n)) =
        LeanLab.PNTPort.LargeSieve.e (θ * A) *
          ∑ j ∈ range (B + 1 - A), LeanLab.PNTPort.LargeSieve.e (θ * j) := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [← LeanLab.PNTPort.LargeSieve.e_add]
      congr 1
      push_cast
      ring
    rw [hk, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
    simpa only [mul_comm, LeanLab.PNTPort.LargeSieve.dist0, nint] using
      LeanLab.PNTPort.LargeSieve.norm_geom_le (B + 1 - A) hdist

/-- Partial summation for the logarithmic weight in Lemma 6.5 on page 170. -/
theorem task147_log_interval (A B N : ℕ) (X θ : ℝ) (hA : 1 ≤ A) (hBN : B ≤ N) (hBX : (B : ℝ) ≤ X) :
    ‖∑ m ∈ Icc A B, (Real.log m : ℂ) * e (θ * m)‖ ≤ Real.log N * minK X θ := by
  have hX0 : 0 ≤ X := (Nat.cast_nonneg B).trans hBX
  have hM0 : 0 ≤ minK X θ := by
    unfold minK
    split_ifs
    · exact hX0
    · exact le_min hX0 (by unfold nint; positivity)
  by_cases hAB : A ≤ B
  · have hw : Monotone (fun i : ℕ => Real.log ((A + i : ℕ) : ℝ)) := by
      intro i j hij
      apply Real.log_le_log
      · exact_mod_cast (show 0 < A + i by omega)
      · exact_mod_cast (Nat.add_le_add_left hij A)
    have hw0 : 0 ≤ Real.log ((A + 0 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have htail : ∀ a ≤ B - A,
        ‖∑ i ∈ Ico a (B - A + 1), e (θ * ((A + i : ℕ) : ℝ))‖ ≤ minK X θ := by
      intro a ha
      rw [sum_Ico_add (fun m : ℕ => e (θ * m)) a (B - A + 1) A]
      rw [show B - A + 1 + A = B + 1 by omega, Ico_add_one_right_eq_Icc]
      apply task147_geom_interval
      apply le_trans _ hBX
      exact_mod_cast (show B + 1 - (a + A) ≤ B by omega)
    have ht := task147_weighted_suffix
      (fun i : ℕ => Real.log ((A + i : ℕ) : ℝ))
      (fun i : ℕ => e (θ * ((A + i : ℕ) : ℝ))) (B - A) (minK X θ) hw hw0 htail
    have hlast : A + (B - A) = B := by omega
    rw [hlast] at ht
    have hh : ‖∑ m ∈ Icc A B, (Real.log m : ℂ) * e (θ * m)‖ ≤ Real.log B * minK X θ := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      rw [show B + 1 - A = B - A + 1 by omega]
      exact ht
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast (show 0 < B by omega)) (by exact_mod_cast hBN)) hM0)
  · rw [Icc_eq_empty_of_lt (by omega : B < A), sum_empty, norm_zero]
    exact mul_nonneg (Real.log_natCast_nonneg N) hM0

/-- Grouping the coefficient of S3 by k equals r t on page 170. -/
theorem task147_pair_divisors (n : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ r ∈ n.divisors, ∑ t ∈ n.divisors, if r * t ∣ n then F r t else 0) =
      ∑ k ∈ n.divisors, ∑ r ∈ k.divisors, F r (k / r) := by
  classical
  simp only [← sum_filter]
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩)
  · intro p hp
    obtain ⟨hr, ht⟩ := mem_sigma.mp hp
    obtain ⟨ht, hprod⟩ := mem_filter.mp ht
    have hn0 := (Nat.mem_divisors.mp hr).2
    apply mem_sigma.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hprod, hn0⟩, Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, ?_⟩⟩
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.pos_of_mem_divisors hr) (Nat.pos_of_mem_divisors ht))
  · intro p hp p' hp' he
    have hr : p.1 = p'.1 := congrArg (fun x : (_root_.Sigma fun _ : ℕ => ℕ) => x.2) he
    have hm : p.1 * p.2 = p'.1 * p'.2 := congrArg Sigma.fst he
    have hr0 := Nat.pos_of_mem_divisors (mem_sigma.mp hp).1
    have ht : p.2 = p'.2 := by
      rw [← hr] at hm
      exact Nat.eq_of_mul_eq_mul_left hr0 hm
    cases p
    cases p'
    simp_all
  · intro p hp
    obtain ⟨hk, hr⟩ := mem_sigma.mp hp
    have hkn := (Nat.mem_divisors.mp hk).1
    have hrk := (Nat.mem_divisors.mp hr).1
    have hn0 := (Nat.mem_divisors.mp hk).2
    have hk0 := Nat.pos_of_mem_divisors hk
    have he : p.2 * (p.1 / p.2) = p.1 := by rw [mul_comm, Nat.div_mul_cancel hrk]
    refine ⟨⟨p.2, p.1 / p.2⟩, ?_, ?_⟩
    · apply mem_sigma.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨hrk.trans hkn, hn0⟩, mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hrk).trans hkn, hn0⟩
      · simpa only [he] using hkn
    · simp only [he]
  · intro p hp
    have hr0 := Nat.pos_of_mem_divisors (mem_sigma.mp hp).1
    simp only [Nat.mul_div_right _ hr0]

/-- The UV support restriction in the proof of Lemma 6.6 on page 170. -/
theorem task147_lam3_reindex (n : ℕ) (U V : ℝ) (hU : 0 ≤ U) :
    lam3 U V n = -∑ k ∈ n.divisors.filter (fun k : ℕ => (k : ℝ) ≤ U * V),
      ∑ r ∈ k.divisors, if (r : ℝ) ≤ U ∧ ((k / r : ℕ) : ℝ) ≤ V then
        (vonMangoldt r : ℝ) * (moebius (k / r) : ℝ) else 0 := by
  unfold lam3
  congr 1
  have he : ∀ r t : ℕ,
      (if (r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n then
        (vonMangoldt r : ℝ) * (moebius t : ℝ) else 0) =
      if r * t ∣ n then (if (r : ℝ) ≤ U ∧ (t : ℝ) ≤ V then
        (vonMangoldt r : ℝ) * (moebius t : ℝ) else 0) else 0 := by
    intro r t
    split_ifs <;> tauto
  simp_rw [he]
  rw [task147_pair_divisors, sum_filter]
  apply sum_congr rfl
  intro k hk
  by_cases h : (k : ℝ) ≤ U * V
  · rw [if_pos h]
  · rw [if_neg h]
    apply sum_eq_zero
    intro r hr
    split_ifs with hrt
    · have hd := (Nat.mem_divisors.mp hr).1
      have hp : (r : ℝ) * ((k / r : ℕ) : ℝ) = k := by
        exact_mod_cast (show r * (k / r) = k by rw [mul_comm, Nat.div_mul_cancel hd])
      have hh := mul_le_mul hrt.1 hrt.2 (Nat.cast_nonneg (k / r)) hU
      rw [hp] at hh
      exact (h hh).elim
    · rfl

/-- A direct first sum budget for Proposition 6.1, pages 168 to 170.
The coefficient 0.0999 is a derived budget, not a printed constant of Lemma 6.2. -/
theorem task147_S1_direct (c : ℝ) (N : ℕ) (hL : 30.95 ≤ Real.log N) (α : ℝ) :
    ‖Ssum (lam1 (Uf N)) c N α‖ ≤
      0.0999 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hL; linarith
    · exact_mod_cast h
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hU0 : 0 ≤ Uf N := by unfold Uf; positivity
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpsi : (∑ n ∈ Icc 1 ⌊Uf N⌋₊, (vonMangoldt n : ℝ)) ≤ 6 * Uf N := by
    have hset : Icc 1 ⌊Uf N⌋₊ = Ioc 0 ⌊Uf N⌋₊ := by ext n; simp; omega
    rw [hset]
    change Chebyshev.psi (Uf N) ≤ 6 * Uf N
    exact (Chebyshev.psi_le_const_mul_self hU0).trans
      (mul_le_mul_of_nonneg_right (by linarith : Real.log 4 + 4 ≤ 6) hU0)
  have hUp : Uf N ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by
    unfold Uf
    apply mul_le_of_le_one_right (by positivity)
    exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hdouble : 2 * (N : ℝ) ^ ((2 : ℝ) / 5) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hN, Real.log_rpow hN]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hLp : Real.log N ≤ Real.log N ^ (1.4 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 1.4 by norm_num)
  calc
    _ ≤ 6 * Uf N := (task147_S1_triangle c N (Uf N) α).trans hpsi
    _ ≤ 6 * (N : ℝ) ^ ((2 : ℝ) / 5) := by gcongr
    _ ≤ 3 * (N : ℝ) ^ ((4 : ℝ) / 5) := by linarith
    _ ≤ _ := by
      have hc : 3 ≤ 0.0999 * Real.log N ^ (1.4 : ℝ) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hN.le ((4 : ℝ) / 5))]

/-- The endpoint difference between display 3.8 on page 144 and display 6.8 on page 169. -/
theorem task147_cutoff_error (c : ℝ) (N : ℕ) (α : ℝ) :
    ‖Vaughan109.S N c α - Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ Real.log N := by
  classical
  let E : Finset ℕ := (Icc 1 N).filter (fun n : ℕ => c * N = n)
  let F : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * e (α * n)
  have hset : range (N + 1) = insert 0 (Icc 1 N) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have hinc : Vaughan109.S N c α = ∑ n ∈ Icc 1 N, if c * N ≤ (n : ℝ) then F n else 0 := by
    unfold Vaughan109.S Vaughan109.weightedSum
    rw [Nat.floor_natCast, hset, sum_insert (by simp)]
    have hv0 : (vonMangoldt 0 : ℝ) = 0 := by simp
    simp only [hv0, Complex.ofReal_zero, zero_mul, ite_self, zero_add]
    simp only [F, e, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hstrict : Ssum (fun n => (vonMangoldt n : ℝ)) c N α =
      ∑ n ∈ Icc 1 N, if c * N < (n : ℝ) then F n else 0 := by
    unfold Ssum rangeN
    rw [sum_filter]
  have hd : Vaughan109.S N c α - Ssum (fun n => (vonMangoldt n : ℝ)) c N α = ∑ n ∈ E, F n := by
    rw [hinc, hstrict, ← sum_sub_distrib]
    unfold E
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hl : c * N < (n : ℝ)
    · have hne : c * N ≠ (n : ℝ) := ne_of_lt hl
      simp [hl, hl.le, hne]
    · by_cases he : c * N = (n : ℝ)
      · simp [he]
      · have hle : ¬c * N ≤ (n : ℝ) := by
          intro h
          exact he (le_antisymm h (le_of_not_gt hl))
        simp [hl, he, hle]
  have hcard : E.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    exact_mod_cast ha'.symm.trans hb'
  have hterm : ∀ n ∈ E, ‖F n‖ ≤ Real.log N := by
    intro n hn
    obtain ⟨hn, -⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have he : ‖e (α * n)‖ = 1 := by rw [e, Complex.norm_exp]; simp
    dsimp only [F]
    rw [norm_mul, he, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans (Real.log_le_log hn0 (by exact_mod_cast hnN))
  rw [hd]
  calc
    _ ≤ ∑ n ∈ E, Real.log N := norm_sum_le_of_le E hterm
    _ = (E.card : ℝ) * Real.log N := by simp
    _ ≤ Real.log N := by
      have hc : (E.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith [Real.log_natCast_nonneg N]

/-- The endpoint interpolation on M4 in the proof of Theorem 1 on page 174. -/
theorem task147_m4_numeric (N q : ℕ) (hL : 3100 ≤ Real.log N)
    (hqlo : Real.log N ^ 6 ≤ (q : ℝ)) (hqhi : (q : ℝ) ≤ N / Real.log N ^ 7) :
    0.28 * N / √q * Real.log N ^ 2 +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.09 * √N * √q * Real.log N ^ (2.5 : ℝ) ≤ 0.3 * N / Real.log N := by
  have hN : (0 : ℝ) < N := (task141_logs N hL).1
  have hqhi' : (q : ℝ) ≤ exp (Real.log N) / Real.log N ^ 7 := by rwa [Real.exp_log hN]
  have hh := ArcBounds109.m4_bound (Real.log N) q hL hqlo hqhi'
  rw [Real.exp_log hN] at hh
  simpa only [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg q), div_eq_mul_inv,
    mul_assoc] using hh

/-- Absorbing the endpoint error in the M4 coefficient margin on page 174. -/
theorem task147_cutoff_absorb (N : ℕ) (hL : 3100 ≤ Real.log N) :
    Real.log N ≤ 0.012 * N / Real.log N := by
  have hN : (0 : ℝ) < N := (task141_logs N hL).1
  have hL0 : 0 < Real.log N := by linarith
  have he := LeanLab.LiuWang2002.Constants.exp_ge_pow (Real.log N) hL0.le 4
  rw [Real.exp_log hN] at he
  norm_num [Nat.factorial] at he
  apply (le_div_iff₀ hL0).mpr
  have h2 : (3100 : ℝ) ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
  have hh := mul_le_mul_of_nonneg_left h2 (sq_nonneg (Real.log N))
  nlinarith [sq_nonneg (Real.log N)]

/-- The parameter logarithms on the full range of display 6.6 on page 168. -/
theorem task147_logs_full (N : ℕ) (hL : 30.95 ≤ Real.log N) :
    0 < (N : ℝ) ∧ 0 < Uf N ∧ 0 < Vf N ∧
    Real.log (Uf N) = 2 / 5 * Real.log N - 4 / 5 * Real.log (Real.log N) ∧
    Real.log (Vf N) = 2 / 5 * Real.log N + 1 / 5 * Real.log (Real.log N) := by
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hL; linarith
    · exact_mod_cast h
  have hL0 : 0 < Real.log N := by linarith
  have hp := Real.rpow_pos_of_pos hN ((2 : ℝ) / 5)
  have hU : 0 < Uf N := mul_pos hp (Real.rpow_pos_of_pos hL0 _)
  have hV : 0 < Vf N := mul_pos hp (Real.rpow_pos_of_pos hL0 _)
  refine ⟨hN, hU, hV, ?_, ?_⟩
  · unfold Uf
    rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]
    ring
  · unfold Vf
    rw [Real.log_mul hp.ne' (Real.rpow_pos_of_pos hL0 _).ne', Real.log_rpow hN,
      Real.log_rpow hL0]

/-- The denominator range on the full range of display 6.5 on page 168. -/
theorem task147_q_range_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) : 15 ≤ q ∧ q ≤ N := by
  have h4 : (30.95 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have h5 : (30.95 : ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have hL5 : (0 : ℝ) < Real.log N ^ 5 := by positivity
  constructor
  · have : (15 : ℝ) < q := by nlinarith
    exact_mod_cast this.le
  · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log N ^ 5 ≤ N := by
      rw [div_le_iff₀ hL5]; nlinarith
    exact_mod_cast (hq2.trans_le this).le

/-- The printed logarithm bound in the proof of Lemma 6.5 on page 170. -/
theorem task147_q_log_upper_full (N q : ℕ) (hL : 30.95 ≤ Real.log N)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Real.log q ≤ Real.log N - 12.34 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [Nat.cast_zero, Real.log_zero]
    linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simp at hL; linarith
    · exact_mod_cast hn
  have hL0 : 0 < Real.log N := by linarith
  have he : exp (12.34 : ℝ) ≤ (2.7182818286 : ℝ) ^ 12 * 1.405 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 12
    have he12 : exp (12 : ℝ) = exp 1 ^ 12 := by simpa using Real.exp_nat_mul (1 : ℝ) 12
    have hr : exp (0.34 : ℝ) ≤ 1.405 := by
      have hh := Real.exp_bound' (x := (0.34 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hh
      linarith
    rw [show (12.34 : ℝ) = 12 + 0.34 by norm_num, Real.exp_add, he12]
    exact mul_le_mul hp hr (Real.exp_pos _).le (by positivity)
  have hc : (1.0012 / 0.09) ^ 2 * exp (12.34 : ℝ) ≤ Real.log N ^ 5 := by
    have hp : (30.95 : ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
    calc
      _ ≤ (1.0012 / 0.09) ^ 2 * ((2.7182818286 : ℝ) ^ 12 * 1.405) := by gcongr
      _ ≤ (30.95 : ℝ) ^ 5 := by norm_num
      _ ≤ _ := hp
  have hdiv : (1.0012 / 0.09) ^ 2 / Real.log N ^ 5 ≤ exp (-12.34 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (pow_pos hL0 5) (Real.exp_pos _)).mpr
    simpa only [one_mul] using hc
  have hqN : (q : ℝ) ≤ (N : ℝ) * exp (-12.34 : ℝ) := by
    calc
      _ ≤ (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 := hq2.le
      _ = N * ((1.0012 / 0.09) ^ 2 / Real.log N ^ 5) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hN0.le
  have hh := Real.log_le_log hq0 hqN
  rw [Real.log_mul hN0.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
  linarith

/-- The n65c coefficient estimate on the full paper range on page 170. -/
theorem task147_n65c_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Vf N) * Real.log N ≤ 0.0282 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task147_logs_full N hL
  have hL0 : 0 < Real.log N := by linarith
  have hlogL := Real.log_le_sub_one_of_pos hL0
  have hlv1 : Real.log (Vf N) ≤ Real.log N := by rw [hlv]; linarith
  have h4 : (30.95 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hqbig : (250 : ℝ) ≤ √q := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)).mpr
    nlinarith
  have hsq : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq0 : (0 : ℝ) < q := by nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hs0 : (0 : ℝ) < √q := by linarith
  calc
    _ ≤ 5 * N / q * Real.log N * Real.log N := by gcongr
    _ = ((N : ℝ) / √q * Real.log N ^ 2) * (5 / √q) := by
      field_simp
      nlinarith [hsq]
    _ ≤ ((N : ℝ) / √q * Real.log N ^ 2) * 0.0282 := by
      gcongr
      apply (div_le_iff₀ hs0).mpr
      linarith
    _ = _ := by ring

/-- The n66c coefficient estimate on the full paper range on page 170. -/
theorem task147_n66c_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) ≤
      0.0131 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task147_logs_full N hL
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL1
  have hlogLupper := Real.log_le_sub_one_of_pos hL0
  have huv0 : 0 ≤ Real.log (Uf N * Vf N) := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have huv : Real.log (Uf N * Vf N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have h4 : (30.95 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hqbig : (250 : ℝ) ≤ √q := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)).mpr
    nlinarith
  have hsq : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq0 : (0 : ℝ) < q := by nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hs0 : (0 : ℝ) < √q := by linarith
  calc
    _ ≤ 5 * N / q * (0.8 * Real.log N) * (0.8 * Real.log N) := by gcongr
    _ = ((N : ℝ) / √q * Real.log N ^ 2) * (3.2 / √q) := by
      field_simp
      nlinarith [hsq]
    _ ≤ ((N : ℝ) / √q * Real.log N ^ 2) * 0.0131 := by
      gcongr
      apply (div_le_iff₀ hs0).mpr
      linarith
    _ = _ := by ring

/-- The n65a coefficient estimate on the full paper range on page 170. -/
theorem task147_n65a_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log N ≤
      0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hq15, hqN⟩ := task147_q_range_full N hL q hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg _
  have hupper := task147_q_log_upper_full N q hL hq2
  have hfirst : 5 + 1.5 * Real.log q ≤ 1.5 * Real.log N := by linarith
  have hpl : (Real.log N ^ (2.5 : ℝ)) ^ 2 = Real.log N ^ 5 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0.le]
    norm_num
  have hs : √(q : ℝ) * Real.log N ^ (2.5 : ℝ) ≤ (1.0012 / 0.09) * √N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q), Real.sq_sqrt (Nat.cast_nonneg N), hpl]
    exact ((lt_div_iff₀ (pow_pos hL0 5)).mp hq2).le
  have h3 : 1.5 * (1.0012 / 0.09) ≤ 0.0006 * Real.log N ^ 3 := by
    have hh : (30.95 : ℝ) ^ 3 ≤ Real.log N ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    nlinarith
  have hc : (1.0012 / 0.09) * (1.5 * Real.log N) * Real.log N ≤ 0.0006 * Real.log N ^ 5 := by
    have hm := mul_le_mul_of_nonneg_right h3 (sq_nonneg (Real.log N))
    nlinarith
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hL0 (2.5 : ℝ))).mp
  calc
    _ = √(q : ℝ) * (√q * Real.log N ^ (2.5 : ℝ)) *
        (5 + 1.5 * Real.log q) * Real.log N := by
      ring_nf
      rw [Real.sq_sqrt (Nat.cast_nonneg q)]
      ring
    _ ≤ √(q : ℝ) * ((1.0012 / 0.09) * √N) * (1.5 * Real.log N) * Real.log N := by gcongr
    _ = √(N : ℝ) * √q * ((1.0012 / 0.09) * (1.5 * Real.log N) * Real.log N) := by ring
    _ ≤ √(N : ℝ) * √q * (0.0006 * Real.log N ^ 5) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) * Real.log N ^ (2.5 : ℝ) := by
      rw [← hpl]
      ring
    _ = Real.log N ^ (2.5 : ℝ) * (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) := by ring

/-- The n65b coefficient estimate on the full paper range on page 170. -/
theorem task147_n65b_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Vf N * Real.log q * Real.log N ≤ 0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task147_logs_full N hL
  have hL0 : 0 < Real.log N := by linarith
  obtain ⟨hq15, hqN⟩ := task147_q_range_full N hL q hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hlogL : Real.log (Real.log N) ≤ 3.4325 + (Real.log N / 30.95 - 1) := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < Real.log N / 30.95 by positivity)
    rw [Real.log_div hL0.ne' (by norm_num)] at hh
    linarith [Decomp109b.log_endpoint]
  have hc : (-9.3 : ℝ) ≤ Real.log (0.0001 : ℝ) := by
    have hh : Real.log (10000 : ℝ) ≤ 9.3 := by
      have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 10000)
        (show (10000 : ℝ) ≤ (2 : ℝ) ^ 13 * 1.25 by norm_num)
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow] at ht
      norm_num only [Nat.cast_ofNat] at ht
      linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.25)]
    rw [show (0.0001 : ℝ) = (10000 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  calc
    _ ≤ Vf N * Real.log N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlq (mul_pos hV hL0).le]
    _ ≤ _ := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_mul hV.ne' (pow_pos hL0 2).ne', Real.log_pow, hlv,
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
      norm_num at hlogL ⊢
      linarith

/-- The n66a coefficient estimate on the full paper range on page 170. -/
theorem task147_n66a_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log (Uf N * Vf N) ≤
      0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task147_logs_full N hL
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have huv : Real.log (Uf N * Vf N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have hq15 := (task147_q_range_full N hL q hq1 hq2).1
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  calc
    _ ≤ (5 * q + 1.5 * q * Real.log q) * (0.8 * Real.log N) := by gcongr
    _ = 0.8 * ((5 * q + 1.5 * q * Real.log q) * Real.log N) := by ring
    _ ≤ 0.8 * (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) :=
      mul_le_mul_of_nonneg_left (task147_n65a_full N hL q hq1 hq2) (by norm_num)
    _ ≤ _ := by
      have h : 0 ≤ √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) := by positivity
      nlinarith

/-- The n66b coefficient estimate on the full paper range on page 170. -/
theorem task147_n66b_full (N : ℕ) (hL : 30.95 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) ≤
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task147_logs_full N hL
  have hL0 : 0 < Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have huv : Real.log (Uf N * Vf N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have hlogLupper := Real.log_le_sub_one_of_pos hL0
  have huv0 : 0 ≤ Real.log (Uf N * Vf N) := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  obtain ⟨hq15, hqN⟩ := task147_q_range_full N hL q hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have he : Uf N * Vf N * Real.log N ^ 2 =
      (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_mul (mul_pos hU hV).ne' (pow_pos hL0 2).ne',
      Real.log_mul hU.ne' hV.ne', Real.log_pow, hlu, hlv,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
    ring
  calc
    _ ≤ Uf N * Vf N * Real.log N * (0.8 * Real.log N) := by gcongr
    _ = 0.8 * (Uf N * Vf N * Real.log N ^ 2) := by ring
    _ = _ := by rw [he]; ring

/-! ### Leaves -/

/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170, first line, by partial summation:
`|S2(α)| ≤ log N ∑_{t≤V} min(N/t, 1/(2‖αt‖))`, for `c ≥ 0`. -/
theorem S2_le (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (V α : ℝ) :
    ‖Ssum (lam2 V) c N α‖ ≤
      Real.log N * ∑ t ∈ Icc 1 ⌊V⌋₊, minK ((N : ℝ) / t) (α * t) := by
  rw [task147_S2_reindex, mul_sum]
  apply norm_sum_le_of_le
  intro t ht
  have ht0 : 0 < t := (mem_Icc.mp ht).1
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hx : 0 ≤ c * N / (t : ℝ) := by positivity
  have hset : (Icc 1 (N / t)).filter (fun m : ℕ => c * N < ((m * t : ℕ) : ℝ)) =
      Icc (⌊c * N / (t : ℝ)⌋₊ + 1) (N / t) := by
    ext m
    simp only [mem_filter, mem_Icc, Nat.cast_mul]
    have hcut : c * N < (m : ℝ) * t ↔ ⌊c * N / (t : ℝ)⌋₊ + 1 ≤ m := by
      rw [← div_lt_iff₀ htR, ← Nat.floor_lt hx]
      omega
    rw [hcut]
    omega
  rw [norm_mul, hset]
  have hBX : ((N / t : ℕ) : ℝ) ≤ (N : ℝ) / t := by
    apply (le_div_iff₀ htR).mpr
    exact_mod_cast Nat.div_mul_le_self N t
  have hinner := task147_log_interval (⌊c * N / (t : ℝ)⌋₊ + 1) (N / t) N
    ((N : ℝ) / t) (α * t) (by omega) (Nat.div_le_self N t) hBX
  have hmu : ‖(moebius t : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast (abs_moebius_le_one (n := t))
  calc
    _ ≤ 1 * (Real.log N * minK ((N : ℝ) / t) (α * t)) :=
      mul_le_mul hmu hinner (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170, first line: with `k = rt ≤ UV` and
`|∑_{rt=k} Λ(r) μ(t)| ≤ ∑_{r|k} Λ(r) = log k ≤ log(UV)`,
`|S3(α)| ≤ log(UV) ∑_{k≤UV} min(N/k, 1/(2‖αk‖))`, for `c ≥ 0`, `U, V ≥ 1`. -/
theorem S3_le (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (U V α : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ‖Ssum (lam3 U V) c N α‖ ≤
      Real.log (U * V) * ∑ k ∈ Icc 1 ⌊U * V⌋₊, minK ((N : ℝ) / k) (α * k) := by
  classical
  let f : ℕ → ℝ := fun k => ∑ r ∈ k.divisors,
    if (r : ℝ) ≤ U ∧ ((k / r : ℕ) : ℝ) ≤ V then
      (vonMangoldt r : ℝ) * (moebius (k / r) : ℝ) else 0
  have hcoeff : ∀ n, lam3 U V n = -∑ k ∈ n.divisors.filter (fun k : ℕ => (k : ℝ) ≤ U * V), f k :=
    fun n => task147_lam3_reindex n U V (by linarith)
  have hs : Ssum (lam3 U V) c N α =
      -∑ k ∈ Icc 1 ⌊U * V⌋₊, (f k : ℂ) *
        ∑ m ∈ (Icc 1 (N / k)).filter (fun m : ℕ => c * N < ((m * k : ℕ) : ℝ)),
          e ((α * k) * m) := by
    unfold Ssum
    simp_rw [hcoeff]
    simp only [Complex.ofReal_neg, Complex.ofReal_sum, neg_mul, sum_neg_distrib, Finset.sum_mul]
    congr 1
    rw [task147_divisor_reindex]
    apply sum_congr rfl
    intro k hk
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    congr 2
    push_cast
    ring
  rw [hs, norm_neg, mul_sum]
  apply norm_sum_le_of_le
  intro k hk
  have hk0 : 0 < k := (mem_Icc.mp hk).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hx : 0 ≤ c * N / (k : ℝ) := by positivity
  have hset : (Icc 1 (N / k)).filter (fun m : ℕ => c * N < ((m * k : ℕ) : ℝ)) =
      Icc (⌊c * N / (k : ℝ)⌋₊ + 1) (N / k) := by
    ext m
    simp only [mem_filter, mem_Icc, Nat.cast_mul]
    have hcut : c * N < (m : ℝ) * k ↔ ⌊c * N / (k : ℝ)⌋₊ + 1 ≤ m := by
      rw [← div_lt_iff₀ hkR, ← Nat.floor_lt hx]
      omega
    rw [hcut]
    omega
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hset]
  have hBX : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast Nat.div_mul_le_self N k
  have hinner : ‖∑ m ∈ Icc (⌊c * N / (k : ℝ)⌋₊ + 1) (N / k), e ((α * k) * m)‖ ≤
      minK ((N : ℝ) / k) (α * k) := by
    apply task147_geom_interval
    apply le_trans _ hBX
    apply Nat.cast_le.mpr
    rw [Nat.add_sub_add_right]
    exact Nat.sub_le _ _
  have hkUV : (k : ℝ) ≤ U * V := (Nat.le_floor_iff' (by omega : k ≠ 0)).mp (mem_Icc.mp hk).2
  have hf : |f k| ≤ Real.log (U * V) := (task147_S3_coefficient k U V).trans
    (Real.log_le_log hkR hkUV)
  have hl0 : 0 ≤ Real.log (U * V) := Real.log_nonneg (by nlinarith : 1 ≤ U * V)
  exact mul_le_mul hf hinner (norm_nonneg _) hl0

/-- LEAF. Unit U-1543. Lemma 6.2 p. 169, for `log N ≥ 3100`:
`|S1(α)| ≤ ∑_{n≤U} Λ(n) ≤ 1.02 U`, using a Chebyshev bound at `U ≥ exp(9.634)`.
External input: Rosser and Schoenfeld 1975, page 265, displays 5.1 and 5.3.
The elementary triangle step is `task147_S1_triangle`; the cited input stays open. -/
theorem lemma62_S1 (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) :
    ‖Ssum (lam1 (Uf N)) c N α‖ ≤ 1.02 * Uf N := by
  unfold Ssum
  sorry


/-- LEAF. Unit U-1543. The `S1` term is absorbed in the middle term of (6.2) p. 168:
`1.02 U ≤ 0.38 N^(4/5) log^1.4 N` for `log N ≥ 3100`. -/
theorem S1_absorb (N : ℕ) (hL : 3100 ≤ Real.log N) :
    1.02 * Uf N ≤ 0.38 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hL1 : 1 ≤ Real.log N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by exact_mod_cast hN)
  have hUp : Uf N ≤ (N : ℝ) ^ ((2 : ℝ) / 5) := by
    unfold Uf
    apply mul_le_of_le_one_right (by positivity)
    exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hNp : (N : ℝ) ^ ((2 : ℝ) / 5) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hLp : Real.log N ≤ Real.log N ^ (1.4 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 1.4 by norm_num)
  calc
    _ ≤ 1.02 * (N : ℝ) ^ ((4 : ℝ) / 5) := by gcongr; exact hUp.trans hNp
    _ ≤ _ := by
      have hc : 1.02 ≤ 0.38 * Real.log N ^ (1.4 : ℝ) := by linarith
      have hm := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hN.le ((4 : ℝ) / 5))
      nlinarith

/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170: under (6.3),
`(5q + 1.5 q log q) log N ≤ 0.0006 N^(1/2) q^(1/2) log^2.5 N`, for `log N ≥ 3100`. -/
theorem n65a (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log N ≤
      0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hq15, hqN⟩ := q_range N hL q hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have h3 : (0 : ℝ) < Real.log N ^ 3 := by positivity
  have h5 : (0 : ℝ) < Real.log N ^ 5 := by positivity
  have hqL : (q : ℝ) * Real.log N ^ 2 ≤ N := by
    calc
      _ = ((q : ℝ) * Real.log N ^ 5) / Real.log N ^ 3 := by field_simp
      _ ≤ ((1.0012 / 0.09) ^ 2 * N) / Real.log N ^ 3 := by
        exact div_le_div_of_nonneg_right ((lt_div_iff₀ h5).mp hq2).le h3.le
      _ ≤ N := by
        rw [div_le_iff₀ h3]
        have hc : (1.0012 / 0.09) ^ 2 ≤ Real.log N ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3100) hL 3
          norm_num at *
          linarith
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hs : √(q : ℝ) * Real.log N ≤ √N := by
    calc
      _ = √((q : ℝ) * Real.log N ^ 2) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq hL0.le]
      _ ≤ _ := Real.sqrt_le_sqrt hqL
  have hp : Real.log N ^ 2 ≤ Real.log N ^ (2.5 : ℝ) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show (2 : ℝ) ≤ 2.5 by norm_num)
  calc
    _ = √(q : ℝ) * (√q * Real.log N) * (5 + 1.5 * Real.log q) := by
      ring_nf
      rw [Real.sq_sqrt (Nat.cast_nonneg q)]
      ring
    _ ≤ √(q : ℝ) * √N * (1.502 * Real.log N) := by
      gcongr
      linarith
    _ ≤ √(q : ℝ) * √N * (0.0006 * Real.log N ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith :
        1.502 * Real.log N ≤ 0.0006 * Real.log N ^ 2) (by positivity)
    _ ≤ √(q : ℝ) * √N * (0.0006 * Real.log N ^ (2.5 : ℝ)) := by gcongr
    _ = _ := by ring


/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170: `V log q · log N ≤ 0.0001 N^(4/5) log^1.4 N`;
the paper writes `N^(2/5) (log N)^(1/5) log q ≤ 0.0001 N^(4/5) log^0.4 N`. -/
theorem n65b (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Vf N * Real.log q * Real.log N ≤ 0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hL0 : 0 < Real.log N := by linarith
  obtain ⟨hq15, hqN⟩ := q_range N hL q hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hlogL := task141_log_log (Real.log N) hL
  have hc : (-36 : ℝ) ≤ Real.log (0.0001 : ℝ) := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    have he : (0.0001 : ℝ) = ((10 : ℝ) ^ 4)⁻¹ := by norm_num
    rw [he, Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ Vf N * Real.log N ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hlq (mul_pos hV hL0).le]
    _ ≤ _ := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_mul hV.ne' (pow_pos hL0 2).ne', Real.log_pow, hlv,
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
      linarith

/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170: `5 N q^(-1) log V · log N ≤ 0.0282 N q^(-1/2)
log^2 N`. -/
theorem n65c (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Vf N) * Real.log N ≤ 0.0282 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hL0 : 0 < Real.log N := by linarith
  have hlogL := task141_log_log (Real.log N) hL
  have hlv0 : 0 ≤ Real.log (Vf N) := by
    have hv1 := (params_facts N hL).2.1
    exact Real.log_nonneg ((Real.one_le_exp (by norm_num)).trans hv1)
  have hlv1 : Real.log (Vf N) ≤ Real.log N := by rw [hlv]; linarith
  have h4 : (3100 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hqbig : (1000 : ℝ) ≤ √q := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)).mpr
    nlinarith
  have hsq : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq0 : (0 : ℝ) < q := by nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hs0 : (0 : ℝ) < √q := by linarith
  calc
    _ ≤ 5 * N / q * Real.log N * Real.log N := by gcongr
    _ = ((N : ℝ) / √q * Real.log N ^ 2) * (5 / √q) := by
      field_simp
      nlinarith [hsq]
    _ ≤ ((N : ℝ) / √q * Real.log N ^ 2) * 0.0282 := by
      gcongr
      apply (div_le_iff₀ hs0).mpr
      linarith
    _ = _ := by ring


/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170: `(5q + 1.5 q log q) log(UV) ≤
0.0005 N^(1/2) q^(1/2) log^2.5 N`. -/
theorem n66a (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log (Uf N * Vf N) ≤
      0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have huv : Real.log (Uf N * Vf N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have hq15 := (q_range N hL q hq1 hq2).1
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  calc
    _ ≤ (5 * q + 1.5 * q * Real.log q) * (0.8 * Real.log N) := by gcongr
    _ = 0.8 * ((5 * q + 1.5 * q * Real.log q) * Real.log N) := by ring
    _ ≤ 0.8 * (0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)) :=
      mul_le_mul_of_nonneg_left (n65a N hL q hq1 hq2) (by norm_num)
    _ ≤ _ := by
      have h : 0 ≤ √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) := by positivity
      nlinarith


/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170: `UV (log q) log(UV) ≤ 0.8 N^(4/5) log^1.4 N`. -/
theorem n66b (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) ≤
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hL0 : 0 < Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have huv : Real.log (Uf N * Vf N) ≤ 0.8 * Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have huv0 : 0 ≤ Real.log (Uf N * Vf N) := by
    apply Real.log_nonneg
    obtain ⟨hu, hv, -⟩ := params_facts N hL
    have hv1 : 1 ≤ Vf N := (Real.one_le_exp (by norm_num)).trans hv
    nlinarith
  obtain ⟨hq15, hqN⟩ := q_range N hL q hq1 hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlq : Real.log q ≤ Real.log N := Real.log_le_log hq0 (by exact_mod_cast hqN)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have he : Uf N * Vf N * Real.log N ^ 2 =
      (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_mul (mul_pos hU hV).ne' (pow_pos hL0 2).ne',
      Real.log_mul hU.ne' hV.ne', Real.log_pow, hlu, hlv,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
    ring
  calc
    _ ≤ Uf N * Vf N * Real.log N * (0.8 * Real.log N) := by gcongr
    _ = 0.8 * (Uf N * Vf N * Real.log N ^ 2) := by ring
    _ = _ := by rw [he]; ring


/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170: `5 N q^(-1) log^2(UV) ≤ 0.0131 N q^(-1/2)
log^2 N`. -/
theorem n66c (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) ≤
      0.0131 * N / √q * Real.log N ^ 2 := by
  obtain ⟨hN, hU, hV, hlu, hlv⟩ := task141_logs N hL
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL1
  have huv1 : 1 ≤ Uf N * Vf N := by
    obtain ⟨hu, hv, -⟩ := params_facts N hL
    have hv1 : 1 ≤ Vf N := (Real.one_le_exp (by norm_num)).trans hv
    nlinarith
  have huv0 : 0 ≤ Real.log (Uf N * Vf N) := Real.log_nonneg huv1
  have huv : Real.log (Uf N * Vf N) ≤ Real.log N := by
    rw [Real.log_mul hU.ne' hV.ne', hlu, hlv]
    linarith
  have h4 : (3100 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hqbig : (1000 : ℝ) ≤ √q := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)).mpr
    nlinarith
  have hsq : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hq0 : (0 : ℝ) < q := by nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hs0 : (0 : ℝ) < √q := by linarith
  calc
    _ ≤ 5 * N / q * Real.log N * Real.log N := by gcongr
    _ = ((N : ℝ) / √q * Real.log N ^ 2) * (5 / √q) := by
      field_simp
      nlinarith [hsq]
    _ ≤ ((N : ℝ) / √q * Real.log N ^ 2) * 0.0131 := by
      gcongr
      apply (div_le_iff₀ hs0).mpr
      linarith
    _ = _ := by ring


/-! ### Assemblies -/

/-- Lemma 6.5 p. 169 for `log N ≥ 3100` and `q` in (6.3): `|S2(α)| ≤ 0.0282 N q^(-1/2) log^2 N
+ 0.0001 N^(4/5) log^1.4 N + 0.0006 N^(1/2) q^(1/2) log^2.5 N`. PROVED, CONDITIONAL ON `S2_le`,
`wc_lemma3`, `n65a`, `n65b`, `n65c`, `params_facts`. -/
theorem lemma65 (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (lam2 (Vf N)) c N α‖ ≤ 0.0282 * N / √q * Real.log N ^ 2 +
      0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨-, hV13, -, -, -, hN0⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  have hq15 := (q_range N hL q hq1 hq2).1
  have hw := wc_lemma3 α a q hD hq15 (Vf N) N hV1 hN0
  have hL0 : 0 ≤ Real.log N := by linarith
  have h1 := (S2_le c hc N (Vf N) α).trans (mul_le_mul_of_nonneg_left hw hL0)
  have e : Real.log N * (5 * q + 1.5 * q * Real.log q + Vf N * Real.log q +
      5 * N / q * Real.log (Vf N)) = (5 * q + 1.5 * q * Real.log q) * Real.log N +
      Vf N * Real.log q * Real.log N + 5 * N / q * Real.log (Vf N) * Real.log N := by ring
  rw [e] at h1
  linarith [n65a N hL q hq1 hq2, n65b N hL q hq1 hq2, n65c N hL q hq1 hq2]

/-- Lemma 6.6 p. 170 for `log N ≥ 3100` and `q` in (6.3): `|S3(α)| ≤ 0.0131 N q^(-1/2) log^2 N
+ 0.8 N^(4/5) log^1.4 N + 0.0005 N^(1/2) q^(1/2) log^2.5 N`. PROVED, CONDITIONAL ON `S3_le`,
`wc_lemma3`, `n66a`, `n66b`, `n66c`, `params_facts`. -/
theorem lemma66 (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ ≤ 0.0131 * N / √q * Real.log N ^ 2 +
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hU15, hV13, -, -, -, hN0⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  have hU1 : (1 : ℝ) ≤ Uf N := by linarith
  have hUV1 : (1 : ℝ) ≤ Uf N * Vf N := by nlinarith
  have hq15 := (q_range N hL q hq1 hq2).1
  have hw := wc_lemma3 α a q hD hq15 (Uf N * Vf N) N hUV1 hN0
  have hl0 : 0 ≤ Real.log (Uf N * Vf N) := Real.log_nonneg hUV1
  have h1 := (S3_le c hc N (Uf N) (Vf N) α hU1 hV1).trans (mul_le_mul_of_nonneg_left hw hl0)
  have e : Real.log (Uf N * Vf N) * (5 * q + 1.5 * q * Real.log q +
      Uf N * Vf N * Real.log q + 5 * N / q * Real.log (Uf N * Vf N)) =
      (5 * q + 1.5 * q * Real.log q) * Real.log (Uf N * Vf N) +
      Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) +
      5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) := by ring
  rw [e] at h1
  linarith [n66a N hL q hq1 hq2, n66b N hL q hq1 hq2, n66c N hL q hq1 hq2]

/-- Lemma 6.5 on the full paper range on page 170.
CONDITIONAL ON the explicitly supplied Wang and Chen Lemma 3. -/
theorem task147_lemma65_full (hWC : WCLemma3) (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 30.95 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (lam2 (Vf N)) c N α‖ ≤ 0.0282 * N / √q * Real.log N ^ 2 +
      0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hN0, hU0, hV0, hlu, hlv⟩ := task147_logs_full N hL
  have hLp : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL1
  have hLV : 0 ≤ Real.log (Vf N) := by rw [hlv]; linarith
  have hV1 : 1 ≤ Vf N := by
    have hh := Real.one_le_exp hLV
    rwa [Real.exp_log hV0] at hh
  have hq15 := (task147_q_range_full N hL q hq1 hq2).1
  have hw := hWC α a q hD hq15 (Vf N) N hV1 hN0
  have hL0 : 0 ≤ Real.log N := by linarith
  have h1 := (S2_le c hc N (Vf N) α).trans (mul_le_mul_of_nonneg_left hw hL0)
  have e : Real.log N * (5 * q + 1.5 * q * Real.log q + Vf N * Real.log q +
      5 * N / q * Real.log (Vf N)) = (5 * q + 1.5 * q * Real.log q) * Real.log N +
      Vf N * Real.log q * Real.log N + 5 * N / q * Real.log (Vf N) * Real.log N := by ring
  rw [e] at h1
  linarith [task147_n65a_full N hL q hq1 hq2, task147_n65b_full N hL q hq1 hq2, task147_n65c_full N hL q hq1 hq2]

/-- Lemma 6.6 on the full paper range on page 170.
CONDITIONAL ON the explicitly supplied Wang and Chen Lemma 3. -/
theorem task147_lemma66_full (hWC : WCLemma3) (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 30.95 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ ≤ 0.0131 * N / √q * Real.log N ^ 2 +
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hN0, hU0, hV0, hlu, hlv⟩ := task147_logs_full N hL
  have hLp : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hlogL : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hL1
  have hLV : 0 ≤ Real.log (Vf N) := by rw [hlv]; linarith
  have hV1 : 1 ≤ Vf N := by
    have hh := Real.one_le_exp hLV
    rwa [Real.exp_log hV0] at hh
  have hhalf := Real.log_le_sub_one_of_pos (show 0 < Real.log N / 2 by positivity)
  rw [Real.log_div hLp.ne' (by norm_num)] at hhalf
  have hLU : 0 ≤ Real.log (Uf N) := by
    rw [hlu]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hU1 : 1 ≤ Uf N := by
    have hh := Real.one_le_exp hLU
    rwa [Real.exp_log hU0] at hh
  have hUV1 : (1 : ℝ) ≤ Uf N * Vf N := by nlinarith
  have hq15 := (task147_q_range_full N hL q hq1 hq2).1
  have hw := hWC α a q hD hq15 (Uf N * Vf N) N hUV1 hN0
  have hl0 : 0 ≤ Real.log (Uf N * Vf N) := Real.log_nonneg hUV1
  have h1 := (S3_le c hc N (Uf N) (Vf N) α hU1 hV1).trans (mul_le_mul_of_nonneg_left hw hl0)
  have e : Real.log (Uf N * Vf N) * (5 * q + 1.5 * q * Real.log q +
      Uf N * Vf N * Real.log q + 5 * N / q * Real.log (Uf N * Vf N)) =
      (5 * q + 1.5 * q * Real.log q) * Real.log (Uf N * Vf N) +
      Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) +
      5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) := by ring
  rw [e] at h1
  linarith [task147_n66a_full N hL q hq1 hq2, task147_n66b_full N hL q hq1 hq2, task147_n66c_full N hL q hq1 hq2]

/-- A derived coefficient margin for Proposition 6.1, pages 168 to 174.
CONDITIONAL ON the Vaughan split, Wang and Chen Lemma 3, and the remaining Lemma 6.7 inputs. -/
theorem task147_prop61_margin (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ)
    (q : ℕ) (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 0.96 * (0.28 * N / √q * Real.log N ^ 2 +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.09 * √N * √q * Real.log N ^ (2.5 : ℝ)) := by
  obtain ⟨-, hV13, -, -, -, -⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  obtain ⟨hq15, hqN⟩ := q_range N hL q hq1 hq2
  rw [S_split c N (Uf N) (Vf N) α hV1]
  have h1 := task147_S1_direct c N (by linarith) α
  have h2 := lemma65 c hc N hL α a q hD hq1 hq2
  have h3 := lemma66 c hc N hL α a q hD hq1 hq2
  have h4 := lemma67 c N hL α a q hD (by omega) hqN
  have p1 : 0 ≤ (N : ℝ) / √q * Real.log N ^ 2 := by positivity
  have p2 : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by positivity
  have p3 : 0 ≤ √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) := by positivity
  have t : ‖Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α +
      Ssum (lam3 (Uf N) (Vf N)) c N α + Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤
      ‖Ssum (lam1 (Uf N)) c N α‖ + ‖Ssum (lam2 (Vf N)) c N α‖ +
      ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ + ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ := norm_add₄_le
  set A := (N : ℝ) / √q * Real.log N ^ 2 with hA
  set B := (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) with hB
  set C := √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) with hC
  have e1 : ∀ x : ℝ, x * N / √q * Real.log N ^ 2 = x * A := fun x => by rw [hA]; ring
  have e2 : ∀ x : ℝ, x * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) = x * B :=
    fun x => by rw [hB]; ring
  have e3 : ∀ x : ℝ, x * √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) = x * C :=
    fun x => by rw [hC]; ring
  rw [e1, e2, e3] at h2 h3 h4 ⊢
  rw [e2] at h1
  linarith

/-- Proposition 6.1 p. 168, (6.2), for `log N ≥ 3100`, `c ≥ 0` and `q` in the range (6.3):
`|S(α)| ≤ 0.28 N q^(-1/2) log^2 N + 4 N^(4/5) log^1.4 N + 0.09 N^(1/2) q^(1/2) log^2.5 N`,
with `S` summed over `cN < n ≤ N`. The coefficients add up as `0.0282 + 0.0131 + 0.2264 ≤ 0.28`,
`0.0999 + 0.0001 + 0.8 + 2.81 ≤ 4`, `0.0006 + 0.0005 + 0.0785 ≤ 0.09`. PROVED, CONDITIONAL ON
`S_split`, `lemma65`, `lemma66`, `lemma67` and their remaining cited and open inputs.
The first sum is bounded by `task147_S1_direct` without the cited `lemma62_S1`. -/
theorem prop61_large (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ)
    (q : ℕ) (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 0.28 * N / √q * Real.log N ^ 2 +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.09 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨-, hV13, -, -, -, -⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  obtain ⟨hq15, hqN⟩ := q_range N hL q hq1 hq2
  rw [S_split c N (Uf N) (Vf N) α hV1]
  have h1 := task147_S1_direct c N (by linarith) α
  have h2 := lemma65 c hc N hL α a q hD hq1 hq2
  have h3 := lemma66 c hc N hL α a q hD hq1 hq2
  have h4 := lemma67 c N hL α a q hD (by omega) hqN
  have p1 : 0 ≤ (N : ℝ) / √q * Real.log N ^ 2 := by positivity
  have p2 : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by positivity
  have p3 : 0 ≤ √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) := by positivity
  have t : ‖Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α +
      Ssum (lam3 (Uf N) (Vf N)) c N α + Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤
      ‖Ssum (lam1 (Uf N)) c N α‖ + ‖Ssum (lam2 (Vf N)) c N α‖ +
      ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ + ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ := norm_add₄_le
  set A := (N : ℝ) / √q * Real.log N ^ 2 with hA
  set B := (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) with hB
  set C := √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) with hC
  have e1 : ∀ x : ℝ, x * N / √q * Real.log N ^ 2 = x * A := fun x => by rw [hA]; ring
  have e2 : ∀ x : ℝ, x * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) = x * B :=
    fun x => by rw [hB]; ring
  have e3 : ∀ x : ℝ, x * √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) = x * C :=
    fun x => by rw [hC]; ring
  rw [e1, e2, e3] at h2 h3 h4 ⊢
  rw [e2] at h1
  linarith

/-- The actual inclusive sum bound on the M4 denominator range on page 174.
CONDITIONAL ON the named Vaughan, Wang and Chen, and Lemma 6.7 inputs. -/
theorem task147_m4_inclusive (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N)
    (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q)
    (hqlo : Real.log N ^ 6 ≤ (q : ℝ)) (hqhi : (q : ℝ) ≤ N / Real.log N ^ 7) :
    ‖Vaughan109.S N c α‖ ≤ 0.3 * N / Real.log N := by
  have hN : (0 : ℝ) < N := (task141_logs N hL).1
  have hL0 : 0 < Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have h4 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < Real.log N ^ 4 := by
    have hp : 0 < Real.log N ^ 4 := by positivity
    nlinarith
  have h46 : Real.log N ^ 4 ≤ Real.log N ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have hq1 := h4.trans_le (h46.trans hqlo)
  have hsmall : (N : ℝ) / Real.log N ^ 7 ≤ N / Real.log N ^ 5 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) (pow_pos hL0 5)
      (pow_le_pow_right₀ hL1 (by norm_num))
  have hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 := by
    calc
      _ ≤ (N : ℝ) / Real.log N ^ 7 := hqhi
      _ ≤ (N : ℝ) / Real.log N ^ 5 := hsmall
      _ < (1.0012 / 0.09) ^ 2 * ((N : ℝ) / Real.log N ^ 5) := by
        nlinarith [div_pos hN (pow_pos hL0 5)]
      _ = _ := by ring
  have hm := task147_prop61_margin c hc N hL α a q hD hq1 hq2
  have hn := task147_m4_numeric N q hL hqlo hqhi
  have hstrict : ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 0.288 * N / Real.log N := by
    calc
      _ ≤ _ := hm
      _ ≤ 0.96 * (0.3 * N / Real.log N) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring
  have he := task147_cutoff_error c N α
  have ha := task147_cutoff_absorb N hL
  have ht := norm_add_le (Ssum (fun n => (vonMangoldt n : ℝ)) c N α)
    (Vaughan109.S N c α - Ssum (fun n => (vonMangoldt n : ℝ)) c N α)
  have hid : Ssum (fun n => (vonMangoldt n : ℝ)) c N α +
      (Vaughan109.S N c α - Ssum (fun n => (vonMangoldt n : ℝ)) c N α) = Vaughan109.S N c α := by abel
  rw [hid] at ht
  calc
    _ ≤ _ := ht
    _ ≤ 0.288 * N / Real.log N + 0.012 * N / Real.log N := add_le_add hstrict (he.trans ha)
    _ = _ := by ring

/-- Nonzero instances of the Vaughan sums and the endpoint difference on pages 144 and 169. -/
theorem task147_nonzero_instances :
    Ssum (lam1 2) 0 2 0 = (Real.log 2 : ℂ) ∧
    Ssum (lam2 1) 0 2 0 = (Real.log 2 : ℂ) ∧
    Ssum (lam3 2 1) 0 2 0 = -(Real.log 2 : ℂ) ∧
    Vaughan109.S 2 1 0 - Ssum (fun n => (vonMangoldt n : ℝ)) 1 2 0 = (Real.log 2 : ℂ) ∧
    0 < Real.log (2 : ℝ) := by
  have hI : Icc 1 (2 : ℕ) = {1, 2} := by decide
  have hd1 : (1 : ℕ).divisors = {1} := by decide
  have hd2 : (2 : ℕ).divisors = {1, 2} := by decide
  have hv2 : (vonMangoldt 2 : ℝ) = Real.log 2 := vonMangoldt_apply_prime Nat.prime_two
  norm_num [Ssum, rangeN, lam1, lam2, lam3, hI, hd1, hd2, e, hv2,
    Vaughan109.S, Vaughan109.weightedSum, Finset.sum_range_succ,
    Finset.sum_insert, Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton, Finset.filter_empty]
  exact Real.log_pos (by norm_num)

/-- A joint nonvacuity instance of the M4 hypotheses on page 174. -/
theorem task147_m4_hyps_hold : ∃ N q : ℕ, 3100 ≤ Real.log N ∧ Real.log N ^ 6 ≤ (q : ℝ) ∧
    (q : ℝ) ≤ N / Real.log N ^ 7 ∧ Dioph (1 / q) 1 q := by
  let N : ℕ := ⌈exp 3100⌉₊
  let L : ℝ := Real.log N
  have hL : 3100 ≤ L := logN_hyp_holds
  have hN : (0 : ℝ) < N := (task141_logs N hL).1
  have hL1 : 1 ≤ L := by linarith
  have hL6 : 0 < L ^ 6 := by positivity
  have hq0 : 0 < ⌈L ^ 6⌉₊ := Nat.ceil_pos.mpr hL6
  refine ⟨N, ⌈L ^ 6⌉₊, hL, Nat.le_ceil _, ?_, ?_⟩
  · have hh := ArcBounds109.denominator_separation L hL
    rw [Real.exp_log hN] at hh
    have hc := Nat.ceil_lt_add_one hL6.le
    have h6 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
    linarith
  · refine ⟨hq0, by simp, ?_⟩
    push_cast
    rw [sub_self, abs_zero]
    positivity

/-- A negative comparison for two attempted replacements of the cited estimate on page 169.
This compares candidate upper bounds and does not assert that the paper estimate is false. -/
theorem task147_chebyshev_gap (X : ℝ) (hX : 15000 ≤ X) :
    1.02 * X < Real.log 4 * X + 2 * √X * Real.log X ∧
    1.02 * X < 1.10556 * X + 5 / (4 * Real.log 6) * Real.log X ^ 2 + 5 / 4 * Real.log X := by
  have hh := BoundLimits109.mathlib_bound_too_large X (by linarith)
  have hx : 0 < X := by linarith
  have hl : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  constructor
  · nlinarith [hh.1]
  · have ht : 0 ≤ 5 / (4 * Real.log 6) * Real.log X ^ 2 := by positivity
    nlinarith

/-! ### Vacuity instances -/

/-- Vacuity: the hypotheses of `WCLemma3` can hold: `α = 1/15`, `a = 1`, `q = 15`. PROVED. -/
theorem wcLemma3_hyps_hold : Dioph (1 / 15) 1 15 ∧ 15 ≤ 15 := by
  refine ⟨⟨by norm_num, by decide, ?_⟩, le_rfl⟩
  norm_num

/-- Vacuity: the hypotheses of `prop61_large`, `lemma65`, `lemma66` and the numerical leaves of
this file hold together, with `N = ⌈e^3100⌉`, `q = ⌈log^6 N⌉`, `α = 1/q`, `a = 1`. PROVED,
using `Constants.aux_half`. -/
theorem prop61_hyps_hold : ∃ N q : ℕ, 3100 ≤ Real.log N ∧
    (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q ∧
    (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 ∧ Dioph (1 / q) 1 q := by
  have hL := logN_hyp_holds
  set N : ℕ := ⌈exp 3100⌉₊ with hNdef
  set L := Real.log N with hLdef
  have hN : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 3100) (Nat.le_ceil _)
  have hNe : (N : ℝ) = exp L := (Real.exp_log hN).symm
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL6 : 0 < L ^ 6 := by positivity
  have hq0 : 0 < ⌈L ^ 6⌉₊ := Nat.ceil_pos.mpr hL6
  refine ⟨N, ⌈L ^ 6⌉₊, hL, ?_, ?_, ?_⟩
  · have h2 : (3100 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
    have h4 : 0 < L ^ 4 := by positivity
    have : (0.28 / 1.0012) ^ 2 * L ^ 4 < L ^ 6 := by
      have : L ^ 6 = L ^ 4 * L ^ 2 := by ring
      rw [this]; nlinarith
    exact this.trans_le (Nat.le_ceil _)
  · have hc : (⌈L ^ 6⌉₊ : ℝ) < L ^ 6 + 1 := Nat.ceil_lt_add_one hL6.le
    have hh := LeanLab.LiuWang2002.Constants.aux_half L hL
    have hE : 81 * L ^ 14 ≤ exp L := by
      have : exp L = exp (L / 2) * exp (L / 2) := by rw [← Real.exp_add]; ring_nf
      rw [this]
      have h7 : 0 ≤ 9 * L ^ 7 := by positivity
      nlinarith [mul_le_mul hh hh h7 (Real.exp_pos _).le]
    have hL5 : 0 < L ^ 5 := by positivity
    have h611 : L ^ 11 ≤ L ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
    have h06 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
    rw [lt_div_iff₀ hL5, hNe]
    have : (L ^ 6 + 1) * L ^ 5 ≤ 2 * L ^ 11 := by
      have : L ^ 11 = L ^ 6 * L ^ 5 := by ring
      nlinarith
    nlinarith
  · refine ⟨hq0, by simp, ?_⟩
    push_cast
    rw [sub_self, abs_zero]
    positivity

end LeanLab.LiuWang2002.U1543
