/-
Exact overlap kernels for P0088 page 11 Lemma 3.4 and page 7 A2.3.
These finite identities isolate the cancellation still needed by the first sum.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD
import LeanLab.PNTPort.Vinogradov.Count
import LeanLab.KumchevLiu2007.Kernel634Base

namespace LeanLab.KumchevLiu2007.Task674

open Real Complex MeasureTheory Task556a
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Page 11 Lemma 3.4: the overlap length of two moving short windows,
clipped to the integration interval. This is an exact elementary identity. -/
theorem short_pair_integral (u v H a b K : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, if (t < u ∧ u ≤ t + H) ∧ (t < v ∧ v ≤ t + H)
      then K else 0) =
      max 0 (min b (min u v) - max a (max u v - H)) * K := by
  have hcond : (fun t : ℝ => if (t < u ∧ u ≤ t + H) ∧ (t < v ∧ v ≤ t + H)
      then K else 0) = (Set.Ico (max u v - H) (min u v)).indicator (fun _ => K) := by
    ext t
    simp only [Set.indicator, Set.mem_Ico, lt_min_iff]
    congr 1
    apply propext
    constructor
    · rintro ⟨⟨htu, hut⟩, ⟨htv, hvt⟩⟩
      exact ⟨by rw [sub_le_iff_le_add, max_le_iff]; exact ⟨hut, hvt⟩, htu, htv⟩
    · rintro ⟨hl, htu, htv⟩
      have hl' : max u v ≤ t + H := by linarith
      exact ⟨⟨htu, (le_max_left _ _).trans hl'⟩,
        ⟨htv, (le_max_right _ _).trans hl'⟩⟩
  rw [hcond, intervalIntegral.integral_of_le hab, ← integral_Ico_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Ico, Set.Ico_inter_Ico]
  simp [smul_eq_mul, max_comm]

/-- Page 11 Lemma 3.4: clipping an overlap cannot increase its length. -/
theorem short_overlap_le_triangle (u v H a b : ℝ) :
    max 0 (min b (min u v) - max a (max u v - H)) ≤ max 0 (H - |u - v|) := by
  apply max_le_max_left
  have hmin := min_le_right b (min u v)
  have hmax := le_max_right a (max u v - H)
  have hdiff : max u v - min u v = |u - v| := by
    simpa only [abs_sub_comm] using max_sub_min_eq_abs u v
  linarith

/-- Page 11 Lemma 3.4: separated square frequencies have no overlap. -/
theorem short_overlap_eq_zero_of_separated (u v H a b : ℝ) (hsep : H ≤ |u - v|) :
    max 0 (min b (min u v) - max a (max u v - H)) = 0 := by
  have h := short_overlap_le_triangle u v H a b
  rw [max_eq_left (by linarith : H - |u - v| ≤ 0)] at h
  exact le_antisymm h (le_max_left _ _)

/-- Page 11 Lemma 3.4: in the square root window, frequency separation
is at least square root Y times the separation of the indices. -/
theorem square_frequency_separation {Y : ℝ} (_hY : 0 ≤ Y) {m n : ℕ}
    (hm : m ∈ squareWindow Y) (hn : n ∈ squareWindow Y) :
    Real.sqrt Y * |(m : ℝ) - n| ≤ |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
  have hml := (Finset.mem_filter.mp hm).2.1
  have hnl := (Finset.mem_filter.mp hn).2.1
  have hsum : Real.sqrt Y ≤ (m : ℝ) + n := by linarith
  calc
    Real.sqrt Y * |(m : ℝ) - n| ≤ ((m : ℝ) + n) * |(m : ℝ) - n| :=
      mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ = |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + n)]

/-- Page 11 Lemma 3.4: the short square sum energy equals a finite
sum over pairs, with the exact clipped overlap kernel. No cancellation
estimate is assumed. -/
theorem short_sum_energy_eq_pairs (S : Finset ℕ) (c : ℕ → ℂ) (H a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) =
    ∑ m ∈ S, ∑ n ∈ S,
      max 0 (min b (min ((m : ℝ) ^ 2) ((n : ℝ) ^ 2)) -
        max a (max ((m : ℝ) ^ 2) ((n : ℝ) ^ 2) - H)) *
        (c m * (starRingEnd ℂ) (c n)).re := by
  have hfull (f : ℕ → ℂ) : ‖∑ m ∈ S, f m‖ ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S, (f m * (starRingEnd ℂ) (f n)).re := by
    rw [Complex.sq_norm]
    have h := congrArg Complex.re (Complex.mul_conj (∑ m ∈ S, f m))
    simp only [Complex.ofReal_re] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
  let F : ℕ → ℕ → ℝ → ℝ := fun m n t =>
    if (t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) ∧
      (t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H)
    then (c m * (starRingEnd ℂ) (c n)).re else 0
  have hint (m n : ℕ) : IntervalIntegrable (F m n) volume a b := by
    have hmeas : Measurable (F m n) := by
      apply Measurable.ite _ measurable_const measurable_const
      exact ((measurableSet_lt measurable_id measurable_const).inter
        (measurableSet_le measurable_const (measurable_id.add_const H))).inter
        ((measurableSet_lt measurable_id measurable_const).inter
          (measurableSet_le measurable_const (measurable_id.add_const H)))
    apply (intervalIntegrable_const (c := |(c m * (starRingEnd ℂ) (c n)).re|)).mono_fun'
      hmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      dsimp [F]
      split_ifs <;> simp)
  have hpoint (t : ℝ) :
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S, F m n t := by
    rw [Finset.sum_filter, hfull]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [F]
    split_ifs <;> simp_all
  simp_rw [hpoint]
  have hintsum (m : ℕ) : IntervalIntegrable (fun t => ∑ n ∈ S, F m n t) volume a b := by
    have h := IntervalIntegrable.sum S (fun n _ => hint m n)
    convert h using 1
    ext t
    rw [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum (fun m _ => hintsum m)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_finsetSum (fun n _ => hint m n)]
  exact Finset.sum_congr rfl (fun n _ => short_pair_integral _ _ H a b _ hab)

/-- Page 11 Lemma 3.4: over the complete support in t the overlap kernel
is triangular, depending only on the difference of square frequencies. -/
theorem short_sum_energy_eq_triangle (S : Finset ℕ) (c : ℕ → ℂ) (N : ℕ)
    (hS : ∀ m ∈ S, m ≤ N) (H : ℝ) (hH : 0 ≤ H) :
    (∫ t in (-H)..(N : ℝ) ^ 2,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) =
    ∑ m ∈ S, ∑ n ∈ S,
      max 0 (H - |(m : ℝ) ^ 2 - (n : ℝ) ^ 2|) *
        (c m * (starRingEnd ℂ) (c n)).re := by
  rw [short_sum_energy_eq_pairs S c H (-H) ((N : ℝ) ^ 2) ((neg_nonpos.mpr hH).trans (sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hmN : (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left (hS m hm) 2
  have hnN : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left (hS n hn) 2
  have hmin : min ((m : ℝ) ^ 2) ((n : ℝ) ^ 2) ≤ (N : ℝ) ^ 2 :=
    (min_le_left _ _).trans hmN
  have hmax : -H ≤ max ((m : ℝ) ^ 2) ((n : ℝ) ^ 2) - H := by
    have h0 := (sq_nonneg (m : ℝ)).trans (le_max_left ((m : ℝ) ^ 2) ((n : ℝ) ^ 2))
    linarith
  rw [min_eq_right hmin, max_eq_right hmax]
  have he : min ((m : ℝ) ^ 2) ((n : ℝ) ^ 2) -
      (max ((m : ℝ) ^ 2) ((n : ℝ) ^ 2) - H) =
      H - |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
    have h := max_sub_min_eq_abs ((m : ℝ) ^ 2) ((n : ℝ) ^ 2)
    rw [abs_sub_comm] at h
    linarith
  rw [he]

/-- Page 11 Lemma 3.4, an elementary partial summation tool for the
small cutoff case. Nonnegative decreasing weights cost only their initial
value when every unweighted prefix has norm at most B. -/
theorem norm_sum_antitone_weight_le (f : ℕ → ℂ) (w : ℕ → ℝ) (N : ℕ)
    (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) (B : ℝ)
    (hB : ∀ k ≤ N, ‖∑ j ∈ Finset.range k, f j‖ ≤ B) :
    ‖∑ j ∈ Finset.range N, w j • f j‖ ≤ w 0 * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 (Nat.zero_le _)
  cases N with
  | zero => simpa using mul_nonneg (hw0 0) hB0
  | succ N =>
    rw [Finset.sum_range_by_parts w f, Nat.add_sub_cancel]
    have htel : ∑ j ∈ Finset.range N, (w j - w (j + 1)) = w 0 - w N := by
      clear hB
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih]; ring
    calc
      _ ≤ ‖w N • ∑ j ∈ Finset.range (N + 1), f j‖ +
          ‖∑ j ∈ Finset.range N, (w (j + 1) - w j) • ∑ i ∈ Finset.range (j + 1), f i‖ :=
        norm_sub_le _ _
      _ ≤ w N * B + ∑ j ∈ Finset.range N, (w j - w (j + 1)) * B := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 N)]
          exact mul_le_mul_of_nonneg_left (hB (N + 1) le_rfl) (hw0 N)
        · apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro j hj
          have hdiff : w (j + 1) ≤ w j := hw (Nat.le_succ j)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hdiff), neg_sub]
          exact mul_le_mul_of_nonneg_left (hB (j + 1) (by
            have := Finset.mem_range.mp hj
            omega)) (sub_nonneg.mpr hdiff)
      _ = w 0 * B := by rw [← Finset.sum_mul, htel]; ring

/-- Page 11 Lemma 3.4, partial summation after differencing the phase.
A decreasing nonnegative weight on a shifted linear phase sum preserves
the geometric sum bound up to the initial weight. -/
theorem norm_weighted_linear_phase_le (w : ℕ → ℝ) (N M : ℕ) (θ : ℝ)
    (hw : Antitone w) (hw0 : ∀ n, 0 ≤ w n) :
    ‖∑ j ∈ Finset.range N, w j •
      LeanLab.PNTPort.LargeSieve.e (((M + 1 : ℕ) : ℝ) * θ + (j : ℝ) * θ)‖ ≤
      w 0 * LeanLab.PNTPort.Vinogradov.G N θ := by
  apply norm_sum_antitone_weight_le _ w N hw hw0
  intro k hk
  have heq : (∑ j ∈ Finset.range k,
      LeanLab.PNTPort.LargeSieve.e (((M + 1 : ℕ) : ℝ) * θ + (j : ℝ) * θ)) =
      ∑ j ∈ Finset.Ioc M (M + k), LeanLab.PNTPort.LargeSieve.e ((j : ℝ) * θ) := by
    rw [LeanLab.PNTPort.Vinogradov.sum_Ioc_e_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => LeanLab.PNTPort.LargeSieve.e_add _ _)
  rw [heq]
  exact (LeanLab.PNTPort.Vinogradov.norm_sum_Ioc_e_le M k θ).trans
    (LeanLab.PNTPort.Vinogradov.G_mono (by exact_mod_cast hk) θ)

/-- Page 11 Lemma 3.4, the difference of indices in the small cutoff
mean square. Each ordered pair with m below n is indexed uniquely by
its positive gap and its lower index. -/
theorem sum_pairs_by_gap {R : Type*} [AddCommMonoid R] (F : ℕ → ℕ → R) (N : ℕ) :
    (∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).filter (fun n => m < n), F m n) =
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (N - d), F m (m + d) := by
  classical
  let S := ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 < p.2)
  let T := ((Finset.Icc 1 N) ×ˢ (Finset.range N)).filter (fun p => p.2 + p.1 < N)
  have hleft : (∑ p ∈ S, F p.1 p.2) =
      ∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).filter (fun n => m < n), F m n := by
    simp only [S, Finset.sum_filter, Finset.sum_product]
  have hright : (∑ p ∈ T, F p.2 (p.2 + p.1)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (N - d), F m (m + d) := by
    simp only [T, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_filter]
    have heq : (Finset.range N).filter (fun m => m + d < N) = Finset.range (N - d) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      have := Finset.mem_Icc.mp hd
      omega
    rw [heq]
  rw [← hleft, ← hright]
  refine Finset.sum_nbij' (fun p : ℕ × ℕ => (p.2 - p.1, p.1))
    (fun p : ℕ × ℕ => (p.2, p.2 + p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [S, T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at *
    omega
  · intro p hp
    simp only [S, T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at *
    omega
  · intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · intro p hp
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp
    ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Prod.fst, Prod.snd]
    congr 1
    omega

/-- Page 11 Lemma 3.4, the diagonal and positive gap expansion of a
symmetric real pair kernel. -/
theorem sum_symmetric_pairs_by_gap (F : ℕ → ℕ → ℝ) (N : ℕ)
    (hF : ∀ m n, F m n = F n m) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, F m n) =
      (∑ m ∈ Finset.range N, F m m) +
        2 * ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (N - d), F m (m + d) := by
  have hp (m n : ℕ) : F m n =
      (if m = n then F m m else 0) + (if m < n then F m n else 0) +
        (if n < m then F n m else 0) := by
    rcases lt_trichotomy m n with h | h | h
    · simp [ne_of_lt h, h, not_lt_of_ge h.le]
    · subst n
      simp
    · simp [(ne_of_lt h).symm, h, not_lt_of_ge h.le, hF m n]
  have hdiag : (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      if m = n then F m m else 0) = ∑ m ∈ Finset.range N, F m m := by
    apply Finset.sum_congr rfl
    intro m hm
    simp [hm]
  have hlow : (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      if n < m then F n m else 0) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, if m < n then F m n else 0 := by
    rw [Finset.sum_comm]
  calc
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        ((if m = n then F m m else 0) + (if m < n then F m n else 0) +
          (if n < m then F n m else 0)) :=
      Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hp m n))
    _ = (∑ m ∈ Finset.range N, F m m) +
        2 * (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, if m < n then F m n else 0) := by
      simp only [Finset.sum_add_distrib]
      rw [hdiag, hlow]
      ring
    _ = _ := by
      simpa only [Finset.sum_filter] using congrArg
        (fun x : ℝ => (∑ m ∈ Finset.range N, F m m) + 2 * x) (sum_pairs_by_gap F N)

/-- P0088 page 11 Lemma 3.4, the unweighted first sum after taking a
positive gap. The triangular overlap weight decreases with the lower index,
so partial summation leaves a geometric sum at frequency twice d alpha.
See Liu and Zhan 1997 page 384 display 17 with the outer indices fixed. -/
theorem quadratic_gap_sum_le (L K N d : ℕ) (H α : ℝ) (hKN : K ≤ N) (hH : 0 ≤ H) :
    (∑ j ∈ Finset.range K,
      max 0 (H - (d : ℝ) * (2 * ((L + j : ℕ) : ℝ) + d)) *
        (LeanLab.PNTPort.LargeSieve.e
          (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2)))).re) ≤
      H * LeanLab.PNTPort.Vinogradov.G N (2 * d * α) := by
  let w : ℕ → ℝ := fun j => max 0 (H - (d : ℝ) * (2 * ((L + j : ℕ) : ℝ) + d))
  let θ : ℝ := 2 * d * α
  let c : ℝ := α * d * (2 * L + d) - θ
  have hw : Antitone w := by
    intro i j hij
    apply max_le_max_left
    have hijr : (i : ℝ) ≤ j := by exact_mod_cast hij
    push_cast
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hw0 (j : ℕ) : 0 ≤ w j := le_max_left _ _
  have hwH : w 0 ≤ H := by
    dsimp [w]
    apply max_le hH
    have hprod : 0 ≤ (d : ℝ) * (2 * (L : ℝ) + d) := by positivity
    linarith
  have hb := norm_weighted_linear_phase_le w K 0 θ hw hw0
  have heq (j : ℕ) : LeanLab.PNTPort.LargeSieve.e
      (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2))) =
      LeanLab.PNTPort.LargeSieve.e c *
        LeanLab.PNTPort.LargeSieve.e ((((0 + 1 : ℕ) : ℝ) * θ + (j : ℝ) * θ)) := by
    rw [← LeanLab.PNTPort.LargeSieve.e_add]
    congr 1
    dsimp [c, θ]
    push_cast
    ring
  have hsum : (∑ j ∈ Finset.range K, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e
      (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2)))) =
      LeanLab.PNTPort.LargeSieve.e c * ∑ j ∈ Finset.range K,
        w j • LeanLab.PNTPort.LargeSieve.e ((((0 + 1 : ℕ) : ℝ) * θ + (j : ℝ) * θ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [heq, Complex.real_smul]
    ring
  have hreal : (∑ j ∈ Finset.range K,
      w j * (LeanLab.PNTPort.LargeSieve.e
        (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2)))).re) =
      (∑ j ∈ Finset.range K, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e
        (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2)))).re := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  change (∑ j ∈ Finset.range K, w j * _) ≤ _
  rw [hreal]
  calc
    _ ≤ ‖∑ j ∈ Finset.range K, (w j : ℂ) * LeanLab.PNTPort.LargeSieve.e
        (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2)))‖ :=
      Complex.re_le_norm _
    _ ≤ w 0 * LeanLab.PNTPort.Vinogradov.G K θ := by
      rw [hsum, norm_mul, LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
      exact hb
    _ ≤ H * LeanLab.PNTPort.Vinogradov.G N θ :=
      mul_le_mul hwH (LeanLab.PNTPort.Vinogradov.G_mono (by exact_mod_cast hKN) θ)
        (LeanLab.PNTPort.Vinogradov.G_nonneg (Nat.cast_nonneg K) θ) hH

/-- P0088 page 11 Lemma 3.4, the rational approximation count needed
after differencing the unweighted quadratic sum. Restricting the existing
Vinogradov count to even multipliers costs only a doubled range. -/
theorem sum_G_even_le {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (hcop : IsCoprime a (q : ℤ))
    {α : ℝ} (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (D N : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, LeanLab.PNTPort.Vinogradov.G N (2 * d * α)) ≤
      ((2 * (D : ℝ)) / q + 1) * (4 * N + q * (1 + Real.log q)) := by
  let S := (Finset.Icc 1 D).image (fun d => 2 * d)
  have hsub : S ⊆ Finset.Icc 1 (2 * D) := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  have heq : (∑ d ∈ Finset.Icc 1 D, LeanLab.PNTPort.Vinogradov.G N (2 * d * α)) =
      ∑ m ∈ S, LeanLab.PNTPort.Vinogradov.G N (α * m) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      congr 1
      push_cast
      ring
    · intro i hi j hj hij
      dsimp at hij
      omega
  rw [heq]
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ =>
    LeanLab.PNTPort.Vinogradov.G_nonneg (Nat.cast_nonneg N) (α * m))).trans
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    LeanLab.PNTPort.Vinogradov.sum_G_le hq hcop hα (2 * D) (Nat.cast_nonneg N)

/-- P0088 page 11 Lemma 3.4, the elementary positive gap bound for the
unweighted triangular quadratic kernel. The cutoff D excludes gaps whose
square frequency distance already reaches H. -/
theorem quadratic_triangle_sum_le (L N D : ℕ) (H α : ℝ) (hH : 0 ≤ H)
    (hD : H ≤ ((D + 1 : ℕ) : ℝ) * (2 * L + (D + 1 : ℕ))) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      max 0 (H - |((L + i : ℕ) : ℝ) ^ 2 - ((L + j : ℕ) : ℝ) ^ 2|) *
        (LeanLab.PNTPort.LargeSieve.e
          (α * |((L + i : ℕ) : ℝ) ^ 2 - ((L + j : ℕ) : ℝ) ^ 2|)).re) ≤
      H * N + 2 * H * ∑ d ∈ Finset.Icc 1 D,
        LeanLab.PNTPort.Vinogradov.G N (2 * d * α) := by
  let F : ℕ → ℕ → ℝ := fun i j =>
    max 0 (H - |((L + i : ℕ) : ℝ) ^ 2 - ((L + j : ℕ) : ℝ) ^ 2|) *
      (LeanLab.PNTPort.LargeSieve.e
        (α * |((L + i : ℕ) : ℝ) ^ 2 - ((L + j : ℕ) : ℝ) ^ 2|)).re
  have hsym (i j : ℕ) : F i j = F j i := by dsimp [F]; rw [abs_sub_comm]
  have hdiag : (∑ i ∈ Finset.range N, F i i) = H * N := by
    simp only [F, sub_self, abs_zero, sub_zero, max_eq_right hH, mul_zero,
      LeanLab.PNTPort.LargeSieve.e_zero, Complex.one_re, mul_one,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hgap (d j : ℕ) : F j (j + d) =
      max 0 (H - (d : ℝ) * (2 * ((L + j : ℕ) : ℝ) + d)) *
        (LeanLab.PNTPort.LargeSieve.e
          (α * ((((L + j + d : ℕ) : ℝ) ^ 2) - (((L + j : ℕ) : ℝ) ^ 2)))).re := by
    have hle : ((L + j : ℕ) : ℝ) ^ 2 ≤ ((L + (j + d) : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast Nat.pow_le_pow_left (by omega : L + j ≤ L + (j + d)) 2
    dsimp [F]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hdist : -(((L + j : ℕ) : ℝ) ^ 2 - ((L + (j + d) : ℕ) : ℝ) ^ 2) =
        (d : ℝ) * (2 * ((L + j : ℕ) : ℝ) + d) := by push_cast; ring
    rw [hdist]
    congr 2
    push_cast
    ring
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      (∑ j ∈ Finset.range (N - d), F j (j + d)) ≤
        if d ≤ D then H * LeanLab.PNTPort.Vinogradov.G N (2 * d * α) else 0 := by
    simp_rw [hgap]
    split_ifs with hdD
    · exact quadratic_gap_sum_le L (N - d) N d H α (Nat.sub_le _ _) hH
    · have hDd : D + 1 ≤ d := by omega
      have hDdr : ((D + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hDd
      have hpoly : ((D + 1 : ℕ) : ℝ) * (2 * L + (D + 1 : ℕ)) ≤
          (d : ℝ) * (2 * L + d) := by
        apply mul_le_mul hDdr _ (by positivity) (by positivity)
        linarith
      have hcut : H ≤ (d : ℝ) * (2 * L + d) := hD.trans hpoly
      have hz (j : ℕ) : max 0 (H - (d : ℝ) * (2 * ((L + j : ℕ) : ℝ) + d)) = 0 := by
        apply max_eq_left
        push_cast
        nlinarith [show (0 : ℝ) ≤ (d : ℝ) * j by positivity]
      simp_rw [hz, zero_mul]
      simp
  have hsum : (∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (N - d), F j (j + d)) ≤
      H * ∑ d ∈ Finset.Icc 1 D, LeanLab.PNTPort.Vinogradov.G N (2 * d * α) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N,
          if d ≤ D then H * LeanLab.PNTPort.Vinogradov.G N (2 * d * α) else 0 :=
        Finset.sum_le_sum hterm
      _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ≤ D),
          H * LeanLab.PNTPort.Vinogradov.G N (2 * d * α) := (Finset.sum_filter _ _).symm
      _ ≤ ∑ d ∈ Finset.Icc 1 D,
          H * LeanLab.PNTPort.Vinogradov.G N (2 * d * α) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
          omega
        · intro d hd hnot
          exact mul_nonneg hH (LeanLab.PNTPort.Vinogradov.G_nonneg (Nat.cast_nonneg N) _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  change (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j) ≤ _
  rw [sum_symmetric_pairs_by_gap F N hsym, hdiag]
  nlinarith

/-- Page 2 display 5: exact integer endpoints of the square root window. -/
theorem squareWindow_eq_Ico (Y : ℝ) :
    squareWindow Y = Finset.Ico ⌈Real.sqrt Y / 2⌉₊ ⌈Real.sqrt Y⌉₊ := by
  ext m
  simp only [squareWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
    Nat.ceil_le, Nat.lt_ceil]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.le), h⟩

/-- P0088 page 11 Lemma 3.4 at small cutoff, before logarithmic absorption.
This explicit mean square bound follows from differencing and the existing
Vinogradov rational approximation count. It is uniform over subintervals
of the paper window and assumes no cited analytic theorem. -/
theorem unweighted_square_energy_bound (Y H α a b : ℝ) (hY : 1 ≤ Y)
    (hH : Real.sqrt Y ≤ H) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Y)
    {q : ℕ} (hq : 1 ≤ q) {v : ℤ} (hcop : IsCoprime v (q : ℤ))
    (hα : |α - v / q| ≤ 1 / (q : ℝ) ^ 2) :
    (∫ t in a..b,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      18 * H * Real.sqrt Y + 32 * H ^ 2 / q +
        4 * H ^ 2 * (1 + Real.log q) / Real.sqrt Y +
          2 * H * q * (1 + Real.log q) := by
  let r := Real.sqrt Y
  let L : ℕ := ⌈r / 2⌉₊
  let U : ℕ := ⌈r⌉₊
  let N : ℕ := U - L
  let D : ℕ := ⌊H / r⌋₊
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr hY
  have hH0 : 0 ≤ H := hr.le.trans hH
  have hL : r / 2 ≤ (L : ℝ) := Nat.le_ceil _
  have hU : r ≤ (U : ℝ) := Nat.le_ceil _
  have hN : (N : ℝ) ≤ 2 * r := by
    have hNU : N ≤ U := Nat.sub_le _ _
    have hNUr : (N : ℝ) ≤ U := by exact_mod_cast hNU
    have hUupper : (U : ℝ) < r + 1 := Nat.ceil_lt_add_one hr.le
    linarith
  have hDupper : (D : ℝ) ≤ H / r := Nat.floor_le (div_nonneg hH0 hr.le)
  have hDcut : H ≤ ((D + 1 : ℕ) : ℝ) * (2 * L + (D + 1 : ℕ)) := by
    have hfloor : H / r < (D : ℝ) + 1 := Nat.lt_floor_add_one (H / r)
    have h1 : H ≤ ((D : ℝ) + 1) * r := ((div_lt_iff₀ hr).mp hfloor).le
    have h2 : r ≤ 2 * L + (D + 1 : ℕ) := by
      have hpos : (0 : ℝ) ≤ (D + 1 : ℕ) := Nat.cast_nonneg _
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (D : ℝ) + 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h1.trans h3
  have hSU : ∀ m ∈ squareWindow Y, m ≤ U := by
    intro m hm
    rw [squareWindow_eq_Ico] at hm
    exact (Finset.mem_Ico.mp hm).2.le
  have hYU : Y ≤ (U : ℝ) ^ 2 := by
    have hs := pow_le_pow_left₀ hr.le hU 2
    simpa only [r, Real.sq_sqrt (by linarith : 0 ≤ Y)] using hs
  let c : ℕ → ℂ := fun m => fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))
  have hint := Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow Y) c H (-H) ((U : ℝ) ^ 2)
  have hmono := intervalIntegral.integral_mono_interval (a := a) (b := b)
    (by linarith : -H ≤ a) hab (hb.trans hYU)
    (Filter.Eventually.of_forall (fun t => sq_nonneg
      ‖∑ m ∈ (squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖)) hint
  rw [short_sum_energy_eq_triangle (squareWindow Y) c U hSU H hH0] at hmono
  have hphase (x y : ℝ) :
      (LeanLab.PNTPort.LargeSieve.e (x * α) *
        (starRingEnd ℂ) (LeanLab.PNTPort.LargeSieve.e (y * α))).re =
      (LeanLab.PNTPort.LargeSieve.e (α * |x - y|)).re := by
    rw [← LeanLab.PNTPort.LargeSieve.e_neg, ← LeanLab.PNTPort.LargeSieve.e_add]
    by_cases h : 0 ≤ x - y
    · rw [abs_of_nonneg h]
      congr 2
      ring
    · rw [abs_of_nonpos (le_of_not_ge h)]
      have he : x * α + -(y * α) = -(α * -(x - y)) := by ring
      rw [he, LeanLab.PNTPort.LargeSieve.e_neg]
      simp
  conv at hmono =>
    rhs
    simp only [c, Task556d.fourier_nat_eq_e]
    simp only [Nat.cast_pow, hphase, squareWindow_eq_Ico, Finset.sum_Ico_eq_sum_range]
  have htri := quadratic_triangle_sum_le L N D H α hH0 hDcut
  have hfirst : (∫ t in a..b,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      H * N + 2 * H * ∑ d ∈ Finset.Icc 1 D,
        LeanLab.PNTPort.Vinogradov.G N (2 * d * α) := by
    exact hmono.trans htri
  have hcount := sum_G_even_le hq hcop hα D N
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  calc
    _ ≤ H * N + 2 * H * (((2 * (D : ℝ)) / q + 1) *
        (4 * N + q * (1 + Real.log q))) :=
      hfirst.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcount
        (show 0 ≤ 2 * H by positivity)))
    _ ≤ H * (2 * r) + 2 * H * (((2 * (H / r)) / q + 1) *
        (4 * (2 * r) + q * (1 + Real.log q))) := by
      gcongr
    _ = _ := by
      dsimp [r]
      field_simp [ne_of_gt hr, ne_of_gt hq0]
      <;> ring

end LeanLab.KumchevLiu2007.Task674

#print axioms LeanLab.KumchevLiu2007.Task674.short_pair_integral
#print axioms LeanLab.KumchevLiu2007.Task674.short_overlap_le_triangle
#print axioms LeanLab.KumchevLiu2007.Task674.short_overlap_eq_zero_of_separated
#print axioms LeanLab.KumchevLiu2007.Task674.square_frequency_separation
#print axioms LeanLab.KumchevLiu2007.Task674.short_sum_energy_eq_pairs
#print axioms LeanLab.KumchevLiu2007.Task674.short_sum_energy_eq_triangle
#print axioms LeanLab.KumchevLiu2007.Task674.norm_sum_antitone_weight_le
#print axioms LeanLab.KumchevLiu2007.Task674.norm_weighted_linear_phase_le

#print axioms LeanLab.KumchevLiu2007.Task674.sum_pairs_by_gap

#print axioms LeanLab.KumchevLiu2007.Task674.sum_symmetric_pairs_by_gap

#print axioms LeanLab.KumchevLiu2007.Task674.quadratic_gap_sum_le

#print axioms LeanLab.KumchevLiu2007.Task674.sum_G_even_le

#print axioms LeanLab.KumchevLiu2007.Task674.quadratic_triangle_sum_le

#print axioms LeanLab.KumchevLiu2007.Task674.squareWindow_eq_Ico
#print axioms LeanLab.KumchevLiu2007.Task674.unweighted_square_energy_bound
